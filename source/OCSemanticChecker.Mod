MODULE OCSemanticChecker; (* AUTHOR "fof & fn"; PURPOSE "Oberon Compiler: Semantic Checker"; *)
(* (c) fof ETHZ 2009 *)

IMPORT D := Debugging, Basic := OCBasic, Scanner := OCScanner, SyntaxTree := OCSyntaxTree,
Diagnostics, Global := OCGlobal, Printout:= OCPrintout, Formats := OCFormats, SYSTEM, Machine,Strings;

CONST
	Trace = FALSE;

	Infinity = MAX(LONGINT); (* for type distance *)
	InvalidPosition = Diagnostics.Invalid;
	UndefinedPhase = 0; DeclarationPhase=1; ImplementationPhase=2;

TYPE

	LateFix= POINTER TO RECORD (* contains a late fix to be resolved in a later step: type fixes and implementations *)
		p: ANY; scope: SyntaxTree.Scope;
		next: LateFix;
	END;

	LateFixList = OBJECT (* fifo queue for items to be resolved later on - deferred fixes *)
	VAR first,last: LateFix;

		PROCEDURE & Init;
		BEGIN first := NIL; last := NIL;
		END Init;

		(* get and remove element from list *)
		PROCEDURE Get(VAR scope: SyntaxTree.Scope): ANY;
		VAR p: ANY;
		BEGIN
			IF first # NIL THEN p := first.p; scope := first.scope; first := first.next ELSE p := NIL; END;
			IF first = NIL THEN last := NIL END;
			RETURN p;
		END Get;

		(* add unresolved type to list *)
		PROCEDURE Add(p: ANY; scope: SyntaxTree.Scope);
		VAR next: LateFix;
		BEGIN
			ASSERT(scope # NIL);
			NEW(next); next.p := p; next.scope := scope;
			next.next := NIL;
			IF first = NIL THEN first := next; last := next;
			ELSE last.next := next; last := next
			END;
		END Add;

	END LateFixList;

	(** checker object: used to check and resolve a module
		- resolves types
		- resolves expressions
		- resolves designators
		- resolves declarations
		- resolves statements
		- resolves implementations (bodies)
	**)
	Checker*= OBJECT (SyntaxTree.Visitor)
	VAR
		diagnostics: Diagnostics.Diagnostics;
		error-: BOOLEAN;
		VerboseErrorMessage: BOOLEAN;
		typeFixes: LateFixList;
		importCache-: SyntaxTree.ModuleScope; (* contains global imports, did not take ImportList as it was much slower, for whatever reasons *)
		arrayBaseImported: BOOLEAN;
		phase: LONGINT;
		system-: Global.System;
		symbolFileFormat-: Formats.SymbolFileFormat;

		(* temporary variables for the visitors
		    they replace variables on a stack during use of the visitor pattern and may only be
			- set and AcceptXXX procedures
			- set and read in ResolveXXX procedures
		*)
		resolvedType: SyntaxTree.Type; (** temporary used for type resolution **)
		resolvedExpression: SyntaxTree.Expression; (** temporary variable used for expression resolution **)
		resolvedStatement: SyntaxTree.Statement; (** used for statement resolution **)
		currentScope: SyntaxTree.Scope;
		currentFlags: SET; (** used for check on recursive exclusive sections etc. *)
		global: SyntaxTree.ModuleScope;


		PROCEDURE &InitChecker*(diagnostics: Diagnostics.Diagnostics; verboseErrorMessage: BOOLEAN; system: Global.System; symbolFileFormat: Formats.SymbolFileFormat; VAR importCache: SyntaxTree.ModuleScope);
		BEGIN
			SELF.diagnostics := diagnostics;
			SELF.system := system;
			SELF.symbolFileFormat := symbolFileFormat;
			error := FALSE;
			NEW(typeFixes);
			resolvedType := NIL;
			resolvedExpression := NIL;
			resolvedStatement := NIL;
			currentScope := NIL;
			IF importCache = NIL THEN importCache := SyntaxTree.NewModuleScope() END;
			SELF.importCache := importCache;
			arrayBaseImported := FALSE;
			SELF.VerboseErrorMessage := verboseErrorMessage;
			global := NIL;
			phase := UndefinedPhase;
			currentFlags := {};
		END InitChecker;

		(** report error **)
		PROCEDURE Error(position: LONGINT; code: LONGINT; CONST message: ARRAY OF CHAR);
		VAR errorMessage: ARRAY 256 OF CHAR;
		BEGIN
			IF diagnostics # NIL THEN
				Basic.GetErrorMessage(code,message,errorMessage);
				diagnostics.Error(currentScope.ownerModule.sourceName, position, code, errorMessage);
			END;
			error := TRUE;
		END Error;

		PROCEDURE ErrorSS(position: LONGINT; CONST msg,msg2: ARRAY OF CHAR);
		VAR errorMessage: ARRAY 256 OF CHAR;
		BEGIN
			IF diagnostics # NIL THEN
				Basic.Concat(errorMessage,msg," ", msg2);
				diagnostics.Error(currentScope.ownerModule.sourceName, position, Diagnostics.Invalid, errorMessage);
			END;
			error := TRUE;
		END ErrorSS;

		(*** symbol lookup ***)

		(** find a symbol in the current scope, traverse to outer scope if traverse=true and no symbol found yet
		**)
		PROCEDURE Find(inScope: SyntaxTree.Scope; name: SyntaxTree.Identifier; traverse: BOOLEAN): SyntaxTree.Symbol;
		VAR
			scope,baseScope: SyntaxTree.Scope;
			symbol: SyntaxTree.Symbol;
			ownerRecord,base: SyntaxTree.RecordType;
		BEGIN
			scope := inScope;
			WHILE (scope # NIL) & (symbol = NIL) DO
				symbol := scope.FindSymbol(name);

				WHILE (symbol # NIL) & (symbol.scope.ownerModule # currentScope.ownerModule) & (symbol.access * SyntaxTree.Public = {}) DO
					(* found symbol in different module, but is it not exported, can we go on searching in record base scopes ? *)
					IF (symbol.scope IS SyntaxTree.RecordScope) THEN
						ownerRecord := symbol.scope(SyntaxTree.RecordScope).ownerRecord;
						base := RecordBase(ownerRecord);
						IF (base # NIL) THEN
							baseScope := base.recordScope;
							symbol := Find(baseScope,name,FALSE);
						ELSE
							symbol := NIL;
						END;
					ELSE
						symbol := NIL;
					END;
				END;
				IF traverse THEN scope := scope.outerScope ELSE scope := NIL END;
			END;
			IF (symbol # NIL) THEN
				IF ~(SyntaxTree.Resolved IN symbol.state) THEN
					ASSERT((phase = DeclarationPhase) OR (symbol IS SyntaxTree.GuardedVariable));
					ResolveSymbol(symbol)
				END;
			END;
			RETURN symbol
		END Find;

		(*** types ***)

		(** find type declaration with name qualifiedIdentifier and return resolved type
			- check qualified identifier prefix, set scope to module scope if appropriate
			- check suffix in scope
		**)
		PROCEDURE ResolveNamedType(qualifiedIdentifier: SyntaxTree.QualifiedIdentifier; VAR typeDeclaration: SyntaxTree.TypeDeclaration): SyntaxTree.Type;
		VAR prevScope: SyntaxTree.Scope; symbol: SyntaxTree.Symbol; result:SyntaxTree.Type;
		BEGIN
			result := NIL;
			prevScope := currentScope;
			IF (qualifiedIdentifier.prefix) # NIL THEN
				symbol := Find(currentScope,qualifiedIdentifier.prefix,TRUE);
				IF (symbol # NIL) & (symbol IS SyntaxTree.Import) THEN
					IF symbol(SyntaxTree.Import).module = NIL THEN
						Error(qualifiedIdentifier.suffix.position,Diagnostics.Invalid,"module not loaded");
						result := Global.invalidType;
						symbol := NIL;
					ELSE
						currentScope := symbol(SyntaxTree.Import).module.moduleScope;
						symbol := Find(currentScope,qualifiedIdentifier.suffix,FALSE);
						IF (symbol = NIL) OR (symbol.access * SyntaxTree.Public = {}) THEN Error(qualifiedIdentifier.suffix.position,Diagnostics.Invalid,"undeclared identifier (prefix-suffix)") END;
					END;
				ELSE
					Error(qualifiedIdentifier.suffix.position,Diagnostics.Invalid,"prefix does not denote a module name");
					symbol := NIL;
				END;
			ELSE
				symbol := Find(currentScope,qualifiedIdentifier.suffix,TRUE);
				IF symbol = NIL THEN
					Error(qualifiedIdentifier.suffix.position,Diagnostics.Invalid,"undeclared identifier (qualident suffix)");
					IF VerboseErrorMessage THEN
						Printout.Info("Qualident",qualifiedIdentifier);
						Printout.Info("in scope",currentScope) ;
					END;
				END;
			END;

			IF symbol = NIL THEN (* error already handled *)
				typeDeclaration := NIL;
				result := Global.invalidType;
			ELSIF ~(symbol IS SyntaxTree.TypeDeclaration) THEN
				Error(qualifiedIdentifier.suffix.position,Diagnostics.Invalid,"symbol does not denote a type");
				typeDeclaration := NIL;
				result := Global.invalidType;
			ELSE
				currentScope := symbol.scope;
				typeDeclaration := symbol(SyntaxTree.TypeDeclaration);
				result := ResolveType(typeDeclaration.declaredType);
				ASSERT(result # NIL);
			END;
			currentScope := prevScope;


			RETURN result
		END ResolveNamedType;

		(** Check if a node has already been resolved. If not then mark as currently being resolved.
			If node is currently being resolved then emit a cyclic definition error.
			Return TRUE only if node is fully resolved.
		**)
		PROCEDURE TypeNeedsResolution(x: SyntaxTree.Type): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			IF SyntaxTree.Resolved IN x.state THEN
				result := FALSE
			ELSIF SyntaxTree.BeingResolved IN x.state THEN
				Error(x.position,Diagnostics.Invalid,"cyclic definition");
				result := FALSE;
			ELSE
				result := TRUE;
				x.SetState(SyntaxTree.BeingResolved)
			END;
			RETURN result
		END TypeNeedsResolution;

		(** Return invalid type if x is currently being resolved, return x otherwise**)
		PROCEDURE ResolvedType(x: SyntaxTree.Type): SyntaxTree.Type;
		BEGIN
			IF SyntaxTree.Resolved IN x.state THEN
				RETURN x
			ELSE
				RETURN Global.invalidType
			END;
		END ResolvedType;

		PROCEDURE VisitType(x: SyntaxTree.Type);
		BEGIN
			ASSERT(x = Global.invalidType);
		END VisitType;

		(** resolve basic type **)
		PROCEDURE VisitBasicType(x: SyntaxTree.BasicType);
		BEGIN
			IF TypeNeedsResolution(x) THEN
				x.SetState(SyntaxTree.Resolved);
			END;
			resolvedType := ResolvedType(x)
		END VisitBasicType;

		(** resolve character type **)
		PROCEDURE VisitCharacterType(x: SyntaxTree.CharacterType);
		BEGIN
			VisitBasicType(x);
		END VisitCharacterType;

		(** resolve integer type **)
		PROCEDURE VisitIntegerType(x: SyntaxTree.IntegerType);
		BEGIN
			VisitBasicType(x);
		END VisitIntegerType;

		(** resolve real type **)
		PROCEDURE VisitFloatType(x: SyntaxTree.FloatType);
		BEGIN
			VisitBasicType(x);
		END VisitFloatType;

		(**
			resolve string type: nothing to be done
		**)
		PROCEDURE VisitStringType(x: SyntaxTree.StringType);
		BEGIN
			IF TypeNeedsResolution(x) THEN
				x.SetState(SyntaxTree.Resolved);
			END;
			resolvedType := ResolvedType(x)
		END VisitStringType;

		PROCEDURE VisitEnumerator(enumerator: SyntaxTree.Enumerator);
		VAR scope: SyntaxTree.EnumerationScope;
		BEGIN
			IF SymbolNeedsResolution(enumerator) THEN
				scope := enumerator.scope(SyntaxTree.EnumerationScope);
				enumerator.SetType(scope.ownerEnumeration);
				enumerator.value.SetValue(enumerator.value.value+scope.ownerEnumeration.baseValue);
				enumerator.SetState(SyntaxTree.Resolved);
			END;
		END VisitEnumerator;

		(**
			check enumeration scope: enter symbols and check for duplicate names
		**)
		PROCEDURE CheckEnumerationScope(x: SyntaxTree.EnumerationScope);
		VAR e: SyntaxTree.Enumerator;
		BEGIN
			e := x.firstEnumerator;
			WHILE (e # NIL) DO
				Register(e,x,FALSE);
				VisitEnumerator(e);
				e := e.nextEnumerator;
			END;
		END CheckEnumerationScope;

		(**
			resolve enumeration type: check enumeration scope
		**)
		PROCEDURE VisitEnumerationType(x: SyntaxTree.EnumerationType);
		VAR position: LONGINT; baseScope: SyntaxTree.EnumerationScope; baseType,resolved: SyntaxTree.Type; enumerationBase: SyntaxTree.EnumerationType;
		BEGIN
			IF TypeNeedsResolution(x) THEN
				IF x.enumerationBase # NIL THEN
					position := x.enumerationBase.position;
					baseType := ResolveType(x.enumerationBase);
					resolved := baseType.resolved;
					baseScope := NIL;
					IF resolved = Global.invalidType THEN (* error already handled *)
					ELSIF ~(resolved IS SyntaxTree.EnumerationType) THEN
						Error(position,Diagnostics.Invalid,"base type is no enumeration type");
					ELSE
						enumerationBase := resolved(SyntaxTree.EnumerationType);
						baseScope := enumerationBase.enumerationScope;
						x.SetBaseValue(enumerationBase.baseValue + baseScope.numberEnumerators);
					END;
					x.SetEnumerationBase(baseType);

				END;
				CheckEnumerationScope(x.enumerationScope);
				x.SetState(SyntaxTree.Resolved);
			END;
			resolvedType := ResolvedType(x);
		END VisitEnumerationType;

		(**
			resolve range type: nothing to be done
		**)
		PROCEDURE VisitRangeType(x: SyntaxTree.RangeType);
		BEGIN
			IF TypeNeedsResolution(x) THEN
				x.SetState(SyntaxTree.Resolved);
			END;
			resolvedType := ResolvedType(x)
		END VisitRangeType;

		(**
			resolve qualified type
			- find and resolve named type and set resolved type
		**)
		PROCEDURE VisitQualifiedType(x: SyntaxTree.QualifiedType);
		VAR type: SyntaxTree.Type; typeDeclaration: SyntaxTree.TypeDeclaration;
		BEGIN
			IF TypeNeedsResolution(x) THEN
				type := ResolveNamedType(x.qualifiedIdentifier, typeDeclaration);
				x.SetResolved(type.resolved);
				x.SetState(SyntaxTree.Resolved);
				x.SetTypeDeclaration (typeDeclaration);
			ELSIF ~(SyntaxTree.Resolved IN x.state) THEN
				x.SetResolved(Global.invalidType);
			END;
			resolvedType := x;
		END VisitQualifiedType;

		(**
			resolve array type
			- check base type
				- array of math array  forbidden
				- static array of open array forbidden
		**)
		PROCEDURE VisitArrayType(x: SyntaxTree.ArrayType);
		VAR arrayBase: SyntaxTree.Type;
		BEGIN
			IF TypeNeedsResolution(x) THEN
				x.SetArrayBase(ResolveType(x.arrayBase));
				arrayBase := x.arrayBase.resolved;
				IF x.length # NIL THEN
					x.SetLength(ConstantIntegerGeq0(x.length));
				END;
				IF arrayBase IS SyntaxTree.ArrayType THEN
					IF (x.form = SyntaxTree.Static) & (arrayBase(SyntaxTree.ArrayType).form = SyntaxTree.Open) THEN
						Error(x.position,Diagnostics.Invalid,"forbidden static array of dynamic array");
					END;
				ELSIF arrayBase IS SyntaxTree.MathArrayType THEN
					Error(x.position,Diagnostics.Invalid,"forbidden array mixed form");
				END;
				x.SetState(SyntaxTree.Resolved);
			END;
			resolvedType := ResolvedType(x);
		END VisitArrayType;

		PROCEDURE ImportArrayBase(position: LONGINT);
		VAR module: SyntaxTree.Module; import: SyntaxTree.Import; moduleScope: SyntaxTree.ModuleScope;
		BEGIN
			module := currentScope.ownerModule;
			IF module.name.Equals(Global.ArrayBaseName) THEN
				(* do nothing *)
			ELSE
				moduleScope := module.moduleScope;
				import := moduleScope.FindImport(Global.ArrayBaseName);
				IF import = NIL THEN
					import := SyntaxTree.NewImport(position,Global.ArrayBaseName,Global.ArrayBaseName,TRUE);
					moduleScope.AddImport(import);
					Register(import,moduleScope,FALSE);
					VisitImport(import);
				ELSE
					D.Str("array base already imported"); D.Ln;
				END;
			END;
		END ImportArrayBase;

		(**
			resolve math array type
			- check base type
				- open math array of array  forbidden
				- math array of tensor forbidden
				- static array of open array forbidden
		**)
		PROCEDURE VisitMathArrayType(x: SyntaxTree.MathArrayType);
		VAR arrayBase: SyntaxTree.Type;
		BEGIN
			IF TypeNeedsResolution(x) THEN
				x.SetArrayBase(ResolveType(x.arrayBase));
				ASSERT(x.arrayBase # NIL); (* must be guaranteed by parser *)
				IF x.length # NIL THEN
					x.SetLength(ConstantIntegerGeq0(x.length));
				END;
				arrayBase := x.arrayBase.resolved;
				IF arrayBase = Global.invalidType THEN
					(* error already handled *)
				ELSIF arrayBase IS SyntaxTree.ArrayType THEN
					Error(x.position,Diagnostics.Invalid,"forbidden array mixed form");
				ELSIF arrayBase IS SyntaxTree.MathArrayType THEN
					IF (x.form = SyntaxTree.Tensor) OR (arrayBase(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor) THEN
						Error(x.position,Diagnostics.Invalid,"forbidden Tensor Array mix")
					ELSIF (x.form=SyntaxTree.Static) & (arrayBase(SyntaxTree.MathArrayType).form # SyntaxTree.Static) THEN
						Error(x.position,Diagnostics.Invalid,"forbidden static array of dynamic array")
					END;
				END;
				IF x.form = SyntaxTree.Static THEN
					x.SetIncrement(system.SizeOf(arrayBase));
				END;
				x.SetState(SyntaxTree.Resolved);
			END;
			resolvedType := ResolvedType(x);
		END VisitMathArrayType;

		(* anonymous type declarations are used for variables that use an anonymous type. They are not used for records that are
			pointed to by a pointer to record. The following diagram shows the possible cases for records and pointer to records.

			(1) Rec = RECORD ... END;					Ptr		<--->		Rec
				Ptr = POINTER TO Rec;						^				 |
																|				 |
															TypeDesc			TypeDesc


			(2)	Obj = POINTER TO RECORD .. END;		Obj		<--->		Record
																^				/
																|			   /
															TypeDesc	<-- /
		*)

		PROCEDURE AnonymousTypeDeclaration(x: SyntaxTree.Type; CONST prefix: ARRAY OF CHAR);
		VAR typeDeclaration: SyntaxTree.TypeDeclaration; name,number: Scanner.StringType;
		BEGIN
			Strings.IntToStr(x.position,number);
			COPY(prefix,name);
			Strings.Append(name,"@");
			Strings.Append(name,number);
			typeDeclaration := SyntaxTree.NewTypeDeclaration(x.position,SyntaxTree.NewIdentifier(InvalidPosition,name));
			typeDeclaration.SetDeclaredType(x);
			typeDeclaration.SetAccess(SyntaxTree.Hidden);
			x.SetTypeDeclaration(typeDeclaration);
			currentScope.AddTypeDeclaration(typeDeclaration);
			typeDeclaration.SetScope(currentScope);
		END AnonymousTypeDeclaration;


		(**
			deferred pointer type resolving
			- resolve base type
			- check that base type is a record or array type
			- if error then set base type to invalid type
		**)
		PROCEDURE FixPointerType(type: SyntaxTree.PointerType);
		VAR resolved: SyntaxTree.Type; position: LONGINT;
		BEGIN
			ASSERT(type.pointerBase # NIL);
			position := type.pointerBase.position;
			IF (type.pointerBase IS SyntaxTree.RecordType) THEN (* direct POINTER TO RECORD *)
				type.pointerBase(SyntaxTree.RecordType).SetPointerType(type);
				(* not for pointers, a type is needed for the records only
				IF type.typeDeclaration = NIL THEN
					AnonymousTypeDeclaration(type);
				END;
				*)
			END;
			resolved := ResolveType(type.pointerBase);
			IF (resolved.resolved IS SyntaxTree.RecordType) OR (resolved.resolved IS SyntaxTree.ArrayType) THEN
				type.SetPointerBase(resolved);
			ELSE
				Error(position,Diagnostics.Invalid,"forbidden pointer base type");
				type.SetPointerBase(Global.invalidType)
			END
		END FixPointerType;

		(**
			resolve pointer type
			- enter pointer type to list of deferred fixes (to avoid infinite loops in the declaration phase)
		**)
		PROCEDURE VisitPointerType(x: SyntaxTree.PointerType);
		VAR recordType: SyntaxTree.RecordType; recordBaseType: SyntaxTree.Type;
		BEGIN
			IF TypeNeedsResolution(x) THEN
				(* inheritance cycle check
					example:
					A=POINTER TO RECORD(B) END;
					B=POINTER TO RECORD(A) END;
				*)
				IF x.pointerBase IS SyntaxTree.RecordType THEN
					recordType := x.pointerBase(SyntaxTree.RecordType);
					recordBaseType := ResolveType(recordType.baseType);
					recordType.SetBaseType(recordBaseType);
				END;
				typeFixes.Add(x,currentScope);
				x.SetState(SyntaxTree.Resolved);
			END;
			resolvedType := ResolvedType(x)
		END VisitPointerType;

		(**
			deferred procedure type resolving
			- resolve return type
			- traverse and resolve parameters
		**)
		PROCEDURE FixProcedureType(procedureType: SyntaxTree.ProcedureType);
		VAR resolved: SyntaxTree.Type; returnParameter,parameter (*,selfParameter*): SyntaxTree.Parameter;

		BEGIN
				resolved := ResolveType(procedureType.returnType);

				IF (resolved # NIL) & (resolved.resolved IS SyntaxTree.ArrayType) & (resolved.resolved(SyntaxTree.ArrayType).length = NIL) THEN
					Error(procedureType.position,Diagnostics.Invalid,"forbidden open array return type");
				END;

				procedureType.SetReturnType(resolved);

				IF (resolved # NIL) & (resolved IS SyntaxTree.MathArrayType) THEN
					(*! RET should be replaced by better name, procedure name for example ? *)
					parameter := SyntaxTree.NewParameter(procedureType.position,procedureType,Global.ResultName, SyntaxTree.VarParameter);
					parameter.SetType(procedureType.returnType);
					parameter.SetAccess(SyntaxTree.Internal);
					VisitParameter(parameter);
					procedureType.SetReturnParameter(parameter);
				END;

				(* process parameters *)
				parameter :=procedureType.firstParameter;
				WHILE (parameter # NIL) DO
					VisitParameter(parameter);
					parameter := parameter.nextParameter;
				END;

				IF (procedureType.flags * {SyntaxTree.CFlag,SyntaxTree.WinAPIFlag} = {} ) & (procedureType.returnType # NIL) & ContainsPointer(procedureType.returnType) THEN (*! needed for compatibility with paco *)
					returnParameter := SyntaxTree.NewParameter(procedureType.position,procedureType,Global.PointerReturnName,SyntaxTree.VarParameter);
					returnParameter.SetType(procedureType.returnType);
					returnParameter.SetAccess(SyntaxTree.Hidden);
					procedureType.AddParameter(returnParameter);
				END;

				system.GenerateParameterOffsets(procedureType,FALSE);
		END FixProcedureType;

		PROCEDURE FlagByIdentifier(identifier: SyntaxTree.Identifier): LONGINT;
		VAR name: Scanner.StringType;
		BEGIN
			IF identifier = NIL THEN RETURN MIN(LONGINT)
			ELSE
				identifier.GetString(name);
				Basic.Uppercase(name,name);
				IF (name = Global.StringWinAPI) THEN RETURN  SyntaxTree.WinAPIFlag
				ELSIF (name = Global.StringC)  THEN RETURN  SyntaxTree.CFlag
				ELSIF (name = Global.StringUntraced) THEN RETURN SyntaxTree.UntracedFlag
				ELSIF (name = Global.StringDelegate) THEN RETURN  SyntaxTree.DelegateFlag
				ELSIF (name = Global.StringRealtime) THEN RETURN SyntaxTree.RealtimeFlag
				ELSE Error(identifier.position,Diagnostics.Invalid,"Unknown Flag"); RETURN MIN(LONGINT);
				END;
			END;
		END FlagByIdentifier;

		(**
			convert a flag identifier to a (checker module local) flag
		**)
		PROCEDURE Flag(flagList: SyntaxTree.Modifier; allowedFlags: SET): LONGINT;
		VAR thisFlag: LONGINT;
		BEGIN
			thisFlag := MIN(LONGINT);
			IF flagList = NIL THEN (* no flag *)
			ELSIF flagList.nextModifier # NIL THEN (* too many flags *)
				Error(flagList.nextModifier.identifier.position,Diagnostics.Invalid,"too many flags: only one flag allowed");
			ELSE
				thisFlag := FlagByIdentifier(flagList.identifier);
				IF ~(thisFlag IN allowedFlags) THEN  Error(flagList.identifier.position, Basic.IllegalyMarkedIdentifier,"") END;
			END;
			RETURN thisFlag
		END Flag;

		PROCEDURE Flags(flagList: SyntaxTree.Modifier; allowedFlags: SET): SET;
		VAR flags: SET; flag: LONGINT;
		BEGIN
			flags := {};
			WHILE flagList # NIL DO
				flag := FlagByIdentifier(flagList.identifier);
				IF flag > 0 THEN
					IF  ~(flag IN allowedFlags) THEN Error(flagList.identifier.position,Basic.IllegalyMarkedIdentifier,"")
					ELSE
						INCL(flags,flag);
						IF flag = SyntaxTree.WinAPIFlag THEN allowedFlags := allowedFlags - {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag,SyntaxTree.DelegateFlag}
						ELSIF flag = SyntaxTree.CFlag THEN allowedFlags := allowedFlags - {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag,SyntaxTree.DelegateFlag}
						ELSIF flag = SyntaxTree.DelegateFlag THEN allowedFlags := allowedFlags - {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag,SyntaxTree.DelegateFlag}
						END;
					END;
				END;
				flagList := flagList.nextModifier;
			END;
			RETURN flags;
		END Flags;

		(**
			resolve procedure type
			- enter procedure to list of deferred fixes (to avoid infinite loops in the declaration phase)
		**)
		PROCEDURE VisitProcedureType(x: SyntaxTree.ProcedureType);
		VAR flags: SET;
		BEGIN
			IF TypeNeedsResolution(x) THEN
				flags := Flags(x.flagList,{SyntaxTree.WinAPIFlag,SyntaxTree.CFlag,SyntaxTree.DelegateFlag,SyntaxTree.RealtimeFlag});
				x.AddFlags(flags);

				typeFixes.Add(x,currentScope);
				x.SetState(SyntaxTree.Resolved);
			END;
			resolvedType := ResolvedType(x)
		END VisitProcedureType;

		(** check and resolve record type
			- check base type: must be record
			- check declarations
			- every record type is guaranteed to have a type declaration in the module scope (anonymous or not)
		**)
		PROCEDURE VisitRecordType(x: SyntaxTree.RecordType);
		VAR resolved, baseType: SyntaxTree.Type; position: LONGINT;
			numberMethods: LONGINT; recordBase: SyntaxTree.RecordType; procedure: SyntaxTree.Procedure;
			symbol: SyntaxTree.Symbol;
		BEGIN
			IF TypeNeedsResolution(x) THEN
				IF x.baseType # NIL THEN
					position := x.baseType.position;
					baseType := ResolveType(x.baseType);
					resolved := baseType.resolved;
					IF resolved = Global.invalidType THEN
						(* error already handled *)
					ELSIF (resolved = Global.Object) & (x.pointerType # NIL) THEN
						baseType := NIL;
					ELSIF (resolved IS SyntaxTree.PointerType) & (resolved(SyntaxTree.PointerType).pointerBase.resolved # NIL) &  (resolved(SyntaxTree.PointerType).pointerBase.resolved IS SyntaxTree.RecordType) & (x.pointerType # NIL) THEN
					ELSIF ~(resolved IS SyntaxTree.RecordType) THEN
						Error(position,Diagnostics.Invalid,"record extends a non-record")
					ELSIF (resolved IS SyntaxTree.RecordType) & (resolved(SyntaxTree.RecordType).isObject) THEN
						Error(position,Diagnostics.Invalid,"record extends an object")
					END;
					x.SetBaseType(baseType);
					IF x.Level() > 15 THEN
						Error(position,Diagnostics.Invalid,"record inheritance level too high");
						(* note:
							the restriction to inheritance with a maximum level of 15 is caused by the implementation of the
							runtime structures: type tests are very efficient and rely on the fact that each type descriptor contains the whole
							inheritance history of a type.
							Example: let inhertitance oe given by B(A), C(B), D(C) etc.
							Then the type descriptor of G contains: A|B|C|D|E|F|G|0|0|0...
							while the type decriptor of D contains: A|B|C|D|0|0|0|0|0|0...
						*)
					END;
				END;
				Declarations(x.recordScope);

				(* computation of sizes and offsets skipped -> done in backend / system *)

				recordBase := x.GetBaseRecord();
				IF recordBase # NIL THEN
					x.IsProtected(x.isProtected OR recordBase.isProtected);
				END;

				IF recordBase = NIL THEN numberMethods := 0
				ELSE numberMethods := recordBase.recordScope.numberMethods
				END;

				symbol := x.recordScope.firstSymbol; (* sorted symbols, important to go through procedures in a sorted way here !*)
				WHILE symbol # NIL DO
					IF symbol IS SyntaxTree.Procedure THEN
						procedure := symbol(SyntaxTree.Procedure);
						IF procedure.super # NIL THEN
							procedure.SetMethodNumber(procedure.super.methodNumber)
						ELSE
							procedure.SetMethodNumber(numberMethods);
							INC(numberMethods);
						END;
					END;
					symbol := symbol.nextSymbol;
				END;
				(*
				procedure := x.recordScope.firstProcedure;
				WHILE (procedure # NIL) DO
					IF procedure.super # NIL THEN
						procedure.SetMethodNumber(procedure.super.methodNumber)
					ELSE
						procedure.SetMethodNumber(numberMethods);
						INC(numberMethods);
					END;
					procedure := procedure.nextProcedure;
				END;
				*)
				x.recordScope.SetNumberMethods(numberMethods);

				(*! testing
				recordBase := x;
				WHILE recordBase # NIL DO
					IF recordBase.typeDeclaration # NIL THEN
						D.Str0(recordBase.typeDeclaration.name.name);D.Ln;
					ELSE
						D.Str("no type decl"); D.Ln;
					END;
					symbol := recordBase.recordScope.firstSymbol;
					WHILE symbol # NIL DO
						IF symbol IS SyntaxTree.Procedure THEN
							D.String("procedure ");
							D.Str0(symbol.name.name);
							D.String(" : ");
							D.Int(symbol(SyntaxTree.Procedure).methodNumber,1);
							D.Ln;
						END;
						symbol := symbol.nextSymbol
					END;
					recordBase := recordBase.GetBaseRecord();
				END;
				*)

				IF (x.isObject) & (x.baseType # NIL) & ~(x.baseType.resolved IS SyntaxTree.PointerType) THEN
					Error(x.position,Diagnostics.Invalid,"object extends a record");
				END;

				IF (x.typeDeclaration = NIL) THEN
					IF (x.pointerType # NIL) & (x.pointerType.resolved.typeDeclaration # NIL) THEN
						x.SetTypeDeclaration(x.pointerType.resolved.typeDeclaration);
						(*
						x.pointerType.resolved.typeDeclaration.name.GetString(name);
						AnonymousTypeDeclaration(x,name);
						*)
					ELSE
						AnonymousTypeDeclaration(x,"Anonymous");
					END;
				END;
				x.SetState(SyntaxTree.Resolved);
			END;
			resolvedType := ResolvedType(x);
		END VisitRecordType;



		(** resolve all pending types (late resolving).
			- type fixes are resolved at the end of the declaration phase
			- type fixes may imply new type fixes that are also entered at the end of the list
		**)
		PROCEDURE FixTypes;
		VAR p: ANY; prevScope: SyntaxTree.Scope;
		BEGIN
			prevScope := currentScope;
			p := typeFixes.Get(currentScope);
			WHILE p # NIL DO
				ASSERT(currentScope # NIL);
				ASSERT(p IS SyntaxTree.Type);

				IF p IS SyntaxTree.PointerType THEN
					FixPointerType(p(SyntaxTree.PointerType))
				ELSIF p IS SyntaxTree.ProcedureType THEN
					FixProcedureType(p(SyntaxTree.ProcedureType))
				ELSE
					HALT(100);
				END;
				p := typeFixes.Get(currentScope);
			END;
			currentScope :=prevScope;
		END FixTypes;

		(**
			resolve type x
			- if x is nil then return nil
			- if x cannot be resolved then the result is invalidType else the result is x
			- the resolved type is entered into x.resolved
		**)
		PROCEDURE ResolveType(x: SyntaxTree.Type): SyntaxTree.Type;
		VAR prev,resolved: SyntaxTree.Type;
		BEGIN
			prev := resolvedType;
			resolvedType := Global.invalidType;
			IF x = NIL THEN resolvedType := NIL
			ELSE x.Accept(SELF); ASSERT(resolvedType # NIL); (* in error cases it must be invalidType *)
			END;
			resolved := resolvedType;
			resolvedType := prev;

			ASSERT((resolved = NIL) OR (resolved.resolved # NIL));

			RETURN resolved
		END ResolveType;

		(*** compatibility rules ***)

		(**
			return a regular type: if type is invalid, NIL, importType or typeDeclarationType then return invalidType else return type
		**)
		PROCEDURE RegularType(position: LONGINT; type: SyntaxTree.Type): SyntaxTree.Type;
		VAR result: SyntaxTree.Type;
		BEGIN
			result := Global.invalidType;
			IF type = NIL THEN Error(position,Diagnostics.Invalid,"expression of type NIL");
			ELSIF type = Global.invalidType THEN (* error already handled *)
			ELSIF type.resolved = SyntaxTree.importType THEN Error(position,Diagnostics.Invalid,"expression is an import");
			ELSIF type.resolved = SyntaxTree.typeDeclarationType THEN Error(position,Diagnostics.Invalid,"expression is a type");
			ELSE result := type.resolved
			END;
			RETURN result
		END RegularType;

		(** returns signature compatibility of procedure types this and to
			- if not compatible then error is reported
			- compatibility means type equality
		**)
		PROCEDURE SignatureCompatible(position: LONGINT; this, to: SyntaxTree.ProcedureType): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := SameType(to,this,NIL);
			IF ~result THEN
				Error(position,Diagnostics.Invalid,"signature incompatible");
				IF VerboseErrorMessage THEN
					Printout.Info("this",this);
					Printout.Info("to",to);
				END;
			ELSIF (SyntaxTree.RealtimeFlag IN to(SyntaxTree.ProcedureType).flags) & ~(SyntaxTree.RealtimeFlag IN this(SyntaxTree.ProcedureType).flags) THEN
				Error(position,Diagnostics.Invalid,"signature incompatible: realtime flag must be inherited");
			END;
			RETURN result
		END SignatureCompatible;

		(** check parameter compatibility for expressions of the form P(actual) where P = PROCEDURE([VAR|CONST] formal)
			- for var parameters compatibility means same type except for
				- formal is of open array of system byte
				- formal is of record type
				- formal is of open array type
				- formal is of open math array type
			- for value parameters compatibllity means assignment compatibility except for
				- formal is of open array type
			if compatible the return true else report error and return false
		**)
		PROCEDURE ParameterCompatible(formal: SyntaxTree.Parameter; actual: SyntaxTree.Expression): BOOLEAN;
		VAR formalType, actualType: SyntaxTree.Type; result,error: BOOLEAN;
		BEGIN
			formalType := RegularType(formal.position,formal.type);
			actualType := RegularType(actual.position,actual.type);
			error := FALSE;

			IF actualType = Global.invalidType THEN (* error already handled *)
			ELSIF formal.kind = SyntaxTree.VarParameter THEN

				IF (SyntaxTree.WinAPIFlag IN formal.procedureType.flags) & (actualType = Global.Nil) THEN
					result := TRUE; (* special rule for WINAPI parameters, needed to be able to pass NIL address to var parameters *)
				ELSIF ~IsVariable(actual) THEN
					result := FALSE; error := TRUE;
					Error(actual.position,Diagnostics.Invalid,"is not a variable");
					IF VerboseErrorMessage THEN
						Printout.Info("actual",actual);
						Printout.Info("formal",formal);
					END;
				ELSIF (formalType = Global.Byte) OR (formalType IS SyntaxTree.RecordType) & (~formalType(SyntaxTree.RecordType).isObject) THEN
					result := CompatibleTo(actualType,formalType);
				ELSIF (formalType IS SyntaxTree.ArrayType) & (formalType(SyntaxTree.ArrayType).form = SyntaxTree.Open) THEN
					result := OpenArrayCompatible(formalType(SyntaxTree.ArrayType),actualType);
				ELSIF (formalType IS SyntaxTree.MathArrayType) THEN
					result := MathArrayCompatible(formalType(SyntaxTree.MathArrayType),actualType);
					IF result & (actualType(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor) & (formalType(SyntaxTree.MathArrayType).form # SyntaxTree.Tensor) THEN
						Error(actual.position,Diagnostics.Invalid,"incompatible tensor (use a range expression)");
					END;
				ELSE
					result := SameType(actualType,formalType,NIL)
				END
			ELSE
				IF (formalType IS SyntaxTree.CharacterType) & (actualType IS SyntaxTree.StringType) & (actualType(SyntaxTree.StringType).length = 2) THEN
					actualType := Global.Char;
				END;
				IF (SyntaxTree.WinAPIFlag IN formal.procedureType.flags) &  (actualType = Global.Nil) THEN
					result := TRUE; (* special rule for WINAPI parameters *)
				ELSIF (formalType IS SyntaxTree.ArrayType) & (formalType(SyntaxTree.ArrayType).form = SyntaxTree.Open) THEN
					result := OpenArrayCompatible(formalType(SyntaxTree.ArrayType),actualType);
				ELSE
					result := CompatibleTo(actualType,formalType)
				END;
			END;
			IF ~result & ~error THEN
				Error(actual.position,Diagnostics.Invalid,"incompatible parameter");
				IF VerboseErrorMessage THEN
					Printout.Info("actual",actual);
					Printout.Info("formal",formal);
				END;
			END;
			RETURN result
		END ParameterCompatible;

		(** check compatibility for expressions of the form left := right
			- if compatible then return true else error report and return false
			- check if left is variable
			- check compatiblity
		**)
		PROCEDURE AssignmentCompatible(VAR left: SyntaxTree.Designator; right: SyntaxTree.Expression): BOOLEAN;
		VAR leftType,rightType: SyntaxTree.Type; VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			leftType := RegularType(left.position,left.type);
			rightType := RegularType(right.position,right.type);

			IF (leftType IS SyntaxTree.CharacterType) & (rightType IS SyntaxTree.StringType) & (rightType(SyntaxTree.StringType).length = 2) THEN
				rightType := Global.Char; (* conversion character "x" -> string "x" *)
			END;

			IF (leftType = Global.invalidType) OR (rightType = Global.invalidType) THEN
				(* error already handled *)
				result := TRUE;
			ELSIF ~IsVariable(left) THEN
				Error(left.position,Diagnostics.Invalid,"is not a variable");
				IF VerboseErrorMessage THEN
					Printout.Info("left",left);
					Printout.Info("right",right);
				END;
			ELSIF ~CompatibleTo(rightType,leftType) THEN
				Error(left.position,Diagnostics.Invalid,"incompatible assignment");
				IF VerboseErrorMessage THEN
					Printout.Info("left",left);
					Printout.Info("right",right);
				END;
			ELSIF (right IS SyntaxTree.SymbolDesignator) & (right(SyntaxTree.SymbolDesignator).symbol IS SyntaxTree.Procedure) &
				(right(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.Procedure).scope IS SyntaxTree.ProcedureScope) THEN
				Error(right.position,Diagnostics.Invalid,"forbidden assignment of a nested procedure");
			ELSE
				result := TRUE
			END;
			RETURN result
		END AssignmentCompatible;

		(*** values  ***)

		(** check and resolve integer value **)
		PROCEDURE VisitIntegerValue(value: SyntaxTree.IntegerValue);
		VAR hugeint: HUGEINT;
		BEGIN
			hugeint := value(SyntaxTree.IntegerValue).hvalue;
			value.SetType(Global.GetIntegerType(system,hugeint));
			resolvedExpression := value
		END VisitIntegerValue;

		(** check and resolve real value **)
		PROCEDURE VisitRealValue(value: SyntaxTree.RealValue);
		VAR subtype: LONGINT; type: SyntaxTree.Type;
		BEGIN
			subtype := value(SyntaxTree.RealValue).subtype;
			IF subtype = Scanner.Real THEN
				type := Global.Real
			ELSIF subtype = Scanner.Longreal THEN
				type := Global.Longreal
			ELSE
				HALT(100)
			END;
			value.SetType(type);
			resolvedExpression := value
		END VisitRealValue;

		(** check and resolve set value **)
		PROCEDURE VisitSetValue(value: SyntaxTree.SetValue);
		BEGIN
			value.SetType(Global.Set);
			resolvedExpression := value
		END VisitSetValue;

		(** check and resolve set value **)
		PROCEDURE VisitMathArrayValue(value: SyntaxTree.MathArrayValue);
		BEGIN
			value.SetType(Global.invalidType);
			resolvedExpression := value
		END VisitMathArrayValue;

		(** check and resolve boolean value **)
		PROCEDURE VisitBooleanValue(value: SyntaxTree.BooleanValue);
		BEGIN
			value.SetType(Global.Boolean);
			resolvedExpression := value
		END VisitBooleanValue;

		(** check and resolve string value **)
		PROCEDURE VisitStringValue(value: SyntaxTree.StringValue);
		BEGIN
			value.SetType(ResolveType(SyntaxTree.NewStringType(value.position,value.length)));
			resolvedExpression := value
		END VisitStringValue;

		(** check and resolve character value **)
		PROCEDURE VisitCharacterValue(value: SyntaxTree.CharacterValue);
		BEGIN
			value.SetType(Global.Char);
			resolvedExpression := value
		END VisitCharacterValue;

		(** check and resolve nil value **)
		PROCEDURE VisitNilValue(value: SyntaxTree.NilValue);
		BEGIN
			value.SetType(Global.Nil);
			resolvedExpression := value
		END VisitNilValue;

		(** check and resolve enumerator value **)
		PROCEDURE VisitEnumeratorValue(value: SyntaxTree.EnumeratorValue);
		BEGIN
			value.SetType(value.enumerator.type);
			resolvedExpression := value
		END VisitEnumeratorValue;

		(*** expressions ***)

		(** check and resolve a Set expression of the form {element | range, element | range, ...}
			- check all elements on integer type
			- if element or range is constant, then check lower and upper bound
			- if all elements constant then return constant set value else return set expression (via global variable resolvedExpression)
			if an error occurs then report error and return invalidExpression
		**)
		PROCEDURE VisitSet(set: SyntaxTree.Set);
		VAR i: LONGINT; element: SyntaxTree.Expression; constant: BOOLEAN; elements: SyntaxTree.ExpressionList; s: SET;
		result: SyntaxTree.Expression; type: SyntaxTree.Type; value: SyntaxTree.Value;

			PROCEDURE CheckElement(element: SyntaxTree.Expression): SyntaxTree.Expression;
			VAR leftInteger, rightInteger: LONGINT;  left,right: SyntaxTree.Expression; elementResult: SyntaxTree.Expression;
			BEGIN
				elementResult := ResolveExpression(element); (* implies checking of subexpressions in binary expressions *)
				IF (elementResult IS SyntaxTree.RangeExpression) THEN
					left := elementResult(SyntaxTree.RangeExpression).from; right := elementResult(SyntaxTree.RangeExpression).to;
					left := NewConversion(left.position,left,Global.Longint);
					right := NewConversion(right.position,right,Global.Longint);
					elementResult(SyntaxTree.RangeExpression).SetFrom(left);
					elementResult(SyntaxTree.RangeExpression).SetTo(right);
					ASSERT(elementResult(SyntaxTree.RangeExpression).by = NIL); (* must be guaranteed by parser *)
					ASSERT(left.type.resolved = right.type.resolved); (* guaranteed by VisitRangeExpression *)
					type := left.type.resolved;
				ELSE
					left := elementResult; right := elementResult;
					type := elementResult.type.resolved;
					elementResult := NewConversion(left.position,left,Global.Longint);
				END;

				IF ~(type IS SyntaxTree.IntegerType) THEN
					Error(left.position,Diagnostics.Invalid,"wrong type in set");
					elementResult := Global.invalidExpression;
					constant := FALSE;
				ELSE
					IF IsIntegerValue(left,leftInteger) & IsIntegerValue(right,rightInteger) THEN
						IF (leftInteger<0) OR (leftInteger > MAX(SET)) THEN
							Error(left.position,Diagnostics.Invalid,"not allowed set integer value");
							IF (rightInteger<0) OR (rightInteger > MAX(SET)) THEN
								Error(right.position,Diagnostics.Invalid,"not allowed set integer value");
							END;
						ELSIF (rightInteger<0) OR (rightInteger > MAX(SET)) THEN
							Error(right.position,Diagnostics.Invalid,"not allowed set integer value");
						ELSE
							s := s + {leftInteger..rightInteger};
							(* same but more explicit:
							WHILE (leftInteger <= rightInteger) DO
								INCL(s,leftInteger);
								INC(leftInteger);
							END;
							*)
						END;
					ELSE
						constant := FALSE;
					END;
				END;
				RETURN elementResult;
			END CheckElement;

		BEGIN
			result := set; constant := TRUE; s := {}; elements := set.elements;
			IF elements # NIL THEN
				FOR i := 0 TO elements.Length()-1 DO
					element := elements.GetExpression(i);
					element := CheckElement(element);
					IF element = Global.invalidExpression THEN
						result := Global.invalidExpression
					END;
					elements.SetExpression(i,element);
				END;
			END;
			IF constant THEN
				value := SyntaxTree.NewSetValue(set.position,s);
				value.SetType(Global.Set);
				result.SetResolved(value);
			END;
			(* optimization possible
				convert {a,b,1,2,3,4,c,d} into {a,b,c,d} + {1,2,3,4}
				left this to the programmer...
			*)
			result.SetType(Global.Set);
			resolvedExpression := result;
		END VisitSet;

		(*!
		old variant: quite generic but needs better conversion handling, do this?

		PROCEDURE VisitMathArrayExpression(x: SyntaxTree.MathArrayExpression);
		VAR type: SyntaxTree.Type; position,numberElements,i: LONGINT; expression: SyntaxTree.Expression; isValue: BOOLEAN;
			value: SyntaxTree.MathArrayValue; arrayType: SyntaxTree.MathArrayType;
		BEGIN
			type := NIL;
			numberElements := x.elements.Length();
			FOR i := 0 TO numberElements-1 DO
				expression := x.elements.GetExpression(i);
				position := expression.position;
				expression := ResolveExpression(x.elements.GetExpression(i));
				x.elements.SetExpression(i,expression);
				IF type = NIL THEN
					type := expression.type;
				ELSIF CompatibleTo(expression.type,type) THEN
					(* ok *)
				ELSIF CompatibleTo(type,expression.type) THEN
					type := expression.type
				ELSE
					Error(expression.position,Diagnostics.Invalid, "incompatible element types");
					type := Global.invalidType;
				END;
			END;
			isValue := TRUE;
			FOR i := 0 TO numberElements-1 DO
				expression := NewConversion(position,x.elements.GetExpression(i),type);
				x.elements.SetExpression(i,expression);
				isValue := isValue & (expression.resolved # NIL);
			END;
			arrayType := SyntaxTree.NewMathArrayType(x.position,NIL, SyntaxTree.Static);
			arrayType.SetArrayBase(type);
			arrayType.SetLength(Global.NewIntegerValue(system,NewIntegerValue(system,rElements));
			IF isValue THEN
				value := SyntaxTree.NewMathArrayValue(position);
				value.SetElements(x.elements);
				x.SetResolved(value);
			END;
			x.SetType(arrayType);
			resolvedExpression := x;
		END VisitMathArrayExpression;
		*)

		PROCEDURE VisitMathArrayExpression(x: SyntaxTree.MathArrayExpression);
		VAR type: SyntaxTree.Type; isValue: BOOLEAN;
			value: SyntaxTree.MathArrayValue; arrayType: SyntaxTree.Type;

			PROCEDURE RecursivelyFindType(x: SyntaxTree.MathArrayExpression);
			VAR position,numberElements,i: LONGINT; expression: SyntaxTree.Expression;
			BEGIN
				numberElements := x.elements.Length();
				FOR i := 0 TO numberElements-1 DO
					expression := x.elements.GetExpression(i);
					IF expression IS SyntaxTree.MathArrayExpression THEN
						RecursivelyFindType(expression(SyntaxTree.MathArrayExpression))
					ELSE
						position := expression.position;
						expression := ResolveExpression(x.elements.GetExpression(i));
						x.elements.SetExpression(i,expression);
						IF type = NIL THEN
							type := expression.type;
						ELSIF CompatibleTo(expression.type,type) THEN
							(* ok *)
						ELSIF CompatibleTo(type,expression.type) THEN
							type := expression.type
						ELSE
							Error(expression.position,Diagnostics.Invalid, "incompatible element types");
							type := Global.invalidType;
						END;
					END;
				END;
			END RecursivelyFindType;

			PROCEDURE RecursivelySetExpression(x: SyntaxTree.MathArrayExpression);
			VAR position,numberElements,i: LONGINT; expression: SyntaxTree.Expression;
			BEGIN
				numberElements := x.elements.Length();
				FOR i := 0 TO numberElements-1 DO
					expression := x.elements.GetExpression(i);
					IF expression IS SyntaxTree.MathArrayExpression THEN
						RecursivelySetExpression(expression(SyntaxTree.MathArrayExpression));
					ELSE
						position := expression.position;
						expression := NewConversion(position,x.elements.GetExpression(i),type);
						x.elements.SetExpression(i,expression);
						isValue := isValue & (expression.resolved # NIL);
					END;
				END;
			END RecursivelySetExpression;

			PROCEDURE RecursivelySetType(x: SyntaxTree.MathArrayExpression): SyntaxTree.Type;
			VAR position,numberElements,i,size,gsize: LONGINT; baseType: SyntaxTree.Type;expression: SyntaxTree.Expression;
				arrayType: SyntaxTree.MathArrayType;
			BEGIN
				numberElements := x.elements.Length();
				baseType := NIL;
				gsize := 0;
				FOR i := 0 TO numberElements-1 DO
					expression := x.elements.GetExpression(i);
					IF expression IS SyntaxTree.MathArrayExpression THEN
						size := expression(SyntaxTree.MathArrayExpression).elements.Length();
						IF i=0 THEN
							gsize := size;
							baseType := RecursivelySetType(expression(SyntaxTree.MathArrayExpression));
						ELSIF (baseType = type) OR (gsize # size) THEN  Error(expression.position,Diagnostics.Invalid, "invalid array dimensions");
						ELSE expression.SetType(baseType)
						END;
					ELSIF baseType = NIL THEN baseType := type;
					ELSIF baseType # type THEN Error(expression.position,Diagnostics.Invalid, "invalid array dimensions");
					END;
				END;
				arrayType := SyntaxTree.NewMathArrayType(x.position,NIL, SyntaxTree.Static);
				arrayType.SetArrayBase(baseType);
				arrayType.SetLength(Global.NewIntegerValue(system,x.position,numberElements));
				RETURN ResolveType(arrayType);
			END RecursivelySetType;


		BEGIN
			type := NIL;
			RecursivelyFindType(x);
			isValue := TRUE;
			RecursivelySetExpression(x);
			arrayType := RecursivelySetType(x);
			x.SetType(arrayType);
			IF isValue THEN
				value := SyntaxTree.NewMathArrayValue(x.position);
				value.SetArray(x);
				x.SetResolved(value);
				value.SetType(arrayType);
			END;
			x.SetType(arrayType);
			resolvedExpression := x;
		END VisitMathArrayExpression;

		(** check and resolve unary expression **)
		PROCEDURE VisitUnaryExpression(unaryExpression: SyntaxTree.UnaryExpression);
		VAR
			left: SyntaxTree.Expression;
			int: HUGEINT; real: LONGREAL; set: SET; operator: LONGINT;
			bool: BOOLEAN;
			result: SyntaxTree.Expression; type: SyntaxTree.Type; operatorCall: SyntaxTree.Expression;
			value: SyntaxTree.Value;
		BEGIN
			type := Global.invalidType;
			left := ResolveExpression(unaryExpression.left);
			unaryExpression.SetLeft(left);
			operator := unaryExpression.operator;
			result := unaryExpression;
			IF ~system.operatorDefined[operator] THEN
				Error(left.position,Diagnostics.Invalid,"Operator Not Defined");
			END;
			IF  ~(left.type.resolved IS SyntaxTree.BasicType) THEN
				operatorCall := NewOperatorCall(unaryExpression.position, operator,left,NIL,Global.All);
			END;
			IF operatorCall # NIL THEN
				result := operatorCall;
				type := operatorCall.type;
				(* admissible operators
					Minus		number, set
					Not			boolean
				*)
			ELSE
				CASE unaryExpression.operator OF
				|Scanner.Minus:
					IF left.type.resolved IS SyntaxTree.IntegerType THEN
						IF left.resolved # NIL THEN
							int := -left.resolved(SyntaxTree.IntegerValue).hvalue;
							value := SyntaxTree.NewIntegerValue(unaryExpression.position,int);
							result.SetResolved(value);
							type := Global.GetIntegerType(system,int);
							value.SetType(type);
						ELSE
							type := left.type
						END
					ELSIF left.type.resolved IS SyntaxTree.FloatType THEN
						IF IsRealValue(left,real) THEN
							value := SyntaxTree.NewRealValue(unaryExpression.position,-real);
							result.SetResolved(value);
							type := left.type;
							value.SetType(type);
						ELSE
							type := left.type;
						END;
					ELSIF left.type.resolved = Global.Set THEN
						IF IsSetValue(left,set) THEN
							value := SyntaxTree.NewSetValue(unaryExpression.position,-set);
							result.SetResolved(value);
							type := left.type;
							value.SetType(type);
						ELSE
							type := left.type;
						END;
					ELSE
						Error(left.position,Diagnostics.Invalid,"unary operator not applicable");
					END;
				|Scanner.Not:
					IF left.type.resolved = Global.Boolean THEN
						IF IsBooleanValue(left,bool)  THEN
							value := SyntaxTree.NewBooleanValue(unaryExpression.position,~bool);
							result.SetResolved(value);
							type := Global.Boolean;
							value.SetType(type);
						ELSE
							type := Global.Boolean;
						END;
					ELSE
						Error(left.position,Diagnostics.Invalid,"unary operator not applicable");
					END;
				|Scanner.Plus:
					IF (left.type.resolved IS SyntaxTree.NumberType) THEN
						result := left; type := left.type;
					ELSE
						Error(left.position,Diagnostics.Invalid,"unary operator not applicable");
					END;
				END;
			END;
			result.SetType(type);
			resolvedExpression := result
		END VisitUnaryExpression;

		PROCEDURE MathArrayConversion(expression: SyntaxTree.Expression; type: SyntaxTree.Type): SyntaxTree.Expression;
		VAR
			result: SyntaxTree.Expression;

			PROCEDURE BaseType(type: SyntaxTree.Type): SyntaxTree.Type;
			BEGIN
				type := type.resolved;
				WHILE(type IS SyntaxTree.MathArrayType) DO
					type := type(SyntaxTree.MathArrayType).arrayBase.resolved;
				END;
				RETURN type
			END BaseType;

		BEGIN
			result := Global.invalidExpression;
			IF (BaseType(expression.type.resolved) = BaseType(type)) OR (BaseType(type)=Global.All) THEN
				result := expression (* do not convert *)
			ELSE (* should the search for operators be restricted to the ArrayBase module here ? *)
				result := NewOperatorCall(expression.position,Global.Conversion,expression,NIL,type);
				IF result = NIL THEN
					result := Global.invalidExpression;
					Error(expression.position,Diagnostics.Invalid,"incompatible conversion");
					IF VerboseErrorMessage THEN
						Printout.Info("expression",expression);
						Printout.Info("type",type);
					END;
				END;
			END;
			RETURN result
		END MathArrayConversion;


		PROCEDURE ConvertValue(position: LONGINT; expression: SyntaxTree.Value; type: SyntaxTree.Type): SyntaxTree.Expression;
		VAR result: SyntaxTree.Expression; int: HUGEINT; real: LONGREAL; set: SET; char: CHAR; string: Scanner.StringType;
		BEGIN
			result := expression; type := type.resolved;
			IF expression IS SyntaxTree.IntegerValue THEN
				int := expression(SyntaxTree.IntegerValue).hvalue;
				IF (type = Global.Shortint) OR (type = Global.Integer) OR (type = Global.Longint) OR (type= Global.Hugeint) 
					OR (type = system.sizeType) THEN
					int := Global.Trim(int,system.SizeOf(type)); 
					result := SyntaxTree.NewIntegerValue(position,int);
					result.SetType(type);
				ELSIF (type = Global.Address) THEN
					IF int < 0 THEN Error(position,Diagnostics.Invalid,"negative value cannot be converted to address") END;
					int := Global.Trim(int,system.SizeOf(type)); 
					result := SyntaxTree.NewIntegerValue(position,int);
					result.SetType(type);					
				ELSIF (type= Global.Real) OR (type= Global.Longreal) THEN
					result := SyntaxTree.NewRealValue(expression.position,int);
					result.SetType(type);
				ELSIF (type = Global.Set) THEN
					result := SyntaxTree.NewSetValue(expression.position,SYSTEM.VAL(SET,int));
					result.SetType(type);
				ELSIF (type = Global.Char) OR (type = Global.Byte) THEN
					result := SyntaxTree.NewCharacterValue(expression.position,SYSTEM.VAL(CHAR,int));
					result.SetType(type);
				ELSE
					Error(position,Diagnostics.Invalid,"integer value cannot be converted");
					result := Global.invalidExpression;
					IF VerboseErrorMessage THEN
						Printout.Info("expression",expression);
						Printout.Info("type",type);
					END;
				END;
			ELSIF IsRealValue(expression,real) THEN
				IF (type = Global.Shortint) OR (type = Global.Integer) OR (type = Global.Longint) THEN
					int := ENTIER(real);
					IF type = Global.Shortint THEN int := SHORT(SHORT(SHORT(int)))
					ELSIF type= Global.Integer THEN int := SHORT(SHORT(int))
					ELSIF type = Global.Longint THEN int := SHORT(int)
					END;
					result := SyntaxTree.NewIntegerValue(expression.position,int);
					result.SetType(type);
				ELSIF (type = Global.Hugeint) THEN
					int := ENTIERH(real);
					result := SyntaxTree.NewIntegerValue(expression.position,int);
					result.SetType(type);
				ELSIF (type= Global.Real) OR (type= Global.Longreal) THEN
					result := SyntaxTree.NewRealValue(position,real);
					result.SetType(type);
				ELSE
					Error(position,Diagnostics.Invalid,"real value cannot be converted");
					result := Global.invalidExpression;
				END;
			ELSIF IsSetValue(expression,set) THEN
				IF (type = Global.Shortint) OR (type = Global.Integer) OR (type = Global.Longint) OR (type= Global.Hugeint) THEN
					result := SyntaxTree.NewIntegerValue(expression.position,SYSTEM.VAL(LONGINT,set));
					result.SetType(type);
				ELSIF (type = Global.Char) OR (type = Global.Byte) THEN (* for example: possible via ch = CHR(SYSTEM.VAL(LONGINT,set)) *)
					result := SyntaxTree.NewCharacterValue(expression.position,SYSTEM.VAL(CHAR,set));
					result.SetType(type);
				ELSE
					Error(position,Diagnostics.Invalid,"set value cannot be converted");
					result := Global.invalidExpression;
				END;
			ELSIF IsStringValue(expression,string) THEN
				IF ((type = Global.Char) OR (type = Global.Byte)) & (string[1]=0X) THEN
					result := SyntaxTree.NewCharacterValue(expression.position,string[0]);
					result.SetType(type);
				ELSIF (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).arrayBase.resolved = Global.Char) THEN (* nothing to be done *)
				ELSE
					Error(position,Diagnostics.Invalid,"string value cannot be converted");
					result := Global.invalidExpression;
				END;
			ELSIF IsCharacterValue(expression,char) THEN
				IF (type IS SyntaxTree.StringType) OR (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).arrayBase.resolved = Global.Char) THEN
					string[0] := char; string[1] := 0X;
					type := SyntaxTree.NewStringType(InvalidPosition,2);
					result := SyntaxTree.NewStringValue(expression.position,string);
					result.SetType(type);
				ELSIF (type=Global.Byte) THEN
					(* do not simply set the new type as this could invalidate types of constants *)
					result := SyntaxTree.NewCharacterValue(expression.position,char);
					result.SetType(type)
				ELSIF (type = Global.Shortint) OR (type = Global.Integer) OR (type = Global.Longint) OR (type= Global.Hugeint) THEN
					result := SyntaxTree.NewIntegerValue(expression.position,SYSTEM.VAL(LONGINT,char));
					result.SetType(type);
				ELSIF (type = Global.Set) THEN
					result := SyntaxTree.NewSetValue(expression.position,SYSTEM.VAL(SET,char));
					result.SetType(type);
				ELSIF (type = Global.Char) THEN
					result := SyntaxTree.NewCharacterValue(expression.position,char);
					result.SetType(type);
				ELSE
					Error(position,Diagnostics.Invalid,"character value cannot be converted");
					result := Global.invalidExpression;
				END;
			ELSIF expression IS SyntaxTree.NilValue THEN
				result := expression;
				(* nothing to be done *)
			ELSIF expression IS SyntaxTree.MathArrayValue THEN
				result := MathArrayConversion(expression,type);
			ELSIF expression IS SyntaxTree.EnumeratorValue THEN
				result := expression;
				(* nothing to be done *)
			ELSE
				Error(position,Diagnostics.Invalid,"expression cannot be converted");
				IF VerboseErrorMessage THEN
					Printout.Info("expression",expression);
					Printout.Info("type",type);
				END;
				result := Global.invalidExpression;
			END;
			RETURN result
		END ConvertValue;


		(**
			return a conversion of an expression to a given type
				- if expression is already of same type then return expression
				- if incompatible conversion then report error and return invalidExpression
		**)
		PROCEDURE NewConversion(position: LONGINT; expression: SyntaxTree.Expression; type: SyntaxTree.Type): SyntaxTree.Expression;
		VAR result: SyntaxTree.Expression; value: SyntaxTree.Expression; expressionList: SyntaxTree.ExpressionList; typeDeclaration: SyntaxTree.TypeDeclaration; typeSymbol: SyntaxTree.Designator;
		BEGIN
			type := type.resolved;

			ASSERT(type # NIL); ASSERT(~(type IS SyntaxTree.QualifiedType));
			result := expression;

			IF expression = Global.invalidExpression THEN (* error already handled *)
			ELSIF expression = NIL THEN (* NIL expression *)
			ELSIF expression.type = NIL THEN
				Error(position,Diagnostics.Invalid,"expression of type NIL cannot be converted");
			ELSIF expression.type.resolved = type THEN (* nothing to be done ! *)
			ELSIF (expression.type.resolved = Global.Any) & (type = Global.Object) THEN (*! symbol file problem: ANY and OBJECT cannot be distinguished  *)
			ELSIF (expression.type.resolved = Global.Object) & (type =Global.Any) THEN (*! symbol file problem *)
			ELSIF expression.resolved # NIL THEN (* value *)
				value := ConvertValue(position,expression.resolved(SyntaxTree.Value),type);
				IF expression.resolved # value THEN
					result.SetType(type);
				END;
				IF value IS SyntaxTree.Value THEN
					result.SetResolved(value(SyntaxTree.Value));
				END;
			ELSIF (type = Global.Byte) THEN (* do not convert *)
				expressionList := SyntaxTree.NewExpressionList();
				typeDeclaration := SyntaxTree.NewTypeDeclaration(expression.position,SyntaxTree.NewIdentifier(InvalidPosition,"@byte"));
				typeDeclaration.SetDeclaredType(type);
				typeSymbol := SyntaxTree.NewSymbolDesignator(InvalidPosition,NIL,typeDeclaration);
				typeSymbol.SetType(typeDeclaration.type);
				expressionList.AddExpression(typeSymbol); (* type declaration symbol skipped *)
				expressionList.AddExpression(expression);
				result := SyntaxTree.NewBuiltinCallDesignator(expression.position,Global.systemVal,expressionList);
				result.SetType(type);
			ELSIF (type IS SyntaxTree.MathArrayType) THEN
				IF expression.type.resolved IS SyntaxTree.MathArrayType THEN
					result := MathArrayConversion(expression,type);
				ELSE
					Error(expression.position,Diagnostics.Invalid,"cannot convert non array type to array type")
				END;
			ELSIF (expression.type.resolved IS SyntaxTree.MathArrayType) THEN
					Error(expression.position,Diagnostics.Invalid,"cannot convert array type to non-array type")
			ELSIF ~(type IS SyntaxTree.BasicType) & (expression.type.resolved # Global.Char) THEN
				(*skip, no conversion*)
			ELSIF (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).arrayBase.resolved = Global.Byte) THEN
				(* skip, no conversion *)
			ELSE
				result := SyntaxTree.NewConversion(expression.position,expression,type);
			END;
			RETURN result
		END NewConversion;

		(**
			convert operands left and right to a type that both operands are compatible with, if no such type exists then report error
		**)
		PROCEDURE ConvertOperands(VAR left,right: SyntaxTree.Expression);
		VAR leftType,rightType: SyntaxTree.Type;
		BEGIN
			IF left.type = NIL THEN Error(left.position,Diagnostics.Invalid,"no type")
			ELSIF right.type= NIL THEN Error(right.position,Diagnostics.Invalid,"no type")
			ELSE
				leftType := left.type.resolved; rightType := right.type.resolved;
				IF CompatibleTo(leftType,rightType) THEN
					left := NewConversion(left.position,left,right.type.resolved);
				ELSIF CompatibleTo(rightType,leftType) THEN
					right := NewConversion(right.position,right,left.type.resolved);
				ELSE
					Error(left.position,Diagnostics.Invalid,"incompatible operands");
				END;
			END;
		END ConvertOperands;

		(** find and return best operator matching to parameter list (nil, if none)
			- search current module scope and all (directly or indirectly) imported modules for matching operator
			- take operator with smalles distance, where signature distance is computed in procedure Distance
		**)
		PROCEDURE FindOperator*(operator: LONGINT; actualParameters: SyntaxTree.ExpressionList; returnType: SyntaxTree.Type): SyntaxTree.Operator;
		VAR bestOperator: SyntaxTree.Operator; bestDistance: LONGINT; import: SyntaxTree.Import; numberParameters: LONGINT; procedureType: SyntaxTree.ProcedureType;
			identifier: SyntaxTree.Identifier;

			PROCEDURE FindInScope(scope: SyntaxTree.ModuleScope; access: SET);
			VAR operator: SyntaxTree.Operator; distance,i: LONGINT;
			BEGIN
				operator := scope.firstOperator;
				WHILE(operator # NIL) DO
					IF (operator.name.Equals(identifier)) & (operator.access * access # {}) THEN
						procedureType := operator.type(SyntaxTree.ProcedureType);
						distance := Distance(procedureType,actualParameters);
						IF (distance < Infinity) THEN
							IF returnType # NIL THEN
								IF procedureType.returnType = NIL THEN
									distance := Infinity
								ELSE
									i := TypeDistance(returnType,procedureType.returnType,TRUE);
									IF i = Infinity THEN distance := Infinity ELSE INC(distance,i) END;
								END;
							ELSIF procedureType.returnType # NIL THEN
								distance := Infinity
							END;
						END;

						(*
						IF distance < Infinity THEN
							Printout.Info("potential operator",operator);
						ELSE
							Printout.Info("operator not possible",operator);
						END;
						*)

						IF distance < bestDistance THEN
							bestDistance := distance;
							bestOperator := operator;
						END;
					END;
					operator := operator.nextOperator;
				END;
				(*
				Printout.Info("taken operator",bestOperator);
				*)
			END FindInScope;

		BEGIN
			bestDistance := Infinity; bestOperator := NIL; numberParameters := actualParameters.Length();
			identifier := Global.GetIdentifier(operator,currentScope.ownerModule.case);
			FindInScope(currentScope.ownerModule.moduleScope,SyntaxTree.ReadOnly);
			import := currentScope.ownerModule.moduleScope.firstImport;
			WHILE (bestDistance > 0) & (import # NIL) DO
				IF import.module # NIL THEN
					identifier := Global.GetIdentifier(operator,import.module.case);
					FindInScope(import.module.moduleScope,SyntaxTree.Public);
				END;
				import := import.nextImport;
			END;
			RETURN bestOperator
		END FindOperator;

		PROCEDURE SetCurrentScope*(scope: SyntaxTree.Scope);
		BEGIN
			currentScope := scope;
		END SetCurrentScope;


		(**
			return a procedure call designator for the  best matching operator procedure of the form "op"(leftExpression,rightExpression) (if any)
			- find operator, if found then
				- if in other module then add import designator
				- create symbol designator for operator
			- if error then return invalidExpression, if no operator then return NIL
		**)
		PROCEDURE NewOperatorCall*(position: LONGINT; op: LONGINT; leftExpression,rightExpression: SyntaxTree.Expression; resultType: SyntaxTree.Type): SyntaxTree.Expression;
		VAR operator: SyntaxTree.Operator; import: SyntaxTree.Import; expression: SyntaxTree.Expression; designator: SyntaxTree.Designator;  result: SyntaxTree.Expression;
			actualParameters: SyntaxTree.ExpressionList;
		BEGIN
			IF (leftExpression = Global.invalidExpression) OR (rightExpression = Global.invalidExpression)  THEN
				result := Global.invalidExpression
			ELSIF (leftExpression = NIL) THEN
				result := NIL
			ELSE
				IF ~arrayBaseImported &
					((leftExpression # NIL) & (leftExpression.type # NIL) & (leftExpression.type.resolved IS SyntaxTree.MathArrayType)
				OR (rightExpression # NIL) & (rightExpression.type # NIL) & (rightExpression.type.resolved IS SyntaxTree.MathArrayType)) THEN
					IF ((op # Global.Len) OR (rightExpression = NIL)) & (op # Global.Dim) THEN
						ImportArrayBase(position);
						arrayBaseImported := TRUE;
					END;
				END;

				actualParameters := SyntaxTree.NewExpressionList();
				actualParameters.AddExpression(leftExpression);
				IF rightExpression # NIL THEN
					actualParameters.AddExpression(rightExpression)
				END;
				operator := FindOperator(op,actualParameters,resultType);

				IF operator # NIL THEN
					designator := NIL;
					IF operator.scope.ownerModule # currentScope.ownerModule THEN
						import := currentScope.ownerModule.moduleScope.firstImport;
						WHILE(import # NIL) & (import.module # operator.scope.ownerModule) DO
							import := import.nextImport;
						END;
						expression := NewSymbolDesignator(position,NIL,import);
						designator := expression(SyntaxTree.Designator);
					END;
					expression := NewSymbolDesignator(position,designator,operator);
					designator := expression(SyntaxTree.Designator);
					result := NewProcedureCallDesignator(position,designator,actualParameters);
				ELSE
					result := NIL;
				END;
			END;
			RETURN result
		END NewOperatorCall;

		(** check and resolve binary expression **)
		(*! clean up *)
		PROCEDURE VisitBinaryExpression(binaryExpression: SyntaxTree.BinaryExpression);
		VAR left,right,result: SyntaxTree.Expression;
			il,ir: LONGINT; rl,rr: LONGREAL; hl,hr: HUGEINT;bl,br: BOOLEAN; sl,sr: SET;  strl,strr: Scanner.StringType;
			cl,cr: CHAR;
			operator: LONGINT; operatorCall: SyntaxTree.Expression;
			type: SyntaxTree.Type;
			value: SyntaxTree.Value;

			PROCEDURE NewBool(v: BOOLEAN);
			BEGIN
				value := SyntaxTree.NewBooleanValue(binaryExpression.position,v);
				value.SetType(Global.Boolean);
				result.SetResolved(value);
				type := Global.Boolean;
			END NewBool;

			PROCEDURE NewSet(v: SET);
			BEGIN
				value := SyntaxTree.NewSetValue(binaryExpression.position,v);
				value.SetType(Global.Set);
				result.SetResolved(value);
				type := Global.Set;
			END NewSet;

			PROCEDURE NewInteger(v: HUGEINT; t: SyntaxTree.Type);
			BEGIN
				value := Global.NewIntegerValue(system,binaryExpression.position,v);
				(*
				value.SetType(t);
				*)
				result.SetResolved(value);
				type := value.type;
			END NewInteger;

			PROCEDURE NewReal(v: LONGREAL; t: SyntaxTree.Type);
			BEGIN
				value := SyntaxTree.NewRealValue(binaryExpression.position,v);
				value.SetType(t);
				result.SetResolved(value);
				type := t;
			END NewReal;


		BEGIN
			type := Global.invalidType;
			left := ResolveExpression(binaryExpression.left);
			right := ResolveExpression(binaryExpression.right);
			binaryExpression.SetLeft(left);
			binaryExpression.SetRight(right);

			result := binaryExpression;
			operator := binaryExpression.operator;
			IF ~system.operatorDefined[operator] THEN
				Error(left.position,Diagnostics.Invalid,"Operator Not Defined");
				result := Global.invalidExpression;
				RETURN
			END;
			IF left.type = NIL THEN
				Error(left.position,Diagnostics.Invalid,"Expression has no result type");
				result := Global.invalidExpression;
				RETURN;
			END;
			IF right.type = NIL THEN
				Error(right.position,Diagnostics.Invalid,"Expression has no result type");
				result := Global.invalidExpression;
				RETURN;
			END;
			IF (~(left.type.resolved IS SyntaxTree.BasicType) OR ~(right.type.resolved IS SyntaxTree.BasicType)) THEN
				operatorCall := NewOperatorCall(binaryExpression.position,operator,left,right,Global.All);
			END;

			IF operatorCall # NIL THEN
				result := operatorCall;
				type := operatorCall.type;

			(* admissible operators:

				Times, Plus, Minus			numeric		numeric		numeric
											set			set			set
				Slash 						numeric		numeric		real
											set			set			set
				Div , Mod					integer		integer		integer
				And, Or						bool		bool		bool
				Equal, Unequal 				basic		basic		bool
											pointer 		pointer 		bool
											object		object		bool
											record		record		bool
											string		string		bool
											enumerator enumerator	bool

				Less, LessEqual,
				Greater, GreaterEqual		numeric		numeric		bool
											enumerator	enumerator	bool

				In							integer		set			bool
				Is							pointer		type		bool
				 							object		type		bool
				 							record		type		bool

				 Upto: special abbreviation for a..b
			*)

			ELSIF (left.type = NIL) THEN
				Error(left.position,Diagnostics.Invalid,"type (left operand) = NIL in binary expression");
				D.Str("nil type in "); D.Type(left); D.Ln;
				result := Global.invalidExpression;
			ELSIF (right.type = NIL) THEN
				Error(right.position,Diagnostics.Invalid,"type (right operand) = NIL in binary expression");
				result := Global.invalidExpression;
			ELSIF (left.type.resolved = Global.invalidType) OR (right.type.resolved = Global.invalidType) THEN (* error already handled *)
				result := Global.invalidExpression;
			ELSIF operator = Scanner.Upto THEN (* left .. right: now solved as RangeExpression*)
				HALT(100);
			ELSIF operator = Scanner.Is THEN (* left IS right: now solved as IsExpression *)
				type := Global.Boolean;
				IF  ~(right.type.resolved = SyntaxTree.typeDeclarationType) THEN
					Error(right.position,Diagnostics.Invalid,"is not a type ");
				ELSIF ~IsTypeExtension(left.type.resolved, right(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType.resolved) THEN
					Error(binaryExpression.position,Diagnostics.Invalid,"is not a  type extension of ");
					IF VerboseErrorMessage THEN
						Printout.Info("left",left);
						Printout.Info("right",right);
					END;
				ELSIF left.type.resolved = right(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType.resolved THEN
					NewBool(TRUE)
				ELSIF right(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType.resolved = Global.Object THEN
					NewBool(TRUE);
				ELSIF IsUnextensibleRecord(left) THEN
					NewBool(FALSE)
				END
			ELSIF (right IS SyntaxTree.SymbolDesignator) & (right(SyntaxTree.SymbolDesignator).symbol IS SyntaxTree.TypeDeclaration) THEN
				Error(right.position,Diagnostics.Invalid,"must not be a type");
			ELSIF operator = Scanner.In THEN (* left IN right *)
				IF (left.type.resolved IS SyntaxTree.IntegerType) & (right.type.resolved=Global.Set) THEN
					IF IsIntegerValue(left,il) & IsSetValue(right,sr) THEN
						NewBool(il IN sr);
					ELSE
						IF left.type.resolved # Global.Longint THEN
							left := NewConversion(left.position, left, Global.Longint);
							binaryExpression.SetLeft(left)
						END;
						type := Global.Boolean;
					END
				ELSE
					Error(binaryExpression.position,Diagnostics.Invalid, "incompatible operands");
				END
			ELSIF (left.type.resolved IS SyntaxTree.ProcedureType) OR (right.type.resolved IS SyntaxTree.ProcedureType) THEN
				IF ~CompatibleTo(left.type.resolved,right.type.resolved) & ~CompatibleTo(right.type.resolved,left.type.resolved) THEN
					Error(binaryExpression.position,Diagnostics.Invalid,"incompatible operands");
				END;

				IF (operator = Scanner.Equal) OR (operator = Scanner.Unequal) THEN type := Global.Boolean
				ELSE  Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 1")
				END
			ELSIF IsPointerType(left.type.resolved) OR IsPointerType(right.type.resolved) THEN
				IF ~CompatibleTo(left.type.resolved,right.type.resolved) & ~CompatibleTo(right.type.resolved,left.type.resolved) THEN
				(* IsPointerType(left.type.resolved) OR ~IsPointerType(right.type.resolved) THEN *)
					Error(binaryExpression.position,Diagnostics.Invalid,"incompatible operands");
					IF VerboseErrorMessage THEN Printout.Info("left.type.resolved",left.type.resolved); Printout.Info("right",right.type.resolved) END
				ELSIF (operator = Scanner.Equal) OR (operator = Scanner.Unequal) THEN
					IF (left.type.resolved = Global.Nil) & (right.type.resolved = Global.Nil) THEN
						IF operator = Scanner.Equal THEN NewBool(TRUE) ELSE NewBool(FALSE) END;
					END;
					type := Global.Boolean;
				ELSE
					Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 3");
				END
			ELSIF (left.resolved# NIL) & (left.resolved IS SyntaxTree.NilValue) THEN Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined");
			ELSIF (right.resolved # NIL) & (right.resolved IS SyntaxTree.NilValue) THEN Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined");
			ELSIF IsStringType(left.type.resolved) & IsStringType(right.type.resolved) THEN		(* string ops*)
				IF IsStringType(left.type.resolved) & IsStringType(right.type.resolved) THEN	(*ok*)
					IF IsStringValue(left,strl) & IsStringValue(right,strr) THEN
						CASE operator OF
						|Scanner.Equal: NewBool(strl=strr);
						|Scanner.Unequal:NewBool(strl#strr);
						|Scanner.Less: NewBool(strl<strr);
						|Scanner.LessEqual: NewBool(strl<=strr);
						|Scanner.Greater:  NewBool(strl>strr);
						|Scanner.GreaterEqual: NewBool(strl>=strr);
						ELSE
							Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 4");
						END;
					END;
				ELSIF (operator = Scanner.Equal) OR (operator=Scanner.Unequal) OR (operator = Scanner.Less)
						OR (operator = Scanner.LessEqual) OR (operator = Scanner.Greater) OR (operator = Scanner.GreaterEqual) THEN
						type := Global.Boolean
				ELSE
					Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 5");
				END;
				IF (operator = Scanner.Equal) OR (operator=Scanner.Unequal)
					OR 	(operator = Scanner.Less) OR (operator = Scanner.LessEqual)
					OR (operator = Scanner.Greater) OR (operator = Scanner.GreaterEqual) THEN
					type := Global.Boolean;
				ELSE
					Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 6");
				END
			ELSIF (left.type.resolved IS SyntaxTree.EnumerationType) OR (right.type.resolved IS SyntaxTree.EnumerationType) THEN
				IF IsEnumerationExtension(left.type,right.type) OR IsEnumerationExtension(right.type,left.type) THEN
					IF (operator = Scanner.Equal) OR (operator = Scanner.Unequal) OR (operator = Scanner.Less) OR (operator = Scanner.LessEqual)
						OR (operator = Scanner.Greater) OR (operator = Scanner.GreaterEqual) THEN
						type := Global.Boolean
					ELSE
						Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined for enumerators");
					END;
				ELSE
					Error(binaryExpression.position,Diagnostics.Invalid,"operator not applicable between different enumerators");
				END;
			ELSIF (left.type.resolved IS SyntaxTree.BasicType) & (right.type.resolved IS SyntaxTree.BasicType)
				OR IsCharacterType(left.type.resolved) & IsCharacterType(right.type.resolved)
			THEN
				IF left.type.resolved # right.type.resolved THEN
					ConvertOperands(left,right); (* operands must be of the same type here *)
					binaryExpression.SetLeft(left);
					binaryExpression.SetRight(right);
					type := left.type.resolved;
				END;
				IF left.type.resolved # right.type.resolved THEN
					Error(binaryExpression.position,Diagnostics.Invalid,"conversion failed ?");
					IF VerboseErrorMessage THEN
						Printout.Info("left",left);
						Printout.Info("right",right);
					END;
				ELSIF (left.type.resolved IS SyntaxTree.IntegerType) THEN
					IF IsIntegerValue(right,ir) & (type # Global.Hugeint) THEN
						IF (ir=0) & ((operator = Scanner.Mod) OR (operator = Scanner.Div) OR (operator = Scanner.Slash)) THEN
							Error(binaryExpression.position,Diagnostics.Invalid,"division by zero");
						ELSIF (ir<0) & ((operator = Scanner.Mod) OR (operator = Scanner.Div))THEN
							Error(binaryExpression.position,Diagnostics.Invalid,"integer division by negative number");
						END;
					END;
					(* constant folding *)
					IF IsIntegerValue(left,il) & IsIntegerValue(right,ir)  & (type#Global.Hugeint) THEN
						CASE operator OF
						|Scanner.Plus: NewInteger(il+ir,left.type);
						|Scanner.Minus: NewInteger(il-ir,left.type);
						|Scanner.Times: NewInteger(il*ir,left.type);
						|Scanner.Slash:
							IF ir # 0 THEN
								NewReal(il/ir, Global.Real);
							END;
						|Scanner.Mod:
							IF ir > 0 THEN
								NewInteger(il MOD ir,left.type);
							END;
						|Scanner.Div:
							IF ir > 0 THEN
								NewInteger(il DIV ir,left.type);
							END;
						|Scanner.Equal: NewBool(il=ir);
						|Scanner.Unequal:NewBool(il#ir);
						|Scanner.Less: NewBool(il<ir);
						|Scanner.LessEqual: NewBool(il<=ir);
						|Scanner.Greater:  NewBool(il>ir);
						|Scanner.GreaterEqual: NewBool(il>=ir);
						ELSE Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 7");
						END;
					ELSIF IsIntegerValue(left,il) & IsIntegerValue(right,ir) & (type=Global.Hugeint) THEN
						hl := left.resolved(SyntaxTree.IntegerValue).hvalue;
						hr := right.resolved(SyntaxTree.IntegerValue).hvalue;
						CASE operator OF
						|Scanner.Plus: NewInteger(hl+hr,left.type);
						|Scanner.Minus: NewInteger(hl-hr,left.type);
						|Scanner.Times: NewInteger(hl*hr,left.type);
						|Scanner.Slash:
							IF hr = 0 THEN
								Error(binaryExpression.position,Diagnostics.Invalid,"division by zero");
							ELSE
								NewReal(hl/hr,Global.Longreal);
							END;
						(* do the bootstrapping for this kind of expression on hugeint values , then enable: *)
						|Scanner.Mod:
							IF hr = 0 THEN
								Error(binaryExpression.position,Diagnostics.Invalid,"division by zero");
							ELSE
								NewInteger(hl - Machine.DivH(hl,hr)*hr,left.type);
							END;
						|Scanner.Div:
							IF hr = 0 THEN
								Error(binaryExpression.position,Diagnostics.Invalid,"division by zero");
							ELSE
								NewInteger(Machine.DivH(hl,hr),left.type);
							END;
						(**)
						|Scanner.Equal: NewBool(hl=hr);
						|Scanner.Unequal: NewBool(hl#hr);
						|Scanner.Less: NewBool(hl<hr);
						|Scanner.LessEqual: NewBool(hl<=hr);
						|Scanner.Greater: NewBool(hl>hr);
						|Scanner.GreaterEqual:NewBool(hl>=hr);
						ELSE Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 8");
						END;
					ELSIF (operator = Scanner.Plus) OR (operator = Scanner.Minus) OR (operator = Scanner.Times) OR
					(operator = Scanner.Mod) OR (operator = Scanner.Div) THEN
						type := left.type
					ELSIF (operator = Scanner.Slash) THEN
						left := NewConversion(left.position,left,Global.Real);
						right := NewConversion(right.position,right,Global.Real);
						binaryExpression.SetLeft(left);
						binaryExpression.SetRight(right);
						type := Global.Real
					ELSIF (operator = Scanner.Equal) OR (operator = Scanner.Unequal) OR (operator = Scanner.Less) OR (operator = Scanner.LessEqual)
						OR (operator = Scanner.Greater) OR (operator = Scanner.GreaterEqual) THEN
						type := Global.Boolean
					ELSE
						Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 9");
					END;
				ELSIF (left.type.resolved IS SyntaxTree.FloatType) THEN
					IF IsRealValue(left,rl) & IsRealValue(right,rr) THEN
						CASE operator OF
						|Scanner.Plus: NewReal(rl+rr,left.type.resolved);
						|Scanner.Minus: NewReal(rl-rr,left.type.resolved);
						|Scanner.Times:NewReal(rl*rr,left.type.resolved);
						|Scanner.Slash:
							IF rr = 0 THEN
								Error(binaryExpression.position,Diagnostics.Invalid,"division by zero");
							ELSE
								NewReal(rl/rr,left.type.resolved);
							END
						|Scanner.Equal: NewBool(rl=rr);
						|Scanner.Unequal: NewBool(rl#rr);
						|Scanner.Less: NewBool(rl<rr);
						|Scanner.LessEqual:  NewBool(rl<=rr);
						|Scanner.Greater:  NewBool(rl>rr);
						|Scanner.GreaterEqual: NewBool(rl>=rr);
						ELSE Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 10");
						END;
					ELSIF (operator = Scanner.Plus) OR (operator = Scanner.Minus) OR (operator = Scanner.Times) OR (operator = Scanner.Slash) THEN
						type := left.type
					ELSIF (operator = Scanner.Equal) OR (operator = Scanner.Unequal) OR (operator = Scanner.Less) OR (operator = Scanner.LessEqual)
						OR (operator = Scanner.Greater) OR (operator = Scanner.GreaterEqual) THEN
						type := Global.Boolean
					ELSE
						Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 11");
						IF VerboseErrorMessage THEN
							Printout.Info("left",left);
							Printout.Info("right",right);
						END;
					END;
				ELSIF (left.type.resolved = Global.Boolean) THEN
					IF IsBooleanValue(left,bl) & IsBooleanValue(right,br) THEN
						CASE operator OF
						|Scanner.And: NewBool(bl & br);
						|Scanner.Or: NewBool(bl OR br);
						|Scanner.Equal: NewBool(bl = br);
						|Scanner.Unequal: NewBool(bl # br);
						ELSE Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 12");
						END;
					ELSIF (operator = Scanner.Equal) OR (operator = Scanner.Unequal) OR (operator = Scanner.And) OR (operator = Scanner.Or)  THEN
						type := Global.Boolean
					ELSE
						Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 13");
					END;
				ELSIF (left.type.resolved= Global.Set) THEN
					IF IsSetValue(left,sl) & IsSetValue(right,sr) THEN
						CASE operator OF
						|Scanner.Plus: NewSet(sl + sr);
						|Scanner.Minus:  NewSet(sl - sr);
						|Scanner.Times:  NewSet(sl * sr);
						|Scanner.Slash:  NewSet(sl / sr);
						|Scanner.Equal:  NewBool(sl=sr);
						|Scanner.Unequal: NewBool(sl#sr);
						|Scanner.Less: NewBool( (sl * sr = sl) & (sl#sr));
						|Scanner.LessEqual: NewBool(sl*sr = sl);
						|Scanner.Greater: NewBool( (sl * sr = sr) & (sl # sr));
						|Scanner.GreaterEqual: NewBool(sl*sr = sr);
						ELSE Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 14");
						END;
					ELSIF (operator = Scanner.Equal) OR (operator = Scanner.Unequal)
						OR (operator = Scanner.Less) OR (operator = Scanner.LessEqual)
						OR (operator = Scanner.Greater) OR (operator = Scanner.GreaterEqual)  (* implement inclusion *)
						THEN
						type := Global.Boolean
					ELSIF (operator = Scanner.Plus) OR (operator = Scanner.Minus) OR (operator = Scanner.Times) OR (operator = Scanner.Slash) THEN
						type := left.type
					ELSE
						Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 15");
					END;
				ELSIF IsCharacterType(left.type) THEN
					IF IsCharacterValue(left,cl) & IsCharacterValue(right,cr) THEN
						CASE operator OF
						|Scanner.Equal:  NewBool(cl=cr);
						|Scanner.Unequal: NewBool(cl#cr);
						|Scanner.Less: NewBool(cl<cr);
						|Scanner.LessEqual:  NewBool(cl<=cr);
						|Scanner.Greater:  NewBool(cl>cr);
						|Scanner.GreaterEqual: NewBool(cl>=cr);
						ELSE Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 16");
						END;
					ELSIF (operator = Scanner.Equal) OR (operator = Scanner.Unequal) OR (operator = Scanner.Less) OR (operator = Scanner.LessEqual)
						OR (operator = Scanner.Greater) OR (operator = Scanner.GreaterEqual) THEN
						type := Global.Boolean
					ELSE
						Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 17");
					END;
				ELSE
					Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 18");
				END;
			ELSE
				Error(binaryExpression.position,Diagnostics.Invalid,"operator not defined 19");
			END;
			IF type = Global.invalidType THEN
				result := Global.invalidExpression
			ELSE
				result.SetType(type)
			END;
			resolvedExpression := result
		END VisitBinaryExpression;

		(** resolve a range expression from .. to BY by
			- if from or to are not of integer type or character type error
			- if from and to type incompatible then error
			- if by # NIL and by of incompatible type then error
			if error then return invalidExpression else set range type
		**)
		PROCEDURE VisitRangeExpression(x: SyntaxTree.RangeExpression);
		VAR from,to,by: SyntaxTree.Expression; commonType: SyntaxTree.Type; result: SyntaxTree.Expression;
		BEGIN
			result := x;
			IF x.from # NIL THEN from := ResolveExpression(x.from) ELSE from := NIL END;
			IF x.to # NIL THEN to := ResolveExpression(x.to)  ELSE to := NIL END;
			IF x.by # NIL THEN by := ResolveExpression(x.by) ELSE by := NIL END;

			IF from = NIL THEN
			ELSIF ~(from.type.resolved IS SyntaxTree.IntegerType) & ~IsCharacterType(from.type) THEN
				Error(x.position,Diagnostics.Invalid,"forbidden lower range type");
				result := Global.invalidExpression;
			ELSIF (from IS SyntaxTree.StringValue) THEN
				from := ConvertValue(from.position,from(SyntaxTree.Value),Global.Char);
			END;
			IF to = NIL THEN
			ELSIF ~(to.type.resolved IS SyntaxTree.IntegerType) & ~IsCharacterType(to.type) THEN
				Error(to.position,Diagnostics.Invalid,"forbidden upper range type");
				result := Global.invalidExpression;
			ELSIF (to IS SyntaxTree.StringValue) THEN
				to := ConvertValue(to.position,to(SyntaxTree.Value),Global.Char);
			END;
			IF result # Global.invalidExpression THEN
				IF (from # NIL) & (to # NIL) THEN
					ConvertOperands(from,to);
					IF from.type.resolved # to.type.resolved THEN
						Error(x.position,Diagnostics.Invalid,"incompatible range operands");
						result := Global.invalidExpression;
					END;
					commonType := from.type;
				ELSE
					commonType := Global.Longint
				END;
				IF (by = NIL) OR CompatibleTo(by.type.resolved,commonType.resolved) THEN
					x.SetFrom(from); x.SetTo(to); x.SetBy(by);
					x.SetType(SyntaxTree.NewRangeType(x.position,NIL,commonType))
				ELSE
					Error(by.position,Diagnostics.Invalid,"incompatible increment in range");
					result := Global.invalidExpression;
				END;
			END;
			resolvedExpression := result
		END VisitRangeExpression;

		PROCEDURE VisitTensorRangeExpression(x: SyntaxTree.TensorRangeExpression);
		BEGIN
			x.SetType(NIL);
			resolvedExpression := x;
		END VisitTensorRangeExpression;


		(** resolve the expression d and return result as designator
			- resolve expression
			- if expression is a designator then return designator else error message and return invalidDesignator
		**)
		PROCEDURE ResolveDesignator(d: SyntaxTree.Expression): SyntaxTree.Designator;
		VAR result: SyntaxTree.Designator; resolved: SyntaxTree.Expression;
		BEGIN
			IF Trace THEN D.Str("ResolveDesignator"); D.Ln; END;
			resolved := ResolveExpression(d);
			IF resolved = Global.invalidExpression THEN
				(* error should already have been reported *)
				result := Global.invalidDesignator;
			ELSIF resolved IS SyntaxTree.Designator THEN
				result := resolved(SyntaxTree.Designator)
			ELSE
				 Error(d.position,Diagnostics.Invalid,"is no designator ! ");
				 result := Global.invalidDesignator;
			END;

			(* result.type might be nil.  *)
			RETURN result
		END ResolveDesignator;

		(**
			symbol designator generated in this module
			nothing to be resolved
		**)
		PROCEDURE VisitSymbolDesignator(x: SyntaxTree.SymbolDesignator);
		BEGIN
			resolvedExpression := x;
		END VisitSymbolDesignator;

		(**
			self designator generated in this module
			nothing to be resolved
		**)
		PROCEDURE VisitSelfDesignator(x: SyntaxTree.SelfDesignator);
		VAR scope: SyntaxTree.Scope; record: SyntaxTree.RecordType; type: SyntaxTree.Type;
		BEGIN
			(* check if in record scope *)
			scope := currentScope;
			WHILE (scope # NIL) & ~(scope IS SyntaxTree.RecordScope) DO
				scope := scope.outerScope;
			END;
			IF scope = NIL THEN (* in module scope *)
				x.SetType(Global.Any);
			ELSE (* in record scope *)
				record := scope(SyntaxTree.RecordScope).ownerRecord;
				IF (record # NIL) & (record.pointerType # NIL) THEN
					type := ResolveType(record.pointerType);
					x.SetType(type);
				ELSE
					x.SetType(record);
				END;
			END;
			resolvedExpression := x;
		END VisitSelfDesignator;

		(**
			return symbol designator as an expression
			- if symbol is a constant then return the constant value expression
			- else
				- if no left designator present then do auto-self if in record scope identifier-> SELF.identiifer
				- if symbol is a guarded variable then return a TypeGuardDesignator
				- else return a symbol designator
		**)
		PROCEDURE NewSymbolDesignator*(position: LONGINT; left: SyntaxTree.Designator; symbol: SyntaxTree.Symbol): SyntaxTree.Expression;
		VAR result,variableSymbol: SyntaxTree.Expression; guard: SyntaxTree.GuardedVariable; assignable: BOOLEAN; scope: SyntaxTree.Scope;
		BEGIN
			IF Trace THEN D.Str("NewSymbolDesignator "); D.Ln; END;
			result := Global.invalidExpression;
			ASSERT(symbol # NIL);
			(*
			not necessary any more since a type declaration is of type SyntaxTree.typeDeclarationType now
			IF symbol IS SyntaxTree.TypeDeclaration THEN
				Error(position,Diagnostics.Invalid,"type not allowed here");
			ELS *)

			(* not needed any more as values are stored in the expression
			IF symbol IS SyntaxTree.Constant THEN
				result := symbol(SyntaxTree.Constant).value
				IF symbol(SyntaxTree.Constant).value # NIL THEN
				IF symbol(SyntaxTree.Constant).value IS SyntaxTree.Value THEN
					result := symbol(SyntaxTree.Constant).value(SyntaxTree.Value).Copy(position);
				ELSE
					result := symbol(SyntaxTree.Constant).value
				END;
			ELSE
			*)
			IF (left = NIL) & (symbol.scope IS SyntaxTree.RecordScope) THEN
				left := ResolveDesignator(SyntaxTree.NewSelfDesignator(position)); (* auto self *)
				IF IsPointerType(left.type) THEN
					left := NewDereferenceDesignator(position,left)
				END;
			ELSIF (symbol.scope IS SyntaxTree.ProcedureScope) THEN
				scope := currentScope;
				WHILE (scope # NIL) & (scope # symbol.scope) & ~(scope IS SyntaxTree.RecordScope) DO
					scope := scope.outerScope;
				END;
				IF (scope # NIL) & (scope # symbol.scope) & ~(symbol IS SyntaxTree.Constant) THEN
					Error(position,Diagnostics.Invalid,"forbidden access to symbol in parent procedure scope");
				END;
			END;

			assignable := (left = NIL) OR left.assignable OR (left IS SyntaxTree.DereferenceDesignator);

			IF (symbol.scope.ownerModule # currentScope.ownerModule) THEN
				assignable := assignable & (SyntaxTree.PublicWrite IN symbol.access);
			ELSE
				assignable := assignable & (SyntaxTree.InternalWrite IN symbol.access);
			END;

			IF symbol IS SyntaxTree.GuardedVariable THEN
				guard := symbol(SyntaxTree.GuardedVariable);
				variableSymbol := NewSymbolDesignator(position,left,guard.variable);
				result := NewTypeGuardDesignator(position,variableSymbol(SyntaxTree.Designator),guard.type,guard.typeExpression);
			ELSE
				result := SyntaxTree.NewSymbolDesignator(position,left,symbol);
				result.SetType(symbol.type);
				result.SetAssignable(assignable);
				IF symbol IS SyntaxTree.Constant THEN
					result.SetResolved(symbol(SyntaxTree.Constant).value.resolved);
				ELSIF symbol IS SyntaxTree.Enumerator THEN
					result.SetResolved(symbol(SyntaxTree.Enumerator).value);
				END;
			END;

			ASSERT(result.type # NIL);
			RETURN result
		END NewSymbolDesignator;

		(** check and resolve an identifier designator "identifier"
			- if identifier = self then return SelfDesignator
			- else find symbol in current scope
				- if symbol found then return SymbolDesignator, else error message and return invalidDesignator
		**)
		PROCEDURE VisitIdentifierDesignator(identifierDesignator: SyntaxTree.IdentifierDesignator);
		VAR symbol: SyntaxTree.Symbol;
		BEGIN
			IF Trace THEN D.Str("VisitIdentifierDesignator "); D.Ln; END;
			symbol := Find(currentScope,identifierDesignator.identifier,TRUE);
			IF symbol # NIL THEN
				ResolveSymbol(symbol);
				ASSERT(symbol.type # NIL);
				resolvedExpression := NewSymbolDesignator(identifierDesignator.position,NIL,symbol);
			ELSE
				Error(identifierDesignator.position,Basic.UndeclaredIdentifier,"");
				IF VerboseErrorMessage THEN
					Printout.Info("undeclared identifier designator",identifierDesignator);
				END;
				resolvedExpression := Global.invalidDesignator;
			END;
		END VisitIdentifierDesignator;


		(** check and resolve a selector designator of the form left.designator
			- if left is a pointer type then do auto dereferenciation
			- left denotes a search scope:
				- if left type is import type then set search scope to respective module
				- if left type is enumeration type then set search scope to respective enumeration scope
				- elsif left type is record type then set search scope to record scope
			- search symbol in computed scope
			returns selector designator (via global variable resolvedExpression) if symbol found, else error message is given and invalidDesignator is returned
		**)
		PROCEDURE VisitSelectorDesignator(selectorDesignator: SyntaxTree.SelectorDesignator);
		VAR
			symbol: SyntaxTree.Symbol; left: SyntaxTree.Designator; scope: SyntaxTree.Scope;
			module: SyntaxTree.Module; result: SyntaxTree.Expression; type: SyntaxTree.Type;
		BEGIN
			IF Trace THEN D.Str("VisitSelectorDesignator"); D.Ln; END;
			left := ResolveDesignator(selectorDesignator.left);

			result := Global.invalidDesignator;
			IF left # NIL THEN
				IF (left.type # NIL) & IsPointerType(left.type.resolved) THEN
					left := NewDereferenceDesignator(selectorDesignator.position,left);
				END;

				scope := NIL;
				IF left.type = NIL THEN
					Error(selectorDesignator.position,Diagnostics.Invalid,"field on nil typed designator");
					IF VerboseErrorMessage THEN Printout.Info("nil typed designator",left) END;
				ELSIF left.type.resolved = Global.invalidType THEN (* error already handled *)
				ELSIF left.type.resolved = SyntaxTree.importType THEN
					symbol := left(SyntaxTree.SymbolDesignator).symbol;
					module := symbol(SyntaxTree.Import).module;
					IF module # NIL THEN
						scope := module.moduleScope
					ELSE
						Error(left.position,Diagnostics.Invalid,"module not loaded");
						IF VerboseErrorMessage THEN Printout.Info("unloaded module",symbol) END;
					END;
				ELSIF left.type.resolved IS SyntaxTree.RecordType THEN
					scope := left.type.resolved(SyntaxTree.RecordType).recordScope;
					ASSERT(scope # NIL)
				ELSIF left.type.resolved = SyntaxTree.typeDeclarationType THEN
					symbol := left(SyntaxTree.SymbolDesignator).symbol;
					type := symbol(SyntaxTree.TypeDeclaration).declaredType.resolved;
					IF type IS SyntaxTree.EnumerationType THEN
						scope := type(SyntaxTree.EnumerationType).enumerationScope;
					ELSE
						Error(selectorDesignator.position,Diagnostics.Invalid,"field on non-enumeration type declaration");
						IF VerboseErrorMessage THEN Printout.Info("non-record type designator",left) END;
					END;
				ELSE
					Error(selectorDesignator.position,Diagnostics.Invalid,"field on non-record type designator");
					IF VerboseErrorMessage THEN Printout.Info("non-record type designator",left) END;
				END;

				symbol := NIL;
				IF scope = NIL THEN
				ELSE
					symbol := Find(scope,selectorDesignator.identifier,FALSE (* do not visit nested scopes *));
					IF symbol # NIL THEN
						ResolveSymbol(symbol);
						result := NewSymbolDesignator(selectorDesignator.position,left,symbol);
					ELSE
						Error(selectorDesignator.position,Diagnostics.Invalid,"undeclared identifier (selector)");
						IF VerboseErrorMessage THEN
							Printout.Info("undeclared identifier",selectorDesignator);
							Printout.Info("left resolved designator",left);
						END
					END;
				END;

			END;
			resolvedExpression := result;
		END VisitSelectorDesignator;

		PROCEDURE IndexCheck(index,length: SyntaxTree.Expression);
		VAR len,idx: LONGINT;
		BEGIN
			IF (index # NIL) & IsIntegerValue(index,idx) THEN
				IF idx < 0 THEN
					Error(index.position,Diagnostics.Invalid,"index out of bounds (too small)")
				ELSE
					IF (length # NIL) & IsIntegerValue(length,len) & (idx >= len)  THEN
						Error(index.position,Diagnostics.Invalid,"index out of bounds (too large)");
					END;
				END;
			END;
		END IndexCheck;

		PROCEDURE SetIndexBaseType(index: SyntaxTree.IndexDesignator; type: SyntaxTree.Type);
		VAR m: SyntaxTree.MathArrayType;
		BEGIN
			IF index.type = NIL THEN
				index.SetType(type)
			ELSE (* index must be a math array type *)
				m := index.type(SyntaxTree.MathArrayType);
				WHILE (m.arrayBase # NIL) & (m.arrayBase IS SyntaxTree.MathArrayType) DO
					ASSERT(m#type);
					m := m.arrayBase(SyntaxTree.MathArrayType);
				END;
				ASSERT(m#type);
				m.SetArrayBase(type);
			END;
		END SetIndexBaseType;

		(** check and append index to indexer of math array
			- index check
			- compute new type
				- if range then create new array type
				- otherwise take over.arrayBase as new type
				- type is not only replaced but might have to be inserted when resolving expressions of the form A[*,i,j,*]
		**)
		PROCEDURE AppendMathIndex(position: LONGINT; index: SyntaxTree.IndexDesignator; expression: SyntaxTree.Expression; over: SyntaxTree.MathArrayType);
		VAR parameters: SyntaxTree.ExpressionList;
		range: SyntaxTree.RangeExpression; array: SyntaxTree.MathArrayType; from,to,by: SyntaxTree.Expression;
		fromvalue,tovalue,byvalue,length: LONGINT;
		BEGIN
			parameters := index.parameters;
			IF (expression.type = Global.invalidType) THEN (* error already handled *)
				parameters.AddExpression(expression);
			ELSIF expression IS SyntaxTree.TensorRangeExpression THEN
				parameters.AddExpression(expression);
				array := SyntaxTree.NewMathArrayType(position,NIL,SyntaxTree.Tensor);
				SetIndexBaseType(index,array);
				index.HasRange;
			ELSIF (expression.type.resolved IS SyntaxTree.IntegerType) THEN
				IndexCheck(expression,over.length);
				expression := NewConversion(InvalidPosition,expression,system.sizeType);
				parameters.AddExpression(expression);
			ELSIF (expression IS SyntaxTree.RangeExpression) THEN
				range := expression(SyntaxTree.RangeExpression);
				parameters.AddExpression(expression);
				array := SyntaxTree.NewMathArrayType(position,NIL,SyntaxTree.Open);
				SetIndexBaseType(index,array);
				index.HasRange;
				IF ~(expression.type.resolved(SyntaxTree.RangeType).commonType.resolved IS SyntaxTree.IntegerType) THEN
					Error(position,Diagnostics.Invalid,"non-integer range type");
				END;
				from := range.from; to := range.to; by := range.by;

				IF (from = NIL) THEN
					(* handled by backend
					from := Global.NewIntegerValue(system,position,0);
					range.SetFrom(from);
					*)
				ELSE IndexCheck(from,over.length)
				END;

				IF (to = NIL) THEN
					(* handled by backend
					IF (over.length # NIL) & IsIntegerValue(over.length,length)  THEN
						to := Global.NewIntegerValue(system,position,length-1);
						range.SetTo(to);
					END;
					*)
				ELSE IndexCheck(to,over.length)
				END;

				range.SetFrom(NewConversion(InvalidPosition,range.from,system.sizeType));
				range.SetTo(NewConversion(InvalidPosition,range.to,system.sizeType));

				IF (to # NIL) & IsIntegerValue(from,fromvalue) & IsIntegerValue(to,tovalue) & ((by = NIL) OR IsIntegerValue(by,byvalue)) THEN
					length := tovalue - fromvalue;
					INC(length);
					IF by # NIL THEN
						length := length DIV byvalue;
					END;
					array.SetLength(Global.NewIntegerValue(system,position,length));
				ELSE
					array.SetLength(over.length);
				END;
			ELSE
				Error(position,Diagnostics.Invalid,"invalid indexer");
			END;
		END AppendMathIndex;


		PROCEDURE AppendIndex(position: LONGINT; index: SyntaxTree.IndexDesignator; expression: SyntaxTree.Expression; over: SyntaxTree.ArrayType);
		VAR  parameters: SyntaxTree.ExpressionList;
		BEGIN
			parameters := index.parameters;
			IF (expression.type = NIL) THEN
				Error(position,Diagnostics.Invalid,"invalid index");
			ELSIF (expression.type.resolved IS SyntaxTree.IntegerType) THEN
				IndexCheck(expression,over.length);
				expression := NewConversion(InvalidPosition,expression,system.sizeType);
				parameters.AddExpression(expression);
			ELSE
				Error(position,Diagnostics.Invalid,"invalid index");
			END;
		END AppendIndex;

		(** check and semantically resolve a bracket designator of the form left[expression, ... , expression]
			- returns a (chain of) index designator(s)
				left[expression,expression,expression]^[expression,expression] ...
			- does auto-dereferenciation for each index designator

			Note that for mathematical arrays there can be a difference between
				A[ expression , expression ]
			and
				A[ expression ][ expression ].
			This is due to the fact that while A[x] is of the base type of A the expression A[*] is of an array type of the base type of A.
			Example:
			Let A: ARRAY [*,*] OF LONGINT;
			Here the expression A[*][i] is equivalent to A[i] while A[*,i] stands for the first column of the matrix A.

			Indexers are not chained as in older Oberon compilers, i.e. A[x,y,z] -> A[x][y][z] but rather the other way round:
			A[left][right] is translated to A[left,right] whenever possible (i.e. whenever there is no range between left and right).
			When autodereferenciation takes place then the indexers are separated:
			Let A: POINTER TO ARRAY OF POINTER TO ARRAY OF LONGINT;
			Here A[x,y] -> A^[x]^[y].

			Note that mathematical arrays of conventional arrays (vice versa) are forbidden by the type system.
			However pointers are permitted: ARRAY [10] OF POINTER TO ARRAY is a valid type.
		**)
		PROCEDURE VisitBracketDesignator(bracketDesignator: SyntaxTree.BracketDesignator);
		VAR left: SyntaxTree.Designator; expressionList: SyntaxTree.ExpressionList; i: LONGINT;
			expression: SyntaxTree.Expression; position: LONGINT;
			type: SyntaxTree.Type; index: SyntaxTree.IndexDesignator;
		BEGIN
			IF Trace THEN D.Str("VisitBracketDesignator"); D.Ln; END;
			position := bracketDesignator.position;
			expressionList := bracketDesignator.parameters;
			left := ResolveDesignator(bracketDesignator.left);
			type := left.type.resolved;

			IF (left IS SyntaxTree.IndexDesignator) & ~(left(SyntaxTree.IndexDesignator).hasRange) THEN
				index := left(SyntaxTree.IndexDesignator);
			ELSIF (type IS SyntaxTree.PointerType) THEN
				left := NewDereferenceDesignator(bracketDesignator.position,left);
				type := left.type.resolved;
				index := SyntaxTree.NewIndexDesignator(bracketDesignator.position,left);
				index.SetAssignable(left.assignable);
				left := index;
			ELSE
				index := SyntaxTree.NewIndexDesignator(bracketDesignator.position,left);
				index.SetAssignable(left.assignable);
			END;
			index.SetType(NIL); (* type will be re-set after indexer traversal *)
			left := index;

			FOR i := 0 TO expressionList.Length()-1 DO
				expression := expressionList.GetExpression(i);
				position := expression.position;
				expression := ResolveExpression(expression);
				IF (type IS SyntaxTree.PointerType) THEN
					IF (index.hasRange) THEN
						(* forbidden expression of the form A[*,...] over ARRAY [...] OF POINTER TO ARRAY OF ... *)
						Error(position,Diagnostics.Invalid,"forbidden range valued indexer over pointer to array");
						type := Global.invalidType;
						left := Global.invalidDesignator;
					ELSE
						(* expression of the form A[x,...] over ARRAY [...] OF POINTER TO ARRAY OF ... *)
						SetIndexBaseType(index,type);
						left := NewDereferenceDesignator(bracketDesignator.position,left);
						type := left.type.resolved;
						index := SyntaxTree.NewIndexDesignator(bracketDesignator.position,left);
						index.SetAssignable(left.assignable);
						left := index;
					END;
				END;

				IF type = Global.invalidType THEN (* error already handled *)
				ELSIF (type IS SyntaxTree.ArrayType) THEN
					(* index over array, can only be of the form [... x ...] *)
					AppendIndex(position,index,expression,type(SyntaxTree.ArrayType));
					type := type(SyntaxTree.ArrayType).arrayBase.resolved;
				ELSIF (type IS SyntaxTree.MathArrayType) THEN
					(* index over math array, might be [ ... x ... ] or [... x..y by z ....] *)
					AppendMathIndex(position,index,expression,type(SyntaxTree.MathArrayType));
					IF type(SyntaxTree.MathArrayType).form # SyntaxTree.Tensor THEN
						type := type(SyntaxTree.MathArrayType).arrayBase.resolved;
					END;
				ELSE
					Error(position,Diagnostics.Invalid,"indexed element is no array");
					type := Global.invalidType;
				END;
			END;
			IF (type IS SyntaxTree.MathArrayType) & (type(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor) THEN
				type := type(SyntaxTree.MathArrayType).arrayBase.resolved;
			END;
			IF type = Global.invalidType THEN (* error *)
				left := Global.invalidDesignator;
			ELSE
				SetIndexBaseType(index,type);
			END;
			resolvedExpression := left;
		END VisitBracketDesignator;

		(** check and resolve expression list
			- resolve each expression in an expression list
			- returns true if and only if all statements could have successfully been resolved
		**)
		PROCEDURE ExpressionList(expressionList: SyntaxTree.ExpressionList): BOOLEAN;
		VAR i: LONGINT; expression: SyntaxTree.Expression; result: BOOLEAN;
		BEGIN
			result := TRUE;
			FOR i := 0 TO expressionList.Length()-1 DO
				expression := ResolveExpression(expressionList.GetExpression(i));
				IF expression = Global.invalidExpression THEN result := FALSE END;
				expressionList.SetExpression(i,expression);
			END;
			RETURN result
		END ExpressionList;

		(** return procedure call designator left(actualParameters)
			- check realtime procedure call in realtime procedure
			- check number of parameters
			- check parameter compatibility
			return invalidDesignator if error
		**)
		PROCEDURE NewProcedureCallDesignator(position: LONGINT; left: SyntaxTree.Designator; actualParameters:SyntaxTree.ExpressionList): SyntaxTree.Designator;
		VAR result: SyntaxTree.Designator;
			numberFormalParameters, numberActualParameters: LONGINT;
			formalType: SyntaxTree.ProcedureType;
			formalParameter: SyntaxTree.Parameter;
			actualParameter: SyntaxTree.Expression;
			i: LONGINT;
			hiddenPointerDesignator: SyntaxTree.Designator;
		BEGIN
			IF Trace THEN D.Str("ProcedureCallDesignator"); D.Ln; END;
			result := Global.invalidDesignator;
			formalType := left.type.resolved(SyntaxTree.ProcedureType); (* type checked in VisitParameterDesignator *)
			numberFormalParameters := formalType.numberParameters-formalType.numberHiddenParameters;
			numberActualParameters := actualParameters.Length();

			IF (SyntaxTree.RealtimeFlag IN currentFlags) & ~(SyntaxTree.RealtimeFlag IN formalType.flags) THEN
				Error(position,Diagnostics.Invalid,"forbidden call of non-realtime procedure in realtime block");
			END;

			IF ~ExpressionList(actualParameters) THEN
				result := Global.invalidDesignator
			ELSE
				result := SyntaxTree.NewProcedureCallDesignator(position,left,actualParameters);
				result.SetAssignable(FALSE);
				result.SetType(left.type.resolved(SyntaxTree.ProcedureType).returnType);

				IF numberActualParameters = numberFormalParameters THEN
					formalParameter := formalType.firstParameter;
					FOR i := 0 TO numberActualParameters-1 DO
						actualParameter := actualParameters.GetExpression(i);
						IF (actualParameter = Global.invalidExpression) THEN
						ELSIF ~ParameterCompatible(formalParameter,actualParameter) THEN
						ELSE
							IF formalParameter.type.resolved # actualParameter.type.resolved THEN
								actualParameter := NewConversion(actualParameter.position,actualParameter,formalParameter.type);
							END;
							actualParameters.SetExpression(i,actualParameter);
						END;
						formalParameter := formalParameter.nextParameter;
					END;
				ELSIF numberActualParameters > numberFormalParameters THEN
					Error(position,Diagnostics.Invalid,"more actual than formal parameters")
				ELSE
					Error(position,Diagnostics.Invalid,"less actual than formal parameters")
				END;

				(*! do this in backend? *)
				IF ContainsPointer(formalType.returnType) & (formalType.flags * {SyntaxTree.CFlag,SyntaxTree.WinAPIFlag} = {} )THEN
					hiddenPointerDesignator := GetTemporaryVariable(formalType.returnType,position); (*! try to make reuse of pointers *)
					actualParameters.AddExpression(hiddenPointerDesignator);
				END;

			END;

			RETURN result
		END NewProcedureCallDesignator;

		(**
			builtin call designator generated in VisitParameterDesignator
			-> nothing to be resolved
		**)
		PROCEDURE VisitTypeGuardDesignator(x: SyntaxTree.TypeGuardDesignator);
		BEGIN
			resolvedExpression := x;
		END VisitTypeGuardDesignator;

		(**
			builtin call designator generated in VisitParameterDesignator
			-> nothing to be resolved
		**)
		PROCEDURE VisitBuiltinCallDesignator(x: SyntaxTree.BuiltinCallDesignator);
		BEGIN
			resolvedExpression := x;
		END VisitBuiltinCallDesignator;

		(**
			procedure call designator generated in VisitParameterDesignator
			-> nothing to be resolved
		**)
		PROCEDURE VisitProcedureCallDesignator(x: SyntaxTree.ProcedureCallDesignator);
		BEGIN
			resolvedExpression := x;
		END VisitProcedureCallDesignator;

		(** return true if x is a variable else return false and report error **)
		PROCEDURE CheckVariable(x: SyntaxTree.Expression): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := TRUE;
			IF x = Global.invalidExpression THEN
				result := FALSE;
			ELSIF ~IsVariable(x) THEN
				Error(x.position,Diagnostics.Invalid,"non variable expression");
				IF VerboseErrorMessage THEN Printout.Info("non variable",x) END;
				result := FALSE;
			END;
			RETURN result
		END CheckVariable;


		(**
			if expression x is of basic type then return true else report error and return false
		**)
		PROCEDURE CheckBasicType(x: SyntaxTree.Expression): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF ~IsBasicType(x.type) THEN
				Error(x.position,Diagnostics.Invalid,"is no basic type");
				result := FALSE
			ELSE result := TRUE
			END;
			RETURN result
		END CheckBasicType;


		(**
			if expression x is of number type then return true else report error and return false
		**)
		PROCEDURE CheckNumberType(x: SyntaxTree.Expression): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF ~(x.type.resolved IS SyntaxTree.NumberType) THEN
				Error(x.position,Diagnostics.Invalid,"is non number type");
			ELSE result := TRUE
			END;
			RETURN result
		END CheckNumberType;

		(**
			if expression x is of integer type then return true else report error and return false
		**)
		PROCEDURE CheckIntegerType(x: SyntaxTree.Expression): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF ~(x.type.resolved IS SyntaxTree.IntegerType) & (x.type.resolved # Global.Byte) THEN
				Error(x.position,Diagnostics.Invalid,"is no integer type");
			ELSE result := TRUE
			END;
			RETURN result
		END CheckIntegerType;

		(**
			if expression x is of character type then return true else report error and return false
		**)
		PROCEDURE CheckCharacterType(x: SyntaxTree.Expression): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF ~(x.type.resolved = Global.Char) & (x.type.resolved # Global.Byte) & ~IsCharacterType(x.type.resolved) THEN
				Error(x.position,Diagnostics.Invalid,"is no character type");
			ELSE result := TRUE
			END;
			RETURN result
		END CheckCharacterType;

		(**
			if expression x is of real type then return true else report error and return false
		**)
		PROCEDURE CheckRealType(x: SyntaxTree.Expression): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF ~(x.type.resolved IS SyntaxTree.FloatType) THEN
				Error(x.position,Diagnostics.Invalid,"is no float type");
			ELSE result := TRUE
			END;
			RETURN result
		END CheckRealType;

		(**
			if expression x is of boolean type then return true else report error and return false
		**)
		PROCEDURE CheckBooleanType(x: SyntaxTree.Expression): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF (x.type.resolved # Global.Boolean) THEN
				Error(x.position,Diagnostics.Invalid,"is no boolean type");
			ELSE result := TRUE
			END;
			RETURN result
		END CheckBooleanType;

		(**
			if expression x is of set type then return true else report error and return false
		**)
		PROCEDURE CheckSetType(x: SyntaxTree.Expression): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF (x.type.resolved # Global.Set) THEN
				Error(x.position,Diagnostics.Invalid,"is no set type");
			ELSE result := TRUE
			END;
			RETURN result
		END CheckSetType;

		(**
			if expression x is of string or array of character type then return true else report error and return false
		**)
		PROCEDURE CheckStringType(x: SyntaxTree.Expression): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF ~IsStringType(x.type.resolved) THEN
				Error(x.position,Diagnostics.Invalid,"is no string type");
			ELSE result := TRUE
			END;
			RETURN result
		END CheckStringType;

		(**
			if expression x is a type declaration type return true else report error and return false
		**)
		PROCEDURE CheckTypeDeclarationType(x: SyntaxTree.Expression): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF (x.type.resolved # SyntaxTree.typeDeclarationType) THEN
				Error(x.position,Diagnostics.Invalid,"is not a type declaration");
			ELSE result := TRUE
			END;
			RETURN result
		END CheckTypeDeclarationType;

		PROCEDURE CheckIntegerValue(x: SyntaxTree.Expression; VAR value: LONGINT): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF (x.resolved # NIL) & (x.resolved IS SyntaxTree.IntegerValue) THEN
				result := TRUE;
				value := x.resolved(SyntaxTree.IntegerValue).value;
			ELSE
				Error(x.position,Diagnostics.Invalid,"expression is not an integer constant");
			END;
			RETURN result;
		END CheckIntegerValue;

		PROCEDURE CheckCharacterValue(x: SyntaxTree.Expression; VAR value: CHAR): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF (x.resolved # NIL) & (x.resolved IS SyntaxTree.CharacterValue) THEN
				result := TRUE;
				value := x.resolved(SyntaxTree.CharacterValue).value;
			ELSIF (x.resolved # NIL) & (x.resolved IS SyntaxTree.StringValue) & (x.resolved(SyntaxTree.StringValue).length =2) THEN
				result := TRUE;
				value := x.resolved(SyntaxTree.StringValue).value[0];
			ELSE
				Error(x.position,Diagnostics.Invalid,"expression is not a character constant");
			END;
			RETURN result;
		END CheckCharacterValue;

		PROCEDURE CheckPositiveIntegerValue(x: SyntaxTree.Expression; VAR value: LONGINT; includeZero: BOOLEAN): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			IF x = Global.invalidExpression THEN
			ELSIF (x.resolved # NIL) & (x.resolved IS SyntaxTree.IntegerValue) THEN
				value := x.resolved(SyntaxTree.IntegerValue).value;
				IF (value > 0) OR includeZero & (value = 0)  THEN
					result := TRUE;
				ELSE
					Error(x.position,Diagnostics.Invalid,"integer is not positive");
				END
			ELSE
				Error(x.position,Diagnostics.Invalid,"expression is not an integer constant");
			END;
			RETURN result;
		END CheckPositiveIntegerValue;


		(* move to builtin procedure call statement ?
			remove builtin procedure call designator ?
		*)
		PROCEDURE NewBuiltinCallDesignator(position: LONGINT; builtin: SyntaxTree.Builtin; actualParameters:SyntaxTree.ExpressionList; left: SyntaxTree.Designator): SyntaxTree.Expression;
		VAR
			numberActualParameters,numberFormalParameters: LONGINT;
			formalParameter: SyntaxTree.Parameter;
			actualParameter: SyntaxTree.Expression;
			procedureType: SyntaxTree.ProcedureType;
			parameter0, parameter1, parameter2, result: SyntaxTree.Expression;
			constructor: SyntaxTree.Procedure;
			type0,type1,type2: SyntaxTree.Type;
			type,base: SyntaxTree.Type;
			arrayType: SyntaxTree.ArrayType;
			i,i0,i1: LONGINT;
			r,r0,r1: LONGREAL;
			c: CHAR;
			id: LONGINT;
			b: BOOLEAN;

			mathArrayType: SyntaxTree.MathArrayType;

			PROCEDURE Parameters(from,to: LONGINT): BOOLEAN;
			VAR resultB: BOOLEAN;
			BEGIN
				IF numberActualParameters < from THEN
					Error(position,Diagnostics.Invalid,"less actual than formal parameters");
					result := Global.invalidExpression;
					resultB := FALSE;
				ELSIF numberActualParameters > to THEN
					Error(position,Diagnostics.Invalid,"more actual than formal parameters");
					result := Global.invalidExpression;
					resultB := FALSE;
				ELSE
					resultB := TRUE;
				END;
				RETURN resultB
			END  Parameters;

		BEGIN
			type := NIL; result := NIL;

			numberActualParameters := actualParameters.Length();
			IF numberActualParameters>0 THEN
				parameter0 := actualParameters.GetExpression(0);
				type0 := parameter0.type.resolved;
			END;
			IF numberActualParameters >1 THEN
				parameter1 := actualParameters.GetExpression(1);
				type1 := parameter1.type.resolved;
			END;
			IF numberActualParameters >2 THEN
				parameter2 := actualParameters.GetExpression(2);
				type2 := parameter1.type.resolved;
			END;

			id := builtin.id;
			IF system.operatorDefined[id] THEN (* try to find overloaded operator *)
				result := NewOperatorCall(position,builtin.id,parameter0,parameter1,Global.All);
			END;

			IF result = Global.invalidExpression THEN (* error already handled *)
			ELSIF result # NIL THEN type := result.type (* operator *)
			ELSE
				result := SyntaxTree.NewBuiltinCallDesignator(position,id,actualParameters);
				result(SyntaxTree.Designator).SetLeft(left);
				(* ---- ASSERT ----- *)
				IF (id = Global.Assert) & Parameters(1,2)  THEN
					IF CheckBooleanType(parameter0) THEN
	(*					mk: Commented this out because Oberon 07 uses Assert(FALSE, trap) instead of HALT
						fof: commented in again as ASSERT is crucial for compilation tests, Oberon07 obviously needs a HALT statement
							misusing ASSERT does not make the language clearer nor odes it make the compiler simpler!
	*)
						IF IsBooleanValue(parameter0,b) & ~b & ~(SyntaxTree.UnreachableFlag IN currentFlags)  THEN
							Error(position,Diagnostics.Invalid,"assert failed");
						END;
						IF (numberActualParameters > 1) & CheckIntegerValue(parameter1,i1) THEN
							IF (i1<20) THEN
								Error(position,Diagnostics.Invalid,"too small parameter")
							END;
						END;
					END;
				(* ---- COPY ----- *)
				ELSIF (id = Global.Copy) & Parameters(2,2) THEN
					IF~IsStringType(type0) THEN
						Error(parameter0.position,Diagnostics.Invalid,"no string type");
					END;
					IF ~IsStringType(type1) THEN
						Error(parameter1.position,Diagnostics.Invalid,"no string type");
					ELSIF CheckVariable(parameter1) THEN
						IF (type0 IS SyntaxTree.StringType) THEN
							arrayType := type1(SyntaxTree.ArrayType);
							IF arrayType.form = SyntaxTree.Static THEN
								IF arrayType.staticLength < type0(SyntaxTree.StringType).length THEN
									Error(position,Diagnostics.Invalid,"destination length smaller than source length")
								END;
							END;
						END;
					END;
				(* ---- INC, DEC----- *)
				ELSIF ((id = Global.Dec) OR (id = Global.Inc)) & Parameters(1,2) THEN
					IF numberActualParameters = 1 THEN
						parameter1 :=Global.NewIntegerValue(system,position,1);
						actualParameters.AddExpression(parameter1);
					END;
					IF CheckVariable(parameter0) & CheckIntegerType(parameter0) & CheckIntegerType(parameter1) THEN
						IF ~CompatibleTo(parameter1.type,parameter0.type) THEN
							Error(position,Diagnostics.Invalid,"incompatible increment");
						ELSE
							parameter1 := NewConversion(0,parameter1,parameter0.type);
							actualParameters.SetExpression(1,parameter1);
						END;
					END;
				(* ---- EXCL, INCL----- *)
				ELSIF ((id = Global.Excl) OR (id = Global.Incl)) & Parameters(2,2) THEN
					IF CheckVariable(parameter0) & CheckSetType(parameter0) & CheckIntegerType(parameter1) THEN
						IF IsIntegerValue(parameter1,i0) THEN
							IF (i0 < MIN(SET)) OR (i0>MAX(SET)) THEN
								Error(position,Diagnostics.Invalid,"parameter out of SET range")
							END;
						END;
						parameter1 := NewConversion(0,parameter1,Global.Longint);
						actualParameters.SetExpression(1,parameter1);
					END;
				(* ---- HALT, SYSTEM.HALT ----- *)
				ELSIF ((id = Global.Halt) OR (id = Global.systemHalt)) & Parameters(1,1) THEN
					IF CheckPositiveIntegerValue(parameter0,i0,FALSE) THEN
						IF (i0<20) & (id=Global.Halt) THEN
							Error(position,Diagnostics.Invalid,"too small parameter")
						END;
					END;
				(* ---- NEW ----- *)
				ELSIF (id = Global.New) & Parameters(1,Infinity) THEN
					IF SyntaxTree.RealtimeFlag IN currentFlags THEN
						Error(position,Diagnostics.Invalid,"forbidden new in realtime block");
					END;
					(* check constructor *)
					IF CheckVariable(parameter0) THEN
						IF type0 IS SyntaxTree.PointerType THEN
							base := type0(SyntaxTree.PointerType).pointerBase.resolved;
							IF base IS SyntaxTree.ArrayType THEN
								arrayType := base(SyntaxTree.ArrayType);
								IF arrayType.form = SyntaxTree.Static THEN
									i := 1
								ELSIF arrayType.form = SyntaxTree.Open THEN
									i := Dimension(arrayType,{SyntaxTree.Open})+1;
								ELSE HALT(100)
								END;
								IF Parameters(i,i) & (numberActualParameters>1) THEN
									i := 1;
									REPEAT
										actualParameter := actualParameters.GetExpression(i);
										IF CheckIntegerType(actualParameter) THEN
											actualParameter := NewConversion(0,actualParameter,Global.Longint);
											actualParameters.SetExpression(i,actualParameter);
										END;
										INC(i);
									UNTIL ~CheckIntegerType(actualParameter) OR (actualParameter.resolved # NIL) & ~CheckPositiveIntegerValue(actualParameter,i0,TRUE) OR (i=numberActualParameters);
								END;
							ELSE
								ASSERT(base IS SyntaxTree.RecordType);
								constructor := GetConstructor(base(SyntaxTree.RecordType));
								IF constructor = NIL THEN
									IF Parameters(1,1) THEN END;
								ELSIF (constructor.scope.ownerModule # currentScope.ownerModule) & ~(SyntaxTree.PublicRead IN constructor.access) THEN
									Error(position,Diagnostics.Invalid,"new on object with hidden constructor");
								ELSE
									procedureType := constructor.type(SyntaxTree.ProcedureType);
									numberFormalParameters := procedureType.numberParameters-procedureType.numberHiddenParameters;
									DEC(numberActualParameters);
									IF numberActualParameters = numberFormalParameters THEN
										formalParameter := procedureType.firstParameter;
										FOR i := 1 TO numberActualParameters DO
											actualParameter := actualParameters.GetExpression(i);
											IF (actualParameter = Global.invalidExpression) THEN
											ELSIF ~ParameterCompatible(formalParameter,actualParameter) THEN
											ELSE
												IF formalParameter.type.resolved # actualParameter.type.resolved THEN
													actualParameter := NewConversion(actualParameter.position,actualParameter,formalParameter.type);
												END;
												actualParameters.SetExpression(i,actualParameter);
											END;
											formalParameter := formalParameter.nextParameter;
										END;
										result(SyntaxTree.BuiltinCallDesignator).SetHiddenVariable(GetTemporaryVariable(type0,parameter0.position));
									ELSIF numberActualParameters > numberFormalParameters THEN
										Error(position,Diagnostics.Invalid,"more actual than formal parameters")
									ELSE
										Error(position,Diagnostics.Invalid,"less actual than formal parameters")
									END;
								END;
							END;
						ELSIF type0 IS SyntaxTree.MathArrayType THEN
							mathArrayType := type0(SyntaxTree.MathArrayType);
							IF mathArrayType.form = SyntaxTree.Static THEN
								Error(position,Diagnostics.Invalid,"new on static array");
							ELSE
								IF mathArrayType.form = SyntaxTree.Tensor THEN
									i0 := 2; i1 := Infinity;
								ELSIF mathArrayType.form = SyntaxTree.Open THEN
									i0 := Dimension(mathArrayType,{SyntaxTree.Open})+1;
									i1 := i0;
								ELSE HALT(100);
								END;
								IF Parameters(i0,i1) & (numberActualParameters >1) THEN
									i := 1;
									REPEAT
										actualParameter := actualParameters.GetExpression(i);
										IF CheckIntegerType(actualParameter) THEN
											actualParameter := NewConversion(0,actualParameter,system.sizeType);
											actualParameters.SetExpression(i,actualParameter);
										END;
										INC(i);
									UNTIL ~CheckIntegerType(actualParameter) OR (actualParameter.resolved # NIL) & ~CheckPositiveIntegerValue(actualParameter,i0,TRUE) OR (i=numberActualParameters);
								END;
							END;
						ELSE
							Error(position,Diagnostics.Invalid,"new on non-pointer");
						END;
					END;
				(* ---- GETPROCEDURE ----- *)
				ELSIF (id = Global.GetProcedure) & Parameters(3,3) THEN
					IF CheckStringType(parameter0) & CheckStringType(parameter1) THEN
						IF CheckVariable(parameter2) THEN
							IF ~GetProcedureAllowed(parameter2.type) THEN
								Error(parameter2.position,Diagnostics.Invalid,"GETPROCEDURE not allowed on this type");
							END;
						END;
					END;
				(* ---- ABS ----- *)
				ELSIF (id = Global.Abs) & Parameters(1,1) THEN
					IF CheckNumberType(parameter0) THEN
						type := type0;
						IF IsIntegerValue(parameter0,i0) THEN
							result.SetResolved(SyntaxTree.NewIntegerValue(position,ABS(i0)));
							type := Global.GetIntegerType(system,ABS(i0));
						ELSIF IsRealValue(parameter0,r) THEN
							result.SetResolved(SyntaxTree.NewRealValue(position,ABS(r)));
						END;
					END;
				(* ---- ASH ----- *)
				ELSIF (id = Global.Ash) & Parameters(2,2) THEN
					type := type0;
					IF CheckIntegerType(parameter0) & CheckIntegerType(parameter1) THEN
						IF IsIntegerValue(parameter0,i0) THEN
							IF IsIntegerValue(parameter1,i1) THEN
								i0 := ASH(i0,i1);
								result.SetResolved(SyntaxTree.NewIntegerValue(position,i0));
								result := ResolveExpression(result);
								type := Global.GetIntegerType(system,i0);
							ELSE
								type := Global.Longint
							END;
						END;
						type := Global.Longint;
						parameter1 := NewConversion(parameter1.position,parameter1,type);
						parameter0 := NewConversion(parameter0.position,parameter0,type);
						actualParameters.SetExpression(0,parameter0);
						actualParameters.SetExpression(1,parameter1);
					END;
				(* ---- CAP ----- *)
				ELSIF (id = Global.Cap) & Parameters(1,1) THEN
					type := Global.Char;
					IF CheckCharacterType (parameter0) THEN
						IF IsCharacterValue(parameter0,c) THEN
							IF (c <= "z") & (c >= "a") THEN
								result.SetResolved(SyntaxTree.NewCharacterValue(position,CAP(c)))
							ELSE
								result.SetResolved(SyntaxTree.NewCharacterValue(position,c))
							END;
						END;
					END;
				(* ---- CHR ----- *)
				ELSIF (id = Global.Chr) & Parameters(1,1) THEN
					type := Global.Char;
					IF CheckIntegerType(parameter0) THEN
						IF IsIntegerValue(parameter0,i0)  THEN
							result.SetResolved(SyntaxTree.NewCharacterValue(position,CHR(i0)));
							result := ResolveExpression(result);
						ELSE
							(*
							result := NewConversion(parameter0.position,parameter0,type);
							*)
						END;
					END
				(* ---- ENTIER ----- *)
				ELSIF (id = Global.Entier) & Parameters(1,1) THEN
					type := Global.Longint;
					IF CheckRealType(parameter0) THEN
						IF IsRealValue(parameter0,r) THEN
							result.SetResolved(SyntaxTree.NewIntegerValue(position,ENTIER(r)));
							type := Global.GetIntegerType(system,ENTIER(r));
						END
					END;
				(* ---- ENTIERH ----- *)
				ELSIF (id = Global.EntierH) & Parameters(1,1) THEN
					type := Global.Hugeint;
					IF CheckRealType(parameter0) THEN
						IF IsRealValue(parameter0,r) THEN
							result.SetResolved(SyntaxTree.NewIntegerValue(position,ENTIERH(r)));
						END
					END;
				(* ---- LEN ----- *)
				ELSIF (id = Global.Len) & Parameters(1,2) THEN
					type := Global.Longint;
					base := type0;

					IF (base IS SyntaxTree.PointerType) & (parameter0 IS SyntaxTree.Designator) THEN
						parameter0 := NewDereferenceDesignator(position,parameter0(SyntaxTree.Designator));
						actualParameters.SetExpression(0,parameter0);
						type0 := parameter0.type.resolved;
						base := type0;
					END;

					IF (numberActualParameters=1) OR (numberActualParameters =2) & CheckIntegerType(parameter1) THEN
						IF ~(numberActualParameters=2) OR ~IsIntegerValue(parameter1,i1) THEN i1 := 0 END;
						IF i1 < 0 THEN
							Error(position,Diagnostics.Invalid,"invalid dimension");
							base := Global.invalidType;
						ELSE
							base := ArrayBase(base,i1);
							IF (base # NIL) & Indexable(base) THEN
							ELSE
								Error(position,Diagnostics.Invalid,"len on no array");
								IF VerboseErrorMessage THEN
									Printout.Info("base",base);
								END;
								base := Global.invalidType;
							END;
						END;
						IF numberActualParameters=2 THEN
							parameter1 := NewConversion(parameter1.position,parameter1,Global.Longint);
							actualParameters.SetExpression(1,parameter1);
						ELSIF base IS SyntaxTree.MathArrayType THEN
							Error(position,Diagnostics.Invalid,"missing dimension specification");
						END;
						IF (numberActualParameters=1) OR (numberActualParameters =2) & (parameter1 IS SyntaxTree.IntegerValue) THEN
							IF base IS SyntaxTree.ArrayType THEN
								arrayType := base(SyntaxTree.ArrayType);
								IF (arrayType.length # NIL) & (arrayType.length.resolved # NIL) & IsIntegerValue(arrayType.length,i) THEN
									(* do not use length directly such as in result := length as this mide have side-effects when result types get converted *)
									result := SyntaxTree.NewIntegerValue(position,i);
									type := arrayType.length.type;
								END;
							ELSIF base IS SyntaxTree.MathArrayType THEN
								mathArrayType := base(SyntaxTree.MathArrayType);
								IF (mathArrayType.length # NIL) & (mathArrayType.length.resolved # NIL) & IsIntegerValue(mathArrayType.length,i) THEN
									result := SyntaxTree.NewIntegerValue(position,i);
									type := mathArrayType.length.type;
								END;
							END;
						END;
					ELSE
						type := Global.Longint;
					END;
				(* ---- MAX ----- *)
				ELSIF (id = Global.Max) & Parameters(1,2) THEN
					IF numberActualParameters = 1 THEN
						IF parameter0.type = SyntaxTree.typeDeclarationType THEN
							type := parameter0(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType.resolved;
							IF type = Global.Char THEN result.SetResolved(SyntaxTree.NewCharacterValue(position,MAX(CHAR)));
							ELSIF type = Global.Char16 THEN result.SetResolved(SyntaxTree.NewIntegerValue(position,0FFFFH));
							ELSIF type = Global.Char32 THEN result.SetResolved(SyntaxTree.NewIntegerValue(position,0FFFFFFFFH));
							ELSIF type IS SyntaxTree.IntegerType THEN result.SetResolved(SyntaxTree.NewIntegerValue(position,Global.MaxInteger(system,type)));
							ELSIF type = Global.Real THEN result.SetResolved(SyntaxTree.NewRealValue(position,MAX(REAL)));
							ELSIF type = Global.Longreal THEN result.SetResolved(SyntaxTree.NewRealValue(position,MAX(LONGREAL)));
							ELSIF type = Global.Set THEN result.SetResolved(SyntaxTree.NewIntegerValue(position,system.SizeOf(type)-1)); type := Global.Shortint;
							ELSE Error(Diagnostics.Invalid,parameter0.position,"builtin function not applicable to this type");
							END;
						ELSE
							Error(parameter0.position,Diagnostics.Invalid,"is not a type symbol");
						END
					ELSIF CheckNumberType(parameter0) & CheckNumberType(parameter1) THEN
						ConvertOperands(parameter0,parameter1);
						actualParameters.SetExpression(0,parameter0);
						actualParameters.SetExpression(1,parameter1);
						IF IsRealValue(parameter0,r0) & IsRealValue(parameter1,r1) THEN
							IF r0 > r1 THEN result.SetResolved(parameter0(SyntaxTree.Value))
							ELSE result.SetResolved(parameter0(SyntaxTree.Value))
							END;
						ELSIF IsIntegerValue(parameter0,i0) & IsIntegerValue(parameter1,i1) THEN
							IF i0 > i1 THEN result.SetResolved(parameter0(SyntaxTree.Value))
							ELSE result.SetResolved(parameter1(SyntaxTree.Value))
							END;
						END;
						type := parameter0.type;
					END;
				(* ---- MIN ----- *)
				ELSIF (id = Global.Min) & Parameters(1,2) THEN
					IF numberActualParameters = 1 THEN
						IF parameter0.type = SyntaxTree.typeDeclarationType THEN
							type := parameter0(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType.resolved;
							IF type = Global.Char THEN result.SetResolved(SyntaxTree.NewCharacterValue(position,MIN(CHAR)));
							ELSIF type = Global.Char16 THEN result.SetResolved(SyntaxTree.NewIntegerValue(position,0H));
							ELSIF type = Global.Char32 THEN result.SetResolved(SyntaxTree.NewIntegerValue(position,0H));
							ELSIF type IS SyntaxTree.IntegerType THEN result.SetResolved(SyntaxTree.NewIntegerValue(position,Global.MinInteger(system,type)));
							ELSIF type = Global.Real THEN result.SetResolved(SyntaxTree.NewRealValue(position,MIN(REAL)));
							ELSIF type = Global.Longreal THEN result.SetResolved(SyntaxTree.NewRealValue(position,MIN(LONGREAL)));
							ELSIF type = Global.Set THEN result.SetResolved(SyntaxTree.NewIntegerValue(position,0)); type := Global.Shortint;
							ELSE Error(parameter0.position,Diagnostics.Invalid,"builtin function not applicable to this type");
							END;
						ELSE
							Error(parameter0.position,Diagnostics.Invalid,"is not a type symbol");
						END
					ELSIF CheckNumberType(parameter0) & CheckNumberType(parameter1) THEN
						ConvertOperands(parameter0,parameter1);
						actualParameters.SetExpression(0,parameter0);
						actualParameters.SetExpression(1,parameter1);
						IF IsRealValue(parameter0,r0) & IsRealValue(parameter1,r1) THEN
							IF r0 < r1 THEN result.SetResolved(parameter0.resolved)
							ELSE result.SetResolved(parameter1.resolved)
							END;
						ELSIF IsIntegerValue(parameter0,i0) & IsIntegerValue(parameter1,i1) THEN
							IF i0 < i1 THEN result.SetResolved(parameter0.resolved)
							ELSE result.SetResolved(parameter1.resolved)
							END;
						END;
						type := parameter0.type;
					END;
				(* ---- ODD ----- *)
				ELSIF (id = Global.Odd) & Parameters(1,1) THEN
					type := Global.Boolean;
					IF CheckIntegerType(parameter0) THEN
						IF IsIntegerValue(parameter0,i0)  THEN
							result.SetResolved(SyntaxTree.NewBooleanValue(position,ODD(i0)));
							type := Global.Boolean;
						END;
					END;
				(* ---- ORD ----- *)
				ELSIF (id = Global.Ord) & Parameters(1,1) THEN
					type := Global.Integer;
					IF CheckCharacterType(parameter0) THEN
						 IF IsCharacterValue(parameter0,c)THEN
							result.SetResolved(Global.NewIntegerValue(system,position,ORD(c)));
							type := Global.GetIntegerType(system,ORD(c));
						END;
					END;
				(* ---- SHORT ----- *)
				ELSIF (id = Global.Short) & Parameters(1,1) THEN
					type := type0;
					i := LEN(Global.NumericType)-1;
					WHILE(i>=0) & (Global.NumericType[i] # type) DO
						DEC(i);
					END;
					IF (i<0) OR (Global.NumericType[i]=Global.Shortint) OR (Global.NumericType[i]=Global.Real)  THEN
						Error(parameter0.position,Diagnostics.Invalid,"short not applicable");
						result := Global.invalidExpression;
					ELSE
						type := Global.NumericType[i-1];
						IF (parameter0.resolved # NIL) THEN
							parameter0 := ConvertValue(parameter0.position,parameter0.resolved,type);
							IF parameter0 IS SyntaxTree.Value THEN
								result.SetResolved(parameter0(SyntaxTree.Value));
							END;
						END;
					END;
				(* ---- LONG ----- *)
				ELSIF (id = Global.Long) & Parameters(1,1) THEN
					type := type0;
					IF type = Global.Char THEN
						type := Global.Longint;
					ELSE
						i := 0;
						WHILE(i<LEN(Global.NumericType)) & (Global.NumericType[i] # type) DO
							INC(i);
						END;
						IF (i = LEN(Global.NumericType)) OR (Global.NumericType[i] = Global.Longreal) OR (Global.NumericType[i]= Global.Hugeint) THEN
							Error(parameter0.position,Diagnostics.Invalid,"long not applicable");
							result := Global.invalidExpression;
						ELSE
							type := Global.NumericType[i+1];
							IF (parameter0.resolved # NIL) THEN
								parameter0 := ConvertValue(parameter0.position,parameter0.resolved,type);
								IF parameter0 IS SyntaxTree.Value THEN
									result.SetResolved(parameter0(SyntaxTree.Value));
								END;
							END;
						END;
					END;
				(* ---- SYSTEM.SIZEOF ----- *)
				ELSIF (id = Global.systemSizeOf) & Parameters(1,1) THEN
					IF (parameter0.type = SyntaxTree.typeDeclarationType) THEN
						type := parameter0(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType;
						result.SetResolved(SyntaxTree.NewIntegerValue(position,system.SizeOf(type.resolved) DIV 8 (* in bytes *) ));
						type := Global.Integer;
						(* was Int16  in paco but should be systemSize (conflict with current release) *)
					ELSE
						(* for variables, system sizeof could represent the physically occupied size
							determined via the type descriptor, implement that ? *)
						Error(parameter0.position,Diagnostics.Invalid,"is not a type symbol");
					END
				(* ---- SYSTEM.TRACE -----*)
				ELSIF (id = Global.systemTrace) & Parameters(1,1) THEN
					IF ~IsBasicType(parameter0.type) & ~IsStringType(parameter0.type) THEN
						Error(parameter0.position,Diagnostics.Invalid,"incompatible parameter");
					END;
					(* remaining issues can only be tested in backend *)
				(* ---- SYSTEM.ADR----- *)
				ELSIF (id = Global.systemAdr) & Parameters(1,1) THEN
						type := system.addressType;
				(* ---- SYSTEM.BIT ----- *)
				ELSIF (id = Global.systemBit) & Parameters(2,2) THEN
					(*! implement *)
				(* ---- SYSTEM.GET64 ----- *)
				ELSIF (id = Global.systemGet64) & Parameters(1,1) THEN
					IF CheckIntegerType(parameter0) THEN
						parameter0 := NewConversion(0,parameter0,system.addressType);
						actualParameters.SetExpression(0,parameter0);
					END;
					type := Global.Hugeint;
					(*! implement *)
				(* ---- SYSTEM.GET32 ----- *)
				ELSIF (id = Global.systemGet32) & Parameters(1,1) THEN
					IF CheckIntegerType(parameter0) THEN
						parameter0 := NewConversion(0,parameter0,system.addressType);
						actualParameters.SetExpression(0,parameter0);
					END;
					type := Global.Longint;
					(*! implement *)
				(* ---- SYSTEM.GET16 ----- *)
				ELSIF (id = Global.systemGet16) & Parameters(1,1) THEN
					IF CheckIntegerType(parameter0) THEN
						parameter0 := NewConversion(0,parameter0,system.addressType);
						actualParameters.SetExpression(0,parameter0);
					END;
					type := Global.Integer;
					(*! implement *)
				(* ---- SYSTEM.GET8 ----- *)
				ELSIF (id = Global.systemGet8) & Parameters(1,1) THEN
					IF CheckIntegerType(parameter0) THEN
						parameter0 := NewConversion(0,parameter0,system.addressType);
						actualParameters.SetExpression(0,parameter0);
					END;
					type := Global.Shortint;
					(*! implement *)
				(* ---- SYSTEM.LSH ----- *)
				ELSIF (id = Global.systemLsh) & Parameters(2,2) THEN
				 	type := type0;
					IF IsIntegerValue(parameter0,i0) & IsIntegerValue(parameter1,i1) THEN
						result.SetResolved(SyntaxTree.NewIntegerValue(position,SYSTEM.LSH(i0,i1)));
					END;
					(*! check  *)
				(* ---- SYSTEM.ROT ----- *)
				ELSIF (id = Global.systemRot) & Parameters(2,2) THEN
					type := type0;
					(*! implement *)
				(* ---- SYSTEM.VAL ----- *)
				ELSIF (id = Global.systemVal) & Parameters(2,2) THEN
					IF CheckTypeDeclarationType(parameter0) THEN
						type := parameter0(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType;
						IF (type.resolved IS SyntaxTree.ArrayType) & (type.resolved(SyntaxTree.ArrayType).form # SyntaxTree.Static) THEN
							result := Global.invalidExpression;
							Error(parameter0.position,Diagnostics.Invalid,"is no basic type");
						ELSE
							 IF (parameter1.resolved # NIL) THEN
								parameter0 := ConvertValue(parameter1.position,parameter1.resolved,type);
								IF parameter0 IS SyntaxTree.Value THEN
									result.SetResolved(parameter0(SyntaxTree.Value));
								END;
							END;
							result.SetAssignable(parameter1.assignable);
						END;
					END;
				(* ---- SYSTEM.GET ----- *)
				ELSIF (id = Global.systemGet) & Parameters(2,2) THEN
					IF CheckIntegerType(parameter0) & CheckBasicType(parameter1) THEN
						parameter0 := NewConversion(0,parameter0,system.addressType);
						actualParameters.SetExpression(0,parameter0);
					END;
				(* ---- SYSTEM.PUT ----- *)
				ELSIF (id = Global.systemPut) & Parameters(2,2) THEN
					IF CheckIntegerType(parameter0) & CheckBasicType(parameter1) THEN
						parameter0 := NewConversion(0,parameter0,system.addressType);
						actualParameters.SetExpression(0,parameter0);
					END;
				(* ---- SYSTEM.PUT64 ----- *)
				ELSIF (id = Global.systemPut64) & Parameters(2,2) THEN
					IF CheckIntegerType(parameter0) & CheckBasicType(parameter1) THEN
						parameter0 := NewConversion(parameter0.position,parameter0,system.addressType);
						parameter1 := NewConversion(parameter1.position,parameter1,Global.Hugeint);
						actualParameters.SetExpression(0,parameter0);
						actualParameters.SetExpression(1,parameter1);
					END;
				(* ---- SYSTEM.PUT32 ----- *)
				ELSIF (id = Global.systemPut32) & Parameters(2,2) THEN
					IF CheckIntegerType(parameter0) & CheckBasicType(parameter1) THEN
						parameter0 := NewConversion(parameter0.position,parameter0,system.addressType);
						parameter1 := NewConversion(parameter1.position,parameter1,Global.Longint);
						actualParameters.SetExpression(0,parameter0);
						actualParameters.SetExpression(1,parameter1);
					END;
				(* ---- SYSTEM.PUT16 ----- *)
				ELSIF (id = Global.systemPut16) & Parameters(2,2) THEN
					IF CheckIntegerType(parameter0) & CheckBasicType(parameter1) THEN
						parameter0 := NewConversion(parameter0.position,parameter0,system.addressType);
						parameter1 := NewConversion(parameter1.position,parameter1,Global.Integer);
						actualParameters.SetExpression(0,parameter0);
						actualParameters.SetExpression(1,parameter1);
					END;
				(* ---- SYSTEM.PUT8 ----- *)
				ELSIF (id = Global.systemPut8) & Parameters(2,2) THEN
					IF CheckIntegerType(parameter0) & CheckBasicType(parameter1) THEN
						parameter0 := NewConversion(parameter0.position,parameter0,system.addressType);
						parameter1 := NewConversion(parameter1.position,parameter1,Global.Shortint);
						actualParameters.SetExpression(0,parameter0);
						actualParameters.SetExpression(1,parameter1);
					END;
				(* ---- SYSTEM.MOVE ----- *)
				ELSIF (id = Global.systemMove) & Parameters(3,3) THEN
					IF CheckIntegerType(parameter0) & CheckIntegerType(parameter1) & CheckIntegerType(parameter2) THEN
						parameter0 := NewConversion(0,parameter0,Global.Address);
						parameter1 := NewConversion(0,parameter1,Global.Address);
						parameter2 := NewConversion(0,parameter2,Global.Address);
						actualParameters.SetExpression(0,parameter0);
						actualParameters.SetExpression(1,parameter1);
						actualParameters.SetExpression(2,parameter2);
					END;
				(* ---- SYSTEM.NEW ----- *)
				ELSIF (id = Global.systemNew) & Parameters(2,2) THEN
					(*! implement *)
				(* ---- SYSTEM.INCR ----- *)
				ELSIF (id = Global.systemIncr) & Parameters(1,2) THEN




					type := system.sizeType;
					base := type0;


					IF (numberActualParameters =2) & CheckIntegerType(parameter1) THEN
						IF ~IsIntegerValue(parameter1,i1) THEN i1 := 0 END;
						IF i1 < 0 THEN
							Error(position,Diagnostics.Invalid,"invalid dimension");
							base := Global.invalidType;
						ELSE
							base := ArrayBase(base,i1);
							IF (base # NIL) & Indexable(base) THEN
							ELSE
								Error(position,Diagnostics.Invalid,"len on no array");
								IF VerboseErrorMessage THEN
									Printout.Info("base",base);
								END;
								base := Global.invalidType;
							END;
						END;
						parameter1 := NewConversion(parameter1.position,parameter1,Global.Longint);
						actualParameters.SetExpression(1,parameter1);
						IF (numberActualParameters =2) & (parameter1 IS SyntaxTree.IntegerValue) THEN
							mathArrayType := base(SyntaxTree.MathArrayType);
							IF (mathArrayType.form = SyntaxTree.Static) THEN
								result := SyntaxTree.NewIntegerValue(position,ToMemoryUnits(system,mathArrayType.staticIncrementInBits));
								type := Global.Longint;
							END;
						END;
					ELSE
						type := Global.Longint;
					END;


				(* ---- SUM ----- *)
				ELSIF (id = Global.Sum) & Parameters(1,2) THEN
					IF numberActualParameters=1 THEN
					ELSE
					END;
				(* ---- DIM ----- *)
				ELSIF (id = Global.Dim) & Parameters(1,1) THEN
					type := system.sizeType;
					IF type0 IS SyntaxTree.MathArrayType THEN
						IF type0(SyntaxTree.MathArrayType).form # SyntaxTree.Tensor THEN
							i := Dimension(type0,{SyntaxTree.Open,SyntaxTree.Static});
							result.SetResolved(SyntaxTree.NewIntegerValue(position,i));
						END;
					ELSE
						Error(position,Diagnostics.Invalid,"dimension on non math array type");
					END;
				(* ---- RESHAPE ----- *)
				ELSIF (id = Global.systemReshape) & Parameters(2,2) THEN
					(*! implement *)
				(* ---- SYSTEM.ZEROCOPY----- *)
				ELSIF (id = Global.systemZeroCopy) & Parameters(2,2) THEN
					(*! implement *)
				(* ---- SYSTEM.TYPECODE ----- *)
				ELSIF (id = Global.systemTypeCode) & Parameters(1,1) THEN
					IF (parameter0.type = SyntaxTree.typeDeclarationType) THEN
						type := parameter0(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType;
						type := type.resolved;
						IF type IS SyntaxTree.PointerType THEN
							type := type(SyntaxTree.PointerType).pointerBase.resolved;
						END;
						IF ~(type IS SyntaxTree.RecordType) THEN
							Error(parameter0.position,Diagnostics.Invalid,"must be type with type descriptor");
						END;
					ELSE
						Error(parameter0.position,Diagnostics.Invalid,"is not a type symbol");
					END;
					type := system.addressType;
				(* -------- ERA --------- *)
				(* ---- SYSTEM.NULL ----- *)
				ELSIF (id = Global.systemNull) & Parameters(1,1) THEN
					type := Global.Boolean;
				(* -------- FLT --------- *)
				ELSIF (id = Global.Flt) & Parameters(1,1) THEN
					type := Global.Real;
					IF IsRealValue(parameter0, r) THEN
						result.SetResolved(SyntaxTree.NewRealValue(position, r));
					ELSIF CheckIntegerType(parameter0) & IsIntegerValue(parameter0, i) THEN
						i0 := i; i := ABS(i);
						IF i # 0 THEN
							i1 := 23;
							IF i >= 2*800000H THEN
								REPEAT i := i DIV 2; INC(i1) UNTIL i < 2*800000H;
							ELSIF i < 800000H THEN
								REPEAT i := 2 * i; DEC(i1) UNTIL i >= 800000H;
							END;
							i := (i1 + 127)*800000H - 800000H + i;
							IF i0 < 0 THEN i := SYSTEM.VAL(LONGINT, SYSTEM.VAL(SET, i) + {31}); END;
						END;
						result.SetResolved(SyntaxTree.NewRealValue(position, SYSTEM.VAL(REAL, i)));
					END;
				(* ------- FLOOR -------- *)
				ELSIF (id = Global.Floor) & Parameters(1,1) THEN
					type := Global.Longint;
					IF CheckRealType(parameter0) & IsRealValue(parameter0,r) THEN
						result.SetResolved(SyntaxTree.NewIntegerValue(position,ENTIER(r)));
					END;
				(* ------- PROC -------- *)
				ELSIF (id = Global.systemProc) & Parameters(2,2) THEN
					 type := parameter1.type.resolved;
					 result := parameter0; (*! should not be done via direct replacement ! *)
				(* ------- STOP -------- *)
				ELSIF (id = Global.systemStop) & Parameters(0,0) THEN
				(* ------- SHIFTS -------- *)
				ELSIF ((id = Global.ASR) OR (id = Global.LSR) OR (id = Global.LSL) OR (id = Global.systemROR)) & Parameters(2,2) THEN
					IF CheckIntegerType(parameter0) & CheckIntegerType(parameter1) THEN
						type := type0;
					END;
					type := type0;
				(* ------ XOR ------- *)
				ELSIF (id = Global.systemXOR) THEN
					IF CheckIntegerType(parameter0) & (type0=type1) THEN
					END;
					type := type0;
				ELSE
					Error(position,Diagnostics.Invalid,"unknown builtin");
					result := Global.invalidExpression;
				END;
			END;

			IF result # Global.invalidExpression THEN
				type := ResolveType(type);
				IF result.resolved # NIL THEN result.resolved.SetType(type) END;
				result.SetType(type);
			END;

			RETURN result
		END NewBuiltinCallDesignator;

		(** return type guard designator left(type)
			- check if type can be extended (i.e. is no static record)
			- check if type is a type extension of left.type
			- returns new type guard designator
			returns invalidDesignator = invalidExpression if error
		**)
		PROCEDURE NewTypeGuardDesignator(position: LONGINT; left: SyntaxTree.Designator; type: SyntaxTree.Type; typeExpression: SyntaxTree.Expression): SyntaxTree.Designator;
		VAR result: SyntaxTree.Designator;
		BEGIN
			result := Global.invalidDesignator;

			IF ~IsTypeExtension(left.type.resolved,type.resolved) THEN
				Error(position,Diagnostics.Invalid,"no type extension of type");
				IF VerboseErrorMessage THEN
					Printout.Info("left",left);
					Printout.Info("type",type);
				END;
			ELSIF ~(left.type.resolved = type.resolved) & ~IsExtensibleDesignator(left) THEN (* left is not extensible *)
				Error(position,Diagnostics.Invalid,"variable cannot be extended");
			ELSE
				result := SyntaxTree.NewTypeGuardDesignator(position,left,type);
				result(SyntaxTree.TypeGuardDesignator).SetTypeExpression(typeExpression);
				result.SetType(type);
				result.SetAssignable(left.assignable);
			END;
			RETURN result
		END NewTypeGuardDesignator;

		(** check and resolve parameter designator left(expression list)
			- check expression list
			- if one parameter and left is extensible type and parameter contains type declaration then return TypeGuardDesignator
			- elsif left is a procedure type then
				- if left is a built-in procedure then return NewBuiltinCallDesignator
				- else return is a procedure call then return ProcedureCallDesignator
			returns invalidDesignator = invalidExpression if error
		**)
		PROCEDURE VisitParameterDesignator(designator: SyntaxTree.ParameterDesignator);
		VAR
			parameters: SyntaxTree.ExpressionList;
			left: SyntaxTree.Designator;
			result: SyntaxTree.Expression;
			typeDeclaration: SyntaxTree.TypeDeclaration;
		BEGIN
			IF Trace THEN D.Str("VisitParameterDesignator"); D.Ln; END;
			result := Global.invalidDesignator;
			left := ResolveDesignator(designator.left);
			IF left # Global.invalidDesignator THEN
				parameters := designator.parameters;
				IF ExpressionList(parameters) THEN
					IF IsExtensibleDesignator(left) & (parameters.Length()=1) & IsTypeDesignator(parameters.GetExpression(0),typeDeclaration) THEN
						result := NewTypeGuardDesignator(designator.position,left,typeDeclaration.declaredType,parameters.GetExpression(0))
					ELSIF IsUnextensibleRecord(left) & (parameters.Length()=1) & IsTypeDesignator(parameters.GetExpression(0),typeDeclaration) & (typeDeclaration.declaredType.resolved = left.type.resolved) THEN
						result := NewTypeGuardDesignator(designator.position,left,typeDeclaration.declaredType,parameters.GetExpression(0))
					ELSIF (left.type.resolved IS SyntaxTree.ProcedureType) THEN
						IF (left IS SyntaxTree.SymbolDesignator) & (left(SyntaxTree.SymbolDesignator).symbol IS SyntaxTree.Builtin) THEN
							result := NewBuiltinCallDesignator(designator.position,left(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.Builtin),parameters,left);
						ELSE
							result := NewProcedureCallDesignator(designator.position,left,parameters)
						END
					ELSE
						Error(left.position,Diagnostics.Invalid,"called object is not a procedure or cannot be extended");
						IF VerboseErrorMessage THEN Printout.Info("designator",designator); Printout.Info("left",left) END;
						result := Global.invalidDesignator;
					END;
				ELSE
					result := Global.invalidDesignator
				END;
			END;
			resolvedExpression := result;
		END VisitParameterDesignator;

		(** check dereference designator left^
			 - check if left is pointer type or left is object type
			 - return new dereference designator with type = left.baseType.type (if appropriate)
			with error handling
			returns invalidDesignator = invalidExpression if error
		**)
		PROCEDURE NewDereferenceDesignator(position: LONGINT; left: SyntaxTree.Designator): SyntaxTree.Designator;
		VAR type: SyntaxTree.Type; result: SyntaxTree.Designator;
		BEGIN
			result := Global.invalidDesignator;
			type := left.type;
			IF (type # NIL) & ((type.resolved IS SyntaxTree.PointerType)) THEN
				type := type.resolved(SyntaxTree.PointerType).pointerBase;
				result := SyntaxTree.NewDereferenceDesignator(position,left);
				result.SetAssignable(TRUE);
				result.SetType(type);
			ELSE
				Error(position,Diagnostics.Invalid,"dereference on no pointer");
			END;
			RETURN result
		END NewDereferenceDesignator;

		(** check supercall designator left^
			- if left is symbol designator with procedure symbol containing non-nil supermethod then
				- return new supercall designator with type = left.type
			with error handling
		**)
		PROCEDURE NewSupercallDesignator(position: LONGINT; left: SyntaxTree.Designator): SyntaxTree.Designator;
		VAR result: SyntaxTree.Designator; symbol: SyntaxTree.Symbol; procedure: SyntaxTree.Procedure;
			objectScope: SyntaxTree.Scope;
		BEGIN
			result := Global.invalidDesignator;
			IF left = Global.invalidDesignator THEN
				(* error already handled *)
			ELSIF left IS SyntaxTree.SymbolDesignator THEN
				symbol := left(SyntaxTree.SymbolDesignator).symbol;
				ASSERT(symbol # Global.invalidSymbol);
				IF symbol IS SyntaxTree.Procedure THEN
					procedure := symbol(SyntaxTree.Procedure);
					objectScope := currentScope;
					WHILE (objectScope # NIL) & ~(objectScope IS SyntaxTree.RecordScope) DO
						objectScope := objectScope.outerScope;
					END;
					IF (left.left = NIL) OR ~
						(
						(left.left IS SyntaxTree.SelfDesignator) OR
						(left.left IS SyntaxTree.DereferenceDesignator)
						& (left.left(SyntaxTree.Designator).left # NIL)
						& (left.left(SyntaxTree.Designator).left IS SyntaxTree.SelfDesignator)) OR (procedure.scope # objectScope)  THEN
						Error(position,Diagnostics.Invalid,"procedure not in immediate object scope");
						IF VerboseErrorMessage THEN
							Printout.Info("left.left",left.left);
						END;
					ELSIF procedure.super # NIL THEN
						result := SyntaxTree.NewSupercallDesignator(position,left);
						result.SetType(left.type.resolved)
					ELSE
						Error(position,Diagnostics.Invalid,"no supermethod for this procedure");
					END;
				ELSE
					Error(position,Diagnostics.Invalid,"symbol is not a procedure");
				END;
			ELSE
				Error(position,Diagnostics.Invalid,"is no symbol designator");
			END;

			RETURN result
		END NewSupercallDesignator;

		(** check and semantically resolve arrow designator left^
			- if left is procedure type -> result := SupercallDesignator
			- else result :=  DereferenceDesignator
			returns result via global variable resolvedExpression
			error handling deferred to procedures SupercallDesignator and DereferenceDesignator
		**)
		PROCEDURE VisitArrowDesignator(arrowDesignator: SyntaxTree.ArrowDesignator);
		VAR left: SyntaxTree.Designator;
		BEGIN
			IF Trace THEN D.Str("VisitArrowDesignator"); D.Ln; END;
			left := ResolveDesignator(arrowDesignator.left);
			IF left # NIL THEN
				IF (left.type.resolved # NIL) & (left.type.resolved IS SyntaxTree.ProcedureType) THEN
					resolvedExpression := NewSupercallDesignator(arrowDesignator.position,left);
				ELSE
					resolvedExpression := NewDereferenceDesignator(arrowDesignator.position,left)
				END
			END
		END VisitArrowDesignator;

		(** check and return expression
			- if expression has no type then resolve expression
			- resulting expression is exchanged via global variable "resolvedExpression" which makes this mechanism thread-unsafe
			- return result
		**)
		PROCEDURE ResolveExpression(expression: SyntaxTree.Expression): SyntaxTree.Expression;
		VAR result,prev: SyntaxTree.Expression;
		BEGIN
			IF (expression.type = NIL) THEN
				prev := resolvedExpression;
				resolvedExpression := Global.invalidExpression;
				expression.SetType(Global.invalidType);
				expression.Accept(SELF);
				result := resolvedExpression;
				resolvedExpression := prev
			ELSE
				result := expression
			END;
			RETURN result
		END ResolveExpression;

		(**
			check expression to be constant expression
			- resolve expression
			- if valid then check that of value type
			report error and return invalidExpression if anything fails
		**)
		PROCEDURE ConstantExpression(expression: SyntaxTree.Expression): SyntaxTree.Expression;
		VAR position: LONGINT;
		BEGIN
			position := expression.position;
			expression := ResolveExpression(expression);
			IF expression = Global.invalidExpression THEN (* error already reported *)
			ELSIF (expression.resolved = NIL) THEN
				Error(position,Diagnostics.Invalid,"expression is not constant");
				IF VerboseErrorMessage THEN Printout.Info("expression",expression); END;
				expression := Global.invalidExpression;
			END;
			RETURN expression
		END ConstantExpression;

		(** check expression to be constant integer
			- resolve expresssion
			- if valid then check that of integer value type
			report error and return invalidExpression if anything fails
		**)
		PROCEDURE ConstantInteger(expression: SyntaxTree.Expression): SyntaxTree.Expression;
		VAR position: LONGINT;
		BEGIN
			position := expression.position;
			expression := ResolveExpression(expression);
			IF expression = Global.invalidExpression THEN (* error already reported *)
			ELSIF (expression.resolved = NIL) OR ~(expression.resolved IS SyntaxTree.IntegerValue) THEN
				expression := Global.invalidExpression;
				Error(position,Diagnostics.Invalid,"expression is not a constant integer");
			END;
			RETURN expression
		END ConstantInteger;

		(** check expression as positive (>=0) constant integer
			- resolve expression
			- if valid then check that integer value
			- if integer value then check that value >= 0
			report error and return invalidExpression if anything fails
		**)
		PROCEDURE ConstantIntegerGeq0(expression: SyntaxTree.Expression): SyntaxTree.Expression;
		VAR position: LONGINT;
		BEGIN
			position := expression.position;
			expression := ConstantExpression(expression);
			IF expression = Global.invalidExpression THEN
				(* error already reported *)
			ELSIF  (expression.resolved = NIL) OR ~(expression.resolved IS SyntaxTree.IntegerValue) THEN
				Error(position,Diagnostics.Invalid,"expression is not integer valued");
				expression := Global.invalidExpression
			ELSIF (expression.resolved(SyntaxTree.IntegerValue).hvalue <0) THEN
				Error(position,Diagnostics.Invalid,"integer is not greater or equal zero");
			END;
			RETURN expression
		END ConstantIntegerGeq0;

		(** check expression as condition
			- resolve expression
			- if valid expression then check that result type is boolean
			report error and return invalidExpression if anything fails
		**)
		PROCEDURE ResolveCondition(expression: SyntaxTree.Expression): SyntaxTree.Expression;
		VAR position: LONGINT;
		BEGIN
			position := expression.position;
			expression := ResolveExpression(expression);
			IF expression = Global.invalidExpression THEN (* error already reported *)
			ELSIF (expression.type = NIL) OR ~(expression.type.resolved = Global.Boolean) THEN
				expression := Global.invalidExpression;
				Error(position,Diagnostics.Invalid,"expression is not boolean");
			END;
			RETURN expression
		END ResolveCondition;

		(*** symbols ***)

		PROCEDURE ResolveSymbol(x: SyntaxTree.Symbol);
		BEGIN
			x.Accept(SELF);
		END ResolveSymbol;

		(** check a symbol
			- check visibility flags (symbols within procedure scope (direct or indirect) cannot be exported)
		**)
		PROCEDURE CheckSymbol(symbol: SyntaxTree.Symbol);
		VAR scope: SyntaxTree.Scope;
		BEGIN
			(* visibility *)
			scope := symbol.scope;
			WHILE (scope # NIL) & ~(scope IS SyntaxTree.ProcedureScope) DO
				scope := scope.outerScope;
			END;
			IF (scope # NIL) THEN (* symbol (directly or indirectly) in procedure scope *)
				IF (symbol.access * SyntaxTree.Public # {}) & ~(SyntaxTree.BodyProcedureFlag IN symbol.flags) & ~(SyntaxTree.ConstructorFlag IN symbol.flags)  THEN
					Error(symbol.position,Diagnostics.Invalid,"cannot be exported");
					IF VerboseErrorMessage THEN
						Printout.Info("symbol",symbol);
					END;
				END;
			END;
		END CheckSymbol;

				(** Check if a node has already been resolved. If not then mark as currently being resolved.
			If node is currently being resolved then emit a cyclic definition error.
			Return TRUE only if node is fully resolved.
		**)
		PROCEDURE SymbolNeedsResolution(x: SyntaxTree.Symbol): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			IF SyntaxTree.Resolved IN x.state THEN
				result := FALSE
			ELSIF SyntaxTree.BeingResolved IN x.state THEN
				Error(x.position,Diagnostics.Invalid,"cyclic definition");
				result := FALSE;
			ELSE
				result := TRUE;
				x.SetState(SyntaxTree.BeingResolved)
			END;
			RETURN result
		END SymbolNeedsResolution;


		(** check and resolve a type declaration symbol = Type
			- set type to declaration type
				-> the type of a type declaration is NOT the declared type but the "declaration" type.
				     This is so because the type declaration itself does not have a type but it only stands for a type.
				     In the implementation of the compiler this made a lot much easier.
			- resolve and set declared type
			- check symbol
		**)
		PROCEDURE VisitTypeDeclaration(typeDeclaration: SyntaxTree.TypeDeclaration);
		BEGIN
			IF Trace THEN D.Str("VisitTypeDeclaration "); D.Str0(typeDeclaration.name.name);  D.Ln;  END;
			IF SymbolNeedsResolution(typeDeclaration) THEN
				typeDeclaration.SetType(SyntaxTree.typeDeclarationType);
				typeDeclaration.SetDeclaredType(ResolveType(typeDeclaration.declaredType));
				CheckSymbol(typeDeclaration);
				typeDeclaration.SetState(SyntaxTree.Resolved);
			END;
		END VisitTypeDeclaration;

		(** check and resolve a constant declaration symbol = (constant) expression
			- check expression
			- set type and value
			- check symbol
		**)
		PROCEDURE VisitConstant(constant: SyntaxTree.Constant);
		VAR
			expression: SyntaxTree.Expression;
			type: SyntaxTree.Type;
		BEGIN
			IF Trace THEN D.Str("VisitConstant "); D.Str0(constant.name.name);  D.Ln;  END;
			IF SymbolNeedsResolution(constant) THEN
				constant.SetType(Global.invalidType);
				expression := ConstantExpression(constant.value);
				type := expression.type.resolved;
				constant.SetType(type);
				constant.SetValue(expression);
				CheckSymbol(constant);
				constant.SetState(SyntaxTree.Resolved);
			END;
		END VisitConstant;

		(** check and resolve a variable / field
			- check and set type
			- negative check on open array type
			- check symbol
		**)
		PROCEDURE VisitVariable(variable: SyntaxTree.Variable);
		BEGIN
			IF Trace THEN D.Str("VisitVariable "); D.Str0(variable.name.name);  D.Ln;  END;
			IF SymbolNeedsResolution(variable) THEN
				IF Flag(variable.flagList,{SyntaxTree.UntracedFlag}) = SyntaxTree.UntracedFlag THEN
					variable.AddFlags({SyntaxTree.UntracedFlag});
				END;
				variable.SetType(ResolveType(variable.type));
				IF variable.type.resolved IS SyntaxTree.ArrayType THEN
					IF variable.type.resolved(SyntaxTree.ArrayType).length = NIL THEN
						Error(variable.position,Diagnostics.Invalid,"forbidden open array variable");
					END;
				END;
				CheckSymbol(variable);
				IF SyntaxTree.UntracedFlag IN variable.flags THEN
					IF ~ContainsPointer(variable.type) THEN
						IF VerboseErrorMessage THEN Printout.Info("variable",variable); Printout.Info("variable.type",variable.type.resolved); END;
						Error(variable.position,Diagnostics.Invalid,"untraced flag on non-pointer variable");
					END;
				END;
				variable.SetState(SyntaxTree.Resolved);
			END;
		END VisitVariable;

		(** check and resolve a with guarded variable
			- check and set type
			- check referenced variable
		**)
		PROCEDURE VisitGuardedVariable(variable: SyntaxTree.GuardedVariable);
		BEGIN
			IF Trace THEN D.Str("VisitGuardedVariable "); D.Str0(variable.name.name);  D.Ln;  END;
			IF SymbolNeedsResolution(variable) THEN
				variable.SetType(ResolveType(variable.type));
				ResolveSymbol(variable.variable);
				variable.SetState(SyntaxTree.Resolved);
			END;
		END VisitGuardedVariable;

		(** check and resolve a (procedure) parameter
			- check and set type
			- check symbol
			- check parameter kind and set read-only flags if appropriate
		**)
		PROCEDURE VisitParameter(parameter: SyntaxTree.Parameter);
		BEGIN
			IF Trace THEN D.Str("VisitParameter "); D.Str0(parameter.name.name);  D.Ln;  END;
			IF SymbolNeedsResolution(parameter) THEN
				parameter.SetType(ResolveType(parameter.type));
				ASSERT(parameter.type.resolved # NIL);
				CheckSymbol(parameter);
				IF parameter.kind = SyntaxTree.ConstParameter THEN parameter.SetAccess(parameter.access * SyntaxTree.ReadOnly) END;
				parameter.SetState(SyntaxTree.Resolved);
			END;
		END VisitParameter;

		(** check and resolve a procedure (with declaration and implementation scope)
			- check the procedure type
			- check if method (i.e. in record scope), if so then
				- check if (unique) constructor
				- check if super method available, if so then check signature
			- of not in record scope then negative check on constructor flag
			- check declarations (including a delayed implementation check, cf procedure Declarations)
			- check procedure symbol
		**)
		PROCEDURE VisitProcedure(procedure: SyntaxTree.Procedure);
		VAR super,testsuper,proc: SyntaxTree.Procedure; record: SyntaxTree.RecordType;
			recordBase: SyntaxTree.RecordType; procedureType: SyntaxTree.ProcedureType;
			selfParameter: SyntaxTree.Parameter; qualifiedIdentifier: SyntaxTree.QualifiedIdentifier;
			qualifiedType: SyntaxTree.QualifiedType; recentFlags: SET; flags: SET;
			returnType: SyntaxTree.Type;

		BEGIN
			IF Trace THEN D.Str("VisitProcedure "); D.Str0(procedure.name.name);  D.Ln;  END;
			IF SymbolNeedsResolution(procedure) THEN
				recentFlags := currentFlags;
				IF Trace THEN D.Str("undefined"); D.Ln; END;
				procedureType := procedure.type(SyntaxTree.ProcedureType);
				flags := Flags(procedureType.flagList,{SyntaxTree.WinAPIFlag,SyntaxTree.CFlag,SyntaxTree.DelegateFlag,SyntaxTree.RealtimeFlag});
				procedureType.AddFlags(flags);
				FixProcedureType(procedureType);
				IF SyntaxTree.DelegateFlag IN procedureType.flags THEN
					Error(procedure.position,Diagnostics.Invalid,"procedure illegaly marked delegate");
				END;
				procedure.AddFlags(procedureType.flags);
				currentFlags := currentFlags + procedure.flags;


				IF procedure.scope IS SyntaxTree.ProcedureScope THEN
					procedure.SetLevel(procedure.scope(SyntaxTree.ProcedureScope).ownerProcedure.level+1);
					system.GenerateParameterOffsets(procedureType,TRUE);
				END;
				IF procedure.scope IS SyntaxTree.RecordScope THEN
					record := procedure.scope(SyntaxTree.RecordScope).ownerRecord;
					procedureType.AddFlags({SyntaxTree.DelegateFlag});
					procedure.AddFlags({SyntaxTree.DelegateFlag});

					selfParameter := SyntaxTree.NewParameter(procedure.position,procedureType,Global.SelfParameterName,SyntaxTree.ValueParameter);
					IF record.pointerType.typeDeclaration = NIL THEN
						selfParameter.SetType(record.pointerType);
					ELSE
						qualifiedIdentifier := SyntaxTree.NewQualifiedIdentifier(procedure.position,NIL,record.pointerType.typeDeclaration.name);
						qualifiedType := SyntaxTree.NewQualifiedType(procedure.position,procedure.scope,qualifiedIdentifier);
						qualifiedType.SetResolved(record.pointerType);
						selfParameter.SetType(qualifiedType);
					END;
					selfParameter.SetAccess(SyntaxTree.Hidden);
					procedureType.AddParameter(selfParameter);


					(*! constructor information is redundant, we can remove "isConstructor" and repplace by constructor procedure reference *)
					IF SyntaxTree.ConstructorFlag IN procedure.flags THEN
						(*! constructor is always visible, compatibility to paco *)
						procedure.SetAccess(SyntaxTree.Public+SyntaxTree.Protected+SyntaxTree.Internal);

						IF procedureType.returnType # NIL THEN
							Error(procedure.position,Diagnostics.Invalid,"constructor with forbidden return type");
						END;
						proc := procedure.scope.firstProcedure;
						WHILE (proc # NIL) & ((proc = procedure) OR ~(SyntaxTree.ConstructorFlag IN proc.flags)) DO
							proc := proc.nextProcedure;
						END;
						IF proc # NIL THEN
							Error(procedure.position,Diagnostics.Invalid,"duplicate constructor")
						ELSE
							procedure.scope(SyntaxTree.RecordScope).SetConstructor(procedure);
						END;
					END;
					recordBase := RecordBase(record);
					IF (recordBase # NIL) THEN
						super := recordBase.recordScope.FindProcedure(procedure.name);
						IF (super = NIL) OR (super.scope.ownerModule = procedure.scope.ownerModule) OR (SyntaxTree.Public * super.access # {}) THEN
							(* ok: no super method or super method is in same module scope or is exported or is constructor *)
						ELSE
							(* check if there is an exported method in the chain of super methods *)
							testsuper := super;
							WHILE (testsuper # NIL) & (SyntaxTree.Public*testsuper.access = {}) DO
								testsuper := testsuper.super;
							END;
							IF testsuper = NIL THEN
								super := NIL; (* no exported sup-method for this procedure *)
							END;
						END;
						IF (super # NIL) & SignatureCompatible(procedure.position,procedureType,super.type.resolved(SyntaxTree.ProcedureType)) THEN
							IF (SyntaxTree.ConstructorFlag IN super.flags) & ~(SyntaxTree.ConstructorFlag IN procedure.flags) THEN
								Error(procedure.position,Diagnostics.Invalid,"incompatible signature: non-constructor extends constructor");
							END;
							procedure.SetSuper(super);
							procedure.SetAccess(procedure.access+super.access);
						END;
					END;
					system.GenerateParameterOffsets(procedureType,FALSE); (* assume that this is no nested procedure, is fixed later otherwise *)
				ELSIF SyntaxTree.ConstructorFlag IN procedure.flags THEN
					Error(procedure.position,Diagnostics.Invalid,"nested procedure illegaly marked as initializer");
				END;
				Declarations(procedure.procedureScope);
				(* body resolution part done as late fix of the procedure type *)
				CheckSymbol(procedure);
				procedure.SetState(SyntaxTree.Resolved);
				currentFlags := recentFlags;
			END;
		END VisitProcedure;

		(**
			a builtin procedure is a global item that may not be modified locally
			instead the resolving of builtin procedure calls are done in the NewBuiltinCallDesignator
		**)
		PROCEDURE VisitBuiltin(builtinProcedure: SyntaxTree.Builtin);
		VAR type: SyntaxTree.Type;
		BEGIN
			type := ResolveType(builtinProcedure.type);
		END VisitBuiltin;

		(** check and resolve operator **)
		PROCEDURE VisitOperator(operator: SyntaxTree.Operator);
		BEGIN
			VisitProcedure(operator);
			(*! check operator (number of parameters etc.) *)
		END VisitOperator;

		PROCEDURE AddImport*(module: SyntaxTree.Module; x: SyntaxTree.Import);
		VAR prevScope: SyntaxTree.Scope;
		BEGIN
			prevScope := currentScope;
			currentScope := module.moduleScope;
			module.moduleScope.AddImport(x);
			VisitImport(x);
			currentScope := prevScope;
		END AddImport;


		(** check and resolve import
			- check for name = SYSTEM
			- check for forbidden self import
			- search through global import cache: already imported?
			- check if already imported indirectly
			- import if necessary -> set module and enter into import cache
			- enter re-imports into list of imported modules as non-direct import (if not in direct import list)
			- after this import this direct import and all indirect imports are stored in the current module's import list
		**)
		PROCEDURE VisitImport(x: SyntaxTree.Import);
		VAR
			module: SyntaxTree.Module;
			moduleScope: SyntaxTree.ModuleScope;
			import,reimport: SyntaxTree.Import;
			filename: Scanner.StringType;
		BEGIN
			IF SymbolNeedsResolution(x) THEN
				x.SetType(SyntaxTree.importType);
				moduleScope := currentScope.ownerModule.moduleScope;

				IF x.moduleName.Equals(Global.SystemName) THEN x.SetModule(system.systemModule[Scanner.Uppercase])
				ELSIF x.moduleName.Equals(Global.systemName) THEN x.SetModule(system.systemModule[Scanner.Lowercase])
				ELSIF x.moduleName.Equals(currentScope.ownerModule.name) & x.context.Equals(currentScope.ownerModule.context) THEN
					Error(x.position,Diagnostics.Invalid,"forbidden self import");
				ELSE

					(* search through global import list: already imported ? *)
					IF (x.module = NIL) & (importCache # NIL)  THEN
						import := importCache.ImportByModuleName(x.moduleName,x.context);
					ELSE import := NIL
					END;

					IF x.module # NIL THEN (* already imported indirectly *)
						module := x.module;
					ELSIF import # NIL THEN (* already in module list *)
						module := import.module;
						ASSERT(module # NIL);
						x.SetModule(module);
					ELSE (* must be imported *)
						Global.ModuleFileName(x.moduleName,x.context,filename);
						IF symbolFileFormat # NIL THEN
							module := symbolFileFormat.Import(filename,importCache); (* includes module parsing *)
							IF module = NIL THEN
								ErrorSS(x.position,"could not import",filename);
								IF VerboseErrorMessage THEN
									Printout.Info("import",x)
								END
							ELSE
								(*
								IF ~(SyntaxTree.Resolved IN module.state) THEN
									(*! should rather be done by importer *)
									checker := NewChecker(diagnostics,VerboseErrorMessage,system,symbolFileFormat,importCache);
									checker.importCache := importCache;
									checker.arrayBaseImported := arrayBaseImported;
									checker.global := global;
									checker.Module(module); (* semantic check *)
									error := error OR checker.error;
								END;
								*)
								(*
								ASSERT(SyntaxTree.Resolved IN module.state);
								*)
								x.SetModule(module);
								IF importCache # NIL THEN
									import := SyntaxTree.NewImport(InvalidPosition,x.moduleName,x.moduleName,FALSE);
									import.SetContext(x.context);
									import.SetModule(module);
									importCache.AddImport(import);
								END;
							END;
						ELSE
							ErrorSS(x.position,"no symbol file specified: cannot import",filename);
						END;
					END;
					IF module # NIL THEN (* enter reimports into list of imported modules *)
						import := module.moduleScope.firstImport;
						WHILE(import # NIL) DO
							ASSERT(import.moduleName # NIL);
							ASSERT(currentScope # NIL);
							ASSERT(currentScope.ownerModule # NIL);
							ASSERT(import.context # NIL);

							IF import.moduleName.Equals(currentScope.ownerModule.name) & import.context.Equals(currentScope.ownerModule.context) THEN
								Error(x.position,Diagnostics.Invalid,"recursive import");
							ELSE
								IF import.context = NIL THEN import.SetContext(x.context) END;
								reimport := moduleScope.ImportByModuleName(import.moduleName,import.context);
								IF reimport = NIL THEN  (* indirect import *)
									reimport := SyntaxTree.NewImport(InvalidPosition,import.moduleName,import.moduleName,FALSE);
									reimport.SetContext(import.context);
									reimport.SetModule(import.module);
									moduleScope.AddImport(reimport);
								ELSE
									ASSERT(import.module # NIL);
									reimport.SetModule(import.module); (* direct or indirect import *)
								END;
							END;
							import := import.nextImport;
						END;
					END;
				END;
				(* ELSE nothing to be done *)
				x.SetState(SyntaxTree.Resolved);
			END;
		END VisitImport;

		(*** statements ***)

		PROCEDURE ResolveStatement(x: SyntaxTree.Statement): SyntaxTree.Statement;
		VAR prev,resolved: SyntaxTree.Statement;
		BEGIN
			prev := resolvedStatement;
			resolvedStatement := x;
			IF SyntaxTree.UnreachableFlag IN currentFlags THEN x.AddFlags({SyntaxTree.UnreachableFlag}) END;
			x.Accept(SELF);
			resolved := resolvedStatement;
			resolvedStatement := prev;
			RETURN resolved
		END ResolveStatement;

		(** check and resolve statement sequence
			- check all statements, replace if necessary
		**)
		PROCEDURE StatementSequence(statementSequence: SyntaxTree.StatementSequence);
		VAR i: LONGINT; statement,resolved: SyntaxTree.Statement;
		BEGIN
			IF statementSequence # NIL THEN (* else empty *)
				FOR i := 0 TO statementSequence.Length()-1 DO
					statement := statementSequence.GetStatement(i);
					resolved := ResolveStatement(statement);
					IF (resolved # statement) THEN
						statementSequence.SetStatement(i,resolved);
					END;
				END;
			END;
		END StatementSequence;

		(** check and resolve procedure call statement procedureCall() or procedureCall;
			- check if call is a procedure call designator, if not (procedure type symbol) try to make one out of it
			- check if procedure is callable
			- check return type = NIL (otherwise must be assignment statement)
		**)
		PROCEDURE VisitProcedureCallStatement(procedureCall: SyntaxTree.ProcedureCallStatement);
		VAR call: SyntaxTree.Designator;
		BEGIN
			IF Trace THEN D.Str("VisitProcedureCallStatement"); D.Ln; END;
			call := procedureCall.call;
			IF (call # NIL) &  ~(call IS SyntaxTree.ParameterDesignator) & ~(call IS SyntaxTree.ProcedureCallDesignator) & ~(call IS SyntaxTree.BuiltinCallDesignator)  THEN
				call := SyntaxTree.NewParameterDesignator(call.position,call,SyntaxTree.NewExpressionList());
			END;
			call := ResolveDesignator(call);

			IF call = Global.invalidDesignator THEN
				(* error already handled *)
			ELSIF ~IsCallable(call) THEN
				Error(procedureCall.position,Diagnostics.Invalid,"called object is not a procedure");
			ELSIF (call.type # NIL) &  (call.left # NIL) &  ~(SyntaxTree.WinAPIFlag IN call.left.type.resolved(SyntaxTree.ProcedureType).flags) THEN
				Error(procedureCall.position,Diagnostics.Invalid,"calling procedure with non-void return type");
				IF VerboseErrorMessage THEN Printout.Info("call ",call) END;
			END;
			procedureCall.SetCall(call);
		END VisitProcedureCallStatement;


		(** check and resolve assignment left := right
			- check left designator and right expression
			- check for operator first
			- check if assignment compatible
			- set left designator and right expression
		**)
		PROCEDURE VisitAssignment(assignment: SyntaxTree.Assignment);
		VAR left: SyntaxTree.Designator; right: SyntaxTree.Expression;
			operator: SyntaxTree.Expression;
		BEGIN
			left := ResolveDesignator(assignment.left);
			assignment.SetLeft(left);
			right := ResolveExpression(assignment.right);
			assignment.SetRight(right);

			IF (left = Global.invalidDesignator) OR (right = Global.invalidExpression) THEN
				(* error already handled *)
			ELSIF CheckVariable(left) THEN
				operator := NewOperatorCall(assignment.position,Scanner.Becomes,assignment.left,assignment.right,NIL);
				IF (operator # NIL) & (operator IS SyntaxTree.ProcedureCallDesignator) THEN
					IF (left.type.resolved IS SyntaxTree.MathArrayType) & (right.type.resolved IS SyntaxTree.MathArrayType) &
						AssignmentCompatible(left,right)
					THEN
						right := NewConversion(right.position,right,left.type.resolved);
						operator(SyntaxTree.ProcedureCallDesignator).parameters.SetExpression(1,right);
					END;
					resolvedStatement := SyntaxTree.NewProcedureCallStatement(assignment.position,operator(SyntaxTree.ProcedureCallDesignator),assignment.outer);
				ELSIF AssignmentCompatible(left,right) THEN
					assignment.SetLeft(left);
					assignment.SetRight(NewConversion(right.position,right,left.type.resolved));
					resolvedStatement := assignment;
				END;
			END;
		END VisitAssignment;

		(** check and resolve if/eslif part
			- check condition
			- check statement sequence
		**)
		PROCEDURE IfPart(ifPart: SyntaxTree.IfPart; VAR true: BOOLEAN);
		VAR prevFlags: SET; b: BOOLEAN;
		BEGIN
			prevFlags := currentFlags;
			ifPart.SetCondition(ResolveCondition(ifPart.condition));
			IF IsBooleanValue(ifPart.condition,b) THEN
				IF b=FALSE THEN
					INCL(currentFlags,SyntaxTree.UnreachableFlag);
				ELSIF b=TRUE THEN
					true := TRUE
				END;
			END;
			StatementSequence(ifPart.statements);
			currentFlags := prevFlags;
		END IfPart;

		(** check and resolve if statement
			- check if parts and else part statement sequence
		**)
		PROCEDURE VisitIfStatement(ifStatement: SyntaxTree.IfStatement);
		VAR elsif: SyntaxTree.IfPart; i: LONGINT; ifPartTrue: BOOLEAN; prevFlags: SET;
		BEGIN
			prevFlags := currentFlags;
			ifPartTrue := FALSE;
			IfPart(ifStatement.ifPart,ifPartTrue);
			FOR i := 0 TO ifStatement.ElsifParts()-1 DO
				elsif := ifStatement.GetElsifPart(i);
				IfPart(elsif,ifPartTrue);
			END;
			IF ifStatement.elsePart # NIL THEN
				IF ifPartTrue THEN
					INCL(currentFlags,SyntaxTree.UnreachableFlag);
				END;
				StatementSequence(ifStatement.elsePart)
			END;
			currentFlags := prevFlags;
		END VisitIfStatement;



		(** check and resolve with statement WITH variable: type DO ... END;
			- check type and variable
			- check that variable type is type extension of type
			- check that variable is a variable
			- enter new with scope and enter guardedVariable with same name and reference to variable
			- create if statement:
				WITH variable: type DO ... END; 	--> IF ~(variable IS type) THEN HALT(withTrap) ELSE ... END;
		**)
		PROCEDURE VisitWithStatement(withStatement: SyntaxTree.WithStatement);
		VAR variable,typeDesignator: SyntaxTree.Designator;
			type,variableType: SyntaxTree.Type;
			position: LONGINT;
			prevScope : SyntaxTree.Scope;
			guardedVariable: SyntaxTree.GuardedVariable;
			b: BOOLEAN;
		BEGIN
			prevScope := currentScope;
			position := withStatement.position;
			variable := ResolveDesignator(withStatement.variable);
			withStatement.SetVariable(variable);
			typeDesignator := ResolveDesignator(withStatement.type);
			withStatement.SetType(typeDesignator);
			IF ~(typeDesignator IS SyntaxTree.SymbolDesignator) OR ~(typeDesignator.type.resolved = SyntaxTree.typeDeclarationType) THEN
				Error(typeDesignator.position,Diagnostics.Invalid,"is not a type");
				type := Global.invalidType;
			ELSE
				type := typeDesignator(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType;
			END;

			variableType := variable.type.resolved;

			WHILE variable IS SyntaxTree.TypeGuardDesignator DO
				variable := variable(SyntaxTree.TypeGuardDesignator).left(SyntaxTree.Designator);
			END;

			IF (type.resolved = Global.invalidType) OR (variableType = Global.invalidType) THEN (* error already reported *)
			ELSIF ~(type.resolved = variableType) & ~IsExtensibleDesignator(variable) THEN
				Error(variable.position,Diagnostics.Invalid,"is not extensible designator");
			ELSIF ~(variable IS SyntaxTree.SymbolDesignator) (* OR (variable(SyntaxTree.SymbolDesignator).left # NIL) needed ?? *)  THEN
				Error(variable.position,Diagnostics.Invalid,"is no local variable ");
				IF VerboseErrorMessage THEN
					Printout.Info("variable",variable)
				END;
			ELSIF ~IsTypeExtension(variableType, type.resolved) THEN
				Error(variable.position,Diagnostics.Invalid,"withguarded symbol is no type extension of ");
				IF VerboseErrorMessage THEN
					Printout.Info("variable",variable);
					Printout.Info("type",type);
				END;
			ELSIF ~(variable(SyntaxTree.SymbolDesignator).symbol IS SyntaxTree.Variable)
					& ~(variable(SyntaxTree.SymbolDesignator).symbol IS SyntaxTree.Parameter) THEN
				Error(variable.position,Diagnostics.Invalid,"withguarded symbol is no variable ");
				IF VerboseErrorMessage THEN
					Printout.Info("variable",variable);
					Printout.Info("type",type);
				END;
			ELSE
				guardedVariable := SyntaxTree.NewGuardedVariable(variable.position,variable(SyntaxTree.SymbolDesignator).symbol.name,variable(SyntaxTree.SymbolDesignator).symbol);
				guardedVariable.SetType(type);
				currentScope := SyntaxTree.NewWithScope(currentScope,guardedVariable);
				currentScope.EnterSymbol(guardedVariable,b);
				StatementSequence(withStatement.statements);
			END;

			currentScope := prevScope;
			(*! removed code for translation WITH ... => IF a IS ... THEN ELSE ... ; should be emitted by backend *)

		END VisitWithStatement;



		(** check and resolve case part   a,b,c..d: StatementSequence
			- check expression to be constant or binary expression from .. to with constants from and to and compatible to type
			- check from < to and no overlaps between different case labels
			- check statement sequence
		**)
		PROCEDURE CasePart(casePart: SyntaxTree.CasePart; type: SyntaxTree.Type; VAR allcases: SyntaxTree.CaseConstant; VAR min,max: LONGINT);
		VAR i: LONGINT; position: LONGINT; expression,left,right: SyntaxTree.Expression; expressionType: SyntaxTree.Type;
			l,r: LONGINT; cl,cr: CHAR;
			thiscases: SyntaxTree.CaseConstant;
		BEGIN
			thiscases := NIL;
			FOR i := 0 TO casePart.elements.Length()-1 DO
				expression := casePart.elements.GetExpression(i);
				position := expression.position;
				expression := ResolveExpression(expression);
				IF expression = Global.invalidExpression THEN
					(* error already reported *)
					expressionType := Global.invalidType;
				ELSIF (expression IS SyntaxTree.RangeExpression) THEN
					left := ConstantExpression(expression(SyntaxTree.RangeExpression).from);
					right := ConstantExpression(expression(SyntaxTree.RangeExpression).to);
					IF IsStringType(left.type) & IsCharacterValue(left,cl) THEN
						left := Global.NewCharacterValue(left.position,cl);
						expression(SyntaxTree.RangeExpression).from.SetResolved(left(SyntaxTree.CharacterValue));
					END;
					IF IsStringType(right.type) & IsCharacterValue(right,cr) THEN
						right := Global.NewCharacterValue(right.position,cr);
						expression(SyntaxTree.RangeExpression).to.SetResolved(right(SyntaxTree.CharacterValue));
					END;
					expressionType := RegularType(position,left.type);
					ASSERT(left.type.resolved = right.type.resolved); (* guaranteed by parser *)
					ASSERT(expression(SyntaxTree.RangeExpression).by = NIL); (* guaranteed by VisitRangeExpression *)
				ELSE
					expression := ConstantExpression(expression);
					IF IsStringType(expression.type) & IsCharacterValue(expression,cl) THEN
						left := Global.NewCharacterValue(expression.position,cl);
						expression := casePart.elements.GetExpression(i);
						expression.SetResolved(left(SyntaxTree.CharacterValue));
						expression := left
					END;
					left := expression; right := expression;
					expressionType := RegularType(position,expression.type);
				END;

				IF (expressionType = Global.invalidType) THEN
				ELSIF ~CompatibleTo(expressionType,type) THEN
					Error(position,Diagnostics.Invalid,"inadmissible case label");
					expression := Global.invalidExpression;
				ELSE
					l := 0; r := 0;
					IF IsIntegerValue(left,l) & CheckIntegerValue(right,r) THEN
					ELSIF IsCharacterValue(left,cl) & CheckCharacterValue(right,cr) THEN
						l := ORD(cl); r := ORD(cr);
					ELSE
						expression := Global.invalidExpression
					END;

					IF expression # Global.invalidExpression THEN
						IF l>r THEN
							Error(position,Diagnostics.Invalid,"empty case label")
						ELSIF ~EnterCase(thiscases,l,r) OR ~EnterCase(allcases,l,r) THEN
							Error(position,Diagnostics.Invalid,"duplicate case label");
						ELSE
							IF l < min THEN min := l END;
							IF r > max THEN max := r END;
						END;
					END;
				END;
				casePart.elements.SetExpression(i,expression);
			END;
			(*! Coalesce(caseConstants); sort and find succeeeding numbers !!! *)
			casePart.SetConstants(thiscases);
			StatementSequence(casePart.statements);
		END CasePart;


		(** check and resolve case statement CASE variable OF ... END;
			- check variable
			- check case parts
		**)
		PROCEDURE VisitCaseStatement(caseStatement: SyntaxTree.CaseStatement);
		VAR expression: SyntaxTree.Expression; i: LONGINT; type: SyntaxTree.Type; caseList: SyntaxTree.CaseConstant;
			ch: CHAR; l: LONGINT; min,max: LONGINT;
		BEGIN
			expression := ResolveExpression(caseStatement.variable);
			type := RegularType(expression.position,expression.type);
			IF type = Global.invalidType THEN
				expression := Global.invalidExpression;
			ELSIF (type IS SyntaxTree.IntegerType) THEN
			ELSIF IsStringType(expression.type) & IsCharacterValue(expression,ch) THEN
				expression := Global.NewCharacterValue(expression.position,ch);
				type := expression.type;
			ELSIF IsCharacterType(type) THEN
			ELSE
				Error(caseStatement.variable.position,Diagnostics.Invalid,"variable must be integer or character type");
				expression := Global.invalidExpression;
			END;
			caseStatement.SetVariable(expression);
			caseList := NIL;
			min := MAX(LONGINT); max := MIN(LONGINT);
			FOR i := 0 TO caseStatement.CaseParts()-1 DO
				CasePart(caseStatement.GetCasePart(i),type,caseList,min,max);
			END;
			caseStatement.SetMinMax(min,max);
			StatementSequence(caseStatement.elsePart);
			IF expression.resolved # NIL THEN
				IF IsCharacterValue(expression,ch) THEN
					l := ORD(ch)
				ELSIF IsIntegerValue(expression,l) THEN
				END;
				IF EnterCase(caseList,l,l) & (caseStatement.elsePart = NIL) THEN Error(caseStatement.position,Diagnostics.Invalid,"no matching case label") END;
			END;

		END VisitCaseStatement;

		(** check and resolve while statement
			- check condition
			- check statement sequence
		**)
		PROCEDURE VisitWhileStatement(whileStatement: SyntaxTree.WhileStatement);
		VAR prevFlags: SET; b: BOOLEAN;
		BEGIN
			prevFlags := currentFlags;
			whileStatement.SetCondition(ResolveCondition(whileStatement.condition));
			IF IsBooleanValue(whileStatement.condition,b) THEN
				IF b=FALSE THEN
					INCL(currentFlags,SyntaxTree.UnreachableFlag);
				END;
			END;
			StatementSequence(whileStatement.statements);
			currentFlags := prevFlags;
		END VisitWhileStatement;

		(** check and resolve repeat statement
			- check condition
			- check statement sequence
		**)
		PROCEDURE VisitRepeatStatement(repeatStatement: SyntaxTree.RepeatStatement);
		BEGIN
			repeatStatement.SetCondition(ResolveCondition(repeatStatement.condition));
			StatementSequence(repeatStatement.statements);
		 END VisitRepeatStatement;


		PROCEDURE GetVariableScope(): SyntaxTree.Scope;
		VAR scope: SyntaxTree.Scope;
		BEGIN
			scope := currentScope;
			WHILE scope IS SyntaxTree.WithScope DO
				scope := scope.outerScope
			END;
			RETURN scope
		END GetVariableScope;

		(**
			create a temporary variable in current scope
		**)
		PROCEDURE GetTemporaryVariable(type: SyntaxTree.Type; index: LONGINT): SyntaxTree.Designator;
		VAR name: SyntaxTree.Identifier; string: Scanner.StringType ; var: SyntaxTree.Expression; variable: SyntaxTree.Symbol;
		scope: SyntaxTree.Scope; duplicate: BOOLEAN; offset: LONGINT;
		BEGIN
			COPY("@hiddenVar",string);
			IF index # 0 THEN
				Basic.AppendNumber(string,index);
			END;
			name := SyntaxTree.NewIdentifier(index,string);
			scope := GetVariableScope();
			variable := Find(scope, name,FALSE);
			IF variable = NIL THEN
				variable := SyntaxTree.NewVariable(index,name);
				variable.SetType(type);
				variable.SetAccess(SyntaxTree.Hidden);

				IF scope.lastVariable # NIL THEN
					offset := scope.lastVariable.offsetInBits;
				ELSE
					offset := 0;
				END;
				DEC(offset,system.SizeOf(variable.type));
				Basic.Align(offset,-system.AlignmentOf(system.variableAlignment,variable.type));
				variable(SyntaxTree.Variable).SetOffset(offset);

				scope.AddVariable(variable(SyntaxTree.Variable));
				scope.EnterSymbol(variable, duplicate);
				ASSERT(~duplicate);
			ELSE
				ASSERT(variable.type.resolved = type.resolved)
			END;
			var := NewSymbolDesignator(index,NIL,variable);
			RETURN var(SyntaxTree.Designator)
		END GetTemporaryVariable;


		(** check and resolve for statement FOR variable := from TO to BY by DO StatementSequence END;
			- check that variable is an integer variable
			- check that from is integer typed with compatible type
			- check that to has compatible type
			- check that by is constant integer with compatible type
		**)
		PROCEDURE VisitForStatement(forStatement: SyntaxTree.ForStatement);
		VAR expression: SyntaxTree.Expression; designator: SyntaxTree.Designator; type: SyntaxTree.Type;
		BEGIN
			designator := ResolveDesignator(forStatement.variable);
			type := Global.invalidType;
			IF designator.type = Global.invalidType THEN (* error already handled *)
				designator := Global.invalidDesignator;
			ELSIF ~(designator.type.resolved IS SyntaxTree.IntegerType) THEN
				Error(designator.position,Diagnostics.Invalid,"control variable of non-integer type");
				designator := Global.invalidDesignator;
			ELSIF CheckVariable(designator) THEN
				type := designator.type;
				forStatement.SetTemporary(GetTemporaryVariable(type,forStatement.position));
			END;
			forStatement.SetVariable(designator);

			expression := ResolveExpression(forStatement.from);
			IF expression = Global.invalidExpression THEN
			ELSIF ~CompatibleTo(expression.type.resolved,designator.type.resolved) THEN
				Error(expression.position,Diagnostics.Invalid,"start value of incompatible type");
				expression := Global.invalidExpression;
			ELSIF type # Global.invalidType THEN
				expression := NewConversion(expression.position,expression,type)
			END;
			forStatement.SetFrom(expression);

			expression := ResolveExpression(forStatement.to);
			IF expression = Global.invalidExpression THEN
			ELSIF ~CompatibleTo(expression.type.resolved,designator.type.resolved) THEN
				Error(expression.position,Diagnostics.Invalid,"end value of incompatible type");
				expression := Global.invalidExpression;
			ELSIF type # Global.invalidType THEN
				expression := NewConversion(expression.position,expression,type)
			END;
			forStatement.SetTo(expression);

			IF forStatement.by # NIL THEN
				expression := ConstantInteger(forStatement.by);
			ELSE
				expression := Global.NewIntegerValue(system,InvalidPosition,1);
			END;


			IF expression = Global.invalidExpression THEN
			ELSIF  ~CompatibleTo(expression.type.resolved,designator.type.resolved) THEN
				Error(expression.position,Diagnostics.Invalid,"step value of incompatible type");
			ELSIF (expression.resolved(SyntaxTree.IntegerValue).hvalue = 0) THEN
				Error(expression.position,Diagnostics.Invalid,"invalid step value");
			ELSIF type # Global.invalidType THEN
				expression := NewConversion(expression.position,expression,type)
			END;
			forStatement.SetBy(expression);

			StatementSequence(forStatement.statements);
		END VisitForStatement;

		(** check and resolve loop statement LOOP StatementSequence END
			- check statement sequence
		**)
		PROCEDURE VisitLoopStatement(loopStatement: SyntaxTree.LoopStatement);
		BEGIN
			StatementSequence(loopStatement.statements)
		END VisitLoopStatement;

		(** check and resolve exit statement EXIT
			- check that exit is within LOOP statement block
		**)
		PROCEDURE VisitExitStatement(exitStatement: SyntaxTree.ExitStatement);
		VAR outer: SyntaxTree.Statement;
		BEGIN
			outer := exitStatement.outer;
			WHILE(outer # NIL) & ~(outer IS SyntaxTree.LoopStatement) DO
				outer := outer.outer;
			END;
			IF outer = NIL THEN
				Error(exitStatement.position,Diagnostics.Invalid,"exit statement not within loop statement");
			END;
		 END VisitExitStatement;

		(** check and resolve return statement RETURN [expression]
			- check expression (if any)
			- check if in procedure scope
				- if in procedure scope then check expression compatibility
				- if not in procecdure scope then check on return without expression
		**)
		PROCEDURE VisitReturnStatement(returnStatement: SyntaxTree.ReturnStatement);
		VAR expression: SyntaxTree.Expression; position: LONGINT; procedure: SyntaxTree.Procedure;
			returnType: SyntaxTree.Type; outer: SyntaxTree.Statement; scope: SyntaxTree.Scope;
		BEGIN
			position := returnStatement.position;
			expression := returnStatement.returnValue;
			IF expression # NIL THEN
				expression := ResolveExpression(expression);
				returnStatement.SetReturnValue(expression);
			END;
			outer := returnStatement.outer;
			WHILE(outer # NIL) & ~(outer IS SyntaxTree.Body) DO
				outer := outer.outer
			END;
			IF (outer # NIL) THEN
				scope := outer(SyntaxTree.Body).inScope;
				IF ~(scope IS SyntaxTree.ProcedureScope) THEN
					IF (expression # NIL) THEN
						Error(position,Diagnostics.Invalid,"return statement with parameter not in procedure scope");
					END;
				ELSE
					procedure := scope(SyntaxTree.ProcedureScope).ownerProcedure;
					returnType := procedure.type(SyntaxTree.ProcedureType).returnType;
					IF returnType # NIL THEN
						returnType := returnType.resolved;
						IF expression = NIL THEN
							Error(position,Diagnostics.Invalid,"empty return type in procedure providing a return type")
						ELSIF ~CompatibleTo(expression.type.resolved,returnType) THEN
							Error(position,Diagnostics.Invalid,"return type not compatible");
							IF VerboseErrorMessage THEN
								Printout.Info("returnType",returnType);
								Printout.Info("expression",expression);
							END;
						ELSE
							expression := NewConversion(expression.position,expression,returnType);
							returnStatement.SetReturnValue(expression);
						END;
					ELSIF expression # NIL THEN
						Error(position,Diagnostics.Invalid,"non-empty return type in procedure providing no return type");
					END;
				END;
			END;
		 END VisitReturnStatement;

		(** check and resolve await statement AWAIT(condition: Expression)
			- check await condition
		**)
		PROCEDURE VisitAwaitStatement(awaitStatement: SyntaxTree.AwaitStatement);
		VAR condition: SyntaxTree.Expression;
		BEGIN
			condition := ResolveCondition(awaitStatement.condition);
			IF SyntaxTree.RealtimeFlag IN currentFlags THEN
				Error(awaitStatement.position,Diagnostics.Invalid,"forbidden await statement in realtime block");
			END;
			IF (condition.resolved # NIL) & (condition.resolved IS SyntaxTree.BooleanValue) THEN
				Error(awaitStatement.position,Diagnostics.Invalid,"senseless await statement with constant condition");
			END;
			awaitStatement.SetCondition(condition);
		END VisitAwaitStatement;

		(** check and resolve code statement: do nothing, must be done by assembler
		**)
		PROCEDURE VisitCode(code: SyntaxTree.Code);
		BEGIN
		END VisitCode;


		(** check and set flags of a statement block
			- check for multiply occurence of a flag
			- check and set priority only in bodies
			- check for valid names
		**)
		PROCEDURE BlockFlags(block: SyntaxTree.StatementBlock);
		VAR blockModifier: SyntaxTree.Modifier; expression: SyntaxTree.Expression; name: Scanner.StringType; flags: SET; position: LONGINT;
			forbidden: SET; flag: LONGINT;

			PROCEDURE SetProtectedRecord;
			VAR scope: SyntaxTree.Scope;
			BEGIN
				scope := currentScope;
				WHILE (scope # NIL) & ~(scope IS SyntaxTree.RecordScope) DO
					scope := scope.outerScope
				END;
				IF scope # NIL THEN
					scope(SyntaxTree.RecordScope).ownerRecord.IsProtected(TRUE);
				END;
			END SetProtectedRecord;


		BEGIN
			flags := {};
			IF ~(block IS SyntaxTree.Body) OR ~(SyntaxTree.BodyProcedureFlag IN currentFlags) OR (currentScope.outerScope # NIL) & (currentScope.outerScope IS SyntaxTree.ModuleScope) (* module body *) THEN
				forbidden := {SyntaxTree.PriorityFlag, SyntaxTree.ActiveFlag, SyntaxTree.SafeFlag, SyntaxTree.RealtimeFlag}
			ELSE
				forbidden := {};
			END;
			blockModifier := block.blockModifiers;
			WHILE(blockModifier # NIL) DO
				blockModifier.identifier.GetString(name);
				Basic.Uppercase(name,name);
				expression := blockModifier.expression;
				position := blockModifier.identifier.position;
				flag := -1;
				IF (name = Global.StringPriority) THEN
					flag := SyntaxTree.PriorityFlag;
					IF expression = NIL THEN
						Error(position,Diagnostics.Invalid,"missing priority expression");
					ELSE
						block(SyntaxTree.Body).SetPriority(expression);
					END;
				ELSIF expression # NIL THEN
					Error(expression.position,Diagnostics.Invalid,"expression not in connection with priority")
				ELSIF name = Global.StringExclusive THEN
					flag := SyntaxTree.ExclusiveFlag; SetProtectedRecord;
				ELSIF name = Global.StringActive THEN
					flag := SyntaxTree.ActiveFlag; SetProtectedRecord;
				ELSIF name = Global.StringSafe THEN
					flag := SyntaxTree.SafeFlag;
				ELSIF name = Global.StringRealtime THEN
					flag := SyntaxTree.RealtimeFlag
				ELSE
					Error(position,Diagnostics.Invalid,"unknown block modifier");
				END;

				IF flag >= 0 THEN
					IF flag IN forbidden THEN
						Error(position,Diagnostics.Invalid,"forbidden modifier");
					ELSIF flag IN flags THEN
						Error(position,Diagnostics.Invalid,"duplicate modifier");
					ELSE
						INCL(flags,flag);
					END
				END;
				blockModifier := blockModifier.nextModifier;
			END;
			block.AddFlags(flags);
		END BlockFlags;

		(** check and resolve statement block
			- check flags (exclusive)
			- check statement sequence
		**)
		PROCEDURE VisitStatementBlock(statementBlock: SyntaxTree.StatementBlock);
		VAR flags: SET;
		BEGIN
			BlockFlags(statementBlock);

			IF SyntaxTree.ExclusiveFlag IN statementBlock.flags THEN
				(* check that not in exclusive block *)
				IF SyntaxTree.ExclusiveFlag IN currentFlags THEN
					Error (statementBlock.position,Diagnostics.Invalid,"forbidden recursive exclusive")
				ELSIF SyntaxTree.RealtimeFlag IN currentFlags THEN
					Error( statementBlock.position,Diagnostics.Invalid,"forbidden exculsive in realtime block");
				END;
			END;
			flags := currentFlags;
			currentFlags := currentFlags + statementBlock.flags;
			StatementSequence(statementBlock.statements);
			currentFlags := flags;
		END VisitStatementBlock;

		(** check and resolve body
			- check flags (active, priority, safe)
			- check body and finally part
		 **)
		PROCEDURE Body(body: SyntaxTree.Body);
		BEGIN
			VisitStatementBlock(body);
			IF SyntaxTree.ActiveFlag IN body.flags THEN
				IF  ~(SyntaxTree.BodyProcedureFlag IN currentFlags) THEN
					Error(body.position,Diagnostics.Invalid,"active flag not in object body");
				ELSIF SyntaxTree.PriorityFlag IN body.flags THEN
					body.SetPriority(ConstantInteger(body.priority));
				END;
			ELSIF SyntaxTree.SafeFlag IN body.flags THEN
				Error(body.position,Diagnostics.Invalid,"safe flag not in active body");
			ELSIF SyntaxTree.PriorityFlag IN body.flags THEN
				Error(body.position,Diagnostics.Invalid,"priority flag not in active body");
			END;
			StatementSequence(body.finally)
		END Body;

		(*** scopes ***)

		(** Register a symbol in a scope. Check for duplicate symbols and collision with globally defined symbols. **)
		PROCEDURE Register(symbol: SyntaxTree.Symbol; scope: SyntaxTree.Scope; allowDuplicate: BOOLEAN);
		VAR duplicateSymbol: BOOLEAN;
		BEGIN
			ASSERT(symbol.name # NIL);
			ASSERT(symbol.name.name # Basic.MakeString(""));
			IF ~allowDuplicate & (global.FindSymbol(symbol.name)#NIL) THEN
				Error(symbol.position,Diagnostics.Invalid,"globally defined keyword")
			END;

			scope.EnterSymbol(symbol,duplicateSymbol);
			IF ~allowDuplicate & duplicateSymbol THEN
				Error(symbol.position,Basic.MultiplyDefinedIdentifier,"");
				IF VerboseErrorMessage THEN
					Printout.Info("multiply defined identifier",symbol);
					Printout.Info("with name", symbol.name);
					Printout.Info("in scope",scope);
				END;
			END;
		END Register;

		(**
			implementation: check and resolve an implementation part
		**)
		(*!	can in principle be done in parallel on different checkers: implementations do only depend on declarations)
		 move implementation checker to a separate object ? *)
		PROCEDURE Implementation(scope: SyntaxTree.Scope);
		VAR prevScope: SyntaxTree.Scope; prevFlags: SET;
		BEGIN
			prevFlags := currentFlags;
			prevScope := currentScope;
			currentScope := scope;
			IF (scope IS SyntaxTree.ProcedureScope) THEN
				currentFlags := currentFlags + scope(SyntaxTree.ProcedureScope).ownerProcedure.type(SyntaxTree.ProcedureType).flags;
				currentFlags := currentFlags + scope(SyntaxTree.ProcedureScope).ownerProcedure.flags;
			END;
			IF (scope IS SyntaxTree.ProcedureScope) & (scope(SyntaxTree.ProcedureScope).body # NIL) (* & ~(scope IS SyntaxTree.RecordScope) *) THEN
				(* module body, record bodies are wrapped into an artifical procedure *)
				Body(scope(SyntaxTree.ProcedureScope).body)
			END;
			currentScope := prevScope;
			currentFlags := prevFlags;
		END Implementation;

		(** implementation phase:
			check and resolve all scopes (implementation phase) that have been entered into a list during the declaration phase
		**)
		PROCEDURE Implementations(x: SyntaxTree.Module);
		VAR  scope: SyntaxTree.Scope; prevPhase: LONGINT;
		BEGIN
			prevPhase := phase;
			phase := ImplementationPhase;
			scope := x.firstScope;
			WHILE(scope # NIL) DO
				Implementation(scope);
				scope := scope.nextScope;
			END;
			phase := prevPhase;
		END Implementations;

		(** declaration phase:
			check and resolve all declarations of a scope (module scope, procedure scope, record scope):
			- import lists (for module scopes)
			- parameter list (for procedure scopes)
			- constant declarations
			- type declarations
			- variable declarations
			- procedure declarations
			preformed in two stages:
				- first all symbols are entered into the symbol table (with uniqueness check),
				- then all symbols are resolved
			after declaration check, bodies are entered into the global list of implementations that remain to be resolved after all declarations.

			Declarations depend on other declarations, this procedure is neither thread safe not would it be wise to try concurrency here
		**)
		PROCEDURE Declarations(scope: SyntaxTree.Scope);
		VAR
			constant: SyntaxTree.Constant;
			typeDeclaration: SyntaxTree.TypeDeclaration;
			variable: SyntaxTree.Variable;
			procedure: SyntaxTree.Procedure;
			prevScope: SyntaxTree.Scope;
			parameter: SyntaxTree.Parameter;
			import: SyntaxTree.Import;
			symbol: SyntaxTree.Symbol;
			prevPhase: LONGINT;

		BEGIN
			prevPhase := phase;
			phase := DeclarationPhase;
			prevScope := currentScope;
			currentScope := scope;

			(* first enter all symbols in scope *)
			IF scope IS SyntaxTree.ModuleScope THEN
				(* treat imports first for a module scope, , set default context if necessary *)
				import := scope(SyntaxTree.ModuleScope).firstImport;
				WHILE(import # NIL) DO
					IF import.context = NIL THEN import.SetContext(scope.ownerModule.context) END;
					Register(import, currentScope, FALSE); import := import.nextImport;
				END;
			ELSIF scope IS SyntaxTree.ProcedureScope THEN
				(* enter parameters for a procedure scope *)
				parameter := scope(SyntaxTree.ProcedureScope).ownerProcedure.type.resolved(SyntaxTree.ProcedureType).firstParameter;
				WHILE(parameter # NIL) DO
					Register(parameter,currentScope, FALSE); parameter := parameter.nextParameter;
				END;
				parameter := scope(SyntaxTree.ProcedureScope).ownerProcedure.type.resolved(SyntaxTree.ProcedureType).returnParameter;
				IF parameter # NIL THEN
					Register(parameter,currentScope, FALSE);
				END;
			END;
			(* constants *)
			constant := scope.firstConstant;
			WHILE (constant # NIL) DO
				Register(constant, currentScope, FALSE); constant := constant.nextConstant;
			END;
			(* type declarations *)
			typeDeclaration := scope.firstTypeDeclaration;
			WHILE (typeDeclaration # NIL) DO
				Register(typeDeclaration, currentScope, FALSE); typeDeclaration := typeDeclaration.nextTypeDeclaration;
			END;
			(* variables *)
			variable := scope.firstVariable;
			WHILE (variable # NIL) DO
				Register(variable, currentScope, FALSE); variable := variable.nextVariable;
			END;
			(* procedures *)
			procedure := scope.firstProcedure;
			WHILE (procedure # NIL) DO
				Register(procedure, currentScope, procedure IS SyntaxTree.Operator); procedure := procedure.nextProcedure;
			END;

			(* now process all symbols without any presumption on the order *)

			symbol := scope.firstSymbol;
			WHILE(symbol # NIL) DO
				IF ~(symbol IS SyntaxTree.Parameter) THEN
					ResolveSymbol(symbol)
				END;
				symbol := symbol.nextSymbol;
			END;

			IF ~error THEN system.GenerateVariableOffsets(scope) END;

			IF scope.ownerModule # NIL THEN
				(* add scope to global list of all scopes, very handy for code generation and for checking implementations *)
				scope.ownerModule.AddScope(scope);
			END;

			phase := prevPhase;
			currentScope := prevScope;
		END Declarations;

		(** check module:
			- check module declaration
			- add context, if necessary
			- remove module from import cache, if necessary
			- check declarations
			- resolve all type fixes
			- check implementation (bodies)
		**)
		PROCEDURE Module*(x: SyntaxTree.Module);
		BEGIN
			ASSERT(x # NIL);
			global := system.globalScope[x.case];
			x.moduleScope.SetGlobalScope(global);
			IF x.name.Equals(Global.SystemName) OR x.name.Equals(Global.systemName) THEN Error(x.position,Diagnostics.Invalid,"name reserved") END;
			IF x.context = NIL THEN x.SetContext(Global.A2Name) END;
			RemoveModuleFromCache(importCache,x);
			Declarations(x.moduleScope);
			FixTypes();
			Implementations(x);
		END Module;


	END Checker;



	Same= POINTER TO RECORD
		t1,t2: SyntaxTree.Type;
		next: Same;
	END;

	PROCEDURE ToMemoryUnits(system: Global.System; size: LONGINT): LONGINT;
	BEGIN
		ASSERT(size MOD system.dataUnit = 0);
		RETURN size DIV system.dataUnit
	END ToMemoryUnits;

	(* Returns TRUE if the built-in function GETPROCEDURE can be used with this procedure type *)
	PROCEDURE GetProcedureAllowed*(type: SyntaxTree.Type) : BOOLEAN;
	VAR procedureType: SyntaxTree.ProcedureType; numberParameters: LONGINT;

		PROCEDURE TypeAllowed(t : SyntaxTree.Type) : BOOLEAN;
		BEGIN
			IF t = NIL THEN
				RETURN TRUE
			ELSE
				t := t.resolved;
				RETURN (t IS SyntaxTree.RecordType) OR IsPointerToRecord(t);
			END;
		END TypeAllowed;

	BEGIN
		type := type.resolved;
		IF ~(type IS SyntaxTree.ProcedureType) THEN
			RETURN FALSE
		ELSE
			procedureType := type(SyntaxTree.ProcedureType);
			numberParameters := procedureType.numberParameters-procedureType.numberHiddenParameters;
			RETURN
				(numberParameters = 0) & TypeAllowed(procedureType.returnType) OR
				(numberParameters = 1) & TypeAllowed(procedureType.firstParameter.type) & TypeAllowed(procedureType.returnType) OR
				(numberParameters = 1) & (procedureType.firstParameter.procedureType.resolved = Global.Any) & (procedureType.returnType.resolved = Global.Any)
		END;
	END GetProcedureAllowed;

	(** check import cache: if module x is in current import cache then remove x and all modules importing x from the cache **)
	PROCEDURE RemoveModuleFromCache*(importCache: SyntaxTree.ModuleScope; x: SyntaxTree.Module);
	VAR import: SyntaxTree.Import;
	BEGIN
		import := importCache.ImportByModuleName(x.name,x.context);
		IF import # NIL THEN
			importCache.RemoveImporters(x.name,x.context);
		END;
	END RemoveModuleFromCache;

	PROCEDURE CompatibleTo(this,to: SyntaxTree.Type): BOOLEAN;
	(* to <- this assignment compatibility *)
	VAR result: BOOLEAN;
	BEGIN
		IF this= NIL THEN result := (to=NIL)
		ELSIF to=NIL THEN result := FALSE
		ELSIF to=Global.invalidType THEN result := FALSE
		ELSE
			this := this.resolved; to := to.resolved;
			IF to = this THEN
				result := ~(to IS SyntaxTree.ArrayType) OR (to(SyntaxTree.ArrayType).form # SyntaxTree.Open);
			ELSIF to IS SyntaxTree.BasicType THEN
				IF (to IS SyntaxTree.NumberType) & (this IS SyntaxTree.NumberType) THEN
					result := Global.BasicTypeDistance(this(SyntaxTree.BasicType),to(SyntaxTree.BasicType)) < Infinity;
				ELSIF to = Global.Any THEN
					result :=  (this IS SyntaxTree.RecordType) & this(SyntaxTree.RecordType).isObject OR (this IS SyntaxTree.PointerType) OR (this IS SyntaxTree.ProcedureType) OR (this =Global.Nil) OR (this = Global.Any) OR (this=Global.Object);
				ELSIF to = Global.Object THEN
					result := IsPointerToRecord(this) OR (this = Global.Nil) OR (this = Global.Object) OR (this = Global.Any) (*! remove when symbol file can distinguish OBJECT from ANY *) ;
				ELSIF to = Global.Byte THEN
					result := (this = Global.Shortint) OR IsCharacterType(this)
				ELSIF to = Global.Char THEN
					result := IsCharacterType(this)
				ELSE
					result := FALSE
				END;
			ELSIF to IS SyntaxTree.PointerType THEN
				result := IsPointerType(this) & (IsTypeExtension(to,this) OR ((to(SyntaxTree.PointerType).pointerBase.resolved IS SyntaxTree.ArrayType) & SameType(to,this,NIL))) OR (this = Global.Nil)
			ELSIF to IS SyntaxTree.ProcedureType THEN
				result := (this = Global.Nil) OR (this IS SyntaxTree.ProcedureType) & SameType(to(SyntaxTree.ProcedureType),this(SyntaxTree.ProcedureType),NIL)
					& (~(SyntaxTree.DelegateFlag IN this(SyntaxTree.ProcedureType).flags) OR (SyntaxTree.DelegateFlag IN to(SyntaxTree.ProcedureType).flags))
					& (~(SyntaxTree.RealtimeFlag IN to(SyntaxTree.ProcedureType).flags) OR (SyntaxTree.RealtimeFlag IN this(SyntaxTree.ProcedureType).flags))
			ELSIF (to IS SyntaxTree.RecordType) & to(SyntaxTree.RecordType).isObject THEN
				result := (this = Global.Nil) OR IsTypeExtension(to,this);
			ELSIF to IS SyntaxTree.RecordType THEN
				result :=  (this IS SyntaxTree.RecordType) & IsTypeExtension(to,this);
			ELSIF to IS SyntaxTree.ArrayType THEN
				IF IsStringType(to) & (this IS SyntaxTree.StringType) THEN
					result := (to(SyntaxTree.ArrayType).form = SyntaxTree.Open) OR (to(SyntaxTree.ArrayType).staticLength >= this(SyntaxTree.StringType).length)
				ELSE
					result := (to(SyntaxTree.ArrayType).staticLength # 0) & SameType(to,this,NIL)
				END;
			ELSIF to IS SyntaxTree.MathArrayType THEN
				IF this IS SyntaxTree.MathArrayType THEN
					IF to(SyntaxTree.MathArrayType).arrayBase.resolved = Global.All THEN
						IF to(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
							result := TRUE;
						ELSE
							result := ~(this(SyntaxTree.MathArrayType).arrayBase.resolved IS SyntaxTree.MathArrayType);
						END;
						(* special case: ARRAY [...] OF SYSTEM.ALL *)
					ELSIF (to(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor) OR (this(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor) THEN
						(* ARRAY [?] OF <- ARRAY [x,...,x] OF *)
						result := CompatibleTo(ArrayBase(this,Infinity),ArrayBase(to,Infinity));
					ELSIF (to(SyntaxTree.MathArrayType).form = SyntaxTree.Open) OR (this(SyntaxTree.MathArrayType).form = SyntaxTree.Open)
						OR (to(SyntaxTree.MathArrayType).staticLength = this(SyntaxTree.MathArrayType).staticLength) THEN
						(* ARRAY [x] OF <- ARRAY [x] OF  *)
						result := CompatibleTo(this(SyntaxTree.MathArrayType).arrayBase,to(SyntaxTree.MathArrayType).arrayBase);
					ELSE
						result := FALSE
					END;
				ELSE
					result := FALSE;
				END;
			ELSIF to IS SyntaxTree.StringType THEN
				result := FALSE;
			ELSIF to IS SyntaxTree.EnumerationType THEN
				result := IsEnumerationExtension(this,to);
			ELSE
				Printout.Info("CompatibleTo",to);
				HALT(100); (* implement missing type check *)
			END;

		END;
		RETURN result
	END CompatibleTo;


	PROCEDURE OpenArrayCompatible(formalType: SyntaxTree.ArrayType; actualType: SyntaxTree.Type): BOOLEAN;
	VAR arrayBase: SyntaxTree.Type; result: BOOLEAN;

		PROCEDURE TC(formal,actual: SyntaxTree.Type): BOOLEAN;
		VAR actualBase,formalBase: SyntaxTree.Type; result: BOOLEAN;
		BEGIN
			result := SameType(formal,actual,NIL);
			IF ~result & (formal IS SyntaxTree.ArrayType) & (actual IS SyntaxTree.ArrayType) THEN
				actualBase := actual(SyntaxTree.ArrayType).arrayBase.resolved;
				formalBase := formal(SyntaxTree.ArrayType).arrayBase.resolved;
				result := (formal(SyntaxTree.ArrayType).form = SyntaxTree.Open) & TC(formalBase,actualBase)
			END;
			RETURN result
		END TC;

	BEGIN
		IF formalType.form # SyntaxTree.Open THEN result := FALSE
		ELSE
			arrayBase := formalType.arrayBase.resolved;
			IF (actualType IS SyntaxTree.StringType) THEN
				result := arrayBase = Global.Char8
			ELSIF actualType IS SyntaxTree.ArrayType THEN
				result := (arrayBase = Global.Byte) OR TC(formalType,actualType)
			ELSE
				result := (arrayBase = Global.Byte)
			END;
		END;
		RETURN result
	END OpenArrayCompatible;

	PROCEDURE MathArrayCompatible(formalType: SyntaxTree.MathArrayType; actualType: SyntaxTree.Type): BOOLEAN;
	(* special compatibility rule for parameters of the form VAR A: ARRAY [x] OF , VAR A: ARRAY [*] OF and VAR A: ARRAY [?] OF  *)
	VAR formalBase,actualBase: SyntaxTree.Type; result: BOOLEAN; actualArray: SyntaxTree.MathArrayType;
	BEGIN
		IF actualType IS SyntaxTree.MathArrayType THEN
			actualArray := actualType(SyntaxTree.MathArrayType);
			IF (formalType.form = SyntaxTree.Tensor) OR (actualArray.form = SyntaxTree.Tensor) THEN
				(*
					ARRAY [?] OF  -> ARRAY [?|*|k] OF
					ARRAY [?|*|k] OF -> ARRAY [?] OF
				*)
				actualBase := ArrayBase(actualType,Infinity);
				formalBase := ArrayBase(formalType,Infinity);
				result := SameType(formalBase,actualBase,NIL) OR (formalBase = Global.All);
			ELSE
				(*
					ARRAY [*|k] OF -> ARRAY [*|n] OF
				*)
				formalBase := formalType.arrayBase.resolved;
				actualBase := actualArray.arrayBase.resolved;
				IF (formalType.form = SyntaxTree.Static) & (actualArray.form = SyntaxTree.Static) THEN
					(*
						ARRAY [k] -> ARRAY [n]
					*)
					result := (formalType.staticLength = actualArray.staticLength)
				ELSE
					result := TRUE
				END;
				IF ~result THEN
				ELSIF formalBase IS SyntaxTree.MathArrayType THEN
					result := MathArrayCompatible(formalBase(SyntaxTree.MathArrayType),actualBase)
				ELSIF formalBase = Global.All THEN
					result := ~(actualBase IS SyntaxTree.MathArrayType);
				ELSE
					result := SameType(formalBase,actualBase,NIL)
				END;
			END;
		ELSE
			result := FALSE
		END;
		RETURN result
	END MathArrayCompatible;



	(**
		Math Array Type distance for assignments / parameter passings of the form
		from -> to
		variants:
		ARRAY [num] | ARRAY [*] | ARRAY [?] -> ARRAY [num] | ARRAY[*] | ARRAY [?]

		allowed:
			static -> static (& size match)
			static -> open
			static -> tensor
			open -> open
			open -> tensor
			open -> static
			tensor -> tensor
			tensor -> open
			tensor -> static
	**)
	(*! think about the metric here: is form matching more important than element type matching? *)
	PROCEDURE MathArrayTypeDistance(from,to: SyntaxTree.MathArrayType): LONGINT;
	VAR i: LONGINT; fromBase, toBase: SyntaxTree.Type;
	BEGIN
		fromBase := from.arrayBase.resolved;
		toBase := to.arrayBase.resolved;
		i := Infinity;
		IF from = to THEN
			i := 0;
		ELSIF (from.form = to.form) THEN
			(* static -> static, open -> open, tensor -> tensor *)
			IF (from.form # SyntaxTree.Static) OR (from.staticLength = to.staticLength) THEN
				IF fromBase = toBase THEN i := 0
				ELSIF toBase = Global.All THEN i := 1
				ELSIF (fromBase IS SyntaxTree.MathArrayType) & (toBase IS SyntaxTree.MathArrayType) THEN
					i := MathArrayTypeDistance(fromBase(SyntaxTree.MathArrayType),toBase(SyntaxTree.MathArrayType));
				END;
			END;
		ELSIF (to.form = SyntaxTree.Static) THEN
			(* forbidden *)
		ELSIF (from.form = SyntaxTree.Tensor) OR (to.form = SyntaxTree.Tensor) THEN
			(* static -> tensor, open -> tensor, tensor -> open *)
			IF toBase=fromBase THEN i := 0;
			ELSIF toBase = Global.All THEN i := 1;
			ELSIF (toBase IS SyntaxTree.MathArrayType) THEN
				toBase := ArrayBase(toBase,Infinity);
				IF fromBase=toBase THEN i := 0 END;
			ELSIF (fromBase IS SyntaxTree.MathArrayType) THEN
				fromBase := ArrayBase(fromBase,Infinity);
				IF fromBase=toBase THEN i := 0 END;
			END;
			IF i # Infinity THEN INC(i,2) END;
		ELSIF (from.form = SyntaxTree.Static) THEN
			(* static -> open *)
			IF toBase=fromBase THEN i := 0
			ELSIF toBase = Global.All THEN i := 1
			ELSIF (toBase IS SyntaxTree.MathArrayType) & (fromBase IS SyntaxTree.MathArrayType) THEN
				i := MathArrayTypeDistance(fromBase(SyntaxTree.MathArrayType),toBase(SyntaxTree.MathArrayType));
			END;
			IF i # Infinity THEN INC(i,1) END;
		ELSE HALT(100); (* unknown case *)
		END;
		RETURN i;
	END MathArrayTypeDistance;

	(** compute and return the distance of two array types
	- return the distance of the base types
	**)
	PROCEDURE ArrayTypeDistance(from, to: SyntaxTree.ArrayType): LONGINT;
	VAR i: LONGINT;
	BEGIN
		i := Infinity;
		IF from = to THEN
			i := 0
		ELSE
			i := TypeDistance(from.arrayBase.resolved, to.arrayBase.resolved,FALSE);
		(*
		ELSIF (from.mode = static) & (to.mode IN {open}) THEN
			i := TypeDistance(from.base, to.base);
			IF i >= 0 THEN INC(i) END
		ELSIF (from.mode = open) & (to.mode = open) THEN
			i := TypeDistance(from.base, to.base);
		*)
		END;
		RETURN i
	END ArrayTypeDistance;

	(** compute the signature distance of a procedure and an actual parameter list
		- if any of the parameters are not compatible, the result is infinite
		- add up and return the distance over all parameters
	**)
	PROCEDURE Distance(procedureType: SyntaxTree.ProcedureType; actualParameters: SyntaxTree.ExpressionList): LONGINT;
	VAR result: LONGINT; formalParameter: SyntaxTree.Parameter; actualParameter: SyntaxTree.Expression;
	distance: LONGINT; baseFormal,baseActual: SyntaxTree.Type; i: LONGINT;
	BEGIN
		IF actualParameters.Length() # (procedureType.numberParameters-procedureType.numberHiddenParameters) THEN
			result := Infinity
		ELSE
			formalParameter := procedureType.firstParameter;
			i := 0;
			result := 0;
			(*! taken from paco, seems to not be 100% correct, check (in particular array part -> length of arrays??) *)
			WHILE (formalParameter # NIL) & (formalParameter.access # SyntaxTree.Hidden) & (result # Infinity) DO
				actualParameter := actualParameters.GetExpression(i);
				distance := TypeDistance(actualParameter.type.resolved,formalParameter.type.resolved,formalParameter.kind = SyntaxTree.VarParameter);
				IF distance = Infinity THEN
					result := Infinity;
				ELSE
					IF (formalParameter.kind = SyntaxTree.VarParameter) & (result # 0) THEN
						IF ~(formalParameter.type.resolved IS SyntaxTree.ArrayType) OR ~(actualParameter.type.resolved IS SyntaxTree.ArrayType) THEN
							result := Infinity
						ELSE
							baseActual := actualParameter.type.resolved(SyntaxTree.ArrayType).arrayBase.resolved;
							baseFormal := formalParameter.type.resolved(SyntaxTree.ArrayType).arrayBase.resolved;
							WHILE(baseActual IS SyntaxTree.ArrayType) & (baseFormal IS SyntaxTree.ArrayType) DO
								baseActual := baseActual(SyntaxTree.ArrayType).arrayBase.resolved;
								baseFormal := baseFormal(SyntaxTree.ArrayType).arrayBase.resolved;
							END;
							IF TypeDistance(baseActual,baseFormal,FALSE) # 0 THEN
								result := Infinity
							END;
						END;
					ELSE
						INC(result,distance);
					END;
				END;
				formalParameter := formalParameter.nextParameter; INC(i);
			END;
		END;
		ASSERT(result >= 0);
		RETURN result
	END Distance;

	(** compute and return the distance between two types, used for computation of signature distance
		from -> to
	**)
	PROCEDURE TypeDistance(from, to: SyntaxTree.Type; varpar: BOOLEAN): LONGINT;
	VAR i: LONGINT; ptr: SyntaxTree.PointerType;
	BEGIN
		i := Infinity;
		IF from = to THEN
			i := 0
		ELSIF to = Global.All THEN
			i := 1;
		ELSIF from = Global.All THEN
			i := 1;
		ELSIF (to IS SyntaxTree.ArrayType) & (to(SyntaxTree.ArrayType).length = NIL) & (to(SyntaxTree.ArrayType).arrayBase.resolved = Global.Byte) THEN
			i := 1
		ELSIF (from IS SyntaxTree.StringType) THEN
			IF (to IS SyntaxTree.ArrayType) & (to(SyntaxTree.ArrayType).length = NIL) & (to(SyntaxTree.ArrayType).arrayBase.resolved = Global.Char8) THEN  i := 1  END
		ELSIF (from = Global.Char8) THEN
			IF (to IS SyntaxTree.ArrayType) & (to(SyntaxTree.ArrayType).length = NIL) & (to(SyntaxTree.ArrayType).arrayBase.resolved = Global.Char8) THEN  i := 1
			ELSIF to = Global.Byte THEN i := 1 END
		ELSIF (from = Global.Shortint) & (to = Global.Byte) THEN
			i := 1
		ELSIF (from = Global.Nil) THEN
			IF (to = Global.Any) OR (to = Global.Object) OR (to IS SyntaxTree.PointerType) OR (to IS SyntaxTree.ProcedureType) THEN i := 1 END
		(*
		ELSIF (from = NoType) THEN
			IF (to IS Delegate) THEN i := 1 END	(*special case: procedure -> proctype, not resolved yet*)
		*)
		ELSIF (from IS SyntaxTree.BasicType) THEN
			IF to IS SyntaxTree.BasicType THEN  i := Global.BasicTypeDistance(from(SyntaxTree.BasicType), to(SyntaxTree.BasicType)) END
		ELSIF (from IS SyntaxTree.ArrayType) THEN
			IF to IS SyntaxTree.ArrayType THEN i := ArrayTypeDistance(from(SyntaxTree.ArrayType), to(SyntaxTree.ArrayType)) END
		ELSIF (from IS SyntaxTree.RecordType) THEN
			IF to IS SyntaxTree.RecordType THEN i := RecordTypeDistance(from(SyntaxTree.RecordType), to (SyntaxTree.RecordType)) END
		ELSIF (from IS SyntaxTree.MathArrayType) THEN
			IF to IS SyntaxTree.MathArrayType THEN
				IF varpar & (from(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor) & (to(SyntaxTree.MathArrayType).form # SyntaxTree.Tensor) THEN
					i := Infinity;
				ELSE
					i := MathArrayTypeDistance(from(SyntaxTree.MathArrayType), to(SyntaxTree.MathArrayType))
				END;
			END
		ELSIF (from IS SyntaxTree.PointerType) THEN
			ptr := from(SyntaxTree.PointerType);
			IF (to = Global.Any) THEN i := 1
			ELSIF to IS SyntaxTree.PointerType THEN i := PointerTypeDistance(ptr, to(SyntaxTree.PointerType))
			(* ELSE i := TypeDistance(ptr.base, to); *)
			END
		(*no procedure test, procedure must be the same*)
		END;
		RETURN i
	END TypeDistance;

	PROCEDURE IsIntegerValue(x: SyntaxTree.Expression; VAR value: LONGINT): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		IF (x.resolved # NIL) & (x.resolved IS SyntaxTree.IntegerValue) THEN
			value :=  x.resolved(SyntaxTree.IntegerValue).value;
			result := TRUE
		ELSE
			result := FALSE
		END;
		RETURN result
	END IsIntegerValue;

	PROCEDURE IsRealValue(x: SyntaxTree.Expression; VAR value: LONGREAL): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		IF  (x.resolved # NIL) & (x.resolved IS SyntaxTree.RealValue) THEN
			value :=  x.resolved(SyntaxTree.RealValue).value;
			result := TRUE
		ELSE
			result := FALSE
		END;
		RETURN result
	END IsRealValue;

	PROCEDURE IsCharacterValue(x: SyntaxTree.Expression; VAR value: CHAR): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		IF  (x.resolved # NIL) & (x.resolved IS SyntaxTree.CharacterValue) THEN
			value :=  x.resolved(SyntaxTree.CharacterValue).value;
			result := TRUE
		ELSIF (x.resolved # NIL) & (x.resolved IS SyntaxTree.StringValue) & (x.resolved(SyntaxTree.StringValue).length =2) THEN
			result := TRUE;
			value := x.resolved(SyntaxTree.StringValue).value[0];
		ELSE
			result := FALSE
		END;
		RETURN result
	END IsCharacterValue;

	PROCEDURE IsBooleanValue(x: SyntaxTree.Expression; VAR value: BOOLEAN): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		IF  (x.resolved # NIL) & (x.resolved IS SyntaxTree.BooleanValue) THEN
			value :=  x.resolved(SyntaxTree.BooleanValue).value;
			result := TRUE
		ELSE
			result := FALSE
		END;
		RETURN result
	END IsBooleanValue;

	PROCEDURE IsSetValue(x: SyntaxTree.Expression; VAR value: SET): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		IF  (x.resolved # NIL) & (x.resolved IS SyntaxTree.SetValue) THEN
			value :=  x.resolved(SyntaxTree.SetValue).value;
			result := TRUE
		ELSE
			result := FALSE
		END;
		RETURN result
	END IsSetValue;

	PROCEDURE IsStringValue(x: SyntaxTree.Expression; VAR value: Scanner.StringType): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		IF  (x.resolved # NIL) & (x.resolved IS SyntaxTree.StringValue) THEN
			value :=  x.resolved(SyntaxTree.StringValue).value;
			result := TRUE
		ELSE
			result := FALSE
		END;
		RETURN result
	END IsStringValue;

	PROCEDURE Indexable(x: SyntaxTree.Type): BOOLEAN;
	BEGIN
		x := x.resolved;
		RETURN (x IS SyntaxTree.ArrayType) OR (x IS SyntaxTree.MathArrayType);
	END Indexable;




	PROCEDURE SameType(t1,t2: SyntaxTree.Type; sameList: Same): BOOLEAN;
	VAR result: BOOLEAN; s: Same;

		PROCEDURE CheckRecursion(t1,t2: SyntaxTree.Type): BOOLEAN;
		VAR result: BOOLEAN;
		BEGIN
			result := FALSE;
			s := sameList;
			WHILE(s # NIL) DO
				IF (s.t1=t1) & (s.t2=t2) THEN result := TRUE END;
				s := s.next;
			END;
			IF ~result THEN
				NEW(s); s.t1 := t1; s.t2 := t2; s.next := sameList; sameList := s;
			END;
			RETURN result
		END CheckRecursion;

		PROCEDURE SameArrayType(t1,t2: SyntaxTree.ArrayType): BOOLEAN;
		BEGIN
			result := CheckRecursion(t1,t2);
			RETURN result OR (t1.staticLength = t2.staticLength) & SameType(t1.arrayBase,t2.arrayBase,sameList)
		END SameArrayType;

		PROCEDURE SameMathArrayType(t1,t2: SyntaxTree.MathArrayType): BOOLEAN;
		BEGIN
			RETURN (t1.form = t2.form) & (t1.staticLength = t2.staticLength) & SameType(t1.arrayBase,t2.arrayBase,sameList)
		END SameMathArrayType;

		PROCEDURE SameProcedureType(t1,t2: SyntaxTree.ProcedureType): BOOLEAN;
		VAR p1,p2: SyntaxTree.Parameter; result: BOOLEAN;
		BEGIN
			(* special cycle check for procedures, for example:
				A = PROCEDURE (b: B);
				B = PROCEDURE (a: A);
				VAR variable: A; result: B;
				BEGIN  result := variable;
			*)

			result := CheckRecursion(t1,t2);
			IF ~result THEN
				IF SameType(t1.returnType,t2.returnType,sameList) THEN
					p1 := t1.firstParameter; p2 := t2.firstParameter;
					WHILE (p1 # NIL) & (p2#NIL) &(p1.access # SyntaxTree.Hidden) & (p2.access # SyntaxTree.Hidden) & (p1.kind = p2.kind) & SameType(p1.type,p2.type,sameList) DO
						p1 := p1.nextParameter; p2 := p2.nextParameter;
					END;
					result := ((p1=NIL) OR (p1.access = SyntaxTree.Hidden)) & ((p2=NIL)  OR (p2.access= SyntaxTree.Hidden));
				ELSE
					result := FALSE
				END;
			END;
			result := result & (t1.flags * {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag} = t2.flags * {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag} );
			RETURN result
		END SameProcedureType;

	BEGIN


		IF result THEN (* same type via recursion ... *)
		ELSIF t1=NIL THEN result := t2=NIL
		ELSIF t2=NIL THEN result := FALSE
		ELSE
			t1 := t1.resolved; t2 := t2.resolved;
			IF (t1 = Global.invalidType) OR (t2=Global.invalidType) THEN (* error already handled elsewhere *)
				result := TRUE
			ELSIF t1=t2 THEN
				result := TRUE
			ELSIF (t1=Global.Object) & (t2=Global.Any) THEN (*! only because we want to get rid of ANY anyway and binary symbol file cannot distinguish the two *)
				result := TRUE
			ELSIF (t2=Global.Object) & (t1=Global.Any) THEN (*! only because we want to get rid of ANY anyway and binary symbol file cannot distinguish the two *)
				result := TRUE
			ELSIF t1 IS SyntaxTree.BasicType THEN
				result := t1=t2;
			ELSIF t1 IS SyntaxTree.ArrayType THEN
				result := (t2 IS SyntaxTree.ArrayType) & SameArrayType(t1(SyntaxTree.ArrayType),t2(SyntaxTree.ArrayType))
			ELSIF t1 IS SyntaxTree.MathArrayType THEN
				result := (t2 IS SyntaxTree.MathArrayType) & SameMathArrayType(t1(SyntaxTree.MathArrayType),t2(SyntaxTree.MathArrayType))
			ELSIF (t1 IS SyntaxTree.RecordType) & t1(SyntaxTree.RecordType).isObject THEN
				result := t1=t2
			ELSIF t1 IS SyntaxTree.RecordType THEN
				result := t1=t2
			ELSIF t1 IS SyntaxTree.PointerType THEN
				result := (t2 IS SyntaxTree.PointerType) & SameType(t1(SyntaxTree.PointerType).pointerBase,t2(SyntaxTree.PointerType).pointerBase,sameList)
			ELSIF t1 IS SyntaxTree.ProcedureType THEN
				result := (t2 IS SyntaxTree.ProcedureType) & SameProcedureType(t1(SyntaxTree.ProcedureType),t2(SyntaxTree.ProcedureType))
			ELSIF t1 IS SyntaxTree.EnumerationType THEN
				result := t1=t2;
			ELSE
				HALT(100); (* implement missing type check *)
			END;
		END;
		RETURN result
	END SameType;

	PROCEDURE ArrayBase*(t: SyntaxTree.Type; max: LONGINT): SyntaxTree.Type;
	BEGIN
		IF t IS SyntaxTree.MathArrayType THEN
			WHILE (t IS SyntaxTree.MathArrayType) & ((t(SyntaxTree.MathArrayType).form # SyntaxTree.Tensor) OR (max = Infinity)) & (max > 0) DO
				t := t(SyntaxTree.MathArrayType).arrayBase.resolved;
				IF (t IS SyntaxTree.PointerType) & (t(SyntaxTree.PointerType).pointerBase.resolved IS SyntaxTree.MathArrayType) THEN t := t(SyntaxTree.PointerType).pointerBase.resolved END;
				DEC(max);
			END;
		ELSIF t IS SyntaxTree.ArrayType THEN
			WHILE (t IS SyntaxTree.ArrayType) & (max > 0) DO
				t := t(SyntaxTree.ArrayType).arrayBase.resolved; DEC(max);
				IF (t IS SyntaxTree.PointerType) & (t(SyntaxTree.PointerType).pointerBase.resolved IS SyntaxTree.ArrayType) THEN t := t(SyntaxTree.PointerType).pointerBase.resolved END;
			END;
		END;
		RETURN t;
	END ArrayBase;

	PROCEDURE Dimension*(t: SyntaxTree.Type; form: SET): LONGINT;
	VAR i: LONGINT;
	BEGIN
		i := 0;
		t := t.resolved;
		IF t IS SyntaxTree.MathArrayType THEN
			WHILE(t IS SyntaxTree.MathArrayType) & (t(SyntaxTree.MathArrayType).form IN form)  DO
				t := t(SyntaxTree.MathArrayType).arrayBase.resolved; INC(i);
			END;
		ELSIF t IS SyntaxTree.ArrayType THEN
			WHILE(t IS SyntaxTree.ArrayType) & (t(SyntaxTree.ArrayType).form IN form) DO
				t := t(SyntaxTree.ArrayType).arrayBase.resolved; INC(i);
			END;
		END;
		RETURN i
	END Dimension;

	PROCEDURE IsVariable(expression: SyntaxTree.Expression): BOOLEAN;
	BEGIN
		RETURN expression.assignable;
	END IsVariable;

	PROCEDURE IsPointerType(type: SyntaxTree.Type): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		IF type = NIL THEN result := FALSE
		ELSE
		type := type.resolved; result :=  (type = Global.Any) OR (type IS SyntaxTree.PointerType) OR (type = Global.Nil) OR (type = Global.Object)
		END;
		RETURN result
	END IsPointerType;

	PROCEDURE IsPointerToRecord(type: SyntaxTree.Type): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		IF type = NIL THEN result := FALSE
		ELSE
			type := type.resolved;
			result := (type IS SyntaxTree.PointerType) & (type(SyntaxTree.PointerType).pointerBase.resolved IS SyntaxTree.RecordType);
			result := result OR	(type IS SyntaxTree.RecordType) & (type(SyntaxTree.RecordType).pointerType # NIL);
			result := result OR (type = Global.Object);
		END;
		RETURN result
	END IsPointerToRecord;


	PROCEDURE ContainsPointer*(type: SyntaxTree.Type): BOOLEAN;
	VAR scope: SyntaxTree.RecordScope; variable: SyntaxTree.Variable;
	BEGIN
		IF type # NIL THEN
			type := type.resolved;
			IF IsPointerType(type) THEN RETURN TRUE
			ELSIF type IS SyntaxTree.ArrayType THEN RETURN ContainsPointer(type(SyntaxTree.ArrayType).arrayBase)
			ELSIF type IS SyntaxTree.MathArrayType THEN RETURN ContainsPointer(type(SyntaxTree.MathArrayType).arrayBase)
			ELSIF type IS SyntaxTree.RecordType THEN
				scope := type(SyntaxTree.RecordType).recordScope;
				variable := scope.firstVariable;
				WHILE(variable # NIL) DO
					IF ContainsPointer(variable.type) THEN RETURN TRUE
					ELSE variable := variable.nextVariable
					END;
				END;
				RETURN ContainsPointer(type(SyntaxTree.RecordType).baseType)
			ELSIF (type IS SyntaxTree.ProcedureType) THEN
				RETURN SyntaxTree.DelegateFlag IN type(SyntaxTree.ProcedureType).flags
			END;
		END;
		RETURN FALSE
	END ContainsPointer;


	PROCEDURE IsStringType*(type: SyntaxTree.Type): BOOLEAN;
	BEGIN
		IF type = NIL THEN RETURN FALSE END;
		type := type.resolved;
		RETURN (type IS SyntaxTree.StringType) OR (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).arrayBase.resolved = Global.Char8);
	END IsStringType;

	PROCEDURE IsCharacterType*(type: SyntaxTree.Type):BOOLEAN;
	BEGIN
		IF type = NIL THEN RETURN FALSE END;
		type := type.resolved;
		RETURN (type IS SyntaxTree.CharacterType) OR (type IS SyntaxTree.StringType) & (type(SyntaxTree.StringType).length = 2)
	END IsCharacterType;


	(** cf. section "Type extension (base type)" in the language report **)
	PROCEDURE IsTypeExtension(base,extension: SyntaxTree.Type): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		ASSERT(base # NIL); ASSERT(extension # NIL);
		base := base.resolved; extension := extension.resolved;

		IF ((base = Global.Object) OR (base = Global.Any)) & IsPointerToRecord(extension) THEN
			result := TRUE;
		ELSE
			IF (base IS SyntaxTree.PointerType) & (extension IS SyntaxTree.PointerType) THEN
				base := base(SyntaxTree.PointerType).pointerBase.resolved;
				extension := extension(SyntaxTree.PointerType).pointerBase.resolved;
			END;

			WHILE (extension # NIL) & (extension # base) DO
				IF extension IS SyntaxTree.RecordType THEN
					extension := extension(SyntaxTree.RecordType).baseType;
					IF (extension # NIL) THEN extension := extension.resolved END;
					IF (extension # NIL) & (extension IS SyntaxTree.PointerType) THEN
						extension := extension(SyntaxTree.PointerType).pointerBase.resolved;
					END;
				ELSE extension := NIL;
				END;
			END;
			result :=  (extension = base) & (extension IS SyntaxTree.RecordType);
		END;
		RETURN result
	END IsTypeExtension;

	(** check if base is the base enumeration type of extension **)
	PROCEDURE IsEnumerationExtension(base,extension: SyntaxTree.Type): BOOLEAN;
	BEGIN
		base := base.resolved; extension := extension.resolved;

		WHILE (extension # NIL) & (extension # base) DO
			IF extension IS SyntaxTree.EnumerationType THEN
				extension := extension(SyntaxTree.EnumerationType).enumerationBase;
				IF extension # NIL THEN extension := extension.resolved END;
			ELSE
				extension := NIL
			END;
		END;
		RETURN (extension = base) & (base IS SyntaxTree.EnumerationType);
	END IsEnumerationExtension;

	PROCEDURE IsCallable(expression: SyntaxTree.Expression): BOOLEAN;
	BEGIN
		IF expression IS SyntaxTree.ProcedureCallDesignator THEN
			RETURN TRUE
		ELSIF expression IS SyntaxTree.BuiltinCallDesignator THEN
			RETURN TRUE
		ELSIF (expression.type # NIL) & (expression.type.resolved IS SyntaxTree.ProcedureType) THEN
			RETURN TRUE
		ELSE
			RETURN FALSE
		END
	END IsCallable;


	(** compute and return the distance of two record types
		returns the number of extension levels of from to to, returns infinite if to is not an extension of from
	**)
	PROCEDURE RecordTypeDistance(from, to: SyntaxTree.RecordType): LONGINT;
	VAR i: LONGINT; baseType: SyntaxTree.Type;
	BEGIN
		i := 0;
		WHILE (from # NIL) & (from # to) DO
			baseType :=  from.baseType;
			IF (baseType # NIL) THEN
				baseType := baseType.resolved;
				IF baseType IS SyntaxTree.PointerType THEN
					baseType := baseType(SyntaxTree.PointerType).pointerBase.resolved;
				END;
				IF baseType IS SyntaxTree.RecordType THEN
					from := baseType(SyntaxTree.RecordType);
				ELSE
					from := NIL;
				END;
			ELSE
				from := NIL
			END;
			INC(i)
		END;
		IF from = NIL THEN  i := Infinity  END;
		RETURN i
	END RecordTypeDistance;

	(** compute and return the distance of two pointer types **)
	PROCEDURE PointerTypeDistance(from, to: SyntaxTree.PointerType): LONGINT;
	BEGIN
		IF ~((to.pointerBase.resolved IS SyntaxTree.RecordType) & (from.pointerBase.resolved IS SyntaxTree.RecordType)) THEN
			RETURN Infinity;
		ELSE
			RETURN RecordTypeDistance(from.pointerBase.resolved(SyntaxTree.RecordType), to.pointerBase.resolved(SyntaxTree.RecordType));
		END;
	END PointerTypeDistance;

	(** check if expression contains a symbol designator pointing to a type declaration.
		- if so then enter type declaration into typeDeclaration and return true else return false
	**)
	PROCEDURE IsTypeDesignator(expression: SyntaxTree.Expression; VAR typeDeclaration: SyntaxTree.TypeDeclaration): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		result := FALSE;
		IF (expression # NIL) & (expression.type.resolved = SyntaxTree.typeDeclarationType) THEN
			result := TRUE;
			typeDeclaration := expression(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration)
		END;
		RETURN result
	END IsTypeDesignator;

	(** returns true if type is an extensible type (pointer to record, record, object or any), returns false otherwise **)
	PROCEDURE IsExtensibleType( type: SyntaxTree.Type): BOOLEAN;
	VAR result: BOOLEAN;
	BEGIN
		type := type.resolved;
		IF type IS SyntaxTree.PointerType THEN
			result := IsExtensibleType(type(SyntaxTree.PointerType).pointerBase.resolved);
		ELSIF (type = Global.Any) OR (type = Global.Object) THEN
			result := TRUE
		ELSE
			result := type IS SyntaxTree.RecordType
		END;
		RETURN result
	END IsExtensibleType;

	PROCEDURE IsUnextensibleRecord(d: SyntaxTree.Expression): BOOLEAN;
	BEGIN
		RETURN (d.type.resolved IS SyntaxTree.RecordType) &
			(d IS SyntaxTree.SymbolDesignator) &
			( (d(SyntaxTree.SymbolDesignator).symbol IS SyntaxTree.Variable)
			OR
			(d(SyntaxTree.SymbolDesignator).symbol IS SyntaxTree.Parameter) & (d(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.Parameter).kind = SyntaxTree.ValueParameter));

	END IsUnextensibleRecord;

	PROCEDURE IsExtensibleDesignator(d: SyntaxTree.Expression): BOOLEAN;
	BEGIN
		IF IsUnextensibleRecord(d) THEN
			RETURN FALSE
		ELSE RETURN IsExtensibleType(d.type.resolved)
		END;
	END IsExtensibleDesignator;

	PROCEDURE IsBasicType(type: SyntaxTree.Type): BOOLEAN;
	BEGIN
		type := type.resolved;
		IF (type IS SyntaxTree.PointerType) THEN
			RETURN TRUE
		ELSIF (type IS SyntaxTree.RecordType) & (type(SyntaxTree.RecordType).pointerType # NIL) (* object *) THEN
			RETURN TRUE
		ELSIF (type IS SyntaxTree.ProcedureType) THEN
			RETURN TRUE
		ELSIF (type IS SyntaxTree.BasicType) THEN
			RETURN TRUE
		END;
		RETURN FALSE
	END IsBasicType;
	
	PROCEDURE RecordBase(record: SyntaxTree.RecordType): SyntaxTree.RecordType;
	VAR baseType: SyntaxTree.Type; recordType: SyntaxTree.RecordType;
	BEGIN
		baseType := record.baseType;
		IF (baseType # NIL) THEN
			baseType := baseType.resolved;
			IF  (baseType IS SyntaxTree.PointerType) THEN
				baseType := baseType(SyntaxTree.PointerType).pointerBase.resolved;
			END;
		END;
		IF (baseType # NIL) & (baseType IS SyntaxTree.RecordType) THEN
			recordType := baseType(SyntaxTree.RecordType);
		ELSE
			recordType := NIL;
		END;
		RETURN recordType
	END RecordBase;

	PROCEDURE GetConstructor(record: SyntaxTree.RecordType): SyntaxTree.Procedure;
	VAR procedure: SyntaxTree.Procedure;
	BEGIN
		procedure := record.recordScope.constructor;
		IF procedure = NIL THEN
			record := RecordBase(record);
			IF record # NIL THEN
				procedure := GetConstructor(record)
			END;
		END;
		RETURN procedure;
	END GetConstructor;

	(* enter a case into a list of cases in a sorted way and check for collision *)
	PROCEDURE EnterCase(VAR root: SyntaxTree.CaseConstant; min,max: LONGINT): BOOLEAN;
	VAR prev,this,new: SyntaxTree.CaseConstant;
	BEGIN
		this := root;
		prev := NIL;
		WHILE (this # NIL) & (min > this.max) DO  prev := this; this := this.next  END;
		IF (this # NIL) & (max >= this.min) THEN	(* collision since min <=  this.max and max >= this.min *)
			RETURN FALSE
		ELSE
			IF (this # NIL) & (this.min = max+1) THEN
				this.min := min
			ELSIF (prev # NIL) & (min+1 = prev.max) THEN
				prev.max := min
			ELSE
				NEW(new);  new.min := min; new.max := max;
				new.next := this;
				IF prev = NIL THEN
					root := new;
				ELSE
					prev.next := new
				END
			END;
			RETURN TRUE
		END;
	END EnterCase;

	(** generate and return a new checker object, errors are entered into diagnostics **)
	PROCEDURE NewChecker*(diagnostics: Diagnostics.Diagnostics; verboseErrorMessage: BOOLEAN; system: Global.System; symbolFileFormat: Formats.SymbolFileFormat; VAR importCache: SyntaxTree.ModuleScope): Checker;
	VAR checker: Checker;
	BEGIN
		NEW(checker, diagnostics,verboseErrorMessage,system,symbolFileFormat,importCache);
		RETURN checker
	END NewChecker;

END OCSemanticChecker.

