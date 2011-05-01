MODULE FoxIntermediateBackend; (** AUTHOR ""; PURPOSE ""; *)

IMPORT Basic := FoxBasic, SyntaxTree := FoxSyntaxTree, SemanticChecker := FoxSemanticChecker, Backend := FoxBackend, Global := FoxGlobal,
	Scanner := FoxScanner, IntermediateCode := FoxIntermediateCode, Sections := FoxSections, Printout := FoxPrintout,
	SYSTEM, Diagnostics, Strings, Options, Streams, Compiler, Formats := FoxFormats, SymbolFileFormat := FoxTextualSymbolFile, D := Debugging,
	FingerPrinter := FoxFingerPrinter, BinaryCode := FoxBinaryCode, Files, StringPool;

CONST
		(* operand modes *)
		ModeUndefined = 0;
		ModeReference = 1;
		ModeValue = 2;

		(* heap data offsets *)
		MethodTable = -18;   (* method table offset *)
		BaseTypesTable = -2;	(*table with all record extensions*)
		ArrayDimTable = 3;	(* dimension table in dyn arrays *)

		(* math array offsets *)
		MathPtrOffset=0;
		MathAdrOffset=1;
		MathFlagsOffset=2;
		MathDimOffset=3;
		MathElementSizeOffset=4;
		MathLenOffset=5;
		MathIncrOffset=6;

		SysDataArrayOffset* = 8*8;   (* array offset in system block, for 32 byte alignment *)
		ArrDataArrayOffset*= 16*8; (* array offset in array block, to be compatible with the GC scheme of POINTER TO ARRAY OF ... *)

		TensorFlag* = 0;   (* flag indicating a tensor array *)
		RangeFlag* = 1;   (* flag indicating a range, e.g. an array derived from A[..,..] *)
		StackFlag* = 2;   (* flag indicates temporary result *)

		(** compiler generated traps *)
		WithTrap* = 1; (* generated when a WITH statement fails *)
		CaseTrap* = 2; (* generated when a case statement without else block fails *)
		ReturnTrap* = 3;
		TypeEqualTrap* = 5;
		TypeCheckTrap* = 6;
		IndexCheckTrap* = 7; (* generated when index is out of bounds or range is invalid *)
		AssertTrap* = 8; (* generated when an assert fails *)
		ArraySizeTrap* = 9;
		ArrayFormTrap*=10; (* indicates that array cannot be (re-)allocated since shape, type or size does not match *)
		SetElementTrap*=11; (* indicates that a set element is out of MIN(SET)...MAX(SET) *)
		NegativeDivisorTrap*=12;

		Trace = FALSE;
		TraceRegisterUsage=FALSE;

		ArrayAlignment = 8*8;			(* first array element of ArrayBlock and first data element of SystemBlock must be aligned to 0 MOD ArrayAlignment *)

		(** system call numbers  *)
		NumberSystemCalls* = 12;
		SysNewRec* = 0;  SysNewArr* = 1;  SysNewSys* = 2;  SysCaseTable* = 3;  SysProcAddr* = 4;
		SysLock* = 5;  SysUnlock* = 6;  SysStart* = 7;  SysAwait* = 8; SysInterfaceLookup* = 9;
		SysRegisterInterface* = 10; SysGetProcedure* = 11;

		DefaultRuntimeModuleName ="Runtime";
		DefaultTraceModuleName ="KernelLog";
		ChannelModuleName = "Channels";

		suppressModuleRegistration=FALSE;

		None=-1;

		(* nopov *)
		(* special pointer values *)
		NonPointer = -1;
		(* NilValue = 0; *)

		(* nopov *)
		(* special type info values *)
		NoType = 0;

		(* nopov *)
		(* for the operator kind *)
		LhsIsPointer = 0;
		RhsIsPointer = 1;

TYPE
	SupportedProcedure= PROCEDURE {DELEGATE} (CONST instr: IntermediateCode.Instruction; VAR moduleName,procedureName: ARRAY OF CHAR): BOOLEAN;

	Operand = RECORD
		mode: SHORTINT;
		op: IntermediateCode.Operand;
		tag: IntermediateCode.Operand;
		extra: IntermediateCode.Operand; (* stores the step size of an array range *)
		dimOffset: LONGINT;
	END;

	Fixup= POINTER TO RECORD
		pc: LONGINT;
		nextFixup: Fixup;
	END;

	WriteBackCall = POINTER TO RECORD
		call: SyntaxTree.ProcedureCallDesignator;
		next: WriteBackCall;
	END;

	Label= OBJECT
	VAR
		fixups: Fixup;
		section: IntermediateCode.Section;
		pc: LONGINT;

		PROCEDURE &InitLabel(section: IntermediateCode.Section);
		BEGIN
			SELF.section := section; pc := -1;
		END InitLabel;

		PROCEDURE Resolve(pc: LONGINT);
		VAR at: LONGINT;
		BEGIN
			SELF.pc := pc;
			WHILE(fixups # NIL) DO
				at := fixups.pc;
				section.PatchAddress(at,pc);
				fixups := fixups.nextFixup;
			END;
		END Resolve;

		PROCEDURE AddFixup(at: LONGINT);
		VAR fixup: Fixup;
		BEGIN
			ASSERT(pc=-1);
			NEW(fixup); fixup.pc := at; fixup.nextFixup := fixups; fixups := fixup;
		END AddFixup;

	END Label;


	ConditionalBranch = PROCEDURE {DELEGATE}(label: Label; op1,op2: IntermediateCode.Operand);

	DeclarationVisitor =OBJECT(SyntaxTree.Visitor)
	VAR
		backend: IntermediateBackend;
		implementationVisitor: ImplementationVisitor;
		system: Global.System;
		currentScope: SyntaxTree.Scope;
		module: Sections.Module;
		moduleSelf: SyntaxTree.Variable;
		dump: BOOLEAN;
		forceModuleBody: BOOLEAN;

		PROCEDURE & Init(system: Global.System; implementationVisitor: ImplementationVisitor; backend: IntermediateBackend; forceModuleBody, dump: BOOLEAN);
		BEGIN
			currentScope := NIL; module := NIL; moduleSelf := NIL;
			SELF.system := system; SELF.implementationVisitor := implementationVisitor;
			SELF.dump := dump;
			SELF.backend := backend;
			SELF.forceModuleBody := forceModuleBody;
		END Init;

		PROCEDURE Error(position: LONGINT; CONST s: ARRAY OF CHAR);
		BEGIN
			backend.Error(module.module.sourceName, position, Diagnostics.Invalid, s);
		END Error;

		PROCEDURE Type(x: SyntaxTree.Type);
		BEGIN
			x.Accept(SELF);
		END Type;

		(** types **)

		PROCEDURE VisitBasicType(x: SyntaxTree.BasicType);
		BEGIN (* no code emission *) END VisitBasicType;

		PROCEDURE VisitCharacterType(x: SyntaxTree.CharacterType);
		BEGIN (* no code emission *)  END VisitCharacterType;

		PROCEDURE VisitIntegerType(x: SyntaxTree.IntegerType);
		BEGIN (* no code emission *)  END VisitIntegerType;

		PROCEDURE VisitFloatType(x: SyntaxTree.FloatType);
		BEGIN (* no code emission *)  END VisitFloatType;

		PROCEDURE VisitQualifiedType(x: SyntaxTree.QualifiedType);
		VAR type: SyntaxTree.Type;
		BEGIN (* no further traversal to x.resolved necessary since type descriptor and code will be inserted at "original" position ? *)
			type := x.resolved;
			IF (type.typeDeclaration # NIL) & (type.typeDeclaration.scope.ownerModule # module.module) THEN
				CheckTypeDeclaration(implementationVisitor, module,type,dump,implementationVisitor.newObjectFile);
			END;
		END VisitQualifiedType;

		PROCEDURE VisitStringType(x: SyntaxTree.StringType);
		BEGIN (* no code emission *)   END VisitStringType;

		PROCEDURE VisitArrayRangeType(x: SyntaxTree.RangeType);
		BEGIN (* no code emission *)
		END VisitArrayRangeType;

		PROCEDURE VisitArrayType(x: SyntaxTree.ArrayType);
		BEGIN (* no code emission *)   END VisitArrayType;

		PROCEDURE VisitMathArrayType(x: SyntaxTree.MathArrayType);
		BEGIN
			CheckTypeDeclaration(implementationVisitor, module,x,dump,implementationVisitor.newObjectFile);
		END VisitMathArrayType;

		PROCEDURE VisitPointerType(x: SyntaxTree.PointerType);
		BEGIN
			CheckTypeDeclaration(implementationVisitor, module,x,dump,implementationVisitor.newObjectFile);
			(* base type must not be visited => will be done via record type declaration, otherwise is done twice ! *)
		END VisitPointerType;

		PROCEDURE VisitRecordType(x: SyntaxTree.RecordType);
		VAR name: ARRAY 256 OF CHAR; td: SyntaxTree.TypeDeclaration;
		BEGIN (* no code emission *)
			CheckTypeDeclaration(implementationVisitor, module,x,dump,implementationVisitor.newObjectFile);
			IF (x.recordScope.ownerModule = module.module) & (x.isObject) THEN
				IF x.pointerType.typeDeclaration # NIL THEN
					td := x.pointerType.typeDeclaration
				ELSE
					td := x.typeDeclaration
				END;
				Global.GetSymbolName(td,name);

				(* code section for object *)
			END;
			Scope(x.recordScope);
		END VisitRecordType;

		PROCEDURE VisitCellType(x: SyntaxTree.CellType);
		VAR name:Basic.PooledName; td: SyntaxTree.TypeDeclaration; type: SyntaxTree.Type; len,port,adr: LONGINT;
			parameter: SyntaxTree.Parameter; symbol: IntermediateCode.Section; op: IntermediateCode.Operand;
		BEGIN
			CheckTypeDeclaration(implementationVisitor, module,x,dump,implementationVisitor.newObjectFile);
			IF (x.cellScope.ownerModule = module.module)  THEN
				td := x.typeDeclaration;
				Global.GetSymbolPooledName(td,name);
				(* code section for object *)
			END;
			port := 0;
			parameter := x.firstParameter;
			WHILE parameter # NIL DO
				type := parameter.type.resolved;
				IF type IS SyntaxTree.PortType THEN
					len := 1;
					INC(port);
				ELSIF SemanticChecker.IsStaticArray(type,type,len) THEN
					Global.GetSymbolPooledName(parameter,name);
					symbol := implementationVisitor.NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,parameter,dump);
					WHILE len > 0 DO
						adr := backend.activeCellsSpecification.GetPortAddress(port);
						IntermediateCode.InitImmediate(op,IntermediateCode.GetType(system,system.addressType),adr);
						symbol.Emit(Data(op));
						DEC(len); INC(port);
					END;
				ELSE
					Error(parameter.position,"should never happen, check semantic checker!");
				END;
				parameter := parameter.nextParameter;
			END;

			Scope(x.cellScope);
		END VisitCellType;

		PROCEDURE VisitProcedureType(x: SyntaxTree.ProcedureType);
		BEGIN (* no code emission *)   END VisitProcedureType;

		PROCEDURE VisitEnumerationType(x: SyntaxTree.EnumerationType);
		BEGIN (* no code emission, exported enumeration type values should be included in symbol file *)
		END VisitEnumerationType;

		(* symbols *)

		PROCEDURE VisitProcedure(x: SyntaxTree.Procedure);
		BEGIN
			Procedure(x);
		END VisitProcedure;

		PROCEDURE VisitOperator(x: SyntaxTree.Operator);
		BEGIN
			Procedure(x);
		END VisitOperator;

		PROCEDURE VisitVariable(x: SyntaxTree.Variable);
		VAR name: Basic.PooledName; irv: IntermediateCode.Section;
		BEGIN
			IF (currentScope IS SyntaxTree.ModuleScope) OR (currentScope IS SyntaxTree.CellScope) THEN
				(* code section for variable *)
				Global.GetSymbolPooledName(x,name);
				irv := implementationVisitor.NewSection(module.allSections, Sections.RegularKind,Sections.VarSection, TRUE, name,x,dump);
				irv.SetPositionOrAlignment(x.fixed, x.alignment);
				irv.SetOffset(ToMemoryUnits(system,x.offsetInBits));
				irv.Emit(Reserve(ToMemoryUnits(system,system.SizeOf(x.type))));
				CheckTypeDeclaration(implementationVisitor, module,x.type,dump,implementationVisitor.newObjectFile);
			ELSIF currentScope IS SyntaxTree.RecordScope THEN
			ELSIF currentScope IS SyntaxTree.ProcedureScope THEN
			END;
			(* do not call Type(x.type) here as this must already performed in the type declaration section ! *)
		END VisitVariable;

		PROCEDURE VisitParameter(x: SyntaxTree.Parameter);
		VAR name: Basic.PooledName; irv: IntermediateCode.Section; op: Operand;
		BEGIN
			ASSERT(currentScope.outerScope IS SyntaxTree.CellScope);
			(* code section for variable *)
			Global.GetSymbolPooledName(x,name);
			irv := implementationVisitor.NewSection(module.allSections, Sections.RegularKind,Sections.VarSection, TRUE, name,x,dump);
			irv.SetPositionOrAlignment(x.fixed, x.alignment);
			(*
			irv.SetOffset(ToMemoryUnits(system,x.offsetInBits));
			*)
			IF x.defaultValue = NIL THEN
				irv.Emit(Reserve(ToMemoryUnits(system,system.SizeOf(x.type))))
			ELSE
				implementationVisitor.Evaluate(x.defaultValue, op);
				irv.Emit(Data(op.op));
			END;
			CheckTypeDeclaration(implementationVisitor, module,x.type,dump,implementationVisitor.newObjectFile);
		END VisitParameter;


		PROCEDURE VisitTypeDeclaration(x: SyntaxTree.TypeDeclaration);
		BEGIN
			Type(x.declaredType); (* => code in objects *)
			IF ~(x.declaredType IS SyntaxTree.QualifiedType) & (x.declaredType.resolved IS SyntaxTree.PointerType) THEN
				Type(x.declaredType.resolved(SyntaxTree.PointerType).pointerBase);
			END;
		END VisitTypeDeclaration;

		PROCEDURE VisitConstant(x: SyntaxTree.Constant);
		BEGIN
			IF (SyntaxTree.Public * x.access # {}) THEN
				implementationVisitor.VisitConstant(x);
			END;
		END VisitConstant;


		PROCEDURE Scope(x: SyntaxTree.Scope);
		VAR procedure: SyntaxTree.Procedure;
			constant: SyntaxTree.Constant;
			variable: SyntaxTree.Variable;
			prevScope: SyntaxTree.Scope;  typeDeclaration: SyntaxTree.TypeDeclaration;
		BEGIN
			IF x IS SyntaxTree.CellScope THEN implementationVisitor.currentCellScope := x(SyntaxTree.CellScope) END;
			prevScope := currentScope;
			currentScope := x;
			(* constants treated in implementation visitor  *)

			typeDeclaration := x.firstTypeDeclaration;
			WHILE typeDeclaration # NIL DO
				VisitTypeDeclaration(typeDeclaration);
				typeDeclaration := typeDeclaration.nextTypeDeclaration;
			END;

			variable := x.firstVariable;
			WHILE variable # NIL DO
				VisitVariable(variable);
				variable := variable.nextVariable;
			END;

			procedure := x.firstProcedure;
			WHILE procedure # NIL DO
				VisitProcedure(procedure);
				procedure := procedure.nextProcedure;
			END;

			constant := x.firstConstant;
			WHILE constant # NIL DO
				VisitConstant(constant);
				constant := constant.nextConstant;
			END;

			IF x IS SyntaxTree.CellScope THEN implementationVisitor.currentCellScope := NIL END;
			currentScope := prevScope;
		END Scope;

		PROCEDURE Parameters(first: SyntaxTree.Parameter);
		VAR parameter: SyntaxTree.Parameter;
		BEGIN
			parameter := first;
			WHILE parameter # NIL DO
				VisitParameter(parameter);
				parameter := parameter.nextParameter;
			END;
		END Parameters;


		PROCEDURE Procedure(x: SyntaxTree.Procedure);
		VAR scope: SyntaxTree.ProcedureScope;
			prevScope: SyntaxTree.Scope;
			inline: BOOLEAN;
			procedureType: SyntaxTree.ProcedureType;
			pc: LONGINT;
			stackSize: LONGINT;
			parSize: LONGINT;
			name: Basic.PooledName; ir: IntermediateCode.Section;
			null,size,fp: IntermediateCode.Operand;
			cc: LONGINT;
			actorType: SyntaxTree.CellType;

			PROCEDURE Signature;
			VAR parameter: SyntaxTree.Parameter; procedureType: SyntaxTree.ProcedureType; returnType : SyntaxTree.Type;
			BEGIN
				procedureType := x.type(SyntaxTree.ProcedureType);
				returnType := procedureType.returnType;
				IF returnType # NIL THEN CheckTypeDeclaration(implementationVisitor, module,returnType,dump,implementationVisitor.newObjectFile) END;
				parameter := procedureType.firstParameter;
				WHILE parameter # NIL DO
					CheckTypeDeclaration(implementationVisitor, module,parameter.type,dump,implementationVisitor.newObjectFile); (* we have to re-export a type, i.e. it has to be present in the list of symbols *)
					parameter := parameter.nextParameter;
				END;
			END Signature;

			PROCEDURE CheckIntegerValue(x: SyntaxTree.Expression; VAR value: LONGINT): BOOLEAN;
			VAR result: BOOLEAN;
			BEGIN
				result := FALSE;
				IF x = SyntaxTree.invalidExpression THEN
				ELSIF (x.resolved # NIL) & (x.resolved IS SyntaxTree.IntegerValue) THEN
					result := TRUE;
					value := x.resolved(SyntaxTree.IntegerValue).value;
				ELSE
					Error(x.position,"expression is not an integer constant");
				END;
				RETURN result;
			END CheckIntegerValue;

			PROCEDURE HasValue(modifiers: SyntaxTree.Modifier; CONST name: ARRAY OF CHAR; VAR value: LONGINT): BOOLEAN;
			VAR this: SyntaxTree.Modifier; id: SyntaxTree.Identifier;
			BEGIN
				this := modifiers; id := SyntaxTree.NewIdentifier(name);
				WHILE (this # NIL) & (this.identifier # id) DO
					this := this.nextModifier;
				END;
				IF this # NIL THEN
					IF this.expression = NIL THEN
						Error(this.position,"expected expression value");
					ELSIF CheckIntegerValue(this.expression,value) THEN
					END;
					RETURN TRUE
				ELSE RETURN FALSE
				END;
			END HasValue;

		BEGIN
			(*
			IF Trace & (dump # NIL) THEN dump.String("DeclarationVisitor:Procedure"); dump.Ln END;
			*)
			(* code section for this procedure *)
			scope := x.procedureScope;
			prevScope := currentScope;
			currentScope := scope;
			procedureType := x.type(SyntaxTree.ProcedureType);

			implementationVisitor.GetCodeSectionNameForSymbol(x, name);
			IF (scope.body # NIL) & (x.isInline) THEN
				inline := TRUE;
				ir := implementationVisitor.NewSection(module.allSections, Sections.RegularKind,Sections.InlineCodeSection, TRUE, name,x,dump);
			ELSIF (x.scope # NIL) & (x.scope IS SyntaxTree.CellScope) & (x.scope(SyntaxTree.CellScope).ownerCell.isCellNet)
				OR (x.scope # NIL) & (x.scope IS SyntaxTree.ModuleScope) & (x.scope(SyntaxTree.ModuleScope).ownerModule.isCellNet) THEN
					(* assembly *)
				RETURN
			ELSIF x = module.module.moduleScope.bodyProcedure THEN
				inline := FALSE;
				AddBodyCallStub(x,Sections.InitCodeSection,0);
				ir := implementationVisitor.NewSection(module.allSections, Sections.RegularKind,Sections.BodyCodeSection, TRUE, name,x,dump);
			ELSIF (scope.outerScope IS SyntaxTree.CellScope) & (x = scope.outerScope(SyntaxTree.CellScope).bodyProcedure) THEN
				inline := FALSE;
				actorType := scope.outerScope(SyntaxTree.CellScope).ownerCell;
				IF ~HasValue(actorType.modifiers,Global.StringDataMemorySize,stackSize) THEN stackSize := 1024 END;
				AddBodyCallStub(x,Sections.InitCode2Section,stackSize);
				ir := implementationVisitor.NewSection(module.allSections, Sections.RegularKind,Sections.BodyCodeSection, TRUE, name,x,dump);
			ELSIF (scope.outerScope IS SyntaxTree.CellScope) & (x.isConstructor) THEN
				inline := FALSE;
				Parameters(procedureType.firstParameter);
				ir := implementationVisitor.NewSection(module.allSections, Sections.RegularKind,Sections.CodeSection, TRUE, name,x,dump);
			ELSE
				inline := FALSE;
				ir := implementationVisitor.NewSection(module.allSections, Sections.RegularKind,Sections.CodeSection, TRUE, name,x,dump);
			END;

			cc := procedureType.callingConvention;

			IF scope.body # NIL THEN
				IF ~inline THEN
					pc := ir.pc;
					IF scope.lastVariable = NIL THEN
						stackSize := 0
					ELSE
						stackSize := scope.lastVariable.offsetInBits;
						IF stackSize <0 THEN stackSize := -stackSize END;
						Basic.Align(stackSize,system.AlignmentOf(system.parameterAlignment,system.byteType));  (* round up to parameter alignment *)
					END;
					(*
					ir.Emit(Nop()); (* placeholder for stack frame check *)
					ir.Emit(Nop()); (* placeholder for stack frame check (2) *)
					*)
					ir.Emit(Nop()); (* placeholder for enter *)
					(*
					ir.Emit(Nop()); (* placeholder for fill *)
					*)
					ir.EnterValidPAF;
				END;

				implementationVisitor.tagsAvailable := procedureType.callingConvention = SyntaxTree.OberonCallingConvention;

				implementationVisitor.Body(scope.body,currentScope,ir,x = module.module.moduleScope.bodyProcedure);

				IF ~inline & ~(procedureType.noPAF) THEN
					IF scope.lastVariable # NIL THEN
						stackSize := scope.lastVariable.offsetInBits;
						IF stackSize <0 THEN stackSize := -stackSize END;
						Basic.Align(stackSize,system.AlignmentOf(system.parameterAlignment,system.byteType));  (* round up to parameter alignment *)
					END;
				END;

				IF ~inline  & ~(procedureType.noPAF) THEN
					IF ToMemoryUnits(system,stackSize) > 4*1024-256 THEN (* stack frame potentially larger than page size *) (*! get page size from backend *)
						(*! unnecessary with new implementation of ENTER -- should potentially be called by backend
						IF implementationVisitor.GetRuntimeProcedure(implementationVisitor.runtimeModuleName,"EnsureAllocatedStack",procedure,TRUE) THEN
							size := IntermediateCode.Immediate(IntermediateCode.GetType(system,system.addressType),ToMemoryUnits(system,stackSize+256));
							ir.EmitAt(pc,Push(size));
							implementationVisitor.StaticCallOperand(result,procedure);
							ir.EmitAt(pc+1,Call(result.op,ProcedureParametersSize(system,procedure)));
						END;
						*)
					END;
					ir.EmitAt(pc(*+2*),Enter(cc,ToMemoryUnits(system,stackSize))); (*!!*)
					IF stackSize > 0 THEN
						IF (stackSize MOD system.addressSize = 0) THEN
							null := IntermediateCode.Immediate(IntermediateCode.GetType(system,system.addressType),0);
							fp := IntermediateCode.Register(IntermediateCode.GetType(system,system.addressType),IntermediateCode.FP);
							IntermediateCode.AddOffset(fp,ToMemoryUnits(system,-system.addressSize));
							size := IntermediateCode.Immediate(IntermediateCode.GetType(system,system.addressType),stackSize DIV system.addressSize);
						ELSE
							null := IntermediateCode.Immediate(int8,0);
							fp := IntermediateCode.Register(IntermediateCode.GetType(system,system.addressType),IntermediateCode.FP);
							IntermediateCode.AddOffset(fp,ToMemoryUnits(system,-null.type.sizeInBits));
							size := IntermediateCode.Immediate(IntermediateCode.GetType(system,system.addressType),stackSize DIV null.type.sizeInBits);
						END;
						(*! should potentially be called by backend -- enter might initialize
						ir.EmitAt(pc+3,Fill(fp,null,size,TRUE));
						*)
					END;

					ir.ExitValidPAF;

					parSize := ProcedureParametersSize(system,x);
					IF (procedureType.returnType = NIL) OR (scope.body.code # NIL)  THEN
						ir.Emit(Leave(cc));
						ir.Emit(Exit(parSize));
					ELSE
						ir.Emit(Trap(ReturnTrap));
					END
				END;
			ELSE (* force body for procedures *)
				ir.Emit(Enter(cc,0));
				parSize := ProcedureParametersSize(system,x);
				ir.EnterValidPAF;
				implementationVisitor.Body(scope.body,currentScope,ir,x = module.module.moduleScope.bodyProcedure);
				ir.ExitValidPAF;
				ir.Emit(Leave(cc));
				ir.Emit(Exit(parSize));
			END;
			Scope(scope);
			Signature;
			IF (x IS SyntaxTree.Operator) & x(SyntaxTree.Operator).isDynamic THEN implementationVisitor.RegisterDynamicOperator(x(SyntaxTree.Operator)) END; (* nopov *)

			currentScope := prevScope;
		END Procedure;

		PROCEDURE AddBodyCallStub(bodyProcedure: SyntaxTree.Procedure; sectionType: SHORTINT; initStack: LONGINT); (* code that is only necessary for static linkers *)
		VAR procedure: SyntaxTree.Procedure; procedureScope: SyntaxTree.ProcedureScope; name: Basic.PooledName;
			ir: IntermediateCode.Section; op: IntermediateCode.Operand;
		BEGIN
			ASSERT (bodyProcedure # NIL);
			procedureScope := SyntaxTree.NewProcedureScope(bodyProcedure.scope);
			procedure := SyntaxTree.NewProcedure(-1,SyntaxTree.NewIdentifier("@BodyStub"), procedureScope);
			procedure.SetScope(bodyProcedure.scope);
			procedure.SetType(SyntaxTree.NewProcedureType(-1,bodyProcedure.scope));
			procedure.SetAccess(SyntaxTree.Hidden);
			Global.GetSymbolPooledName (procedure,name);
			ir := implementationVisitor.NewSection(module.allSections, Sections.RegularKind,sectionType, TRUE, name,procedure,dump);

			IF initStack # 0 THEN
				IntermediateCode.InitImmediate(op,IntermediateCode.GetType(system,system.addressType),initStack);
				ir.Emit(Mov(implementationVisitor.sp,op));
			END;

			Global.GetSymbolPooledName (bodyProcedure,name);
			IntermediateCode.InitAddress(op, IntermediateCode.GetType(system,system.addressType), implementationVisitor.NewSection(module.allSections, Sections.RegularKind,Sections.BodyCodeSection, TRUE, name,bodyProcedure,dump) , 0);
			ir.Emit(Call(op, 0));
		END AddBodyCallStub;

		(** entry function to visit a complete module *)
		PROCEDURE Module(x: SyntaxTree.Module; module: Sections.Module);
		VAR
			ir: IntermediateCode.Section; op: IntermediateCode.Operand; name: Basic.PooledName; str: SyntaxTree.String;
			hasDynamicOperatorDeclarations: BOOLEAN; (* nopov *)
			operator: SyntaxTree.Operator;
			import: SyntaxTree.Import;

			PROCEDURE TypeNeedsInitialization(type: SyntaxTree.Type): BOOLEAN;
			BEGIN
				type := type.resolved;
				IF type IS SyntaxTree.RecordType THEN
					IF ScopeNeedsInitialization(type(SyntaxTree.RecordType).recordScope) THEN RETURN TRUE END;
				ELSIF (type IS SyntaxTree.ArrayType) THEN
					IF type(SyntaxTree.ArrayType).form = SyntaxTree.Static THEN
						IF TypeNeedsInitialization(type(SyntaxTree.ArrayType).arrayBase) THEN RETURN TRUE END;
					END;
				ELSIF type IS SyntaxTree.MathArrayType THEN
					WITH type: SyntaxTree.MathArrayType DO
						IF type.form = SyntaxTree.Open THEN
							RETURN TRUE
						ELSIF type.form = SyntaxTree.Static THEN
							IF TypeNeedsInitialization(type.arrayBase) THEN RETURN TRUE END;
						END;
					END;
				END;
				RETURN FALSE
			END TypeNeedsInitialization;

			PROCEDURE ScopeNeedsInitialization(scope: SyntaxTree.Scope): BOOLEAN;
			VAR variable: SyntaxTree.Variable;
			BEGIN
				variable := scope.firstVariable;
				WHILE variable # NIL DO
					IF TypeNeedsInitialization(variable.type) THEN RETURN TRUE END;
					variable := variable.nextVariable;
				END;
				RETURN FALSE
			END ScopeNeedsInitialization;


		BEGIN
			ASSERT(x # NIL); ASSERT(module # NIL);
			SELF.module := module;

			(* add import names to the generated Sections.Module *)
			import := x.moduleScope.firstImport;
			WHILE import # NIL DO
				import.GetName(str);
				module.imports.AddName(str);
				import := import.nextImport
			END;

			IF ~implementationVisitor.newObjectFile THEN
				Global.GetModulePooledName(module.module,name); Basic.SuffixPooledName(name, Basic.MakeString("@moduleSelf"));
				moduleSelf := SyntaxTree.NewVariable(0,SyntaxTree.NewIdentifier("@moduleSelf"));
				moduleSelf.SetType(system.anyType);
				moduleSelf.SetScope(x.moduleScope);
				moduleSelf.SetUntraced(TRUE);
				ir := implementationVisitor.NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,moduleSelf,dump);  ir.SetOffset(0);
				IntermediateCode.InitImmediate(op,IntermediateCode.GetType(system,system.addressType),0);
				ir.Emit(Data(op));
			END;

			implementationVisitor.module := module;
			implementationVisitor.moduleScope := x.moduleScope;
			implementationVisitor.moduleSelf := moduleSelf;

			IF forceModuleBody OR implementationVisitor.newObjectFile OR ScopeNeedsInitialization(x.moduleScope) THEN
				EnsureBodyProcedure(x.moduleScope); (* currently needed in Oberon, remove ? *)
			END;

			IF backend.profile THEN
				EnsureBodyProcedure(x.moduleScope);
				Global.GetModulePooledName(module.module,name); Basic.SuffixPooledName(name, Basic.MakeString("@ModuleId"));
				implementationVisitor.profileId := implementationVisitor.NewSection(module.allSections, Sections.RegularKind, Sections.VarSection, TRUE, name,NIL,dump);
				implementationVisitor.profileId.Emit(Reserve(ToMemoryUnits(system,system.SizeOf(system.longintType))));
				Global.GetModulePooledName(module.module,name); Basic.SuffixPooledName(name, Basic.MakeString("@InitProfiler"));
				implementationVisitor.profileInit := implementationVisitor.NewSection(module.allSections, Sections.RegularKind, Sections.CodeSection, TRUE, name,NIL,dump);
				implementationVisitor.profileInit.Emit(Enter(0,0));

				Global.GetModuleName(module.module,str);
				implementationVisitor.ProfilerAddModule(str);
				implementationVisitor.numberProcedures := 0;
			END;
			implementationVisitor.profile := backend.profile;

			(* check if there is at least one dynamic operator locally defined *)
			hasDynamicOperatorDeclarations := FALSE;
			operator := x.moduleScope.firstOperator;
			WHILE operator # NIL DO
				IF operator.isDynamic THEN hasDynamicOperatorDeclarations := TRUE END;
				operator := operator.nextOperator
			END;

			(* add operator initialization code section *)
			IF hasDynamicOperatorDeclarations THEN
				EnsureBodyProcedure(x.moduleScope);
				Global.GetModulePooledName(module.module,name); Basic.SuffixPooledName(name, Basic.MakeString("@OperatorInitialization"));
				implementationVisitor.operatorInitializationCodeSection := implementationVisitor.NewSection(module.allSections, Sections.RegularKind, Sections.CodeSection, TRUE, name, NIL, dump);
				implementationVisitor.operatorInitializationCodeSection.Emit(Enter(0,0));
			END;

			Scope(x.moduleScope);

			IF hasDynamicOperatorDeclarations THEN
				implementationVisitor.operatorInitializationCodeSection.Emit(Leave(0));
				implementationVisitor.operatorInitializationCodeSection.Emit(Exit(0));
			END;

			IF backend.profile THEN
				implementationVisitor.ProfilerPatchInit;
			END;

		END Module;

	END DeclarationVisitor;

	UsedArray*=POINTER TO ARRAY OF RECORD count: LONGINT; map: LONGINT; type: IntermediateCode.Type END;
	RegisterUsage*=OBJECT
	VAR used: UsedArray; count: LONGINT;

		PROCEDURE &Init;
		VAR i: LONGINT;
		BEGIN
			count := 0;
			IF used = NIL THEN NEW(used,64); END;
			FOR i := 0 TO LEN(used)-1 DO used[i].count := 0 END;
		END Init;

		PROCEDURE Grow;
		VAR new: UsedArray; size,i: LONGINT;
		BEGIN
			size := LEN(used)*2;
			NEW(new,size);
			FOR i := 0 TO LEN(used)-1 DO
				new[i].count := used[i].count;
				new[i].type := used[i].type;
				new[i].map := used[i].map
			END;
			FOR i := LEN(used) TO LEN(new)-1 DO new[i].count := 0 END;
			used := new
		END Grow;

		PROCEDURE Next(type: IntermediateCode.Type): LONGINT;
		BEGIN
			INC(count);
			IF count = LEN(used) THEN Grow END;
			used[count].type := type;
			used[count].map := count;
			RETURN count;
		END Next;

		PROCEDURE IncUse(register: LONGINT);
		BEGIN
			INC(used[register].count);
		END IncUse;

		PROCEDURE DecUse(register: LONGINT);
		BEGIN
			DEC(used[register].count);
		END DecUse;

		PROCEDURE Map(register: LONGINT): LONGINT;
		VAR map : LONGINT;
		BEGIN
			IF register > 0 THEN
				map := used[register].map;
				WHILE register # map DO register := map; map := used[register].map END;
			END;
			RETURN register
		END Map;

		PROCEDURE Remap(register: LONGINT; to: LONGINT);
		BEGIN
			used[register].map := to
		END Remap;


		PROCEDURE Use(register: LONGINT): LONGINT;
		BEGIN
			IF register < LEN(used) THEN
				RETURN used[register].count
			ELSE
				RETURN 0
			END
		END Use;

	END RegisterUsage;

	RegisterEntry = POINTER TO RECORD
		prev,next: RegisterEntry;
		register: LONGINT;
	END;

	ImplementationVisitor =OBJECT(SyntaxTree.Visitor)
	VAR
		system: Global.System;
		section: IntermediateCode.Section;
		module: Sections.Module;
		moduleScope : SyntaxTree.ModuleScope; (* shortcut for module.module.moduleScope *)
		awaitProcCounter, labelId, constId, caseId: LONGINT;

		hiddenPointerType: SyntaxTree.RecordType; (* used as hidden pointer, for example for ARRAY OF ANY *)
		delegatePointerType: SyntaxTree.RecordType; (* used for delegates, for example in ARRAY OF PROCEDURE{DELEGATE} *)

		checker: SemanticChecker.Checker;
		backend: IntermediateBackend;
		position: LONGINT;
		moduleSelf: SyntaxTree.Variable;

		(* variables for hand over of variables /  temporary state *)
		currentScope: SyntaxTree.Scope;
		constantDeclaration : SyntaxTree.Symbol;
		result: Operand; (* result of the most recent expression / statement *)
		destination: IntermediateCode.Operand;

		arrayDestinationTag: IntermediateCode.Operand;
		arrayDestinationDimension:LONGINT;

		currentLoop: Label; (* variable to hand over loop exit jump list *)
		conditional: BOOLEAN;
		trueLabel, falseLabel: Label;
		locked: BOOLEAN;
		(*
		usedRegisters: Registers;
		*)
		registerUsage: RegisterUsage;
		usedRegisters: RegisterEntry;

		(* useful operands and types *)
		nil,fp,sp,true,false: IntermediateCode.Operand;
		bool,addressType,setType, sizeType: IntermediateCode.Type;

		commentPrintout: Printout.Printer;
		dump: Streams.Writer;
		tagsAvailable : BOOLEAN;
		supported: SupportedProcedure;
		emitLabels: BOOLEAN;
		runtimeModuleName : SyntaxTree.String;
		newObjectFile: BOOLEAN;
		currentCellScope: SyntaxTree.CellScope;
		indexCounter: LONGINT;

		profile: BOOLEAN;
		profileId, profileInit: IntermediateCode.Section;
		profileInitPatchPosition: LONGINT;
		numberProcedures: LONGINT;
		procedureResultDesignator : SyntaxTree.Designator;
		(* nopov *)
		operatorInitializationCodeSection: IntermediateCode.Section;
		fingerPrinter: FingerPrinter.FingerPrinter;

		PROCEDURE & Init(system: Global.System; checker: SemanticChecker.Checker; supportedProcedure: SupportedProcedure; emitLabels: BOOLEAN; CONST runtime: SyntaxTree.String; backend: IntermediateBackend;
			newObjectFile: BOOLEAN);
		BEGIN
			SELF.system := system;
			SELF.runtimeModuleName := runtime;

			currentScope := NIL;
			hiddenPointerType := NIL;
			delegatePointerType := NIL;

			awaitProcCounter := 0;
			labelId := 0; constId := 0; labelId := 0;
			SELF.checker := checker;
			SELF.backend := backend;
			position := Diagnostics.Invalid;
			conditional := FALSE;
			locked := FALSE;
			InitOperand(result,ModeUndefined);
			addressType := IntermediateCode.GetType(system,system.addressType);
			setType := IntermediateCode.GetType(system,system.setType);
			sizeType := IntermediateCode.GetType(system, system.sizeType);
			fp := IntermediateCode.Register(addressType,IntermediateCode.FP);
			sp := IntermediateCode.Register(addressType,IntermediateCode.SP);
			nil := IntermediateCode.Immediate(addressType,0);

			IntermediateCode.InitOperand(destination);
			tagsAvailable := TRUE;
			supported := supportedProcedure;
			SELF.emitLabels := emitLabels;
			IntermediateCode.InitOperand(arrayDestinationTag);

			bool := IntermediateCode.GetType(system,system.booleanType);
			IntermediateCode.InitImmediate(false,bool,0);
			IntermediateCode.InitImmediate(true,bool,1);

			SELF.newObjectFile := newObjectFile;
			currentCellScope := NIL;
			indexCounter := 0;
			NEW(registerUsage);
			usedRegisters := NIL;
			procedureResultDesignator := NIL;
			NEW(fingerPrinter, system) (* nopov *)
		END Init;

		PROCEDURE NewSection(list: Sections.SectionList; kind, type: SHORTINT; isDefinition: BOOLEAN; CONST name: Basic.PooledName; x: SyntaxTree.Symbol; dump: BOOLEAN): IntermediateCode.Section;
		VAR fp: SyntaxTree.FingerPrint;
		BEGIN
			(*IF (x # NIL) & ~((x IS SyntaxTree.Procedure) & (x(SyntaxTree.Procedure).isInline)) THEN fp := fingerPrinter.SymbolFP(x) END;*)
			RETURN IntermediateCode.NewSection(list, kind, type, isDefinition, name, x, dump)
		END NewSection;

		PROCEDURE AcquireRegister(CONST type: IntermediateCode.Type): LONGINT;
		VAR new: LONGINT;
		BEGIN
			new :=  registerUsage.Next(type);
			UseRegister(new);
			RETURN new
		END AcquireRegister;

		PROCEDURE GetIndex(): LONGINT;
		BEGIN
			INC(indexCounter); RETURN indexCounter
		END GetIndex;

		(* nopov *)
		(** get the name for the code section that represens a certain symbol
		(essentially the same as Global.GetSymbolName, apart from operators) **)
		PROCEDURE GetCodeSectionNameForSymbol(symbol: SyntaxTree.Symbol; VAR name: Basic.PooledName);
		VAR
			operatorFingerPrint: SyntaxTree.FingerPrint;
			operatorFingerPrintString,string: ARRAY 32 OF CHAR;
		BEGIN
			Global.GetSymbolPooledName(symbol, name);
			(* if the symbol is an operator, then append the fingerprint to the name *)
			IF symbol IS SyntaxTree.Operator THEN
				operatorFingerPrint := fingerPrinter.SymbolFP(symbol);
				string := "[";
				Strings.IntToHexStr(operatorFingerPrint.shallow, 8, operatorFingerPrintString);
				Strings.Append(string, operatorFingerPrintString);
				Strings.Append(string, "]");
				Basic.AppendToPooledName(name,string);
			END
		END GetCodeSectionNameForSymbol;

		PROCEDURE TraceEnter(CONST s: ARRAY OF CHAR);
		BEGIN
			IF dump # NIL THEN
				dump.String("enter "); dump.String(s); dump.Ln;
			END;
		END TraceEnter;

		PROCEDURE TraceExit(CONST s: ARRAY OF CHAR);
		BEGIN
			IF dump # NIL THEN
				dump.String("exit "); dump.String(s); dump.Ln;
			END;
		END TraceExit;


		PROCEDURE Emit(instruction: IntermediateCode.Instruction);
		VAR moduleName, procedureName: SyntaxTree.String;

			PROCEDURE CheckRegister(VAR op: IntermediateCode.Operand);
			BEGIN
				IF op.register >0 THEN IntermediateCode.SetRegister(op,registerUsage.Map(op.register)) END;
			END CheckRegister;

		BEGIN
			CheckRegister(instruction.op1);
			CheckRegister(instruction.op2);
			CheckRegister(instruction.op3);
			IF supported(instruction,moduleName,procedureName) THEN section.Emit(instruction)
			ELSE Emulate(instruction,moduleName,procedureName);
			END;
		END Emit;

		PROCEDURE Symbol(x: SyntaxTree.Symbol; VAR op: Operand);
		BEGIN
			position := x.position;
			x.Accept(SELF);
			op := result;
		END Symbol;

		PROCEDURE Expression(x: SyntaxTree.Expression);
		BEGIN
			position := x.position;
			constantDeclaration := NIL;
			IF (x IS SyntaxTree.SymbolDesignator) & (x(SyntaxTree.SymbolDesignator).symbol IS SyntaxTree.Constant) THEN
				constantDeclaration := x(SyntaxTree.SymbolDesignator).symbol;
			END;
			IF x.resolved # NIL THEN
				x.resolved.Accept(SELF)
			ELSE
				x.Accept(SELF)
			END;
		END Expression;

		PROCEDURE Statement(x: SyntaxTree.Statement);
		BEGIN
			position := x.position;
			IF emitLabels THEN Emit(LabelInstruction(x.position)) END;
			IF commentPrintout # NIL THEN
				commentPrintout.Statement(x);
				dump.Ln;
				(*dump.Update;*)
			END;
			x.Accept(SELF);
			CheckRegistersFree();
		END Statement;

		(* dereference op. If op is already a memory operand then use auxiliary register to dereference
			result will be registered as a new use of operand, op is not released (op must be released by caller)
		*)
		PROCEDURE MakeMemory(VAR res: IntermediateCode.Operand; op: IntermediateCode.Operand; type: IntermediateCode.Type; offset: LONGINT);
		BEGIN

			IF op.mode = IntermediateCode.ModeMemory THEN
				ReuseCopy(res,op);
			ELSE
				res := op;
				UseIntermediateOperand(res);
			END;
			IntermediateCode.AddOffset(res,offset);

			IntermediateCode.MakeMemory(res,type);
		END MakeMemory;

		PROCEDURE ToMemory(VAR res: IntermediateCode.Operand; type: IntermediateCode.Type; offset: LONGINT);
		VAR mem: IntermediateCode.Operand;
		BEGIN
			MakeMemory(mem,res,type,offset);
			ReleaseIntermediateOperand(res);
			res := mem;
		END ToMemory;

		PROCEDURE LoadValue(VAR operand: Operand; type: SyntaxTree.Type);
		VAR mem: IntermediateCode.Operand;
			firstOp, lastOp, stepOp: IntermediateCode.Operand;
		BEGIN
			type := type.resolved;
			IF operand.mode = ModeReference THEN
				IF type IS SyntaxTree.RangeType THEN
					MakeMemory(firstOp, operand.op, IntermediateCode.GetType(system, system.longintType), 0);
					MakeMemory(lastOp, operand.op, IntermediateCode.GetType(system, system.longintType), ToMemoryUnits(system, system.SizeOf(system.longintType)));
					MakeMemory(stepOp, operand.op, IntermediateCode.GetType(system, system.longintType), 2 * ToMemoryUnits(system, system.SizeOf(system.longintType)));
					ReleaseIntermediateOperand(operand.op);
					operand.op := firstOp;
					operand.tag := lastOp;
					operand.extra := stepOp;
				ELSE
					MakeMemory(mem,operand.op,IntermediateCode.GetType(system,type),0);
					ReleaseIntermediateOperand(operand.op);
					operand.op := mem;
				END;
				operand.mode := ModeValue;
			END;
			ASSERT(operand.mode = ModeValue);
		END LoadValue;

		PROCEDURE Evaluate(x: SyntaxTree.Expression; VAR op: Operand);
		VAR prevConditional: BOOLEAN;
		BEGIN
			prevConditional := conditional;
			conditional := FALSE;
			Expression(x);
			op := result;
			LoadValue(op,x.type.resolved);
			conditional := prevConditional;
		END Evaluate;

		PROCEDURE Designate(x: SyntaxTree.Expression; VAR op: Operand);
		VAR prevConditional: BOOLEAN;
		BEGIN
			prevConditional := conditional;
			conditional := FALSE;
			Expression(x);
			op := result;
		(*
			ASSERT((op.mode = ModeReference) OR (x.type.resolved IS SyntaxTree.NilType)); (* special case: winapi NIL parameter on references *)
		*)
			conditional := prevConditional;
		END Designate;

		PROCEDURE Condition(x: SyntaxTree.Expression; trueL,falseL: Label);
		VAR prevTrue, prevFalse: Label; prevConditional: BOOLEAN;
		BEGIN
			ASSERT(trueL # NIL); ASSERT(falseL # NIL);
			prevTrue := trueLabel; prevFalse := falseLabel; prevConditional := conditional;
			conditional := TRUE;
			trueLabel := trueL; falseLabel := falseL;
			Expression(x);
			trueL := trueLabel; falseL := falseLabel;
			trueLabel := prevTrue;falseLabel := prevFalse;conditional := prevConditional;
		END Condition;

		PROCEDURE NewRegisterOperand(type: IntermediateCode.Type): IntermediateCode.Operand;
		VAR op: IntermediateCode.Operand; reg: LONGINT;
		BEGIN
			reg := AcquireRegister(type);
			IntermediateCode.InitRegister(op, type, reg);
			RETURN op
		END NewRegisterOperand;

		PROCEDURE UnuseRegister(register: LONGINT);
		BEGIN
			IF (register > 0) THEN
				registerUsage.DecUse(register);
				IF TraceRegisterUsage & (dump# NIL) THEN
					dump.String("unuse register "); dump.Int(register,1); dump.String(": ");dump.Int(registerUsage.Use(register),1); dump.Ln;
				END;
				IF registerUsage.Use(register)=0 THEN RemoveRegisterEntry(usedRegisters,register) END;
			END;
		END UnuseRegister;

		PROCEDURE UseRegister(register: LONGINT);
		BEGIN
			IF (register > 0) THEN
				registerUsage.IncUse(register);
				IF TraceRegisterUsage & (dump# NIL) THEN
					dump.String("use register "); dump.Int(register,1); dump.String(": ");dump.Int(registerUsage.Use(register),1); dump.Ln;
				END;
				IF registerUsage.Use(register)=1 THEN AddRegisterEntry(usedRegisters,register) END;
			END;
		END UseRegister;

		PROCEDURE ReleaseIntermediateOperand(CONST op: IntermediateCode.Operand);
		BEGIN
			UnuseRegister(op.register)
		END ReleaseIntermediateOperand;

		PROCEDURE UseIntermediateOperand(CONST op: IntermediateCode.Operand);
		BEGIN
			UseRegister(op.register)
		END UseIntermediateOperand;

		PROCEDURE ReleaseOperand(CONST op: Operand);
		BEGIN
			UnuseRegister(op.op.register);
			UnuseRegister(op.tag.register);
			UnuseRegister(op.extra.register);
		END ReleaseOperand;

		(* save registers marked in array "markedRegisters" to the stack
			remove entries from array "markedRegisters" and save to array "saved" (=> recursion possible)
		*)
		PROCEDURE SaveRegisters();
		VAR op: IntermediateCode.Operand; entry: RegisterEntry; type: IntermediateCode.Type;
		BEGIN
			entry := usedRegisters;
			WHILE entry # NIL DO
				type := registerUsage.used[entry.register].type;
				IntermediateCode.InitRegister(op,type,entry.register);
				Emit(Push(op));
				entry := entry.next;
			END;
		END SaveRegisters;

		PROCEDURE ReleaseUsedRegisters(VAR saved: RegisterEntry);
		BEGIN
			saved := usedRegisters;
			usedRegisters := NIL;
		END ReleaseUsedRegisters;

		(* restore registers from array saved and re-enter into array markedRegisters (recursion possible) *)
		PROCEDURE RestoreRegisters(CONST saved: RegisterEntry);
		VAR op: IntermediateCode.Operand; entry,prev: RegisterEntry; type: IntermediateCode.Type;
		BEGIN
			entry := saved;
			WHILE (entry # NIL) DO prev := entry; entry := entry.next END;
			entry := prev;
			WHILE entry # NIL DO
				prev := entry.prev;
				type := registerUsage.used[entry.register].type;
				IntermediateCode.InitRegister(op,type,entry.register);
				registerUsage.Remap(entry.register,registerUsage.Next(type));
				Emit(Pop(op));
				AddRegisterEntry(usedRegisters,entry.register);
				entry := prev;
			END;
			(*
			usedRegisters := saved;
			*)
		END RestoreRegisters;

		PROCEDURE CheckRegistersFree;
		VAR r: RegisterEntry;
		BEGIN
			IF usedRegisters # NIL THEN
				r := usedRegisters;
				WHILE r # NIL DO
					Error(r.register,"not released register");
					r := r .next;
				END;
				Error(position,"register not released");
			END;
		END CheckRegistersFree;


		(* Reuse2: reuse src1 or src2 for ongoing computation if src1 or src2, respectively, is a register.
			Otherwise allocate a new register.
			Does NOT necessarily keep the content of src1 or src2 in result! *)
		PROCEDURE Reuse2(VAR result: IntermediateCode.Operand; src1,src2: IntermediateCode.Operand);
		BEGIN
			IF ReusableRegister(src1) THEN IntermediateCode.InitRegister(result,src1.type,src1.register);
				UseIntermediateOperand(result);
			ELSIF ReusableRegister(src2) THEN IntermediateCode.InitRegister(result,src2.type,src2.register);
				UseIntermediateOperand(result);
			ELSE IntermediateCode.InitRegister(result,src1.type,AcquireRegister(src1.type));
			END;
		END Reuse2;

		(* Reuse2a: reuse src1 or src2 for ongoing computation if src1 or src2, respectively, is a register.
			Otherwise check if an alternative destination is available. If so, then take the alternative (which is not necessarily a register).
			If not then allocate a new register.
			Does NOT necessarily keep the content of src1 or src2 in result!
		*)
		PROCEDURE Reuse2a(VAR result: IntermediateCode.Operand; src1,src2: IntermediateCode.Operand; VAR alternative: IntermediateCode.Operand);
		BEGIN
			IF ReusableRegister(src1) THEN IntermediateCode.InitRegister(result,src1.type,src1.register);
				UseIntermediateOperand(result);
			ELSIF ReusableRegister(src2) THEN IntermediateCode.InitRegister(result,src2.type,src2.register);
				UseIntermediateOperand(result);
			ELSIF alternative.mode # IntermediateCode.Undefined THEN
				result := alternative; alternative := emptyOperand;
				UseIntermediateOperand(result);
			ELSE IntermediateCode.InitRegister(result,src1.type,AcquireRegister(src1.type));
			END;
		END Reuse2a;

		(* like reuse2 but only one source *)
		PROCEDURE Reuse1(VAR result: IntermediateCode.Operand; src1: IntermediateCode.Operand);
		BEGIN
			IF ReusableRegister(src1) THEN IntermediateCode.InitRegister(result,src1.type,src1.register);
				UseIntermediateOperand(result);
			ELSE IntermediateCode.InitRegister(result,src1.type,AcquireRegister(src1.type));
			END;
		END Reuse1;

		(* like reuse2a but only one source *)
		PROCEDURE Reuse1a(VAR result: IntermediateCode.Operand; src1: IntermediateCode.Operand; VAR alternative: IntermediateCode.Operand);
		BEGIN
			IF ReusableRegister(src1) THEN IntermediateCode.InitRegister(result,src1.type,src1.register);
				UseIntermediateOperand(result);
			ELSIF alternative.mode # IntermediateCode.Undefined THEN result := alternative; alternative := emptyOperand;
				UseIntermediateOperand(result);
			ELSE IntermediateCode.InitRegister(result,src1.type,AcquireRegister(src1.type));
			END;
		END Reuse1a;

		(* like reuse1 but guarantees that content of src1 is in result *)
		PROCEDURE ReuseCopy(VAR result: IntermediateCode.Operand; src1: IntermediateCode.Operand);
		BEGIN
			IF ReusableRegister(src1) THEN
				IntermediateCode.InitRegister(result,src1.type,src1.register);
				IF (src1.mode # IntermediateCode.ModeRegister) OR (src1.offset # 0) THEN
					Emit(Mov(result,src1));
				END;
				UseIntermediateOperand(result);
			ELSE
				IntermediateCode.InitRegister(result,src1.type,AcquireRegister(src1.type));
				Emit(Mov(result,src1));
			END
		END ReuseCopy;

		(** labels and branches **)
		PROCEDURE NewLabel(): Label;
		VAR label: Label;
		BEGIN
			NEW(label,section); RETURN label;
		END NewLabel;

		PROCEDURE SetLabel(label: Label);
		BEGIN label.Resolve(section.pc);
		END SetLabel;

		PROCEDURE LabelOperand(label: Label): IntermediateCode.Operand;
		BEGIN
			ASSERT(label # NIL);
			IF label.pc < 0 THEN (* label not yet set *)
				label.AddFixup(section.pc);
			END;
			RETURN IntermediateCode.Address(addressType,label.section,label.pc);
		END LabelOperand;

		PROCEDURE BrL(label: Label);
		BEGIN
			Emit(Br(LabelOperand(label)));
		END BrL;

		PROCEDURE BrgeL(label: Label; left,right: IntermediateCode.Operand);
		BEGIN
			Emit(Brge(LabelOperand(label),left,right));
		END BrgeL;

		PROCEDURE BrltL(label: Label; left,right: IntermediateCode.Operand);
		BEGIN
			Emit(Brlt(LabelOperand(label),left,right));
		END BrltL;

		PROCEDURE BreqL(label: Label; left,right: IntermediateCode.Operand);
		BEGIN
			Emit(Breq(LabelOperand(label),left,right));
		END BreqL;

		PROCEDURE BrneL(label: Label; left,right: IntermediateCode.Operand);
		BEGIN
			Emit(Brne(LabelOperand(label),left,right));
		END BrneL;

		PROCEDURE Convert(VAR operand: IntermediateCode.Operand; type: IntermediateCode.Type);
		VAR new: IntermediateCode.Operand;
		BEGIN
			IF IntermediateCode.TypeEquals(type,operand.type) THEN (* nothing to be done *)
			ELSIF (operand.mode = IntermediateCode.ModeRegister) THEN
				IF (type.sizeInBits = operand.type.sizeInBits) & (type.form IN IntermediateCode.Integer) & (operand.type.form IN IntermediateCode.Integer)
					& (operand.offset = 0)
				THEN
					IntermediateCode.InitRegister(new,type,operand.register);
					Emit(Conv(new,operand));
				ELSE
					IntermediateCode.InitRegister(new,type,AcquireRegister(type));
					Emit(Conv(new,operand));
					ReleaseIntermediateOperand(operand);
				END;
				operand := new;
			ELSIF (operand.mode = IntermediateCode.ModeImmediate) & (operand.symbol = NIL) & (operand.type.sizeInBits <= type.sizeInBits) & (operand.type.form IN IntermediateCode.Integer) & (type.form IN IntermediateCode.Integer) THEN
				IntermediateCode.InitImmediate(operand,type,operand.intValue);
			ELSE
				IntermediateCode.InitRegister(new,type,AcquireRegister(type));
				Emit(Conv(new,operand));
				ReleaseIntermediateOperand(operand);
				operand := new;
			END;
		END Convert;

		PROCEDURE TrapC(br: ConditionalBranch; left,right:IntermediateCode.Operand; trapNo: LONGINT);
		VAR exit: Label;
		BEGIN
			Assert((left.mode # IntermediateCode.ModeImmediate) OR (right.mode # IntermediateCode.ModeImmediate),"trap emission with two immediates");
			exit := NewLabel();
			br(exit,left,right);
			Emit(Trap(trapNo));
			SetLabel(exit);
		END TrapC;

		(** expressions *)

		(** emit necessary runtime check for set elements **)
		PROCEDURE CheckSetElement(o: IntermediateCode.Operand);
		VAR max: IntermediateCode.Operand;
		BEGIN
			IF backend.noRuntimeChecks THEN RETURN END;
			IF o.mode # IntermediateCode.ModeImmediate THEN (* otherwise it's the job of the checker *)
				IntermediateCode.InitImmediate(max, setType, setType.sizeInBits (* number of bits in set *) -1);
				TrapC(BrgeL, max, o, SetElementTrap);
			END;
		END CheckSetElement;

		(** the set that a range represents **)
		PROCEDURE SetFromRange(x: SyntaxTree.RangeExpression): IntermediateCode.Operand;
		VAR
			operand: Operand;
			resultingSet, temp, size, allBits, noBits, one: IntermediateCode.Operand;
		BEGIN
			ASSERT((x.first # NIL) & (x.last # NIL)); (* ensured by the checker *)

			allBits := IntermediateCode.Immediate(setType, -1);  (* bit mask 111...11111 *)
			noBits := IntermediateCode.Immediate(setType, 0);  (* bit mask 0...0 *)
			one := IntermediateCode.Immediate(setType, 1);

			Evaluate(x, operand);

			Convert(operand.op, setType);
			Convert(operand.tag, setType);

			CheckSetElement(operand.op);
			CheckSetElement(operand.tag);

			(* create mask for lower bound
				i.e. shift 11111111 to the left by the value of the lower bound
			*)
			Reuse1(temp, operand.op);
			Emit(Shl(temp, allBits, operand.op));
			ReleaseIntermediateOperand(operand.op);
			operand.op := temp;

			(* create mask for upper bound
				i.e. shift 11111111 to the right by the difference between the
				upper bound and the maximum number of set elements
			*)
			IF (operand.tag.mode = IntermediateCode.ModeImmediate) & (operand.tag.symbol = NIL) THEN
				IntermediateCode.InitImmediate(operand.tag, operand.tag.type, operand.op.type.sizeInBits - 1- operand.tag.intValue);
				Reuse1(temp, operand.tag);
			ELSE
				Reuse1(temp, operand.tag);
				IntermediateCode.InitImmediate(size, operand.tag.type, operand.op.type.sizeInBits - 1);
				Emit(Sub(temp, size, operand.tag));
			END;
			Emit(Shr(temp, allBits, operand.tag));
			ReleaseIntermediateOperand(operand.tag);
			operand.tag := temp;

			Reuse2(resultingSet, operand.op, operand.tag);

			(* intersect the two masks *)
			Emit(And(resultingSet, operand.op, operand.tag));

			ReleaseOperand(operand);

			RETURN resultingSet
		END SetFromRange;

		PROCEDURE VisitSet(x: SyntaxTree.Set);
		VAR
			res, operand: Operand;
			temp, one, noBits, dest: IntermediateCode.Operand;
			expression: SyntaxTree.Expression;
			i: LONGINT;

		BEGIN
			IF Trace THEN TraceEnter("VisitSet") END;

			dest := destination;
			destination := emptyOperand;

			noBits := IntermediateCode.Immediate(setType, 0);
			one := IntermediateCode.Immediate(setType, 1);

			(* start off with the empty set *)
			InitOperand(res, ModeValue);
			IntermediateCode.InitRegister(res.op, setType, AcquireRegister(setType));
			Emit(Mov(res.op, noBits));

			FOR i := 0 TO x.elements.Length() - 1 DO
				expression := x.elements.GetExpression(i);

				IF expression IS SyntaxTree.RangeExpression THEN
					(* range of set elements *)
					temp := SetFromRange(expression(SyntaxTree.RangeExpression));
					ASSERT(IntermediateCode.TypeEquals(setType, temp.type));
					Emit(Or(res.op, res.op, temp)); (* unify subset with current set *)
					ReleaseIntermediateOperand(temp)
				ELSE
					(* singelton element *)
					Evaluate(expression, operand);
					Convert(operand.op, setType);
					CheckSetElement(operand.op);

					(* create subset containing single element *)
					Reuse1(temp, operand.op);
					Emit(Shl(temp, one, operand.op));
					ReleaseOperand(operand);

					Emit(Or(res.op, res.op, temp)); (* unify subset with current set *)
					ReleaseIntermediateOperand(temp);
				END
			END;

			result := res;
			destination := dest;

			IF Trace THEN TraceExit("VisitSet") END;
		END VisitSet;

		PROCEDURE VisitMathArrayExpression(x: SyntaxTree.MathArrayExpression);
		VAR variable: SyntaxTree.Variable; index: SyntaxTree.IndexDesignator; dim: LONGINT;
			designator: SyntaxTree.Designator; i: LONGINT; element: SyntaxTree.IntegerValue;

			PROCEDURE RecursiveAssignment(x: SyntaxTree.MathArrayExpression; dim: LONGINT);
			VAR numberElements,i: LONGINT; expression: SyntaxTree.Expression;
				element: SyntaxTree.IntegerValue;
			BEGIN
				numberElements := x.elements.Length();
				expression := index.parameters.GetExpression(dim);
				element := expression(SyntaxTree.IntegerValue);
				FOR i := 0 TO numberElements-1 DO
					expression := x.elements.GetExpression(i);
					element.SetValue(i);
					IF expression IS SyntaxTree.MathArrayExpression THEN
						RecursiveAssignment(expression(SyntaxTree.MathArrayExpression),dim+1);
					ELSE
						Assign(index,expression);
					END;
				END;
			END RecursiveAssignment;

		BEGIN
			variable := GetTemporaryVariable(x.type);
			designator := SyntaxTree.NewSymbolDesignator(-1,NIL,variable);
			designator.SetType(variable.type);
			dim := SemanticChecker.Dimension(x.type,{SyntaxTree.Static});
			index := SyntaxTree.NewIndexDesignator(x.position,designator);
			FOR i := 0 TO dim-1 DO
				element := SyntaxTree.NewIntegerValue(x.position,0);
				element.SetType(system.longintType);
				index.parameters.AddExpression(element);
			END;
			index.SetType(SemanticChecker.ArrayBase(x.type,dim));
			RecursiveAssignment(x,0);
			Expression(designator);
		END VisitMathArrayExpression;


		PROCEDURE VisitUnaryExpression(x: SyntaxTree.UnaryExpression);
		VAR type: SyntaxTree.Type; operand: Operand; dest: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitUnaryExpression") END;
			dest := destination; destination := emptyOperand;
			IF x.operator = Scanner.Not THEN
				IF conditional THEN
					Condition(x.left,falseLabel,trueLabel)
				ELSE
					Evaluate(x.left,operand);
					InitOperand(result,ModeValue);
					Reuse1a(result.op,operand.op,dest);
					Emit(Xor(result.op,operand.op,true));
					ReleaseOperand(operand);
				END;
			ELSIF x.operator = Scanner.Minus THEN
				Evaluate(x.left,operand);
				InitOperand(result,ModeValue);
				Reuse1a(result.op,operand.op,dest);
				type := x.left.type.resolved;
				IF type IS SyntaxTree.SetType THEN
					Emit(Not(result.op,operand.op));
				ELSIF (type IS SyntaxTree.NumberType) OR (type IS SyntaxTree.SizeType) OR (type IS SyntaxTree.AddressType) THEN
					Emit(Neg(result.op,operand.op));
				ELSE HALT(200)
				END;
				ReleaseOperand(operand);
			ELSE HALT(100)
			END;
			destination := dest;
			IF Trace THEN TraceExit("VisitUnaryExpression") END;
		END VisitUnaryExpression;

		(* test if e is of type type, side effect: result of evaluation of e stays in the operand *)
		PROCEDURE TypeTest(tag: IntermediateCode.Operand; type: SyntaxTree.Type; trueL,falseL: Label);
		VAR left,right: IntermediateCode.Operand; level,offset: LONGINT;
		BEGIN
			type := type.resolved;
			IF type IS SyntaxTree.PointerType THEN
				type := type(SyntaxTree.PointerType).pointerBase.resolved;
			END;
			ASSERT(type IS SyntaxTree.RecordType);
			level := type(SyntaxTree.RecordType).Level();
			(* get type desc tag of level relative to base tag *)
			offset := addressType.sizeInBits*BaseTypesTable - addressType.sizeInBits * level;
			(*
			IntermediateCode.MakeMemory(tag,addressType); (*! already done during generation *)
			*)
			ReuseCopy(left,tag);
			IntermediateCode.AddOffset(left,ToMemoryUnits(system,offset));
			right := TypeDescriptorAdr(type);
			IntermediateCode.MakeMemory(left,addressType);
			IF ~newObjectFile THEN
				IntermediateCode.MakeMemory(right,addressType);
			END;
			BreqL(trueL,left,right);
			ReleaseIntermediateOperand(left); ReleaseIntermediateOperand(right);
			BrL(falseL);
		END TypeTest;

		PROCEDURE Error(position: LONGINT; CONST s: ARRAY OF CHAR);
		BEGIN
			backend.Error(module.module.sourceName,position,Diagnostics.Invalid,s);
			IF dump # NIL THEN
				dump.String(s); dump.Ln;
			END;
		END Error;

		PROCEDURE AddImport(CONST moduleName: ARRAY OF CHAR; VAR module: SyntaxTree.Module; force: BOOLEAN): BOOLEAN;
		VAR import: SyntaxTree.Import;
			s: Scanner.StringType;
			selfName: SyntaxTree.String;
		BEGIN
			moduleScope.ownerModule.GetName(selfName);
			IF (moduleName = selfName) & (moduleScope.ownerModule.context = Global.A2Name) THEN
				module := moduleScope.ownerModule
			ELSE
				import := moduleScope.ImportByModuleName(SyntaxTree.NewIdentifier(moduleName),SyntaxTree.NewIdentifier("A2"));
				IF import = NIL THEN
					import := SyntaxTree.NewImport(-1,SyntaxTree.NewIdentifier(moduleName),SyntaxTree.NewIdentifier(moduleName),TRUE);

					import.SetContext(SyntaxTree.NewIdentifier("A2"));
					IF ~checker.AddImport(moduleScope.ownerModule,import) THEN
						IF force THEN
							s := "Module ";
							Strings.Append(s,moduleName);
							Strings.Append(s," cannot be imported.");
							Error(position,s);
						(* ELSE import could not be resolved, is (allowed) upcall. For low level modules. *)
						END;
						RETURN FALSE
					ELSE
						SELF.module.imports.AddName(moduleName)
					END;
				ELSIF import.module = NIL THEN (* already tried *)
					RETURN FALSE
				END;
				module := import.module;
			END;
			RETURN TRUE
		END AddImport;

		PROCEDURE Emulate(CONST x: IntermediateCode.Instruction; CONST moduleName,procedureName: Scanner.StringType);
		(*! this emulation procedure emulates instructions with destination operand only *)
		VAR
			machine: SyntaxTree.Module;
			procedure: SyntaxTree.Procedure;
			saved: RegisterEntry;
			s: Scanner.StringType;
			prevResult: Operand;
		BEGIN
			IF AddImport(moduleName,machine,TRUE) THEN
				(*IF x.op1.register > 0 THEN
					registers.Unuse(x.op1.register); (* avoid push on acquired but not yet set destination register *)
				END;*)
				IF x.op1.register >0 THEN RemoveRegisterEntry(usedRegisters,x.op1.register) END;
				procedure := machine.moduleScope.FindProcedure(SyntaxTree.NewIdentifier(procedureName));
				IF procedure = NIL THEN
					s := "Instruction not supported on target, emulation procedure ";
					Strings.Append(s,moduleName);
					Strings.Append(s,".");
					Strings.Append(s,procedureName);
					Strings.Append(s," not present");
					Error(position,s);
				ELSE
					prevResult := result;
					StaticCallOperand(result,procedure);
					SaveRegisters();
					IF x.op2.mode # IntermediateCode.Undefined THEN
						Emit(Push(x.op2));
					END;
					IF x.op3.mode # IntermediateCode.Undefined THEN
						Emit(Push(x.op3));
					END;
					ReleaseUsedRegisters(saved);
					Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
					(*IF x.op1.register > 0 THEN
						registers.Use(x.op1.register); (* avoid push on acquired but not yet set destination register *)
					END;*)
					Emit(Result(x.op1));
					result := prevResult;
					RestoreRegisters(saved);
					IF x.op1.register >0 THEN AddRegisterEntry(usedRegisters,x.op1.register) END;
				END;
				(*
				AcquireThisRegister(x.op1.type,IntermediateCode.Result);
				RestoreRegisters(saved);
				IF x.op1.register > 0 THEN
					IF usedRegisters[x.op1.register].count = 0 THEN
						AcquireThisRegister(usedRegisters[x.op1.register].type,x.op1.register)
					ELSE
						UseRegister(x.op1.register);
					END;
				END;
				IntermediateCode.InitRegister(reg,x.op1.type,IntermediateCode.Result);
				Emit(Mov(x.op1,reg));
				ReleaseIntermediateOperand(reg);
				*)
			END;
		END Emulate;

		PROCEDURE SysCall(nr: LONGINT);
		VAR op: IntermediateCode.Operand; section: IntermediateCode.Section; pooledName: Basic.PooledName;
		BEGIN
			Basic.InitPooledName(pooledName);
			pooledName[0] := systemCalls[nr].name;
			section := NewSection(module.allSections, Sections.SystemCallKind,Sections.CodeSection, FALSE, pooledName,systemCalls[nr],commentPrintout # NIL); (* NOTE: by default no definition *)
			section.SetEntryNumber(nr);
			IntermediateCode.InitAddress(op,addressType,section,0);
			Emit(Call(op,0)); (*! replace 0 by par size for other architectures ! *)
		END SysCall;

		PROCEDURE ConditionToValue(x: SyntaxTree.Expression);
		VAR exit: Label; trueL,falseL: Label;
		BEGIN
			trueL := NewLabel();
			falseL := NewLabel();
			exit := NewLabel();
			Condition(x,trueL,falseL);
			InitOperand(result,ModeValue);
			SetLabel(trueL);
			IntermediateCode.InitRegister(result.op,IntermediateCode.GetType(system,x.type),AcquireRegister(IntermediateCode.GetType(system,x.type)));
			Emit(Mov(result.op,true));
			BrL(exit);
			SetLabel(falseL);
			Emit(MovReplace(result.op,false));
			SetLabel(exit);
		END ConditionToValue;

		PROCEDURE ValueToCondition(VAR op: Operand);
		BEGIN
			LoadValue(op,system.booleanType);
			BrneL(trueLabel,op.op, false);
			ReleaseOperand(op);
			BrL(falseLabel);
		END ValueToCondition;

		PROCEDURE GetDynamicSize(type: SyntaxTree.Type; tag: IntermediateCode.Operand):IntermediateCode.Operand;
		VAR size: LONGINT;
			PROCEDURE GetArraySize(type: SyntaxTree.ArrayType; offset: LONGINT):IntermediateCode.Operand;
			VAR baseType: SyntaxTree.Type; size: LONGINT; sizeOperand,len,res: IntermediateCode.Operand;
			BEGIN
				ASSERT(type.form = SyntaxTree.Open);
				baseType := type.arrayBase.resolved;
				IF IsOpenArray(baseType) THEN
					sizeOperand := GetArraySize(baseType(SyntaxTree.ArrayType),offset+system.addressSize);
				ELSE
					size := ToMemoryUnits(system,system.SizeOf(baseType));
					sizeOperand :=  IntermediateCode.Immediate(addressType,size);
				END;
				len := tag;
				IntermediateCode.AddOffset(len,ToMemoryUnits(system,offset));
				IntermediateCode.MakeMemory(len,addressType);
				UseIntermediateOperand(len);
				Reuse2(res,sizeOperand,len);
				Emit(Mul(res,sizeOperand,len));
				ReleaseIntermediateOperand(sizeOperand); ReleaseIntermediateOperand(len);
				RETURN res
			END GetArraySize;

		BEGIN
			type := type.resolved;
			IF IsOpenArray(type)  THEN
				IF tag.mode = IntermediateCode.ModeImmediate THEN (* special rule for winapi/c  arrays *)
					RETURN tag
				ELSE
					RETURN  GetArraySize(type.resolved(SyntaxTree.ArrayType),0)
				END;
			ELSE
				size := ToMemoryUnits(system,system.SizeOf(type));
				RETURN IntermediateCode.Immediate(addressType,size)
			END;
		END GetDynamicSize;

		(*
		to find imported symbol. not needed ?
		PROCEDURE SymbolByName(CONST moduleName, symbolName: ARRAY OF CHAR): SyntaxTree.Symbol;
		VAR importedModule: SyntaxTree.Module; symbol: SyntaxTree.Symbol;
		BEGIN
			IF AddImport(moduleName,importedModule,FALSE) THEN
				symbol := importedModule.moduleScope.FindSymbol(SyntaxTree.NewIdentifier(symbolName));
				RETURN symbol
			ELSE
				RETURN NIL
			END
		END SymbolByName;
		*)

		PROCEDURE GetRuntimeProcedure(CONST moduleName, procedureName: ARRAY OF CHAR; VAR procedure: SyntaxTree.Procedure; force: BOOLEAN): BOOLEAN;
		VAR runtimeModule: SyntaxTree.Module; s: Scanner.StringType;
		BEGIN
			IF AddImport(moduleName,runtimeModule,force) THEN
				procedure := runtimeModule.moduleScope.FindProcedure(SyntaxTree.NewIdentifier(procedureName));
				IF procedure = NIL THEN
					s := "Procedure ";
					Strings.Append(s,moduleName);
					Strings.Append(s,".");
					Strings.Append(s,procedureName);
					Strings.Append(s," not present");
					Error(position,s);
					RETURN FALSE
				ELSE
					RETURN TRUE
				END;
			ELSE RETURN FALSE
			END;
		END GetRuntimeProcedure;

		PROCEDURE GetTypeDescriptor(CONST moduleName, typeName: ARRAY OF CHAR): IntermediateCode.Section;
		VAR importedModule: SyntaxTree.Module; source: IntermediateCode.Section; symbol: SyntaxTree.Symbol; pooledName: Basic.PooledName;
			s: Scanner.StringType;
		BEGIN
			Basic.InitPooledName(pooledName);
			pooledName[0] := Basic.MakeString(moduleName);
			pooledName[1] := Basic.MakeString(typeName);

			IF AddImport(moduleName,importedModule, FALSE) THEN
				symbol := importedModule.moduleScope.FindTypeDeclaration(SyntaxTree.NewIdentifier(typeName));
				IF symbol = NIL THEN
					s := "type  ";
					Strings.Append(s,moduleName);
					Strings.Append(s,".");
					Strings.Append(s,typeName);
					Strings.Append(s," not present");
					Error(position,s);
				END;
			ELSE symbol := NIL;
			END;
			IF importedModule = moduleScope.ownerModule THEN
				source := NewSection(module.allSections, Sections.RegularKind, Sections.ConstSection, TRUE, pooledName, symbol, commentPrintout # NIL);
			ELSE
				IF currentCellScope # NIL THEN
					currentCellScope.AddImport(importedModule);
				END;
				source := NewSection(module.allSections, Sections.ImportedSymbolKind, Sections.ConstSection, FALSE, pooledName, symbol, commentPrintout # NIL);
			END;
			RETURN source
		END GetTypeDescriptor;


		PROCEDURE CallThis(CONST moduleName, procedureName: ARRAY OF CHAR);
		VAR procedure: SyntaxTree.Procedure; result: Operand; reg: IntermediateCode.Operand; source: IntermediateCode.Section;
			pooledName: Basic.PooledName;
		BEGIN
			IF GetRuntimeProcedure(moduleName,procedureName,procedure,FALSE) THEN (* ready for dynamic linking *)
				StaticCallOperand(result,procedure);
				Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
				ReleaseOperand(result);
			ELSE (* only static linking possible *)
				IF currentCellScope # NIL THEN
					(*
					currentCellScope.AddImport(importedModule);
					*)
				END;
				Basic.InitPooledName(pooledName);
				pooledName[0] := Basic.MakeString(moduleName);
				pooledName[1] := Basic.MakeString(procedureName);
				source := NewSection(module.allSections, Sections.ImportedSymbolKind, Sections.CodeSection, FALSE, pooledName, NIL,commentPrintout # NIL);
				IntermediateCode.InitAddress(reg, addressType, source , 0);
				Emit(Call(reg, 0));
			END;
		END CallThis;
		(* call moduleName.procedureName if it can be imported, otherwise use altModuleName.altProcedureName  *)
		PROCEDURE CallThis2(CONST moduleName, procedureName,altModuleName, altProcedureName: ARRAY OF CHAR; return: IntermediateCode.Operand);
		VAR procedure: SyntaxTree.Procedure; result: Operand; address: IntermediateCode.Operand; source: IntermediateCode.Section;
			pooledName: Basic.PooledName;
		BEGIN
			IF GetRuntimeProcedure(moduleName,procedureName,procedure,FALSE) THEN (* ready for dynamic linking *)
				StaticCallOperand(result,procedure);
				Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
				Emit(Result(return));
				ReleaseOperand(result);
			ELSE (* only static linking possible *)
				IF currentCellScope # NIL THEN
					(* currentCellScope.AddImport(importedModule);*)
				END;
				Basic.InitPooledName(pooledName);
				pooledName[0] := Basic.MakeString(altModuleName);
				pooledName[1] := Basic.MakeString(altProcedureName);
				source := NewSection(module.allSections, Sections.ImportedSymbolKind, Sections.CodeSection, FALSE, pooledName, NIL,commentPrintout # NIL);
				IntermediateCode.InitAddress(address, addressType, source , 0);
				Emit(Call(address, 0));

				Emit(Result(return));
			END;
		END CallThis2;

		PROCEDURE CompareString(br: ConditionalBranch; leftExpression,rightExpression: SyntaxTree.Expression);
		VAR
			left,right: Operand;
			leftSize, rightSize: IntermediateCode.Operand;
			procedure: SyntaxTree.Procedure;
			saved: RegisterEntry;
			reg: IntermediateCode.Operand;
			procedureName: SyntaxTree.String;
		BEGIN
			procedureName := "CompareString";

			IF GetRuntimeProcedure(runtimeModuleName,procedureName,procedure,TRUE) THEN
				SaveRegisters();ReleaseUsedRegisters(saved);
				Designate(leftExpression,left);
				leftSize := GetDynamicSize(leftExpression.type,left.tag);
				Emit(Push(leftSize));
				ReleaseIntermediateOperand(leftSize);
				Emit(Push(left.op));
				ReleaseOperand(left);

				Designate(rightExpression,right);
				rightSize := GetDynamicSize(rightExpression.type,right.tag);
				Emit(Push(rightSize));
				ReleaseIntermediateOperand(rightSize);
				Emit(Push(right.op));
				ReleaseOperand(right);

				StaticCallOperand(result,procedure);
				IntermediateCode.InitRegister(reg,int8,AcquireRegister(int8));
				Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
				Emit(Result(reg));
				ReleaseOperand(result);
				(*
				AcquireThisRegister(int8,IntermediateCode.Result);
				*)
				RestoreRegisters(saved); (* must be done before use of result, might be jumped over otherwise *)
				(*
				IntermediateCode.InitRegister(reg,int8,IntermediateCode.Result);
				*)
				br(trueLabel,reg,IntermediateCode.Immediate(int8,0));
				ReleaseIntermediateOperand(reg);
				BrL(falseLabel);
			END;
		END CompareString;

		PROCEDURE CopyString(leftExpression,rightExpression: SyntaxTree.Expression);
		VAR
			left,right: Operand;
			leftSize, rightSize: IntermediateCode.Operand;
			procedure: SyntaxTree.Procedure;
			saved: RegisterEntry;
			procedureName: SyntaxTree.String;
		BEGIN
			procedureName := "CopyString";

			IF GetRuntimeProcedure(runtimeModuleName,procedureName,procedure,TRUE) THEN
				SaveRegisters();ReleaseUsedRegisters(saved);
				Designate(leftExpression,left);
				leftSize := GetDynamicSize(leftExpression.type,left.tag);
				Emit(Push(leftSize));
				ReleaseIntermediateOperand(leftSize);
				Emit(Push(left.op));
				ReleaseOperand(left);

				Designate(rightExpression,right);
				rightSize := GetDynamicSize(rightExpression.type,right.tag);
				Emit(Push(rightSize));
				ReleaseIntermediateOperand(rightSize);
				Emit(Push(right.op));
				ReleaseOperand(right);

				StaticCallOperand(result,procedure);
				Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
				ReleaseOperand(result);
				RestoreRegisters(saved);
			END;
		END CopyString;

		PROCEDURE VisitBinaryExpression(x: SyntaxTree.BinaryExpression);
		VAR left,right: Operand; temp: Operand;  zero, one: IntermediateCode.Operand;
			leftType,rightType: SyntaxTree.Type;
			leftExpression,rightExpression : SyntaxTree.Expression;
			value: HUGEINT; exp: LONGINT;next,exit: Label; recordType: SyntaxTree.RecordType; dest: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitBinaryExpression") END;
			dest := destination; destination := emptyOperand;
			leftType := x.left.type.resolved;
			rightType := x.right.type.resolved;
			(* for "OR" and "&" the left and right expressions may not be emitted first <= shortcut evaluation *)
			CASE x.operator OF
			Scanner.Or:
				(* shortcut evaluation of left OR right *)
				IF ~conditional THEN ConditionToValue(x);
				ELSE
					next := NewLabel();
					Condition(x.left,trueLabel,next);
					SetLabel(next);
					Condition(x.right,trueLabel,falseLabel);
				END;
			|Scanner.And:
				(* shortcut evaluation of left & right *)
				IF ~conditional THEN ConditionToValue(x);
				ELSE
					next := NewLabel();
					Condition(x.left,next,falseLabel);
					SetLabel(next);
					Condition(x.right,trueLabel,falseLabel);
				END;
			|Scanner.Is:
				IF ~conditional THEN ConditionToValue(x);
				ELSE
					(* get type desc tag *)
					IF IsPointerToRecord(leftType,recordType) THEN
						Evaluate(x.left,left);
						Dereference(left,recordType)
					ELSE
						Designate(x.left,left);
					END;
					TypeTest(left.tag,x.right(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType.resolved,trueLabel,falseLabel);
					ReleaseOperand(left);
				END;
			|Scanner.Plus:
				Evaluate(x.left,left);
				Evaluate(x.right,right);
				IF leftType IS SyntaxTree.SetType THEN
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(Or(result.op,left.op,right.op));
				ELSE
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(Add(result.op,left.op,right.op));
				END;
				ReleaseOperand(left); ReleaseOperand(right);
			|Scanner.Minus:
				Evaluate(x.left,left);
				Evaluate(x.right,right);
				IF leftType IS SyntaxTree.SetType THEN
					InitOperand(result,ModeValue);
					Reuse1(result.op,right.op);
					Emit(Not(result.op,right.op));
					ReleaseOperand(right);
					Emit(And(result.op,result.op,left.op));
					ReleaseOperand(left);
				ELSE
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(Sub(result.op,left.op,right.op));
					ReleaseOperand(left); ReleaseOperand(right);
				END;
			|Scanner.Times:
				Evaluate(x.left,left);
				Evaluate(x.right,right);
				IF leftType IS SyntaxTree.SetType THEN
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(And(result.op,left.op,right.op));
				ELSIF (x.type.resolved IS SyntaxTree.IntegerType) & IsIntegerConstant(x.right,value) & PowerOf2(value,exp) THEN
					InitOperand(result,ModeValue);
					Reuse1a(result.op,left.op,dest);
					IntermediateCode.InitImmediate(right.op,IntermediateCode.GetType(system,rightType),exp);
					Emit(Shl(result.op,left.op,right.op));
				ELSE
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(Mul(result.op,left.op,right.op));
				END;
				ReleaseOperand(left); ReleaseOperand(right);
			|Scanner.Div:
				Evaluate(x.left,left);
				Evaluate(x.right,right);
				IF (x.type.resolved IS SyntaxTree.IntegerType) & IsIntegerConstant(x.right,value) & PowerOf2(value,exp) THEN
					InitOperand(result,ModeValue);
					Reuse1a(result.op,left.op,dest);
					IntermediateCode.InitImmediate(right.op,IntermediateCode.GetType(system,rightType),exp);
					Emit(Shr(result.op,left.op,right.op));
				ELSE
					IF (x.type.resolved IS SyntaxTree.IntegerType) & (x.right.resolved = NIL) THEN (* divisor negative check *)
						IntermediateCode.InitImmediate(zero,IntermediateCode.GetType(system,rightType),0);
						IF ~backend.noRuntimeChecks THEN
							exit := NewLabel();
							BrltL(exit,zero,right.op);
							Emit(Trap(NegativeDivisorTrap));
							SetLabel(exit);
						END;
					END;
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(Div(result.op,left.op,right.op));
				END;
				ReleaseOperand(left); ReleaseOperand(right);
			|Scanner.Mod:
				Evaluate(x.left,left);
				Evaluate(x.right,right);
				IF (x.type.resolved IS SyntaxTree.IntegerType) & IsIntegerConstant(x.right,value) & PowerOf2(value,exp) THEN
					IntermediateCode.InitImmediate(right.op,IntermediateCode.GetType(system,x.type),value-1);
					InitOperand(result,ModeValue);
					Reuse1a(result.op,left.op,dest);
					Emit(And(result.op,left.op,right.op));
				ELSE
					IF (x.type.resolved IS SyntaxTree.IntegerType) & (x.right.resolved = NIL) THEN (* divisor negative check *)
						IntermediateCode.InitImmediate(zero,IntermediateCode.GetType(system,rightType),0);
						IF ~backend.noRuntimeChecks THEN
							exit := NewLabel();
							BrltL(exit,zero,right.op);
							Emit(Trap(NegativeDivisorTrap));
							SetLabel(exit);
						END;
					END;
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(Mod(result.op,left.op,right.op));
				END;
				ReleaseOperand(left); ReleaseOperand(right);
			|Scanner.Slash:
				Evaluate(x.left,left);
				Evaluate(x.right,right);
				IF leftType IS SyntaxTree.SetType THEN
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(Xor(result.op,left.op,right.op));
				ELSE
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(Div(result.op,left.op,right.op));
				END;
				ReleaseOperand(left); ReleaseOperand(right);
			|Scanner.Equal:
				IF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BreqL,x.left,x.right);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					IF leftType IS SyntaxTree.RangeType THEN
						ASSERT(rightType IS SyntaxTree.RangeType);
						BrneL(falseLabel, left.op, right.op); (* first *)
						BrneL(falseLabel, left.tag, right.tag); (* last *)
						BrneL(falseLabel, left.extra, right.extra); (* step *)
						ReleaseOperand(left); ReleaseOperand(right);
						BrL(trueLabel)
					ELSE
						BrneL(falseLabel,left.op,right.op); (* inverse evaluation to optimize jumps for true case *)
						ReleaseOperand(left); ReleaseOperand(right);
						BrL(trueLabel);
					END;
				END;
			|Scanner.LessEqual:
				IF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BrgeL,x.right,x.left);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					IF leftType IS SyntaxTree.SetType THEN (* left subsetequal right: left \cap right = left  *)
						Reuse1(temp.op,right.op);
						Emit(And(temp.op,left.op,right.op));
						ReleaseOperand(right);
						BreqL(trueLabel,temp.op,left.op);
						BrL(falseLabel);
						ReleaseOperand(temp);ReleaseOperand(left);
					ELSE
						BrltL(falseLabel,right.op,left.op); (* inverse evaluation to optimize jumps for true case *)
						ReleaseOperand(left); ReleaseOperand(right);
						BrL(trueLabel);
					END;
				END;
			|Scanner.Less:
				IF leftType IS SyntaxTree.SetType THEN (* left < right <=> left <= right & left # right *)
					leftExpression := SyntaxTree.NewBinaryExpression(-1,x.left,x.right,Scanner.LessEqual);
					leftExpression.SetType(system.booleanType);
					rightExpression := SyntaxTree.NewBinaryExpression(-1,x.left,x.right,Scanner.Unequal);
					rightExpression.SetType(system.booleanType);
					leftExpression := SyntaxTree.NewBinaryExpression(-1,leftExpression,rightExpression,Scanner.And);
					leftExpression.SetType(system.booleanType);
					Expression(leftExpression);
				ELSIF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BrltL,x.left,x.right);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					BrgeL(falseLabel,left.op,right.op); (* inverse evaluation to optimize jumps for true case *)
					ReleaseOperand(left); ReleaseOperand(right);
					BrL(trueLabel);
				END;
			|Scanner.Greater:
				IF leftType IS SyntaxTree.SetType THEN (* left > right <=> left >= right & left # right  *)
					leftExpression := SyntaxTree.NewBinaryExpression(-1,x.left,x.right,Scanner.GreaterEqual);
					leftExpression.SetType(system.booleanType);
					rightExpression := SyntaxTree.NewBinaryExpression(-1,x.left,x.right,Scanner.Unequal);
					rightExpression.SetType(system.booleanType);
					leftExpression := SyntaxTree.NewBinaryExpression(-1,leftExpression,rightExpression,Scanner.And);
					leftExpression.SetType(system.booleanType);
					Expression(leftExpression);
				ELSIF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BrltL,x.right,x.left);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					BrgeL(falseLabel, right.op,left.op); (* inverse evaluation to optimize jumps for true case *)
					ReleaseOperand(left); ReleaseOperand(right);
					BrL(trueLabel);
				END;
			|Scanner.GreaterEqual:
				IF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BrgeL,x.left,x.right);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					IF leftType IS SyntaxTree.SetType THEN (* left supsetequal right: left \cap right = right *)
						Reuse1(temp.op,left.op);
						Emit(And(temp.op,left.op,right.op));
						ReleaseOperand(left);
						BreqL(trueLabel, temp.op,right.op);
						ReleaseOperand(temp); ReleaseOperand(right);
						BrL(falseLabel);
					ELSE
						BrltL(falseLabel, left.op,right.op); (* inverse evaluation to optimize jumps for true case *)
						ReleaseOperand(left); ReleaseOperand(right);
						BrL(trueLabel);
					END;
				END;
			|Scanner.Unequal:
				IF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BrneL,x.left,x.right);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					IF leftType IS SyntaxTree.RangeType THEN
						ASSERT(rightType IS SyntaxTree.RangeType);
						BrneL(trueLabel, left.op, right.op); (* first *)
						BrneL(trueLabel, left.tag, right.tag); (* last *)
						BrneL(trueLabel, left.extra, right.extra); (* step *)
						ReleaseOperand(left); ReleaseOperand(right);
						BrL(falseLabel)
					ELSE
						BreqL(falseLabel,left.op,right.op); (* inverse evaluation to optimize jumps for true case *)
						ReleaseOperand(left); ReleaseOperand(right);
						BrL(trueLabel);
					END;
				END;
			|Scanner.In:
				ASSERT(rightType.resolved IS SyntaxTree.SetType);
				Evaluate(x.left,left);
				Evaluate(x.right,right);
				Convert(left.op,setType);
				ReuseCopy(temp.op,right.op);
				Emit(Shr(temp.op,temp.op,left.op));
				ReleaseOperand(right); ReleaseOperand(left);
				IntermediateCode.InitImmediate(one,setType,1);
				Emit(And(temp.op,temp.op,one));
				IF conditional THEN
					IntermediateCode.InitImmediate(zero,setType,0);
					BrneL(trueLabel,temp.op,zero);
					ReleaseOperand(temp);
					BrL(falseLabel);
				ELSE
					Convert(temp.op,bool);
					result.mode := ModeValue;
					result.op := temp.op;
				END;
			ELSE
				HALT(100);
			END;
			destination := dest;
			IF Trace THEN TraceExit("VisitBinaryExpression") END;
		END VisitBinaryExpression;

		PROCEDURE VisitRangeExpression(x: SyntaxTree.RangeExpression);
		VAR localResult, operand: Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitRangeExpression") END;

			InitOperand(localResult, ModeValue);

			ASSERT(x.first # NIL);
			Evaluate(x.first, operand);
			localResult.op := operand.op;
			ReleaseOperand(operand);
			UseIntermediateOperand(localResult.op);

			ASSERT(x.last # NIL);
			Evaluate(x.last, operand);
			localResult.tag := operand.op;
			ReleaseOperand(operand);
			UseIntermediateOperand(localResult.tag);

			IF x.step # NIL THEN
				Evaluate(x.step, operand);
				localResult.extra := operand.op;
				ReleaseOperand(operand);
				UseIntermediateOperand(localResult.extra);
			END;

			result := localResult;

			IF Trace THEN TraceExit("VisitRangeExpression") END
		END VisitRangeExpression;

		PROCEDURE VisitTensorRangeExpression*(x: SyntaxTree.TensorRangeExpression);
		BEGIN
			HALT(100); (* should never be evaluated *)
		END VisitTensorRangeExpression;

		PROCEDURE VisitConversion(x: SyntaxTree.Conversion);
		VAR old: Operand; dest: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitConversion") END;
			ASSERT(~(x.expression.type.resolved IS SyntaxTree.RangeType));

			dest := destination; destination := emptyOperand;
			Evaluate(x.expression,old);
			InitOperand(result,ModeValue);
			result.op := old.op;
			ASSERT(result.op.mode # 0);
			Convert(result.op,IntermediateCode.GetType(system,x.type));
			ASSERT(result.op.mode # 0);
			result.tag := old.tag; (*! probably never used *)
			destination := dest;
			IF Trace THEN TraceExit("VisitConversion") END;
		END VisitConversion;

		PROCEDURE VisitTypeDeclaration(x: SyntaxTree.TypeDeclaration);
		BEGIN
			IF Trace THEN TraceEnter("VisitTypeDeclaration") END;
			ASSERT((x.declaredType.resolved IS SyntaxTree.EnumerationType) OR (x.declaredType.resolved IS SyntaxTree.RecordType)
			OR (x.declaredType.resolved IS SyntaxTree.PointerType) & (x.declaredType.resolved(SyntaxTree.PointerType).pointerBase.resolved IS SyntaxTree.RecordType));
			IF Trace THEN TraceExit("VisitTypeDeclaration") END;
		END VisitTypeDeclaration;

		(** designators (expressions) *)

		PROCEDURE VisitSymbolDesignator(x: SyntaxTree.SymbolDesignator);
		BEGIN
			IF Trace THEN TraceEnter("VisitSymbolDesignator") END;
			IF x.left # NIL THEN Expression(x.left) END;
			Symbol(x.symbol,result);
			IF Trace THEN TraceExit("VisitSymbolDesignator") END;
		END VisitSymbolDesignator;

		PROCEDURE BoundCheck(index,length: IntermediateCode.Operand);
		BEGIN
			IF backend.noRuntimeChecks THEN RETURN END;
			IF tagsAvailable THEN
				TrapC(BrltL,index,length,IndexCheckTrap);
			END;
		END BoundCheck;

		PROCEDURE DimensionCheck(base,dim: IntermediateCode.Operand; op: ConditionalBranch );
		VAR d: IntermediateCode.Operand;
		BEGIN
			IF backend.noRuntimeChecks THEN RETURN END;
			MakeMemory(d,base,dim.type,ToMemoryUnits(system,MathDimOffset * addressType.sizeInBits));
			TrapC(op,dim,d,ArraySizeTrap);
			ReleaseIntermediateOperand(d);
		END DimensionCheck;

(*		old version
		PROCEDURE MathIndexDesignator(x: SyntaxTree.IndexDesignator);
		VAR res,summand: IntermediateCode.Operand; index,array,incr,length: Operand; i: LONGINT; e: SyntaxTree.Expression;
			indexLen: IntermediateCode.Operand; type,leftType: SyntaxTree.Type; dim,indexDim: LONGINT; tmp: IntermediateCode.Operand;
			baseType: SyntaxTree.Type; numberRanges,srcDimOffset, destDimOffset: LONGINT;

			srcDim, destDim: IntermediateCode.Operand; first: BOOLEAN;
		BEGIN
			ASSERT(tagsAvailable);
			dim := x.parameters.Length();
			indexDim := 0;

			type := x.type.resolved; (* resulting type *)
			leftType := x.left.type.resolved; (* type of array to be indexed over *)

			numberRanges := 0;
			FOR i := 0 TO dim-1 DO
				e := x.parameters.GetExpression(i);
				IF e IS SyntaxTree.RangeExpression THEN
					INC(numberRanges);
				END;
			END;

			srcDimOffset := 0;
			destDimOffset := 0;
			first := TRUE;
			FOR i := 0 TO dim-1 DO
				e := x.parameters.GetExpression(i);
				IF e IS SyntaxTree.TensorRangeExpression THEN
					srcDimOffset := -dim;
					destDimOffset := -numberRanges;
				ELSE
					Evaluate(e,index);
					Convert(index.op,addressType);
					IF first THEN
						Designate(x.left,array);
						IF leftType(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
							Dereference(array,leftType);
							IF arrayDestinationDimension # 0 THEN
								DimensionCheck(array.tag, IntermediateCode.Immediate(int32,arrayDestinationDimension),BreqL);
							END;
						END;
					END;
					IF srcDimOffset < 0 THEN
						GetMathArrayField(tmp,array.tag, MathDimOffset);
						ReuseCopy(srcDim,tmp);
						ReleaseIntermediateOperand(tmp);
						Emit(Add(srcDim,srcDim,IntermediateCode.Immediate(addressType,i+srcDimOffset)));
					ELSE
						srcDim := IntermediateCode.Immediate(int32,i);
					END;
					GetMathArrayLength(leftType(SyntaxTree.MathArrayType),array,srcDim,FALSE,length);
					Convert(length.op,addressType);
					IF (length.op.mode # IntermediateCode.ModeImmediate) OR (index.op.mode # IntermediateCode.ModeImmediate) THEN
						BoundCheck(index.op, length.op);
					END;
					IF e IS SyntaxTree.RangeExpression THEN
						IF e(SyntaxTree.RangeExpression).to = NIL THEN
							index.tag := length.op;
							UseIntermediateOperand(index.tag);
						ELSE
							Convert(index.tag,addressType);
							IF (length.op.mode # IntermediateCode.ModeImmediate) OR (index.tag.mode # IntermediateCode.ModeImmediate) THEN
								BoundCheck(index.tag, length.op);
							END;
						END;
					END;
					ReleaseOperand(length);
					GetMathArrayIncrement(leftType(SyntaxTree.MathArrayType),array,srcDim,FALSE,incr);
					ReleaseIntermediateOperand(srcDim);
					Convert(incr.op,addressType);
					IF e IS SyntaxTree.RangeExpression THEN
						Convert(index.tag,addressType);
						IF e(SyntaxTree.RangeExpression).from # NIL THEN
							Reuse1(indexLen,index.tag);
							Emit(Sub(indexLen,index.tag,index.op));
						ELSE
							ReuseCopy(indexLen,index.tag);
						END;
						IF e(SyntaxTree.RangeExpression).to # NIL THEN
							Emit(Add(indexLen,indexLen,IntermediateCode.Immediate(addressType,1)));
						END;
						IF destDimOffset < 0 THEN
							GetMathArrayField(tmp,array.tag,MathDimOffset);
							ReuseCopy(destDim,tmp);
							ReleaseIntermediateOperand(tmp);
							Emit(Add(destDim,destDim,IntermediateCode.Immediate(int32,indexDim+destDimOffset)));
							PutMathArrayLenOrIncr(arrayDestinationTag,indexLen,destDim,FALSE);
							PutMathArrayLenOrIncr(arrayDestinationTag,incr.op,destDim,TRUE);
							ReleaseIntermediateOperand(destDim);
						ELSE
							PutMathArrayLength(arrayDestinationTag,indexLen,indexDim);
							PutMathArrayIncrement(arrayDestinationTag,incr.op,indexDim);
						END;
						ReleaseIntermediateOperand(indexLen);
						INC(indexDim);
					END;
					ReuseCopy(summand,index.op);
					ReleaseOperand(index);
					Emit(Mul(summand,summand,incr.op));

					ReleaseOperand(incr);
					IF first THEN
						ReuseCopy(res,summand);
						first := FALSE;
					ELSE
						Emit(Add(res,res,summand));
					END;
					ReleaseIntermediateOperand(summand);
				END;
			END;

			IF first THEN (* empty indexer, for example in a[?] *)
				Designate(x.left,array);
				IF leftType(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
					Dereference(array,leftType);
					IF arrayDestinationDimension # 0 THEN
						DimensionCheck(array.tag, IntermediateCode.Immediate(int32,arrayDestinationDimension),BreqL);
					END;
				END;
				ReuseCopy(res,array.op);
			ELSE
				Emit(Add(res,res,array.op));
			END;

			InitOperand(result,ModeReference);
			result.op := res;

			IF (type IS SyntaxTree.RecordType) & (type(SyntaxTree.RecordType).pointerType = NIL) THEN
				ReleaseIntermediateOperand(result.tag);
				result.tag := TypeDescriptorAdr(type);
				IF ~newObjectFile THEN
					IntermediateCode.MakeMemory(result.tag,addressType);
				END;
			ELSIF IsDelegate(type) THEN
				ReleaseIntermediateOperand(result.tag);
				IntermediateCode.InitMemory(result.tag,addressType,result.op,ToMemoryUnits(system,system.addressSize));
				UseIntermediateOperand(result.tag);
			ELSIF (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form = SyntaxTree.Static) THEN
				ReleaseIntermediateOperand(result.tag);
				IntermediateCode.InitImmediate(result.tag,addressType,type(SyntaxTree.ArrayType).staticLength);
			ELSIF (type IS SyntaxTree.ArrayType)  THEN
				result.tag := array.tag; UseIntermediateOperand(result.tag); result.dimOffset := array.dimOffset+dim-1;
			ELSIF (type IS SyntaxTree.MathArrayType) THEN
				i := dim;
				WHILE indexDim < arrayDestinationDimension DO
					srcDim := IntermediateCode.Immediate(int32,i);
					GetMathArrayLength(leftType(SyntaxTree.MathArrayType),array,srcDim,FALSE,length);
					PutMathArrayLength(arrayDestinationTag,length.op,indexDim);
					ReleaseOperand(length);
					GetMathArrayIncrement(leftType(SyntaxTree.MathArrayType),array,srcDim,FALSE,incr);
					PutMathArrayIncrement(arrayDestinationTag,incr.op,indexDim);
					ReleaseOperand(incr);
					INC(i); INC(indexDim);
				END;

				IF leftType(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
					tmp := nil;
				ELSE
					GetMathArrayField(tmp,array.tag,MathPtrOffset);
				END;
				PutMathArrayField(arrayDestinationTag,tmp,MathPtrOffset);
				ReleaseIntermediateOperand(tmp);
				IF leftType(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
					baseType := SemanticChecker.ArrayBase(type,indexDim);
					tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOf(baseType)));
				ELSE
					GetMathArrayField(tmp,array.tag,MathElementSizeOffset);
				END;
				PutMathArrayField(arrayDestinationTag,tmp,MathElementSizeOffset);
				ReleaseIntermediateOperand(tmp);
				PutMathArrayField(arrayDestinationTag,res,MathAdrOffset);

				IF arrayDestinationDimension # 0 THEN
					PutMathArrayField(arrayDestinationTag,IntermediateCode.Immediate(addressType,arrayDestinationDimension),MathDimOffset);
				END;
				PutMathArrayField(arrayDestinationTag,IntermediateCode.Immediate(addressType,SYSTEM.VAL(LONGINT,{RangeFlag})),MathFlagsOffset);

				ReleaseIntermediateOperand(result.tag);
				result.tag := arrayDestinationTag;
			END;
			ReleaseOperand(array);

			IF (conditional)  & (type.resolved IS SyntaxTree.BooleanType)  THEN
				ValueToCondition(result); (*! wrong as the result of an index designator is always an address *)
			END;
		END MathIndexDesignator;
*)

		PROCEDURE MathIndexDesignator(x: SyntaxTree.IndexDesignator);
		VAR
			index, range, array, sourceLength, sourceIncrement, localResult: Operand;
			firstIndex, lastIndex, stepSize, summand, targetLength, targetIncrement, tmp, srcDim, destDim: IntermediateCode.Operand;
			expression: SyntaxTree.Expression;
			resultingType, leftType, baseType: SyntaxTree.Type;
			skipLabel1, skipLabel2: Label;
			i, indexListSize, indexDim, rangeCount, indexCount, srcDimOffset, destDimOffset, targetArrayDimensionality: LONGINT;
			staticSourceLength, staticSourceIncrement, staticIndex, staticFirstIndex, staticLastIndex, staticStepSize, staticTargetLength: LONGINT;
			lastIndexIsMax: BOOLEAN;
			variableOp: Operand;
			variable: SyntaxTree.Variable;
			hasTensorRange: BOOLEAN;
		BEGIN
			ASSERT(tagsAvailable);

			resultingType := x.type.resolved; (* resulting type *)
			leftType := x.left.type.resolved; (* type of array to be indexed over *)

			InitOperand(localResult, ModeReference);

			IF resultingType IS SyntaxTree.MathArrayType THEN
				targetArrayDimensionality := resultingType(SyntaxTree.MathArrayType).Dimensionality();

				IF arrayDestinationTag.mode # IntermediateCode.Undefined THEN
					(* a globally defined array destination tag is available -> use and invalidate it*)
					localResult.tag := arrayDestinationTag;
					IntermediateCode.InitOperand(arrayDestinationTag)
				ELSE
					(* otherwise, create a temporary variable and use it to store the array destination tag *)
					variable := GetTemporaryVariable(GetMathArrayDescriptorType(targetArrayDimensionality));
					Symbol(variable, variableOp);
					ReuseCopy(localResult.tag, variableOp.op);
					ReleaseOperand(variableOp);
				END
			END;

			indexListSize := x.parameters.Length();

			(* count the number of ranges in the index list *)
			rangeCount := 0; hasTensorRange := FALSE; indexCount := 0;
			FOR i := 0 TO indexListSize - 1 DO
				expression := x.parameters.GetExpression(i);
				IF expression IS SyntaxTree.TensorRangeExpression THEN hasTensorRange := TRUE
				ELSIF (expression.type # NIL) & (expression.type.resolved IS SyntaxTree.RangeType) THEN INC(rangeCount)
				ELSE INC(indexCount)
				END
			END;

			(* designate the array  to be indexed over *)
			Designate(x.left, array);

			IF leftType(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
				Dereference(array, leftType);
				IF ~hasTensorRange THEN
					DimensionCheck(array.tag, IntermediateCode.Immediate(int32, rangeCount+indexCount), BreqL)
				END
			END;


			(* determine source and destination dimension offsets; this depends on if the list starts with a '?' *)
			IF x.parameters.GetExpression(0) IS SyntaxTree.TensorRangeExpression THEN
				srcDimOffset := -indexListSize;
				destDimOffset := -rangeCount
			ELSE
				srcDimOffset := 0;
				destDimOffset := 0
			END;

			indexDim := 0;

			(* use address of source array as basis *)
			ReuseCopy(localResult.op, array.op);
			(* Convert(localResult.op, addressType); *)

			(* go through the index list *)
			FOR i := 0 TO indexListSize - 1 DO
				expression := x.parameters.GetExpression(i);

				IF expression IS SyntaxTree.TensorRangeExpression THEN
					(* nothing to do *)
				ELSE
					(* determine which dimension of source array is currently looked at *)
					IF srcDimOffset < 0 THEN
						GetMathArrayField(tmp, array.tag, MathDimOffset);
						ReuseCopy(srcDim, tmp);
						ReleaseIntermediateOperand(tmp);
						Emit(Add(srcDim, srcDim, IntermediateCode.Immediate(addressType, i + srcDimOffset)))
					ELSE
						srcDim := IntermediateCode.Immediate(int32, i)
					END;

					(* get length and increment of source array for current dimension *)
					GetMathArrayLength(leftType(SyntaxTree.MathArrayType), array, srcDim, FALSE, sourceLength);
					Convert(sourceLength.op, sizeType);
					GetMathArrayIncrement(leftType(SyntaxTree.MathArrayType), array, srcDim, FALSE, sourceIncrement);
					Convert(sourceIncrement.op, sizeType);
					ReleaseIntermediateOperand(srcDim);

					IF SemanticChecker.IsIntegerType(expression.type.resolved) THEN
						(* SINGLE INDEX *)
						Evaluate(expression, index);
						Convert(index.op, sizeType);

						(* lower bound check *)
						IF IsIntegerImmediate(index.op, staticIndex) THEN
							ASSERT(staticIndex >= 0) (* ensured by the checker *)
						ELSIF backend.noRuntimeChecks THEN (* do nothing *)
						ELSE
							TrapC(BrgeL, index.op, IntermediateCode.Immediate(sizeType, 0), IndexCheckTrap)
						END;

						(* upper bound check *)
						IF IsIntegerImmediate(index.op, staticIndex) & IsIntegerImmediate(sourceLength.op, staticSourceLength) THEN
							ASSERT(staticIndex < staticSourceLength)
						ELSIF backend.noRuntimeChecks THEN (* do nothing *)
						ELSE
							TrapC(BrltL, index.op, sourceLength.op, IndexCheckTrap)
						END;

						ReleaseOperand(sourceLength);
						Convert(index.op, addressType);
						ReuseCopy(summand, index.op);
						ReleaseOperand(index)

					ELSIF expression.type.resolved IS SyntaxTree.RangeType THEN
						(* RANGE OF INDICES *)
						Evaluate(expression, range);
						firstIndex := range.op; UseIntermediateOperand(firstIndex);
						lastIndex := range.tag; UseIntermediateOperand(lastIndex);
						stepSize := range.extra; UseIntermediateOperand(stepSize);
						ReleaseOperand(range);

						Convert(firstIndex, sizeType);
						Convert(lastIndex, sizeType);
						Convert(stepSize, sizeType);

						(* for dynamic upper bounds: add a runtime check, which repaces the upper bound with the largest valid index
						if it is 'MAX(LONGINT)' *)
						IF ~IsIntegerImmediate(lastIndex, staticLastIndex) THEN
							tmp := lastIndex;
							ReuseCopy(lastIndex, tmp);
							ReleaseIntermediateOperand(tmp);
							skipLabel1 := NewLabel();
							BrneL(skipLabel1, lastIndex, IntermediateCode.Immediate(sizeType, MAX(LONGINT)));
							Emit(MovReplace(lastIndex, sourceLength.op)); (* make sure that no new register is allocated *)
							Emit(Sub(lastIndex, lastIndex, IntermediateCode.Immediate(sizeType, 1)));
							SetLabel(skipLabel1)
						END;

						(* check if step size is valid *)
						IF IsIntegerImmediate(stepSize, staticStepSize) THEN
							ASSERT(staticStepSize >= 1) (* ensured by the checker *)
						ELSIF backend.noRuntimeChecks THEN (* do nothing *)
						ELSE
							TrapC(BrgeL, stepSize, IntermediateCode.Immediate(sizeType, 1), IndexCheckTrap)
						END;

						(* check lower bound check *)
						IF IsIntegerImmediate(firstIndex, staticFirstIndex) THEN
							ASSERT(staticFirstIndex >= 0) (* ensured by the checker *)
						ELSIF backend.noRuntimeChecks THEN (* do nothing *)
						ELSE
							TrapC(BrgeL, firstIndex, IntermediateCode.Immediate(sizeType, 0), IndexCheckTrap)
						END;

						(* check upper bound check *)
						IF IsIntegerImmediate(lastIndex, staticLastIndex) & (staticLastIndex = MAX(LONGINT)) THEN
							(* statically open range: nothing to do *)
						ELSIF IsIntegerImmediate(lastIndex, staticLastIndex) & IsIntegerImmediate(sourceLength.op, staticSourceLength) THEN
							ASSERT(staticLastIndex < staticSourceLength)
						ELSIF backend.noRuntimeChecks THEN (* do nothing *)
						ELSE
							TrapC(BrltL, lastIndex, sourceLength.op, IndexCheckTrap)
						END;

						(* determine length of target array for current dimension *)
						(* 1. incorporate last index: *)
						IF IsIntegerImmediate(lastIndex, staticLastIndex) THEN
							(* last index is static *)
							IF IsIntegerImmediate(lastIndex, staticLastIndex) & (staticLastIndex = MAX(LONGINT)) THEN
								targetLength := sourceLength.op
							ELSE
								targetLength := IntermediateCode.Immediate(sizeType, staticLastIndex + 1)
							END;
							UseIntermediateOperand(targetLength);
						ELSE
							(* targetLength := lastIndex + 1 *)
							Reuse1(targetLength, lastIndex);
							Emit(Add(targetLength, lastIndex, IntermediateCode.Immediate(sizeType, 1)));
						END;
						ReleaseOperand(sourceLength);
						ReleaseIntermediateOperand(lastIndex);
						(* 2. incorporate first index: *)
						IF IsIntegerImmediate(firstIndex, staticFirstIndex) & IsIntegerImmediate(targetLength, staticTargetLength) THEN
							(* first index and current target length are static *)
							targetLength := IntermediateCode.Immediate(sizeType, staticTargetLength - staticFirstIndex)
						ELSIF IsIntegerImmediate(firstIndex, staticFirstIndex) & (staticFirstIndex = 0) THEN
							(* first index = 0: nothing to do *)
						ELSE
							(* targetLength := targetLength - firstIndex *)
							ReleaseIntermediateOperand(targetLength);
							ReuseCopy(targetLength, targetLength);
							Emit(Sub(targetLength, targetLength, firstIndex))
						END;

						(* clip negative lengths to 0 *)
						IF IsIntegerImmediate(targetLength, staticTargetLength) THEN
							IF staticTargetLength < 0 THEN
								targetLength := IntermediateCode.Immediate(sizeType, 0)
							END
						ELSE
							skipLabel1 := NewLabel();
							BrgeL(skipLabel1, targetLength, IntermediateCode.Immediate(sizeType, 0));
							Emit(Mov(targetLength, IntermediateCode.Immediate(sizeType, 0)));
							SetLabel(skipLabel1)
						END;

						(* 3. incorporate index step size: *)
						IF IsIntegerImmediate(stepSize, staticStepSize) & IsIntegerImmediate(targetLength, staticTargetLength) THEN
							(* step size and current target length are static *)
							IF staticTargetLength MOD staticStepSize = 0 THEN
								staticTargetLength := staticTargetLength DIV staticStepSize
							ELSE
								staticTargetLength := 1 + staticTargetLength DIV staticStepSize
							END;
							targetLength := IntermediateCode.Immediate(sizeType, staticTargetLength)
						ELSIF IsIntegerImmediate(stepSize, staticStepSize) & (staticStepSize = 1) THEN
							(* step size = 1: nothing to do *)
						ELSE
							(* emit code for this:
							tmp := targetLength MOD stepSize;
							IF tmp = 0 THEN
								targetLength := targetLength DIV stepSize
							ELSE
								targetLength := targetLength DIV stepSize;
								targetLength := targetLength + 1
							END
							*)
							skipLabel1 := NewLabel();
							skipLabel2 := NewLabel();
							tmp := 	IntermediateCode.Register(sizeType, AcquireRegister(sizeType));
							Emit(Mod(tmp, targetLength, stepSize));
							BrneL(skipLabel1, tmp, IntermediateCode.Immediate(sizeType, 0));
							ReleaseIntermediateOperand(targetLength);
							ReuseCopy(targetLength, targetLength);
							Emit(Div(targetLength, targetLength, stepSize));
							BrL(skipLabel2);
							SetLabel(skipLabel1);
							Emit(Div(targetLength, targetLength, stepSize));
							Emit(Add(targetLength, targetLength, IntermediateCode.Immediate(sizeType, 1)));
							SetLabel(skipLabel2);
							ReleaseIntermediateOperand(tmp);
						END;

						(* determine increment of target array for current dimension *)
						IF IsIntegerImmediate(sourceIncrement.op, staticSourceIncrement) & IsIntegerImmediate(stepSize, staticStepSize) THEN
							targetIncrement := IntermediateCode.Immediate(sizeType, staticSourceIncrement * staticStepSize);
							UseIntermediateOperand(targetIncrement) (* actually not needed *)
						ELSIF IsIntegerImmediate(stepSize, staticStepSize) & (staticStepSize = 1) THEN
							(* step size = 1 *)
							targetIncrement := sourceIncrement.op;
							UseIntermediateOperand(targetIncrement)
						ELSE
							(* targetIncrement := sourceIncrement * stepSize *)
							Reuse1(targetIncrement, stepSize);
							ASSERT((sourceIncrement.op.mode # IntermediateCode.ModeImmediate) OR (stepSize.mode # IntermediateCode.ModeImmediate));
							Emit(Mul(targetIncrement, sourceIncrement.op, stepSize))
						END;
						ReleaseIntermediateOperand(stepSize);

						(* write length and increment of target array to descriptor *)
						IF destDimOffset < 0 THEN
							(* determine which dimension of target array is currently looked at *)
							GetMathArrayField(tmp, array.tag, MathDimOffset);
							ReuseCopy(destDim, tmp);
							ReleaseIntermediateOperand(tmp);
							Emit(Add(destDim, destDim, IntermediateCode.Immediate(sizeType, indexDim + destDimOffset)));

							PutMathArrayLenOrIncr(localResult.tag, targetLength, destDim, FALSE);
							PutMathArrayLenOrIncr(localResult.tag, targetIncrement, destDim, TRUE);

							ReleaseIntermediateOperand(destDim)
						ELSE
							PutMathArrayLength(localResult.tag, targetLength, indexDim);
							PutMathArrayIncrement(localResult.tag , targetIncrement, indexDim)
						END;
						ReleaseIntermediateOperand(targetLength);
						ReleaseIntermediateOperand(targetIncrement);

						INC(indexDim);

						Convert(firstIndex, addressType);
						ReuseCopy(summand, firstIndex);
						ReleaseIntermediateOperand(firstIndex)
					ELSE HALT(100);
					END;

					ASSERT((summand.mode # IntermediateCode.ModeImmediate) OR (sourceIncrement.op.mode # IntermediateCode.ModeImmediate));
					Convert(sourceIncrement.op, addressType);
					Convert(summand, addressType);
					Emit(Mul(summand, summand, sourceIncrement.op));

					ReleaseOperand(sourceIncrement);

					Emit(Add(localResult.op, localResult.op, summand));
					ReleaseIntermediateOperand(summand);
				END
			END;

			result := localResult;

			IF (resultingType IS SyntaxTree.RecordType) & (resultingType(SyntaxTree.RecordType).pointerType = NIL) THEN
				ReleaseIntermediateOperand(result.tag);
				result.tag := TypeDescriptorAdr(resultingType);
				IF ~newObjectFile THEN
					IntermediateCode.MakeMemory(result.tag,addressType);
				END;

			ELSIF IsDelegate(resultingType) THEN
				ReleaseIntermediateOperand(result.tag);
				IntermediateCode.InitMemory(result.tag,addressType,result.op,ToMemoryUnits(system,system.addressSize));
				UseIntermediateOperand(result.tag);

			ELSIF (resultingType IS SyntaxTree.ArrayType) & (resultingType(SyntaxTree.ArrayType).form = SyntaxTree.Static) THEN
				ReleaseIntermediateOperand(result.tag);
				IntermediateCode.InitImmediate(result.tag,addressType,resultingType(SyntaxTree.ArrayType).staticLength);

			ELSIF (resultingType IS SyntaxTree.ArrayType) THEN
				result.tag := array.tag; UseIntermediateOperand(result.tag); result.dimOffset := array.dimOffset+indexListSize-1;

			ELSIF (resultingType IS SyntaxTree.MathArrayType) THEN
				(* finalize target array descriptor *)
				ASSERT(result.tag.mode # IntermediateCode.Undefined); (* tag has been already set in the beginning *)

				(* write lengths and increments of target array for remaining dimensions *)
				i := indexListSize;
				WHILE indexDim < targetArrayDimensionality DO
					srcDim := IntermediateCode.Immediate(int32, i);
					GetMathArrayLength(leftType(SyntaxTree.MathArrayType),array,srcDim,FALSE, sourceLength);
					PutMathArrayLength(result.tag, sourceLength.op,indexDim);
					ReleaseOperand(sourceLength);
					GetMathArrayIncrement(leftType(SyntaxTree.MathArrayType),array,srcDim,FALSE,sourceIncrement);
					PutMathArrayIncrement(result.tag, sourceIncrement.op,indexDim);
					ReleaseOperand(sourceIncrement);
					INC(i); INC(indexDim);
				END;

				IF leftType(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
					tmp := nil;
				ELSE
					GetMathArrayField(tmp,array.tag,MathPtrOffset);
				END;
				PutMathArrayField(result.tag, tmp, MathPtrOffset);
				ReleaseIntermediateOperand(tmp);
				IF leftType(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
					baseType := SemanticChecker.ArrayBase(resultingType, indexDim);
					tmp := IntermediateCode.Immediate(addressType, ToMemoryUnits(system,system.SizeOf(baseType)));
				ELSE
					GetMathArrayField(tmp,array.tag, MathElementSizeOffset);
				END;
				PutMathArrayField(result.tag, tmp, MathElementSizeOffset);
				ReleaseIntermediateOperand(tmp);

				PutMathArrayField(result.tag, result.op, MathAdrOffset);

				(* write dimensionality *)
				IF targetArrayDimensionality # 0 THEN
					PutMathArrayField(result.tag, IntermediateCode.Immediate(addressType, targetArrayDimensionality),MathDimOffset);
				END;

				PutMathArrayField(result.tag, IntermediateCode.Immediate(addressType,SYSTEM.VAL(LONGINT,{RangeFlag})),MathFlagsOffset);

			END;

			ReleaseOperand(array);

			IF conditional & (resultingType.resolved IS SyntaxTree.BooleanType) THEN
				ValueToCondition(result); (*! wrong as the result of an index designator is always an address *)
			END;

		END MathIndexDesignator;

		(* TENTATIVE *)
		PROCEDURE DumpOperand(operand: Operand);
		BEGIN
			D.Log.String("    op = ");
			IntermediateCode.DumpOperand(D.Log, operand.op );
			D.Log.Ln;
			D.Log.String("    tag = ");
			IntermediateCode.DumpOperand(D.Log, operand.tag );
			D.Log.Ln;
			D.Log.String("    extra = ");
			IntermediateCode.DumpOperand(D.Log, operand.extra );
			D.Log.Ln;
			D.Log.Update
		END DumpOperand;


		PROCEDURE IndexDesignator(x: SyntaxTree.IndexDesignator);
		VAR length,res: IntermediateCode.Operand; type: SyntaxTree.Type; maxDim: LONGINT; array:Operand;
			index: Operand; e: SyntaxTree.Expression;i: LONGINT; size: LONGINT;

			PROCEDURE Length(type: SyntaxTree.Type; dim: LONGINT; tag: IntermediateCode.Operand): IntermediateCode.Operand;
			VAR res: IntermediateCode.Operand; size: LONGINT;
			BEGIN
				type := type.resolved;
				IF type IS SyntaxTree.ArrayType THEN
					IF type(SyntaxTree.ArrayType).form = SyntaxTree.Static THEN
						RETURN IntermediateCode.Immediate(addressType,type(SyntaxTree.ArrayType).staticLength);
					ELSE
						res := tag;
						IntermediateCode.AddOffset(res,ToMemoryUnits(system,addressType.sizeInBits*(DynamicDim(type(SyntaxTree.ArrayType))-1)));
						IntermediateCode.MakeMemory(res,addressType);
						RETURN res
					END
				ELSE
					size := ToMemoryUnits(system,system.SizeOf(type));
					RETURN IntermediateCode.Immediate(addressType,size);
				END;
			END Length;

			PROCEDURE StaticSize(type: SyntaxTree.Type): LONGINT;
			BEGIN
				WHILE (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form # SyntaxTree.Static) DO
					type := type(SyntaxTree.ArrayType).arrayBase;
				END;
				WHILE (type IS SyntaxTree.MathArrayType) & (type(SyntaxTree.MathArrayType).form # SyntaxTree.Static) DO
					type := type(SyntaxTree.MathArrayType).arrayBase;
				END;
				RETURN ToMemoryUnits(system,system.SizeOf(type));
			END StaticSize;

			PROCEDURE IsImmediate(x: IntermediateCode.Operand): BOOLEAN;
			BEGIN
				RETURN (x.mode = IntermediateCode.ModeImmediate) & (x.symbol = NIL);
			END IsImmediate;


			PROCEDURE AddInt(VAR res: IntermediateCode.Operand; x,y: IntermediateCode.Operand);
			BEGIN
				IF IsImmediate(x) & IsImmediate(y) THEN
					IntermediateCode.InitImmediate(res,x.type,x.intValue+y.intValue);
				ELSE
					IF res.mode # IntermediateCode.ModeRegister THEN
						IntermediateCode.InitRegister(res,x.type,AcquireRegister(x.type));
					END;
					IF IsImmediate(x) & (x.intValue = 0) THEN
						Emit(Mov(res,y))
					ELSIF IsImmediate(y) & (y.intValue=0) THEN
						Emit(Mov(res,x))
					ELSE
						Emit(Add(res, x, y));
					END;
				END;
			END AddInt;

			PROCEDURE MulInt(VAR res: IntermediateCode.Operand; x,y: IntermediateCode.Operand);
			BEGIN
				IF IsImmediate(x) & IsImmediate(y) THEN
					IntermediateCode.InitImmediate(res,x.type,x.intValue*y.intValue);
				ELSE
					IF res.mode # IntermediateCode.ModeRegister THEN
						IntermediateCode.InitRegister(res,x.type,AcquireRegister(x.type));
					END;
					IF IsImmediate(x) & (x.intValue = 1) THEN
						Emit(Mov(res,y))
					ELSIF IsImmediate(y) & (y.intValue=1) THEN
						Emit(Mov(res,x))
					ELSE
						Emit(Mul(res, x, y));
					END;
				END;
			END MulInt;


		BEGIN
			type := x.left.type.resolved;
			maxDim := x.parameters.Length()-1;
			IntermediateCode.InitImmediate(res,addressType,0);
			FOR i := 0 TO maxDim DO
				e := x.parameters.GetExpression(i);
				Evaluate(e,index);
				Convert(index.op,addressType);
				(*
				IF i = 0 THEN
					ReuseCopy(res,index.op);
				ELSE
				*)
					AddInt(res,res,index.op);
				(*
				END;
				*)

				IF i = 0 THEN
					Designate(x.left,array);
					type := x.left.type.resolved;
				END;

				length := Length(type(SyntaxTree.ArrayType),array.dimOffset+i,array.tag);
				IF ((length.mode # IntermediateCode.ModeImmediate) OR (index.op.mode # IntermediateCode.ModeImmediate)) & tagsAvailable THEN
					BoundCheck(index.op, length);
				END;
				ReleaseOperand(index);
				type := type(SyntaxTree.ArrayType).arrayBase.resolved;
				length := Length(type,array.dimOffset+i-1,array.tag);
				IF (length.mode # IntermediateCode.ModeImmediate) OR (length.intValue # 1) THEN
					MulInt(res,res,length);
				END;
			END;
			IF (type IS SyntaxTree.ArrayType) THEN
				IF (type(SyntaxTree.ArrayType).form # SyntaxTree.Static) THEN
					size := StaticSize(type);
					IF size # 1 THEN
						length := IntermediateCode.Immediate(addressType,size);
						MulInt(res,res,length);
					END;
				ELSE
					size := StaticSize(type(SyntaxTree.ArrayType).arrayBase);
					IF size # 1 THEN
						length := IntermediateCode.Immediate(addressType,size);
						MulInt(res,res,length);
					END;
				END;
			END;
			AddInt(res,res,array.op);
			InitOperand(result,ModeReference);
			result.op := res;

			IF (type IS SyntaxTree.RecordType) & (type(SyntaxTree.RecordType).pointerType = NIL) THEN
				ReleaseIntermediateOperand(result.tag);
				result.tag := TypeDescriptorAdr(type);
				IF ~newObjectFile THEN
					IntermediateCode.MakeMemory(result.tag,addressType);
				END
			ELSIF IsDelegate(type) THEN
				ReleaseIntermediateOperand(result.tag);
				IntermediateCode.InitMemory(result.tag,addressType,result.op,ToMemoryUnits(system,system.addressSize));
				UseIntermediateOperand(result.tag);
			ELSIF (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form = SyntaxTree.Static) THEN
				ReleaseIntermediateOperand(result.tag);
				IntermediateCode.InitImmediate(result.tag,addressType,type(SyntaxTree.ArrayType).staticLength);
			ELSIF (type IS SyntaxTree.ArrayType)  THEN
				result.tag := array.tag; UseIntermediateOperand(result.tag); result.dimOffset := array.dimOffset+maxDim;
			END;
			ReleaseOperand(array);

			IF (conditional)  & (type.resolved IS SyntaxTree.BooleanType)  THEN
				ValueToCondition(result); (*! wrong as the result of an index designator is always an address *)
			END;
		END IndexDesignator;

		PROCEDURE VisitIndexDesignator(x: SyntaxTree.IndexDesignator);
		VAR type: SyntaxTree.Type; dest: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitIndexDesignator") END;
			dest := destination; destination := emptyOperand;
			type := x.left.type.resolved;
			IF type IS SyntaxTree.MathArrayType THEN
				MathIndexDesignator(x);
			ELSE ASSERT(type IS SyntaxTree.ArrayType);
				IndexDesignator(x);
			END;
			destination := dest;
			IF Trace THEN TraceExit("VisitIndexDesignator") END;
		END VisitIndexDesignator;

		PROCEDURE PrepareTensorDescriptor(expression: SyntaxTree.IndexDesignator): SyntaxTree.Variable;
		VAR variable: SyntaxTree.Variable; srcOperand,destOperand,procOp: Operand;
			moduleName, procedureName: SyntaxTree.String; arrayBase: SyntaxTree.Module; saved: RegisterEntry; s: SyntaxTree.String;
			procedure: SyntaxTree.Procedure;
			parameters: SyntaxTree.ExpressionList; e: SyntaxTree.Expression;
			prefixIndices, prefixRanges, suffixIndices, suffixRanges,i : LONGINT; tensorFound: BOOLEAN;
		BEGIN
			variable := GetTemporaryVariable(expression.left.type);
			parameters := expression.parameters;

			moduleName := "FoxArrayBase";
			procedureName := "CopyDescriptor";
			IF AddImport(moduleName,arrayBase,TRUE) THEN
				SaveRegisters();ReleaseUsedRegisters(saved);
				procedure := arrayBase.moduleScope.FindProcedure(SyntaxTree.NewIdentifier(procedureName));
				IF procedure = NIL THEN
					s := "procedure ";
					Strings.Append(s,moduleName);
					Strings.Append(s,".");
					Strings.Append(s,procedureName);
					Strings.Append(s," not present");
					Error(position,s);
				ELSE
					(* push address of temporary variable *)
					Symbol(variable,destOperand);
					Emit(Push(destOperand.op));
					ReleaseOperand(destOperand);
					(* push src *)
					Evaluate(expression.left,srcOperand);
					(*
					Dereference(srcOperand,expression.type.resolved);
					Emit(Push(srcOperand.tag));
					*)
					Emit(Push(srcOperand.op));
					ReleaseOperand(srcOperand);

					tensorFound := FALSE;
					FOR i := 0 TO parameters.Length()-1 DO
						e := parameters.GetExpression(i);
						IF e IS SyntaxTree.TensorRangeExpression THEN
							tensorFound := TRUE;
						ELSIF e IS SyntaxTree.RangeExpression THEN
							IF tensorFound THEN INC(suffixRanges) ELSE INC(prefixRanges) END;
						ELSE
							IF tensorFound THEN INC(suffixIndices) ELSE INC(prefixIndices) END;
						END;
					END;

					Emit(Push(IntermediateCode.Immediate(int32,prefixIndices)));
					Emit(Push(IntermediateCode.Immediate(int32,prefixRanges)));
					Emit(Push(IntermediateCode.Immediate(int32,suffixIndices)));
					Emit(Push(IntermediateCode.Immediate(int32,suffixRanges)));

					StaticCallOperand(procOp,procedure);
					Emit(Call(procOp.op,ProcedureParametersSize(system,procedure)));
					ReleaseOperand(procOp);
				END;
				RestoreRegisters(saved);
			END;
			RETURN variable

		END PrepareTensorDescriptor;

		(* nopov *)
		PROCEDURE PushParameter(expression: SyntaxTree.Expression; parameter: SyntaxTree.Parameter; callingConvention: LONGINT; needsParameterBackup: BOOLEAN; VAR parameterBackup: IntermediateCode.Operand);
		VAR
			type, descriptorType, baseType: SyntaxTree.Type;
			operand, tmpOperand, variableOp: Operand;
			baseReg, tmp, dimOp: IntermediateCode.Operand;
			variable: SyntaxTree.Variable;
			dim, i, size: LONGINT;

			(* TODO: needed? *)
			oldArrayDestinationTag: IntermediateCode.Operand;
			oldArrayDestinationDimension: LONGINT;

			PROCEDURE PushArrayLens(formalType,actualType: SyntaxTree.Type; dim: LONGINT);
			VAR tmp: IntermediateCode.Operand;
			BEGIN
				formalType := formalType.resolved; actualType := actualType.resolved;
				IF IsOpenArray(formalType)THEN
					IF actualType IS SyntaxTree.StringType THEN
						Emit(Push(IntermediateCode.Immediate(addressType,actualType(SyntaxTree.StringType).length)));
						RETURN;
					ELSIF actualType(SyntaxTree.ArrayType).form = SyntaxTree.Static THEN
						Emit(Push(IntermediateCode.Immediate(addressType,actualType(SyntaxTree.ArrayType).staticLength)));
					ELSE
						tmp := baseReg;
						IntermediateCode.AddOffset(tmp,ToMemoryUnits(system,dim*system.addressSize));
						IntermediateCode.MakeMemory(tmp,addressType);
						Emit(Push(tmp));
					END;
					PushArrayLens(formalType(SyntaxTree.ArrayType).arrayBase.resolved, actualType(SyntaxTree.ArrayType).arrayBase.resolved,dim-1);
				END;
			END PushArrayLens;

		BEGIN
			IF Trace THEN TraceEnter("PushParameter") END;
			IF expression.resolved # NIL THEN expression := expression.resolved END;
			type := expression.type.resolved;

			ASSERT( (type IS SyntaxTree.MathArrayType) = (parameter.type.resolved IS SyntaxTree.MathArrayType) );

			(* TODO: needed? *)
			oldArrayDestinationTag := arrayDestinationTag;
			oldArrayDestinationDimension := arrayDestinationDimension;

			IF IsArrayOfSystemByte(parameter.type) THEN
				Designate(expression,operand);
				tmp := GetDynamicSize(type,operand.tag);
				ReleaseIntermediateOperand(operand.tag);
				operand.tag := tmp;
				IF callingConvention = SyntaxTree.OberonCallingConvention  THEN
					Emit(Push(operand.tag));
				END;
				Emit(Push(operand.op));
			ELSIF IsOpenArray(parameter.type) THEN
				Designate(expression,operand);
				baseReg := operand.tag;
				IF callingConvention = SyntaxTree.OberonCallingConvention  THEN
					PushArrayLens(parameter.type,type,operand.dimOffset+DynamicDim(parameter.type)-1);
				END;
				Emit(Push(operand.op)); (* address of the array *)
			ELSIF parameter.type.resolved IS SyntaxTree.MathArrayType THEN
				(* case 1 *)
				IF (parameter.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open) &
					(parameter.kind IN {SyntaxTree.ValueParameter, SyntaxTree.ConstParameter}) THEN
					size := MathLenOffset + 2*SemanticChecker.Dimension(parameter.type.resolved,{SyntaxTree.Open});
					size := ToMemoryUnits(system,size*addressType.sizeInBits);
					Emit(Sub(sp,sp,IntermediateCode.Immediate(addressType,size)));
					dim := SemanticChecker.Dimension(parameter.type.resolved,{SyntaxTree.Open});
					arrayDestinationTag := sp;

					(* case 1b *)
					IF expression IS SyntaxTree.IndexDesignator THEN
					(*
						dim := SemanticChecker.Dimension(parameter.type.resolved,{SyntaxTree.Open});
						descriptorType := GetMathArrayDescriptorType(dim);
						variable := GetTemporaryVariable(descriptorType,expression.position);
						Symbol(variable,variableOp);
						arrayDestinationTag := variableOp.op;
						*)
						ReuseCopy(arrayDestinationTag,arrayDestinationTag);
						dim := SemanticChecker.Dimension(parameter.type.resolved,{SyntaxTree.Open});
						arrayDestinationDimension := dim;
						Designate(expression,operand);
					(* case 1a *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open THEN
					Designate(expression,operand);
						Emit(Copy(arrayDestinationTag,operand.tag,IntermediateCode.Immediate(addressType,size)));
						i := 0;
						WHILE (i< dim) & (type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open) DO
							type := type.resolved(SyntaxTree.MathArrayType).arrayBase;
							INC(i);
						END;
						type := expression.type.resolved;
						WHILE (i<dim) DO (* remaining static dimensions *)
							dimOp := IntermediateCode.Immediate(addressType,i);
							GetMathArrayLength(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
							PutMathArrayLength(arrayDestinationTag,tmpOperand.op,i);
							ReleaseOperand(tmpOperand);
							GetMathArrayIncrement(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
							PutMathArrayIncrement(arrayDestinationTag,tmpOperand.op,i);
							ReleaseOperand(tmpOperand);
							INC(i);
						END;
						dimOp := IntermediateCode.Immediate(addressType,dim);
						PutMathArrayField(arrayDestinationTag,dimOp,MathDimOffset);
						PutMathArrayField(arrayDestinationTag,nil,MathFlagsOffset);
					(* case 1d *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
						Designate(expression,operand);
						Dereference(operand,type.resolved);
						DimensionCheck(operand.tag, IntermediateCode.Immediate(int32,dim),BreqL);
						Emit(Copy(sp(*arrayDestinationTag*),operand.tag,IntermediateCode.Immediate(addressType,size)));
						PutMathArrayField(arrayDestinationTag,nil,MathFlagsOffset);
					(* case 1f *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
						Designate(expression,operand);
						FOR i := 0 TO dim-1 DO
							dimOp := IntermediateCode.Immediate(addressType,i);
							GetMathArrayLength(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
							PutMathArrayLength(arrayDestinationTag,tmpOperand.op,i);
							ReleaseOperand(tmpOperand);
							GetMathArrayIncrement(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
							PutMathArrayIncrement(arrayDestinationTag,tmpOperand.op,i);
							ReleaseOperand(tmpOperand);
						END;
						dimOp := IntermediateCode.Immediate(addressType,dim);
						PutMathArrayField(arrayDestinationTag,dimOp,MathDimOffset);
						PutMathArrayField(arrayDestinationTag,operand.op,MathAdrOffset);
						PutMathArrayField(arrayDestinationTag,nil,MathPtrOffset);
						PutMathArrayField(arrayDestinationTag,nil,MathFlagsOffset); (*! set static flag *)
						baseType := SemanticChecker.ArrayBase(type,dim);
						tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOf(baseType)));
						PutMathArrayField(arrayDestinationTag,tmp,MathElementSizeOffset);
					ELSE HALT(100);
					END;
				ELSIF (parameter.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open) & (parameter.kind = SyntaxTree.VarParameter) THEN
					dim := SemanticChecker.Dimension(parameter.type.resolved,{SyntaxTree.Open});
					(* case 2b *)
					IF expression IS SyntaxTree.IndexDesignator THEN
						descriptorType := GetMathArrayDescriptorType(dim);
						variable := GetTemporaryVariable(descriptorType);
						Symbol(variable,variableOp);
						arrayDestinationTag := variableOp.op;
						ReuseCopy(arrayDestinationTag,arrayDestinationTag);
						arrayDestinationDimension := dim;
						Designate(expression,operand);
						Emit(Push(operand.tag));
					(* case 2a *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open THEN
						WHILE (i< dim) & (type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open) DO
							type := type.resolved(SyntaxTree.MathArrayType).arrayBase;
							INC(i);
						END;
						IF i = dim THEN
							Designate(expression,operand);
							Emit(Push(operand.tag));
						ELSE (* open-static *)
							type := expression.type.resolved;
							descriptorType := GetMathArrayDescriptorType(dim);
							variable := GetTemporaryVariable(descriptorType);
							Symbol(variable,variableOp);
							arrayDestinationTag := variableOp.op;
							Designate(expression,operand);
							FOR i := 0 TO dim-1 DO
								dimOp := IntermediateCode.Immediate(addressType,i);
								GetMathArrayLength(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
								PutMathArrayLength(arrayDestinationTag,tmpOperand.op,i);
								ReleaseOperand(tmpOperand);
								GetMathArrayIncrement(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
								PutMathArrayIncrement(arrayDestinationTag,tmpOperand.op,i);
								ReleaseOperand(tmpOperand);
							END;
							dimOp := IntermediateCode.Immediate(addressType,dim);
							PutMathArrayField(arrayDestinationTag,dimOp,MathDimOffset);
							PutMathArrayField(arrayDestinationTag,operand.op,MathAdrOffset);
							PutMathArrayField(arrayDestinationTag,nil,MathPtrOffset);
							PutMathArrayField(arrayDestinationTag,nil,MathFlagsOffset); (*! set static flag *)
							baseType := SemanticChecker.ArrayBase(type,dim);
							tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOf(baseType)));
							PutMathArrayField(arrayDestinationTag,tmp,MathElementSizeOffset);
							Emit(Push(arrayDestinationTag));
						END;
					(* case 2d *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
						Designate(expression,operand);
						Dereference(operand,type.resolved);
						DimensionCheck(operand.tag, IntermediateCode.Immediate(int32,dim),BreqL);
						Emit(Push(operand.tag));
					(* case 2f *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
						descriptorType := GetMathArrayDescriptorType(dim);
						variable := GetTemporaryVariable(descriptorType);
						Symbol(variable,variableOp);
						arrayDestinationTag := variableOp.op;
						Designate(expression,operand);
						FOR i := 0 TO dim-1 DO
							dimOp := IntermediateCode.Immediate(addressType,i);
							GetMathArrayLength(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
							PutMathArrayLength(arrayDestinationTag,tmpOperand.op,i);
							ReleaseOperand(tmpOperand);
							GetMathArrayIncrement(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
							PutMathArrayIncrement(arrayDestinationTag,tmpOperand.op,i);
							ReleaseOperand(tmpOperand);
						END;
						dimOp := IntermediateCode.Immediate(addressType,dim);
						PutMathArrayField(arrayDestinationTag,dimOp,MathDimOffset);
						PutMathArrayField(arrayDestinationTag,operand.op,MathAdrOffset);
						PutMathArrayField(arrayDestinationTag,nil,MathPtrOffset);
						PutMathArrayField(arrayDestinationTag,nil,MathFlagsOffset); (*! set static flag *)
						baseType := SemanticChecker.ArrayBase(type,dim);
						tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOf(baseType)));
						PutMathArrayField(arrayDestinationTag,tmp,MathElementSizeOffset);
						Emit(Push(arrayDestinationTag));
					ELSE HALT(100);
					END;
				ELSIF (parameter.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor) & (parameter.kind IN {SyntaxTree.ConstParameter,SyntaxTree.ValueParameter}) THEN
					dim := SemanticChecker.Dimension(type,{SyntaxTree.Open,SyntaxTree.Static});
					(* case 3b *)
					IF expression IS SyntaxTree.IndexDesignator THEN
						IF type(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN (* indexer of form a[e,....,?] *)
							variable := PrepareTensorDescriptor(expression(SyntaxTree.IndexDesignator));
							Symbol(variable,variableOp);
							LoadValue(variableOp,system.addressType);
						ELSE
							descriptorType := GetMathArrayDescriptorType(dim);
							variable := GetTemporaryVariable(descriptorType);
							Symbol(variable,variableOp);
						END;
						arrayDestinationTag := variableOp.op;
						ReuseCopy(arrayDestinationTag,arrayDestinationTag);
						arrayDestinationDimension := 0;
						Designate(expression,operand);
						Emit(Push(operand.tag));
					(* case 3a *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open THEN
						i := 0;
						WHILE (i< dim) & (type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open) DO
							type := type.resolved(SyntaxTree.MathArrayType).arrayBase;
							INC(i);
						END;
						IF i = dim THEN
							Designate(expression,operand);
							Emit(Push(operand.tag));
						ELSE (* open-static *)
							type := expression.type.resolved;
							descriptorType := GetMathArrayDescriptorType(dim);
							variable := GetTemporaryVariable(descriptorType);
							Symbol(variable,variableOp);
							arrayDestinationTag := variableOp.op;
							Designate(expression,operand);
							FOR i := 0 TO dim-1 DO
								dimOp := IntermediateCode.Immediate(addressType,i);
								GetMathArrayLength(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
								PutMathArrayLength(arrayDestinationTag,tmpOperand.op,i);
								ReleaseOperand(tmpOperand);
								GetMathArrayIncrement(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
								PutMathArrayIncrement(arrayDestinationTag,tmpOperand.op,i);
								ReleaseOperand(tmpOperand);
							END;
							dimOp := IntermediateCode.Immediate(addressType,dim);
							PutMathArrayField(arrayDestinationTag,dimOp,MathDimOffset);
							PutMathArrayField(arrayDestinationTag,operand.op,MathAdrOffset);
							PutMathArrayField(arrayDestinationTag,nil,MathPtrOffset);
							PutMathArrayField(arrayDestinationTag,nil,MathFlagsOffset); (*! set static flag *)
							baseType := SemanticChecker.ArrayBase(type,dim);
							tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOf(baseType)));
							PutMathArrayField(arrayDestinationTag,tmp,MathElementSizeOffset);
							Emit(Push(arrayDestinationTag));
						END;
					(* case 3d *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
						Designate(expression,operand);
						Dereference(operand,type.resolved);
						(*
						DimensionCheck(operand.tag, IntermediateCode.Immediate(int32,dim),BreqL);
						*)
						Emit(Push(operand.tag));
					(* case 3f *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
						descriptorType := GetMathArrayDescriptorType(dim);
						variable := GetTemporaryVariable(descriptorType);
						Symbol(variable,variableOp);
						arrayDestinationTag := variableOp.op;
						Designate(expression,operand);
						FOR i := 0 TO dim-1 DO
							dimOp := IntermediateCode.Immediate(addressType,i);
							GetMathArrayLength(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
							PutMathArrayLength(arrayDestinationTag,tmpOperand.op,i);
							ReleaseOperand(tmpOperand);
							GetMathArrayIncrement(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
							PutMathArrayIncrement(arrayDestinationTag,tmpOperand.op,i);
							ReleaseOperand(tmpOperand);
						END;
						dimOp := IntermediateCode.Immediate(addressType,dim);
						PutMathArrayField(arrayDestinationTag,dimOp,MathDimOffset);
						PutMathArrayField(arrayDestinationTag,operand.op,MathAdrOffset);
						PutMathArrayField(arrayDestinationTag,nil,MathPtrOffset);
						PutMathArrayField(arrayDestinationTag,nil,MathFlagsOffset); (*! set static flag *)
						baseType := SemanticChecker.ArrayBase(type,dim);
						tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOf(baseType)));
						PutMathArrayField(arrayDestinationTag,tmp,MathElementSizeOffset);
						Emit(Push(arrayDestinationTag));
					ELSE HALT(100);
					END;
				ELSIF (parameter.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor) & (parameter.kind = SyntaxTree.VarParameter) THEN
					dim := SemanticChecker.Dimension(type,{SyntaxTree.Open,SyntaxTree.Static});
					(* case 4b *)
					IF expression IS SyntaxTree.IndexDesignator THEN
						IF type(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN (* indexer of form a[e,....,?] *)
							variable := PrepareTensorDescriptor(expression(SyntaxTree.IndexDesignator));
							Symbol(variable,variableOp);
							LoadValue(variableOp,system.addressType);
						ELSE
							descriptorType := GetMathArrayDescriptorType(dim);
							variable := GetTemporaryVariable(descriptorType);
							Symbol(variable,variableOp);
						END;
						arrayDestinationTag := variableOp.op;
						ReuseCopy(arrayDestinationTag,arrayDestinationTag);
						arrayDestinationDimension := 0;
						Designate(expression,operand);
						IF type(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
							Symbol(variable,variableOp);
						ELSE
							variable := GetTemporaryVariable(parameter.type.resolved);
							Symbol(variable,variableOp);
							MakeMemory(tmp,variableOp.op,addressType,0);
							Emit(Mov(tmp,operand.tag));
							ReleaseIntermediateOperand(tmp);
						END;
						Emit(Push(variableOp.op));
						ReleaseOperand(variableOp);
					(* case 4a *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open THEN
						i := 0;
						WHILE (i< dim) & (type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open) DO
							type := type.resolved(SyntaxTree.MathArrayType).arrayBase;
							INC(i);
						END;
						IF i = dim THEN
							Designate(expression,operand);
							arrayDestinationTag := operand.tag;
						ELSE (* open-static *)
							type := expression.type.resolved;
							descriptorType := GetMathArrayDescriptorType(dim);
							variable := GetTemporaryVariable(descriptorType);
							Symbol(variable,variableOp);
							arrayDestinationTag := variableOp.op;
							Designate(expression,operand);
							FOR i := 0 TO dim-1 DO
								dimOp := IntermediateCode.Immediate(addressType,i);
								GetMathArrayLength(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
								PutMathArrayLength(arrayDestinationTag,tmpOperand.op,i);
								ReleaseOperand(tmpOperand);
								GetMathArrayIncrement(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
								PutMathArrayIncrement(arrayDestinationTag,tmpOperand.op,i);
								ReleaseOperand(tmpOperand);
							END;
							dimOp := IntermediateCode.Immediate(addressType,dim);
							PutMathArrayField(arrayDestinationTag,dimOp,MathDimOffset);
							PutMathArrayField(arrayDestinationTag,operand.op,MathAdrOffset);
							PutMathArrayField(arrayDestinationTag,nil,MathPtrOffset);
							PutMathArrayField(arrayDestinationTag,nil,MathFlagsOffset); (*! set static flag *)
							baseType := SemanticChecker.ArrayBase(type,dim);
							tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOf(baseType)));
							PutMathArrayField(arrayDestinationTag,tmp,MathElementSizeOffset);
						END;
						variable := GetTemporaryVariable(parameter.type.resolved);
						Symbol(variable,variableOp);
						MakeMemory(tmp,variableOp.op,addressType,0);
						Emit(Mov(tmp,arrayDestinationTag));
						ReleaseIntermediateOperand(tmp);
						Emit(Push(variableOp.op));
						ReleaseOperand(variableOp);
					(* case 4d *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
						Designate(expression,operand);
						(*
						Dereference(operand,type.resolved);
						*)
						(*
						DimensionCheck(operand.tag, IntermediateCode.Immediate(int32,dim),BreqL);
						*)
						Emit(Push(operand.op));
					(* case 4f *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
						descriptorType := GetMathArrayDescriptorType(dim);
						variable := GetTemporaryVariable(descriptorType);
						Symbol(variable,variableOp);
						arrayDestinationTag := variableOp.op;
						Designate(expression,operand);
						FOR i := 0 TO dim-1 DO
							dimOp := IntermediateCode.Immediate(addressType,i);
							GetMathArrayLength(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
							PutMathArrayLength(arrayDestinationTag,tmpOperand.op,i);
							ReleaseOperand(tmpOperand);
							GetMathArrayIncrement(type.resolved(SyntaxTree.MathArrayType),operand,dimOp,FALSE,tmpOperand);
							PutMathArrayIncrement(arrayDestinationTag,tmpOperand.op,i);
							ReleaseOperand(tmpOperand);
						END;
						dimOp := IntermediateCode.Immediate(addressType,dim);
						PutMathArrayField(arrayDestinationTag,dimOp,MathDimOffset);
						PutMathArrayField(arrayDestinationTag,operand.op,MathAdrOffset);
						PutMathArrayField(arrayDestinationTag,nil,MathPtrOffset);
						PutMathArrayField(arrayDestinationTag,nil,MathFlagsOffset); (*! set static flag *)
						baseType := SemanticChecker.ArrayBase(type,dim);
						tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOf(baseType)));
						PutMathArrayField(arrayDestinationTag,tmp,MathElementSizeOffset);
						variable := GetTemporaryVariable(parameter.type.resolved);
						Symbol(variable,variableOp);
						MakeMemory(tmp,variableOp.op,addressType,0);
						Emit(Mov(tmp,arrayDestinationTag));
						ReleaseIntermediateOperand(tmp);
						Emit(Push(variableOp.op));
						ReleaseOperand(variableOp);
					ELSE HALT(100);
					END;
				ELSIF (parameter.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Static) & (parameter.kind = SyntaxTree.ValueParameter) THEN
						IF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
						size := system.SizeOf(type);
						Basic.Align(size,system.AlignmentOf(system.parameterAlignment,type));
						size := ToMemoryUnits(system,size);
						Emit(Sub(sp,sp,IntermediateCode.Immediate(addressType,size)));
						arrayDestinationTag := sp;
						Designate(expression,operand);
						Emit(Copy(arrayDestinationTag,operand.op,IntermediateCode.Immediate(addressType,size)));
					ELSE HALT(100);
					END;
				ELSIF (parameter.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Static) & (parameter.kind IN {SyntaxTree.VarParameter,SyntaxTree.ConstParameter}) THEN
					IF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
						Designate(expression,operand);
						Emit(Push(operand.op));
					ELSE HALT(100);
					END;
				ELSE HALT(200)
				END;

			ELSIF parameter.type.resolved IS SyntaxTree.RangeType THEN
				IF parameter.kind = SyntaxTree.VarParameter THEN
					ASSERT(~(expression IS SyntaxTree.RangeExpression));
					Designate(expression, operand);
					Emit(Push(operand.op))
				ELSE
					ASSERT((parameter.kind = SyntaxTree.ValueParameter) OR (parameter.kind = SyntaxTree.ConstParameter));
					Evaluate(expression, operand);
					Emit(Push(operand.extra)); (* step *)
					Emit(Push(operand.tag)); (* last *)
					Emit(Push(operand.op)) (* first *)
				END

			ELSE
				IF (parameter.kind = SyntaxTree.ValueParameter) OR (parameter.kind = SyntaxTree.ConstParameter) & ~(parameter.type.resolved IS SyntaxTree.RecordType) & ~(parameter.type.resolved IS SyntaxTree.ArrayType) THEN
					IF (type IS SyntaxTree.RecordType) OR IsStaticArray(parameter.type) THEN
						Designate(expression,operand);
						size := ToMemoryUnits(system,system.SizeOf(parameter.type));
						(* stack allocation *)
						Emit(Sub(sp,sp,IntermediateCode.Immediate(addressType,size + (-size) MOD (system.addressSize DIV system.dataUnit))));
						(*! parameter alignment to be discussed ... *)

						IF type IS SyntaxTree.StringType THEN (* source potentially shorter than destination *)
							size := type(SyntaxTree.StringType).length;
						END;
						Emit(Copy(sp,operand.op,IntermediateCode.Immediate(addressType,size)));
					ELSIF IsOpenArray(parameter.type) THEN
						Designate(expression,operand);
						baseReg := operand.tag;
						IF callingConvention = SyntaxTree.OberonCallingConvention  THEN
							PushArrayLens(parameter.type,type,operand.dimOffset+DynamicDim(parameter.type)-1);
						END;
						Emit(Push(operand.op)); (* address of the array *)
					ELSIF IsDelegate(parameter.type) THEN
						Evaluate(expression,operand);
						Emit(Push(operand.tag));
						Emit(Push(operand.op));
					ELSE
						Evaluate(expression,operand);
						Emit(Push(operand.op));
					END;
				ELSIF expression IS SyntaxTree.NilValue THEN (* for special WinAPI rule *)
					Evaluate(expression,operand);
					Emit(Push(operand.op));
				ELSIF (type IS SyntaxTree.RecordType) & (parameter.kind IN {SyntaxTree.ConstParameter, SyntaxTree.VarParameter}) THEN
					Designate(expression,operand);
					IF callingConvention = SyntaxTree.OberonCallingConvention  THEN
						(* MakeTypeTag(operand); (* late emission, otherwise type tags are generated when not used *) *)
						Emit(Push(operand.tag));
					END;
					Emit(Push(operand.op));
				ELSIF IsDelegate(parameter.type) THEN (* var parameter delegate: push base address only *)
					Designate(expression,operand); (* push address *)
					(* Emit(Push(operand.tag));*)
					Emit(Push(operand.op));
				ELSE (* var parameter *)
					Designate(expression,operand);
					Emit(Push(operand.op));
				END;
			END;

			(* TODO: needed? *)
			arrayDestinationTag := oldArrayDestinationTag;
			arrayDestinationDimension := oldArrayDestinationDimension;

			(* nopov *)
			IF needsParameterBackup THEN
				(* IF dump # NIL THEN dump.String("backup parameter"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
				ReuseCopy(parameterBackup, operand.op)
			END;

			ReleaseOperand(operand);
			IF Trace THEN TraceExit("PushParameter") END;
		END PushParameter;

		PROCEDURE VisitProcedureCallDesignator(x: SyntaxTree.ProcedureCallDesignator);
		VAR
			parameters: SyntaxTree.ExpressionList;
			d, resultDesignator, actualParameter: SyntaxTree.Expression;
			designator: SyntaxTree.Designator;
			procedureType: SyntaxTree.ProcedureType;
			formalParameter: SyntaxTree.Parameter;
			noPush: Label;
			operand: Operand;
			reg, size, mem, mask, dest: IntermediateCode.Operand;
			saved: RegisterEntry;
			symbol: SyntaxTree.Symbol;
			variable: SyntaxTree.Variable;
			i, parametersSize, returnTypeSize, returnTypeOffset: LONGINT;
			structuredReturnType: BOOLEAN;
			firstWriteBackCall, currentWriteBackCall: WriteBackCall;
			tempVariableDesignator: SyntaxTree.Designator;
			gap: LONGINT; (*fld*)

			(* TODO: remove unnecessary backup variables *)
			oldResult: Operand;
			oldCurrentScope: SyntaxTree.Scope;
			oldArrayDestinationTag: IntermediateCode.Operand;
			oldArrayDestinationDimension: LONGINT;
			oldConstantDeclaration: SyntaxTree.Symbol;
			oldDestination: IntermediateCode.Operand;
			oldCurrentLoop: Label;
			oldConditional: BOOLEAN;
			oldTrueLabel, oldFalseLabel: Label;
			oldLocked: BOOLEAN;
			registerUsage: RegisterUsage;
			usedRegisters,oldUsedRegisters: RegisterEntry;

			return: IntermediateCode.Operand;

			(* nopov *)
			parameterBackups: ARRAY 2 OF IntermediateCode.Operand;
			arg: IntermediateCode.Operand;
			dummy: IntermediateCode.Operand;
			recordType: SyntaxTree.RecordType;
			operatorSelectionProcedureOperand: Operand;
			operatorSelectionProcedure: SyntaxTree.Procedure;
			fingerPrint: SyntaxTree.FingerPrint;
			isCallOfDynamicOperator, hasDynamicOperands: BOOLEAN;
			identifierNumber: LONGINT;

			PROCEDURE BackupGlobalState;
			BEGIN
				oldResult := result;
				oldCurrentScope := currentScope;
				oldArrayDestinationTag := arrayDestinationTag;
				oldArrayDestinationDimension := arrayDestinationDimension;
				oldConstantDeclaration := constantDeclaration;
				oldDestination := destination;
				oldCurrentLoop := currentLoop;
				oldConditional := conditional;
				oldTrueLabel := trueLabel;
				oldFalseLabel := falseLabel;
				oldLocked := locked;
				oldUsedRegisters := usedRegisters
			END BackupGlobalState;

			PROCEDURE RestoreGlobalState;
			BEGIN
				result := oldResult;
				currentScope := oldCurrentScope;
				arrayDestinationTag := oldArrayDestinationTag;
				arrayDestinationDimension := oldArrayDestinationDimension;
				constantDeclaration := oldConstantDeclaration;
				destination := oldDestination;
				currentLoop := oldCurrentLoop;
				conditional := oldConditional;
				trueLabel := oldTrueLabel;
				falseLabel := oldFalseLabel;
				locked := oldLocked;
				usedRegisters := oldUsedRegisters
			END RestoreGlobalState;

			(* nopov *)
			(** do preparations before parameter push for array-structured object types (ASOTs):
				if ASOT is passed as VAR parameter:
				- allocate temporary variable of math array type
				- copy contents of ASOT to be passed to temporary variable
				- use temporary variable as the actual parameter instead
				- create and store a write-back call in a list (an index operator call that writes the contents of the temp. variable back into the ASOT)
			**)
			PROCEDURE PrepareParameter(VAR actualParameter: SyntaxTree.Expression; formalParameter: SyntaxTree.Parameter);
			VAR
				expression: SyntaxTree.Expression;
			BEGIN
				IF actualParameter IS SyntaxTree.Designator THEN
					designator := actualParameter(SyntaxTree.Designator);
					IF (formalParameter.kind = SyntaxTree.VarParameter) & (designator.relatedAsot # NIL) THEN
						(* actual parameter is an index read operator call on ASOT and formal parameter is of VAR kind *)
						(* IF dump # NIL THEN dump.String("!!! BEGIN ASOT VAR parameter preparation"); dump.Ln; dump.Update END; *) (* TENTATIVE*)
						ASSERT(checker # NIL);
						checker.SetCurrentScope(currentScope);

						(* allocate temporary variable *)
						ASSERT(actualParameter.type # NIL);
						ASSERT(actualParameter.type.resolved IS SyntaxTree.MathArrayType);
						variable := GetTemporaryVariable(actualParameter.type.resolved);
						tempVariableDesignator := SyntaxTree.NewSymbolDesignator(SemanticChecker.InvalidPosition, NIL, variable);
						tempVariableDesignator.SetType(actualParameter.type.resolved);
						ASSERT(tempVariableDesignator IS SyntaxTree.SymbolDesignator);
						ASSERT(tempVariableDesignator.type # NIL);
						ASSERT(tempVariableDesignator.type.resolved IS SyntaxTree.MathArrayType);

						(* copy math array stored in actual parameter to temporary variable *)
						BackupGlobalState;
						AssignMathArray(tempVariableDesignator, actualParameter);
						RestoreGlobalState;

						(* use temporary variable as actual parameter instead of the original one *)
						actualParameter := tempVariableDesignator;

						(* create write-back call and store it in linked list *)
						(* create new list entry *)
						IF firstWriteBackCall = NIL THEN
							NEW(firstWriteBackCall);
							currentWriteBackCall := firstWriteBackCall
						ELSE
							ASSERT(currentWriteBackCall # NIL);
							NEW(currentWriteBackCall.next);
							currentWriteBackCall := currentWriteBackCall.next
						END;
 						expression := checker.NewIndexOperatorCall(SemanticChecker.InvalidPosition, designator.relatedAsot, designator.relatedIndexList, tempVariableDesignator);
						ASSERT(expression.type = NIL);
						currentWriteBackCall.call := expression(SyntaxTree.ProcedureCallDesignator);
					END
				END
			END PrepareParameter;

		BEGIN
			IF Trace THEN TraceEnter("VisitProcedureCallDesignator") END;
			resultDesignator := procedureResultDesignator; procedureResultDesignator := NIL;
			dest := destination; destination := emptyOperand;
			SaveRegisters();ReleaseUsedRegisters(saved);

			procedureType := x.left.type.resolved(SyntaxTree.ProcedureType);
			parameters := x.parameters;

			(* nopov *)
			IF (x.left IS SyntaxTree.SymbolDesignator) & (x.left(SyntaxTree.SymbolDesignator).symbol IS SyntaxTree.Operator) THEN
				(* an operator is called *)
				(* IF dump # NIL THEN dump.String("*** begin of operator call ***"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
				ASSERT(procedureType.callingConvention = SyntaxTree.OberonCallingConvention);

				(* check if a dynamic operator call should be performed *)
				isCallOfDynamicOperator := x.left(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.Operator).isDynamic
			ELSE
				isCallOfDynamicOperator := FALSE
			END;

			IF procedureType.stackAlignment > 1 THEN
				IntermediateCode.InitRegister(reg,addressType,AcquireRegister(addressType));
				Emit(Mov(reg, sp));
				Emit(Sub(sp, sp, IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.addressSize))));
				IntermediateCode.InitImmediate(mask,addressType,-procedureType.stackAlignment);
				Emit(And(sp, sp, mask));
				IntermediateCode.InitMemory(mem, addressType, sp, 0);
				Emit(Mov(mem,reg));
				ReleaseIntermediateOperand(reg);
			END;

			IF procedureType.callingConvention = SyntaxTree.DarwinCCallingConvention THEN	(*fld*)
				IntermediateCode.InitImmediate(mask,addressType,-16);
				Emit(And(sp, sp, mask));
				gap := (-ParametersSize( system, procedureType, FALSE )) MOD 16;
				IF gap # 0 THEN
					IntermediateCode.InitImmediate(size,addressType,gap);
					Emit(Sub(sp,sp,size))
				END;
			END;

			(* determine if a structured return type is needed *)
			structuredReturnType := StructuredReturnType(procedureType);

			IF structuredReturnType THEN
				IF resultDesignator  # NIL THEN
					d := resultDesignator;
				ELSE
					variable := GetTemporaryVariable(procedureType.returnType);
					(*
					returnTypeOffset := variable.offsetInBits;
					returnTypeSize := system.SizeOf(procedureType.returnType.resolved);
					reg := fp; IntermediateCode.AddOffset(reg,ToMemoryUnits(system,returnTypeOffset));
					size := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,returnTypeSize));
					*)
					d := SyntaxTree.NewSymbolDesignator(-1,NIL,variable);
					d.SetType(variable.type);
				END;
				IF (procedureType.returnType.resolved IS SyntaxTree.RecordType) THEN
					Designate(d,operand);
					returnTypeSize := system.SizeOf(procedureType.returnType.resolved);
					size := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,returnTypeSize));
			 		Emit(Push(size));
			 		Emit(Push(operand.op));
			 		ReleaseOperand(operand);
				ELSE
					PushParameter(d,procedureType.returnParameter,procedureType.callingConvention, FALSE, dummy)
		 		END;
		 	END;

			firstWriteBackCall := NIL; (* reset write-back call list *)

			IF procedureType.callingConvention # SyntaxTree.OberonCallingConvention THEN
				formalParameter := procedureType.lastParameter;
				FOR i := parameters.Length() - 1 TO 0 BY -1 DO
					actualParameter := parameters.GetExpression(i);
					PrepareParameter(actualParameter, formalParameter);
					PushParameter(actualParameter, formalParameter, procedureType.callingConvention, FALSE, dummy);
					formalParameter := formalParameter.prevParameter;
				END;
			ELSE
				hasDynamicOperands := FALSE; (* nopov *)
				formalParameter := procedureType.firstParameter;
				FOR i := 0 TO parameters.Length() - 1 DO
					actualParameter := parameters.GetExpression(i);

					IF formalParameter # NIL THEN (* TENTATIVE *)
						PrepareParameter(actualParameter, formalParameter);

						(* nopov *)
						IF isCallOfDynamicOperator  & IsStrictlyPointerToRecord(formalParameter.type) & (formalParameter.access # SyntaxTree.Hidden) THEN (* TODO: remove hidden parameters *)
							ASSERT(i < 2);
							hasDynamicOperands := TRUE;
							PushParameter(actualParameter, formalParameter, procedureType.callingConvention, TRUE, parameterBackups[i])
						ELSE
							PushParameter(actualParameter, formalParameter, procedureType.callingConvention, FALSE, dummy)
						END;

						formalParameter := formalParameter.nextParameter;
					END;
				END;
			END;

			IF x.left IS SyntaxTree.SupercallDesignator THEN
				symbol := x.left(SyntaxTree.SupercallDesignator).left(SyntaxTree.SymbolDesignator).symbol;
			ELSIF x.left IS SyntaxTree.IndexDesignator THEN
				symbol := x.left(SyntaxTree.IndexDesignator).left(SyntaxTree.SymbolDesignator).symbol;
			ELSE
				symbol := x.left(SyntaxTree.SymbolDesignator).symbol;
			END;

			(* nopov *)
			IF isCallOfDynamicOperator & hasDynamicOperands THEN
				IF dump # NIL THEN dump.String("++++++++++ dynamic operator call ++++++++++"); dump.Ln; dump.Update END; (* TENTATIVE *)
				(* push ID *)
				(* IF dump # NIL THEN dump.String("push ID"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
				ASSERT(x.left IS SyntaxTree.SymbolDesignator);
				identifierNumber := Global.GetSymbol(module.module.case, x.left(SyntaxTree.SymbolDesignator).symbol.name);
				Emit(Push(IntermediateCode.Immediate(IntermediateCode.GetType(system, system.longintType), identifierNumber)));

				formalParameter := procedureType.firstParameter;
				FOR i := 0 TO parameters.Length() - 1 DO
					IF formalParameter.access # SyntaxTree.Hidden THEN
						ASSERT(i < 2);
						IF IsStrictlyPointerToRecord(formalParameter.type) THEN
							(* push pointer *)
							(* IF dump # NIL THEN dump.String("push pointer"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
							IF formalParameter.kind = SyntaxTree.VarParameter THEN
								(* add dereference *)
								(* IF dump # NIL THEN dump.String("dereference pointer"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
								ReleaseIntermediateOperand(parameterBackups[i]);
								MakeMemory(parameterBackups[i], parameterBackups[i], addressType, 0)
							END;
							Emit(Push(parameterBackups[i]));
							ReleaseIntermediateOperand(parameterBackups[i]);

							(* push typetag *)
							(* IF dump # NIL THEN dump.String("push typetag"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
							recordType := formalParameter.type.resolved(SyntaxTree.PointerType).pointerBase.resolved(SyntaxTree.RecordType);
							arg := TypeDescriptorAdr(recordType);
							IF ~newObjectFile THEN IntermediateCode.MakeMemory(arg, addressType) END;
							Emit(Push(arg));
						ELSE
							(* push 'NonPointer' *)
							(* IF dump # NIL THEN dump.String("push 'NonPointer'"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
							Emit(Push(IntermediateCode.Immediate(IntermediateCode.GetType(system, system.longintType), NonPointer)));

							(* push fingerprint *)
							(* IF dump # NIL THEN dump.String("push fingerprint"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
							fingerPrint := fingerPrinter.TypeFP(formalParameter.type.resolved);
							Emit(Push(IntermediateCode.Immediate(IntermediateCode.GetType(system, system.longintType), fingerPrint.shallow))) (* TODO: push the type's fingerprint *)
						END
					END;
					formalParameter := formalParameter.nextParameter
				END;

				(* for unary operators: complete the information for the second parameter *)
				IF procedureType.numberParameters < 2 THEN
					(* push 'NonPointer' *)
					(* IF dump # NIL THEN dump.String("push 'NonPointer'"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
					Emit(Push(IntermediateCode.Immediate(IntermediateCode.GetType(system, system.longintType), NonPointer)));

					(* push 'NoType' *)
					(* IF dump # NIL THEN dump.String("push 'NoType'"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
					Emit(Push(IntermediateCode.Immediate(IntermediateCode.GetType(system, system.longintType), NoType)));
				END;

				(* call operator selection procedure *)
				IF GetRuntimeProcedure("FoxOperatorRuntime", "SelectOperator", operatorSelectionProcedure, TRUE) THEN
					StaticCallOperand(operatorSelectionProcedureOperand, operatorSelectionProcedure);
					Emit(Call(operatorSelectionProcedureOperand.op, ProcedureParametersSize(system, operatorSelectionProcedure)));
					ReleaseOperand(operatorSelectionProcedureOperand);

					(* use the address that the operator selection procedure returned as the target address of the call *)
					InitOperand(operand, ModeValue);
					operand.op := IntermediateCode.Register(addressType, AcquireRegister(addressType));
					Emit(Result(operand.op))
				END
			ELSE
				Evaluate(x.left, operand)
			END;

			IF symbol IS SyntaxTree.Procedure THEN
				IF (symbol.scope IS SyntaxTree.ProcedureScope) THEN (* nested procedure *)
					GetBaseRegister(reg,currentScope,symbol.scope); (* static link, may be fp or [fp+8] (if nested proc calls itself) *)
					Emit(Push(reg));
					ReleaseIntermediateOperand(reg);
				END;
				IF x.left IS SyntaxTree.SupercallDesignator THEN
					Emit(Push(operand.tag));
				ELSIF (procedureType.isDelegate) THEN
					Emit(Push(operand.tag));
				END;
				parametersSize := ProcedureParametersSize(system,symbol(SyntaxTree.Procedure));
			ELSIF (symbol IS SyntaxTree.Variable) OR (symbol IS SyntaxTree.Parameter) THEN
				IF (procedureType.isDelegate) THEN (* push self pointer only if procedure is a method *)
					noPush := NewLabel();
					BreqL(noPush,operand.tag,nil);
					Emit(Push(operand.tag));
					SetLabel(noPush);
				END;
				parametersSize := ParametersSize(system,procedureType,FALSE);
			ELSE HALT(200);
			END;
			Emit(Call(operand.op,parametersSize));
			IF (procedureType.returnType # NIL) & ~structuredReturnType THEN
				return := NewRegisterOperand(IntermediateCode.GetType(system,procedureType.returnType));
				Emit(Result(return));
			END;
			ReleaseOperand(operand);

			IF procedureType.callingConvention = SyntaxTree.CCallingConvention THEN
				size := IntermediateCode.Immediate(addressType,parametersSize);
				Emit(Add(sp,sp,size));
			END;
			IF (resultDesignator = NIL) & (procedureType.returnType # NIL) THEN
				IF structuredReturnType THEN
					(* stack pointer rewinding done by callee
					size := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOfParameter(procedureType.returnParameter)));
					Emit(Add(sp,sp,size));
					*)
					RestoreRegisters(saved);
					InitOperand(result,ModeReference);
					Symbol(variable,result);
				ELSE
					RestoreRegisters(saved);
					InitOperand(result,ModeValue);
					result.op := return;
				END;
			END;

			IF procedureType.stackAlignment > 1 THEN
				Emit(Pop(sp));
			END;

			IF conditional & (procedureType.returnType # NIL) & (procedureType.returnType.resolved IS SyntaxTree.BooleanType) THEN
				ValueToCondition(result);
			END;
			destination := dest;

			(* perform all write-back calls in the list *)
			BackupGlobalState;
			currentWriteBackCall := firstWriteBackCall;
			WHILE currentWriteBackCall # NIL DO
				VisitProcedureCallDesignator(currentWriteBackCall.call);
				currentWriteBackCall := currentWriteBackCall.next
			END;
			RestoreGlobalState;

			(* nopov *)
			(* TENATIVE *)
			(*
			IF isOperatorCall THEN
				IF dump # NIL THEN dump.String("*** end of operator call ***"); dump.Ln; dump.Update END
			END;
			*)

			IF Trace THEN TraceExit("VisitProcedureCallDesignator") END;
		END VisitProcedureCallDesignator;

		PROCEDURE TypeDescriptorAdr(t: SyntaxTree.Type): IntermediateCode.Operand;
		VAR res: IntermediateCode.Operand; source: Sections.Section; offset: LONGINT;

			td: SyntaxTree.TypeDeclaration;

			PROCEDURE GetHiddenPointerType(): SyntaxTree.Type;
			VAR scope: SyntaxTree.RecordScope; variable: SyntaxTree.Variable; typeDeclaration: SyntaxTree.TypeDeclaration;
			BEGIN
				IF (hiddenPointerType = NIL) OR (hiddenPointerType.typeDeclaration.scope.ownerModule # module.module) THEN
					scope := SyntaxTree.NewRecordScope(module.module.moduleScope);
					variable := SyntaxTree.NewVariable(-1,SyntaxTree.NewIdentifier("@Any"));
					variable.SetType(system.anyType);
					scope.AddVariable(variable);
					hiddenPointerType := SyntaxTree.NewRecordType(-1,NIL,scope);
					typeDeclaration := SyntaxTree.NewTypeDeclaration(-1,SyntaxTree.NewIdentifier("@HdPtrDesc"));
					typeDeclaration.SetDeclaredType(hiddenPointerType);
					typeDeclaration.SetScope(module.module.moduleScope);
					hiddenPointerType.SetTypeDeclaration(typeDeclaration);
					hiddenPointerType.SetState(SyntaxTree.Resolved);
				END;
				RETURN hiddenPointerType;
			END GetHiddenPointerType;

			PROCEDURE GetDelegateType(): SyntaxTree.Type;
			VAR scope: SyntaxTree.RecordScope; variable: SyntaxTree.Variable; typeDeclaration: SyntaxTree.TypeDeclaration;
			BEGIN
				IF (delegatePointerType = NIL) OR (delegatePointerType.typeDeclaration.scope.ownerModule # module.module) THEN
					scope := SyntaxTree.NewRecordScope(module.module.moduleScope);
					variable := SyntaxTree.NewVariable(-1,SyntaxTree.NewIdentifier("@Procedure"));
					variable.SetType(SyntaxTree.NewProcedureType(-1,NIL));
					scope.AddVariable(variable);
					variable := SyntaxTree.NewVariable(-1,SyntaxTree.NewIdentifier("@Any"));
					variable.SetType(system.anyType);
					scope.AddVariable(variable);
					delegatePointerType := SyntaxTree.NewRecordType(-1,NIL,scope);
					typeDeclaration := SyntaxTree.NewTypeDeclaration(-1,SyntaxTree.NewIdentifier("@Delegate"));
					typeDeclaration.SetDeclaredType(delegatePointerType);
					typeDeclaration.SetScope(module.module.moduleScope);
					delegatePointerType.SetTypeDeclaration(typeDeclaration);
					delegatePointerType.SetState(SyntaxTree.Resolved);
				END;
				RETURN delegatePointerType
			END GetDelegateType;


			PROCEDURE GetBackendType(x: SyntaxTree.Type; VAR offset: LONGINT): Sections.Section;
			(* create anonymous type declaration for types that need a type descriptor but have been declared anonymously
				such as in VAR a: RECORD ... END;
				reason: type desciptors in Sections are then accessible via a type declaration symbol and for types
				and variables, constants and procedures the same mechanism can be used for fixups etc.
			*)
			VAR  source: Sections.Section;null: HUGEINT; td: SyntaxTree.TypeDeclaration;
				name: Basic.PooledName; op: IntermediateCode.Operand;
			BEGIN (* no code emission *)
				source := NIL;
				x := x.resolved;
				IF (x IS SyntaxTree.AnyType) OR (x IS SyntaxTree.PointerType) THEN
					x := GetHiddenPointerType();
				ELSIF IsDelegate(x) THEN
					x := GetDelegateType();
				ELSIF (x IS SyntaxTree.RecordType) (* OR (x IS SyntaxTree.PointerType) *) THEN
				ELSE HALT(200);
				END;

				td := x.typeDeclaration;
				IF td = NIL THEN
					ASSERT(x(SyntaxTree.RecordType).pointerType # NIL);
					td := x(SyntaxTree.RecordType).pointerType.resolved.typeDeclaration;
					ASSERT(td # NIL);
				END;

				IF newObjectFile THEN
					Global.GetSymbolPooledName(td,name);
					IF (td.scope = NIL) OR (td.scope.ownerModule = module.module) THEN
						CheckTypeDeclaration(SELF, module,x,commentPrintout # NIL, newObjectFile);
						source := NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,td,commentPrintout # NIL);
					ELSE
						IF currentCellScope # NIL THEN
							currentCellScope.AddImport(td.scope.ownerModule);
						END;

						source := NewSection(module.allSections, Sections.ImportedSymbolKind,Sections.ConstSection, FALSE, name,td,commentPrintout # NIL);
					END;
					offset := ToMemoryUnits(system,(1+x(SyntaxTree.RecordType).recordScope.numberMethods+16+1)*system.addressSize);
				ELSE
					source := module.allSections.FindBySymbolAndKind(td, Sections.RegularKind); (*TODO*)
					IF source = NIL THEN
						null := 0;
						Global.GetSymbolPooledName(td,name);
						source := NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,td,commentPrintout # NIL);
						IntermediateCode.InitImmediate(op,addressType,0);
						source(IntermediateCode.Section).Emit(Data(op));
						source.SetReferenced(FALSE)
					ELSE
						ASSERT(source.kind = Sections.RegularKind)
					END;
				END;

				RETURN source;
			END GetBackendType;

		BEGIN
			td := t.typeDeclaration;
			source := GetBackendType(t,offset); (*! do not dereference a pointer here as the type descriptor for the pointer might be asked for *)
			(*
			IF t IS SyntaxTree.PointerType THEN
				source := GetBackendType(t(SyntaxTree.PointerType).pointerBase.resolved);
			ELSE
				source := GetBackendType(t);
			END;
			*)
			ASSERT(source # NIL);
			IF newObjectFile THEN
				IntermediateCode.InitAddress(res, addressType, source, 0 (*
				1+t(SyntaxTree.RecordType).recordScope.numberMethods+16+1 *));
				IntermediateCode.SetOffset(res,offset);
			ELSE
				IntermediateCode.InitAddress(res, addressType, source,0);
			END;
			(*
			IntermediateCode.MakeMemory(res,IntermediateCode.UnsignedInteger,addressType.sizeInBits);
			make memory should be used when tag is used, not earlier
			*)


			RETURN res
		END TypeDescriptorAdr;

		(*
		PROCEDURE MakeTypeTag(VAR operand: Operand);
		VAR result: IntermediateCode.Operand;
		BEGIN
			IF operand.tag.mode = IntermediateCode.Undefined THEN
				operand.tag := TypeDescriptorAdr(operand.type);
				IntermediateCode.MakeMemory(operand.tag,addressType);
				UseIntermediateOperand(operand.tag);
			END;
		END MakeTypeTag;
		*)

		PROCEDURE ProfilerInit;
		VAR reg: IntermediateCode.Operand;
		BEGIN
			IntermediateCode.InitAddress(reg, addressType, profileInit , 0);
			Emit(Call(reg,0));
		END ProfilerInit;

		PROCEDURE ProfilerEnterExit(procedureNumber: LONGINT; enter: BOOLEAN);
		VAR reg: IntermediateCode.Operand; result: Operand; procedure: SyntaxTree.Procedure;
		BEGIN
			IF enter & GetRuntimeProcedure("FoxProfiler","EnterProcedure",procedure,TRUE)
			OR ~enter & GetRuntimeProcedure("FoxProfiler","ExitProcedure",procedure,TRUE)
			THEN
				IntermediateCode.InitAddress(reg, addressType, profileId , 0);
				IntermediateCode.MakeMemory(reg, IntermediateCode.GetType(system,system.longintType));
				Emit(Push(reg));
				IntermediateCode.InitImmediate(reg, IntermediateCode.GetType(system,system.longintType), procedureNumber);
				Emit(Push(reg));
				StaticCallOperand(result,procedure);
				Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
				ReleaseOperand(result);
			END;
		END ProfilerEnterExit;

		PROCEDURE ProfilerAddProcedure(procedureNumber: LONGINT; CONST name: ARRAY OF CHAR);
		VAR reg: IntermediateCode.Operand; result: Operand; procedure: SyntaxTree.Procedure; sv: SyntaxTree.StringValue;type: SyntaxTree.Type;
		BEGIN
			IF GetRuntimeProcedure("FoxProfiler","AddProcedure",procedure,TRUE) THEN
				IntermediateCode.InitAddress(reg, addressType, profileId , 0);
				IntermediateCode.MakeMemory(reg, IntermediateCode.GetType(system,system.longintType));
				profileInit.Emit(Push(reg));
				IntermediateCode.InitImmediate(reg, IntermediateCode.GetType(system,system.longintType), procedureNumber);
				profileInit.Emit(Push(reg));
				sv := SyntaxTree.NewStringValue(-1,name);
				type := SyntaxTree.NewStringType(-1,system.characterType,Strings.Length(name));
				sv.SetType(type);
				Designate(sv,result);
				profileInit.Emit(Push(result.tag));
				profileInit.Emit(Push(result.op));
				StaticCallOperand(result,procedure);
				profileInit.Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
				ReleaseOperand(result);
			END;
		END ProfilerAddProcedure;

		PROCEDURE ProfilerAddModule(CONST name: ARRAY OF CHAR);
		VAR sv: SyntaxTree.StringValue; type: SyntaxTree.Type; result: Operand;  reg: IntermediateCode.Operand; procedure: SyntaxTree.Procedure;
		BEGIN
			IF GetRuntimeProcedure("FoxProfiler","AddModule",procedure,TRUE) THEN
				IntermediateCode.InitAddress(reg, addressType, profileId , 0);
				profileInit.Emit(Push(reg));
				profileInitPatchPosition := profileInit.pc;
				profileInit.Emit(Nop()); (* placeholder, will be patched by number of procedures *)
				sv := SyntaxTree.NewStringValue(-1,name);
				type := SyntaxTree.NewStringType(-1,system.characterType,Strings.Length(name));
				sv.SetType(type);
				Designate(sv,result);
				profileInit.Emit(Push(result.tag));
				profileInit.Emit(Push(result.op));
				StaticCallOperand(result,procedure);
				profileInit.Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
				ReleaseOperand(result);
			END;
		END ProfilerAddModule;

		PROCEDURE ProfilerPatchInit;
		VAR reg: IntermediateCode.Operand;
		BEGIN
			IntermediateCode.InitImmediate(reg, IntermediateCode.GetType(system,system.longintType), numberProcedures);
			profileInit.EmitAt(profileInitPatchPosition,Push(reg));
			profileInit.Emit(Leave(0));
			profileInit.Emit(Exit(0));
		END ProfilerPatchInit;

		(* nopov *)
		(** if operator can be overloaded dynamically, emit code that registers it in the runtime **)
		PROCEDURE RegisterDynamicOperator(operator: SyntaxTree.Operator);
		VAR
			id: LONGINT;
			leftType, rightType: SyntaxTree.Type;
			procedureType: SyntaxTree.ProcedureType;
			runtimeProcedure: SyntaxTree.Procedure;
			runtimeProcedureOperand, operatorOperand: Operand;
			kind: SET;

			PROCEDURE PushTypeInfo(type: SyntaxTree.Type);
			VAR
				arg: IntermediateCode.Operand;
				recordType: SyntaxTree.RecordType;
				fingerPrint: SyntaxTree.FingerPrint;
			BEGIN
				IF type = NIL THEN
					(* no type: push 'NoType' *)
					(* IF dump # NIL THEN dump.String("push 'NoType'"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
					arg := IntermediateCode.Immediate(IntermediateCode.GetType(system, system.longintType), NoType)
				ELSIF IsStrictlyPointerToRecord(type) THEN
					(* pointer to record type: push typetag *)
					(* IF dump # NIL THEN dump.String("push typetag"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
					recordType := type.resolved(SyntaxTree.PointerType).pointerBase.resolved(SyntaxTree.RecordType);
					arg := TypeDescriptorAdr(recordType);
					IF ~newObjectFile THEN IntermediateCode.MakeMemory(arg, addressType) END;
				ELSE
					(* non-pointer to record type: push fingerprint *)
					(* IF dump # NIL THEN dump.String("push fingerprint"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
					fingerPrint := fingerPrinter.TypeFP(type.resolved);
					arg := IntermediateCode.Immediate(IntermediateCode.GetType(system, system.longintType), fingerPrint.shallow)
				END;
				operatorInitializationCodeSection.Emit(Push(arg))
			END PushTypeInfo;
		BEGIN
			ASSERT(operatorInitializationCodeSection # NIL);

			ASSERT(operator.type IS SyntaxTree.ProcedureType);
			procedureType := operator.type(SyntaxTree.ProcedureType);

			(* determine types *)
			leftType := procedureType.firstParameter.type;
			IF procedureType.numberParameters = 2 THEN
				ASSERT(procedureType.firstParameter.nextParameter # NIL);
				rightType := procedureType.firstParameter.nextParameter.type;
			ELSE
				rightType := NIL
			END;


			(* determine operator kind *)
			IF IsStrictlyPointerToRecord(leftType) THEN
				kind := {LhsIsPointer}
			ELSE
				kind := {}
			END;
			IF IsStrictlyPointerToRecord(rightType) THEN
				kind := kind + {RhsIsPointer}
			END;

			IF kind # {} THEN (* TODO: to be removed later on *)
				(* at least one of the types is a pointer to record *)

				(* emit a code that registers this specific operator in the runtime *)
				dump := operatorInitializationCodeSection.comments;

				(* IF dump # NIL THEN dump.String("*** begin of operator registration ***"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
				IF GetRuntimeProcedure("FoxOperatorRuntime", "RegisterOperator", runtimeProcedure, TRUE) THEN
					(* push ID *)
					(* IF dump # NIL THEN dump.String("push ID"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
					id := Global.GetSymbol(module.module.case, operator.name);
					operatorInitializationCodeSection.Emit(Push(IntermediateCode.Immediate(IntermediateCode.GetType(system, system.longintType), id)));

					(* push kind *)
					(* IF dump # NIL THEN dump.String("push kind"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
					operatorInitializationCodeSection.Emit(Push(IntermediateCode.Immediate(setType, SYSTEM.VAL(LONGINT, kind))));

					(* push type infos *)
					PushTypeInfo(leftType);
					PushTypeInfo(rightType);

					(* push operator address *)
					(* IF dump # NIL THEN dump.String("push operator address"); dump.Ln; dump.Update END; *) (* TENTATIVE *)
					StaticCallOperand(operatorOperand, operator);
					operatorInitializationCodeSection.Emit(Push(operatorOperand.op));
					ReleaseOperand(operatorOperand);

					StaticCallOperand(runtimeProcedureOperand, runtimeProcedure);
					operatorInitializationCodeSection.Emit(Call(runtimeProcedureOperand.op, ProcedureParametersSize(system, runtimeProcedure)));
					ReleaseOperand(runtimeProcedureOperand)
				END
				(* IF dump # NIL THEN dump.String("*** end of operator registration ***"); dump.Ln; dump.Update END *) (* TENTATIVE *)
			END
		END RegisterDynamicOperator;

		PROCEDURE SystemTrace(x: SyntaxTree.ExpressionList);
		VAR
			traceModule: SyntaxTree.Module;
			procedure: SyntaxTree.Procedure;
			s,msg: Scanner.StringType;
			res: Operand;
			i: LONGINT;
			sv: SyntaxTree.StringValue;
			type: SyntaxTree.Type;
			recordType: SyntaxTree.RecordType;
			printout: Printout.Printer;
			stringWriter: Streams.StringWriter;
			expression: SyntaxTree.Expression;

			PROCEDURE GetProcedure(CONST procedureName: ARRAY OF CHAR): BOOLEAN;
			BEGIN
				procedure := traceModule.moduleScope.FindProcedure(SyntaxTree.NewIdentifier(procedureName));
				IF procedure = NIL THEN
					s := "procedure ";
					Strings.Append(s,backend.traceModuleName);
					Strings.Append(s,".");
					Strings.Append(s,procedureName);
					Strings.Append(s," not present");
					Error(position,s);
					RETURN FALSE
				ELSE
					RETURN TRUE
				END;
			END GetProcedure;

			PROCEDURE CallProcedure;
			BEGIN
				StaticCallOperand(result,procedure);
				Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
			END CallProcedure;

			PROCEDURE String(CONST s: ARRAY OF CHAR);
			BEGIN
				IF GetProcedure("String") THEN
					sv := SyntaxTree.NewStringValue(-1,s);
					type := SyntaxTree.NewStringType(-1,system.characterType,Strings.Length(s));
					sv.SetType(type);
					Designate(sv,res);
					Emit(Push(res.tag));
					Emit(Push(res.op));
					CallProcedure;
				END;
			END String;

			PROCEDURE Integer(op: IntermediateCode.Operand);
			BEGIN
				IF GetProcedure("Int") THEN
					Emit(Push(op));
					Emit(Push(IntermediateCode.Immediate(int32,1)));
					CallProcedure;
				END;
			END Integer;

			PROCEDURE Hex64(op: IntermediateCode.Operand);
			BEGIN
				IF GetProcedure("HIntHex") THEN
					Emit(Push(op));
					Emit(Push(IntermediateCode.Immediate(int32,16)));
					CallProcedure;
				END;
			END Hex64;

			PROCEDURE Float(op: IntermediateCode.Operand);
			BEGIN
				IF GetProcedure("HIntHex") THEN
					Emit(Push(op));
					Emit(Push(IntermediateCode.Immediate(int32,16)));
					CallProcedure;
				END;
			END Float;

			PROCEDURE Set(op: IntermediateCode.Operand);
			BEGIN
				IF GetProcedure("Bits") THEN
					Emit(Push(op));
					Emit(Push(IntermediateCode.Immediate(int32,0))); (* ofs *)
					Emit(Push(IntermediateCode.Immediate(int32,32))); (* n *)
					CallProcedure;
				END;
			END Set;

			PROCEDURE Boolean(op: IntermediateCode.Operand);
			BEGIN
				IF GetProcedure("Boolean") THEN
					Emit(Push(op));
					CallProcedure;
				END;
			END Boolean;

			PROCEDURE Char(op: IntermediateCode.Operand);
			BEGIN
				IF GetProcedure("Char") THEN
					Emit(Push(op));
					CallProcedure;
				END;
			END Char;

			PROCEDURE Address(op: IntermediateCode.Operand);
			BEGIN
				IF GetProcedure("Address") THEN
					Emit(Push(op));
					CallProcedure;
				END;
			END Address;

			PROCEDURE StringOperand(op,tag: IntermediateCode.Operand);
			BEGIN
				IF GetProcedure("String") THEN
					Emit(Push(tag));
					Emit(Push(op));
					CallProcedure;
				END;
			END StringOperand;


			PROCEDURE Ln;
			BEGIN
				IF GetProcedure("Ln") THEN
					CallProcedure;
				END;
			END Ln;


		BEGIN
			IF AddImport(backend.traceModuleName,traceModule,TRUE) THEN
				NEW(stringWriter,LEN(s));
				FOR i := 0 TO x.Length()-1 DO
					msg := "";
					expression := x.GetExpression(i);
					Global.GetModuleName(module.module, s);
					stringWriter.String(s); stringWriter.String("@"); stringWriter.Int(expression.position,1);
					stringWriter.String(":");

					printout := Printout.NewPrinter(stringWriter,Printout.SourceCode,FALSE);
					IF ~(expression IS SyntaxTree.StringValue) THEN
						printout.Expression(expression);
						stringWriter.Get(s);
						Strings.Append(msg,s);
						Strings.Append(msg,"= ");
					ELSE stringWriter.Get(s); (* remove from string writer *)
					END;
					String(msg);
					IF SemanticChecker.IsStringType(expression.type) THEN
						Designate(expression,res);
						StringOperand(res.op,res.tag);
					ELSE
						Evaluate(expression,res);
						IF expression.type.resolved IS SyntaxTree.IntegerType THEN
							IF res.op.type.sizeInBits = IntermediateCode.Bits64 THEN
								Hex64(res.op); String("H");
							ELSE
								IF res.op.type.sizeInBits < IntermediateCode.Bits32 THEN
									Convert(res.op,int32);
								END;
								Integer(res.op);
							END;
						ELSIF expression.type.resolved IS SyntaxTree.BooleanType THEN
							Boolean(res.op);
						ELSIF expression.type.resolved IS SyntaxTree.SetType THEN
							Set(res.op);
						ELSIF expression.type.resolved IS SyntaxTree.FloatType THEN
							IF res.op.type.sizeInBits = IntermediateCode.Bits32 THEN
								Convert(res.op,float64);
							END;
							Float(res.op);
						ELSIF expression.type.resolved = Global.Character8 THEN
							Char(res.op);
						ELSIF expression.type.resolved = system.addressType THEN
							Address(res.op);String("H");
						ELSIF (expression.type.resolved IS SyntaxTree.PointerType) OR IsPointerToRecord(expression.type,recordType) THEN
							Address(res.op);String("H");
						ELSE HALT(200);
						END;
					END;
					ReleaseOperand(res);
					String("; ");
				END;
				Ln;
			END;
		END SystemTrace;

		PROCEDURE InitFields(type: SyntaxTree.Type; CONST adr: IntermediateCode.Operand; offset: LONGINT);
		VAR baseType: SyntaxTree.Type; imm: IntermediateCode.Operand; dim,size: LONGINT;
			variable: SyntaxTree.Variable; i: LONGINT;
		BEGIN
			type := type.resolved;
			IF type IS SyntaxTree.RecordType THEN
				WITH type: SyntaxTree.RecordType DO
					baseType := type.baseType;
					IF baseType # NIL THEN
						baseType := baseType.resolved;
						IF baseType IS SyntaxTree.PointerType THEN baseType := baseType(SyntaxTree.PointerType).pointerBase END;
						InitFields(baseType,adr,offset);
					END;
					variable := type.recordScope.firstVariable;
					WHILE variable # NIL DO
						InitFields(variable.type, adr, offset+ ToMemoryUnits(system,variable.offsetInBits));
						variable := variable.nextVariable
					END;
				END;
			ELSIF (type IS SyntaxTree.ArrayType) THEN
				WITH type: SyntaxTree.ArrayType DO
					IF type.form = SyntaxTree.Static THEN
						baseType := type.arrayBase;
						size := ToMemoryUnits(system,system.SizeOf(baseType));
						FOR i := 0 TO type.staticLength-1 DO
							InitFields(baseType,adr,offset+i*size);
						END;
					END;
				END;
			ELSIF type IS SyntaxTree.MathArrayType THEN
				WITH type: SyntaxTree.MathArrayType DO
					IF type.form = SyntaxTree.Open THEN
						dim := DynamicDim(type);
						imm := IntermediateCode.Immediate(addressType,dim);
						PutMathArrayFieldOffset(adr,imm,MathDimOffset,offset);
						baseType := SemanticChecker.ArrayBase(type,dim);
						IF baseType = NIL THEN size := 0 ELSE size := system.SizeOf(baseType) END;
						imm := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,size));
						PutMathArrayFieldOffset(adr,imm,MathElementSizeOffset,offset);
						ReleaseIntermediateOperand(imm);
						(* flags remain empty (=0) for open array *)
					ELSIF type.form = SyntaxTree.Static THEN
						baseType := type.arrayBase;
						size := ToMemoryUnits(system,system.SizeOf(baseType));
						FOR i := 0 TO type.staticLength-1 DO
							InitFields(baseType,adr,offset+i*size);
						END;
					END;
				END;
			END;
		END InitFields;

		PROCEDURE InitVariable(VAR variable: SyntaxTree.Variable);
		VAR type: SyntaxTree.Type; operand: Operand;
		BEGIN
			type := variable.type.resolved;
			IF (type IS SyntaxTree.MathArrayType) THEN
				WITH type: SyntaxTree.MathArrayType DO
					IF type.form = SyntaxTree.Open THEN
						Symbol(variable,operand);
						InitFields(type, operand.tag,0);
					END;
				END;
			ELSE
				Symbol(variable,operand);
				InitFields(type, operand.op,0);
				ReleaseOperand(operand);
			END;
		END InitVariable;

		PROCEDURE MathArrayDim(type: SyntaxTree.MathArrayType; CONST base: IntermediateCode.Operand; VAR result: Operand);
		VAR end: Label;
		BEGIN
			IF type.form = SyntaxTree.Tensor THEN
				InitOperand(result,ModeValue);
				ReuseCopy(result.op,base);
				end := NewLabel();
				BreqL(end,result.op,IntermediateCode.Immediate(addressType,0));
				Emit(MovReplace(result.op,IntermediateCode.Memory(addressType,result.op,ToMemoryUnits(system,MathDimOffset*addressType.sizeInBits))));
				SetLabel(end);
				Convert(result.op,int32);
			ELSE
				InitOperand(result,ModeValue);
				IntermediateCode.InitImmediate(result.op, int32, SemanticChecker.Dimension(type,{SyntaxTree.Open, SyntaxTree.Static}));
			END
		END MathArrayDim;

		PROCEDURE PutMathArrayField(base,value: IntermediateCode.Operand; fieldOffset: LONGINT);
		VAR mem: IntermediateCode.Operand; offset: LONGINT;
		BEGIN
			offset := ToMemoryUnits(system,fieldOffset*addressType.sizeInBits);
			MakeMemory(mem,base,addressType,offset);
			Emit(Mov(mem,value));
			ReleaseIntermediateOperand(mem);
		END PutMathArrayField;

		PROCEDURE PutMathArrayFieldOffset(base,value: IntermediateCode.Operand; fieldOffset, offset: LONGINT);
		VAR mem: IntermediateCode.Operand;
		BEGIN
			offset := offset + ToMemoryUnits(system,fieldOffset*addressType.sizeInBits);
			MakeMemory(mem,base,addressType,offset);
			Emit(Mov(mem,value));
			ReleaseIntermediateOperand(mem);
		END PutMathArrayFieldOffset;

		PROCEDURE GetMathArrayField(VAR value: IntermediateCode.Operand; base: IntermediateCode.Operand; offset: LONGINT);
		BEGIN
			offset := ToMemoryUnits(system,offset*addressType.sizeInBits);
			MakeMemory(value,base,addressType,offset);
		END GetMathArrayField;

		PROCEDURE PutMathArrayLenOrIncr(CONST base,value,dim: IntermediateCode.Operand; incr: BOOLEAN);
		VAR offset: LONGINT; reg,mem: IntermediateCode.Operand;
		BEGIN
			IF incr THEN
				offset := ToMemoryUnits(system,MathIncrOffset*addressType.sizeInBits);
			ELSE
				offset := ToMemoryUnits(system,MathLenOffset*addressType.sizeInBits);
			END;
			IF dim.mode=IntermediateCode.ModeImmediate THEN
				PutMathArrayField(base,value,offset + ToMemoryUnits(system,SHORT(dim.intValue) * 2 * addressType.sizeInBits));
			ELSE
				IntermediateCode.InitRegister(reg,addressType,AcquireRegister(addressType));
				Emit(Mov(reg,dim));
				Emit(Mul(reg,reg,IntermediateCode.Immediate(addressType,ToMemoryUnits(system,2*addressType.sizeInBits))));
				Emit(Add(reg,reg,base));
				MakeMemory(mem,reg,addressType,offset);
				ReleaseIntermediateOperand(reg);
				Emit(Mov(mem,value));
				ReleaseIntermediateOperand(mem);
			END;
		END PutMathArrayLenOrIncr;

		PROCEDURE PutMathArrayLength(base,value: IntermediateCode.Operand; dim: LONGINT);
		BEGIN
			PutMathArrayField(base,value,MathLenOffset + dim * 2);
		END PutMathArrayLength;

		PROCEDURE PutMathArrayIncrement(base,value: IntermediateCode.Operand; dim: LONGINT);
		BEGIN
			PutMathArrayField(base,value,MathIncrOffset + dim * 2);
		END PutMathArrayIncrement;

		PROCEDURE GetMathArrayIncrement(type: SyntaxTree.MathArrayType; CONST operand: Operand; VAR dim: IntermediateCode.Operand; check: BOOLEAN; VAR result: Operand);
		BEGIN
			MathArrayLenOrIncr(type,operand,dim,TRUE,check,result);
		END GetMathArrayIncrement;

		PROCEDURE GetMathArrayLength(type: SyntaxTree.MathArrayType; CONST operand: Operand; VAR dim: IntermediateCode.Operand; check: BOOLEAN; VAR result: Operand);
		BEGIN
			MathArrayLenOrIncr(type,operand,dim,FALSE,check,result);
		END GetMathArrayLength;

		PROCEDURE MathArrayLenOrIncr(type: SyntaxTree.MathArrayType; CONST operand: Operand; VAR dim: IntermediateCode.Operand; increment: BOOLEAN; check: BOOLEAN; VAR result: Operand );
		VAR val: LONGINT; res,res2: IntermediateCode.Operand; end,next: Label; t: SyntaxTree.Type; imm: IntermediateCode.Operand; hasDynamicPart: BOOLEAN;
			offset: LONGINT;
		BEGIN
			IF increment THEN
				offset := MathIncrOffset;
			ELSE
				offset := MathLenOffset;
			END;
			INC(offset,operand.dimOffset*2);
			IF check & (type.form = SyntaxTree.Tensor) &  ~backend.noRuntimeChecks THEN
				TrapC(BrneL,operand.tag,IntermediateCode.Immediate(addressType,0),IndexCheckTrap);
			END;
			IF  dim.mode = IntermediateCode.ModeImmediate THEN
				IF check & (type.form = SyntaxTree.Tensor) THEN
					DimensionCheck(operand.tag,dim,BrltL);
				END;
				val := SHORT(dim.intValue);
				IF type.form # SyntaxTree.Tensor THEN
					t := SemanticChecker.ArrayBase(type,val);
					type := t.resolved(SyntaxTree.MathArrayType);
					IF type.form = SyntaxTree.Static THEN
						IF increment THEN
							res := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,type.staticIncrementInBits));
						ELSE
							res := IntermediateCode.Immediate(addressType,type.staticLength);
						END;
						InitOperand(result,ModeValue);
						result.op := res;
						RETURN;
					END;
				END;
				offset := ToMemoryUnits(system, (val*2+offset)*addressType.sizeInBits);
				MakeMemory(res,operand.tag,addressType,offset);
				(*
				res := IntermediateCode.Memory(addressType,operand.tag,offset);
				*)
				InitOperand(result,ModeValue);
				result.op := res;
			ELSE
				Convert(dim,addressType);
				IF check THEN
					IF type.form = SyntaxTree.Tensor THEN
						DimensionCheck(operand.tag,dim,BrltL);
					ELSIF backend.noRuntimeChecks THEN (* do nothing *)
					ELSE
						TrapC(BrltL,dim,IntermediateCode.Immediate(addressType,SemanticChecker.Dimension(type,{SyntaxTree.Open,SyntaxTree.Static})), IndexCheckTrap);
					END;
				END;
				end := NewLabel(); next := NIL;

				IntermediateCode.InitRegister(res,addressType,AcquireRegister(addressType));
				Emit(Mov(res,dim));
				Convert(res,int32);

				t := type; val := operand.dimOffset; hasDynamicPart := FALSE;
				WHILE t IS SyntaxTree.MathArrayType DO
					type := t(SyntaxTree.MathArrayType);
					IF type.form = SyntaxTree.Static THEN
						imm := IntermediateCode.Immediate(int32,val);
						next := NewLabel();
						BrneL(next,imm,res);
						IF increment THEN
							imm := IntermediateCode.Immediate(int32,ToMemoryUnits(system,type.staticIncrementInBits));
						ELSE
							imm := IntermediateCode.Immediate(int32,type.staticLength);
						END;
						Emit(MovReplace(res,imm));
						BrL(end);
					ELSE hasDynamicPart := TRUE;
					END;
					t := type.arrayBase.resolved;
					val := val + 1;
					IF next # NIL THEN SetLabel(next) END;
				END;
				IF hasDynamicPart THEN
					IntermediateCode.InitRegister(res2,addressType,AcquireRegister(addressType));
					Emit(Mov(res2,dim));
					Emit(Mul(res2,res2,IntermediateCode.Immediate(addressType,2*ToMemoryUnits(system,addressType.sizeInBits))));
					imm := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,offset*addressType.sizeInBits));
					Emit(Add(res2,res2,imm));
					Emit(Add(res2,res2,operand.tag));
					IntermediateCode.MakeMemory(res2,int32);
					Emit(MovReplace(res,res2));
					ReleaseIntermediateOperand(res2);
				END;
				SetLabel(end);
				Convert(res,int32);
				InitOperand(result,ModeValue);
				result.op := res;
			END;
		END MathArrayLenOrIncr;



		PROCEDURE ArrayLen(type: SyntaxTree.ArrayType; VAR operand: Operand; VAR dim: IntermediateCode.Operand; VAR result: Operand );
		VAR val: LONGINT; res,res2: IntermediateCode.Operand; end,next: Label; t: SyntaxTree.Type; imm: IntermediateCode.Operand; hasDynamicPart: BOOLEAN;
			offset: LONGINT;
		BEGIN
			offset := operand.dimOffset+DynamicDim(type)-1;
			IF  dim.mode = IntermediateCode.ModeImmediate THEN
				ASSERT(type.form IN {SyntaxTree.Open});
				val := SHORT(dim.intValue);
				t := SemanticChecker.ArrayBase(type,val);
				type := t.resolved(SyntaxTree.ArrayType);
				IF type.form = SyntaxTree.Static THEN
					res := IntermediateCode.Immediate(addressType,type.staticLength);
				ELSE
					offset := ToMemoryUnits(system, (offset-val)*addressType.sizeInBits);
					res := IntermediateCode.Memory(addressType,operand.tag,offset);
				END;
				UseIntermediateOperand(res);
				InitOperand(result,ModeValue);
				result.op := res;
			ELSE
				Convert(dim,addressType);
				IF ~backend.noRuntimeChecks THEN
					TrapC(BrltL,dim,IntermediateCode.Immediate(addressType,SemanticChecker.Dimension(type,{SyntaxTree.Open,SyntaxTree.Static})), IndexCheckTrap);
				END;

				end := NewLabel(); next := NIL;

				(* ReuseCopy(dim,res); *)
				IntermediateCode.InitRegister(res,addressType,AcquireRegister(addressType));
				Emit(Mov(res,dim));
				Convert(res,int32);

				Convert(res,int32);
				t := type; val := operand.dimOffset; hasDynamicPart := FALSE;
				WHILE t IS SyntaxTree.ArrayType DO
					type := t(SyntaxTree.ArrayType);
					IF type.form = SyntaxTree.Static THEN
						imm := IntermediateCode.Immediate(int32,val);
						next := NewLabel();
						BrneL(next,imm,res);
						imm := IntermediateCode.Immediate(int32,type.staticLength);
						Emit(MovReplace(res,imm));
						BrL(end);
					ELSE hasDynamicPart := TRUE;
					END;
					t := type.arrayBase.resolved;
					val := val + 1;
					IF next # NIL THEN SetLabel(next) END;
				END;
				IF hasDynamicPart THEN
					ReuseCopy(res2,dim); (* dim is now in register res2 *)
					Convert(res2,addressType);
					Emit(Mul(res2,res2,IntermediateCode.Immediate(addressType,ToMemoryUnits(system,addressType.sizeInBits))));
					imm := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,offset*addressType.sizeInBits));
					Emit(Sub(res2,imm,res2));
					Emit(Add(res2,res2,operand.tag));
					IntermediateCode.MakeMemory(res2,int32);
					Emit(MovReplace(res,res2));
					ReleaseIntermediateOperand(res2);
				END;
				SetLabel(end);
				Convert(res,int32);
				InitOperand(result,ModeValue);
				result.op := res;
			END;
		END ArrayLen;

		(**
			create a temporary variable in current scope
		**)
		PROCEDURE GetTemporaryVariable(type: SyntaxTree.Type): SyntaxTree.Variable;
		VAR name: SyntaxTree.Identifier; string: Scanner.StringType ; variable: SyntaxTree.Symbol;
		scope: SyntaxTree.Scope; duplicate: BOOLEAN; offset: LONGINT;
		BEGIN
			COPY("@hiddenIRVar",string);
			Basic.AppendNumber(string,GetIndex());
			name := SyntaxTree.NewIdentifier(string);
			scope := currentScope;
			variable := currentScope.FindVariable(name);
			IF variable = NIL THEN
				variable := SyntaxTree.NewVariable(Diagnostics.Invalid,name);
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

				InitVariable(variable(SyntaxTree.Variable));
			ELSE
				ASSERT(variable.type.resolved = type.resolved)
			END;
			RETURN variable(SyntaxTree.Variable)
		END GetTemporaryVariable;

		PROCEDURE GetMathArrayDescriptorType(dimensions: LONGINT): SyntaxTree.Type;
		VAR name: ARRAY 32 OF CHAR; symbol: SyntaxTree.Symbol; typeDeclaration: SyntaxTree.TypeDeclaration;
			recordType: SyntaxTree.RecordType; type: SyntaxTree.Type;
			recordScope: SyntaxTree.RecordScope; parentScope: SyntaxTree.Scope; identifier: SyntaxTree.Identifier;
			i: LONGINT; duplicate: BOOLEAN;

			PROCEDURE AddVariable(CONST name: ARRAY OF CHAR; type: SyntaxTree.Type);
			VAR variable: SyntaxTree.Variable;
			BEGIN
				variable := SyntaxTree.NewVariable(-1,SyntaxTree.NewIdentifier(name));
				variable.SetType(type);
				recordScope.AddVariable(variable);
			END AddVariable;


		BEGIN
			name := "@ArrayDescriptor";
			Basic.AppendNumber(name,dimensions);
			identifier := SyntaxTree.NewIdentifier(name);
			parentScope := module.module.moduleScope;
			symbol := parentScope.FindSymbol(identifier);
			IF symbol # NIL THEN
				typeDeclaration := symbol(SyntaxTree.TypeDeclaration);
				type := typeDeclaration.declaredType;
			ELSE
				typeDeclaration := SyntaxTree.NewTypeDeclaration(-1,SyntaxTree.NewIdentifier(name));
				recordScope := SyntaxTree.NewRecordScope(parentScope);
				recordType := SyntaxTree.NewRecordType( -1, parentScope, recordScope);
				recordType.SetTypeDeclaration(typeDeclaration);
				recordType.SetState(SyntaxTree.Resolved);
				typeDeclaration.SetDeclaredType(recordType);
				AddVariable("@ptr",system.anyType);
				AddVariable("@adr",system.addressType);
				AddVariable("@flags",system.addressType);
				AddVariable("@dim",system.addressType);
				AddVariable("@elementSize",system.addressType);
				FOR i := 0 TO dimensions-1  DO
					name := "@len";
					Basic.AppendNumber(name,i);
					AddVariable(name,system.addressType);
					name := "@incr";
					Basic.AppendNumber(name,i);
					AddVariable(name,system.addressType);
				END;
				parentScope.AddTypeDeclaration(typeDeclaration);
				parentScope.EnterSymbol(typeDeclaration,duplicate);
				ASSERT(~duplicate);
				type := recordType;
			END;
			RETURN type
		END GetMathArrayDescriptorType;

		PROCEDURE NewMathArrayDescriptor(op: Operand; dimensions: LONGINT);
		VAR reg: IntermediateCode.Operand; type: SyntaxTree.Type;
		BEGIN
			type := GetMathArrayDescriptorType(dimensions);
			Emit(Push(op.op));
			(* push type descriptor *)
			reg := TypeDescriptorAdr(type);
			IF ~newObjectFile THEN
				IntermediateCode.MakeMemory(reg,addressType);
			END;
			Emit(Push(reg));
			ReleaseIntermediateOperand(reg);
			(* push realtime flag: false by default *)
			Emit(Push(false));
			IF newObjectFile THEN CallThis("Heaps","NewRec") ELSE
			SysCall(SysNewRec);
			END;
		END NewMathArrayDescriptor;

		PROCEDURE VisitBuiltinCallDesignator(x: SyntaxTree.BuiltinCallDesignator);
		VAR
			p0,p1,p2,parameter: SyntaxTree.Expression; len,val: LONGINT; l,r: Operand; res,adr,reg: IntermediateCode.Operand; type: SyntaxTree.Type;
			constructor: SyntaxTree.Procedure; s0,s1,s2: Operand; hint: HUGEINT;
			i: LONGINT; formalParameter: SyntaxTree.Parameter;
			tmp:IntermediateCode.Operand;
			size: LONGINT; dim,openDim: LONGINT; pointer: IntermediateCode.Operand; t,t0,t1,t2: SyntaxTree.Type; trueL,falseL,ignore: Label;
			exit,else,end: Label; procedureType: SyntaxTree.ProcedureType;
			name: Basic.PooledName; symbol: Sections.Section; operand: Operand;
			dest: IntermediateCode.Operand;
			staticLength: LONGINT; itype: IntermediateCode.Type;
			convert,isTensor: BOOLEAN;
			flags: SET;
			left: SyntaxTree.Expression;
			call: SyntaxTree.Designator;
			procedure: SyntaxTree.Procedure;
			temporaryVariable: SyntaxTree.Variable;
			dummy: IntermediateCode.Operand; (* nopov *)

			PROCEDURE CallBodies(self: IntermediateCode.Operand; type: SyntaxTree.Type);
			VAR recordScope: SyntaxTree.RecordScope; procedure: SyntaxTree.Procedure; body: SyntaxTree.Body; flags: LONGINT;
				priority: IntermediateCode.Operand;
				op: Operand;
			BEGIN
				IF type = NIL THEN RETURN END;
				type := type.resolved;
				IF type IS SyntaxTree.PointerType THEN
					type := type(SyntaxTree.PointerType).pointerBase.resolved
				END;
				IF type IS SyntaxTree.MathArrayType THEN RETURN END;
				CallBodies(self,type(SyntaxTree.RecordType).baseType);
				recordScope := type(SyntaxTree.RecordType).recordScope;
				IF recordScope.bodyProcedure # NIL THEN
					procedure := recordScope.bodyProcedure;
					body := procedure.procedureScope.body;
					Emit(Push(self));
					IF body.isActive THEN
						StaticCallOperand(result,procedure);
						Emit(Push(result.op));
						IF body.priority # NIL THEN Evaluate(body.priority,op); priority := op.op;
							Convert(priority,int32);
						ELSE priority := IntermediateCode.Immediate(int32,0)
						END;
						Emit(Push(priority));
						ReleaseIntermediateOperand(priority);
						flags := 0;
						IF body.isSafe THEN
							flags := 1;
						END;
						Emit(Push(IntermediateCode.Immediate(IntermediateCode.GetType(system,system.setType),flags)));
						Emit(Push(self));
						IF newObjectFile THEN
							CallThis("Objects","CreateProcess")
						ELSE
							SysCall(SysStart);
						END;
					ELSE
						Emit(Push(self));
						StaticCallOperand(result,procedure);
						Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
					END;
					Emit(Pop(self));
				END;
			END CallBodies;

			PROCEDURE PushString(op: Operand; actualType: SyntaxTree.Type);
			BEGIN
				actualType := actualType.resolved;
				IF actualType IS SyntaxTree.StringType THEN
					Emit(Push(IntermediateCode.Immediate(addressType,actualType(SyntaxTree.StringType).length)));
				ELSIF actualType(SyntaxTree.ArrayType).form = SyntaxTree.Static THEN
					Emit(Push(IntermediateCode.Immediate(addressType,actualType(SyntaxTree.ArrayType).staticLength)));
				ELSE
					tmp := op.tag;
					IntermediateCode.MakeMemory(tmp,addressType);
					Emit(Push(tmp));
				END;
				Emit(Push(op.op))
			END PushString;

			PROCEDURE PushTD(type: SyntaxTree.Type);
			VAR op: IntermediateCode.Operand;
			BEGIN
				IF type = NIL THEN Emit(Push(IntermediateCode.Immediate(addressType,0)))
				ELSIF type.resolved IS SyntaxTree.AnyType THEN Emit(Push(IntermediateCode.Immediate(addressType,1)))
				ELSE
					IF type.resolved IS SyntaxTree.PointerType THEN
						type := type.resolved(SyntaxTree.PointerType).pointerBase;
					END;
					op := TypeDescriptorAdr(type.resolved);
					IF ~newObjectFile THEN
						IntermediateCode.MakeMemory(op,addressType);
					END;
					Emit(Push(op));
				END
			END PushTD;


		BEGIN
			IF Trace THEN TraceEnter("VisitBuiltinCallDesignator") END;

			dest := destination; destination := emptyOperand;
			p0 := NIL; p1 := NIL; p2 := NIL; len := x.parameters.Length();
			IF len > 0 THEN p0 := x.parameters.GetExpression(0); t0 := p0.type.resolved END;
			IF len > 1 THEN p1 := x.parameters.GetExpression(1); t1 := p1.type.resolved END;
			IF len > 2 THEN p2 := x.parameters.GetExpression(2); t2 := p2.type.resolved END;

			CASE x.id OF

			(* ---- COPY ----- *)
			|Global.Copy:
				CopyString(p1,p0); (* roles exchanged: COPY ( src => dest ) *)
			(* ---- EXCL, INCL----- *)
			|Global.Excl,Global.Incl:
				Evaluate(p0,s0);
				Evaluate(p1,s1);
				Convert(s1.op,setType);
				IF (s1.op.mode # IntermediateCode.ModeImmediate) & ~backend.noRuntimeChecks THEN
					TrapC(BrltL,s1.op,IntermediateCode.Immediate(setType,setType.sizeInBits),IndexCheckTrap);
				END;
				ReuseCopy(res,s0.op);
				ReleaseOperand(s0);
				Reuse1(tmp,s1.op);
				ReleaseOperand(s1);
				Emit(Shl(tmp,IntermediateCode.Immediate(setType,1),s1.op));
				IF x.id = Global.Excl THEN
					Emit(Not(tmp,tmp));
					Emit(And(res,res,tmp));
				ELSE
					Emit(Or(res,res,tmp));
				END;
				ReleaseIntermediateOperand(tmp);
				Designate(p0,s0);
				ToMemory(s0.op,setType,0);
				Emit(Mov(s0.op,res));
				ReleaseOperand(s0); ReleaseIntermediateOperand(res);
			(* ---- GETPROCEDURE ----- *)
			|Global.GetProcedure:
				Designate(p0,s0);
				PushString(s0,p0.type);
				Designate(p1,s1);
				PushString(s1,p1.type);
				procedureType := p2.type.resolved(SyntaxTree.ProcedureType);
				IF (procedureType.firstParameter = NIL) OR (procedureType.firstParameter.access = SyntaxTree.Hidden) THEN PushTD(NIL)
				ELSE PushTD(procedureType.firstParameter.type)
				END;
				PushTD(procedureType.returnType);

				Designate(p2,s2);
				Emit(Push(s2.op));
				ReleaseOperand(s0); ReleaseOperand(s1); ReleaseOperand(s2);
				IF newObjectFile THEN
					CallThis("Modules","GetProcedure");
				ELSE
				SysCall(SysGetProcedure);
				END;
			(* ---- ASH, LSH, ROT ----- *)
			|Global.Ash, Global.systemLsh, Global.systemRot:
				Evaluate(p0,s0);
				IF (x.id = Global.systemLsh) OR (x.id = Global.systemRot) THEN
					IF s0.op.type.form = IntermediateCode.SignedInteger THEN
						convert:= TRUE;
						itype := s0.op.type;
						IntermediateCode.InitType(itype,IntermediateCode.UnsignedInteger,s0.op.type.sizeInBits);
						Convert(s0.op,itype);
					ELSE
						convert := FALSE;
					END;
				END;
				Evaluate(p1,s1);
				IF IsIntegerConstant(p1,hint) THEN
					ReuseCopy(reg,s0.op);
					IF hint  > 0 THEN
						IntermediateCode.InitImmediate(s1.op,s0.op.type,hint);
						IF x.id = Global.Ash THEN Emit(Shl(reg,s0.op,s1.op))
						ELSIF x.id = Global.systemLsh THEN Emit(Shl(reg,s0.op,s1.op))
						ELSIF x.id = Global.systemRot THEN Emit(Rol(reg,s0.op,s1.op))
						END;
					ELSIF hint < 0 THEN
						IntermediateCode.InitImmediate(s1.op,s0.op.type,-hint);
						IF x.id = Global.Ash THEN Emit(Shr(reg,s0.op,s1.op));
						ELSIF x.id = Global.systemLsh THEN Emit(Shr(reg,s0.op,s1.op));
						ELSIF x.id = Global.systemRot THEN Emit(Ror(reg,s0.op,s1.op));
						END;
					END;
					ReleaseOperand(s0); ReleaseOperand(s1);
				ELSE
					exit := NewLabel();
					end := NewLabel();
					ReuseCopy(reg,s0.op);
					BrgeL(exit,s1.op,IntermediateCode.Immediate(IntermediateCode.GetType(system,p1.type),0));
					Reuse1(tmp,s1.op);
					Emit(Neg(tmp,s1.op));
					Convert(tmp,s0.op.type);
					IF x.id = Global.Ash THEN Emit(Shr(reg,reg,tmp))
					ELSIF x.id = Global.systemLsh THEN Emit(Shr(reg,reg,tmp))
					ELSIF x.id = Global.systemRot THEN Emit(Ror(reg,reg,tmp))
					END;
					ReleaseIntermediateOperand(tmp);
					(*!!!!! distinction arithmetic / logical shift *)
					BrL(end);
					SetLabel(exit);
					ReuseCopy(tmp,s1.op);
					Convert(tmp,s0.op.type);
					IF x.id = Global.Ash THEN Emit(Shl(reg,reg,tmp))
					ELSIF x.id = Global.systemLsh THEN Emit(Shl(reg,reg,tmp))
					ELSIF x.id = Global.systemRot THEN Emit(Rol(reg,reg,tmp))
					END;
					ReleaseIntermediateOperand(tmp);
					SetLabel(end);
					ReleaseOperand(s0); ReleaseOperand(s1);
				END;
				InitOperand(result,ModeValue);
				IF convert THEN
					itype := reg.type;
					IntermediateCode.InitType(itype,IntermediateCode.SignedInteger,reg.type.sizeInBits);
					Convert(reg,itype);
				END;
				result.op := reg;
			(* ---- CAP ----- *)
			|Global.Cap:
				Evaluate(p0,result);
				ReuseCopy(reg,result.op);
				ReleaseIntermediateOperand(result.op);
				ignore := NewLabel();
				BrltL(ignore, reg,IntermediateCode.Immediate(IntermediateCode.GetType(system,system.characterType),ORD("a")));
				BrltL(ignore,IntermediateCode.Immediate(IntermediateCode.GetType(system,system.characterType),ORD("z")),reg);
				Emit(And(reg,reg,IntermediateCode.Immediate(IntermediateCode.GetType(system,system.characterType),5FH)));
				SetLabel(ignore);
				result.op := reg;
			(* ---- CHR ----- *)
			|Global.Chr:
				Evaluate(p0,result);
				Convert(result.op,IntermediateCode.GetType(system,x.type));
			|Global.Entier, Global.EntierH:
				Evaluate(p0,result);
				Convert(result.op,IntermediateCode.GetType(system,x.type));
			(* ---- MIN and MAX ----- *)
			|Global.Max,Global.Min:
				Evaluate(p0,s0);
				Evaluate(p1,s1);
				Reuse2(res,s0.op,s1.op);
				else := NewLabel();
				IF x.id = Global.Max THEN BrltL(else,s0.op,s1.op);
				ELSE BrltL(else,s1.op,s0.op) END;
				Emit(Mov(res,s0.op));
				ReleaseOperand(s0);
				end := NewLabel();
				BrL(end);
				SetLabel(else);
				Emit(MovReplace(res,s1.op));
				SetLabel(end);
				ReleaseOperand(s1);
				InitOperand(result,ModeValue);
				result.op := res;
			(* ---- ODD ----- *)
			|Global.Odd:
				IF ~conditional THEN
					ConditionToValue(x)
				ELSE
					Evaluate(p0,result);
					res := IntermediateCode.Immediate(IntermediateCode.GetType(system,p0.type),1);
					Reuse1(res,result.op);
					Emit(And(res,result.op,IntermediateCode.Immediate(IntermediateCode.GetType(system,p0.type),1)));
					ReleaseIntermediateOperand(result.op);
					result.op := res;
					BreqL(trueLabel,IntermediateCode.Immediate(IntermediateCode.GetType(system,p0.type),1),result.op);
					ReleaseOperand(result);
					BrL(falseLabel);
				END;
			(* ---- ORD ----- *)
			|Global.Ord:
				Evaluate(p0,result);
				Convert(result.op,IntermediateCode.GetType(system,x.type));
			(* ---- SHORT, LONG ----- *)
			|Global.Short, Global.Long:
				Evaluate(p0,result);
				Convert(result.op,IntermediateCode.GetType(system,x.type));
			(* ---- HALT, SYSTEM.HALT----- *)
			|Global.Halt, Global.systemHalt:
				Evaluate(p0,result);
				ASSERT(result.op.mode = IntermediateCode.ModeImmediate);
				Emit(Trap(SHORT(result.op.intValue)));
			(* ---- ASSERT ----- *)
			|Global.Assert:
				IF ~backend.noAsserts THEN
					trueL := NewLabel();
					falseL := NewLabel();
					Condition(p0,trueL,falseL);

					IF p1 = NIL THEN val := AssertTrap
					ELSE val := p1.resolved(SyntaxTree.IntegerValue).value;
					END;

					SetLabel(falseL);
					Emit(Trap(val));
					SetLabel(trueL);
				END;

				(*
				Emit(TrapC(result.op,val);
				*)
			(* ---- INC, DEC----- *)
			|Global.Inc,Global.Dec:
				Expression(p0); adr := result.op;
				LoadValue(result,p0.type); l := result;
				IF p1 = NIL THEN r.op := IntermediateCode.Immediate(IntermediateCode.GetType(system,p0.type),1);
				ELSE Expression(p1); LoadValue(result,p1.type); r := result;
				END;
				IF x.id = Global.Inc THEN
					Emit(Add(l.op,l.op,r.op));
				ELSE
					Emit(Sub(l.op,l.op,r.op));
				END;
				ReleaseOperand(l); ReleaseOperand(r);
			(* ---- LEN ----- *)
			|Global.Len: (* dynamic length, static length done by checker  *)
				Designate(p0,operand);
				IF p1 = NIL THEN
					InitOperand(l,ModeValue);
					l.op := IntermediateCode.Immediate(int32,0);
				ELSE
					Evaluate(p1,l);
				END;
				IF p0.type.resolved IS SyntaxTree.ArrayType THEN
					ArrayLen(p0.type.resolved(SyntaxTree.ArrayType),operand,l.op, result);
					ReleaseOperand(operand); ReleaseOperand(l);
				ELSIF p0.type.resolved IS SyntaxTree.MathArrayType THEN
					ASSERT(p1 # NIL);
					IF p0.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
						Dereference(operand,p0.type.resolved);
					END;
					GetMathArrayLength(p0.type.resolved(SyntaxTree.MathArrayType),operand, l.op, TRUE, result);
					ReleaseOperand(operand); ReleaseOperand(l);
				ELSE HALT(100);
				END;
				Convert(result.op,IntermediateCode.GetType(system, x.type));

			(* ---- FIRST ---- *)
			|Global.First:
				IF p0 IS SyntaxTree.RangeExpression THEN (* optimization, could also work with designate *)
					Evaluate(p0(SyntaxTree.RangeExpression).first, result)
				ELSE
					Designate(p0, result)
				END

			(* ---- LAST ---- *)
			|Global.Last:
				IF p0 IS SyntaxTree.RangeExpression THEN (* optimization, could also work with designate *)
					Evaluate(p0(SyntaxTree.RangeExpression).last, result)
				ELSE
					Designate(p0, result);
					(* make sure result.op is a register *)
					tmp := result.op;
					ReuseCopy(result.op, result.op);
					ReleaseIntermediateOperand(tmp);
					(* add offset to result.op *)
					IntermediateCode.AddOffset(result.op, ToMemoryUnits(system, system.SizeOf(system.longintType)))
				END

			(* ---- STEP ---- *)
			|Global.Step:
				IF p0 IS SyntaxTree.RangeExpression THEN (* optimization, could also work with designate *)
					Evaluate(p0(SyntaxTree.RangeExpression).step, result)
				ELSE
					Designate(p0, result);

					(* make sure result.op is a register *)
					tmp := result.op;
					ReuseCopy(result.op, result.op);
					ReleaseIntermediateOperand(tmp);

					(* add offset to result.op *)
					IntermediateCode.AddOffset(result.op, 2 * ToMemoryUnits(system, system.SizeOf(system.longintType)))
				END

			(* ---- ABS ----- *)
			|Global.Abs:
				Evaluate(p0,operand);
				type := p0.type.resolved;
				InitOperand(result,ModeValue);
				Reuse1a(result.op,operand.op,dest);
				Emit(Abs(result.op,operand.op));
				ReleaseOperand(operand);
			(* ---- NEW ----- *)
			|Global.New:
				(*! the following code is only correct for "standard" Oberon calling convention *)
				type := p0.type.resolved;
				IF (type IS SyntaxTree.PointerType) & (type(SyntaxTree.PointerType).pointerBase.resolved IS SyntaxTree.RecordType)
				THEN
					temporaryVariable := GetTemporaryVariable(type);
					IF temporaryVariable # NIL THEN
						Symbol(temporaryVariable,l); (*Designate(temporaryVariable,l)*)
					ELSE
						Designate(p0,l);
					END;
					(* l.op contains address of pointer to record *)
					Emit(Push(l.op)); (* address for use after syscall *)
					Emit(Push(l.op));
					ReleaseOperand(l);

					(* push type descriptor *)
					reg := TypeDescriptorAdr(p0.type.resolved(SyntaxTree.PointerType).pointerBase.resolved);
					IF ~newObjectFile THEN
						IntermediateCode.MakeMemory(reg,addressType);
					END;
					Emit(Push(reg));
					ReleaseIntermediateOperand(reg);

					(* push realtime flag *)
					IF (p0.type.resolved.isRealtime) THEN Emit(Push(true));
					ELSE Emit(Push(false));
					END;

					IF newObjectFile THEN
						CallThis("Heaps","NewRec");
					ELSE
						SysCall(SysNewRec);
					END;
					(* check allocation success, if not successful then do not call initializers and bodies *)
					IntermediateCode.InitRegister(pointer,addressType,AcquireRegister(addressType));
					Emit(Pop(pointer));
					MakeMemory(reg,pointer,addressType,0);
					ReleaseIntermediateOperand(pointer); pointer := reg;
					exit := NewLabel();
					BreqL(exit,pointer,nil);
					Emit(Push(pointer));

					(* initialize fields *)
					InitFields(p0.type.resolved(SyntaxTree.PointerType).pointerBase.resolved, pointer,0);

					(* call initializer *)
					constructor := GetConstructor(p0.type.resolved(SyntaxTree.PointerType).pointerBase.resolved(SyntaxTree.RecordType));
					IF constructor # NIL THEN
						(*! should be unified with ProcedureCallDesignator *)
						formalParameter := constructor.type(SyntaxTree.ProcedureType).firstParameter;
						FOR i := 1 TO x.parameters.Length()-1 DO
							PushParameter(x.parameters.GetExpression(i), formalParameter,SyntaxTree.OberonCallingConvention, FALSE, dummy);
							formalParameter := formalParameter.nextParameter;
						END;
						(* static call of the constructor *)
						Emit(Push(pointer));
						ReleaseIntermediateOperand(pointer);
						Global.GetSymbolPooledName(constructor,name);
						ASSERT(~constructor.isInline);
						IF constructor.scope.ownerModule # module.module THEN
							IF currentCellScope # NIL THEN
								currentCellScope.AddImport(constructor.scope.ownerModule);
							END;
							symbol := NewSection(module.allSections, Sections.ImportedSymbolKind,Sections.CodeSection, FALSE, name,constructor,commentPrintout # NIL);
						ELSE
							symbol := NewSection(module.allSections, Sections.RegularKind,Sections.CodeSection, TRUE, name,constructor,commentPrintout # NIL);
						END;
						Emit(Call(IntermediateCode.Address(addressType, symbol,0),ProcedureParametersSize(system,constructor)));
					ELSE
						ReleaseIntermediateOperand(pointer);
					END;

					IntermediateCode.InitRegister(pointer,addressType,AcquireRegister(addressType));
					Emit(Pop(pointer));

					IF temporaryVariable # NIL THEN
						Designate(p0,l);
						ToMemory(l.op,addressType,0);
						Emit(Mov(l.op,pointer));
						ReleaseOperand(l);
					END;

					(* call bodies *)
					CallBodies(pointer,p0.type);
					ReleaseIntermediateOperand(pointer);

					IF temporaryVariable # NIL THEN
						end := NewLabel();
						BrL(end);
						SetLabel(exit);
						Designate(p0,l);
						ToMemory(l.op,addressType,0);
						Emit(Mov(l.op,nil)); (* write NIL to adr *)
						ReleaseOperand(l);
						SetLabel(end);
					ELSE
						SetLabel(exit);
					END;
				ELSIF (type IS SyntaxTree.PointerType) & (type(SyntaxTree.PointerType).pointerBase.resolved IS SyntaxTree.ArrayType)  THEN
					type := type(SyntaxTree.PointerType).pointerBase.resolved;

					dim := 0;

					IF p1 # NIL THEN
						FOR i := 1 TO x.parameters.Length()-1 DO
							type := type(SyntaxTree.ArrayType).arrayBase.resolved;
							parameter := x.parameters.GetExpression(i);
							Evaluate(parameter,r);
							IF (r.op.mode # IntermediateCode.ModeImmediate) & ~backend.noRuntimeChecks THEN
								IntermediateCode.InitImmediate(tmp,IntermediateCode.GetType(system,parameter.type),0);
								TrapC(BrgeL,r.op,tmp,ArraySizeTrap);
							END;
							Emit(Push(r.op));
							IF i=1 THEN
								ReuseCopy(reg,r.op);
							ELSE
								Emit(Mul(reg,reg,r.op)); (*! optimize the multiplication of immediate operands *)
							END;
							ReleaseOperand(r);
							INC(dim);
						END;
						Convert(reg,addressType);
					ELSE
						IntermediateCode.InitRegister(reg,addressType,AcquireRegister(addressType));
						Emit(Mov(reg,IntermediateCode.Immediate(addressType,1)));
					END;

					openDim := dim;
					ASSERT(~(type IS SyntaxTree.ArrayType) OR (type(SyntaxTree.ArrayType).form = SyntaxTree.Static));

					(*! the following code is only correct for "standard" Oberon calling convention *)
					IF SemanticChecker.ContainsPointer(type) THEN
						IF type IS SyntaxTree.ArrayType THEN
							staticLength := 1;
							WHILE (type IS SyntaxTree.ArrayType) DO (* static array *)
								staticLength := staticLength * type(SyntaxTree.ArrayType).staticLength;
								type := type(SyntaxTree.ArrayType).arrayBase.resolved;
							END;
							tmp := IntermediateCode.Immediate(reg.type,staticLength);
							Emit(Mul(reg,reg,tmp));
						END;
						Designate(p0,l);
						IF openDim > 0 THEN
							Emit(Push(l.op)); (* address for use after syscall *)
						END;
						Emit(Push(l.op)); (* address *)
						ReleaseOperand(l);

						tmp := TypeDescriptorAdr(type);
						IF ~newObjectFile THEN
							IntermediateCode.MakeMemory(tmp,addressType);
						END;
						Emit(Push(tmp)); (* type descriptor *)
						ReleaseIntermediateOperand(tmp);

						Emit(Push(reg)); (* number Elements *)
						ReleaseIntermediateOperand(reg);
						tmp := IntermediateCode.Immediate(addressType,dim);
						Emit(Push(tmp)); (* dimensions *)
						(* push realtime flag *)
						IF (p0.type.resolved.isRealtime) THEN Emit(Push(true));
						ELSE Emit(Push(false));
						END;
						IF newObjectFile THEN CallThis("Heaps","NewArr") ELSE
						SysCall(SysNewArr);
						END;
					ELSE
						size := ToMemoryUnits(system,system.SizeOf(type));
						IF (size # 1) THEN
							Emit(Mul(reg,reg,IntermediateCode.Immediate(addressType,size))); (*! optimize the multiplication of immediate operands *)
						END;
						tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,ArrayDimTable * system.addressSize+ system.addressSize+  system.addressSize * 2 * (openDim DIV 2)));
						(* DIV 2 term for some strange alignment, don't understand it at the moment - copied from PCC *)
						Emit(Add(reg,reg,tmp));
						Designate(p0,l);
						IF openDim >0 THEN
							Emit(Push(l.op)); (* address for use after syscall *)
						END;
						Emit(Push(l.op)); (* address for syscall *)
						ReleaseOperand(l); (* pointer address *)

						Emit(Push(reg)); (* size *)
						ReleaseIntermediateOperand(reg);
						(* push realtime flag *)
						IF (p0.type.resolved.isRealtime) THEN Emit(Push(true));
						ELSE Emit(Push(false));
						END;
						IF newObjectFile THEN CallThis("Heaps","NewSys") ELSE
						SysCall(SysNewSys);
						END;
					END;

					IF openDim > 0 THEN
						IntermediateCode.InitRegister(adr,addressType,AcquireRegister(addressType));
						Emit(Pop(adr));
						ToMemory(adr,addressType,0);
						ReuseCopy(tmp,adr);
						ReleaseIntermediateOperand(adr);
						adr := tmp;

						else := NewLabel();
						BreqL(else,adr,IntermediateCode.Immediate(addressType,0));

						i := openDim-1;
						IntermediateCode.InitRegister(reg,addressType,AcquireRegister(addressType));
						WHILE (i >= 0) DO
							Emit(Pop(reg));
							IntermediateCode.InitMemory(res,addressType,adr,ToMemoryUnits(system,ArrayDimTable* system.addressSize + system.addressSize*((openDim-1)-i)));
							Emit(Mov(res,reg));
							DEC(i);
						END;
						ReleaseIntermediateOperand(adr);
						ReleaseIntermediateOperand(reg);

						exit := NewLabel();
						BrL(exit);
						SetLabel(else);
						(* else part: array could not be allocated *)
						tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,openDim*system.addressSize));
						Emit(Add(sp,sp,tmp));
						SetLabel(exit);
					END;
				ELSIF (type IS SyntaxTree.MathArrayType) THEN
					IF t1 IS SyntaxTree.MathArrayType THEN (* NEW(a, array) *)
						IF GetRuntimeProcedure("FoxArrayBase","AllocateTensorX",procedure,TRUE) THEN
							left := SyntaxTree.NewSymbolDesignator(Diagnostics.Invalid,NIL,procedure);
							procedureType := procedure.type(SyntaxTree.ProcedureType);
							left.SetType(procedure.type);
							formalParameter := procedureType.firstParameter;
							(* push array to allocate *)
							PushParameter(p0, formalParameter, procedureType.callingConvention, FALSE, dummy);
							formalParameter :=formalParameter.nextParameter;
							(* push length array *)
							PushParameter(p1, formalParameter, procedureType.callingConvention, FALSE, dummy);
							(* push size *)
							type := t0;
							WHILE (type IS SyntaxTree.MathArrayType) & (type(SyntaxTree.MathArrayType).form # SyntaxTree.Static) DO
								type := type(SyntaxTree.MathArrayType).arrayBase.resolved;
							END;
							tmp := IntermediateCode.Immediate(IntermediateCode.GetType(system, system.longintType),ToMemoryUnits(system,system.SizeOf(type))); (* alignment *)
							Emit(Push(tmp));
							(* *)
							IF SemanticChecker.ContainsPointer(type) THEN
								tmp := TypeDescriptorAdr(type);
								IF ~newObjectFile THEN
									IntermediateCode.MakeMemory(tmp,addressType);
								END;
							ELSE
								tmp := IntermediateCode.Immediate(addressType, 0);
							END;
							Emit(Push(tmp)); (* type descriptor *)

							StaticCallOperand(result,procedure);
							Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
							ReleaseOperand(result);
						END;
						(*
						designator := SyntaxTree.NewIdentifierDesignator(InvalidPosition, Global.ArrayBaseName);
						designator := SyntaxTree.NewSelectorDesignator(InvalidPosition, designator, SyntaxTree.NewIdentifier(InvalidPosition, "AllocateTensorX"));
						result := ResolveExpression(SyntaxTree.NewParameterDesignator(InvalidPosition, designator, actualParameters));
						*)
					ELSE

						dim := 0;

						IF type(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
							(* generate geometry descriptor *)
							Designate(p0,l);
							NewMathArrayDescriptor(l, x.parameters.Length()-1);
							ReleaseOperand(l);
							isTensor := TRUE;
						ELSE
							isTensor := FALSE;
						END;

						FOR i := 1 TO x.parameters.Length()-1 DO
							IF ~isTensor THEN
								type := type(SyntaxTree.MathArrayType).arrayBase.resolved;
							END;
							parameter := x.parameters.GetExpression(i);
							Evaluate(parameter,r);
							IF (r.op.mode # IntermediateCode.ModeImmediate) & ~(backend.noRuntimeChecks) THEN
								IntermediateCode.InitImmediate(tmp,IntermediateCode.GetType(system,parameter.type),0);
								TrapC(BrgeL,r.op,tmp,ArraySizeTrap);
							END;
							Emit(Push(r.op));
							IF i=1 THEN
								ReuseCopy(reg,r.op);
							ELSE
								Emit(Mul(reg,reg,r.op)); (*! optimize the multiplication of immediate operands *)
							END;
							ReleaseOperand(r);
							INC(dim);
						END;
						Convert(reg,addressType);

						openDim := dim;
						ASSERT(~(type IS SyntaxTree.MathArrayType) OR (type(SyntaxTree.MathArrayType).form IN {SyntaxTree.Static,SyntaxTree.Tensor}));

						(*! the following code is only correct for "standard" Oberon calling convention *)
						IF SemanticChecker.ContainsPointer(SemanticChecker.ArrayBase(type,MAX(LONGINT))) THEN
							t := type;
							IF ~isTensor & (t IS SyntaxTree.MathArrayType) THEN
								staticLength := 1;
								WHILE (t IS SyntaxTree.MathArrayType) DO (* static array *)
									staticLength := staticLength * t(SyntaxTree.MathArrayType).staticLength;
									t := t(SyntaxTree.MathArrayType).arrayBase.resolved;
								END;
								tmp := IntermediateCode.Immediate(reg.type,staticLength);
								Emit(Mul(reg,reg,tmp));
							END;
							Designate(p0,l);
							IF isTensor THEN
								Dereference(l,type);
								t := SemanticChecker.ArrayBase(type,MAX(LONGINT));
							END;
							Emit(Push(l.tag)); (* address for use after syscall *)
							Emit(Push(l.tag)); (* address *)
							ReleaseOperand(l);

							tmp := TypeDescriptorAdr(t);
							IF ~newObjectFile THEN
								IntermediateCode.MakeMemory(tmp,addressType);
							END;
							Emit(Push(tmp)); (* type descriptor *)
							ReleaseIntermediateOperand(tmp);

							Emit(Push(reg)); (* number Elements *)
							ReleaseIntermediateOperand(reg);
							tmp := IntermediateCode.Immediate(addressType,0);
							Emit(Push(tmp)); (* dimensions = 0, we control dimensions in the geometry descriptor *)
							(* push realtime flag: false by default *)
							Emit(Push(false));
							IF newObjectFile THEN CallThis("Heaps","NewArr") ELSE SysCall(SysNewArr) END;
							IntermediateCode.InitRegister(adr,addressType,AcquireRegister(addressType));
							Emit(Pop(adr));
							GetMathArrayField(tmp,adr,MathPtrOffset);
							IntermediateCode.InitRegister(reg,addressType,AcquireRegister(addressType));
							Emit(Add(reg,tmp,IntermediateCode.Immediate(addressType,ToMemoryUnits(system,ArrDataArrayOffset))));
							PutMathArrayField(adr,reg,MathAdrOffset);
							ReleaseIntermediateOperand(tmp);
							ReleaseIntermediateOperand(reg);
						ELSE
							IF isTensor THEN
								size := ToMemoryUnits(system,system.SizeOf(SemanticChecker.ArrayBase(type,MAX(LONGINT))));
							ELSE
								size := ToMemoryUnits(system,system.SizeOf(SemanticChecker.ArrayBase(type,openDim)));
							END;
							IF (size # 1) THEN
								Emit(Mul(reg,reg,IntermediateCode.Immediate(addressType,size))); (*! optimize the multiplication of immediate operands *)
							END;
							tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,SysDataArrayOffset));
							(* DIV 2 term for some strange alignment, don't understand it at the moment - copied from PCC *)
							Emit(Add(reg,reg,tmp));

							Designate(p0,l);
							IF isTensor THEN
								Dereference(l,type);
							END;
							Emit(Push(l.tag)); (* address for use after syscall *)
							Emit(Push(l.tag)); (* address for syscall *)
							ReleaseOperand(l); (* pointer address *)

							Emit(Push(reg)); (* size *)
							ReleaseIntermediateOperand(reg);
							(* push realtime flag: false by default *)
							Emit(Push(false));
							IF newObjectFile THEN CallThis("Heaps","NewSys");
							ELSE SysCall(SysNewSys)
							END;
							IntermediateCode.InitRegister(adr,addressType,AcquireRegister(addressType));
							Emit(Pop(adr));
							GetMathArrayField(tmp,adr,MathPtrOffset);
							IntermediateCode.InitRegister(reg,addressType,AcquireRegister(addressType));
							Emit(Add(reg,tmp,IntermediateCode.Immediate(addressType,ToMemoryUnits(system,SysDataArrayOffset))));
							PutMathArrayField(adr,reg,MathAdrOffset);
							ReleaseIntermediateOperand(tmp);
							ReleaseIntermediateOperand(reg);
						END;


						flags := {};
						IntermediateCode.InitImmediate(tmp,addressType,SYSTEM.VAL(LONGINT,flags));
						PutMathArrayField(adr,tmp,MathFlagsOffset);
						IntermediateCode.InitImmediate(tmp,addressType,openDim);
						PutMathArrayField(adr,tmp,MathDimOffset);

						else := NewLabel();
						BreqL(else,IntermediateCode.Memory(addressType,adr,0),IntermediateCode.Immediate(addressType,0));

						i := openDim-1;
						IntermediateCode.InitRegister(reg,addressType,AcquireRegister(addressType));
						IF isTensor THEN
							IntermediateCode.InitImmediate(tmp,addressType,ToMemoryUnits(system,system.SizeOf(SemanticChecker.ArrayBase(type,MAX(LONGINT)))));
						ELSE
							IntermediateCode.InitImmediate(tmp,addressType,ToMemoryUnits(system,system.SizeOf(SemanticChecker.ArrayBase(type,openDim))));
						END;
						PutMathArrayField(adr,tmp,MathElementSizeOffset);
						WHILE (i >= 0) DO
							Emit(Pop(reg));
							PutMathArrayLength(adr,reg,i);
							PutMathArrayIncrement(adr,tmp,i);
							IF i > 0 THEN
								IF i=openDim-1 THEN
									ReuseCopy(tmp,tmp);
								END;
								Emit(Mul(tmp,tmp,reg));
							END;
							DEC(i);
						END;
						ReleaseIntermediateOperand(adr);
						ReleaseIntermediateOperand(reg);
						ReleaseIntermediateOperand(tmp);

						exit := NewLabel();
						BrL(exit);
						SetLabel(else);
						(* else part: array could not be allocated *)
						tmp := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,openDim*system.addressSize));
						Emit(Add(sp,sp,tmp));

						SetLabel(exit);
					END;
				ELSIF type IS SyntaxTree.CellType THEN
					Error(p0.position,"cannot be allocated in runtime yet");
				ELSE (* no pointer to record, no pointer to array *)
					HALT(200);
				END;
			(* ---- SYSTEM.ADR----- *)
			|Global.systemAdr:
				Designate(p0,s0);
				s0.mode := ModeValue;
				IF (t0 IS SyntaxTree.MathArrayType) & (t0(SyntaxTree.MathArrayType).form = SyntaxTree.Open) THEN
					ReleaseIntermediateOperand(s0.op);
					s0.op := s0.tag;
					IntermediateCode.InitOperand(s0.tag);
				END;
				Convert(s0.op,IntermediateCode.GetType(system,x.type));
				result := s0;
			(* ---- SYSTEM.BIT ----- *)
			|Global.systemBit:
				Evaluate(p0,s0);
				ToMemory(s0.op,addressType,0);
				ReuseCopy(res,s0.op);
				ReleaseOperand(s0);
				Evaluate(p1,s1);
				Emit(Ror(res,res,s1.op));
				ReleaseOperand(s1);
				Emit(And(res,res,IntermediateCode.Immediate(IntermediateCode.GetType(system,p0.type),1)));
				Convert(res,IntermediateCode.GetType(system,system.booleanType));
				IF ~conditional THEN
					InitOperand(result,ModeValue); result.op := res;
				ELSE
					BreqL(trueLabel,IntermediateCode.Immediate(res.type,1),res);
					BrL(falseLabel);
					ReleaseIntermediateOperand(res);
				END;
			(* --- SYSTEM.MSK ----*)
			|Global.systemMsk:
				Evaluate(p0,s0);
				Evaluate(p1,s1);
				ReuseCopy(res,s0.op);
				ReleaseOperand(s0);
				Emit(And(res,res,s1.op));
				ReleaseOperand(s1);
				InitOperand(result,ModeValue);
				result.op := res;
			(* ---- SYSTEM.GET8|16|32|64 ----- *)
			|Global.systemGet8, Global.systemGet16, Global.systemGet32, Global.systemGet64:
				Evaluate(p0,s0);
				MakeMemory(res,s0.op,IntermediateCode.GetType(system,x.type),0);
				ReleaseOperand(s0);
				InitOperand(result,ModeValue);
				result.op := res;

			(* ---- SYSTEM.VAL ----- *)
			|Global.systemVal:
				Expression(p1);
				s1 := result;
				type :=p0(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType;
				IF s1.mode = ModeReference THEN
					(* nothing to  be done if not record type, just take over new type *)
					IF (type IS SyntaxTree.RecordType) THEN
						ReleaseIntermediateOperand(s1.tag);
						s1.tag := TypeDescriptorAdr(type);
						IF ~newObjectFile THEN
							IntermediateCode.MakeMemory(s1.tag,addressType);
						END;
						UseIntermediateOperand(s1.tag);
					END;
					result := s1;
				ELSE (* copy over result to different type, may not use convert *)
					itype := IntermediateCode.GetType(system,type);
					IF itype.sizeInBits = s1.op.type.sizeInBits THEN
						IntermediateCode.InitRegister(s0.op,itype,AcquireRegister(itype));
						Emit(Mov(s0.op,s1.op));
						ReleaseOperand(s1);
						InitOperand(result,ModeValue);
						result.op := s0.op;
					ELSE (* different size, must convert *)
						(*! this is not very clean, should we forbid conversions between operands with different sizes or should we implement a cutting move ??? *)
						Convert(s1.op, IntermediateCode.GetType(system,type));
						result := s1;
					END;
				END;
			(* ---- SYSTEM.GET ----- *)
			|Global.systemGet:
				Evaluate(p0,s0); (* adr *)
				Designate(p1,s1); (* variable *)
				ToMemory(s0.op,IntermediateCode.GetType(system,p1.type),0);
				ToMemory(s1.op,IntermediateCode.GetType(system,p1.type),0);
				Emit(Mov(s1.op,s0.op));
				ReleaseOperand(s1);
				ReleaseOperand(s0);
			(* ---- SYSTEM.PUT 8|16|32|64 ----- *)
			|Global.systemPut, Global.systemPut64, Global.systemPut32, Global.systemPut16, Global.systemPut8:
				Evaluate(p0,s0); (*  *)
				Evaluate(p1,s1); (* variable *)
				MakeMemory(res,s0.op,IntermediateCode.GetType(system,p1.type),0);
				ReleaseOperand(s0);
				Emit(Mov(res,s1.op));
				ReleaseIntermediateOperand(res);
				ReleaseOperand(s1);
			(* ---- SYSTEM.MOVE ----- *)
			|Global.systemMove:
				Evaluate(p0,s0);
				Evaluate(p1,s1);
				Evaluate(p2,s2);
				Emit(Copy(s1.op,s0.op,s2.op));
				ReleaseOperand(s0); ReleaseOperand(s1); ReleaseOperand(s2);
			(* ---- SYSTEM.NEW ----- *)
			|Global.systemNew:
				Designate(p0,s0);
				Emit(Push(s0.op));
				ReleaseOperand(s0);
				Evaluate(p1,s1);
				Emit(Push(s1.op));
				ReleaseOperand(s1);
				(* push realtime flag: false by default *)
				Emit(Push(false));
				IF newObjectFile THEN CallThis("Heaps","NewSys") ELSE
				SysCall(SysNewSys);
				END;
			(* ---- SYSTEM.INCR ----- *)
			|Global.systemIncr:
				Designate(p0,operand);
				IF p0.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
					Dereference(operand,p0.type.resolved);
				END;
				ASSERT(p1 # NIL);
				Evaluate(p1,l);
				GetMathArrayIncrement(p0.type.resolved(SyntaxTree.MathArrayType),operand, l.op,TRUE, result);

				ReleaseOperand(operand); ReleaseOperand(l);
				Convert(result.op,IntermediateCode.GetType(system, x.type));
			(* ---- SUM ----- *)
			|Global.Sum: HALT(200);
			(* ---- DIM ----- *)
			|Global.Dim:
				ASSERT(~SemanticChecker.IsArrayStructuredObjectType(p0.type));
				Designate(p0,s0);
				IF p0.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
					Dereference(s0,p0.type.resolved);
				END;
				MathArrayDim(p0.type.resolved(SyntaxTree.MathArrayType),s0.tag,result);
				ReleaseOperand(s0);
			(* ---- RESHAPE ----- *)
			|Global.Reshape:
				IF GetRuntimeProcedure("FoxArrayBase","Reshape",procedure,TRUE) THEN
					left := SyntaxTree.NewSymbolDesignator(Diagnostics.Invalid,NIL,procedure);
					left.SetType(procedure.type);
					call := SyntaxTree.NewProcedureCallDesignator(position,left(SyntaxTree.Designator),x.parameters);
					VisitProcedureCallDesignator(call(SyntaxTree.ProcedureCallDesignator));
				END;
			(* ---- SYSTEM.ZEROCOPY----- *)
			|Global.systemZeroCopy:
				IF GetRuntimeProcedure("FoxArrayBase","ZeroCopy",procedure,TRUE) THEN
					left := SyntaxTree.NewSymbolDesignator(Diagnostics.Invalid, NIL, procedure);
					left.SetType(procedure.type);
					call := SyntaxTree.NewProcedureCallDesignator(position,left(SyntaxTree.Designator),x.parameters);
					VisitProcedureCallDesignator(call(SyntaxTree.ProcedureCallDesignator));
				END;
			(* ---- SYSTEM.TYPECODE ----- *)
			|Global.systemTypeCode:
				type := p0(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType;
				IF type.resolved IS SyntaxTree.PointerType THEN
					type := type.resolved(SyntaxTree.PointerType).pointerBase;
				END;
				result.op := TypeDescriptorAdr(type);
				IF ~newObjectFile THEN
					ToMemory(result.op,IntermediateCode.GetType(system,x.type),0);
				ELSE Convert(result.op, IntermediateCode.GetType(system,x.type));
				END;
				result.mode := ModeValue;
			(* ---- SYSTEM.TRACE ----- *)
			|Global.systemTrace:
				SystemTrace(x.parameters);
			(* ----- CONNECT ------*)
			|Global.Connect:
				Error(x.position,"cannot be connected in runtime yet");
			(* ----- SEND ------*)
			|Global.Send:
				Evaluate(p0,s0);
				Evaluate(p1,s1);
				size := ToMemoryUnits(system,system.SizeOf(p1.type));
				Emit(Push(s0.op));
				Emit(Push(s1.op));
				(*
				Emit(Push(IntermediateCode.Immediate(addressType,size)));
				*)
				IF size # 1 THEN Error(p1.position,"send not implemented for complex data types") END;
				ReleaseOperand(s0);
				ReleaseOperand(s1);
				CallThis(ChannelModuleName,"Send");
			(* ----- RECEIVE ------*)
			|Global.Receive:
				Evaluate(p0,s0);
				Emit(Push(s0.op));
				Designate(p1,s1);
				size := ToMemoryUnits(system,system.SizeOf(p1.type));
				Emit(Push(s1.op));
				IF p2 # NIL THEN
					Designate(p2,s2);
					Emit(Push(s2.op));
				END;


				(*
				Emit(Push(IntermediateCode.Immediate(addressType,size)));
				*)
				IF size # 1 THEN Error(p1.position,"receive not implemented for complex data types") END;
				ReleaseOperand(s0);
				ReleaseOperand(s1);
				ReleaseOperand(s2);
				IF p2 = NIL THEN
					CallThis(ChannelModuleName,"Receive")
				ELSE
					CallThis(ChannelModuleName,"ReceiveNonBlocking")
				END;
			ELSE (* function not yet implemented *)
				Error(position,"not yet implemented");
			END;
			destination := dest;
			IF Trace THEN TraceExit("VisitBuiltinCallDesignator") END;
		END VisitBuiltinCallDesignator;

		PROCEDURE VisitTypeGuardDesignator(x: SyntaxTree.TypeGuardDesignator);
		VAR trueL,falseL: Label; recordType: SyntaxTree.RecordType; dest,tag,ptr: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitTypeGuardDesignator") END;
			dest := destination; destination := emptyOperand;

			Expression(x.left);
			IF x.left.type.resolved = x.type.resolved THEN (* always true: do nothing *)
			ELSIF backend.noRuntimeChecks THEN (* no check *)
			ELSE
				trueL := NewLabel();
				falseL := NewLabel();
				IF IsPointerToRecord(x.left.type,recordType) THEN
					IntermediateCode.InitRegister(tag,addressType,AcquireRegister(addressType));
					Emit(Mov(tag, result.op));
					IF result.mode # ModeValue THEN
						ptr := tag;
						IntermediateCode.MakeMemory(ptr,addressType);
						Emit(Mov(tag, ptr));
					END;
					IntermediateCode.AddOffset(tag,ToMemoryUnits(system,-addressType.sizeInBits));
					IntermediateCode.MakeMemory(tag,addressType);
				ELSE
					tag := result.tag;
				END;
				TypeTest(tag,x.type,trueL,falseL);
				ReleaseIntermediateOperand(tag);
				SetLabel(falseL);
				Emit(Trap(TypeCheckTrap));
				SetLabel(trueL);
			END;
			destination := dest;
			IF Trace THEN TraceExit("VisitTypeGuardDesignator") END;
		END VisitTypeGuardDesignator;

		PROCEDURE Dereference(VAR operand: Operand; type: SyntaxTree.Type);
		VAR dereferenced: IntermediateCode.Operand; arrayDataOffset: LONGINT;
		BEGIN
			LoadValue(operand,system.addressType); (* in case operand is not a value yet *)
			ReuseCopy(dereferenced,operand.op);
			ReleaseOperand(operand);
			operand.mode := ModeReference;
			operand.op := dereferenced;
			operand.tag := dereferenced;
			UseIntermediateOperand(operand.tag);
			IF (type=NIL) OR (type IS SyntaxTree.RecordType) THEN
				IntermediateCode.AddOffset(operand.tag,ToMemoryUnits(system,-addressType.sizeInBits));
				IntermediateCode.MakeMemory(operand.tag,addressType);
			ELSIF type IS SyntaxTree.ArrayType THEN
				arrayDataOffset := DynamicDim(type) * addressType.sizeInBits + 3 * addressType.sizeInBits;
				INC(arrayDataOffset, (-arrayDataOffset) MOD ArrayAlignment);  (* round up to multiple of ArrayAlignment to ensure that first array element is aligned at 0 MOD ArrayAlignment *)
				IntermediateCode.AddOffset(operand.op,ToMemoryUnits(system,arrayDataOffset));
				IntermediateCode.AddOffset(operand.tag,ToMemoryUnits(system,ArrayDimTable*system.addressSize))
			ELSIF type IS SyntaxTree.MathArrayType THEN
				IntermediateCode.AddOffset(operand.op,ToMemoryUnits(system,MathAdrOffset*addressType.sizeInBits));
				IntermediateCode.MakeMemory(operand.op,addressType);
			ELSE HALT(100);
			END;
		END Dereference;

		PROCEDURE VisitDereferenceDesignator(x: SyntaxTree.DereferenceDesignator);
		VAR  type: SyntaxTree.Type; d: Operand; dest: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitDereferenceDesignator") END;
			dest := destination; destination := emptyOperand;
			Evaluate(x.left,d);
			type := x.type.resolved;
			Dereference(d,type);
			result := d;
			destination := dest;
			IF Trace THEN TraceExit("VisitDereferenceDesignator") END;
		END VisitDereferenceDesignator;

		PROCEDURE VisitSupercallDesignator(x: SyntaxTree.SupercallDesignator);
		VAR procedure: SyntaxTree.Procedure; tag: IntermediateCode.Operand; dest: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitSupercallDesignator") END;
			dest := destination; destination := emptyOperand;
			Designate(x.left(SyntaxTree.SymbolDesignator).left,result);
			tag := result.op;
			ReleaseIntermediateOperand(result.tag);
			procedure := x.left(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.Procedure);
			StaticCallOperand(result,procedure.super);
			ReleaseIntermediateOperand(result.tag);
			result.tag := tag;
			destination := dest;
			IF Trace THEN TraceExit("VisitSupercallDesignator") END;
		END VisitSupercallDesignator;

		PROCEDURE VisitSelfDesignator(x: SyntaxTree.SelfDesignator);
		VAR basereg: IntermediateCode.Operand; scope: SyntaxTree.Scope; dest: IntermediateCode.Operand;
			moduleSection: IntermediateCode.Section; moduleOffset: LONGINT;
		BEGIN
			IF Trace THEN TraceEnter("VisitSelfDesignator") END;
			dest := destination; destination := emptyOperand;
			scope := currentScope;
			WHILE (scope.outerScope # NIL) & (scope.outerScope IS SyntaxTree.ProcedureScope) DO
				scope := scope.outerScope;
			END;
			IF scope.outerScope IS SyntaxTree.ModuleScope THEN
				IF newObjectFile THEN
					moduleSection := MetaModuleSection(SELF,module);
					moduleOffset := moduleSection.pc;
					result.mode := ModeValue;
					result.op := IntermediateCode.Address(addressType, moduleSection, moduleOffset);
				ELSE
					Symbol(moduleSelf,result);
					IntermediateCode.MakeMemory(result.op,addressType);
				END
			ELSE
				GetBaseRegister(basereg,currentScope,scope);
				InitOperand(result,ModeReference);
				result.op := basereg;
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,2*addressType.sizeInBits));
				(* tag must be loaded when dereferencing SELF pointer *)
			END;
			destination := dest;
			IF Trace THEN TraceExit("VisitSelfDesignator") END;
		END VisitSelfDesignator;

		PROCEDURE VisitResultDesignator(x: SyntaxTree.ResultDesignator);
		VAR procedure: SyntaxTree.Procedure; procedureType: SyntaxTree.ProcedureType; parameter: SyntaxTree.Parameter;
		BEGIN
			IF Trace THEN TraceEnter("VisitResultDesignator") END;
			procedure := currentScope(SyntaxTree.ProcedureScope).ownerProcedure;
			procedureType := procedure.type(SyntaxTree.ProcedureType);
			parameter := procedureType.returnParameter;
			VisitParameter(parameter);
			IF Trace THEN TraceExit("VisitResultDesignator") END;
		END VisitResultDesignator;

		(** values *)
		PROCEDURE VisitBooleanValue(x: SyntaxTree.BooleanValue);
		BEGIN
			IF Trace THEN TraceEnter("VisitBooleanValue") END;
			IF conditional THEN
				IF x.value THEN BrL(trueLabel)
				ELSE BrL(falseLabel)
				END;
			ELSE
				InitOperand(result,ModeValue);
				IF x.value THEN result.op := true ELSE result.op := false END;
			END;
		END VisitBooleanValue;

		PROCEDURE VisitIntegerValue(x: SyntaxTree.IntegerValue);
		BEGIN
			IF Trace THEN TraceEnter("VisitIntegerValue") END;
			InitOperand(result,ModeValue);
			IntermediateCode.InitImmediate(result.op,IntermediateCode.GetType(system,x.type),x.hvalue);
		END VisitIntegerValue;

		PROCEDURE VisitCharacterValue(x: SyntaxTree.CharacterValue);
		BEGIN
			IF Trace THEN TraceEnter("VisitCharacterValue") END;
			InitOperand(result,ModeValue);
			IntermediateCode.InitImmediate(result.op,IntermediateCode.GetType(system,x.type),ORD(x.value));
		END VisitCharacterValue;

		PROCEDURE VisitSetValue(x: SyntaxTree.SetValue);
		BEGIN
			IF Trace THEN TraceEnter("VisitSetValue") END;
			InitOperand(result,ModeValue);
			IntermediateCode.InitImmediate(result.op,IntermediateCode.GetType(system,x.type),SYSTEM.VAL(LONGINT,x.value));
		END VisitSetValue;

		PROCEDURE VisitMathArrayValue(x: SyntaxTree.MathArrayValue);
		VAR  irv: IntermediateCode.Section; name:Basic.PooledName;

			PROCEDURE RecursiveData(x: SyntaxTree.MathArrayExpression);
			VAR numberElements,i: LONGINT; expression: SyntaxTree.Expression; op: Operand;
			BEGIN
				numberElements := x.elements.Length();
				FOR i := 0 TO numberElements-1 DO
					expression := x.elements.GetExpression(i);
					IF expression IS SyntaxTree.MathArrayExpression THEN
						RecursiveData(expression(SyntaxTree.MathArrayExpression));
					ELSE
						Evaluate(expression,op);
						irv.Emit(Data(op.op));
						ReleaseOperand(op);
					END;
				END;
			END RecursiveData;

		BEGIN
			IF Trace THEN TraceEnter("VisitMathArrayValue") END;
			IF ~TryConstantDeclaration() THEN
				IF constantDeclaration = NIL THEN constantDeclaration:=BuildConstant(module.module,x,constId) END;
				Global.GetSymbolPooledName(constantDeclaration,name);
				irv := NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,constantDeclaration,commentPrintout # NIL);
				RecursiveData(x.array);
				InitOperand(result,ModeReference);
				IntermediateCode.InitAddress(result.op, addressType, irv,0);
			END
		END VisitMathArrayValue;

		PROCEDURE TryConstantDeclaration(): BOOLEAN;
		VAR constant: Sections.Section;
		BEGIN
			IF constantDeclaration = NIL THEN
				RETURN FALSE
			ELSE
				constant := module.allSections.FindBySymbolAndKind(constantDeclaration, Sections.RegularKind); (*TODO*)
				IF constant # NIL THEN
					ASSERT(constant.kind = Sections.RegularKind);
					InitOperand(result,ModeReference);
					IntermediateCode.InitAddress(result.op,addressType,constant,0);
					RETURN TRUE;
				END;
			END;
			RETURN FALSE
		END TryConstantDeclaration;

		PROCEDURE VisitConstant(x: SyntaxTree.Constant);
		BEGIN
			constantDeclaration := x;
			x.value.resolved.Accept(SELF);
		END VisitConstant;

		PROCEDURE VisitRealValue(x: SyntaxTree.RealValue);
		BEGIN
			IF Trace THEN TraceEnter("VisitRealValue") END;
			InitOperand(result,ModeValue);
			IntermediateCode.InitFloatImmediate(result.op,IntermediateCode.GetType(system,x.type),x.value);
		END VisitRealValue;

		PROCEDURE VisitStringValue(x: SyntaxTree.StringValue);
		VAR  i: LONGINT; name: Basic.PooledName;
			irv: IntermediateCode.Section; op: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitStringValue") END;
			IF ~TryConstantDeclaration() THEN
				IF constantDeclaration = NIL THEN constantDeclaration:=BuildConstant(module.module,x,constId) END;
				Global.GetSymbolPooledName(constantDeclaration,name);
				irv := NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,constantDeclaration,commentPrintout # NIL);
				FOR i := 0 TO x.length-1 DO
					IntermediateCode.InitImmediate(op,IntermediateCode.GetType(system,system.characterType),ORD(x.value[i]));
					irv.Emit(Data(op));
				END;
				InitOperand(result,ModeReference);
				IntermediateCode.InitAddress(result.op, addressType, irv,0);
				result.tag := IntermediateCode.Immediate(addressType,x.length);
			END
		END VisitStringValue;

		PROCEDURE VisitNilValue(x: SyntaxTree.NilValue);
		BEGIN
			IF Trace THEN TraceEnter("VisitNilValue") END;
			InitOperand(result,ModeValue);
			result.op := IntermediateCode.Immediate(IntermediateCode.GetType(system,x.type),0);
			result.tag := IntermediateCode.Immediate(IntermediateCode.GetType(system,x.type),0);
		END VisitNilValue;

		PROCEDURE VisitEnumerationValue(x: SyntaxTree.EnumerationValue);
		BEGIN
			IF Trace THEN TraceEnter("VisitEnumerationValue") END;
			InitOperand(result,ModeValue);
			result.op := IntermediateCode.Immediate(IntermediateCode.GetType(system,x.type),x.value);
		END VisitEnumerationValue;

		(** symbols *)

		PROCEDURE VisitImport(x: SyntaxTree.Import);
		BEGIN (* nothing to be done, might however be called via some designator module.procedure *)
		END VisitImport;

		PROCEDURE GetBaseRegister(VAR result: IntermediateCode.Operand; scope,baseScope: SyntaxTree.Scope);
		VAR left,right: IntermediateCode.Operand;level: LONGINT;
		BEGIN
			IF scope # baseScope THEN
				(* left := [fp+8] *)
				IntermediateCode.InitMemory(right,addressType,fp,ToMemoryUnits(system,2*addressType.sizeInBits));
				ReuseCopy(left,right);
				ReleaseIntermediateOperand(right);
				scope := scope.outerScope; DEC(level);
				(* { left := [left+8] } *)
				IntermediateCode.InitMemory(right,addressType,left,ToMemoryUnits(system,2*addressType.sizeInBits));
				WHILE (scope # baseScope) & (scope IS SyntaxTree.ProcedureScope) DO
					Emit(Mov(left,right));
					scope := scope.outerScope; DEC(level);
				END;
				ASSERT((scope = baseScope) OR (baseScope = NIL));
				result := left;
			ELSE
				result := fp;
			END;
		END GetBaseRegister;

		PROCEDURE VisitVariable(x: SyntaxTree.Variable);
		VAR symbol: Sections.Section;  type: SyntaxTree.Type; name: Basic.PooledName; temp: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitVariable");  END;
			type := x.type.resolved;
			IF (x.scope IS SyntaxTree.ProcedureScope) THEN (* local variable (potentially via nested procedure) *)
				InitOperand(result,ModeReference);
				GetBaseRegister(result.op,currentScope,x.scope);
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,x.offsetInBits));
			ELSIF (x.scope = moduleScope) OR (x.scope IS SyntaxTree.CellScope) THEN (* global variable *)
				InitOperand(result,ModeReference);
				Global.GetSymbolPooledName(x,name);
				symbol := NewSection(module.allSections, Sections.RegularKind,Sections.VarSection, TRUE, name,x,commentPrintout # NIL);
				IntermediateCode.InitAddress(result.op, addressType, symbol, 0);
			ELSIF x.scope IS SyntaxTree.ModuleScope THEN (* global variable in imported module *)
				InitOperand(result,ModeReference);
				Global.GetSymbolPooledName(x,name);
				(*! check for new object file, correct? *)
				IF currentCellScope # NIL THEN
					currentCellScope.AddImport(x.scope.ownerModule);
				END;
				symbol := NewSection(module.allSections, Sections.ImportedSymbolKind,Sections.VarSection, FALSE, name,x,commentPrintout # NIL);
				IntermediateCode.InitAddress(result.op, addressType, symbol, 0)
			ELSE (* field, left designator must have been emitted *)
				ASSERT(result.mode = ModeReference);
				IF result.op.mode = IntermediateCode.ModeMemory THEN
					ReuseCopy(temp,result.op);
					ReleaseIntermediateOperand(result.op);
					result.op := temp;
				END;
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,x.offsetInBits));
			END;

			IF conditional & (x.type.resolved IS SyntaxTree.BooleanType) THEN
				ValueToCondition(result);
			ELSIF type IS SyntaxTree.ProcedureType THEN
				ReleaseIntermediateOperand(result.tag);
				IF type(SyntaxTree.ProcedureType).isDelegate THEN
					IntermediateCode.InitMemory(result.tag,addressType,result.op,ToMemoryUnits(system,system.addressSize));
					UseIntermediateOperand(result.tag);
				ELSE
					result.tag := nil; (* nil *)
				END;
			ELSIF (type IS SyntaxTree.ArrayType) THEN
				ReleaseIntermediateOperand(result.tag);
				IntermediateCode.InitImmediate(result.tag,addressType,type(SyntaxTree.ArrayType).staticLength);
			ELSIF (type IS SyntaxTree.MathArrayType) THEN
				IF type(SyntaxTree.MathArrayType).form IN {SyntaxTree.Open} THEN
					ReleaseIntermediateOperand(result.tag);
					result.tag := result.op;
					UseIntermediateOperand(result.tag);
					IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,MathAdrOffset*addressType.sizeInBits));
					IntermediateCode.MakeMemory(result.op,addressType);
				END;
			ELSIF (type IS SyntaxTree.RecordType) & (type(SyntaxTree.RecordType).pointerType = NIL) THEN
				ReleaseIntermediateOperand(result.tag);
				result.tag := TypeDescriptorAdr(type);
				IF ~newObjectFile THEN
					IntermediateCode.MakeMemory(result.tag,addressType);
				END;
				UseIntermediateOperand(result.tag);
			(* tag for pointer type computed not here but during dereferencing *)
			END;
			IF Trace THEN TraceExit("VisitVariable") END;
		END VisitVariable;

		PROCEDURE VisitParameter(x: SyntaxTree.Parameter);
		VAR type: SyntaxTree.Type; basereg, mem: IntermediateCode.Operand; parameter: SyntaxTree.Parameter;adr: LONGINT; symbol: Sections.Section;
			name: Basic.PooledName; parameterType: SyntaxTree.Type; len: LONGINT;
		BEGIN
			type := x.type.resolved;
			IF Trace THEN TraceEnter("VisitParameter") END;

			IF x.ownerType IS SyntaxTree.CellType THEN
				IF ~(x.type.resolved IS SyntaxTree.PortType) THEN
					InitOperand(result,ModeReference);
					Global.GetSymbolPooledName(x,name);
					symbol := NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,x,commentPrintout # NIL);
					IntermediateCode.InitAddress(result.op, addressType, symbol, 0);
					RETURN
				ELSE
					InitOperand(result, ModeValue);
					parameter := x.ownerType(SyntaxTree.CellType).firstParameter;
					adr := 0;
					WHILE parameter # x DO
						parameterType := parameter.type;
						IF SemanticChecker.IsStaticArray(parameterType,parameterType,len) THEN INC(adr,len) ELSE INC(adr) END;
						parameter := parameter.nextParameter
					END;
					adr := backend.activeCellsSpecification.GetPortAddress(adr);
					IntermediateCode.InitImmediate(result.op,addressType,adr);
					RETURN
				END;
			ELSIF (currentScope IS SyntaxTree.ProcedureScope) & (currentScope(SyntaxTree.ProcedureScope).ownerProcedure.isConstructor) & (currentScope.outerScope IS SyntaxTree.CellScope) THEN
				InitOperand(result,ModeReference);
				Global.GetSymbolPooledName(x,name);
				symbol := NewSection(module.allSections, Sections.RegularKind,Sections.VarSection, TRUE, name,x,commentPrintout # NIL);
				IntermediateCode.InitAddress(result.op, addressType, symbol, 0);
				RETURN
			ELSE
				GetBaseRegister(basereg,currentScope,x.scope);
				InitOperand(result,ModeReference);
				result.op := basereg;
			END;

			IF IsOpenArray(type) THEN
				result.tag := basereg;
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,x.offsetInBits));
				IntermediateCode.MakeMemory(result.op,addressType);
				IF Global.IsOberonProcedure(x.ownerType) THEN
					IntermediateCode.AddOffset(result.tag,ToMemoryUnits(system,x.offsetInBits+addressType.sizeInBits));
					UseIntermediateOperand(result.tag);
				ELSE
					IntermediateCode.InitImmediate(result.tag,addressType,MAX(LONGINT)); (* non-Oberon procedure => unbounded array length *)
				END;
			ELSIF IsStaticArray(type) & (x.kind = SyntaxTree.ValueParameter) THEN
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,x.offsetInBits));
			ELSIF IsStaticArray(type) THEN
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,x.offsetInBits));
				IntermediateCode.MakeMemory(result.op,addressType);
				IntermediateCode.InitImmediate(result.tag,addressType,type(SyntaxTree.ArrayType).staticLength);
			ELSIF type IS SyntaxTree.MathArrayType THEN
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,x.offsetInBits));
				WITH type: SyntaxTree.MathArrayType DO
					IF (x.kind = SyntaxTree.ValueParameter) OR (x.kind = SyntaxTree.ConstParameter) THEN
						IF type.form = SyntaxTree.Tensor THEN
						ELSIF type.form = SyntaxTree.Open THEN
							result.tag := result.op;
							IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,MathAdrOffset*addressType.sizeInBits));
							IntermediateCode.MakeMemory(result.op,addressType);
							UseIntermediateOperand(result.tag);
						ELSIF type.form = SyntaxTree.Static THEN
							IF x.kind = SyntaxTree.ConstParameter THEN
								IntermediateCode.MakeMemory(result.op,addressType);
							END;
						ELSE HALT(100)
						END;
					ELSIF x.kind = SyntaxTree.VarParameter THEN
						IF type.form = SyntaxTree.Tensor THEN
							ToMemory(result.op,addressType,0);
						ELSIF type.form = SyntaxTree.Open THEN
							MakeMemory(mem, result.op,  addressType, 0); (* offset already added above *)
							ReuseCopy(result.tag, mem);
							ReleaseIntermediateOperand(mem);
							ReleaseIntermediateOperand(result.op);
							MakeMemory(result.op, result.tag, addressType, ToMemoryUnits(system,MathAdrOffset*addressType.sizeInBits));
						ELSIF type.form = SyntaxTree.Static THEN
							IntermediateCode.MakeMemory(result.op,addressType);
						ELSE HALT(100)
						END;
					ELSE HALT(100)
					END;
				END;
			ELSIF (x.kind = SyntaxTree.VarParameter) OR (x.kind = SyntaxTree.ConstParameter) & (type IS SyntaxTree.RecordType) THEN
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,x.offsetInBits));
				IntermediateCode.MakeMemory(result.op,addressType);

			ELSIF (x.kind = SyntaxTree.ValueParameter) OR (x.kind = SyntaxTree.ConstParameter) THEN
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,x.offsetInBits));
			END;

			IF conditional & (x.type.resolved IS SyntaxTree.BooleanType) THEN
				ValueToCondition(result);
			ELSIF type IS SyntaxTree.ProcedureType THEN
				ReleaseIntermediateOperand(result.tag);
				IF type(SyntaxTree.ProcedureType).isDelegate THEN
					IF x.kind = SyntaxTree.VarParameter THEN
						ReuseCopy(result.tag,result.op);
						IntermediateCode.AddOffset(result.tag,ToMemoryUnits(system,system.addressSize));
						IntermediateCode.MakeMemory(result.tag,addressType);
					ELSE
						IntermediateCode.InitMemory(result.tag,addressType,result.op,ToMemoryUnits(system,system.addressSize));
						UseIntermediateOperand(result.tag);
					END;
				ELSE
					result.tag := nil;
				END;
			(* tag for pointer type computed not here but during dereferencing *)
			ELSIF (type IS SyntaxTree.RecordType) & (type(SyntaxTree.RecordType).pointerType= NIL) & (x.kind IN {SyntaxTree.VarParameter, SyntaxTree.ConstParameter}) THEN
				ReleaseIntermediateOperand(result.tag);
				result.tag := basereg;
				IntermediateCode.AddOffset(result.tag,ToMemoryUnits(system,x.offsetInBits+system.addressSize));
				IntermediateCode.MakeMemory(result.tag,addressType);
				UseIntermediateOperand(result.tag);
			ELSIF (type IS SyntaxTree.RecordType) & (type(SyntaxTree.RecordType).pointerType= NIL) & (x.kind = SyntaxTree.ValueParameter) THEN
				ReleaseIntermediateOperand(result.tag);
				result.tag := TypeDescriptorAdr(type);
				IF ~newObjectFile THEN
					IntermediateCode.MakeMemory(result.tag,addressType);
				END;
				UseIntermediateOperand(result.tag);
			END;
			IF Trace THEN TraceExit("VisitParameter") END;
		END VisitParameter;

		PROCEDURE DynamicCallOperand(VAR operand: Operand; x: SyntaxTree.Procedure);
		VAR tag,reg,tmp: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("DynamicCallOperand") END;
			(* left.p: left already emitted *)
			tag := result.op; (* value of pointer to left *)
			(* get type desc *)
			tmp := result.tag;
			IntermediateCode.MakeMemory(tmp,addressType);
			(* get method adr *)
			Reuse1(reg,tmp);
			ReleaseIntermediateOperand(tmp);
			Emit(Add(reg,tmp,IntermediateCode.Immediate(addressType, ToMemoryUnits(system,system.addressSize  *(MethodTable - x.methodNumber)))));

			InitOperand(operand,ModeReference);
			(* then operand.op contains the method adr and operand.tag contains the potential self pointer value *)
			operand.op := reg;
			operand.tag := tag;
			IF Trace THEN TraceExit("DynamicCallOperand") END;
		END DynamicCallOperand;

		PROCEDURE StaticCallOperand(VAR operand: Operand; x: SyntaxTree.Procedure);
		VAR source: IntermediateCode.Section; tag,reg: IntermediateCode.Operand; name:Basic.PooledName; sectionType: SHORTINT;
		BEGIN
			IF Trace THEN TraceEnter("StaticCallOperand") END;
			tag := nil;
			GetCodeSectionNameForSymbol(x, name); (* nopov *)
			IF x.isInline THEN
				sectionType := Sections.InlineCodeSection;
			ELSE
				sectionType := Sections.CodeSection;
			END;
			IF (x.scope.ownerModule = module.module) THEN
				source := NewSection(module.allSections, Sections.RegularKind,sectionType, TRUE, name,x,commentPrintout # NIL);
			ELSIF (sectionType = Sections.InlineCodeSection) & (x.procedureScope.body.code.sourceCode # NIL) THEN
				source := NewSection(module.allSections, Sections.RegularKind,sectionType, TRUE, name,x,commentPrintout # NIL);
				IF source.pc = 0 THEN (* no code yet *)
					source.Emit(Asm(x.procedureScope.body.code.sourceCode,x.position));
				END;
			ELSE
				IF currentCellScope # NIL THEN
					currentCellScope.AddImport(x.scope.ownerModule);
				END;
				source := NewSection(module.allSections, Sections.ImportedSymbolKind,sectionType, FALSE, name,x,commentPrintout # NIL);
			END;
			IntermediateCode.InitAddress(reg, addressType, source , 0);
			InitOperand(operand,ModeValue);
			operand.op := reg;
			operand.tag := tag;
			IF Trace THEN TraceExit("StaticCallOperand") END;
		END StaticCallOperand;

		PROCEDURE VisitProcedure(x: SyntaxTree.Procedure);
		(* handle expressions of the form designator.procedure or procedure *)
		BEGIN
			IF Trace THEN TraceEnter("VisitProcedure") END;
			IF  x.type(SyntaxTree.ProcedureType).isDelegate THEN
				DynamicCallOperand(result,x);
			ELSIF x.isInline THEN
				StaticCallOperand(result,x);
			ELSE
				StaticCallOperand(result,x);
			END;
			IF Trace THEN TraceExit("VisitProcedure") END;
		END VisitProcedure;

		PROCEDURE VisitOperator(x: SyntaxTree.Operator);
		BEGIN
			VisitProcedure(x);
		END VisitOperator;

		(** statements *)

		PROCEDURE VisitProcedureCallStatement(x: SyntaxTree.ProcedureCallStatement);
		BEGIN
			IF Trace THEN TraceEnter("VisitProcedureCallStatement") END;
			Expression(x.call);
			IF (x.call.type # NIL) THEN (* WINAPI call: procedure returning unused value *)
				ReleaseOperand(result)
			END;
			IF Trace THEN TraceExit("VisitProcedureCallStatement") END;
		END VisitProcedureCallStatement;

		PROCEDURE AssignMathArray(left,right: SyntaxTree.Expression);
		VAR leftType, rightType: SyntaxTree.MathArrayType;
			leftBase, rightBase: SyntaxTree.Type;
			procedureName,s: SyntaxTree.String;
			arrayBase: SyntaxTree.Module; saved: RegisterEntry;  procedure: SyntaxTree.Procedure; parameter: SyntaxTree.Parameter;
			size: LONGINT; rightKind: LONGINT;
			dummy: IntermediateCode.Operand; (* nopov *)

		CONST moduleName = "FoxArrayBase";

			PROCEDURE OpenArray(from: SyntaxTree.MathArrayType): SyntaxTree.MathArrayType;
			VAR result: SyntaxTree.MathArrayType; base: SyntaxTree.Type;
			BEGIN
				base := from(SyntaxTree.MathArrayType).arrayBase.resolved;
				IF base IS SyntaxTree.MathArrayType THEN
					base := OpenArray(base(SyntaxTree.MathArrayType));
				END;
				result := SyntaxTree.NewMathArrayType(left.position,currentScope,SyntaxTree.Open);
				result.SetArrayBase(base);
				RETURN result
			END OpenArray;

		BEGIN
			IF AddImport(moduleName,arrayBase,TRUE) THEN
				SaveRegisters();ReleaseUsedRegisters(saved);
				leftType := left.type.resolved(SyntaxTree.MathArrayType);
				rightType := right.type.resolved(SyntaxTree.MathArrayType);
				leftBase := SemanticChecker.ArrayBase(leftType,MAX(LONGINT));
				rightBase := SemanticChecker.ArrayBase(rightType,MAX(LONGINT));
				ASSERT(leftBase.resolved = rightBase.resolved);

				IF leftType.form = SyntaxTree.Tensor THEN
					procedureName := "CopyTensor"; rightKind := SyntaxTree.ValueParameter;
				ELSIF leftType.form = SyntaxTree.Open THEN
					procedureName := "CopyArray"; rightKind := SyntaxTree.VarParameter;
				ELSIF leftType.form = SyntaxTree.Static THEN
					procedureName := "CopyArray";rightKind := SyntaxTree.VarParameter;
					leftType := OpenArray(leftType); (* necessary since copy procedure presumes an open array *)
				END;

				procedure := arrayBase.moduleScope.FindProcedure(SyntaxTree.NewIdentifier(procedureName));
				IF procedure = NIL THEN
					s := "Instruction not supported on target, emulation procedure ";
					Strings.Append(s,moduleName);
					Strings.Append(s,".");
					Strings.Append(s,procedureName);
					Strings.Append(s," not present");
					Error(position,s);
				ELSE
					parameter := SyntaxTree.NewParameter(left.position,procedure.type(SyntaxTree.ProcedureType),SyntaxTree.NewIdentifier("temp"), SyntaxTree.VarParameter);
					parameter.SetType(leftType);
					parameter.SetAccess(SyntaxTree.Internal);
					PushParameter(left,parameter,SyntaxTree.OberonCallingConvention, FALSE, dummy); (* nopov *)
					parameter.SetKind(rightKind);
					PushParameter(right,parameter,SyntaxTree.OberonCallingConvention, FALSE, dummy); (* nopov *)
					size := ToMemoryUnits(system,system.SizeOf(rightBase));
					Emit(Push(IntermediateCode.Immediate(int32,size)));
					StaticCallOperand(result,procedure);
					Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
					ReleaseOperand(result);
				END;
				RestoreRegisters(saved);
			END;

		END AssignMathArray;

		PROCEDURE Assign(left,right: SyntaxTree.Expression);
		VAR
			leftO, rightO: Operand;
			mem: IntermediateCode.Operand;
			leftType, rightType: SyntaxTree.Type;
			size: LONGINT;

			PROCEDURE CanPassAsResultParameter(right: SyntaxTree.Expression): BOOLEAN;
			VAR procedureType: SyntaxTree.ProcedureType;
			BEGIN
				IF ReturnedAsParameter(right.type) THEN
					IF right IS SyntaxTree.ProcedureCallDesignator THEN
						procedureType := right(SyntaxTree.ProcedureCallDesignator).left.type.resolved(SyntaxTree.ProcedureType);
						RETURN procedureType.callingConvention = SyntaxTree.OberonCallingConvention
					ELSIF right IS SyntaxTree.BuiltinCallDesignator THEN
						WITH right: SyntaxTree.BuiltinCallDesignator DO
							IF right.id = Global.Reshape THEN RETURN TRUE
							ELSIF right.id = Global.systemZeroCopy THEN RETURN TRUE
							END;
						END;
					END;
				END;
				RETURN FALSE
			END CanPassAsResultParameter;

		BEGIN
			ASSERT(left.type # NIL); ASSERT(right.type # NIL);
			leftType := left.type.resolved; rightType:= right.type.resolved;

			IF CanPassAsResultParameter(right) THEN
				procedureResultDesignator := left(SyntaxTree.Designator);
				Expression(right);
			ELSIF leftType IS SyntaxTree.RangeType THEN
				(* LHS is of array range type *)
				ASSERT(rightType IS SyntaxTree.RangeType); (* ensured by the checker *)
				Evaluate(right, rightO);
				Designate(left, leftO);(* The order is crucial. Do not reorder emission of left and right *)

				(* first *)
				MakeMemory(mem, leftO.op, IntermediateCode.GetType(system, system.longintType), 0);
				Emit(Mov(mem, rightO.op));
				ReleaseIntermediateOperand(mem);

				(* last *)
				MakeMemory(mem, leftO.op, IntermediateCode.GetType(system, system.longintType), ToMemoryUnits(system, system.SizeOf(system.longintType)));
				Emit(Mov(mem, rightO.tag));
				ReleaseIntermediateOperand(mem);

				(* step *)
				MakeMemory(mem, leftO.op, IntermediateCode.GetType(system, system.longintType), 2 * ToMemoryUnits(system, system.SizeOf(system.longintType)));
				Emit(Mov(mem, rightO.extra));
				ReleaseIntermediateOperand(mem);

				ReleaseOperand(rightO);
				ReleaseOperand(leftO)
			ELSIF (leftType IS SyntaxTree.BasicType) OR (leftType IS SyntaxTree.PointerType) OR (leftType IS SyntaxTree.EnumerationType)
				OR (leftType IS SyntaxTree.PortType) THEN
				(* rightO := leftO;*)
				Evaluate(right,rightO);
				(* DO NOT REORDER EMISSION OF LEFT AND RIGHT OPERAND *)
				Designate(left,leftO);
				MakeMemory(mem,leftO.op,IntermediateCode.GetType(system,left.type),0);
				destination := mem;
				ReleaseOperand(leftO);
				IF destination.mode # IntermediateCode.Undefined THEN
					Emit(Mov(destination,rightO.op));
				END;
				ReleaseOperand(rightO);
				ReleaseIntermediateOperand(mem);
				IntermediateCode.InitOperand(destination);
			ELSIF (leftType IS SyntaxTree.ProcedureType) THEN
				Evaluate(right,rightO);
				Designate(left,leftO);
				MakeMemory(mem,leftO.op,addressType,0);
				Emit(Mov(mem,rightO.op));
				ReleaseIntermediateOperand(mem);
				IF leftType(SyntaxTree.ProcedureType).isDelegate THEN
					(* delegate *)
					(*
					MakeMemory(leftO.tag,leftO.tag,addressType); no! is already memory
					*)
					Emit(Mov(leftO.tag,rightO.tag));
				END;
				ReleaseOperand(leftO);
				ReleaseOperand(rightO);
			ELSIF (leftType IS SyntaxTree.RecordType) THEN
				Designate(right,rightO);
				Designate(left,leftO);
				size := ToMemoryUnits(system,system.SizeOf(leftType));
				Emit(Copy(leftO.op,rightO.op,IntermediateCode.Immediate(addressType,size)));
				ReleaseOperand(leftO); ReleaseOperand(rightO);
			ELSIF (leftType IS SyntaxTree.ArrayType) THEN
				IF (rightType IS SyntaxTree.StringType) THEN
					CopyString(left,right);
				ELSIF (rightType(SyntaxTree.ArrayType).staticLength # 0) & (leftType(SyntaxTree.ArrayType).staticLength # 0) THEN
					Designate(right,rightO);
					Designate(left,leftO);
					size := ToMemoryUnits(system,system.SizeOf(rightType));
					Emit(Copy(leftO.op, rightO.op, IntermediateCode.Immediate(addressType,size)));
					ReleaseOperand(leftO); ReleaseOperand(rightO);
				ELSE
					HALT(201)
				END;
			ELSIF (leftType IS SyntaxTree.MathArrayType) THEN
				AssignMathArray(left,right);
			ELSE
				HALT(200);
			END;
		END Assign;

		PROCEDURE VisitAssignment(x: SyntaxTree.Assignment);
		BEGIN
			IF Trace THEN TraceEnter("VisitAssignment") END;
			Assign(x.left,x.right);
			IF Trace THEN TraceExit("VisitAssignment") END;
		END VisitAssignment;

		PROCEDURE VisitIfStatement(x: SyntaxTree.IfStatement);
		VAR end: Label; i,elsifs: LONGINT; elsif: SyntaxTree.IfPart;

			PROCEDURE IfPart(if: SyntaxTree.IfPart);
			VAR true, false: Label;
			BEGIN
				true := NewLabel();
				false := NewLabel();
				Condition(if.condition,true,false);
				SetLabel(true);
				StatementSequence(if.statements);
				BrL(end);
				SetLabel(false);
			END IfPart;

		BEGIN
			IF Trace THEN TraceEnter("VisitIfStatement") END;
			end := NewLabel();
			IfPart(x.ifPart);
			elsifs := x.ElsifParts();
			FOR i := 0 TO elsifs-1 DO
				elsif := x.GetElsifPart(i);
				IfPart(elsif);
			END;
			IF x.elsePart # NIL THEN
				StatementSequence(x.elsePart);
			END;
			SetLabel(end);
			IF Trace THEN TraceExit("VisitIfStatement") END;
		END VisitIfStatement;

		PROCEDURE WithPart(x: SyntaxTree.WithPart; VAR falseL, endL: Label);
		VAR trueL: Label; res: Operand; recordType: SyntaxTree.RecordType;
		BEGIN
			(*IF x.variable.type.resolved = x.type.resolved THEN
				(* always true, do nothing *)
			ELSE*)
			Designate(x.variable,res);
			IF IsPointerToRecord(x.variable.type,recordType) THEN
				Dereference(res,recordType)
			END;
			trueL := NewLabel();
			TypeTest(res.tag,x.type,trueL,falseL);
			ReleaseOperand(res);
			SetLabel(trueL);
			StatementSequence(x.statements);
			BrL(endL);
		END WithPart;

		PROCEDURE VisitWithStatement(x: SyntaxTree.WithStatement);
		VAR endL,falseL: Label;i: LONGINT;
		BEGIN
			IF Trace THEN TraceEnter("VisitWithStatement") END;

			endL := NewLabel();
			FOR i := 0 TO x.WithParts()-1 DO
				falseL := NewLabel();
				WithPart(x.GetWithPart(i),falseL,endL);
				SetLabel(falseL);
			END;
			IF x.elsePart = NIL THEN
				IF ~backend.noRuntimeChecks THEN
					Emit(Trap(WithTrap));
				END;
			ELSE
				StatementSequence(x.elsePart)
			END;
			SetLabel(endL);
			IF Trace THEN TraceExit("VisitWithStatement") END;
		END VisitWithStatement;

		PROCEDURE VisitCaseStatement(x: SyntaxTree.CaseStatement);
		VAR var: Operand; jmp,res,op,tmp: IntermediateCode.Operand; j,i,size: LONGINT; part: SyntaxTree.CasePart; constant: SyntaxTree.CaseConstant;
			out,else: Label; label: Label;
			fixups: POINTER TO ARRAY OF Label; section: IntermediateCode.Section; name: Basic.PooledName; string: ARRAY 32 OF CHAR;
			symbol: SyntaxTree.Symbol;
		BEGIN
			(*! split case statement into if-elsif statements for large case label lists *)
			IF Trace THEN TraceEnter("VisitCaseStatement") END;
			size := x.max-x.min+1;
			IF (size<0) OR (size > 1024*1024) THEN Error(x.position,"implementation restriction: case table size too large"); RETURN
			END;
			Evaluate(x.variable,var);
			ReuseCopy(tmp,var.op);
			ReleaseIntermediateOperand(var.op);
			var.op := tmp;
			Emit(Sub(var.op,var.op,IntermediateCode.Immediate(IntermediateCode.GetType(system,x.variable.type),x.min)));
			Convert(var.op,addressType);
			size := x.max-x.min+1;
			else := NewLabel();
			BrgeL(else,var.op,IntermediateCode.Immediate(addressType,size));
			(*
			UniqueId(name,module.module,"case",caseId);
			*)
			string := "@case"; Basic.AppendNumber(string, caseId); INC(caseId);
			Basic.InitPooledName(name);
			name[0] := module.module.name;
			name[1] := Basic.MakeString(string);
			symbol := SyntaxTree.NewSymbol(name[1]);
			symbol.SetScope(moduleScope);
			NEW(fixups,size); FOR i := 0 TO size-1 DO fixups[i] := NIL END;
			section := NewSection(module.allSections,Sections.CaseTableKind, Sections.ConstSection,TRUE, name,SyntaxTree.NewSymbol(name[1]),commentPrintout # NIL);
			IntermediateCode.InitAddress(jmp, addressType, section,0);
			ReuseCopy(res,var.op);
			ReleaseOperand(var);
			Emit(Mul(res,res,IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.addressSize))));
			Emit(Add(res,res,jmp));
			IntermediateCode.MakeMemory(res,addressType);
			Emit(Br(res));
			ReleaseIntermediateOperand(res);
			out := NewLabel();
			FOR i := 0 TO x.caseParts.Length()-1 DO (* case parts *)
				part := x.GetCasePart(i);
				constant := part.firstConstant;
				label := NewLabel();
				SetLabel(label);
				WHILE(constant # NIL) DO (* case labels for this case part *)
					FOR j := constant.min TO constant.max DO
						fixups[j-x.min] := label;
					END;
					constant := constant.next;
				END;
				StatementSequence(part.statements);
				BrL(out);
			END;
			SetLabel(else);
			FOR i := 0 TO size-1 DO
				IF fixups[i] = NIL THEN
					fixups[i] := else;
				END;
			END;
			IF x.elsePart # NIL THEN
				StatementSequence(x.elsePart);
			ELSIF ~backend.noRuntimeChecks THEN
				Emit(Trap(CaseTrap));
			END;
			SetLabel(out);
			FOR i := 0 TO size-1 DO
				IntermediateCode.InitAddress(op, addressType, fixups[i].section, fixups[i].pc);
				section.Emit(Data(op));
			END;
			IF Trace THEN TraceExit("VisitCaseStatement") END;
		END VisitCaseStatement;


		PROCEDURE VisitWhileStatement(x: SyntaxTree.WhileStatement);
		VAR start: Label; true,false: Label;
		BEGIN
			IF Trace THEN TraceEnter("VisitWhileStatement") END;
			start := NewLabel();
			true := NewLabel();
			false := NewLabel();
			SetLabel(start);
			Condition(x.condition,true,false);
			SetLabel(true);
			StatementSequence(x.statements);
			BrL(start);
			SetLabel(false);
			IF Trace THEN TraceExit("VisitWhileStatement") END;
		END VisitWhileStatement;

		PROCEDURE VisitRepeatStatement(x: SyntaxTree.RepeatStatement);
		VAR false,true: Label;
		BEGIN
			IF Trace THEN TraceEnter("VisitRepeatStatement") END;
			true := NewLabel();
			false := NewLabel();
			SetLabel(false);
			StatementSequence(x.statements);
			Condition(x.condition,true,false);
			SetLabel(true);
			IF Trace THEN TraceExit("VisitRepeatStatement") END;
		END VisitRepeatStatement;

		PROCEDURE VisitForStatement(x: SyntaxTree.ForStatement);
		VAR
			binary: SyntaxTree.BinaryExpression; start,true,false : Label; cmp: LONGINT; by: HUGEINT;
			temporaryVariable: SyntaxTree.Variable;
			temporaryVariableDesignator : SyntaxTree.Designator;
		BEGIN
			IF Trace THEN TraceEnter("VisitForStatement") END;
			true := NewLabel();
			false := NewLabel();
			start := NewLabel();

			Assign(x.variable,x.from);
			temporaryVariable := GetTemporaryVariable(x.variable.type);
			temporaryVariableDesignator := SyntaxTree.NewSymbolDesignator(SemanticChecker.InvalidPosition, NIL, temporaryVariable);
			temporaryVariableDesignator.SetType(x.variable.type.resolved);


			Assign(temporaryVariableDesignator,x.to);
			IF x.by = NIL THEN by := 1 ELSE by := x.by.resolved(SyntaxTree.IntegerValue).hvalue END;
			IF by > 0 THEN
				cmp := Scanner.LessEqual
			ELSE
				cmp := Scanner.GreaterEqual
			END;
			binary := SyntaxTree.NewBinaryExpression(0,x.variable,temporaryVariableDesignator,cmp);
			binary.SetType(system.booleanType);

			SetLabel(start);


			Condition(binary,true,false);
			SetLabel(true);
			StatementSequence(x.statements);

			binary := SyntaxTree.NewBinaryExpression(0,x.variable,x.by,Scanner.Plus);
			binary.SetType(x.variable.type);
			Assign(x.variable,binary);

			BrL(start);
			SetLabel(false);
			IF Trace THEN TraceExit("VisitForStatement") END;
		END VisitForStatement;

		PROCEDURE VisitLoopStatement(x: SyntaxTree.LoopStatement);
		VAR prevLoop,start: Label;
		BEGIN
			IF Trace THEN TraceEnter("VisitLoopStatement") END;
			start := NewLabel();
			prevLoop := currentLoop;
			SetLabel(start);
			currentLoop := NewLabel();
			StatementSequence(x.statements);
			BrL(start);
			SetLabel(currentLoop);
			currentLoop := prevLoop;
			IF Trace THEN TraceExit("VisitLoopStatement") END;
		END VisitLoopStatement;

		PROCEDURE VisitExitStatement(x: SyntaxTree.ExitStatement);
		VAR outer: SyntaxTree.Statement;
		BEGIN
			IF Trace THEN TraceEnter("VisitExitStatement") END;
			IF locked  THEN (* r if we jump out of an exclusive block *)
				outer := x.outer;
				WHILE ~(outer IS SyntaxTree.LoopStatement) & ~((outer IS SyntaxTree.StatementBlock) & outer(SyntaxTree.StatementBlock).isExclusive) DO
					outer := outer.outer;
				END;
				IF ~(outer IS SyntaxTree.LoopStatement) THEN
					Lock(FALSE);
				END;
			END;
			BrL(currentLoop);
			IF Trace THEN TraceExit("VisitExitStatement") END;
		END VisitExitStatement;

		PROCEDURE VisitReturnStatement(x: SyntaxTree.ReturnStatement);
		VAR
			expression, parameterDesignator: SyntaxTree.Expression;
			type: SyntaxTree.Type;
			res, right: Operand;
			left, size, mem, reg: IntermediateCode.Operand;
			parameter: SyntaxTree.Parameter;
			procedure: SyntaxTree.Procedure;
			procedureType: SyntaxTree.ProcedureType;
			parSize, returnTypeOffset: LONGINT;
			delegate: BOOLEAN;
		BEGIN
			IF Trace THEN TraceEnter("VisitReturnStatement") END;
			expression := x.returnValue;
			procedure := currentScope(SyntaxTree.ProcedureScope).ownerProcedure;
			procedureType := procedure.type(SyntaxTree.ProcedureType);
			IF expression # NIL THEN
				type := expression.type.resolved;
				IF (expression IS SyntaxTree.ResultDesignator) THEN
					IF locked THEN Lock(FALSE) END;
					IF profile THEN ProfilerEnterExit(numberProcedures,FALSE) END;
					(* "RETURN RESULT" -> no assignment, it is assumed that result has been written to return parameter via structured return type *)
				ELSIF (type IS SyntaxTree.BasicType) & ~(type IS SyntaxTree.RangeType) & ~SemanticChecker.IsPointerType(type) OR (procedureType.callingConvention # SyntaxTree.OberonCallingConvention) THEN
					(* return without structured return parameter *)
					Evaluate(expression,res);
					delegate := (type IS SyntaxTree.ProcedureType) & (type(SyntaxTree.ProcedureType).isDelegate);
					IF locked OR profile THEN
						Emit(Push(res.op));
						IF delegate THEN HALT(200) END;
						ReleaseOperand(res);
						IF locked THEN Lock(FALSE) END;
						IF profile THEN ProfilerEnterExit(numberProcedures,FALSE) END;
						reg := NewRegisterOperand(res.op.type);
						Emit(Pop(reg));
						Emit(Return(reg));
						ReleaseIntermediateOperand(reg);
					ELSE
						Emit(Return(res.op));
						ReleaseOperand(res);
					END;
				ELSIF (type IS SyntaxTree.RecordType) OR (type IS SyntaxTree.ArrayType) OR (type IS SyntaxTree.RangeType) OR SemanticChecker.IsPointerType(type)
				THEN
					(* return using structured return parameter *)
					ASSERT((type IS SyntaxTree.RecordType) OR (type IS SyntaxTree.RangeType) OR (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form = SyntaxTree.Static)
						OR SemanticChecker.IsPointerType(type));
					(* parameter := currentScope(SyntaxTree.ProcedureScope).FindParameter(Global.ReturnParameterName); *)
					parameter :=procedureType.returnParameter;
					ASSERT(parameter # NIL);
					returnTypeOffset := parameter.offsetInBits;
					(*
					IF parameter# NIL THEN
						returnTypeOffset := parameter.offsetInBits + system.SizeOfParameter(parameter);
						INC(returnTypeOffset,(-returnTypeOffset) MOD system.AlignmentOf(system.parameterAlignment,parameter.type));
					ELSE
						returnTypeOffset := system.offsetFirstParameter
					END;
					*)
					left := IntermediateCode.Memory(addressType,fp,ToMemoryUnits(system,returnTypeOffset));

					IF type IS SyntaxTree.RangeType THEN
						(* array range type *)
						Evaluate(expression, right);

						MakeMemory(mem, left, IntermediateCode.GetType(system, system.longintType), 0);
						Emit(Mov(mem, right.op)); (* first *)
						ReleaseIntermediateOperand(mem);

						MakeMemory(mem, left, IntermediateCode.GetType(system, system.longintType), ToMemoryUnits(system, system.SizeOf(system.longintType)));
						Emit(Mov(mem, right.tag)); (* last *)
						ReleaseIntermediateOperand(mem);

						MakeMemory(mem, left, IntermediateCode.GetType(system, system.longintType), 2 * ToMemoryUnits(system, system.SizeOf(system.longintType)));
						Emit(Mov(mem, right.extra)); (* step *)
						ReleaseIntermediateOperand(mem);

						ReleaseOperand(right);
					ELSIF SemanticChecker.IsPointerType(type) THEN
						Evaluate(expression, right);
						MakeMemory(mem, left, IntermediateCode.GetType(system, system.addressType), 0);
						Emit(Mov(mem, right.op)); (* step *)
						ReleaseOperand(right); ReleaseIntermediateOperand(mem);
					ELSE
						(* not array range type *)
						Designate(expression, right);
						IF type IS SyntaxTree.RecordType THEN
							size := IntermediateCode.Memory(addressType, fp, ToMemoryUnits(system, returnTypeOffset + system.addressSize));
						ELSE ASSERT( (type IS SyntaxTree.ArrayType) OR (type IS SyntaxTree.MathArrayType));
							size := IntermediateCode.Immediate(addressType, ToMemoryUnits(system, system.SizeOf(type)));
						END;
						Emit(Copy(left, right.op, size));
						ReleaseOperand(right)
					END;
					ReleaseIntermediateOperand(left);
					IF locked THEN Lock(FALSE) END;
					IF profile THEN ProfilerEnterExit(numberProcedures,FALSE) END;
				ELSIF (type IS SyntaxTree.MathArrayType) OR (type IS SyntaxTree.ProcedureType) THEN
					parameter := procedureType.returnParameter;
					checker.SetCurrentScope(currentScope);

					IF parameter = NIL THEN
						Error(procedure.position, "structured return of parameter of procedure not found");
					ELSE
						parameterDesignator := checker.NewSymbolDesignator(expression.position,NIL,parameter);
						Assign(parameterDesignator,expression);
					END;
					IF locked THEN Lock(FALSE) END;
					IF profile THEN ProfilerEnterExit(numberProcedures,FALSE) END;
				ELSE
					HALT(200);
				END;
			ELSE
				IF locked THEN Lock(FALSE) END;
				IF profile THEN ProfilerEnterExit(numberProcedures,FALSE) END;
			END;
			IF procedureType.callingConvention = SyntaxTree.CCallingConvention THEN parSize := 0
			ELSE parSize := ProcedureParametersSize(system,procedure);
			END;

			Emit(Leave(procedure.type(SyntaxTree.ProcedureType).callingConvention));
			Emit(Exit(parSize));
			IF Trace THEN TraceExit("VisitReturnStatement") END;
		END VisitReturnStatement;

		PROCEDURE MakeAwaitProcedure(x: SyntaxTree.AwaitStatement): SyntaxTree.Procedure;
		VAR procedure: SyntaxTree.Procedure; procedureType: SyntaxTree.ProcedureType; procedureScope: SyntaxTree.ProcedureScope;
			identifier: SyntaxTree.Identifier; body: SyntaxTree.Body; returnStatement : SyntaxTree.ReturnStatement;
			statements: SyntaxTree.StatementSequence;
			name, suffix: Scanner.StringType;
		BEGIN
			Strings.IntToStr(awaitProcCounter,suffix);
			Strings.Concat("@AwaitProcedure",suffix,name);
			identifier := SyntaxTree.NewIdentifier(name);
			INC(awaitProcCounter);
			ASSERT(currentScope IS SyntaxTree.ProcedureScope);
			procedureScope := SyntaxTree.NewProcedureScope(currentScope);
			ASSERT(procedureScope.outerScope IS SyntaxTree.ProcedureScope);
			procedure := SyntaxTree.NewProcedure(x.position,identifier,procedureScope);
			procedure.SetAccess(SyntaxTree.Hidden);
			procedure.SetScope(currentScope);
			procedureType := SyntaxTree.NewProcedureType(x.position,currentScope);
			procedureType.SetReturnType(system.booleanType);
			procedure.SetType(procedureType);
			body := SyntaxTree.NewBody(x.position,procedureScope);
			procedureScope.SetBody(body);
			returnStatement := SyntaxTree.NewReturnStatement(x.position,body);
			returnStatement.SetReturnValue(x.condition);
			statements := SyntaxTree.NewStatementSequence();
			statements.AddStatement(returnStatement);
			body.SetStatementSequence(statements);
			currentScope.AddProcedure(procedure);
			RETURN procedure
		END MakeAwaitProcedure;

		PROCEDURE VisitAwaitStatement(x: SyntaxTree.AwaitStatement);
		VAR proc: SyntaxTree.Procedure; res: IntermediateCode.Operand; symbol: Sections.Section;
			call: IntermediateCode.Operand; label: Label; name: Basic.PooledName;
		BEGIN
			IF Trace THEN TraceEnter("VisitAwaitStatement") END;
			proc := MakeAwaitProcedure(x);
			Emit(Push(fp));
			Global.GetSymbolPooledName(proc,name);
			symbol := NewSection(module.allSections, Sections.RegularKind,Sections.CodeSection, TRUE, name,proc,commentPrintout # NIL);
			IntermediateCode.InitAddress(call,addressType,symbol,0);
			res := NewRegisterOperand(IntermediateCode.GetType(system,system.booleanType));
			Emit(Call(call,ProcedureParametersSize(system,proc)));
			Emit(Result(res));
			(*
			AcquireThisRegister(IntermediateCode.GetType(system,system.booleanType),IntermediateCode.Result);
			IntermediateCode.InitRegister(res,IntermediateCode.GetType(system,system.booleanType),IntermediateCode.Result);
			*)
			InitOperand(result,ModeValue);
			result.op := res;
			label := NewLabel();
			BreqL(label, result.op, true);
			ReleaseOperand(result);
			symbol := NewSection(module.allSections, Sections.RegularKind,Sections.CodeSection, TRUE, name,proc,commentPrintout # NIL);
			IntermediateCode.InitAddress(res, addressType, symbol,0);
			Emit(Push(res));
			Emit(Push(fp));
			PushSelfPointer();
			Emit(Push(nil));
			IF newObjectFile THEN CallThis("Objects","Await") ELSE SysCall(SysAwait) END;
			SetLabel(label);
			IF Trace THEN TraceExit("VisitAwaitStatement") END;
		END VisitAwaitStatement;

		PROCEDURE StatementSequence(x: SyntaxTree.StatementSequence);
		VAR statement: SyntaxTree.Statement;  i: LONGINT; (* pos: LONGINT; *)
		BEGIN
			FOR i := 0 TO x.Length() - 1 DO
				statement := x.GetStatement( i );
				Statement(statement);
			END;
		END StatementSequence;

		PROCEDURE PushSelfPointer;
		VAR scope: SyntaxTree.Scope;  op: Operand; moduleSection: IntermediateCode.Section; moduleOffset: LONGINT;
		BEGIN
			scope := currentScope;
			WHILE(scope.outerScope IS SyntaxTree.ProcedureScope) DO
				scope := scope.outerScope;
			END;
			IF scope.outerScope IS SyntaxTree.ModuleScope THEN
				IF ~newObjectFile THEN
					Symbol(moduleSelf,op);
					IntermediateCode.MakeMemory(op.op,addressType);
				ELSE
					moduleSection := MetaModuleSection(SELF,module);
					moduleOffset := moduleSection.pc;
					op.op := IntermediateCode.Address(addressType, moduleSection, moduleOffset);
				END;
			ELSE
				GetBaseRegister(op.op,currentScope,scope);
				IntermediateCode.AddOffset(op.op,ToMemoryUnits(system,2*addressType.sizeInBits));
				IntermediateCode.MakeMemory(op.op,addressType);
			END;
			Emit(Push(op.op));
			ReleaseOperand(op);
		END PushSelfPointer;

		PROCEDURE Lock(lock: BOOLEAN);
		BEGIN
			IF Trace THEN TraceEnter("Lock") END;
			CheckRegistersFree(); (* no register may be in use as operands should not be preserved over the lock / unlock boundary *)
			IF dump # NIL THEN
				IF lock THEN dump.String("lock") ELSE dump.String("unlock") END;
				dump.Ln;dump.Update;
			END;
			PushSelfPointer;
			Emit(Push(true));
			IF lock THEN
				IF newObjectFile THEN CallThis("Objects","Lock")
				ELSE SysCall(SysLock)
				END;
			ELSE
				IF newObjectFile THEN CallThis("Objects","Unlock");
				ELSE SysCall(SysUnlock)
				END
			END;
			IF Trace THEN TraceExit("Lock") END;
		END Lock;

		PROCEDURE VisitStatementBlock(x: SyntaxTree.StatementBlock);
		BEGIN
			IF Trace THEN TraceEnter("VisitStatementBlock") END;
			IF emitLabels THEN Emit(LabelInstruction(x.position)) END;

			IF x.isExclusive THEN Lock(TRUE); ASSERT(~locked);  locked := TRUE; END;
			IF x.statements # NIL THEN
				StatementSequence(x.statements);
			END;
			IF x.isExclusive THEN Lock(FALSE); ASSERT(locked); locked := FALSE; END;
			IF Trace THEN TraceExit("VisitStatementBlock") END;
		END VisitStatementBlock;

		PROCEDURE VisitCode(x: SyntaxTree.Code);
		VAR (*  inline: Sections.CellNet; symbol: SyntaxTree.Symbol; *)
		BEGIN
			IF Trace THEN TraceEnter("VisitCode") END;
			Emit(Asm(x.sourceCode,x.position));
			(*
			NEW(inline,x."inline",cg.pc,x);
			cg.Inline(inline);
			symbol := currentScope(SyntaxTree.ProcedureScope).ownerProcedure;
			IF symbol(SyntaxTree.Procedure).HasFlag(SyntaxTree.InlineFlag) THEN
				module.inlineCode.Add(inline)
			END;
			*)
			IF Trace THEN TraceExit("VisitCode") END;
		END VisitCode;

		PROCEDURE ParameterCopies(x: SyntaxTree.ProcedureType);
		VAR parameter: SyntaxTree.Parameter; type: SyntaxTree.Type; op: Operand; temp,size,par: IntermediateCode.Operand;
			const: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("ParameterCopies") END;
			parameter := x.firstParameter;
			WHILE parameter # NIL DO
				IF parameter.kind = SyntaxTree.ValueParameter THEN
					type := parameter.type.resolved;
					IF IsOpenArray(type) THEN
						VisitParameter(parameter);
						op := result;
						temp := GetDynamicSize(type,op.tag);
						ReuseCopy(size,temp);
						ReleaseIntermediateOperand(temp);
						const := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,-system.addressSize)); (* alignment *)
						Emit(Sub(size,sp,size));
						Emit(And(size,size,const));
						Emit(Mov(sp,size));
						par := fp;
						IntermediateCode.AddOffset(par,ToMemoryUnits(system,parameter.offsetInBits));
						ReleaseIntermediateOperand(size);
						size := GetDynamicSize(type,op.tag);
						Emit(Copy(sp,op.op,size));
						ReleaseIntermediateOperand(size);
						ReleaseOperand(op);
						IntermediateCode.MakeMemory(par,addressType);
						Emit(Mov(par,sp));
					END;
				END;
				parameter := parameter.nextParameter;
			END;
			IF Trace THEN TraceExit("ParameterCopies") END;
		END ParameterCopies;

		PROCEDURE InitVariables(scope: SyntaxTree.Scope);
		VAR x: SyntaxTree.Variable;
		BEGIN
			x := scope.firstVariable;
			WHILE x # NIL DO
				InitVariable(x);
				x := x.nextVariable;
			END;
		END InitVariables;

		PROCEDURE Body(x: SyntaxTree.Body; scope: SyntaxTree.Scope; ir: IntermediateCode.Section; moduleBody: BOOLEAN);
		VAR prevScope: SyntaxTree.Scope; procedureType: SyntaxTree.ProcedureType; procedure: SyntaxTree.Procedure;
			end: Label;res: IntermediateCode.Operand; cellScope: SyntaxTree.CellScope; op: Operand; string: SyntaxTree.String;
		BEGIN
			IF Trace THEN TraceEnter("Body") END;
			section := ir;
			IF ir.comments # NIL THEN
				commentPrintout := Printout.NewPrinter(ir.comments,Printout.SourceCode,FALSE);
				commentPrintout.SingleStatement(TRUE);
				dump := ir.comments;
			ELSE
				commentPrintout := NIL;
				dump := NIL;
			END;
			registerUsage.Init;

			prevScope := currentScope;
			currentScope := scope;

			procedure := scope(SyntaxTree.ProcedureScope).ownerProcedure;
			procedureType := procedure.type(SyntaxTree.ProcedureType);
			IF newObjectFile & moduleBody & ~suppressModuleRegistration THEN
				PushSelfPointer();
				(*
				moduleSection := ModuleSection(module);
				moduleOffset := moduleSection.pc;
				op := IntermediateCode.Address(addressType, moduleSection, moduleOffset);
				Emit(Push(op));
				*)
				res := NewRegisterOperand(bool);
				CallThis2("Modules","PublishThis","Runtime","InsertModule",res);
				end := NewLabel();
				(*AcquireThisRegister(bool, IntermediateCode.Result);*)
				BrneL(end, res,true);
				ReleaseIntermediateOperand(res);
			END;
			IF x # NIL THEN
				IF profile & (x.code = NIL) THEN (* do not profile assembler code sections *)
					IF moduleBody THEN
						ProfilerInit();
					ELSE
						Basic.FromPooledName(ir.name, string);
						ProfilerAddProcedure(numberProcedures,string);
						ProfilerEnterExit(numberProcedures,TRUE);
					END;
				END;

				(* nopov *)
				IF moduleBody & (operatorInitializationCodeSection # NIL) THEN
					Emit(Call(IntermediateCode.Address(addressType, operatorInitializationCodeSection, 0), 0))
				END;

				section.SetPositionOrAlignment(procedure.fixed, procedure.alignment);
				IF moduleBody THEN
					InitVariables(moduleScope)
				END;
				IF (scope.outerScope # NIL) & (scope.outerScope IS SyntaxTree.CellScope) THEN
					cellScope := scope.outerScope(SyntaxTree.CellScope);
					IF procedure = cellScope.bodyProcedure THEN
						IF cellScope.constructor # NIL THEN
							StaticCallOperand(op, cellScope.constructor);
							Emit(Call(op.op,0));
						END;
					END;
				END;

				ParameterCopies(procedureType);
				InitVariables(scope);
				IF x.code = NIL THEN
					VisitStatementBlock(x);
				ELSE
					VisitCode(x.code)
				END;
				IF x.finally # NIL THEN (*! mark finally block for object file *)
					ir.SetFinally(ir.pc);
					StatementSequence(x.finally)
				END;
				IF profile & (x.code = NIL) & ~moduleBody THEN (* do not profile assembler code sections *)
					ProfilerEnterExit(numberProcedures,FALSE);
					INC(numberProcedures);
				END;

			END;
			IF newObjectFile & moduleBody  & ~suppressModuleRegistration THEN
				PushSelfPointer();
				CallThis("Modules","SetInitialized");
				SetLabel(end);
			END;

			currentScope := prevScope;
			IF Trace THEN TraceExit("Body") END;
		END Body;

	END ImplementationVisitor;

	AllocationArray=POINTER TO ARRAY OF RECORD
		first, last: LONGINT
	END;

	RegisterAllocation*=OBJECT
	VAR
		table: AllocationArray;

		PROCEDURE &Init;
		VAR i: LONGINT;
		BEGIN
			IF table = NIL THEN NEW(table,64) END;
			FOR i := 0 TO LEN(table)-1 DO
				table[i].first := MAX(LONGINT);
				table[i].last := MIN(LONGINT);
			END;
		END Init;

		PROCEDURE Grow;
		VAR new: AllocationArray; i: LONGINT;
		BEGIN
			NEW(new,LEN(table)*2);
			FOR i := 0 TO LEN(table)-1 DO
				new[i] := table[i]
			END;
			FOR i := LEN(table) TO LEN(new)-1 DO
				new[i].first := MAX(LONGINT);
				new[i].last := MIN(LONGINT);
			END;
			table := new;
		END Grow;

		PROCEDURE Use(register, pc: LONGINT);
		BEGIN
			IF LEN(table) <= register THEN Grow END;
			IF table[register].first >pc THEN table[register].first := pc END;
			IF table[register].last <pc THEN table[register].last := pc END;
		END Use;

	END RegisterAllocation;

	IntermediateBackend*= OBJECT (Backend.Backend)
	VAR
		trace-: BOOLEAN;
		traceString-: SyntaxTree.String;
		runtimeModuleName-: SyntaxTree.String;
		traceModuleName-: SyntaxTree.String;
		newObjectFile-: BOOLEAN;
		profile-: BOOLEAN;
		noRuntimeChecks: BOOLEAN;
		noAsserts: BOOLEAN;

		PROCEDURE &InitIntermediateBackend*;
		BEGIN
			InitBackend;SetRuntimeModuleName(DefaultRuntimeModuleName)
		END InitIntermediateBackend;

		PROCEDURE Supported*(CONST instr: IntermediateCode.Instruction; VAR moduleName,procedureName: ARRAY OF CHAR): BOOLEAN;
		BEGIN
			moduleName := ""; procedureName := "";
			RETURN TRUE
		END Supported;

		PROCEDURE GenerateIntermediate*(x: SyntaxTree.Module): Sections.Module;
		VAR
			declarationVisitor: DeclarationVisitor;
			implementationVisitor: ImplementationVisitor;
			module: Sections.Module;
			name, instructionSet, platformName: SyntaxTree.String;
		BEGIN
			ResetError;
			Global.GetSymbolName(x,name);

			IF activeCellsSpecification # NIL THEN
				GetDescription(instructionSet);
				activeCellsSpecification.SetInstructionSet(instructionSet)
			END;

			NEW(module,x,system); (* backend structures *)

			Global.GetModuleName(x, name);
			module.SetModuleName(name);

			NEW(implementationVisitor,system,checker,Supported,Compiler.FindPC IN flags, runtimeModuleName, SELF, newObjectFile);
			NEW(declarationVisitor,system,implementationVisitor,SELF,Compiler.ForceModuleBodies IN flags,trace & (Compiler.Info IN flags));
			declarationVisitor.Module(x,module);

			IF newObjectFile THEN
				MetaModule(implementationVisitor,module);
			END;

			GetDescription(platformName);
			module.SetPlatformName(platformName);

			RETURN module
		END GenerateIntermediate;

		PROCEDURE DumpSectionsModuleIntoFile(module: Sections.Module; filename: ARRAY OF CHAR);
		VAR
			file: Files.File;
			writer: Files.Writer;
		BEGIN
			D.String("DumpSectionsModuleIntoFile"); D.Ln; (* TENTATIVE *)

			file := Files.New(filename);
			Files.OpenWriter(writer, file, 0);

			(*
			writer.String("; This Intermediate Code assembly was generated by the Intermediate Backend of the Fox Compiler Suite");writer.Ln;
			writer.Ln;
			*)

			module.Dump(writer);
			writer.Update;
			file.Update;
			Files.Register(file)
		END DumpSectionsModuleIntoFile;

		PROCEDURE ProcessSyntaxTreeModule(syntaxTreeModule: SyntaxTree.Module): Formats.GeneratedModule;
		BEGIN RETURN ProcessIntermediateCodeModule(GenerateIntermediate(syntaxTreeModule))
		END ProcessSyntaxTreeModule;

		PROCEDURE ProcessIntermediateCodeModule(intermediateCodeModule: Formats.GeneratedModule): Formats.GeneratedModule;
		VAR
			dump: Basic.Writer;
			result: Sections.Module;
			traceName: SyntaxTree.String;
		BEGIN
			ASSERT(intermediateCodeModule IS Sections.Module);
			result := intermediateCodeModule(Sections.Module);

			IF trace THEN
				traceName := "intermediate code trace: ";
				Strings.Append(traceName,traceString);
				dump := Basic.GetWriter(Basic.GetDebugWriter(traceName));
				IF (traceString="") OR (traceString="*") THEN
					result.Dump(dump);
					dump.Update
				ELSE
					Sections.DumpFiltered(dump, result, traceString);
				END
			END;
			RETURN result
		END ProcessIntermediateCodeModule;

		PROCEDURE GetDescription*(VAR instructionSet: ARRAY OF CHAR);
		BEGIN instructionSet := "Intermediate";
		END GetDescription;

		PROCEDURE DefineOptions(options: Options.Options);
		BEGIN
			DefineOptions^(options);
			options.Add(0X,"trace",Options.String);
			options.Add(0X,"runtime",Options.String);
			options.Add(0X,"newObjectFile",Options.Flag);
			options.Add(0X,"traceModule",Options.String);
			options.Add(0X,"profile",Options.Flag);
			options.Add(0X,"noRuntimeChecks",Options.Flag);
			options.Add(0X,"noAsserts",Options.Flag)
		END DefineOptions;

		PROCEDURE GetOptions(options: Options.Options);
		VAR name: SyntaxTree.String;
		BEGIN
			GetOptions^(options);
			trace := options.GetString("trace",traceString);
			newObjectFile := options.GetFlag("newObjectFile");
			profile := options.GetFlag("profile");
			noRuntimeChecks := options.GetFlag("noRuntimeChecks");
			noAsserts := options.GetFlag("noAsserts");
			IF options.GetString("runtime",name) THEN
				COPY(name, runtimeModuleName);
			END;
			IF ~options.GetString("traceModule",traceModuleName) THEN
				traceModuleName := DefaultTraceModuleName;
			END
		END GetOptions;

		PROCEDURE SetRuntimeModuleName*(CONST name: ARRAY OF CHAR);
		BEGIN
			COPY(name, runtimeModuleName);
		END SetRuntimeModuleName;

		PROCEDURE DefaultSymbolFileFormat(): Formats.SymbolFileFormat;
		BEGIN RETURN SymbolFileFormat.Get()
		END DefaultSymbolFileFormat;

	END IntermediateBackend;

	(* ----------------------------------- register allocation ------------------------------------- *)


		(* register mapping scheme
			virtual register number	--> register mapping   = 		part(0)		-->	ticket	<-->	physical register
																											spill offset

																	part(n)		-->	ticket	<-->	physical register
																											spill offset
		*)


	Ticket*=POINTER TO RECORD
		next-: Ticket;
		type-: IntermediateCode.Type;
		lastuse-: LONGINT;
		spilled*: BOOLEAN;
		register*, offset*: LONGINT;
		parts-: LONGINT;
	END;

	Tickets*=OBJECT
	VAR
		live-: Ticket;
		free: Ticket	;

		PROCEDURE &Init*;
		BEGIN
			live := NIL; free := NIL
		END Init;

		(* enter a new ticket into the list of live tickets, sorted by lastuse *)
		PROCEDURE Enter*(CONST type: IntermediateCode.Type; register: LONGINT; spilled: BOOLEAN; offset: LONGINT; lastuse: LONGINT): Ticket;
		VAR ticket,link: Ticket;
		BEGIN
			ASSERT(~spilled & (register # None) OR spilled & (offset # None));
			IF free # NIL THEN ticket := free; free := free.next; ticket.next := NIL;
			ELSE NEW(ticket)
			END;
			ticket.type := type;	ticket.register := register; ticket.spilled := spilled;	ticket.offset := offset; ticket.lastuse := lastuse; ticket.parts := 0;
			IF (live = NIL) OR (live.lastuse > ticket.lastuse) THEN
				ticket.next := live; live := ticket
			ELSE
				link := live;
				WHILE (link.next # NIL) & (link.next.lastuse < ticket.lastuse) DO
					ASSERT((link.register # ticket.register) OR ticket.spilled);
					link := link.next;
				END;
				IF (link.register=ticket.register) & (~ticket.spilled & ~link.spilled) THEN Dump(D.Log); D.Update; END;
				ASSERT((link.register # ticket.register) OR ticket.spilled OR link.spilled);
				ticket.next := link.next; link.next := ticket;
			END;
			RETURN ticket
		END Enter;

		(* remove ticket from live list *)
		PROCEDURE Remove*(ticket: Ticket);
		VAR link: Ticket;
		BEGIN
			IF live=ticket THEN
				live := live.next;
			ELSE
				link := live;
				WHILE (link.next # NIL) & (link.next # ticket) DO
					link := link.next
				END;
				ASSERT(link.next=ticket);
				link.next := ticket.next;
			END;
			ticket.next := free; free := ticket
		END Remove;

		PROCEDURE Dump*(w: Streams.Writer);
		VAR ticket: Ticket;
		BEGIN
			w.String("---- tickets.live ----- "); w.Ln;
			ticket := live;
			WHILE ticket # NIL DO
				DumpTicket(w,ticket);
				w.Ln;
				ticket := ticket.next;
			END;
		END Dump;

	END Tickets;

	VirtualRegisterMappings=POINTER TO ARRAY OF Ticket;

	VirtualRegisters*=OBJECT
	VAR
		tickets: VirtualRegisterMappings;
		parts: LONGINT;

		PROCEDURE &Init*(parts: LONGINT);
		VAR i: LONGINT;
		BEGIN
			SELF.parts := parts;
			IF tickets = NIL THEN NEW(tickets,64*parts) END;
			FOR i := 0 TO LEN(tickets)-1 DO
				tickets[i]:=NIL;
			END;
		END Init;

		PROCEDURE Grow;
		VAR new: VirtualRegisterMappings; i: LONGINT;
		BEGIN
			NEW(new,LEN(tickets)*2);
			FOR i := 0 TO LEN(tickets)-1 DO
				new[i] := tickets[i];
			END;
			FOR i := LEN(tickets) TO LEN(new)-1 DO
				new[i]:=NIL;
			END;
			tickets := new;
		END Grow;

		PROCEDURE Mapped*(register: LONGINT; part: LONGINT): Ticket;
		BEGIN
			ASSERT((part >=0) & (part < parts));
			IF (register > 0 ) & (register*parts < LEN(tickets)) THEN RETURN tickets[register * parts + part] ELSE RETURN NIL END;
		END Mapped;

		PROCEDURE SetMapped*(register: LONGINT; part: LONGINT; ticket: Ticket);
		BEGIN
			ASSERT((part >=0) & (part < parts));
			WHILE (register*parts >= LEN(tickets)) DO Grow END;
			tickets[register*parts+part] := ticket;
			INC(ticket.parts);
		END SetMapped;

		PROCEDURE Unmap*(register: LONGINT);
		VAR i: LONGINT;
		BEGIN
			IF (register > 0) & (register*parts < LEN(tickets)) THEN
				FOR i := 0 TO parts-1 DO
					tickets[register*parts+i] := NIL;
				END;
			END;
		END Unmap;

		PROCEDURE Parts*(): LONGINT;
		BEGIN RETURN parts
		END Parts;

		PROCEDURE Dump*(w: Streams.Writer);
		VAR register,part: LONGINT; ticket: Ticket;
		BEGIN
			w.String("---- virtual register mapping ----- "); w.Ln;
			register := 0;
			WHILE register*parts < LEN(tickets) DO
				FOR part := 0 TO parts-1 DO
					ticket := tickets[register*parts+part];
					IF ticket # NIL THEN
						w.String("register.part "); w.Int(register,1); w.String("."); w.Int(part,1); w.String(": ");
						DumpTicket(w,ticket); w.Ln;
					END;
				END;
				INC(register);
			END;
		END Dump;

	END VirtualRegisters;

	PhysicalRegisters*=OBJECT
	VAR
		PROCEDURE &InitPhysicalRegisters;
		END InitPhysicalRegisters;


		PROCEDURE Allocate*(index: LONGINT; virtualRegister: Ticket);
		END Allocate;

		PROCEDURE Mapped*(physical: LONGINT): Ticket;
		END Mapped;

		PROCEDURE Free*(index: LONGINT);
		END Free;

		PROCEDURE NextFree*(CONST type: IntermediateCode.Type): LONGINT;
		END NextFree;

		(* give a hint for the next register to return by NextFree *)
		PROCEDURE AllocationHint*(index: LONGINT);
		END AllocationHint;

		PROCEDURE SetReserved*(index: LONGINT; res: BOOLEAN);
		BEGIN
		END SetReserved;

		PROCEDURE Reserved*(index: LONGINT): BOOLEAN;
		BEGIN
		END Reserved;

		PROCEDURE Dump*(w: Streams.Writer);
		BEGIN
		END Dump;

		PROCEDURE NumberRegisters*(): LONGINT;
		BEGIN
		END NumberRegisters;


	END PhysicalRegisters;

	CONST 	MaxSpilledRegisters=64;

	TYPE
	SpillStack*=OBJECT
	VAR
		spillStack: ARRAY MaxSpilledRegisters OF Ticket; (* registers of spill stack position to virtual register, none if unused *)
		spillStackSize,maxSpillStackSize: LONGINT;

		PROCEDURE &Init*;
		VAR i: LONGINT;
		BEGIN
			spillStackSize := 0; maxSpillStackSize := 0;
			FOR i := 0 TO LEN(spillStack)-1 DO
				spillStack[i] := NIL;
			END;
		END Init;

		(* return next free spill offset in stack *)
		PROCEDURE NextFree*(): LONGINT;
		VAR i: LONGINT; index: Ticket;
		BEGIN
			i := 0;
			index := spillStack[i];
			WHILE (index # NIL) DO
				INC(i); index := spillStack[i];
			END;
			RETURN i
		END NextFree;

		PROCEDURE Allocate*(offset: LONGINT; ticket: Ticket);
		BEGIN
			spillStack[ticket.offset] := ticket;
			IF spillStackSize <= ticket.offset THEN spillStackSize := ticket.offset+1 END;
			IF maxSpillStackSize < spillStackSize THEN maxSpillStackSize := spillStackSize END;
		END Allocate;

		PROCEDURE Free*(offset: LONGINT);
		BEGIN
			spillStack[offset] := NIL;
			IF offset+1 = spillStackSize THEN (* rewind spillstack *)
				WHILE (offset >= 0) & (spillStack[offset]= NIL) DO
					DEC(offset);
				END;
				spillStackSize := offset+1;
			END;
		END Free;

		PROCEDURE Size*(): LONGINT;
		BEGIN RETURN spillStackSize
		END Size;

		PROCEDURE MaxSize*(): LONGINT;
		BEGIN RETURN maxSpillStackSize
		END MaxSize;

		PROCEDURE Dump*(w: Streams.Writer);
		VAR i: LONGINT;
		BEGIN
			w.String("---- spillstack -----");w.Ln;
			w.String("spillStackSize = "); w.Int(spillStackSize,1); w.Ln;
			w.String("maxSpillStackSze = "); w.Int(maxSpillStackSize,1); w.Ln;
			FOR i := 0 TO spillStackSize-1 DO
				IF spillStack[i]# NIL THEN DumpTicket(w,spillStack[i]);END
			END;
		END Dump;


	END SpillStack;

	GenericCodeGenerator*= OBJECT
	VAR
		diagnostics-: Diagnostics.Diagnostics; (* error stream *)
		module-: Sections.Module;
		dump*: Streams.Writer;
		in-: IntermediateCode.Section; out-: BinaryCode.Section;
		inPC-, outPC-: LONGINT;

		error* : BOOLEAN;
		allocation: RegisterAllocation;

		(* generic *)
		PROCEDURE & InitGenerator*(diagnostics: Diagnostics.Diagnostics);
		BEGIN
			SELF.module := NIL;
			SELF.diagnostics := diagnostics;
			error := FALSE;
			NEW(allocation);
		END InitGenerator;

		PROCEDURE SetModule*(module: Sections.Module); (* needed for inline code for symbol reference *)
		BEGIN
			SELF.module := module;
		END SetModule;

		PROCEDURE Error*(CONST message: ARRAY OF CHAR);
		VAR string: SyntaxTree.String;
		BEGIN
			IF diagnostics # NIL THEN
				Basic.FromPooledName(in.name, string);
				diagnostics.Error(string, inPC, Diagnostics.Invalid, message)
			END;
			IF dump # NIL THEN (* to see error in trace output also *)
				dump.String("Error: "); dump.String(message); dump.Ln; dump.Update;
			END;
			error := TRUE;
		END Error;


		(* generic *)
		PROCEDURE Section*(in: IntermediateCode.Section; out: BinaryCode.Section);
		VAR pc: LONGINT; name: SyntaxTree.String; instruction: IntermediateCode.Instruction;

			PROCEDURE ResolveLocalFixups;
			VAR fixup, next: BinaryCode.Fixup; dest: LONGINT; msg,string: SyntaxTree.String; number: ARRAY 32 OF CHAR;
			BEGIN
				fixup := out.fixupList.firstFixup;
				out.fixupList.InitFixupList;
				WHILE fixup # NIL DO
					next := fixup.nextFixup;
					IF (fixup.symbol = in) & (fixup.mode = BinaryCode.Relative) THEN (* local relative fixup *)
						IF dump # NIL THEN
							dump.String("local fixup "); dump.Int(fixup.offset,1); dump.String(" <-- ");
							fixup.Dump(dump); dump.Ln; (*dump.Update;*)
						END;
						IF fixup.symbolOffset # 0 THEN
							dest := fixup.symbolOffset;
							dest := in.instructions[dest].pc;
						ELSE
							dest := 0;
						END;
						fixup.SetSymbol(fixup.symbol, 0, dest+fixup.displacement);
						IF dump # NIL THEN
							dump.String("local fixup resolved: ");
							dump.Int(fixup.offset,1); dump.String(" <-- ");
							fixup.Dump(dump); dump.Ln; (*dump.Update;*)
						END;
						IF ~out.ApplyFixup(fixup) THEN
							COPY("fixup out of range: ", msg);
							Basic.FromPooledName(fixup.symbol.name, string);
							Strings.Append(msg, string);
							Strings.Append(msg, ":");
							Strings.IntToStr(fixup.offset, number);
							Strings.Append(msg, number);
							Error(msg)
						END
					ELSE
						out.fixupList.AddFixup(fixup);
					END;
					fixup := next;
				END;
			END ResolveLocalFixups;

			PROCEDURE GetRegisterAllocation;
			VAR pc: LONGINT;
				PROCEDURE RegisterUsage(CONST instruction: IntermediateCode.Instruction);
					PROCEDURE Use(CONST operand: IntermediateCode.Operand);
					BEGIN
						IF operand.register > 0 THEN
							allocation.Use(operand.register,inPC);
						END;
					END Use;
				BEGIN
					Use(instruction.op1);
					Use(instruction.op2);
					Use(instruction.op3);
				END RegisterUsage;
			BEGIN
				allocation.Init;
				FOR pc := 0 TO in.pc-1 DO
					inPC := pc;
					RegisterUsage(in.instructions[pc]);
				END;
			END GetRegisterAllocation;

			PROCEDURE DumpInstruction(CONST instruction: IntermediateCode.Instruction);
				PROCEDURE Use(CONST operand: IntermediateCode.Operand);
				BEGIN
					IF FirstUse(operand.register)=inPC THEN
						dump.String(" ; +"); IntermediateCode.DumpRegister(dump,operand.register);
					END;
					IF LastUse(operand.register)=inPC THEN
						dump.String(" ; -"); IntermediateCode.DumpRegister(dump,operand.register);
					END;
				END Use;
			BEGIN
				dump.Int(pc, 1); dump.String(": "); IntermediateCode.DumpInstruction(dump, instruction);
				Use(instruction.op1);
				Use(instruction.op2);
				Use(instruction.op3);
			END DumpInstruction;

		BEGIN
			Basic.FromPooledName(in.name, name);
			SELF.in := in; SELF.out := out;
			dump := out.comments;

			GetRegisterAllocation;
			Prepare;

			FOR pc := 0 TO in.pc-1 DO
				inPC := pc; outPC := out.pc;
				in.SetPC(pc, outPC);
				IF pc = in.finally THEN out.SetFinally(out.pc) END;
				instruction := in.instructions[pc];
				IF dump # NIL THEN DumpInstruction(instruction); dump.Ln END;
				CASE instruction.opcode OF
					IntermediateCode.data: EmitData(instruction);
					|IntermediateCode.reserve: EmitReserve(instruction);
					|IntermediateCode.label: EmitLabel(instruction);
				ELSE
					Generate(instruction);
				END;
			END;

			(* CheckRegistersFree();*)
			ResolveLocalFixups;
			IF dump # NIL THEN
				(*dump.Update*)
			END;
		END Section;

		PROCEDURE FirstUse*(register: LONGINT): LONGINT;
		BEGIN
			IF (register > 0)  THEN RETURN allocation.table[register].first ELSE RETURN None END;
		END FirstUse;

		PROCEDURE LastUse*(register: LONGINT): LONGINT;
		BEGIN
			IF (register > 0)  THEN RETURN allocation.table[register].last ELSE RETURN None END;
		END LastUse;


		(*-------------------  procedures that must be overwritten by implementers  ----------------------*)

		(* generate procedure - is called for any instruction that cannot be output directly by the generic code generator *)
		PROCEDURE Generate*(CONST instr: IntermediateCode.Instruction);
		BEGIN (*HALT(100); *) (* abstract *)
		END Generate;


		(* ---------------------- generically available code emission ------------------------- *)


		PROCEDURE GetDataSection*(): IntermediateCode.Section;
		VAR name: Basic.PooledName; section: IntermediateCode.Section;
		BEGIN
			Basic.InitPooledName(name);
			name[0] := StringPool.GetIndex1(module.moduleName);
			name[1] := StringPool.GetIndex1("@Immediates");
			section := IntermediateCode.NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,NIL,TRUE);
			RETURN section
		END GetDataSection;

		PROCEDURE EmitData(CONST instruction: IntermediateCode.Instruction);
			VAR type: IntermediateCode.Type; fixup: BinaryCode.Fixup; pc: LONGINT;fixupFormat: BinaryCode.FixupPatterns;
		BEGIN
			type := instruction.op1.type;
			pc := out.pc;
			IF type.form IN IntermediateCode.Integer THEN
				out.PutBytes(instruction.op1.intValue,SHORT(type.sizeInBits DIV 8));
			ELSE
				IF type.sizeInBits = IntermediateCode.Bits32 THEN
					out.PutReal(SHORT(instruction.op1.floatValue));
				ELSIF type.sizeInBits = IntermediateCode.Bits64 THEN
					out.PutLongreal(instruction.op1.floatValue);
				ELSE Assert(FALSE,"no floats other than 32 or 64 bit")
				END;
			END;
			IF instruction.op1.symbol # NIL THEN
				NEW(fixupFormat,1);
				fixupFormat[0].offset := 0;
				fixupFormat[0].bits := type.sizeInBits;
				fixup := BinaryCode.NewFixup(BinaryCode.Absolute,pc,instruction.op1.symbol,instruction.op1.symbolOffset,instruction.op1.offset,0,fixupFormat);
				out.fixupList.AddFixup(fixup);
			END;
		END EmitData;

		PROCEDURE EmitReserve(CONST instruction: IntermediateCode.Instruction);
		VAR sizeInUnits,i: LONGINT;
		BEGIN
			sizeInUnits := SHORT(instruction.op1.intValue);
			ASSERT(sizeInUnits >= 0); (* size is initialized to MIN(LONGINT), this checks if size field has been visited *)
			FOR i := 0 TO sizeInUnits-1 DO
				out.PutBits(0,out.unit);
			END;
		END EmitReserve;

		PROCEDURE EmitLabel(CONST instruction: IntermediateCode.Instruction);
		VAR position: LONGINT;
		BEGIN
			position := SHORT(instruction.op1.intValue);
			out.AddLabel(position);
		END EmitLabel;

		PROCEDURE Prepare*;
		BEGIN

		END Prepare;

	END GenericCodeGenerator;

	GeneratorWithTickets*= OBJECT (GenericCodeGenerator)
	VAR
		physicalRegisters-: PhysicalRegisters; (* physical registers <-> tickets *)
		virtualRegisters-: VirtualRegisters; (* virtual registers --> tickets *)
		tickets-: Tickets;  (* tickets <-> physical registers *)
		spillStack-: SpillStack; (* spill stack offset <-> ticket *)

		(* generic *)
		PROCEDURE & InitTicketGenerator*(diagnostics: Diagnostics.Diagnostics; numberRegisterParts: LONGINT; physicalRegisters: PhysicalRegisters);
		BEGIN
			InitGenerator(diagnostics);
			NEW(tickets);
			NEW(virtualRegisters,numberRegisterParts);
			NEW(spillStack);
			SELF.physicalRegisters := physicalRegisters;
		END InitTicketGenerator;

		(*-------------------  procedures that must be overwritten by implementers  ----------------------*)

		(* input: type (such as that of an intermediate operand), output: type part *)
		PROCEDURE GetPartType*(CONST type: IntermediateCode.Type; part: LONGINT; VAR typePart: IntermediateCode.Type);
		BEGIN HALT(100); (* abstract *)
		END GetPartType;

		PROCEDURE ToSpillStack*(ticket: Ticket);
		BEGIN HALT(100) (* abstract *)
		END ToSpillStack;

		PROCEDURE AllocateSpillStack*(size: LONGINT);
		BEGIN HALT(100) (* abstract *)
		END AllocateSpillStack;

		PROCEDURE ToRegister*(ticket: Ticket);
		BEGIN HALT(100) (* abstract *)
		END ToRegister;

		PROCEDURE ExchangeTickets*(ticket1,ticket2: Ticket);
		BEGIN HALT(100) (* abstract *)
		END ExchangeTickets;


		(*---------------------------- ticket handling and register allocation ----------------------------*)

		(* Spill register of a ticket, if any *)
		PROCEDURE Spill*(ticket: Ticket);
		VAR register,offset,size: LONGINT;
		BEGIN
			IF (ticket = NIL) OR (ticket.spilled) THEN RETURN END;
			register := ticket.register;
			offset := spillStack.NextFree();
			ticket.offset := offset;
			size := spillStack.Size();
			spillStack.Allocate(offset,ticket);
			size := spillStack.Size()-size;
			ASSERT(size>=0);
			IF size>0 THEN AllocateSpillStack(size) END;

			ToSpillStack(ticket);
			ticket.offset := offset;
			physicalRegisters.Free(register);
			ticket.spilled := TRUE;
		END Spill;

		(* Make sure a ticket reprents a physical register *)
		PROCEDURE UnSpill*(ticket: Ticket);
		VAR mapped:Ticket; register: LONGINT;

			PROCEDURE ExchangeSpill(ticket1, ticket2: Ticket): BOOLEAN;
			BEGIN
				IF ticket1.spilled THEN ASSERT(~ticket2.spilled); RETURN ExchangeSpill(ticket2,ticket1) END;
				IF (ticket1.type.sizeInBits # ticket2.type.sizeInBits)
					OR ~(ticket1.type.form IN IntermediateCode.Integer) OR ~(ticket2.type.form IN IntermediateCode.Integer)
					OR ticket1.spilled THEN
					RETURN FALSE
				END;

				ASSERT(~ticket1.spilled); ASSERT(ticket1.register # None);
				ASSERT(ticket2.spilled); ASSERT((ticket2.register = ticket1.register) OR (ticket2.register = None));

				ExchangeTickets(ticket1,ticket2);

				physicalRegisters.Free(ticket1.register);
				spillStack.Free(ticket2.offset);
				ticket2.register := ticket1.register;
				ticket1.offset := ticket2.offset;
				ticket1.spilled := TRUE;
				ticket2.spilled := FALSE;
				physicalRegisters.Allocate(ticket2.register,ticket2);
				spillStack.Allocate(ticket1.offset,ticket1);
				RETURN TRUE
			END ExchangeSpill;

			PROCEDURE SpillToRegister(ticket: Ticket; register: LONGINT);
			VAR size: LONGINT;
			BEGIN
				ASSERT(~physicalRegisters.Reserved(ticket.register) OR (register = ticket.register));
				ticket.register := register;
				IF dump # NIL THEN
					dump.String(" allocate register : index="); dump.Int(ticket.register,1); dump.Ln;
				END;
				ToRegister(ticket);
				size := spillStack.Size();
				spillStack.Free(ticket.offset);
				ticket.spilled := FALSE;
				ticket.offset := 0;
				physicalRegisters.Allocate(register,ticket);
				size := spillStack.Size()-size;
				ASSERT(size<=0);
				IF size<0 THEN AllocateSpillStack(size) END;
			END SpillToRegister;

		BEGIN
			IF (ticket = NIL) OR ~ticket.spilled THEN RETURN END;

			register := ticket.register;
			IF register = None THEN
				register := physicalRegisters.NextFree(ticket.type);
				IF register # None THEN (* free register found rightaway*)
					SpillToRegister(ticket, register)
				ELSE
					mapped := GetPreferredSpill(ticket.type);
					IF ~ExchangeSpill(mapped, ticket) THEN
						register := ForceFreeRegister(ticket.type);
						SpillToRegister(ticket, register);
					END;
				END;
			ELSE
				mapped := physicalRegisters.Mapped(register);
				IF mapped = NIL THEN
					SpillToRegister(ticket, register)
				ELSIF ~ExchangeSpill(mapped, ticket) THEN
					WHILE mapped # NIL DO
						Spill(mapped);
						mapped := physicalRegisters.Mapped(ticket.register);
					END;
					SpillToRegister(ticket, register)
				END;
			END;
		END UnSpill;

		PROCEDURE GetPreferredSpill*(CONST type: IntermediateCode.Type): Ticket;
		VAR ticket,spill: Ticket;
			PROCEDURE Spillable(ticket: Ticket; best:BOOLEAN): BOOLEAN;
			BEGIN
				RETURN
					~ticket.spilled & (ticket.register # None)
					& ((ticket.type.form = IntermediateCode.Float) = (type.form = IntermediateCode.Float)) (* don't spill float when int is needed *)
					& (~best OR (ticket.type.sizeInBits = type.sizeInBits))
					& (~physicalRegisters.Reserved(ticket.register))
					(*! check that register is not in use in current instruction*)
			END Spillable;
		BEGIN
			ticket := tickets.live;
			WHILE ticket # NIL DO
				IF Spillable(ticket,TRUE) THEN spill := ticket END;
				ticket := ticket.next
			END;
			IF ticket = NIL THEN
				ticket := tickets.live;
				WHILE ticket # NIL DO
					IF Spillable(ticket,FALSE) THEN spill := ticket END;
					ticket := ticket.next
				END;
			END;
			ASSERT(spill # NIL);
			RETURN spill
		END GetPreferredSpill;

		PROCEDURE ForceFreeRegister*(CONST type:IntermediateCode.Type): LONGINT;
		VAR tempReg: LONGINT; ticket: Ticket;
		BEGIN
			tempReg := physicalRegisters.NextFree(type);
			WHILE tempReg = None DO
				ticket := GetPreferredSpill(type);
				Spill(ticket);
				tempReg := physicalRegisters.NextFree(type);
			END;
			RETURN tempReg
		END ForceFreeRegister;

		PROCEDURE ReservePhysicalRegister*(CONST type: IntermediateCode.Type; register: LONGINT): Ticket;
		VAR ticket: Ticket;
		BEGIN
			ticket := tickets.Enter(type,register,FALSE,None,inPC);
			IF dump # NIL THEN
				dump.String(" allocate register : index="); dump.Int(register,1); dump.Ln;
			END;
			physicalRegisters.Allocate(register, ticket);
			RETURN ticket
		END ReservePhysicalRegister;

		PROCEDURE TemporaryTicket*(CONST type: IntermediateCode.Type): Ticket;
		VAR register: LONGINT; ticket: Ticket;
		BEGIN
			IF type.form > IntermediateCode.Undefined THEN
				register := ForceFreeRegister(type);
				ticket := ReservePhysicalRegister(type,register);
			ELSE
				ticket := NIL
			END;
			RETURN ticket
		END TemporaryTicket;

		(*-------------------  register mapping  ----------------------*)

		PROCEDURE MapVirtualRegister*(virtualRegister: LONGINT; type: IntermediateCode.Type; part: LONGINT);
		VAR partType: IntermediateCode.Type; lastuse:LONGINT;

			PROCEDURE MapTicket(virtualRegister: LONGINT; part: LONGINT; CONST type: IntermediateCode.Type; lastuse:LONGINT);
			VAR index,offset,size: LONGINT; ticket: Ticket;
			BEGIN

				index := physicalRegisters.NextFree(type);
				IF index # None THEN
					ticket := tickets.Enter(type,index,FALSE,0,lastuse);
					IF dump # NIL THEN
						dump.String(" allocate register : index="); dump.Int(index,1); dump.Ln;
					END;
					physicalRegisters.Allocate(index,ticket);
					physicalRegisters.SetReserved(index,TRUE);
				ELSE (* spill new ticket rightaway, no phyiscal register assigned yet *)
					offset := spillStack.NextFree();
					ticket := tickets.Enter(type,index,TRUE,offset,lastuse);
					size := spillStack.Size();
					ticket.offset := offset;
					spillStack.Allocate(offset,ticket);
					size := spillStack.Size()-size;
					ASSERT(size>=0);
					IF size>0 THEN AllocateSpillStack(size) END;
				END;
				virtualRegisters.SetMapped(virtualRegister,part,ticket);
			END MapTicket;

		BEGIN
			IF virtualRegisters.Mapped(virtualRegister,part)=NIL THEN
				lastuse := LastUse(virtualRegister);
				GetPartType(type,part,partType);
				IF partType.form # IntermediateCode.Undefined THEN
					MapTicket(virtualRegister,part,partType,lastuse)
				END;
			END;
		END MapVirtualRegister;

		PROCEDURE ResetTicket(ticket: Ticket);
		BEGIN
			ticket.offset := 0;
			ticket.spilled := FALSE;
			ticket.register := None;
			ticket.parts := 0;
		END ResetTicket;

		PROCEDURE FreeTicket(ticket: Ticket);
		VAR size: LONGINT;
		BEGIN
			IF ticket.spilled THEN
				IF dump # NIL THEN
					dump.String(" free spilled register : ofs="); dump.Int(ticket.offset,1); dump.Ln;
				END;
				size := spillStack.Size();
				spillStack.Free(ticket.offset);
				size := spillStack.Size()-size;
				ASSERT(size<=0);
				IF size<0 THEN AllocateSpillStack(size) END;
			ELSIF ticket.register # None THEN
				IF dump # NIL THEN
					dump.String("free register: index="); dump.Int(ticket.register,1);  dump.Ln;
				END;
				physicalRegisters.SetReserved(ticket.register,FALSE);
				physicalRegisters.Free(ticket.register);
				ASSERT(~physicalRegisters.Reserved(ticket.register));
			END;
		END FreeTicket;

		PROCEDURE RemapTicket(ticket: Ticket);
		VAR size: LONGINT;
		BEGIN
			IF ~ticket.spilled THEN
				IF dump # NIL THEN
					dump.String(" remap register : index="); dump.Int(ticket.register,1); dump.Ln;
				END;
				physicalRegisters.Allocate(ticket.register,ticket);
				physicalRegisters.SetReserved(ticket.register,TRUE);
			ELSE (* spill new ticket rightaway, no phyiscal register assigned yet *)
				size := spillStack.Size();
				spillStack.Allocate(ticket.offset,ticket);
				size := spillStack.Size()-size;
				ASSERT(size>=0);
				IF size>0 THEN AllocateSpillStack(size) END;
			END;
		END RemapTicket;

		(* unmap ticket: free  register or spill stack position and remove ticket from list of live tickets *)
		PROCEDURE UnmapTicket*(ticket: Ticket);
		BEGIN
			IF ticket = NIL THEN RETURN END;
			FreeTicket(ticket);
			tickets.Remove(ticket);
			ResetTicket(ticket);
		END UnmapTicket;

		PROCEDURE TryAllocate*(CONST operand: IntermediateCode.Operand; part: LONGINT);
		BEGIN
			IF (FirstUse(operand.register) = inPC) & (virtualRegisters.Mapped(operand.register,part)=NIL)  THEN
				(*
				D.String("IntermediateBackend.TryAllocate: "); D.Int(operand.register,1); D.Ln;
				*)
				(*ASSERT(virtualRegisters.Mapped(operand.register,0)=NIL);
				*)
				IF operand.mode = IntermediateCode.ModeMemory THEN
					MapVirtualRegister(operand.register,IntermediateCode.GetType(module.system,module.system.addressType),part);
				ELSE
					MapVirtualRegister(operand.register, operand.type,part);
				END;
				ASSERT(virtualRegisters.Mapped(operand.register,part)#NIL);
			END;
		END TryAllocate;

		PROCEDURE TryUnmap*(CONST operand: IntermediateCode.Operand);
		VAR ticket: Ticket; part: LONGINT;
		BEGIN
			IF (operand.register >=0) & (LastUse(operand.register) = inPC) THEN
				part := 0;
				WHILE (part<virtualRegisters.Parts()) DO
					ticket := virtualRegisters.Mapped(operand.register,part);
					IF (ticket # NIL) THEN
						virtualRegisters.Unmap(operand.register)
					END;
					INC(part);
				END;
			END;
		END TryUnmap;

		PROCEDURE ReleaseHint*(register: LONGINT);
		VAR ticket: Ticket;
		BEGIN
			IF register >=0 THEN
				ticket := physicalRegisters.Mapped(register);
				IF (ticket # NIL) & (ticket.lastuse = inPC) THEN
					DEC(ticket.parts); (* to avoid freeing a register that is used at several parts of an operand *)
					IF ticket.parts=0 THEN
						physicalRegisters.SetReserved(register,FALSE);
						UnmapTicket(ticket);
						physicalRegisters.AllocationHint(register);
					END;
				END;
			END;
		END ReleaseHint;

		(* increase usage counter of register mapped by ticket - allocated or not *)
		PROCEDURE ReserveTicketRegister*(ticket: Ticket; reserved: BOOLEAN);
		BEGIN
			IF (ticket#NIL) & (ticket.register # None) THEN
				physicalRegisters.SetReserved(ticket.register,reserved)
			END;
		END ReserveTicketRegister;

		PROCEDURE ReserveOperandRegisters*(CONST operand: IntermediateCode.Operand; reserved: BOOLEAN);
		VAR i: LONGINT; ticket: Ticket;
		BEGIN
			FOR i := 0 TO virtualRegisters.Parts()-1 DO
				ticket := virtualRegisters.Mapped(operand.register,i);
				IF ticket # NIL THEN
					ReserveTicketRegister(ticket,reserved);
					IF operand.mode = IntermediateCode.ModeMemory THEN
						ticket.parts := virtualRegisters.Parts()
					ELSE
						ticket.parts := 1
					END;
				END;
			END;
		END ReserveOperandRegisters;

	END GeneratorWithTickets;



	VAR int8-, int16-, int32-, int64-, uint8-, uint16-, uint32-, uint64-, float32-, float64-: IntermediateCode.Type;
		emptyOperand: IntermediateCode.Operand;
		systemCalls: ARRAY NumberSystemCalls OF SyntaxTree.Symbol;



	PROCEDURE AddRegisterEntry(VAR queue: RegisterEntry; register: LONGINT);
	VAR new: RegisterEntry;
	BEGIN
		NEW(new); new.register := register; new.next := NIL; new.prev := NIL;
		IF queue = NIL THEN
			queue := new
		ELSE
			new.next := queue;
			IF queue#NIL THEN queue.prev := new END;
			queue := new
		END;
	END AddRegisterEntry;

	PROCEDURE RemoveRegisterEntry(VAR queue: RegisterEntry; register: LONGINT);
	VAR this: RegisterEntry;
	BEGIN
		this := queue;
		WHILE (this # NIL) & (this.register # register) DO
			this := this.next;
		END;
		IF this = queue THEN queue := queue.next END;
		IF this.prev # NIL THEN this.prev.next := this.next END;
		IF this.next # NIL THEN this.next.prev := this.prev END;
	END RemoveRegisterEntry;

	PROCEDURE DumpRegisterEntry(dump: Streams.Writer; entry: RegisterEntry);
	BEGIN
		IntermediateCode.DumpRegister(dump,entry.register);
	END DumpRegisterEntry;

	PROCEDURE DumpTicket*(w: Streams.Writer; ticket: Ticket);
	BEGIN
		w.String("register "); w.Int(ticket.register,1);
		w.String(" with type ");
		IntermediateCode.DumpType(w,ticket.type);
		IF ticket.spilled THEN w.String(" spilled at "); w.Int(ticket.offset,1) END;
		w.String(" parts "); w.Int(ticket.parts,1);
		w.String(" last use "); w.Int(ticket.lastuse,1);
	END DumpTicket;

	PROCEDURE Assert(cond: BOOLEAN; CONST reason: ARRAY OF CHAR);
	BEGIN ASSERT(cond);
	END Assert;

	PROCEDURE ReusableRegister(op: IntermediateCode.Operand): BOOLEAN;
	BEGIN
		RETURN (op.mode = IntermediateCode.ModeRegister) & (op.register > 0) & (op.offset = 0);
	END ReusableRegister;

	PROCEDURE EnsureBodyProcedure(moduleScope: SyntaxTree.ModuleScope);
	VAR procedure: SyntaxTree.Procedure; procedureScope: SyntaxTree.ProcedureScope;
	BEGIN
		procedure := moduleScope.bodyProcedure;
		IF procedure = NIL THEN (* artificially add body procedure if not existing. Really needed? *)
			procedureScope := SyntaxTree.NewProcedureScope(moduleScope);
			procedure := SyntaxTree.NewProcedure(-1,Global.ModuleBodyName, procedureScope);
			procedure.SetScope(moduleScope);
			procedure.SetType(SyntaxTree.NewProcedureType(-1,moduleScope));
			procedure.SetAccess(SyntaxTree.Hidden);
			moduleScope.SetBodyProcedure(procedure);
			moduleScope.AddProcedure(procedure);
			procedureScope.SetBody(SyntaxTree.NewBody(-1,procedureScope)); (* empty body *)
		END;
	END EnsureBodyProcedure;

	PROCEDURE MetaHeapBlock(implementationVisitor: ImplementationVisitor; CONST moduleName, typeName: ARRAY OF CHAR; module: Sections.Module; section: IntermediateCode.Section; dataAdrOffset: LONGINT);
	VAR moduleTD: IntermediateCode.Section; offset: LONGINT;
	BEGIN
		INC(dataAdrOffset,6);
		MetaInfo(section,"headerAdr");
		MetaAddress(module,section,0);
		MetaInfo(section,"typeDesc");

		moduleTD := implementationVisitor.GetTypeDescriptor(moduleName,typeName);
		offset := ToMemoryUnits(module.system,(1 + 0 (*= numberMethods*) +16+1)*module.system.addressSize);
		MetaSymbol(module,section, moduleTD, 0, offset);

		MetaInfo(section,"mark: LONGINT;");
		MetaLongint(module,section,-1);
		MetaInfo(section,"dataAdr-: SYSTEM.ADDRESS");
		MetaSymbol(module,section,section,dataAdrOffset,0);
		MetaInfo(section,"size-: SYSTEM.SIZE");
		MetaAddress(module,section,0);
		MetaInfo(section,"nextRealtime: HeapBlock;");
		MetaAddress(module,section,0);
	END MetaHeapBlock;

	PROCEDURE MetaProtectedHeapBlock(implementationVisitor: ImplementationVisitor; CONST moduleName, typeName: ARRAY OF CHAR; module: Sections.Module; section: IntermediateCode.Section; dataAdrOffset: LONGINT);
	VAR i: LONGINT;
	BEGIN
		INC(dataAdrOffset,14);
		MetaHeapBlock(implementationVisitor,moduleName,typeName,module,section,dataAdrOffset);
		MetaInfo(section,"count*: LONGINT");
		MetaLongint(module,section,0);
		MetaInfo(section,"locked*: BOOLEAN");
		MetaLongint(module,section,0);
		MetaInfo(section,"awaitingLock*: ProcessQueue");
		MetaAddress(module,section,0);
		MetaAddress(module,section,0);
		MetaInfo(section,"awaitingCond*: ProcessQueue");
		MetaAddress(module,section,0);
		MetaAddress(module,section,0);
		MetaInfo(section,"lockedBy*: ANY");
		MetaAddress(module,section,0);
		MetaInfo(section,"lock*: ANY");
		MetaAddress(module,section,0);
		MetaInfo(section,"waitingPriorities*: ARRAY NumPriorities OF LONGINT");
		MetaLongint(module,section,1);
		FOR i := 2 TO 6 DO
		MetaLongint(module,section,0);
		END;
	END MetaProtectedHeapBlock;

	PROCEDURE MetaInfo(section: IntermediateCode.Section; CONST s: ARRAY OF CHAR);
	BEGIN
		IF section.comments # NIL THEN section.comments.String(s); section.comments.Ln; section.comments.Update END;
	END MetaInfo;

	PROCEDURE MetaAddress(module: Sections.Module; section: IntermediateCode.Section; value: LONGINT);
	VAR op: IntermediateCode.Operand;
	BEGIN
		IntermediateCode.InitImmediate(op,IntermediateCode.GetType(module.system, module.system.addressType),value);
		section.Emit(Data(op));
	END MetaAddress;

	PROCEDURE MetaSet(module: Sections.Module; section: IntermediateCode.Section; value: SET);
	VAR op: IntermediateCode.Operand;
	BEGIN
		IntermediateCode.InitImmediate(op,IntermediateCode.GetType(module.system, module.system.longintType),SYSTEM.VAL(LONGINT,value));
		section.Emit(Data(op));
	END MetaSet;

	PROCEDURE MetaLongint(module: Sections.Module; section: IntermediateCode.Section; value: LONGINT);
	VAR op: IntermediateCode.Operand;
	BEGIN
		IntermediateCode.InitImmediate(op,IntermediateCode.GetType(module.system, module.system.longintType),value);
		section.Emit(Data(op));
	END MetaLongint;

	PROCEDURE PatchLongint(module: Sections.Module; section: IntermediateCode.Section; pc: LONGINT; value: LONGINT);
	VAR op,noOperand: IntermediateCode.Operand;
	BEGIN
		IntermediateCode.InitOperand(noOperand);
		IntermediateCode.InitImmediate(op,IntermediateCode.GetType(module.system, module.system.longintType),value);
		section.PatchOperands(pc,op,noOperand,noOperand);
	END PatchLongint;

	PROCEDURE MetaBoolean(module: Sections.Module; section: IntermediateCode.Section; value: BOOLEAN);
	VAR op: IntermediateCode.Operand; intValue: LONGINT;
	BEGIN
		IF value = FALSE THEN intValue := 0 ELSE intValue :=1 END;
		IntermediateCode.InitImmediate(op,IntermediateCode.GetType(module.system, module.system.booleanType),intValue);
		section.Emit(Data(op));
	END MetaBoolean;

	PROCEDURE MetaChar(module: Sections.Module; section: IntermediateCode.Section; char: CHAR);
	VAR op: IntermediateCode.Operand;
	BEGIN
		IntermediateCode.InitImmediate(op,IntermediateCode.GetType(module.system, module.system.characterType),ORD(char));
		section.Emit(Data(op));
	END MetaChar;

	PROCEDURE MetaString(module: Sections.Module; section: IntermediateCode.Section; CONST str: ARRAY OF CHAR);
	VAR i: LONGINT;
	BEGIN
		MetaInfo(section,str);
		i := 0;
		WHILE(str[i] # 0X) DO
			MetaChar(module,section,str[i]);
			INC(i);
		END;
		MetaChar(module,section,0X);
	END MetaString;


	PROCEDURE MetaSymbol(module: Sections.Module; section: IntermediateCode.Section; symbol: Sections.Section; virtualOffset, realOffset: LONGINT);
	VAR op: IntermediateCode.Operand;
	BEGIN
		IF symbol = NIL THEN
			MetaAddress(module, section, realOffset);
			ASSERT(virtualOffset = 0);
		ELSE
			IntermediateCode.InitAddress(op, IntermediateCode.GetType(module.system, module.system.addressType), symbol, virtualOffset);
			IntermediateCode.SetOffset(op,realOffset);
			section.Emit(Data(op));
		END;
	END MetaSymbol;

	(* OutPointers delivers
		{pointerOffset}
	*)
	PROCEDURE MetaPointers(offset: LONGINT; symbol: Sections.Section; module: Sections.Module; section: IntermediateCode.Section; type: SyntaxTree.Type; VAR numberPointers: LONGINT);
	VAR variable: SyntaxTree.Variable; i,n,size: LONGINT; base: SyntaxTree.Type;
	BEGIN
		type := type.resolved;
		IF type IS SyntaxTree.AnyType THEN
			MetaSymbol(module,section, symbol, 0, (offset ));
			INC(numberPointers);

			IF Trace THEN D.Str("ptr at offset="); D.Int(offset,1); D.Ln; END;
		ELSIF type IS SyntaxTree.PointerType THEN
			MetaSymbol(module,section, symbol, 0, (offset )); INC(numberPointers);
			IF Trace THEN D.Str("ptr at offset="); D.Int(offset,1);D.Ln;  END;
		ELSIF (type IS SyntaxTree.ProcedureType) & (type(SyntaxTree.ProcedureType).isDelegate) THEN
			MetaSymbol(module,section, symbol, 0, (offset )+module.system.addressSize DIV 8 ); INC(numberPointers);
			IF Trace THEN D.Str("ptr at offset="); D.Int(offset+module.system.addressSize DIV 8,1); END;
		ELSIF (type IS SyntaxTree.RecordType) THEN
			(* never treat a record like a pointer, even if the pointer field is set! *)
			WITH type: SyntaxTree.RecordType DO
				base := type.GetBaseRecord();
				IF base  # NIL THEN
					MetaPointers(offset,symbol,module,section, base,numberPointers);
				END;
				variable := type.recordScope.firstVariable;
				WHILE(variable # NIL) DO
					IF ~(variable.untraced) THEN
						MetaPointers(offset+variable.offsetInBits DIV 8, symbol,  module,section, variable.type,numberPointers);
					END;
					variable := variable.nextVariable;
				END;
			END;
		ELSIF (type IS SyntaxTree.ArrayType) THEN
			WITH type: SyntaxTree.ArrayType DO
				IF type.form= SyntaxTree.Static THEN
					n := type.staticLength;
					base := type.arrayBase.resolved;
					WHILE(base IS SyntaxTree.ArrayType) DO
						type := base(SyntaxTree.ArrayType);
						n := n* type.staticLength;
						base := type.arrayBase.resolved;
					END;
					size := module.system.SizeOf(base) DIV 8;
					IF SemanticChecker.ContainsPointer(base) THEN
						ASSERT(n<1000000); (* not more than one million pointers on the stack ... *)
						FOR i := 0 TO n-1 DO
							MetaPointers(offset+i*size, symbol, module,section, base,numberPointers);
						END;
					END;
				ELSE
					MetaSymbol(module, section, symbol, 0, (offset )); INC(numberPointers);
					IF Trace THEN D.Str("ptr at offset="); D.Int(offset,1); D.Ln; END;
				END;
			END;
		ELSIF (type IS SyntaxTree.MathArrayType) THEN
			WITH type: SyntaxTree.MathArrayType DO
				IF type.form = SyntaxTree.Static THEN
					n := type.staticLength;
					base := type.arrayBase.resolved;
					WHILE(base IS SyntaxTree.MathArrayType) DO
						type := base(SyntaxTree.MathArrayType);
						n := n* type.staticLength;
						base := type.arrayBase.resolved;
					END;
					size := module.system.SizeOf(base) DIV 8;
					IF SemanticChecker.ContainsPointer(base) THEN
						ASSERT(n<1000000); (* not more than one million pointers on the stack ... *)
						FOR i := 0 TO n-1 DO
							MetaPointers(offset+i*size, symbol,  module, section, base,numberPointers);
						END;
					END;
				ELSE
					MetaSymbol(module,section, symbol, 0, (offset )); INC(numberPointers); (* GC relevant pointer is at offset 0 *)
					IF Trace THEN D.Str("ptr at offset="); D.Int(offset,1); D.Ln; END;
				END
			END;
		(* ELSE no pointers in type *)
		END;
	END MetaPointers;

	PROCEDURE MetaExportDesc(module: Sections.Module; source: IntermediateCode.Section;
		fingerPrinter: FingerPrinter.FingerPrinter; symbol: Sections.Section): BOOLEAN;
	VAR fingerPrint: SyntaxTree.FingerPrint;
	BEGIN
		IF (symbol # NIL) & (symbol.symbol # NIL) & (symbol.type # Sections.InitCodeSection)
			& (symbol.type # Sections.InlineCodeSection)
		THEN
			fingerPrint := fingerPrinter.SymbolFP(symbol.symbol);
			MetaLongint(module,source,fingerPrint.shallow);
			MetaSymbol(module,source,symbol,0,0);
			MetaAddress(module,source,0);
			MetaAddress(module,source,0);
			RETURN TRUE
		END;
		RETURN FALSE
	END MetaExportDesc;

	PROCEDURE MetaArray(module: Sections.Module; source: IntermediateCode.Section; VAR sizePC: LONGINT);
	BEGIN
		MetaInfo(source,"ArrayHeader");
		MetaAddress(module,source,0);
		MetaAddress(module,source,0);
		MetaAddress(module,source,0);
		sizePC := source.pc;
		MetaAddress(module,source,0);
		MetaInfo(source,"array data");
	END MetaArray;

	PROCEDURE MetaExportDescArray(module: Sections.Module; source: IntermediateCode.Section; VAR size: LONGINT);
	VAR
		sizePC, i: LONGINT; section: Sections.Section; fingerPrinter : FingerPrinter.FingerPrinter;
	BEGIN
		NEW(fingerPrinter, module.system);
		size := 0;
		MetaArray(module,source,sizePC);
		FOR i := 0 TO module.allSections.Length() - 1 DO
			section := module.allSections.GetSection(i);
			IF section.kind = Sections.RegularKind THEN
				IF MetaExportDesc(module, source, fingerPrinter, section) THEN INC(size) END
			END
		END;
		PatchLongint(module,source,sizePC,size);
	END MetaExportDescArray;

	PROCEDURE MetaExceptionArray(module: Sections.Module; source: IntermediateCode.Section);
	VAR
		p: Sections.Section; finallyPC, sizePC, size, i: LONGINT;
	BEGIN
		MetaInfo(source, "exception table offsets array descriptor");
		size := 0;
		MetaArray(module,source,sizePC);
		MetaInfo(source, "exception table content");
		FOR i := 0 TO module.allSections.Length() - 1 DO
			p := module.allSections.GetSection(i);
			IF p.kind = Sections.RegularKind THEN
			IF p.type = Sections.CodeSection THEN
				finallyPC := p(IntermediateCode.Section).finally;
				IF finallyPC>=0 THEN
					MetaSymbol(module, source, p, 0,0);
					MetaSymbol(module, source, p, finallyPC, 0);
					MetaSymbol(module, source, p, finallyPC,0);
					INC(size);
				END;
			END
			END
		END;
		PatchLongint(module,source,sizePC,size);
		END MetaExceptionArray;

		PROCEDURE MetaName(module: Sections.Module; section: IntermediateCode.Section; CONST name: ARRAY OF CHAR);
		VAR i: LONGINT; ch: CHAR;
		BEGIN
			i := 0;
			REPEAT
				ch := name[i]; INC(i);
				MetaChar(module, section, ch);
			UNTIL ch = 0X;
			WHILE i < 32 DO
				MetaChar(module, section, 0X); INC(i);
			END;
		END MetaName;

		PROCEDURE MetaReferences(module: Sections.Module; section: IntermediateCode.Section);
		CONST
			rfDirect = 1X; rfIndirect = 3X;
			rfStaticArray= 12X; rfDynamicArray=14X; rfOpenArray=15X;
			rfByte = 1X; rfBoolean = 2X; rfChar8=3X; rfShortint=04X; rfInteger = 05X; rfLongint = 06X;
			rfReal = 07X; rfLongreal = 08X; rfSet = 09X; rfDelegate = 0EX;  rfString = 0FH; rfPointer = 0DX; rfHugeint = 10X;
			rfChar16=11X; rfChar32=12X; rfAll=13X; rfSame=14X; rfRange=15X; rfRecord=16X; rfRecordPointer=1DX;
			rfArrayFlag = 80X;

		VAR
			size: LONGINT; s: Sections.Section; sizePC, i: LONGINT;

			PROCEDURE BaseType(arrayOf: BOOLEAN; type: SyntaxTree.Type);
			VAR char: CHAR;
			BEGIN
				IF type = NIL THEN char := rfLongint
				ELSIF type  IS SyntaxTree.ByteType THEN char := rfByte
				ELSIF type IS SyntaxTree.BooleanType THEN char := rfBoolean
				ELSIF type IS SyntaxTree.CharacterType THEN
					IF type.sizeInBits = 8 THEN char := rfChar8
					ELSIF type.sizeInBits = 16 THEN char := rfChar16
					ELSIF type.sizeInBits = 32 THEN char := rfChar32
					END;
				ELSIF type IS SyntaxTree.IntegerType THEN
					IF type.sizeInBits = 8 THEN char := rfShortint
					ELSIF type.sizeInBits = 16 THEN char := rfInteger
					ELSIF type.sizeInBits = 32 THEN char := rfLongint
					ELSIF type.sizeInBits = 64 THEN char := rfHugeint
					END;
				ELSIF type IS SyntaxTree.SizeType THEN char := rfLongint
				ELSIF type IS SyntaxTree.AddressType THEN char := rfLongint
				ELSIF type IS SyntaxTree.FloatType THEN
					IF type.sizeInBits = 32 THEN char := rfReal
					ELSIF type.sizeInBits = 64 THEN  char := rfLongreal
					END;
				ELSIF type IS SyntaxTree.SetType THEN char := rfSet
				ELSIF type IS SyntaxTree.AnyType THEN char := rfPointer
				ELSIF type IS SyntaxTree.ObjectType THEN char := rfPointer
				ELSIF type IS SyntaxTree.PointerType THEN char := rfPointer
				ELSIF type IS SyntaxTree.ProcedureType THEN char := rfDelegate
				ELSE (*ASSERT(arrayOf);*) char := rfPointer; (*RETURN (* ARRAY OF unknown (record): do not write anything *)*)
				END;
				IF arrayOf THEN
					MetaChar(module,section,CHR(ORD(char)+ORD(rfArrayFlag)));
				ELSE
					MetaChar(module,section,char)
				END;
				INC(size);
			END BaseType;

			PROCEDURE RecordType(type: SyntaxTree.RecordType);
			VAR destination: Sections.Section; name: SyntaxTree.String;
			BEGIN
				destination := module.allSections.FindBySymbolAndKind(type.typeDeclaration, Sections.RegularKind); (*TODO*)
				IF destination = NIL THEN
					destination := module.allSections.FindBySymbolAndKind(type.typeDeclaration, Sections.ImportedSymbolKind) (*TODO*)
				END;
				IF destination = NIL THEN
					(* imported unused record type *)
					MetaChar(module,section,0X); (* nil type *)
					INC(size);
					type.typeDeclaration.GetName(name);
					(*
					this happens when a symbol from a different module is used but the type desciptor is not necessary to be present in the current module
					D.Str("Warning: Unreferenced record type encountered: "); D.String(name); D.String(" unused? "); D.Ln;
					*)
				ELSE
					ASSERT((destination.kind = Sections.RegularKind) OR (destination.kind = Sections.ImportedSymbolKind));
					IF type.pointerType # NIL THEN
						MetaChar(module,section,rfRecordPointer)
					ELSE
						MetaChar(module,section,rfRecord);
					END;
					INC(size);
					MetaLongint(module,section,(destination.offset ));
					INC(size,4);
				END;
			END RecordType;

			PROCEDURE ArrayType(type: SyntaxTree.ArrayType);
			BEGIN
				IF type.arrayBase.resolved IS SyntaxTree.ArrayType THEN
					MetaChar(module,section,CHR(ORD(rfPointer)+ORD(rfArrayFlag)));
					INC(size);
				ELSE BaseType(TRUE,type.arrayBase.resolved)
				END;
				IF type.form = SyntaxTree.Static THEN
					MetaLongint(module,section,type.staticLength)
				ELSE
					MetaLongint(module,section,0)
				END;
				INC(size,4);
			END ArrayType;

			PROCEDURE MathArrayType(type: SyntaxTree.MathArrayType);
			BEGIN
				IF type.arrayBase = NIL THEN BaseType(TRUE,NIL)
				ELSIF type.arrayBase.resolved IS SyntaxTree.MathArrayType THEN
					MetaChar(module,section,CHR(ORD(rfPointer)+ORD(rfArrayFlag)));
					INC(size);
				ELSE BaseType(TRUE,type.arrayBase.resolved)
				END;
				IF type.form = SyntaxTree.Static THEN
					MetaLongint(module,section,type.staticLength)
				ELSE
					MetaLongint(module,section,0)
				END;
				INC(size,4);
			END MathArrayType;

			PROCEDURE Type(type: SyntaxTree.Type);
			BEGIN
				IF type = NIL THEN MetaChar(module,section,0X); INC(size); RETURN ELSE type := type.resolved END;

				IF type IS SyntaxTree.BasicType THEN
					BaseType(FALSE,type)
				ELSIF type IS SyntaxTree.RecordType THEN
					RecordType(type(SyntaxTree.RecordType));
				ELSIF type IS SyntaxTree.ArrayType THEN
					ArrayType(type(SyntaxTree.ArrayType))
				ELSIF type IS SyntaxTree.EnumerationType THEN
					BaseType(FALSE,module.system.longintType)
				ELSIF type IS SyntaxTree.PointerType THEN
					IF type(SyntaxTree.PointerType).pointerBase IS SyntaxTree.RecordType THEN
						RecordType(type(SyntaxTree.PointerType).pointerBase(SyntaxTree.RecordType));
					ELSE
						BaseType(FALSE,type)
					END;
				ELSIF type IS SyntaxTree.ProcedureType THEN
					BaseType(FALSE,type);
				ELSIF type IS SyntaxTree.MathArrayType THEN
					MathArrayType(type(SyntaxTree.MathArrayType));
				ELSE HALT(200)
				END;
			END Type;

			PROCEDURE WriteVariable(variable: SyntaxTree.Variable; indirect: BOOLEAN);
				VAR name: ARRAY 256 OF CHAR;
			BEGIN
				IF indirect THEN MetaChar(module,section,rfIndirect) ELSE MetaChar(module,section,rfDirect) END;
				INC(size);
				variable.GetName(name);
				Type(variable.type);
				MetaLongint(module,section,(variable.offsetInBits DIV 8));
				INC(size,4);
				MetaString(module,section,name);
				INC(size,Strings.Length(name)+1);
			END WriteVariable;

			PROCEDURE WriteParameter(variable: SyntaxTree.Parameter; indirect: BOOLEAN);
			VAR name: ARRAY 256 OF CHAR;
			BEGIN
				IF indirect THEN MetaChar(module,section,rfIndirect) ELSE MetaChar(module,section,rfDirect) END;
				INC(size);
				variable.GetName(name);
				Type(variable.type);
				MetaLongint(module,section,(variable.offsetInBits DIV 8));
				INC(size,4);
				variable.GetName(name);
				MetaString(module,section,name);
				INC(size,Strings.Length(name)+1);
			END WriteParameter;

			PROCEDURE ReturnType(type: SyntaxTree.Type);
			BEGIN
				IF type = NIL THEN MetaChar(module,section,0X); INC(size); RETURN ELSE type := type.resolved END;

				IF type IS SyntaxTree.ArrayType THEN
					WITH type: SyntaxTree.ArrayType DO
						IF type.form = SyntaxTree.Static THEN MetaChar(module,section,rfStaticArray)
						ELSE MetaChar(module,section,rfOpenArray)
						END;
						INC(size);
					END
				ELSIF type IS SyntaxTree.MathArrayType THEN
					WITH type: SyntaxTree.MathArrayType DO
						IF type.form = SyntaxTree.Static THEN MetaChar(module,section,rfStaticArray)
						ELSE MetaChar(module,section,rfOpenArray)
						END;
						INC(size);
					END
				ELSIF type IS SyntaxTree.RecordType THEN
					MetaChar(module,section,rfRecord);
					INC(size);
				ELSE
					BaseType(FALSE,type);
				END;
			END ReturnType;

			PROCEDURE DeclarationName(typeDeclaration: SyntaxTree.TypeDeclaration; VAR name: ARRAY OF CHAR);
			BEGIN
				IF typeDeclaration = NIL THEN COPY("@ANONYMOUS",name)
				ELSE typeDeclaration.GetName(name)
				END;
			END DeclarationName;


			PROCEDURE Procedure(s: Sections.Section);
			VAR procedure: SyntaxTree.Procedure; procedureType: SyntaxTree.ProcedureType;
				 parameter: SyntaxTree.Parameter; variable: SyntaxTree.Variable;
				 name,recordName: ARRAY 256 OF CHAR;
				 record: SyntaxTree.RecordType;  i: LONGINT;
			BEGIN
				procedure := s.symbol(SyntaxTree.Procedure); (*! check for variable or type symbol for object body *)
				procedure.GetName(name);
				procedureType := procedure.type(SyntaxTree.ProcedureType);

				MetaChar(module,section,0F9X);
				INC(size);
				MetaSymbol(module,section,s,0,0);
				INC(size,4);
				MetaSymbol(module,section,s,s(IntermediateCode.Section).pc,0);
				INC(size,4);
				MetaLongint(module,section,procedureType.numberParameters);
				INC(size,4);
				ReturnType(procedureType.returnType);
				MetaLongint(module,section,0); (*! level *)
				INC(size,4);
				MetaLongint(module,section,0);
				INC(size,4);
				IF procedure.scope IS SyntaxTree.RecordScope THEN (* add object name *)
					record := procedure.scope(SyntaxTree.RecordScope).ownerRecord;
					recordName := "";
					IF record.pointerType # NIL THEN
						DeclarationName(record.pointerType.typeDeclaration,recordName);
					ELSE
						DeclarationName(record.typeDeclaration,recordName);
					END;
					i := 0;
					MetaInfo(section,recordName);
					WHILE recordName[i] # 0X DO
						MetaChar(module,section,recordName[i]); INC(i);
						INC(size);
					END;
					MetaChar(module,section,".");
					INC(size);
				END;
				MetaString(module,section,name);
				INC(size,Strings.Length(name)+1);
				parameter := procedureType.firstParameter;
				WHILE(parameter # NIL) DO
					WriteParameter(parameter,parameter.kind # SyntaxTree.ValueParameter); (*!treat  exceptions !*)
					parameter := parameter.nextParameter;
				END;
				variable := procedure.procedureScope.firstVariable;
				WHILE(variable # NIL) DO
					WriteVariable(variable,FALSE);
					variable := variable.nextVariable;
				END;
			END Procedure;

			PROCEDURE Scope(s: Sections.Section);
			VAR variable: SyntaxTree.Variable;
			BEGIN
				MetaChar(module,section,0F8X);
				INC(size);
				MetaSymbol(module,section,s,0,0); (* start *)
				INC(size,4);
				MetaSymbol(module,section,s,s(IntermediateCode.Section).pc,0); (* end *)
				INC(size,4);
				MetaString(module,section,"$$");
				INC(size,3);
				variable := module.module.moduleScope.firstVariable;
				WHILE(variable # NIL) DO
					WriteVariable(variable,FALSE);
					variable := variable.nextVariable;
				END;
			END Scope;


		BEGIN
			MetaArray(module,section,sizePC);

			size := 0;
			MetaChar(module,section,0FFX); (* sign for trap writer *)
			INC(size);

			FOR i := 0 TO module.allSections.Length() - 1 DO
				s := module.allSections.GetSection(i);
				IF s.kind = Sections.RegularKind THEN
				IF (s.type # Sections.InitCodeSection) & (s.symbol = module.module.moduleScope.bodyProcedure) THEN
					Scope(s) (*! must be first procedure in ref section *)
				END
				END
			END;

			FOR i := 0 TO module.allSections.Length() - 1 DO
				s := module.allSections.GetSection(i);
				IF s.kind = Sections.RegularKind THEN
				IF (s.symbol = module.module.moduleScope.bodyProcedure) THEN (* already done, see above *)
				ELSIF (s.type # Sections.InitCodeSection) & (s.symbol # NIL) & (s.symbol IS SyntaxTree.Procedure) & ~s.symbol(SyntaxTree.Procedure).isInline THEN
					Procedure(s)
				END
				END
			END;

			PatchLongint(module,section,sizePC,size);

		END MetaReferences;

	(*
	Command* = RECORD
		(* Fields exported for initialization by loader/linker only! Consider read-only! *)
		name*: Name; (* name of the procedure *)
		argTdAdr*, retTdAdr* : SYSTEM.ADDRESS; (* address of type descriptors of argument and return type, 0 if no type *)
		entryAdr* : SYSTEM.ADDRESS; (* entry address of procedure *)
	END;
	*)
	PROCEDURE MetaCommandArray(module: Sections.Module; source: IntermediateCode.Section);
	VAR
		p: Sections.Section;  sizePC, numberCommands: LONGINT;
		procedure : SyntaxTree.Procedure; procedureType: SyntaxTree.ProcedureType;
		name: ARRAY 32 OF CHAR; numberParameters, i: LONGINT;

			(* Returns TRUE if the built-in function GETPROCEDURE can be used with this procedure type *)
			PROCEDURE GetProcedureAllowed() : BOOLEAN;

				PROCEDURE TypeAllowed(type : SyntaxTree.Type) : BOOLEAN;
				BEGIN
					RETURN
						(type = NIL) OR
						(type.resolved IS SyntaxTree.RecordType) OR
						(type.resolved IS SyntaxTree.PointerType) & (type.resolved(SyntaxTree.PointerType).pointerBase.resolved IS SyntaxTree.RecordType);
				END TypeAllowed;

			BEGIN
				numberParameters := procedureType.numberParameters;
				RETURN
					(numberParameters = 0) & TypeAllowed(procedureType.returnType) OR
					(numberParameters = 1) & TypeAllowed(procedureType.firstParameter.type) & TypeAllowed(procedureType.returnType) OR
					(numberParameters = 1) & (procedureType.firstParameter.type.resolved IS SyntaxTree.AnyType) & (procedureType.returnType # NIL) & (procedureType.returnType.resolved IS SyntaxTree.AnyType);
			END GetProcedureAllowed;

			PROCEDURE WriteType(type : SyntaxTree.Type);
			VAR typeDeclaration: SyntaxTree.TypeDeclaration; section: Sections.Section;
				name: Basic.PooledName;
			BEGIN
				IF type = NIL THEN
					MetaAddress(module,source,0);
				ELSIF (type.resolved IS SyntaxTree.AnyType) OR (type.resolved IS SyntaxTree.ObjectType) THEN
					MetaAddress(module,source,1);
				ELSE
					type := type.resolved;
					IF type IS SyntaxTree.PointerType THEN
						type := type(SyntaxTree.PointerType).pointerBase.resolved;
					END;
					typeDeclaration := type.typeDeclaration; (* must be non-nil *)
					IF (typeDeclaration.scope = NIL) OR (typeDeclaration.scope.ownerModule = module.module) THEN
						name[0] := typeDeclaration.name; name[1] := -1;
						section := module.allSections.FindBySymbolAndKind(type.typeDeclaration, Sections.RegularKind); (*TODO*)
						ASSERT(section # NIL);
						ASSERT(section.kind = Sections.RegularKind);
					ELSE
						Global.GetSymbolPooledName(typeDeclaration,name);
						(* TODO *)
						section := IntermediateCode.NewSection(module.allSections, Sections.ImportedSymbolKind,Sections.ConstSection, FALSE, name,typeDeclaration, source.comments # NIL);
					END;
					MetaSymbol(module,source,section, 0, ToMemoryUnits(module.system,(1 + type(SyntaxTree.RecordType).recordScope.numberMethods+16+1)*module.system.addressSize));
				END;
			END WriteType;

	BEGIN
		MetaInfo(source, "command array descriptor");
		MetaArray(module,source,sizePC);
		numberCommands := 0;
		MetaInfo(source, "command array content");

		FOR i := 0 TO module.allSections.Length() - 1 DO
			p := module.allSections.GetSection(i);
			IF p.kind = Sections.RegularKind THEN
			IF (p.symbol # NIL) & (p.symbol IS SyntaxTree.Procedure)  THEN
				procedure := p.symbol(SyntaxTree.Procedure);
				procedureType := procedure.type(SyntaxTree.ProcedureType);
				IF (SyntaxTree.PublicRead IN procedure.access) & ~(procedure.isInline) & ~(procedureType.isDelegate) & GetProcedureAllowed() THEN
					procedure.GetName(name);
					MetaName(module,source,name);
					numberParameters := procedureType.numberParameters;
					(* offset of type of first parameter *)
					IF (numberParameters = 0 ) THEN WriteType(NIL)
					ELSE WriteType(procedureType.firstParameter.type)
					END;
					(* offset of type of return parameter *)
					WriteType(procedureType.returnType);
					(* command name *)
					(* command code offset *)
					MetaSymbol(module,source,p,0,0);
					INC(numberCommands);
					IF Trace THEN
						D.Ln;
					END;
				END;
			END
			END
		END;
		PatchLongint(module,source,sizePC,numberCommands);
	END MetaCommandArray;

	PROCEDURE MetaTypeInfoSection(module: Sections.Module; source: IntermediateCode.Section);
	VAR
		p: Sections.Section; sizePC, size, i: LONGINT;
	BEGIN
		MetaInfo(source, "command array descriptor");
		size := 0;
		MetaArray(module,source,sizePC);
		FOR i := 0 TO module.allSections.Length() - 1 DO
			p := module.allSections.GetSection(i);
			IF p.kind = Sections.RegularKind THEN
			WITH p: IntermediateCode.Section DO
					IF Basic.PooledNameEndsWith(p.name,"@Info") THEN
					MetaSymbol(module,source,p,0,0);
					INC(size);
				END;
			END
			END
		END;
		PatchLongint(module,source,sizePC,size);
	END MetaTypeInfoSection;

	(*
		ProcTableEntry* = RECORD
			pcFrom*, pcLimit*, pcStatementBegin*, pcStatementEnd*: SYSTEM.ADDRESS;
			noPtr*: LONGINT;
		END;

		ProcTable* = POINTER TO ARRAY OF ProcTableEntry;

		PtrTable* = POINTER TO ARRAY OF SYSTEM.ADDRESS;
	*)

	PROCEDURE MetaPointersInProcTables(module: Sections.Module; procArray, pointerArray: IntermediateCode.Section; VAR procArraySize, maxPointers: LONGINT);
	VAR
		destination: Sections.Section;
		pointerArraySizePC, procArraySizePC, pointerArraySize, i: LONGINT;

		PROCEDURE PointerOffsets(destination : IntermediateCode.Section);
		VAR numberPointers: LONGINT; procedure: SyntaxTree.Procedure; procedureType: SyntaxTree.ProcedureType;
			variable: SyntaxTree.Variable; parameter: SyntaxTree.Parameter; string: SyntaxTree.String;
		BEGIN
			MetaInfo(procArray,"pcFrom");
			MetaSymbol(module,procArray,destination,0,0);
			MetaInfo(procArray,"pcTo");
			MetaSymbol(module,procArray,destination,destination.pc,0);
			MetaInfo(procArray,"pcStatementBegin");
			MetaSymbol(module,procArray,destination,destination.validPAFEnter,0);
			MetaInfo(procArray,"pcStatementEnd");
			MetaSymbol(module,procArray,destination,destination.validPAFExit,0);
			Basic.FromPooledName(destination.name, string);
			MetaInfo(pointerArray,string);
			procedure := destination.symbol(SyntaxTree.Procedure);
			procedureType := procedure.type(SyntaxTree.ProcedureType);
			variable := procedure.procedureScope.firstVariable;
			WHILE(variable # NIL) DO
				IF ~(variable.untraced) THEN
					MetaPointers(variable.offsetInBits DIV 8, NIL, module, pointerArray, variable.type, numberPointers);
				END;
				variable := variable.nextVariable
			END;
			parameter := procedureType.firstParameter;
			WHILE(parameter # NIL) DO
				IF ~(parameter.untraced) THEN
					MetaPointers(parameter.offsetInBits DIV 8, NIL, module, pointerArray, parameter.type, numberPointers);
				END;
				parameter := parameter.nextParameter;
			END;
			MetaInfo(procArray,"numberPointers");
			MetaLongint(module,procArray,numberPointers);
			IF numberPointers > maxPointers THEN maxPointers := numberPointers END;
			INC(pointerArraySize, numberPointers);
		END PointerOffsets;

	BEGIN
		maxPointers := 0;
		MetaInfo(procArray, "proc array descriptor");
		MetaAddress(module,procArray,0);
		MetaAddress(module,procArray,0);
		MetaAddress(module,procArray,0);
		procArraySizePC := procArray.pc;
		MetaAddress(module,procArray,0);
		procArraySize := 0;
		MetaInfo(pointerArray, "pointer array descriptor");
		MetaAddress(module,pointerArray,0);
		MetaAddress(module,pointerArray,0);
		MetaAddress(module,pointerArray,0);
		pointerArraySizePC := pointerArray.pc;
		MetaAddress(module,pointerArray,0);
		pointerArraySize := 0;
		procArraySize := 0;
		FOR i := 0 TO module.allSections.Length() - 1 DO
			destination := module.allSections.GetSection(i);
			IF destination.kind = Sections.RegularKind THEN
			IF (destination.type IN {Sections.CodeSection, Sections.BodyCodeSection}) & (destination.symbol # NIL) & (destination.symbol IS SyntaxTree.Procedure) & ~destination.symbol(SyntaxTree.Procedure).isInline THEN
				PointerOffsets(destination(IntermediateCode.Section));
				INC(procArraySize);
			END
			END
		END;

		PatchLongint(module,procArray,procArraySizePC,procArraySize);
		PatchLongint(module,pointerArray,pointerArraySizePC,pointerArraySize);
	END MetaPointersInProcTables;

	(*
		Module* = OBJECT (Heaps.RootObject)	(* cf. Linker0 & Heaps.WriteType *)
		VAR
			next*: Module;	(** once a module is published, all fields are read-only *)
			name*: Name;
			init, published: BOOLEAN;
			refcnt*: LONGINT; (* counts loaded modules that import this module *)
			sb*: SYSTEM.ADDRESS; <- set to beginning of data section by loader
			entry*: POINTER TO ARRAY OF SYSTEM.ADDRESS; <- not needed in new loader
			command*: POINTER TO ARRAY OF Command;
			ptrAdr*: POINTER TO ARRAY OF SYSTEM.ADDRESS;
			typeInfo*: POINTER TO ARRAY OF TypeDesc;
			module*: POINTER TO ARRAY OF Module; <---- currently done by loader
			procTable*: ProcTable; (* information inserted by loader, removed after use in Publish *)
			ptrTable*: PtrTable;  (* information inserted by loader, removed after use in Publish *)
			data*, code*: Bytes;
			staticTypeDescs* (* ug *), refs*: Bytes; <- staticTypeDescs in data section, refs currently unsupported
			export*: ExportDesc;
			term*: TerminationHandler;
			exTable*: ExceptionTable;
			noProcs*: LONGINT;
			firstProc*: SYSTEM.ADDRESS; <-   done by loader
			maxPtrs*: LONGINT;
	*)

	PROCEDURE MetaModuleSection(implementationVisitor: ImplementationVisitor; module: Sections.Module): IntermediateCode.Section;
	VAR name: ARRAY 128 OF CHAR; moduleSection,moduleTD: IntermediateCode.Section; offset: LONGINT; pooledName: Basic.PooledName;
	BEGIN
		Global.GetModuleName(module.module,name);
		Strings.Append(name,".@Module");
		Basic.ToPooledName(name, pooledName);
		moduleSection := IntermediateCode.NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, pooledName,NIL,TRUE);
		IF moduleSection.pc = 0 THEN
			MetaProtectedHeapBlock(implementationVisitor,"Heaps","ProtRecBlockDesc",module,moduleSection,2);
			MetaInfo(moduleSection, "HeapBlock");
			MetaSymbol(module,moduleSection,moduleSection,2,0);
			MetaInfo(moduleSection, "TypeDescriptor");
			moduleTD := implementationVisitor.GetTypeDescriptor("Modules","Module");
			offset := ToMemoryUnits(module.system,(1 + 1 (*= numberMethods*) +16+1)*module.system.addressSize);
			MetaSymbol(module,moduleSection, moduleTD, 0, offset);
		END;
		RETURN moduleSection;
	END MetaModuleSection;


	PROCEDURE MetaModule(implementationVisitor: ImplementationVisitor; module: Sections.Module);
	VAR moduleName: ARRAY 128 OF CHAR;
	moduleSection, pointerSection, emptyArraySection, exportDescArray, exceptionSection, commandsSection,
		typeInfoSection, procTableSection, ptrTableSection, referenceSection : IntermediateCode.Section;
		emptyArraySectionOffset, pointerSectionOffset, numberPointers, exportDescArrayOffset, exportDescSize,
		exceptionSectionOffset, commandsSectionOffset, typeInfoSectionOffset, procTableSectionOffset, ptrTableSectionOffset, maxPointers, numberProcs,temp,
		referenceSectionOffset	: LONGINT;



		PROCEDURE HeapBlock(CONST mName, typeName, suffix: ARRAY OF CHAR; VAR offset: LONGINT): IntermediateCode.Section;
		VAR name: ARRAY 128 OF CHAR; section: IntermediateCode.Section; pooledName: Basic.PooledName;
		BEGIN
			COPY(moduleName,name);
			Strings.Append(name,suffix);
			Basic.ToPooledName(name, pooledName);
			section := IntermediateCode.NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, pooledName, NIL,TRUE);
			MetaHeapBlock(implementationVisitor,mName,typeName,module,section,2);
			MetaInfo(section, "HeapBlock");
			(*
			Symbol(module,section,section,2,0);
			*)
			MetaAddress(module,section,0); (* empty such that GC does not go on traversing *)
			MetaInfo(section, "TypeDescriptor");
			MetaAddress(module,section,0);
			offset := section.pc;
			RETURN section
		END HeapBlock;


	BEGIN
		Global.GetModuleName(module.module,moduleName);
		exportDescArray := HeapBlock("Heaps","SystemBlockDesc",".@ExportDescArray",exportDescArrayOffset);
		MetaExportDescArray(module,exportDescArray, exportDescSize);
		pointerSection := HeapBlock("Heaps","SystemBlockDesc",".@PointerArray",pointerSectionOffset);
		MetaPointerArray(module,pointerSection,module.module.moduleScope, numberPointers);
		commandsSection := HeapBlock("Heaps","SystemBlockDesc",".@CommandArray",commandsSectionOffset);
		MetaCommandArray(module,commandsSection);
		exceptionSection := HeapBlock("Heaps","SystemBlockDesc",".@ExceptionArray",exceptionSectionOffset);
		MetaExceptionArray(module,exceptionSection);
		typeInfoSection := HeapBlock("Heaps","SystemBlockDesc",".@TypeInfoArray",typeInfoSectionOffset);
		MetaTypeInfoSection(module,typeInfoSection);
		referenceSection := HeapBlock("Heaps","SystemBlockDesc",".@References",referenceSectionOffset);
		MetaReferences(module,referenceSection);
		procTableSection := HeapBlock("Heaps","SystemBlockDesc",".@ProcTable",procTableSectionOffset);
		ptrTableSection := HeapBlock("Heaps","SystemBlockDesc",".@PtrTable",ptrTableSectionOffset);
		MetaPointersInProcTables(module,procTableSection,ptrTableSection,numberProcs,maxPointers);
		emptyArraySection := HeapBlock("Heaps","SystemBlockDesc",".@EmptyArray",emptyArraySectionOffset);
		MetaArray(module,emptyArraySection,temp);
		moduleSection := MetaModuleSection(implementationVisitor, module);
		MetaInfo(moduleSection, "nextRoot*: RootObject");
		MetaAddress(module,moduleSection,0);
		MetaInfo(moduleSection, "next*: Module");
		MetaAddress(module,moduleSection,0);
		MetaInfo(moduleSection, "name*: Name");
		MetaName(module,moduleSection,moduleName);
		MetaInfo(moduleSection, "init, published: BOOLEAN");
		MetaBoolean(module,moduleSection,FALSE);
		MetaBoolean(module,moduleSection,FALSE);
		MetaInfo(moduleSection,"filler"); (*! introduce alignment! *)
		MetaBoolean(module,moduleSection,FALSE);
		MetaBoolean(module,moduleSection,FALSE);
		MetaInfo(moduleSection, "refcnt*: LONGINT");
		MetaLongint(module,moduleSection,0);
		MetaInfo(moduleSection, "sb*: SYSTEM.ADDRESS");
		MetaAddress(module,moduleSection,0);
		MetaInfo(moduleSection, "entry*: POINTER TO ARRAY OF SYSTEM.ADDRESS");
		MetaSymbol(module,moduleSection,emptyArraySection,emptyArraySectionOffset,0);
		MetaInfo(moduleSection, "command*: POINTER TO ARRAY OF Command");
		MetaSymbol(module,moduleSection,commandsSection,commandsSectionOffset,0);
		MetaInfo(moduleSection, "ptrAdr*: POINTER TO ARRAY OF SYSTEM.ADDRESS");
		MetaSymbol(module,moduleSection,pointerSection,pointerSectionOffset,0);
		MetaInfo(moduleSection, "typeInfo*: POINTER TO ARRAY OF TypeDesc");
		MetaSymbol(module,moduleSection,typeInfoSection,typeInfoSectionOffset,0);
		MetaInfo(moduleSection, "module*: POINTER TO ARRAY OF Module");
		MetaSymbol(module,moduleSection,emptyArraySection,emptyArraySectionOffset,0);
		MetaInfo(moduleSection, "procTable*: ProcTable");
		MetaSymbol(module,moduleSection,procTableSection,procTableSectionOffset,0);
		MetaInfo(moduleSection, "ptrTable*: PtrTable");
		MetaSymbol(module,moduleSection,ptrTableSection,ptrTableSectionOffset,0);
		MetaInfo(moduleSection, "data*, code*, staticTypeDescs*, refs*: Bytes");
		MetaSymbol(module,moduleSection,emptyArraySection,emptyArraySectionOffset,0);
		MetaSymbol(module,moduleSection,emptyArraySection,emptyArraySectionOffset,0);
		MetaSymbol(module,moduleSection,emptyArraySection,emptyArraySectionOffset,0);
		MetaSymbol(module,moduleSection,referenceSection,referenceSectionOffset,0);
		MetaInfo(moduleSection, "export*: ExportDesc");
		MetaAddress(module,moduleSection,0);
		MetaAddress(module,moduleSection,0);
		MetaLongint(module,moduleSection,exportDescSize);
		MetaSymbol(module,moduleSection,exportDescArray, exportDescArrayOffset,0);
		MetaInfo(moduleSection, "term*: TerminationHandler");
		MetaAddress(module,moduleSection,0);
		MetaInfo(moduleSection, "exTable*: ExceptionTable");
		MetaSymbol(module,moduleSection,exceptionSection,exceptionSectionOffset,0);
		MetaInfo(moduleSection, "noProcs*: LONGINT");
		MetaLongint(module,moduleSection,numberProcs);
		MetaInfo(moduleSection, "firstProc*: SYSTEM.ADDRESS");
		MetaAddress(module,moduleSection,0);
		MetaInfo(moduleSection, "maxPtrs*: LONGINT");
		MetaLongint(module,moduleSection,maxPointers);
	END MetaModule;

	PROCEDURE MetaPointerArray(module: Sections.Module; source: IntermediateCode.Section; scope: SyntaxTree.Scope; VAR numberPointers: LONGINT);
	VAR variable: SyntaxTree.Variable; pc: LONGINT; symbol: Sections.Section;
	BEGIN
		MetaArray(module,source,pc);

		MetaInfo(source, "pointer offsets array data");
		IF scope IS SyntaxTree.RecordScope THEN
			MetaPointers(0,symbol, module,source,scope(SyntaxTree.RecordScope).ownerRecord,numberPointers);
		ELSIF scope IS SyntaxTree.ModuleScope THEN
			variable := scope(SyntaxTree.ModuleScope).firstVariable;
			WHILE variable # NIL DO
				IF ~(variable.untraced) THEN
					symbol := module.allSections.FindBySymbolAndKind(variable, Sections.RegularKind); (*TODO*)
					ASSERT(symbol # NIL);
					ASSERT(symbol.kind = Sections.RegularKind);
					MetaPointers(0,symbol, module,source,variable.type,numberPointers);
				END;
				variable := variable.nextVariable;
			END;
		END;
		PatchLongint(module,source,pc,numberPointers);
	END MetaPointerArray;


	PROCEDURE CheckTypeDeclaration(implementationVisitor: ImplementationVisitor; module: Sections.Module; x: SyntaxTree.Type; dump,newObjectFile: BOOLEAN);
	VAR recordType: SyntaxTree.RecordType;
		tir: IntermediateCode.Section; op: IntermediateCode.Operand; name: Basic.PooledName; td: SyntaxTree.TypeDeclaration;
		section: Sections.Section; string: SyntaxTree.String;

		PROCEDURE NewTypeDescriptorInfo(tag: Sections.Section; offset: LONGINT; isProtected: BOOLEAN): Sections.Section;
		VAR name: Basic.PooledName;source: IntermediateCode.Section;
			moduleSection: IntermediateCode.Section; i: LONGINT; flags: SET;
		CONST MPO=-40000000H;
		BEGIN
				(*
					TypeDesc* = POINTER TO RECORD
						descSize: LONGINT;
						sentinel: LONGINT;	(* = MPO-4 *)
						tag*: SYSTEM.ADDRESS; (* pointer to static type descriptor, only used by linker and loader *)
						flags*: SET;
						mod*: Module;	(* hint only, because module may have been freed (at Heaps.ModOfs) *)
						name*: Name;
					END;
				*)
				(* source := module.sections.FindByName(...) *)
				Global.GetSymbolPooledName(td,name);
				Basic.AppendToPooledName(name,"@Info");
				source := IntermediateCode.NewSection(module.allSections, Sections.RegularKind, Sections.ConstSection, TRUE, name,NIL,dump);
				MetaInfo(source, "type info size");	MetaAddress(module,source, 3*module.system.addressSize DIV 8+32);
				MetaAddress(module,source,MPO-4);
				MetaInfo(source, "type tag pointer");
				MetaSymbol(module, source, tag, offset, 0);
				MetaInfo(source, "type flags");
				flags := {};
				IF isProtected THEN INCL(flags,31) END;
				MetaSet(module, source, flags);
				MetaInfo(source, "pointer to module");
				moduleSection := MetaModuleSection(implementationVisitor,module);
				MetaSymbol(module, source, moduleSection,moduleSection.pc,0);
				MetaInfo(source, "type name");
				i := 0;
				Global.GetSymbolPooledName(td,name);
				Basic.FromPooledName(name, string);
				MetaName(module,source,string);
				source.SetReferenced(FALSE);
				RETURN source;
		END NewTypeDescriptorInfo;

		PROCEDURE GetSection(x: SyntaxTree.Procedure): Sections.Section;
		VAR source: IntermediateCode.Section; sectionType: SHORTINT; name: Basic.PooledName;
		BEGIN
			Global.GetSymbolPooledName(x,name);
			IF x.isInline THEN
				sectionType := Sections.InlineCodeSection;
			ELSE
				sectionType := Sections.CodeSection;
			END;
			IF (x.scope.ownerModule = module.module) THEN
				source := IntermediateCode.NewSection(module.allSections, Sections.RegularKind,sectionType, TRUE, name,x,dump);
			ELSIF (sectionType = Sections.InlineCodeSection) & (x.procedureScope.body.code.sourceCode # NIL) THEN
				HALT(200);
			ELSE
				source := IntermediateCode.NewSection(module.allSections, Sections.ImportedSymbolKind,sectionType, FALSE, name,x,dump);
			END;
			RETURN source
		END GetSection;

		PROCEDURE NewTypeDescriptor;
		VAR name: Basic.PooledName; op: IntermediateCode.Operand; source: IntermediateCode.Section;
			i,methods: LONGINT;
			procedure: SyntaxTree.Procedure;
			baseRecord: SyntaxTree.RecordType; baseTD: SyntaxTree.TypeDeclaration;
			numberPointers: LONGINT;  padding,offset: LONGINT;
		CONST MPO=-40000000H;
		BEGIN
				Global.GetSymbolPooledName(td,name);
				source := IntermediateCode.NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,td,dump);

				(*
								MethodEnd = MPO
								---
								methods (# methods)
								---
								tags (16)
								---
								TypeDesc = TypeInfoAdr
								---
				td adr ---> 	rec size
								----
								pointer offsets
								----
								(padding)
								-----
								empty [2 addresses aligned]
								empty
								empty
								numPtrs
								---
								pointer offsets
								---
				*)

				MetaInfo(source, "MethodEnd = MPO");
				IntermediateCode.InitImmediate(op,IntermediateCode.GetType(module.system, module.system.addressType),MPO);
				source(IntermediateCode.Section).Emit(Data(op));

				MetaInfo(source, "method table");
				methods := recordType.recordScope.numberMethods;
				FOR i := methods-1 TO 0 BY -1 DO
					procedure := recordType.recordScope.FindMethod(i);
					MetaSymbol(module,source, GetSection(procedure),0,0);
				END;

				MetaInfo(source, "tag table");
				baseRecord := recordType;
				i := 0;
				WHILE baseRecord # NIL DO
					INC(i);
					baseRecord := baseRecord.GetBaseRecord();
				END;
				WHILE i < 16 DO
					MetaAddress(module,source,0);
					INC(i);
				END;
				baseRecord := recordType;
				WHILE baseRecord # NIL DO
					baseTD := baseRecord.typeDeclaration;
					Global.GetSymbolPooledName(baseTD,name);
					IF (baseTD.scope = NIL) OR (baseTD.scope.ownerModule = module.module) THEN
						tir := IntermediateCode.NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,baseTD,dump);
					ELSE
						tir := IntermediateCode.NewSection(module.allSections, Sections.ImportedSymbolKind, Sections.ConstSection, FALSE, name,baseTD,dump);
					END;
					offset := ToMemoryUnits(module.system,(1 + baseRecord.recordScope.numberMethods+16+1)*module.system.addressSize);
					MetaSymbol(module,source, tir, 0, offset);
					baseRecord := baseRecord.GetBaseRecord();
				END;
				MetaInfo(source, "type descriptor info pointer");
				MetaSymbol(module,source, NewTypeDescriptorInfo(source,source.pc+1,recordType.IsProtected()),0,0);
				MetaInfo(source, "record size");
				MetaAddress(module,source, module.system.SizeOf(recordType) DIV 8 (* in bytes *));
				MetaInfo(source, "pointer offsets pointer");
				padding := 1- source.pc MOD 2;
				MetaSymbol(module,source, source, source.pc+1+padding,0);
				IF padding >0 THEN
					MetaInfo(source, "padding");
					FOR i := 1 TO padding DO MetaAddress(module,source,0) END;
				END;
				MetaPointerArray(module,source, recordType.recordScope, numberPointers);
				source.SetReferenced(FALSE);
		END NewTypeDescriptor;

	BEGIN
		x := x.resolved;
		IF (x IS SyntaxTree.PointerType) THEN
			x := x(SyntaxTree.PointerType).pointerBase.resolved;
		END;

		IF (x IS SyntaxTree.RecordType) THEN (* enter: insert only if not already inserted *)
			recordType := x(SyntaxTree.RecordType);
			td := x.typeDeclaration;
			IF td = NIL THEN td := recordType.pointerType.resolved.typeDeclaration END; (* for compatibility with paco *)
			ASSERT(td # NIL);

			section := module.allSections.FindBySymbolAndKind(td, Sections.RegularKind); (* TODO *)
			ASSERT((section = NIL) OR (section.kind = Sections.RegularKind));
			IF (section = NIL) OR (section(IntermediateCode.Section).pc = 0) THEN
				IF newObjectFile THEN
					IF (td.scope = NIL) OR (td.scope.ownerModule = module.module) THEN
						NewTypeDescriptor
					END;
				ELSE
					(* data section in intermediate code *)
					Global.GetSymbolPooledName(td,name);
					tir := IntermediateCode.NewSection(module.allSections, Sections.RegularKind,Sections.ConstSection, TRUE, name,td,dump);
					IntermediateCode.InitImmediate(op,IntermediateCode.GetType(module.system, module.system.addressType),0);
					tir.Emit(Data(op));
				END;
			END;

		END
	END CheckTypeDeclaration;

	PROCEDURE InitOperand(VAR op: Operand; mode: SHORTINT);
	BEGIN
		op.mode := mode;
		IntermediateCode.InitOperand(op.op);
		IntermediateCode.InitOperand(op.tag);
		IntermediateCode.InitOperand(op.extra);
		op.dimOffset := 0;
	END InitOperand;

	(* TODO: remove this, and redirect calls to 'IntermediateCode.GetType' directly *)
	PROCEDURE GetType*(system: Global.System; type: SyntaxTree.Type): IntermediateCode.Type;
	BEGIN RETURN IntermediateCode.GetType(system, type)
	END GetType;

	PROCEDURE UniqueId(VAR name: ARRAY OF CHAR; module: SyntaxTree.Module; CONST base: ARRAY OF CHAR; VAR number: LONGINT);
	VAR n: SyntaxTree.String;
	BEGIN
		COPY(base,n);
		Global.GetModuleName(module,name);
		Strings.Append(name,"."); Strings.Append(name,"@"); Strings.Append(name,n); Basic.AppendNumber(name,number);
		INC(number);
	END UniqueId;

	PROCEDURE BuildConstant(module: SyntaxTree.Module; value: SyntaxTree.Value; VAR adr: LONGINT): SyntaxTree.Constant;
	VAR name: Scanner.StringType; constant: SyntaxTree.Constant;
	BEGIN
		name := "@const"; Basic.AppendNumber(name, adr); INC(adr);
		(*
		UniqueId(name,module,name,adr);
		*)
		constant := SyntaxTree.NewConstant(-1,SyntaxTree.NewIdentifier(name));
		constant.SetValue(value);
		module.moduleScope.AddConstant(constant);
		RETURN constant
	END BuildConstant;

	PROCEDURE IsIntegerConstant(expression: SyntaxTree.Expression; VAR val: HUGEINT): BOOLEAN;
	BEGIN
		IF expression.resolved # NIL THEN expression := expression.resolved END;

		IF  (expression IS SyntaxTree.IntegerValue)  THEN
			val := expression(SyntaxTree.IntegerValue).value;
			RETURN TRUE
		ELSE
			RETURN FALSE
		END;
	END IsIntegerConstant;

	PROCEDURE PowerOf2(val: HUGEINT;  VAR exp: LONGINT): BOOLEAN;
	BEGIN
		IF val <= 0 THEN  RETURN FALSE END;
		exp := 0;
		WHILE ~ODD(val) DO
			val := val DIV 2;
			INC(exp)
		END;
		RETURN val = 1
	END PowerOf2;

	PROCEDURE GetConstructor(record: SyntaxTree.RecordType): SyntaxTree.Procedure;
	VAR procedure: SyntaxTree.Procedure;
	BEGIN
		procedure := record.recordScope.constructor;
		IF procedure = NIL THEN
			record := record.GetBaseRecord();
			IF record # NIL THEN
				procedure := GetConstructor(record)
			END;
		END;
		RETURN procedure;
	END GetConstructor;

	PROCEDURE IsIntegerImmediate(CONST op: IntermediateCode.Operand; VAR value: LONGINT): BOOLEAN;
	BEGIN
		value := SHORT(op.intValue);
		RETURN op.mode = IntermediateCode.ModeImmediate;
	END IsIntegerImmediate;

	(* nopov *)
	(** whether a type strictily is a pointer to record or object type
	(however, the basic type <<OBJECT>> is explicitly excluded) **)
	PROCEDURE IsStrictlyPointerToRecord(type: SyntaxTree.Type): BOOLEAN;
	BEGIN
		IF type = NIL THEN
			RETURN FALSE
		ELSIF type.resolved IS SyntaxTree.PointerType THEN
			RETURN type.resolved(SyntaxTree.PointerType).pointerBase.resolved IS SyntaxTree.RecordType
		ELSE
			RETURN FALSE
		END
	END IsStrictlyPointerToRecord;

	PROCEDURE IsPointerToRecord(type: SyntaxTree.Type; VAR recordType: SyntaxTree.RecordType): BOOLEAN;
	BEGIN type := type.resolved;
		IF type IS SyntaxTree.PointerType THEN
			type := type(SyntaxTree.PointerType).pointerBase;
			type := type.resolved;
			IF type IS SyntaxTree.RecordType THEN
				recordType := type(SyntaxTree.RecordType);
				RETURN TRUE
			ELSE
				RETURN FALSE
			END
		ELSIF type IS SyntaxTree.RecordType THEN
			recordType := type(SyntaxTree.RecordType);
			RETURN type(SyntaxTree.RecordType).pointerType # NIL
		ELSIF type IS SyntaxTree.ObjectType THEN
			RETURN TRUE
		ELSIF type IS SyntaxTree.AnyType THEN
			RETURN TRUE (*! potentially is a pointer to record, treat it this way?? *)
		ELSE
			HALT(200)
		END;
	END IsPointerToRecord;

	PROCEDURE IsArrayOfSystemByte(type: SyntaxTree.Type): BOOLEAN;
	BEGIN
		type := type.resolved;
		RETURN (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form = SyntaxTree.Open)
		& (type(SyntaxTree.ArrayType).arrayBase.resolved IS SyntaxTree.ByteType);
	END IsArrayOfSystemByte;

	PROCEDURE IsOpenArray(type: SyntaxTree.Type): BOOLEAN;
	BEGIN
		IF type = NIL THEN RETURN FALSE END;
		type := type.resolved;
		RETURN (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form = SyntaxTree.Open);
	END IsOpenArray;

	PROCEDURE IsStaticArray(type: SyntaxTree.Type): BOOLEAN;
	BEGIN
		IF type = NIL THEN RETURN FALSE END;
		type := type.resolved;
		RETURN (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form = SyntaxTree.Static);
	END IsStaticArray;

	PROCEDURE IsDelegate(type: SyntaxTree.Type): BOOLEAN;
	BEGIN
		IF type = NIL THEN RETURN FALSE END;
		type := type.resolved;
		RETURN (type IS SyntaxTree.ProcedureType) & (type(SyntaxTree.ProcedureType).isDelegate)
	END IsDelegate;

	PROCEDURE DynamicDim(type:SyntaxTree.Type): LONGINT;
	VAR i: LONGINT;
	BEGIN
		i := 0; type := type.resolved;
		WHILE(type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form # SyntaxTree.Static) DO
			INC(i);
			type := type(SyntaxTree.ArrayType).arrayBase.resolved;
		END;
		WHILE(type # NIL) & (type IS SyntaxTree.MathArrayType) & (type(SyntaxTree.MathArrayType).form # SyntaxTree.Static) DO
			INC(i);
			type := type(SyntaxTree.MathArrayType).arrayBase;
			IF type # NIL THEN type := type.resolved END;
		END;
		RETURN i
	END DynamicDim;

	(*
	PROCEDURE ParametersSize(system: Global.System; procedureType: SyntaxTree.ProcedureType; isNested: BOOLEAN): LONGINT;
	VAR parSize: LONGINT; parameter: SyntaxTree.Parameter;

		PROCEDURE Parameter(parameter: SyntaxTree.Parameter);
		BEGIN
			IF parameter # NIL THEN
				INC(parSize,system.SizeOfParameter(parameter));
				parSize := parSize + (-parSize) MOD system.addressSize;
			END;
		END Parameter;

	BEGIN
		parSize := 0;
		Parameter(procedureType.selfParameter);
		parameter :=procedureType.lastParameter;
		WHILE (parameter # NIL) DO
			Parameter(parameter);
			parameter := parameter.prevParameter;
		END;

		(*
		IF procedureType.HasFlag(SyntaxTree.DelegateFlag) THEN INC(parSize,system.addressSize) END; (* method => self pointer *)
			NO, SELF is encoded as regular parameter
		*)
		IF isNested THEN INC(parSize,system.addressSize) END; (* nested procedure => static base *)
		IF NeedsStructuredReturnType(procedureType) THEN
			IF procedureType.returnParameter = NIL THEN (* otherwise handled by caller *)
				parSize := parSize + 2*system.addressSize
			END
		END;

		RETURN ToMemoryUnits(system,parSize)
	END ParametersSize;
	*)

	PROCEDURE ParametersSize(system: Global.System; procedureType: SyntaxTree.ProcedureType; isNested: BOOLEAN): LONGINT;
	VAR parSize: LONGINT; parameter: SyntaxTree.Parameter;
	BEGIN
		parSize := 0;

		IF StructuredReturnType(procedureType) THEN
			parameter := procedureType.returnParameter;
			INC(parSize,system.SizeOfParameter(parameter));
			parSize := parSize + (-parSize) MOD system.addressSize;
		END;

		parameter :=procedureType.lastParameter;
		WHILE (parameter # NIL) DO
			INC(parSize,system.SizeOfParameter(parameter));
			parSize := parSize + (-parSize) MOD system.addressSize;
			parameter := parameter.prevParameter;
		END;

		IF procedureType.isDelegate THEN INC(parSize,system.addressSize) END; (* method => self pointer *)
		IF isNested THEN INC(parSize,system.addressSize) END; (* nested procedure => static base *)

		RETURN ToMemoryUnits(system,parSize)
	END ParametersSize;

	PROCEDURE ReturnedAsParameter(type: SyntaxTree.Type): BOOLEAN;
	BEGIN
		IF type = NIL THEN RETURN FALSE
		ELSE
			type := type.resolved;
			RETURN (type IS SyntaxTree.RecordType) OR (type IS SyntaxTree.RangeType) OR (type IS SyntaxTree.ProcedureType) OR SemanticChecker.IsPointerType(type)
				OR (type IS SyntaxTree.ArrayType) OR (type IS SyntaxTree.MathArrayType);
		END
	END ReturnedAsParameter;

	PROCEDURE StructuredReturnType(procedureType: SyntaxTree.ProcedureType): BOOLEAN;
	BEGIN
		RETURN (procedureType # NIL) & (procedureType.callingConvention=SyntaxTree.OberonCallingConvention) & ReturnedAsParameter(procedureType.returnType);
	END StructuredReturnType;

	PROCEDURE IsNested(procedure: SyntaxTree.Procedure): BOOLEAN;
	BEGIN
		RETURN procedure.scope IS SyntaxTree.ProcedureScope
	END IsNested;

	PROCEDURE ProcedureParametersSize(system: Global.System; procedure: SyntaxTree.Procedure): LONGINT;
	BEGIN
		IF (procedure.scope IS SyntaxTree.CellScope) & (procedure = procedure.scope(SyntaxTree.CellScope).constructor) THEN
			RETURN 0
		ELSE
			RETURN ParametersSize(system,procedure.type(SyntaxTree.ProcedureType),IsNested(procedure));
		END;
	END ProcedureParametersSize;

	PROCEDURE ToMemoryUnits(system: Global.System; size: LONGINT): LONGINT;
	VAR dataUnit: LONGINT;
	BEGIN dataUnit := system.dataUnit;

		ASSERT(size MOD system.dataUnit = 0);
		RETURN size DIV system.dataUnit
	END ToMemoryUnits;

	PROCEDURE Get*(): Backend.Backend;
	VAR backend: IntermediateBackend;
	BEGIN NEW(backend); RETURN backend
	END Get;

	PROCEDURE Nop():IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.nop,emptyOperand,emptyOperand,emptyOperand);
		RETURN instruction
	END Nop;

	PROCEDURE Mov(dest,src: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.mov,dest,src,emptyOperand);
		RETURN instruction
	END Mov;

	(* like Mov but ensures that no new register will be allocated for dest *)
	PROCEDURE MovReplace(dest,src: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.mov,dest,src,dest);
		RETURN instruction
	END MovReplace;

	PROCEDURE Conv(dest,src: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.conv,dest,src,emptyOperand);
		RETURN instruction
	END Conv;

	PROCEDURE Call(op: IntermediateCode.Operand; parSize: LONGINT):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.call,op,IntermediateCode.Number(parSize),emptyOperand);
		RETURN instruction
	END Call;

	PROCEDURE Enter(callconv: LONGINT; varSize: LONGINT):IntermediateCode.Instruction;
	VAR op1,op2: IntermediateCode.Operand;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitNumber(op1,callconv);
		IntermediateCode.InitNumber(op2,varSize);
		IntermediateCode.InitInstruction(instruction,IntermediateCode.enter,op1,op2,emptyOperand);
		RETURN instruction
	END Enter;

	PROCEDURE Leave(callconv: LONGINT):IntermediateCode.Instruction;
	VAR op1: IntermediateCode.Operand;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitNumber(op1,callconv);
		IntermediateCode.InitInstruction(instruction,IntermediateCode.leave,op1,emptyOperand,emptyOperand);
		RETURN instruction
	END Leave;

	PROCEDURE Exit(parSize: LONGINT): IntermediateCode.Instruction;
	VAR op1: IntermediateCode.Operand;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitNumber(op1,parSize);
		IntermediateCode.InitInstruction(instruction,IntermediateCode.exit,op1,emptyOperand,emptyOperand);
		RETURN instruction
	END Exit;

	PROCEDURE Return(res: IntermediateCode.Operand): IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.return,res,emptyOperand,emptyOperand);
		RETURN instruction
	END Return;

	PROCEDURE Result(res: IntermediateCode.Operand): IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.result,res,emptyOperand,emptyOperand);
		RETURN instruction
	END Result;

	PROCEDURE Trap(nr: LONGINT): IntermediateCode.Instruction;
 	VAR op1: IntermediateCode.Operand;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitNumber(op1,nr);
		IntermediateCode.InitInstruction(instruction,IntermediateCode.trap,op1,emptyOperand,emptyOperand);
		RETURN instruction
	END Trap;

	PROCEDURE Br(dest: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.br,dest,emptyOperand,emptyOperand);
		RETURN instruction
	END Br;

	PROCEDURE Breq(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.breq,dest,left,right);
		RETURN instruction
	END Breq;

	PROCEDURE Brne(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.brne,dest,left,right);
		RETURN instruction
	END Brne;

	PROCEDURE Brge(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.brge,dest,left,right);
		RETURN instruction
	END Brge;

	PROCEDURE Brlt(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.brlt,dest,left,right);
		RETURN instruction
	END Brlt;

	PROCEDURE Pop(op:IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.pop,op,emptyOperand,emptyOperand);
		RETURN instruction
	END Pop;

	PROCEDURE Push(op: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.push,op,emptyOperand,emptyOperand);
		RETURN instruction
	END Push;

	PROCEDURE Neg(dest,src: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.neg,dest,src,emptyOperand);
		RETURN instruction
	END Neg;

	PROCEDURE Not(dest,src: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.not,dest,src,emptyOperand);
		RETURN instruction
	END Not;

	PROCEDURE Abs(dest,src: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.abs,dest,src,emptyOperand);
		RETURN instruction
	END Abs;

	PROCEDURE Mul(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.mul,dest,left,right);
		RETURN instruction
	END Mul;

	PROCEDURE Div(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.div,dest,left,right);
		RETURN instruction
	END Div;

	PROCEDURE Mod(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.mod,dest,left,right);
		RETURN instruction
	END Mod;

	PROCEDURE Sub(dest: IntermediateCode.Operand; left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.sub,dest,left,right);
		RETURN instruction
	END Sub;

	PROCEDURE Add(dest: IntermediateCode.Operand; left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.add,dest,left,right);
		RETURN instruction
	END Add;

	PROCEDURE And(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.and,dest,left,right);
		RETURN instruction
	END And;

	PROCEDURE Or(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.or,dest,left,right);
		RETURN instruction
	END Or;

	PROCEDURE Xor(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.xor,dest,left,right);
		RETURN instruction
	END Xor;

	PROCEDURE Shl(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.shl,dest,left,right);
		RETURN instruction
	END Shl;

	PROCEDURE Shr(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.shr,dest,left,right);
		RETURN instruction
	END Shr;

	PROCEDURE Rol(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.rol,dest,left,right);
		RETURN instruction
	END Rol;

	PROCEDURE Ror(dest,left,right: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.ror,dest,left,right);
		RETURN instruction
	END Ror;

	PROCEDURE Copy(dest,src,size: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.copy,dest,src,size);
		RETURN instruction
	END Copy;

	PROCEDURE Fill(dest,src,size: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.fill,dest,src,size);
		RETURN instruction
	END Fill;

	PROCEDURE Asm(s: SyntaxTree.SourceCode; position: LONGINT):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction; string: IntermediateCode.Operand;
	BEGIN
		string := IntermediateCode.String(s);
		IntermediateCode.SetIntValue(string,position); (* for error reporting *)
		IntermediateCode.InitInstruction(instruction,IntermediateCode.asm,string,emptyOperand,emptyOperand);
		RETURN instruction
	END Asm;

	PROCEDURE Data*(op: IntermediateCode.Operand):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitInstruction(instruction,IntermediateCode.data,op,emptyOperand,emptyOperand);
		RETURN instruction
	END Data;

	PROCEDURE Reserve(units: LONGINT):IntermediateCode.Instruction;
	VAR op1: IntermediateCode.Operand;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		(*! generate a warning if size exceeds a certain limit *)
		(*
		ASSERT(bytes < 1000000); (* sanity check *)
		*)
		ASSERT(0 <= units); (* sanity check *)
		IntermediateCode.InitNumber(op1,units);
		IntermediateCode.InitInstruction(instruction,IntermediateCode.reserve,op1,emptyOperand,emptyOperand);
		RETURN instruction
	END Reserve;

	PROCEDURE LabelInstruction(position: LONGINT): IntermediateCode.Instruction;
	VAR op1: IntermediateCode.Operand;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitNumber(op1,position);
		IntermediateCode.InitInstruction(instruction,IntermediateCode.label,op1,emptyOperand,emptyOperand);
		RETURN instruction
	END LabelInstruction;

	PROCEDURE EnterImmediate*(data: IntermediateCode.Section; CONST vop: IntermediateCode.Operand): LONGINT;
	VAR pc: LONGINT;

		PROCEDURE ProvidesValue(CONST instr: IntermediateCode.Instruction; op: IntermediateCode.Operand): BOOLEAN;
		BEGIN
			IF instr.opcode # IntermediateCode.data THEN RETURN FALSE END;
			ASSERT(instr.op1.mode = IntermediateCode.ModeImmediate);
			IF instr.op1.type.sizeInBits # op.type.sizeInBits THEN RETURN FALSE END;
			IF instr.op1.type.form # op.type.form THEN RETURN FALSE END;
			IF instr.op1.type.form = IntermediateCode.Float THEN
				RETURN instr.op1.floatValue = op.floatValue
			ELSE
				RETURN instr.op1.intValue = op.intValue
			END;
		END ProvidesValue;

	BEGIN
		ASSERT(vop.mode = IntermediateCode.ModeImmediate);
		pc := 0;
		WHILE (pc<data.pc) & ~ProvidesValue(data.instructions[pc],vop) DO
			INC(pc);
		END;

		IF pc = data.pc THEN
			data.Emit(Data(vop));
		END;
		RETURN pc
	END EnterImmediate;

	PROCEDURE Init;
	VAR i: LONGINT; name: SyntaxTree.String;
	BEGIN
		int8 := IntermediateCode.NewType(IntermediateCode.SignedInteger,IntermediateCode.Bits8);
		int16 := IntermediateCode.NewType(IntermediateCode.SignedInteger,IntermediateCode.Bits16);
		int32 := IntermediateCode.NewType(IntermediateCode.SignedInteger,IntermediateCode.Bits32);
		int64 := IntermediateCode.NewType(IntermediateCode.SignedInteger,IntermediateCode.Bits64);
		uint8 := IntermediateCode.NewType(IntermediateCode.UnsignedInteger,IntermediateCode.Bits8);
		uint16 := IntermediateCode.NewType(IntermediateCode.UnsignedInteger,IntermediateCode.Bits16);
		uint32 := IntermediateCode.NewType(IntermediateCode.UnsignedInteger,IntermediateCode.Bits32);
		uint64 := IntermediateCode.NewType(IntermediateCode.UnsignedInteger,IntermediateCode.Bits64);
		float32 := IntermediateCode.NewType(IntermediateCode.Float,IntermediateCode.Bits32);
		float64 := IntermediateCode.NewType(IntermediateCode.Float,IntermediateCode.Bits64);
		IntermediateCode.InitOperand(emptyOperand);

		FOR i := 0 TO NumberSystemCalls-1 DO
			name := "@SystemCall";
			Basic.AppendNumber(name,i);
			systemCalls[i] := SyntaxTree.NewSymbol(SyntaxTree.NewIdentifier(name));
		END;
	END Init;


BEGIN
	Init;

END FoxIntermediateBackend.


Compiler.Compile FoxIntermediateBackend.Mod ~
