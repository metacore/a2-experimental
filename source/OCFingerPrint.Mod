MODULE OCFingerPrint; (** AUTHOR "fof"; PURPOSE "Fingerprinting"; *)

(*! decouple type and type0, two visitors even?
*)

(* literature for the fingerprinting: Dissertation Crelier *)

IMPORT SyntaxTree := OCSyntaxTree, SYSTEM, Global := OCGlobal,Scanner := OCScanner,
		D := Debugging,Basic := OCBasic;

(** Fingerprinting

	FP(TypeDeclaration)        = 0 <*> fpModeType -> Name -> Visibility <*> FP(Type).
	FP(ConstantDeclaration)    = 0 <*> fpModeConstant -> Name -> Visibility <*> FP(Type) -> Basic -> Value.
	FP(VariableDeclaration)    = 0 <*> fpModePar -> Name -> Visibility <*> FP(Type).
	FP(ProcedureDeclaration)   = 0 <*> fpModeInlineProcedure -> Name -> Visibility <*> FP(Type) -> Code.
	                            | 0 <*> fpModeExportedProcedure -> Name -> Visibility <*> FP(Type)
	Name(fp,name)              = fp <*> name[0] <*> ... <*> name[n].
	Visibility(fp,vis)         = fp <*> fpExtern | fp <*> fpExternR | fp <*> fpOther <*> vis.
	Value(fp)                  = fp <*> fpTrue | fp <*> fpFalse | fp <*> integer  | fp <*> intlow <*> inthigh | fp -> Name
	FP(Type)                   = FP(BasicType) | FP(RecordType) | FP(PointerType)

                           	 	| FP(ArrayType) | FP(MathArrayType) | FP(ProcedurType)

	FP(BasicType)              = fpTypeChar8 | fpTypeChar16 | fpTypeChar32
	                            | fpTypeShortint | fpTypeInteger | fpTypeLongint | fpTypeHugeint
	                            | fpTypeReal | fpTypeLongreal
	                            | fpTypeSet | fpTypePointer |fpTypeString
	                            | fpTypeByte | fpTypeAll | fpTypeSame | fpTypeRange | fpTypeBoolean.
	PublicFP(BasicType)        = FP(basicType).
	PrivateFP(BasicType)       = sizeof(basicType).

	FP(RecordType)             = fpTypeComposite <*> fptypeRecord
	                            [ -> Name(moduleName) -> Name(typeName)] [<*> FP(baseType)]
	PublicFP(RecordType)       = FP(recordType) [<*> PublicFP(baseType)] {<*> FP(method) <*> methodNumber }
	                            {<*> PublicFP(fieldType) <*> offset(field) <*> FP(field)} <*> flags.
	PrivateFP(RecordType)      = FP(recordType) [<*> PrivateFP(baseType)] {<*> FP(method) <*> methodNumber }
	                            {<*> PrivateFP(fieldType) <*> offset(field) <*> FP(field)}

	FP(Method)                 = 0 <*> fpModeMethod -> Name(methodName) -> Signature(method).

	FP(Field)                  = 0 <*> fpModeField -> Name(fieldName) -> Visibility [<*> fpUntraced] <*> FP(type).

	FP(PointerType)            = fpTypePointer <*> fpTypeBasic -> Name <*> FP(baseType).
	PublicFP(PointerType)      = 0.
	PrivateFP(PointerType)     = 0.

	FP(ArrayType)              = fpTypeComposite <*> (fpTypeOpenArray | fpTypeStaticArray)
	                            -> Name <*> FP(baseType) [<*> length].
	PublicFP(ArrayType)        = FP(arrayType).
	PrivateFP(ArrayType)       = FP(arrayType).

	FP(MathArrayType)          = fpTypeComposite <*> (fpTypeOpenArray | fpTypeStaticArray)
	                            -> Name <*> FP(baseType) [<*> length].
	PublicFP(MathArrayType)    = FP(arrayType).
	PrivateFP(MathArrayType)   = FP(arrayType).

	FP(ProcedureType)          = fpTypeProcedure <*> fpTypeBasic [<*> fpDelegate]-> Name.
	PublicFP(ProcedureType)    = FP(arrayType) -> Signature(procedureType)
	PrivateFP(ProcedureType)   = FP(arrayType)-> Signature(procedureType).

	Signature(f)               = f <*> FP(returnType)
	                            { <*> (fpModeVarParameter | fpModeConstParameter | fpModePar)
	                            <*> FP(parameterType) [-> Name(parameterName)]  }
**)


CONST
	(*Fingerprints/Obj Modes*)
	fpModeVar=1;
	fpModePar=1;
	fpModeVarPar=2;
	fpModeConstPar=fpModeVarPar; (*! for compatibility, must be changed *)
	fpModeConst=3;
	fpModeField=4;
	fpModeType=5;
	fpModeExportedProcedure=7;
	fpModeInlineProcedure=9;
	fpModeMethod=13;

	(*from symbol file, used for finger prints also (cf. PCOM) *)
	sfTypeBoolean= 1;
	sfTypeChar8= 2;
	sfTypeChar16= 3;
	sfTypeChar32= 4;
	sfTypeShortint= 5;
	sfTypeInteger= 6;
	sfTypeLongint= 7;
	sfTypeHugeint =   8;
	sfTypeReal =   9;
	sfTypeLongreal =  10;
	sfTypeSet =  11;
	sfTypeString =  12;
	sfTypeNoType =  13;
	sfTypeNilType =  14;
	sfTypeByte =  15;
	sfTypeSptr =  16;

	(*Fingerprints/Type Forms*)
	fpTypeByte = 1;
	fpTypeBoolean=2;
	fpTypeChar8=3;
	fpTypeShortint=4;
	fpTypeInteger=5;
	fpTypeLongint=6;
	fpTypeReal=7;
	fpTypeLongreal=8;
	fpTypeSet=9;
	fpTypeString=10;
	fpTypeNone = 12;
	fpTypePointer=13;
	fpTypeProcedure=14;
	fpTypeComposite=15;
	fpTypeHugeint=16;
	fpTypeChar16 = 17;
	fpTypeChar32 = 18;
	fpTypeAll = 19;
	fpTypeSame = 20;
	fpTypeRange = 21;
	fpTypeEnum = 22;

	fpTypeBasic=1;
	fpTypeStaticArray=2;
	fpTypeDynamicArray=4;
	fpTypeOpenArray=5;
	fpTypeRecord=6;

	fpIntern=0;
	fpExtern=1;
	fpExternR=2;
	fpOther =3;

	fpFalse=0;
	fpTrue=1;

	fpHasBody = 1;
	fpProtected =4;
	fpActive = 5;

	fpDelegate = 5;
	fpSystemType = 6;

	fpUntraced = 4;

	Trace=FALSE;

TYPE

	FingerPrint*=POINTER TO RECORD
		FP-: LONGINT; (* finger print *)
		privateFP-: LONGINT; (* private finger print *)
		publicFP-: LONGINT; (* public finger print *)
		doneFP-, doneAll-: BOOLEAN;
		x: ANY; (* ! for debugging, remove some later time ! *)
	END;

	Lookup = OBJECT(Basic.HashTable); (* hash table ANY -> FingerPrint *)
	VAR

		PROCEDURE GetFingerPrint(symbol: ANY):FingerPrint;
		VAR p: ANY;
		BEGIN
			p := Get(symbol);
			IF p # NIL THEN
				ASSERT(p(FingerPrint).x = symbol);
				RETURN p(FingerPrint);
			ELSE
				RETURN NIL
			END;
		END GetFingerPrint;

		PROCEDURE PutFingerPrint(symbol: ANY; f: FingerPrint);
		BEGIN
			f.x := symbol;
			Put(symbol,f);
		END PutFingerPrint;

	END Lookup;

	FingerPrinterLookup* = OBJECT(Basic.HashTable); (* hash table: module _> FingerPrinter *)
	VAR system: Global.System;

		PROCEDURE & InitFingerPrinterLookup*(system: Global.System);
		BEGIN SELF.system := system; Init(30);
		END InitFingerPrinterLookup;

		PROCEDURE GetFingerPrinter*(module: SyntaxTree.Module):FingerPrinter;
		VAR p: ANY;fingerprinter: FingerPrinter;
		BEGIN
			p := Get(module);
			IF p # NIL THEN
				ASSERT(p(FingerPrinter).module = module);
				RETURN p(FingerPrinter);
			ELSE
				NEW(fingerprinter,module,system);
				PutFingerPrinter(module,fingerprinter);
				RETURN fingerprinter;
			END;
		END GetFingerPrinter;

		PROCEDURE PutFingerPrinter(module: SyntaxTree.Module; fingerprinter: FingerPrinter);
		BEGIN
			Put(module,fingerprinter);
		END PutFingerPrinter;

	END FingerPrinterLookup;

	FingerPrinter*= OBJECT (SyntaxTree.Visitor)
	VAR fp: LONGINT;
		fingerPrint:FingerPrint;
		module-: SyntaxTree.Module; (* module to fingerprint to *)
		system-: Global.System;
		lookup: Lookup;
		deep: BOOLEAN; (* public / private field of FP needed ? *)
		traceLevel: LONGINT;

		PROCEDURE & InitFingerPrinter*(module: SyntaxTree.Module; system: Global.System);
		BEGIN NEW(lookup,100); fingerPrint:=NIL; fp:= 0; SELF.module := module; SELF.system := system; deep := FALSE;
		traceLevel := 0;
		END InitFingerPrinter;
		(** types *)

		PROCEDURE GetFingerPrint(x: ANY): FingerPrint;
		BEGIN
			fingerPrint := lookup.GetFingerPrint(x);
			IF fingerPrint = NIL THEN
				NEW(fingerPrint);
				lookup.PutFingerPrint(x,fingerPrint);
				fingerPrint.FP := 0; fingerPrint.privateFP := 0; fingerPrint.publicFP := 0; fingerPrint.doneFP := FALSE; fingerPrint.doneAll := FALSE;
			END;
			RETURN fingerPrint
		END GetFingerPrint;

		(*
		FP(BasicType)        = | fpTypeByte | fpTypeAll | fpTypeSame | fpTypeRange | fpTypeBoolean.
                             | fpTypeSet | fpTypePointer
		PublicFP(BasicType)  = FP(basicType).
		PrivateFP(BasicType) = sizeof(basicType).
		*)
		PROCEDURE VisitBasicType(x: SyntaxTree.BasicType);
		VAR fingerPrint: FingerPrint;
		BEGIN
			fingerPrint := GetFingerPrint(x);

			IF ~fingerPrint.doneFP THEN
				IF x =Global.Byte THEN fingerPrint.FP := fpTypeByte; fingerPrint.privateFP := sfTypeByte;
				ELSIF x = Global.All THEN fingerPrint.FP := fpTypeAll; fingerPrint.privateFP := fpTypeAll;
				ELSIF x = Global.Same THEN fingerPrint.FP := fpTypeSame; fingerPrint.privateFP := fpTypeSame;
				ELSIF x = Global.RangeType THEN fingerPrint.FP := fpTypeRange; fingerPrint.privateFP := fpTypeRange;
				ELSIF x = Global.Boolean THEN fingerPrint.FP := fpTypeBoolean; fingerPrint.privateFP := sfTypeBoolean;
				ELSIF x = Global.Set THEN fingerPrint.FP := fpTypeSet; fingerPrint.privateFP := sfTypeSet;
				ELSIF x = Global.Nil THEN fingerPrint.FP := fpTypePointer; fingerPrint.privateFP := sfTypeSptr;
				ELSIF x = Global.Any THEN fingerPrint.FP := fpTypePointer; fingerPrint.privateFP := sfTypeSptr;
				(*
				ELSIF x = Global.Address THEN fingerPrint.FP := fpTypeLongint; fingerPrint.privateFP := fpTypeLongint;
				ELSIF x = Global.Size THEN fingerPrint.FP := fpTypeLongint; fingerPrint.privateFP := fpTypeLongint;
				*)
				ELSIF x = Global.Object THEN fingerPrint.FP := fpTypePointer; fingerPrint.privateFP := sfTypeSptr;
				ELSE HALT(100)
				END;
				fingerPrint.publicFP := fingerPrint.FP;
				fingerPrint.doneFP := TRUE;
				fingerPrint.doneAll := TRUE; (* no distinction between deep and shallow fp necessary *)
			END;

			SELF.fingerPrint := fingerPrint;
		END VisitBasicType;

		(*
		FP(BasicType)        = fpTypeChar8 | fpTypeChar16 | fpTypeChar32
		PublicFP(BasicType)  = FP(basicType).
		PrivateFP(BasicType) = sizeof(basicType).
		*)
		PROCEDURE VisitCharacterType(x: SyntaxTree.CharacterType);
		VAR fingerPrint: FingerPrint;
		BEGIN
			fingerPrint := GetFingerPrint(x);

			IF ~fingerPrint.doneFP THEN
				IF x = Global.Char8 THEN fingerPrint.FP := fpTypeChar8; fingerPrint.privateFP := sfTypeChar8;
				ELSIF x = Global.Char16 THEN fingerPrint.FP := fpTypeChar16; fingerPrint.privateFP := sfTypeChar16;
				ELSIF x = Global.Char32 THEN fingerPrint.FP := fpTypeChar32; fingerPrint.privateFP := sfTypeChar32;
				END;
				fingerPrint.publicFP := fingerPrint.FP;
				fingerPrint.doneFP := TRUE;
				fingerPrint.doneAll := TRUE; (* no distinction between deep and shallow fp necessary *)
			END;

			SELF.fingerPrint := fingerPrint
		END VisitCharacterType;

		(*
		FP(BasicType)        = fpTypeShortint | fpTypeInteger | fpTypeLongint | fpTypeLongint
		PublicFP(BasicType)  = FP(basicType).
		PrivateFP(BasicType) = sizeof(basicType).
		*)
		PROCEDURE VisitIntegerType(x: SyntaxTree.IntegerType);
		VAR fingerPrint: FingerPrint;
		BEGIN
			fingerPrint := GetFingerPrint(x);

			IF ~fingerPrint.doneFP THEN
				IF x = Global.Shortint THEN fingerPrint.FP := fpTypeShortint; fingerPrint.privateFP := sfTypeShortint;
				ELSIF x = Global.Integer THEN fingerPrint.FP := fpTypeInteger; fingerPrint.privateFP := sfTypeInteger;
				ELSIF x = Global.Longint THEN fingerPrint.FP := fpTypeLongint; fingerPrint.privateFP := sfTypeLongint;
				ELSIF x = Global.Hugeint THEN fingerPrint.FP := fpTypeHugeint; fingerPrint.privateFP := sfTypeHugeint;
				END;
				fingerPrint.publicFP := fingerPrint.FP;
				fingerPrint.doneFP := TRUE;
				fingerPrint.doneAll := TRUE; (* no distinction between deep and shallow fp necessary *)
			END;

			SELF.fingerPrint := fingerPrint
		END VisitIntegerType;

		(*
		FP(BasicType)        = fpTypeReal | fpTypeLongreal
		PublicFP(BasicType)  = FP(basicType).
		PrivateFP(BasicType) = sizeof(basicType).
		*)
		PROCEDURE VisitFloatType(x: SyntaxTree.FloatType);
		VAR fingerPrint: FingerPrint;
		BEGIN
			fingerPrint := GetFingerPrint(x);

			IF ~fingerPrint.doneFP THEN
				IF x = Global.Real THEN fingerPrint.FP := fpTypeReal; fingerPrint.privateFP := sfTypeReal;
				ELSIF x = Global.Longreal THEN fingerPrint.FP := fpTypeLongreal; fingerPrint.privateFP := sfTypeLongreal;
				END;
				fingerPrint.publicFP := fingerPrint.FP;
				fingerPrint.doneFP := TRUE;
				fingerPrint.doneAll := TRUE; (* no distinction between deep and shallow fp necessary *)
			END;

			SELF.fingerPrint := fingerPrint
		END VisitFloatType;

		(**
			fp enumeration type
		**)
		PROCEDURE VisitEnumerationType(x: SyntaxTree.EnumerationType);
		VAR fingerPrint: FingerPrint;
		VAR position: LONGINT; baseScope: SyntaxTree.EnumerationScope; baseType,resolved: SyntaxTree.Type; enumerationBase: SyntaxTree.EnumerationType;
			enumerator: SyntaxTree.Constant; fp: LONGINT; 
		BEGIN
			fingerPrint := GetFingerPrint(x);

			IF ~fingerPrint.doneFP THEN
				fp := fpTypeEnum;
				IF x.enumerationBase # NIL THEN
					FPType(fp,x.enumerationBase);
				END;
				enumerator := x.enumerationScope.firstConstant;
				WHILE enumerator # NIL DO
					IF enumerator.access * SyntaxTree.Public # {} THEN
						FPName(fp,enumerator.name); 
					END;
					FPValue(fp,enumerator.value);
					enumerator := enumerator.nextConstant;
				END;
				fingerPrint.FP := fp;
				fingerPrint.publicFP := fingerPrint.FP;
				fingerPrint.privateFP := fingerPrint.FP;
				fingerPrint.doneFP := TRUE;
				fingerPrint.doneAll := TRUE; (* no distinction between deep and shallow fp necessary *)
			END;

			SELF.fingerPrint := fingerPrint
			
			(*! must be implemented 
				IF x.enumerationBase # NIL THEN
					baseType := ResolveType(x.enumerationBase);
					resolved := baseType.resolved;
					enumerationBase := resolved(SyntaxTree.EnumerationType);
					baseScope := enumerationBase.enumerationScope;
					x.SetBaseValue(enumerationBase.baseValue + baseScope.numberEnumerators);
				END;
				CheckEnumerationScope(x.enumerationScope);
				x.SetState(SyntaxTree.Resolved);
			END;
			resolvedType := ResolvedType(x);
			*) 
		END VisitEnumerationType;

		PROCEDURE VisitQualifiedType(x: SyntaxTree.QualifiedType);
		BEGIN
			x.resolved.Accept(SELF);
		END VisitQualifiedType;

		(*
		FP(BasicType)        = fpStringType
		PublicFP(BasicType)  = FP(basicType).
		PrivateFP(BasicType) = sizeof(basicType).
		*)
		PROCEDURE VisitStringType(x: SyntaxTree.StringType);
		VAR fingerPrint: FingerPrint;
		BEGIN
			fingerPrint := GetFingerPrint(x);

			IF ~fingerPrint.doneFP THEN
				fingerPrint.FP := fpTypeString;
				fingerPrint.publicFP := fingerPrint.FP;
				fingerPrint.privateFP := SHORT(system.SizeOf(x));
				fingerPrint.doneFP := TRUE;
				fingerPrint.doneAll := TRUE; (* no distinction between deep and shallow fp necessary *)
			END;

			SELF.fingerPrint := fingerPrint
		END VisitStringType;

		(*
		FP(ArrayType)              = fpTypeComposite <*> (fpTypeOpenArray | fpTypeStaticArray)
		                            -> Name <*> FP(baseType) [<*> length].
		PublicFP(ArrayType)        = FP(arrayType).
		PrivateFP(ArrayType)       = FP(arrayType).
		*)
		PROCEDURE VisitArrayType(x: SyntaxTree.ArrayType);
		VAR fingerPrint: FingerPrint; deep: BOOLEAN; fp: LONGINT;
		BEGIN
			IF Trace THEN TraceEnter("ArrayType") END;
			fingerPrint := GetFingerPrint(x);
			deep := SELF.deep;

			IF ~fingerPrint.doneFP THEN
				fingerPrint.doneFP := TRUE;
				SELF.deep := FALSE;
				fp := 0;
				FPNumber(fp,fpTypeComposite);
				IF x.form = SyntaxTree.Open THEN FPNumber(fp,fpTypeOpenArray)
				ELSIF x.form = SyntaxTree.Static THEN FPNumber(fp,fpTypeStaticArray)
				ELSE HALT(200)
				END;
				TypeName(fp,x);
				FPType(fp,x.arrayBase.resolved);
				IF x.form = SyntaxTree.Static THEN FPNumber(fp,x.staticLength) END;
				fingerPrint.FP := fp;
				SELF.deep := deep;
			END;

			IF deep & ~fingerPrint.doneAll THEN
				x.arrayBase.Accept(SELF);
				fingerPrint.privateFP := fingerPrint.FP;
				fingerPrint.publicFP := fingerPrint.FP;
				fingerPrint.doneAll := TRUE;
			END;

			IF Trace THEN TraceExit("ArrayType",fingerPrint) END;
			SELF.fingerPrint := fingerPrint;
		END VisitArrayType;

		(*

		FP(MathArrayType)          = fpTypeComposite <*> (fpTypeOpenArray | fpTypeStaticArray)
		                            -> Name <*> FP(baseType) [<*> length].
		PublicFP(MathArrayType)    = FP(arrayType).
		PrivateFP(MathArrayType)   = FP(arrayType).
		*)
		PROCEDURE VisitMathArrayType(x: SyntaxTree.MathArrayType);
		VAR fingerPrint: FingerPrint; deep: BOOLEAN; fp: LONGINT;
		BEGIN
			fingerPrint := GetFingerPrint(x);
			deep := SELF.deep;
			IF Trace THEN TraceEnter("MathArrayType") END;


			IF ~fingerPrint.doneFP THEN
				SELF.deep := FALSE;
				fp := 0;
				FPNumber(fp,fpTypeComposite);
				IF x.form = SyntaxTree.Open THEN FPNumber(fp,fpTypeOpenArray)
				ELSIF x.form = SyntaxTree.Static THEN FPNumber(fp,fpTypeStaticArray)
				ELSIF x.form = SyntaxTree.Tensor THEN (* do nothing *)
				ELSE HALT(200)
				END;
				TypeName(fp,x);
				FPType(fp,x.arrayBase.resolved);
				IF x.form = SyntaxTree.Static THEN FPNumber(fp,x.staticLength) END;
				fingerPrint.FP := fp;
				fingerPrint.doneFP := TRUE;
				SELF.deep := deep;
			END;

			IF deep & ~fingerPrint.doneAll THEN
				x.arrayBase.Accept(SELF);
				fingerPrint.privateFP := fingerPrint.FP;
				fingerPrint.publicFP := fingerPrint.FP;
				fingerPrint.doneAll := TRUE;
			END;

			IF Trace THEN TraceExit("MathArrayType",fingerPrint) END;

			SELF.fingerPrint := fingerPrint;
		END VisitMathArrayType;

		(*
			fp = fp [ -> Name(moduleName) -> Name(typeName) ]
		*)
		PROCEDURE TypeName(VAR fp: LONGINT; x:SyntaxTree.Type);
		VAR  typeDeclaration: SyntaxTree.TypeDeclaration;
		BEGIN
			(*
			IF x IS SyntaxTree.RecordType THEN
				typeDeclaration := x.typeDeclaration;
				IF (typeDeclaration = NIL) & (x(SyntaxTree.RecordType).pointerType # NIL) THEN
					typeDeclaration := x(SyntaxTree.RecordType).pointerType.typeDeclaration;
				END;
			ELSE
				typeDeclaration := NIL;
			END;
			*)
			IF (x.scope # NIL) (*
				& (x.scope.ownerModule # NIL)  & (x.scope.ownerModule # module)  
				*)
				THEN
				 (* only executed for imported types, reason:
				 	modification of a type name would result in modified fingerprint leading to modified fingerprints of using structures such as
				 	in the following example:
				 	TYPE A=ARRAY 32 OF CHAR;
				 	PROCEDURE P*(a:A);
				 	...
				 	END P;
				 	IF name of A was changed, P would get a new fingerprint.
				 	Better: fingerprint of P only depends in type of A but not on its declared name.
				 *)
				IF Trace THEN
					TraceIndent;
					D.Str("TypeName  ");
					D.Str0(x.scope.ownerModule.name.name);
				END;
				FPName(fp,x.scope.ownerModule.name);
				typeDeclaration := x.typeDeclaration;
				IF (typeDeclaration # NIL) & (typeDeclaration.declaredType.resolved # x) THEN 
					(* in record type: pointer to type declaration of a pointer *)
					typeDeclaration := NIL 
				END;
				IF (typeDeclaration # NIL) & (typeDeclaration.scope # NIL)THEN
					(*
					ASSERT(typeDeclaration.scope.ownerModule # module); (* must be imported type *)
					*)
					(* should the name of the type and in particular the module name always be fingerprinted to
					abolish the dependency of the importing module? *)
					FPName(fp,typeDeclaration.name);
					IF Trace THEN
						D.Str(".");
						D.Str0(typeDeclaration.name.name);
					END;
				ELSIF (typeDeclaration # NIL) & (typeDeclaration.scope = NIL) THEN
					D.Str("typedeclaration without scope: "); D.Str0(x.typeDeclaration.name.name); D.Int(x.typeDeclaration.position,5); D.Ln;
					D.Update;
				ELSE
					FPNumber(fp,0);
				END;
				IF Trace THEN
					D.Str(", fp = "); 
					D.Hex(fp,-8);
					D.Ln;
				END;

			END;

		END TypeName;

		(*
		FP(PointerType)            = fpTypePointer <*> fpTypeBasic -> Name <*> FP(baseType).
		PublicFP(PointerType)      = 0.
		PrivateFP(PointerType)     = 0.
		*)
		PROCEDURE VisitPointerType(x: SyntaxTree.PointerType);
		VAR fingerPrint: FingerPrint; fp: LONGINT; deep: BOOLEAN;
		BEGIN
			IF Trace THEN TraceEnter("PointerType");  END;
			fingerPrint := GetFingerPrint(x);
			deep := SELF.deep;

			IF ~fingerPrint.doneFP THEN
				IF Trace THEN TraceIndent; D.Str("PointerType shallow");D.Ln;  END;
				SELF.deep := FALSE;
				fp := 0;
				FPNumber(fp, fpTypePointer); FPNumber(fp, fpTypeBasic);
				TypeName(fp,x);
				FPType(fp,x.pointerBase);
				fingerPrint.FP := fp;
				fingerPrint.doneFP := TRUE;
				SELF.deep := deep;
			END;

			fingerPrint.doneAll := TRUE;
			(*
			deep fingerprinting leads to cycles -> must be done on record type directly, if a deep FP is needed
			IF deep & ~fingerPrint.doneAll THEN
				IF Trace THEN TraceIndent; D.Str("PointerType:deep");D.Ln;  END;
				x.pointerBase.Accept(SELF);
				fingerPrint.doneAll := TRUE;
			END;
			*)

			IF Trace THEN TraceExit("PointerType",fingerPrint) END;

			SELF.fingerPrint := fingerPrint;
		END VisitPointerType;

		(*
		FP(Method)  = 0 <*> fpModeMethod -> Name(methodName) -> Signature(method).
		*)
		PROCEDURE FPrintMethod(VAR private,public: LONGINT; procedure,body: SyntaxTree.Procedure);
		VAR fingerPrint: FingerPrint; fp: LONGINT; name: ARRAY 256 OF CHAR; 
		BEGIN
			IF Trace THEN TraceEnter("Method");
				procedure.name.GetString(name);
				TraceIndent; D.Str("name = "); D.Str(name); D.Ln;
			END;
			ASSERT(deep);
			
			 
			IF procedure.access * SyntaxTree.Public # {} THEN (* visible method or visible supermethod *)
				fingerPrint := GetFingerPrint(procedure);
				IF ~fingerPrint.doneFP THEN
					fp := 0;
					FPNumber(fp,fpModeMethod);
					Global.GetSymbolName(procedure,name);
					FPString(fp,name);
					FPSignature(fp,procedure.type(SyntaxTree.ProcedureType),procedure IS SyntaxTree.Operator );
					fingerPrint.FP := fp;
					fingerPrint.doneFP := TRUE;
				ELSE
					fp := fingerPrint.FP;
				END;
				FPNumber(fp,procedure.methodNumber);
				IF procedure # body THEN
					FPNumber(private,fp); FPNumber(public,fp);
				END;
			END;
			IF Trace THEN
			TraceIndent; D.Str("Method, fp = "); D.Hex(private,-8); D.Str(" "); D.Hex(public,-8); D.Ln;
			TraceExit("Method",fingerPrint) END;
		END FPrintMethod;

		(*
		FP(RecordType)             = fpTypeComposite <*> fptypeRecord
		                            [ -> Name(moduleName) -> Name(typeName)] [<*> FP(baseType)]
		PublicFP(RecordType)       = FP(recordType) [<*> PublicFP(baseType)] {<*> FP(method) <*> methodNumber }
		                            {<*> PublicFP(fieldType) <*> offset(field) <*> FP(field)} <*> flags.
		PrivateFP(RecordType)      = FP(recordType) [<*> PrivateFP(baseType)] {<*> FP(method) <*> methodNumber }
		                            {<*> PrivateFP(fieldType) <*> offset(field) <*> FP(field)}
		*)
		PROCEDURE VisitRecordType(x: SyntaxTree.RecordType);
		VAR scope: SyntaxTree.RecordScope; fp: LONGINT; variable: SyntaxTree.Variable;
			fingerPrint,variableFingerPrint,variableTypeFingerPrint,baseFingerPrint: FingerPrint;flags: SET;
			symbol: SyntaxTree.Symbol; procedure: SyntaxTree.Procedure;  baseType: SyntaxTree.Type;
			body: SyntaxTree.Body;
			deep: BOOLEAN;
		(* for dealing with cycles the private and public fingerprint are computed here
			while FP is computed completely during call of Type0 *)
		BEGIN
			fingerPrint := GetFingerPrint(x);
			deep := SELF.deep;

			IF Trace THEN TraceEnter("Record"); END;

			IF ~fingerPrint.doneFP THEN
				IF Trace THEN TraceIndent; D.Str("RecordType Enter Shallow "); D.Ln; END;
				SELF.deep := FALSE;
				fp := 0;
				FPNumber(fp, fpTypeComposite); FPNumber(fp, fpTypeRecord);
				(*! IF SystemType IN type.flags THEN FPNumber(fp, fpSystemType) END; *)
				TypeName(fp,x);
				IF Trace THEN TraceIndent; D.Str("RecordType Name ");D.Hex(fp,-8);  D.Ln; END;

				IF (x.baseType # NIL) THEN
					baseType := x.baseType.resolved;
					IF baseType IS SyntaxTree.PointerType THEN baseType := baseType(SyntaxTree.PointerType).pointerBase.resolved END;
					FPType(fp,baseType);
				END;
				fingerPrint.FP := fp;
				fingerPrint.doneFP := TRUE;
				SELF.deep := deep;
				IF Trace THEN TraceIndent; D.Str("RecordType Shallow Done "); TraceFP(fingerPrint); D.Ln;  END;
			END;

			IF deep & ~fingerPrint.doneAll THEN
				IF Trace THEN TraceIndent; D.Str("RecordType Enter Deep "); D.Ln; END;
				fingerPrint.privateFP := fingerPrint.FP;
				fingerPrint.publicFP := fingerPrint.FP;
				(*! finger printing for interfaces omitted *)
				IF Trace THEN TraceIndent; D.Str("RecordType before basetype"); TraceFP(fingerPrint); D.Ln; END;

				(* now compute base record finger prints *)
				IF  (x.baseType # NIL) THEN
					baseType := x.baseType.resolved;
					IF baseType IS SyntaxTree.PointerType THEN baseType := baseType(SyntaxTree.PointerType).pointerBase.resolved END;
					baseFingerPrint := TypeFP(baseType); (* deep finger print *)
					FPNumber(fingerPrint.privateFP,baseFingerPrint.privateFP);
					FPNumber(fingerPrint.publicFP,baseFingerPrint.publicFP);
				END;

				scope := x.recordScope;
				IF Trace THEN TraceIndent; D.Str("RecordType before methods"); TraceFP(fingerPrint); D.Ln; END;

				(* methods, sorted *)
				symbol := scope.firstSymbol;
				WHILE symbol # NIL DO
					IF symbol IS SyntaxTree.Procedure THEN
						procedure := symbol(SyntaxTree.Procedure);
						FPrintMethod(fingerPrint.privateFP, fingerPrint.publicFP, procedure, scope.bodyProcedure);
						IF Trace THEN TraceIndent; D.Str("RecordType Method "); TraceFP(fingerPrint); D.Ln; END;
					END;
					symbol := symbol.nextSymbol
				END;
				IF Trace THEN TraceIndent; D.Str("RecordType after methods"); TraceFP(fingerPrint); D.Ln; END;

				variable := scope.firstVariable;
				WHILE variable # NIL DO
					variableFingerPrint := GetFingerPrint(variable);
					IF variable.access * SyntaxTree.Public # {} THEN
						(* variable fp =  & fpModeField & Name & Visibility [& fpUntraced] & Type *)
						fp := 0;
						FPNumber(fp,fpModeField);
						FPName(fp,variable.name);

						FPVisibility(fp,variable.access);
						IF SyntaxTree.UntracedFlag IN variable.flags THEN FPNumber(fp,fpUntraced) END;
						variableTypeFingerPrint := TypeFP(variable.type); (* deep finger print *)
						FPNumber(fp,variableTypeFingerPrint.FP);
						variableFingerPrint.FP := fp;
						FPNumber(fingerPrint.privateFP,variableTypeFingerPrint.privateFP);
						FPNumber(fingerPrint.privateFP,SHORT(variable.offsetInBits DIV 8));
						FPNumber(fingerPrint.privateFP,fp);
						FPNumber(fingerPrint.publicFP,variableTypeFingerPrint.publicFP);
						FPNumber(fingerPrint.publicFP,SHORT(variable.offsetInBits DIV 8));
						FPNumber(fingerPrint.publicFP,fp);
						IF Trace THEN TraceIndent; D.Str("RecordType Field "); D.Str0(variable.name.name); D.Str(" "); TraceFP(fingerPrint); D.Ln; END;
					ELSE
						fp := 0;
						IF SyntaxTree.UntracedFlag IN variable.flags THEN FPNumber(fp,fpUntraced) END;
						FPNumber(fingerPrint.privateFP,fp);
						IF Trace THEN TraceIndent; D.Str("RecordType InvisibleField "); TraceFP(fingerPrint); D.Ln;  END;
					END;
					variable := variable.nextVariable;
				END;

				flags := {};
				IF x.recordScope.bodyProcedure # NIL THEN
					body := x.recordScope.bodyProcedure.procedureScope.body;
					INCL(flags,  fpHasBody);
					IF body # NIL THEN 
						IF SyntaxTree.ActiveFlag IN body.flags THEN INCL(flags,fpActive) END;
						IF SyntaxTree.ExclusiveFlag IN body.flags THEN INCL(flags,fpProtected) END;
					END;
					IF Trace THEN TraceIndent; D.Str("RecordType Body "); TraceFP(fingerPrint); D.Ln;  END;
				END;
				IF x.IsProtected() THEN INCL(flags,fpProtected) END;
				FPSet(fingerPrint.publicFP, flags);
				IF Trace THEN TraceIndent; D.Str("RecordType Exit Deep "); TraceFP(fingerPrint); D.Ln;  END;

(*
				ASSERT(fingerPrint.privateFP # 0,100);
				ASSERT(fingerPrint.publicFP # 0,101);
*)
				fingerPrint.doneAll := TRUE;
			END;

			SELF.fingerPrint := fingerPrint;

			IF Trace THEN TraceExit("Record",fingerPrint); END;

		END VisitRecordType;

		(*
		FP(ProcedureType)          = fpTypeProcedure <*> fpTypeBasic [<*> fpDelegate]-> Name.
		PublicFP(ProcedureType)    = FP(arrayType) -> Signature(procedureType)
		PrivateFP(ProcedureType)   = FP(arrayType)-> Signature(procedureType).
		*)
		PROCEDURE VisitProcedureType(x: SyntaxTree.ProcedureType);
		VAR fingerPrint: FingerPrint; deep: BOOLEAN; fp: LONGINT;
		BEGIN
			IF Trace THEN TraceEnter("ProcedureType") END;

			fingerPrint := GetFingerPrint(x);
			deep := SELF.deep;

			IF ~fingerPrint.doneFP THEN
				fingerPrint.doneFP := TRUE; (*! to avoid circles, this is not fully clean - for paco *)
				fp := 0;
				FPNumber(fp,fpTypeProcedure);
				FPNumber(fp,fpTypeBasic);
				IF SyntaxTree.DelegateFlag IN x.flags THEN FPNumber(fp,fpDelegate) END;
				TypeName(fp,x);

				fingerPrint.publicFP := fp; fingerPrint.privateFP := fp;
				fingerPrint.FP := fp;
				FPSignature(fp,x,FALSE);
				fingerPrint.publicFP := fp; fingerPrint.privateFP := fp;
				fingerPrint.FP := fp;
				fingerPrint.doneAll := TRUE;
			END;

			(*
			IF ~fingerPrint.doneAll  THEN
				SELF.deep := FALSE;
				FPSignature(fp,x,FALSE);
				SELF.deep := deep;
				fingerPrint.publicFP := fp; fingerPrint.privateFP := fp;
				fingerPrint.FP := fp;
				fingerPrint.doneAll := TRUE;
			END;
			*)

			IF Trace THEN TraceExit("ProcedureType",fingerPrint) END;
			SELF.fingerPrint := fingerPrint;
		END VisitProcedureType;

		(** values - used in constant symbols - effects in fingerprint modification of (object) global variable fp *)

		(* fp = fp & (fpTrue | fpFalse) *)
		PROCEDURE VisitBooleanValue(x: SyntaxTree.BooleanValue);
		BEGIN IF x.value THEN FPNumber(SELF.fp,fpTrue) ELSE FPNumber(SELF.fp,fpFalse) END
		END VisitBooleanValue;

		(* fp = fp & (HugeInt | Number) *)
		PROCEDURE VisitIntegerValue(x: SyntaxTree.IntegerValue);
		BEGIN IF x.type = Global.Hugeint THEN FPHugeInt(SELF.fp,x.hvalue) ELSE FPNumber(SELF.fp,x.value) END;
		END VisitIntegerValue;

		(* fp = fp & (HugeInt | Number) *)
		PROCEDURE VisitEnumerationValue(x: SyntaxTree.EnumerationValue);
		BEGIN FPNumber(SELF.fp,x.value)
		END VisitEnumerationValue;


		(* fp = fp & ORD(char) *)
		PROCEDURE VisitCharacterValue(x: SyntaxTree.CharacterValue);
		BEGIN FPNumber(SELF.fp,ORD(x.value)) END VisitCharacterValue;

		(* fp = fp & Set *)
		PROCEDURE VisitSetValue(x: SyntaxTree.SetValue);
		BEGIN FPSet(SELF.fp,x.value) END VisitSetValue;

		PROCEDURE VisitMathArrayValue(x: SyntaxTree.MathArrayValue);
		BEGIN HALT(200) (* not yet implemented *) END VisitMathArrayValue;

		(* fp = fp & (Real | LongReal) *)
		PROCEDURE VisitRealValue(x: SyntaxTree.RealValue);
		BEGIN
			IF x.type = Global.Real THEN FPReal(SELF.fp,SHORT(x.value))
			ELSE FPLongReal(SELF.fp,x.value)
			END;
		END VisitRealValue;

		(* fp = fp & String *)
		PROCEDURE VisitStringValue(x: SyntaxTree.StringValue);
		BEGIN FPString(SELF.fp,x.value) END VisitStringValue;

		(* fp = fp & FP(x) *)
		PROCEDURE FPValue(VAR fp: LONGINT; x: SyntaxTree.Expression);
		BEGIN SELF.fp := fp; x.resolved.Accept(SELF); fp := SELF.fp
		END FPValue;

		PROCEDURE FPType(VAR fp: LONGINT; t: SyntaxTree.Type);
		BEGIN
			(*
				IF Trace THEN
					D.Str("FPType: fp "); D.Hex(fp,-8); D.Str(" -> "); D.Ln;
				END;
			*)

			IF t = NIL THEN FPNumber(fp,fpTypeNone);
			ELSE t.Accept(SELF); FPNumber(fp,SELF.fingerPrint.FP);
				(*
				IF Trace THEN
					D.Str("FPType: fp "); D.Str("( "); D.Hex(SELF.fingerPrint.FP,-8); D.Str(")"); D.Ln;
				END;
				*)
			END;
				(*
				IF Trace THEN
					D.Str("FPType: fp _> "); D.Hex(fp,-8); D.Ln;
				END;
				*)
		END FPType;

		(* 	Signature(f)  = f <*> FP(returnType)
	                      { <*> (fpModeVarParameter | fpModeConstParameter | fpModePar)
	                      <*> FP(parameterType) [-> Name(parameterName)]  }
		 *)
		PROCEDURE FPSignature(VAR fp: LONGINT; t: SyntaxTree.ProcedureType; isOperator: BOOLEAN);
		VAR par,self: SyntaxTree.Parameter;

			(* fp = fp & (fpModeVarPar | fpModeConstPar | fpModePar) [ & Name ] *)
			PROCEDURE FPPar(VAR fp: LONGINT;  par: SyntaxTree.Parameter);
			VAR deep: BOOLEAN;
			BEGIN
				IF par.kind = SyntaxTree.VarParameter THEN  FPNumber(fp, fpModeVarPar)
				ELSIF par.kind = SyntaxTree.ConstParameter THEN 
					IF (par.type.resolved IS SyntaxTree.ArrayType) OR (par.type.resolved IS SyntaxTree.RecordType) THEN (*! compatiblity with paco *)
						FPNumber(fp,fpModeVarPar)
					ELSE
						FPNumber(fp,fpModePar)
					END;
				ELSE  FPNumber(fp, fpModePar)  END;

				deep := SELF.deep;
				SELF.deep := FALSE;
				FPType(fp,par.type);
				SELF.deep := deep;

				IF isOperator & ~(par.type.resolved IS SyntaxTree.BasicType) & (par.type.resolved.typeDeclaration # NIL) THEN
					FPName(fp,par.type.resolved.typeDeclaration.name);
					(* D.Str("fp "); D.Str0(par.type.resolved.typeDeclaration.name.name); D.Ln;*)
				ELSIF isOperator & (par.type.resolved IS SyntaxTree.BasicType) THEN
					FPName(fp,par.type.resolved(SyntaxTree.BasicType).name);
					(* D.Str("fpb "); D.Str0(par.type.resolved(SyntaxTree.BasicType).name.name);*)
				END;
			END FPPar;

		BEGIN
			IF Trace THEN
				TraceIndent; D.Str("FPSignature enter "); D.Hex(fp,-8); D.Ln;
			END;
			FPType(fp,t.returnType);
			IF Trace THEN
				TraceIndent; D.Str("FPSignature after return type "); D.Hex(fp,-8); D.Ln;
			END;

			IF IsOberonProcedure(t) THEN

				self := t.firstParameter;
				WHILE (self # NIL) & (~self.name.Equals(Global.SelfParameterName)) DO
					self := self.nextParameter;
				END;
				IF self # NIL THEN FPPar(fp,self) END; (* self parameter *)

				IF Trace THEN
					TraceIndent; D.Str("FPSignature after self "); D.Hex(fp,-8); D.Ln;
				END;
				par := t.firstParameter;
				WHILE (par#self) DO (*! done as in PACO *)
					FPPar(fp, par);
					IF Trace THEN
						TraceIndent; D.Str("FPSignature par "); D.Hex(fp,-8); D.Ln;
					END;
					par:=par.nextParameter;
				END;
				IF Trace THEN
					TraceIndent; D.Str("FPSignature exit "); D.Hex(fp,-8); D.Ln;
				END;
			ELSE
				par := t.lastParameter;
				WHILE (par#NIL) DO (*! done as in PACO *)
					FPPar(fp, par);
					IF Trace THEN
						TraceIndent; D.Str("FPSignature par "); D.Hex(fp,-8); D.Ln;
					END;
					par:=par.prevParameter;
				END;
			END;
		END FPSignature;

		(** symbols *)

		(*
			FP(TypeDeclaration)        = 0 <*> fpModeType -> Name -> Visibility <*> FP(Type).
		*)
		PROCEDURE VisitTypeDeclaration(x: SyntaxTree.TypeDeclaration);
		VAR access: SET; fp: LONGINT;
			fingerPrint: FingerPrint; deep: BOOLEAN;
		BEGIN
			fingerPrint := GetFingerPrint(x);

			IF ~fingerPrint.doneFP THEN
				deep := SELF.deep;
				SELF.deep := FALSE;
				fp := 0;
				FPNumber(fp, fpModeType);
				FPName(fp,x.name);
				(* for compatibility with old compiler: *)
				access := x.access; IF SyntaxTree.PublicRead IN access THEN INCL(access,SyntaxTree.PublicWrite) END;
				FPVisibility(fp, access);
				x.declaredType.Accept(SELF);
				FPNumber(fp, SELF.fingerPrint.FP);
				fingerPrint.FP := fp;
				fingerPrint.doneFP := TRUE;
				SELF.deep := deep;
			END;
			SELF.fingerPrint := fingerPrint
		END VisitTypeDeclaration;

		(*
			FP(ConstantDeclaration)    = 0 <*> fpModeConstant -> Name -> Visibility <*> FP(Type) -> Basic -> Value.
		*)
		PROCEDURE VisitConstant(x: SyntaxTree.Constant);
		VAR access: SET;
			fingerPrint: FingerPrint;
			fp: LONGINT;
			deep: BOOLEAN;
		BEGIN
			fingerPrint := GetFingerPrint(x);

			IF ~fingerPrint.doneFP THEN
				deep := SELF.deep;
				SELF.deep := FALSE;
				fp := 0;
				FPNumber(fp, fpModeConst);
				FPName(fp,x.name);
				(* for compatibility with old compiler: *)
				access := x.access; IF SyntaxTree.PublicRead IN access THEN INCL(access,SyntaxTree.PublicWrite) END;
				FPVisibility(fp, access);
				FPType(fp, x.type);
				FPNumber(fp, fpTypeBasic);
				FPValue(fp, x.value);
				fingerPrint.FP := fp;
				fingerPrint.doneFP := TRUE;
				SELF.deep := deep;
			END;
			SELF.fingerPrint := fingerPrint
		END VisitConstant;

		(*
			FP(VariableDeclaration)    = 0 <*> fpModePar -> Name -> Visibility <*> FP(Type).
		*)
		PROCEDURE VisitVariable(x: SyntaxTree.Variable);
		VAR fingerPrint: FingerPrint; deep: BOOLEAN;
		BEGIN
			fingerPrint := GetFingerPrint(x);

			IF ~fingerPrint.doneFP THEN
				deep := SELF.deep;
				SELF.deep := FALSE;
				fp := 0;
				FPNumber(fp,fpModeVar);
				FPName(fp,x.name);
				FPVisibility(fp,x.access);
				x.type.Accept(SELF);
				FPNumber(fp,SELF.fingerPrint.FP);
				fingerPrint.FP := fp;
				fingerPrint.doneFP := TRUE;
				SELF.deep := deep;
			END;
			SELF.fingerPrint := fingerPrint
		END VisitVariable;

		(*
		FP(ProcedureDeclaration)   = 0 <*> fpModeInlineProcedure -> Name -> Visibility <*> FP(Type) -> Code.
		                            | 0 <*> fpModeExportedProcedure -> Name -> Visibility <*> FP(Type)
		*)
		PROCEDURE VisitProcedure(x: SyntaxTree.Procedure);
		VAR fp: LONGINT; access: SET; fingerPrint: FingerPrint; deep: BOOLEAN; code: SyntaxTree.Code; i: LONGINT;
			size,value: LONGINT; name: ARRAY 256 OF CHAR;
		BEGIN
			(*! missing: inline procedures *)
			fingerPrint := GetFingerPrint(x);

			IF ~fingerPrint.doneFP THEN
				deep := SELF.deep;
				SELF.deep := FALSE;
				(* for compatibility with old compiler: *)
				access := x.access; IF SyntaxTree.PublicRead IN access THEN INCL(access,SyntaxTree.PublicWrite) END;	
				fp := 0;
				IF SyntaxTree.InlineFlag IN x.flags THEN
					FPNumber(fp, fpModeInlineProcedure);
					FPName(fp,x.name);
					FPVisibility(fp, access);
					FPSignature(fp,x.type(SyntaxTree.ProcedureType),x IS SyntaxTree.Operator);
					IF (x.procedureScope.body # NIL) & (x.procedureScope.body.code # NIL) THEN
						code := x.procedureScope.body.code;
						IF code.inlineCode = NIL THEN 
							size := 0 
						ELSE
							size := code.inlineCode.GetSize() DIV 8;
						END;
						FPNumber(fp,size); 
						FOR i := 0 TO size-1 DO 
							value := code.inlineCode.GetBits(i*8,8);
							FPNumber(fp,value); 
						END;
					END;
				ELSE
					FPNumber(fp, fpModeExportedProcedure);
					Global.GetSymbolName(x,name);
					FPString(fp,name);	
					FPVisibility(fp, access);
					FPSignature(fp,x.type(SyntaxTree.ProcedureType),x IS SyntaxTree.Operator);
				END;
				fingerPrint.FP := fp;
				fingerPrint.doneFP := TRUE;
				SELF.deep := deep;
			END;
			SELF.fingerPrint := fingerPrint
		END VisitProcedure;

		(* cf. Procedure *)
		PROCEDURE VisitOperator(x: SyntaxTree.Operator);
		BEGIN 
			VisitProcedure(x) (* same finger print as a procedure *)
		END VisitOperator;

		PROCEDURE TraceIndent;
		VAR i: LONGINT;
		BEGIN
			FOR i := 1 TO traceLevel DO D.Str(" "); END;
		END TraceIndent;

		PROCEDURE TraceEnter(name: ARRAY OF CHAR);
		VAR i: LONGINT;
		BEGIN
			INC(traceLevel); TraceIndent;
			D.Str("Enter ");
			D.Str(name);
			D.Ln;
		END TraceEnter;

		PROCEDURE TraceExit(name: ARRAY OF CHAR; fingerPrint: FingerPrint);
		VAR i: LONGINT;
		BEGIN
			TraceIndent; DEC(traceLevel);
			D.Str("Exit "); D.Str(name); D.Str(" "); TraceFP(fingerPrint); D.Ln;
		END TraceExit;

		PROCEDURE TraceFP(fingerPrint: FingerPrint);
		BEGIN
			IF fingerPrint # NIL THEN
			D.Hex(fingerPrint.FP,-8); D.Str(" "); D.Hex(fingerPrint.privateFP,-8);
			D.Str(" "); D.Hex(fingerPrint.publicFP,-8);
			END;
		END TraceFP;


		(* returns the finger print (object) of a type *)
		PROCEDURE TypeFP*(this: SyntaxTree.Type): FingerPrint;
		VAR deep: BOOLEAN;
		BEGIN
			IF Trace THEN TraceEnter("TypeFP");  END;

			deep := SELF.deep;
			SELF.deep := TRUE;
			this.Accept(SELF);
			SELF.deep := deep;
			ASSERT(fingerPrint.x = this.resolved,100);
			ASSERT(fingerPrint.doneAll,101);
			ASSERT(fingerPrint.FP #0,102);

			IF Trace THEN TraceExit("TypeFP",fingerPrint); D.Ln;
			D.Ln; END;

			RETURN fingerPrint
		END TypeFP;

		(* returns the finger print (object) of a symbol *)
		PROCEDURE SymbolFP*(this: SyntaxTree.Symbol): FingerPrint;
		VAR name: ARRAY 256 OF CHAR; deep: BOOLEAN;
		BEGIN
			deep := SELF.deep;
			SELF.deep := TRUE;
			IF Trace THEN TraceEnter("SymbolFP");
				TraceIndent;
				this.name.GetString(name);
				D.Str("name: ");
				D.Str(name); D.Ln;
			END;
			this.Accept(SELF);
			SELF.deep := deep;
			IF Trace THEN TraceExit("SymbolFP",fingerPrint); D.Ln; END;
			RETURN fingerPrint
		END SymbolFP;

		(*
		(* set the module within which should be fingerprinted *)
		PROCEDURE SetModule*(module: SyntaxTree.Module);
		BEGIN
			SELF.module := module;
		END SetModule;
		*)

	END FingerPrinter;


	(** ---------- Fingerprinting primitives -------------- *)
	PROCEDURE IsOberonProcedure(type: SyntaxTree.ProcedureType): BOOLEAN;
	BEGIN
		RETURN type.flags * {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag} = {}
	END IsOberonProcedure;
	
	(* fp = fp <*> val *)
	PROCEDURE FPNumber*(VAR fp: LONGINT; val: LONGINT);
	BEGIN
		fp:=SYSTEM.VAL(LONGINT, SYSTEM.VAL(SET, SYSTEM.ROT(fp, 7)) / SYSTEM.VAL(SET, val))
	END FPNumber;

	(* fp = fp <*> set *)
	PROCEDURE FPSet*(VAR fp: LONGINT; set: SET);
	BEGIN FPNumber(fp, SYSTEM.VAL(LONGINT, set))
	END FPSet;

	(* fp = fp <*> real *)
	PROCEDURE FPReal*(VAR fp: LONGINT; real: REAL);
	BEGIN FPNumber(fp, SYSTEM.VAL(LONGINT, real))
	END FPReal;

	(* fp = fp <*> low <*> high *)
	PROCEDURE FPLongReal*(VAR fp: LONGINT; lr: LONGREAL);
		VAR l, h: LONGINT;
	BEGIN
		SYSTEM.GET(SYSTEM.ADR(lr)+4, l); SYSTEM.GET(SYSTEM.ADR(lr), h);
		FPNumber(fp, l); FPNumber(fp, h);
	END FPLongReal;

	(* fp = fp <*> low <*> high *)
	PROCEDURE FPHugeInt*(VAR fp: LONGINT; huge: HUGEINT);
	VAR l, h: LONGINT;
	BEGIN
		SYSTEM.GET(SYSTEM.ADR(huge)+4, l); SYSTEM.GET(SYSTEM.ADR(huge), h);
		FPNumber(fp, l); FPNumber(fp, h);
	END FPHugeInt;

	(* fp = fp -> String *)
	PROCEDURE FPName*(VAR fp: LONGINT; x: SyntaxTree.Identifier);
	VAR name: Scanner.StringType;
	BEGIN
		x.GetString(name);
		FPString(fp,name);
	END FPName;

	(* fp = fp {<*> str[i]} *)
	PROCEDURE FPString*(VAR fp: LONGINT; CONST str: ARRAY OF CHAR);
	VAR i: INTEGER; ch: CHAR;
	BEGIN i:=0; REPEAT ch:=str[i]; FPNumber(fp, ORD(ch)); INC(i) UNTIL ch=0X
	END FPString;

	(* fp = fp <*> (fpExtern | fpExternR | fpIntern | fpOther + vis) *)
	PROCEDURE FPVisibility*(VAR fp: LONGINT; vis: SET);
	BEGIN
		IF SyntaxTree.PublicWrite IN vis THEN  FPNumber(fp, fpExtern)
		ELSIF SyntaxTree.PublicRead IN vis THEN  FPNumber(fp, fpExternR)
		ELSIF SyntaxTree.Internal * vis #{} THEN  FPNumber(fp, fpIntern)
		ELSE
			FPNumber(fp, fpOther + SYSTEM.VAL(LONGINT, vis))
		END
	END FPVisibility;

END OCFingerPrint.
