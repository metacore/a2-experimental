MODULE OCGlobal; (** AUTHOR "fof & fn"; PURPOSE "Oberon Compiler Globally Defined Symbols"; *)
(* (c) fof ETH Zürich, 2008 *)

IMPORT
	SyntaxTree := OCSyntaxTree, Basic := OCBasic, Scanner := OCScanner, Strings, Runtime;

CONST
	(* system flag names *)
	StringWinAPI* = "WINAPI";
	StringC* = "C";
	StringUntraced* = "UNTRACED";
	StringDelegate* = "DELEGATE";
	StringInterrupt*= "INTERRUPT";
	StringNoPAF*="NOPAF";
	StringFixed*="FIXED";

	(* block modifier flag names *)
	StringExclusive* = "EXCLUSIVE";
	StringActive* = "ACTIVE";
	StringPriority* = "PRIORITY";
	StringSafe* = "SAFE";
	StringRealtime*= "REALTIME";



	(* traps *)
	WithTrap* = 1;
	CaseTrap* = 2;
	ReturnTrap* = 3;
	TypeEqualTrap* = 5;
	TypeCheckTrap* = 6;
	IndexCheckTrap* = 7;
	AssertTrap* = 8;
	ArraySizeTrap* = 9;
	ArrayFormTrap*=10; (* fof: indicates that array cannot be (re-)allocated since shape, type or size does not match *)

	(** builtin procedures **)
	(* OCProgTools.Enum -e -s=94
		(* global proper procedures *)
		Assert  Copy  Dec  Excl  Halt  Inc  Incl  New GetProcedure
		(* global functions *)
		Abs  Ash  Cap  Chr  Entier  EntierH  Len  Long  Max  Min Odd  Ord  Short  Size
		Sum Dim Lsl Lsr Asr
		(* system proper procedures *)
		systemGet  systemPut  systemMove  systemNew
		systemIncr systemReshape
		systemZeroCopy systemTypeCode systemHalt
		systemPut8 systemPut16 systemPut32 systemPut64 systemTrace
		(* system functions *)
		systemAdr  systemBit  systemGet64  systemGet32  systemGet16  systemGet8
		systemLsh  systemRot  systemVal systemNull

		Conversion
		end
		~
	*)
	(* global proper procedures *)
	Assert*= Scanner.EndOfText+1; Copy*= Assert+1; Dec*= Copy+1; Excl*= Dec+1; Halt*= Excl+1;
	Inc*= Halt+1; Incl*= Inc+1; New*= Incl+1; GetProcedure*= New+1;
	(* global functions *)
	Abs*= GetProcedure+1; Ash*= Abs+1; Cap*= Ash+1; Chr*= Cap+1; Entier*= Chr+1;
	EntierH*= Entier+1; Len*= EntierH+1; Long*= Len+1; Max*= Long+1; Min*= Max+1;
	Odd*= Min+1; Ord*= Odd+1; Short*= Ord+1; systemSizeOf*= Short+1; Sum*= systemSizeOf+1;
	Dim*= Sum+1;

	(* system proper procedures *)
	systemGet*= Dim+1; systemPut*= systemGet+1; systemMove*= systemPut+1;
	systemNew*= systemMove+1;
	systemIncr*= systemNew+1; systemReshape*= systemIncr+1; systemZeroCopy*= systemReshape+1; systemTypeCode*= systemZeroCopy+1; systemHalt*= systemTypeCode+1;
	systemPut8*= systemHalt+1; systemPut16*= systemPut8+1; systemPut32*= systemPut16+1; systemPut64*= systemPut32+1;
	systemTrace*= systemPut64+1;

	(* system functions *)
	systemAdr*= systemTrace+1;
	systemBit*= systemAdr+1; systemGet64*= systemBit+1; systemGet32*= systemGet64+1; systemGet16*= systemGet32+1;
	systemGet8*= systemGet16+1; systemLsh*= systemGet8+1; systemRot*= systemLsh+1; systemVal*= systemRot+1; Conversion*= systemVal+1;

	(* from ERA *)
	systemNull*=systemVal+1; systemXOR*=systemNull+1; systemROR*=systemXOR+1; systemProc*=systemROR+1; systemStop* = systemProc + 1; LSL*=systemStop+1; LSR*=LSL+1; ASR*=LSR+1; Flt*=ASR+1; Floor*=Flt+1; Phi*=Floor+1;

	end= Floor+1;


VAR
	(* names *)
	SelfParameterName-,ReturnParameterName-,SystemName-,systemName-,PointerReturnName-, ResultName-,
	A2Name-,OberonName-,ArrayBaseName-,RecordBodyName-,ModuleBodyName-: SyntaxTree.Identifier;


	(* global types, note that no explicit statement is made about the size of the types *)
	Char-, Char8-, Char16-, Char32-: SyntaxTree.CharacterType; (* currently, the Oberon language defines CHAR = CHAR8 *)
	Hugeint-, Longint-, Integer-, Shortint-: SyntaxTree.IntegerType; (* (signed) integer types *)
	Real-, Longreal-: SyntaxTree.FloatType; (* floating point types *)
	Boolean-, Set-: SyntaxTree.BasicType; (* boolean and set type *)
	Nil-,Any-, Object-: SyntaxTree.BasicType; (* special types for NIL, ANY and OBJECT *)
	All-, Same-, RangeType-: SyntaxTree.Type; (* special types for Math Oberon *)

	Byte-, Address-,Size-: SyntaxTree.BasicType; (* special system types *)

	(* helpful mappings for conversions etc *)
	NumericType-: ARRAY 6 OF SyntaxTree.Type;
	CharacterType-: ARRAY 3 OF SyntaxTree.Type;

	identifiers: ARRAY 2 OF ARRAY end OF SyntaxTree.Identifier;

TYPE
	Alignment* = RECORD
		min, max: LONGINT; (* alignments in bits *)
	END;

	System*= OBJECT
	VAR
		(* system and global scopes and modules  (lowercase and uppercase each) *)
		systemScope-, globalScope-: ARRAY 2 OF SyntaxTree.ModuleScope;
		systemModule-,globalModule-: ARRAY 2 OF SyntaxTree.Module;

		(* addressing granularity in data memory *)
		dataUnit-: LONGINT;
		(* alignment (variables, record entries) *)
		(* alignment (parameters & stack frames) *)
		variableAlignment-, parameterAlignment-: Alignment;
		(* offset of first parameter *)
		offsetFirstParameter-: LONGINT;
		(* to determine if a builtin-procedure can be operator-overloaded *)
		operatorDefined-: ARRAY end OF BOOLEAN;

		(* type sizes defined by backend *)
		addressSize-: LONGINT;

		(* system type mapping, in a later version only the global (unisgned) types should be used
			the following two types are only there for compatibility with the system as is
			problematic are mainly the conversions between (signed) Oberon types and (unsigned) addressType.
			A good concept has to be derived.
		*)
		addressType-, sizeType-: SyntaxTree.BasicType;

		PROCEDURE &InitSystem*(dataUnit: LONGINT; addressSize, minVarAlign, maxVarAlign, minParAlign, maxParAlign, offsetFirstPar: LONGINT);
		VAR i: LONGINT;
		BEGIN
			addressType := Address; sizeType := Size;
			ASSERT(dataUnit > 0);
			ASSERT(minVarAlign > 0);
			ASSERT(maxVarAlign > 0);
			ASSERT(minParAlign > 0);
			ASSERT(maxParAlign > 0);
			SELF.dataUnit := dataUnit;
			SELF.addressSize := addressSize;
			SELF.variableAlignment.min := minVarAlign;
			SELF.variableAlignment.max := maxVarAlign;
			SELF.parameterAlignment.min := minParAlign;
			SELF.parameterAlignment.max := maxParAlign;
			SELF.offsetFirstParameter := offsetFirstPar;
			BuildScopes(SELF);
			FOR i := 0 TO LEN(operatorDefined)-1 DO
				operatorDefined[i] := FALSE;
			END;
		END InitSystem;

		PROCEDURE GenerateRecordOffsets*(x: SyntaxTree.RecordType): BOOLEAN; (* normally done in checker but the binary symbol file format makes this necessary *)
		VAR baseType: SyntaxTree.RecordType; offset,size: LONGINT; alignment: LONGINT; variable: SyntaxTree.Variable;
		BEGIN
			baseType :=x.GetBaseRecord();
			IF (baseType  # NIL) & (baseType.sizeInBits < 0) THEN
				RETURN GenerateRecordOffsets(baseType);
			END;
			IF baseType # NIL THEN
				offset := baseType.sizeInBits
			ELSE
				offset := 0
			END;
			variable := x.recordScope.firstVariable;
			WHILE (variable # NIL) DO
				size := SizeOf(variable.type.resolved);
				IF size < 0 THEN RETURN FALSE END;
				alignment := AlignmentOf(SELF.variableAlignment, variable.type.resolved);
				Basic.Align(offset,alignment);
				variable.SetOffset(offset);
				INC(offset,size);
				variable := variable.nextVariable;
			END;
			Basic.Align(offset,addressSize);
			x.SetSize(offset);
			RETURN TRUE
		END GenerateRecordOffsets;

		PROCEDURE GenerateVariableOffsets*(scope: SyntaxTree.Scope): BOOLEAN;
		VAR variable: SyntaxTree.Variable; offset,size: LONGINT; alignment: LONGINT;
		BEGIN
			IF scope IS SyntaxTree.RecordScope THEN (* increasing indices *)
				RETURN GenerateRecordOffsets(scope(SyntaxTree.RecordScope).ownerRecord)
			ELSE (* module scope or procedure scope: decreasing indices *)
				ASSERT((scope IS SyntaxTree.ModuleScope) OR (scope IS SyntaxTree.ProcedureScope));
				offset := 0;
				variable := scope.firstVariable;
				WHILE (variable # NIL) DO
					size := SizeOf(variable.type.resolved);
					IF size < 0 THEN RETURN FALSE END;
					DEC(offset,size);
					alignment := AlignmentOf(SELF.variableAlignment,variable.type.resolved);
					Basic.Align(offset,-alignment);
					variable.SetOffset(offset);
					variable := variable.nextVariable;
				END;
			END;
			RETURN TRUE
		END GenerateVariableOffsets;

		PROCEDURE GenerateParameterOffsets*(procedureType : SyntaxTree.ProcedureType; nestedProcedure: BOOLEAN): BOOLEAN;
		VAR offset,size: LONGINT;parameter: SyntaxTree.Parameter;
		BEGIN
			offset := SELF.offsetFirstParameter;
			IF nestedProcedure THEN
				INC(offset,addressSize); (* parameter offset of static link *) (*! check alternative: add hidden parameter *)
			END;
			IF procedureType.flags * {SyntaxTree.CFlag,SyntaxTree.WinAPIFlag} = {}  THEN
				parameter := procedureType.lastParameter;
				WHILE (parameter # NIL) DO
					Basic.Align(offset,addressSize);
					parameter.SetOffset(offset);
					size := SizeOfParameter(parameter);
					IF size < 0 THEN RETURN FALSE END;
					INC(offset,SizeOfParameter(parameter));
					parameter := parameter.prevParameter;
				END;
				IF procedureType.returnParameter # NIL THEN
					Basic.Align(offset,addressSize);
					procedureType.returnParameter.SetOffset(offset);
				END;
			ELSE
				parameter := procedureType.firstParameter;
				WHILE (parameter # NIL) DO
					Basic.Align(offset,addressSize);
					parameter.SetOffset(offset);
					size := SizeOfParameter(parameter);
					IF size < 0 THEN RETURN FALSE END;
					INC(offset,size);
					parameter := parameter.nextParameter;
				END;
			END;
			RETURN TRUE
		END GenerateParameterOffsets;

		PROCEDURE SizeOf*(type: SyntaxTree.Type): LONGINT;
		VAR size: LONGINT;
		BEGIN
			type := type.resolved;
			IF type IS SyntaxTree.CharacterType THEN
				IF type = Char8 THEN size := 8
				ELSIF type = Char16 THEN size := 16
				ELSIF type = Char32 THEN size := 32
				ELSE HALT(100)
				END;
			ELSIF type IS SyntaxTree.NumberType THEN
				IF type = Shortint THEN size := 8
				ELSIF type = Integer THEN size := 16
				ELSIF type = Longint THEN size := 32
				ELSIF type = Hugeint THEN size := 64
				ELSIF type = Real THEN size := 32
				ELSIF type = Longreal THEN size := 64
				ELSE HALT(100)
				END;
			ELSIF type IS SyntaxTree.BasicType THEN
				IF type = Byte THEN size := 8
				ELSIF type = All THEN size := addressSize
				ELSIF type = Same THEN size := addressSize
				ELSIF type = Boolean THEN size := 8
				ELSIF type = Set THEN size := addressSize
				ELSIF type = Any THEN size := addressSize
				ELSIF type = RangeType THEN size :=3*addressSize
				ELSIF type = Nil THEN size := addressSize
				ELSIF type = Object THEN size := addressSize
				ELSIF type = Address THEN size := addressSize
				ELSIF type = Size THEN size := addressSize
				ELSE HALT(100);
				END
			ELSIF type IS SyntaxTree.PointerType THEN
				size := addressSize
			ELSIF type IS SyntaxTree.ProcedureType THEN
				IF SyntaxTree.DelegateFlag IN  type(SyntaxTree.ProcedureType).flags THEN
					size := 2*addressSize
				ELSE
					size := addressSize
				END;
			ELSIF type IS SyntaxTree.RecordType THEN
				(* do not treat a record type like a pointer even if the Pointer field is set, this leads to problems in object files
					rather make sure that each reference type is a POINTER TO at least behind the secenes!
				*)
				ASSERT(SyntaxTree.Resolved IN type.state);
				size :=type(SyntaxTree.RecordType).sizeInBits;
				IF size < 0 THEN
					IF GenerateRecordOffsets(type(SyntaxTree.RecordType)) THEN
						size :=type(SyntaxTree.RecordType).sizeInBits;
					ELSE
						size := -1
					END;
				END;
			ELSIF type IS SyntaxTree.ArrayType THEN
				ASSERT(SyntaxTree.Resolved IN type.state);
				IF type(SyntaxTree.ArrayType).form = SyntaxTree.Static THEN
					size := SizeOf(type(SyntaxTree.ArrayType).arrayBase.resolved)*type(SyntaxTree.ArrayType).staticLength
				ELSE
					size := 0;
					WHILE(type IS SyntaxTree.ArrayType) DO
						type := type(SyntaxTree.ArrayType).arrayBase.resolved;
						INC(size); (* length field *)
					END;
					size := size*addressSize+addressSize
				END;
			ELSIF type IS SyntaxTree.MathArrayType THEN
				ASSERT(SyntaxTree.Resolved IN type.state);
				IF type(SyntaxTree.MathArrayType).form = SyntaxTree.Static THEN
					size := SizeOf(type(SyntaxTree.MathArrayType).arrayBase.resolved)*type(SyntaxTree.MathArrayType).staticLength
				ELSIF type(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
					size := addressSize (* pointer to geometry descriptor *)
				ELSE
					size := 0;
					WHILE(type IS SyntaxTree.MathArrayType) DO
						type := type(SyntaxTree.MathArrayType).arrayBase.resolved;
						INC(size);
					END;
					size := size*2*addressSize (* length and increments *) +5*addressSize (* data ptr, adr ptr, flags, dim and elementsize *);
				END;
			ELSIF type IS SyntaxTree.StringType THEN
				ASSERT(SyntaxTree.Resolved IN type.state);
				size := type(SyntaxTree.StringType).length * SizeOf(Char);
			ELSIF type IS SyntaxTree.EnumerationType THEN
				size := addressSize
			ELSIF type = SyntaxTree.invalidType THEN size := 0
			ELSIF type IS SyntaxTree.QualifiedType THEN
				HALT(101); (* hint that unresolved type has been taken for type size computation *)
			ELSE
				HALT(100)
			END;
			RETURN size
		END SizeOf;

		PROCEDURE SizeOfParameter*(par: SyntaxTree.Parameter):LONGINT;
		BEGIN
			IF (par.type.resolved IS SyntaxTree.ArrayType) OR (par.type.resolved IS SyntaxTree.MathArrayType) THEN
				IF (par.type.resolved IS SyntaxTree.ArrayType) & (par.type.resolved(SyntaxTree.ArrayType).form = SyntaxTree.Static) &
					(par.kind IN {SyntaxTree.ConstParameter,SyntaxTree.VarParameter})
					OR (par.type.resolved IS SyntaxTree.MathArrayType) & (par.kind = SyntaxTree.VarParameter)
				THEN
					RETURN addressSize
				ELSIF IsOberonProcedure(par.procedureType) THEN
					RETURN SizeOf(par.type);
				ELSE RETURN addressSize
				END
			ELSIF (par.kind IN {SyntaxTree.ConstParameter,SyntaxTree.VarParameter}) THEN
				IF (par.type.resolved IS SyntaxTree.RecordType) THEN
					IF IsOberonProcedure(par.procedureType) THEN
						RETURN 2*addressSize
					ELSE
						RETURN addressSize
					END
				ELSE
					RETURN addressSize
				END;
			ELSE
				RETURN SizeOf(par.type);
			END;
		END SizeOfParameter;

		PROCEDURE AlignmentOf*(CONST alignment: Alignment;type: SyntaxTree.Type): LONGINT;
		VAR result: LONGINT;
		BEGIN
			type := type.resolved;
			IF type IS SyntaxTree.RecordType THEN
				result := alignment.max
			ELSIF type IS SyntaxTree.ArrayType THEN
				IF type(SyntaxTree.ArrayType).form = SyntaxTree.Static THEN
					result := AlignmentOf(alignment,type(SyntaxTree.ArrayType).arrayBase.resolved);
				ELSE
					result := alignment.max
				END;
			ELSIF type IS SyntaxTree.StringType THEN
				result := SizeOf(Char);
			ELSE
				result := SizeOf(type);
				IF result > alignment.max THEN result := alignment.max END;
				IF result < alignment.min THEN result := alignment.min END;
			END;
			ASSERT(result # 0);
			RETURN result
		END AlignmentOf;

	END System;

	PROCEDURE BuildScopes(system: System);
	VAR i: LONGINT;
	BEGIN
		FOR i := 0 TO end-1 DO
			system.operatorDefined[i] := FALSE
		END;
		system.globalScope[Scanner.Uppercase] := SyntaxTree.NewModuleScope();
		system.globalScope[Scanner.Lowercase] := SyntaxTree.NewModuleScope();
		system.globalModule[Scanner.Uppercase] := SyntaxTree.NewModule("",-1,SyntaxTree.NewIdentifier(-1,"@GLOBAL"),system.globalScope[Scanner.Uppercase],Scanner.Uppercase);
		system.globalModule[Scanner.Lowercase] := SyntaxTree.NewModule("",-1,SyntaxTree.NewIdentifier(-1,"@global"),system.globalScope[Scanner.Lowercase],Scanner.Lowercase);
		system.systemScope[Scanner.Uppercase] := SyntaxTree.NewModuleScope();
		system.systemScope[Scanner.Lowercase] := SyntaxTree.NewModuleScope();
		system.systemModule[Scanner.Uppercase] := SyntaxTree.NewModule("",-1,SystemName,system.systemScope[Scanner.Uppercase],Scanner.Uppercase);
		system.systemModule[Scanner.Lowercase] := SyntaxTree.NewModule("",-1,systemName,system.systemScope[Scanner.Lowercase],Scanner.Lowercase);
	END BuildScopes;

	PROCEDURE MapSystemTypes*(system: System; address, size: SyntaxTree.BasicType);
	BEGIN
		system.addressType := address;
		system.sizeType := size;
	END MapSystemTypes;

	PROCEDURE SetDefaultDeclarations*(system: System);
	BEGIN
		(* type declarations *)
		DeclareType(Byte,"BYTE",system.systemScope);
		MapSystemTypes(system,Longint,Longint);
		DeclareType(system.addressType,"ADDRESS",system.systemScope); (* mapped to longint *)
		DeclareType(system.sizeType,"SIZE",system.systemScope); (* mapped to longint *)
		DeclareType(All,"ALL",system.systemScope);
		DeclareType(Same,"SAME",system.systemScope);

		(* system builtin procedures *)
		NewBuiltin(systemGet,"GET",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemPut,"PUT",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemMove,"MOVE",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemNew,"NEW",system.systemScope,{});
		NewBuiltin(systemReshape,"RESHAPE",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemZeroCopy,"ZEROCOPY",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemHalt,"HALT",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemPut64,"PUT64",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemPut32,"PUT32",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemPut16,"PUT16",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemPut8,"PUT8",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemAdr,"ADR",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemBit,"BIT",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemGet64,"GET64",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemGet32,"GET32",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemGet16,"GET16",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemGet8,"GET8",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemLsh,"LSH",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemRot,"ROT",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemVal,"VAL",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemIncr,"INCR",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemTypeCode,"TYPECODE",system.systemScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemSizeOf,"SIZEOF",system.systemScope,{SyntaxTree.RealtimeFlag});

		(* Set up system types *)
		DeclareType(Char,"CHAR",system.globalScope);
		DeclareType(Char8,"CHAR8",system.globalScope);
		DeclareType(Char16,"CHAR16",system.globalScope);
		DeclareType(Char32,"CHAR32",system.globalScope);
		DeclareType(Shortint,"SHORTINT",system.globalScope);
		DeclareType(Integer,"INTEGER",system.globalScope);
		DeclareType(Longint,"LONGINT",system.globalScope);
		DeclareType(Hugeint,"HUGEINT",system.globalScope);
		DeclareType(Real,"REAL",system.globalScope);
		DeclareType(Longreal,"LONGREAL",system.globalScope);
		DeclareType(Boolean,"BOOLEAN",system.globalScope);
		DeclareType(Set,"SET",system.globalScope);
		DeclareType(Any,"ANY",system.globalScope);
		DeclareType(Object,"OBJECT",system.globalScope);

		(* global functions *)
		NewBuiltin(Abs,"ABS",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Ash,"ASH",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Cap,"CAP",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Chr,"CHR",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Entier,"ENTIER",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(EntierH,"ENTIERH",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Len,"LEN",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Long,"LONG",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Max,"MAX",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Min,"MIN",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Odd,"ODD",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Ord,"ORD",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Short,"SHORT",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Sum,"SUM",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Dim,"DIM",system.globalScope,{SyntaxTree.RealtimeFlag});

		(* global proper procedures *)
		NewBuiltin(Assert,"ASSERT",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Copy,"COPY",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Dec,"DEC",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Excl,"EXCL",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Halt,"HALT",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Inc,"INC",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(Incl,"INCL",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(New,"NEW",system.globalScope,{});
		NewBuiltin(GetProcedure,"GETPROCEDURE",system.globalScope,{SyntaxTree.RealtimeFlag});
		NewBuiltin(systemTrace,"TRACE",system.globalScope,{SyntaxTree.RealtimeFlag});
	END SetDefaultDeclarations;

	PROCEDURE OperatorDefined*(system: System; op: LONGINT; defined: BOOLEAN);
	BEGIN
		system.operatorDefined[op] := defined;
	END OperatorDefined;

	PROCEDURE SetDefaultOperators*(system: System);
	VAR i: LONGINT;
	BEGIN
		FOR i := Scanner.Equal TO Scanner.Not DO
			OperatorDefined(system,i,TRUE);
		END;
		OperatorDefined(system,Dec,TRUE);
		OperatorDefined(system,Excl,TRUE);
		OperatorDefined(system,Inc,TRUE);
		OperatorDefined(system,Incl,TRUE);
		OperatorDefined(system,Abs,TRUE);
		OperatorDefined(system,Ash,TRUE);
		OperatorDefined(system,Cap,TRUE);
		OperatorDefined(system,Chr,TRUE);
		OperatorDefined(system,Entier,TRUE);
		OperatorDefined(system,EntierH,TRUE);
		OperatorDefined(system,Len,TRUE);
		OperatorDefined(system,Long,TRUE);
		OperatorDefined(system,Max,TRUE);
		OperatorDefined(system,Min,TRUE);
		OperatorDefined(system,Odd,TRUE);
		OperatorDefined(system,Short,TRUE);
		OperatorDefined(system,Sum,TRUE);
		OperatorDefined(system,Dim,TRUE);
	END SetDefaultOperators;

	PROCEDURE DefaultSystem*(): System;
	VAR system: System;
	BEGIN
		NEW(system,8,32, 8,32,32,32,64);
		SetDefaultDeclarations(system);
		SetDefaultOperators(system);
		RETURN system
	END DefaultSystem;

	PROCEDURE IsOberonProcedure(type: SyntaxTree.ProcedureType): BOOLEAN;
	BEGIN
		RETURN type.flags * {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag} = {}
	END IsOberonProcedure;

	PROCEDURE AlignedSizeOf*(system: System; CONST alignment: Alignment; type: SyntaxTree.Type):LONGINT;
	VAR value: LONGINT;
	BEGIN
		value := SHORT(system.SizeOf(type));
		INC(value, (-value) MOD system.AlignmentOf(alignment, type));
		RETURN value;
	END AlignedSizeOf;


	(* returns if a module is the system module *)
	PROCEDURE IsSystemModule*(module: SyntaxTree.Module): BOOLEAN;
	BEGIN RETURN module.name.Equals(systemName) OR module.name.Equals(SystemName)
	END IsSystemModule;

	(** Various factories *)
	PROCEDURE DeclareType0(type: SyntaxTree.Type; CONST name: Scanner.StringType; in: SyntaxTree.Scope);
	VAR basic: SyntaxTree.TypeDeclaration; duplicate: BOOLEAN;
	BEGIN
		basic := SyntaxTree.NewTypeDeclaration(-1,SyntaxTree.NewIdentifier(-1,name));
		basic.SetDeclaredType(type);
		basic.SetState(SyntaxTree.Resolved);
		basic.SetAccess(SyntaxTree.ReadOnly);
		in.AddTypeDeclaration(basic);
		in.EnterSymbol(basic,duplicate);
		ASSERT(~duplicate);
	END DeclareType0;

	(** External interface backends can use to add their types etc. to the global scope *)
	PROCEDURE DeclareType*(type: SyntaxTree.Type; CONST name: Scanner.StringType; CONST scope: ARRAY OF SyntaxTree.ModuleScope);
	VAR nameL,nameU: Scanner.StringType;
	BEGIN
		Basic.Lowercase(name,nameL);
		Basic.Uppercase(name,nameU);
		DeclareType0(type,nameU,scope[Scanner.Uppercase]);
		DeclareType0(type,nameL,scope[Scanner.Lowercase]);
	END DeclareType;

	PROCEDURE NewBasicType(CONST name: Scanner.StringType; flags: SET): SyntaxTree.BasicType;
	VAR basicType: SyntaxTree.BasicType;
	BEGIN
		basicType := SyntaxTree.NewBasicType(-1,SyntaxTree.NewIdentifier(-1,name),flags);
		basicType.SetState(SyntaxTree.Resolved);
		RETURN basicType;
	END NewBasicType;

	PROCEDURE NewCharacterType(CONST name: Scanner.StringType): SyntaxTree.CharacterType;
	VAR basicType: SyntaxTree.CharacterType;
	BEGIN
		basicType := SyntaxTree.NewCharacterType(-1,SyntaxTree.NewIdentifier(-1,name));
		basicType.SetState(SyntaxTree.Resolved);
		RETURN basicType;
	END NewCharacterType;

	PROCEDURE NewIntegerType(CONST name: Scanner.StringType): SyntaxTree.IntegerType;
	VAR basicType: SyntaxTree.IntegerType;
	BEGIN
		basicType := SyntaxTree.NewIntegerType(-1,SyntaxTree.NewIdentifier(-1,name));
		basicType.SetState(SyntaxTree.Resolved);
		RETURN basicType;
	END NewIntegerType;

	PROCEDURE NewFloatType(CONST name: Scanner.StringType): SyntaxTree.FloatType;
	VAR basicType: SyntaxTree.FloatType;
	BEGIN
		basicType := SyntaxTree.NewFloatType(-1,SyntaxTree.NewIdentifier(-1,name));
		basicType.SetState(SyntaxTree.Resolved);
		RETURN basicType;
	END NewFloatType;

	PROCEDURE NewConstant0(CONST name: Scanner.StringType; int: LONGINT; type: SyntaxTree.Type; in: SyntaxTree.Scope);
	VAR constant: SyntaxTree.Constant; value: SyntaxTree.IntegerValue;duplicate: BOOLEAN;
	BEGIN
		value := SyntaxTree.NewIntegerValue(-1,int);
		value.SetType(type);
		constant := SyntaxTree.NewConstant(-1,SyntaxTree.NewIdentifier(-1,name));
		constant.SetValue(value);
		constant.SetType(value.type);
		constant.SetAccess(SyntaxTree.ReadOnly);
		constant.SetState(SyntaxTree.Resolved);
		in.AddConstant(constant);
		in.EnterSymbol(constant,duplicate);
		ASSERT(~duplicate);
	END NewConstant0;

	PROCEDURE NewConstant*(CONST name: Scanner.StringType; int: LONGINT; type: SyntaxTree.Type; CONST scope: ARRAY OF SyntaxTree.ModuleScope);
	VAR nameL,nameU: Scanner.StringType;
	BEGIN
		Basic.Lowercase(name,nameL);
		Basic.Uppercase(name,nameU);
		NewConstant0(nameU,int,type,scope[Scanner.Uppercase]);
		NewConstant0(nameL,int,type,scope[Scanner.Lowercase]);
	END NewConstant;

	PROCEDURE NewBuiltin0( id: LONGINT; CONST name: Scanner.StringType; in:  SyntaxTree.ModuleScope; flags: SET);
	VAR basic: SyntaxTree.Builtin; duplicate: BOOLEAN; type: SyntaxTree.ProcedureType;
	BEGIN
		basic := SyntaxTree.NewBuiltin(-1,SyntaxTree.NewIdentifier(-1,name),id);
		basic.SetAccess(SyntaxTree.ReadOnly);
		type := SyntaxTree.NewProcedureType(-1,in);
		type.AddFlags(flags);
		type.SetReturnType(SyntaxTree.invalidType); (* make incompatible to any procedure *)
		basic.SetType(type);
		basic.SetState(SyntaxTree.Resolved);
		in.EnterSymbol(basic,duplicate);
		in.AddBuiltin(basic);
		ASSERT(~duplicate);
	END NewBuiltin0;

	PROCEDURE NewBuiltin*(id: LONGINT; CONST name: Scanner.StringType; CONST scope: ARRAY OF SyntaxTree.ModuleScope; flags: SET);
	VAR nameL,nameU: Scanner.StringType;
	BEGIN
		Basic.Lowercase(name,nameL);
		Basic.Uppercase(name,nameU);
		NewBuiltin0(id,nameU,scope[Scanner.Uppercase],flags);
		NewBuiltin0(id,nameL,scope[Scanner.Lowercase],flags);
	END NewBuiltin;

	PROCEDURE ModuleFileName*(moduleName,context: SyntaxTree.Identifier; VAR fileName: ARRAY OF CHAR);
	VAR prefix,name: Scanner.StringType;
	BEGIN
		moduleName.GetString(name);
		IF (context = NIL) OR context.Equals(A2Name) THEN
			COPY(name,fileName);
		ELSE
			ASSERT(context.Equals(OberonName));
			context.GetString(prefix);
			Basic.Concat(fileName,prefix,".",name);
		END;
	END ModuleFileName;

	PROCEDURE ContextFromName*(CONST fileName: ARRAY OF CHAR; VAR module,context: SyntaxTree.Identifier);
	VAR moduleName, contextName: Scanner.StringType; i,j: LONGINT;
	BEGIN
		i := 0; j := 0;
		WHILE (fileName[i] # 0X) & (fileName[i] # ".") DO
			contextName[i] := fileName[i];
			INC(i);
		END;
		contextName[i] := 0X;
		IF fileName[i] # 0X THEN
			INC(i);
			WHILE(fileName[i] # 0X) DO
				moduleName[j] := fileName[i];
				INC(i); INC(j);
			END;
		END;
		moduleName[j] := 0X;
		IF j = 0 THEN
			moduleName := contextName;
			contextName := "A2";
		END;
		module := SyntaxTree.NewIdentifier(-1,moduleName);
		context := SyntaxTree.NewIdentifier(-1,contextName);
	END ContextFromName;

	PROCEDURE GetSymbolName*(symbol: SyntaxTree.Symbol; VAR name: ARRAY OF CHAR);
	VAR n: SyntaxTree.String; td: SyntaxTree.TypeDeclaration;
		PROCEDURE Scope(scope: SyntaxTree.Scope);
		BEGIN
			IF scope = NIL THEN (* do nothing, locally declared temporary symbol *)
			ELSIF scope IS SyntaxTree.ModuleScope THEN
				scope.ownerModule.name.GetString(n);
				Strings.Append(name,n);Strings.Append(name,".");
			ELSIF scope IS SyntaxTree.RecordScope THEN
				Scope(scope.outerScope);
				td := scope(SyntaxTree.RecordScope).ownerRecord.typeDeclaration;
				IF td = NIL THEN
					td := scope(SyntaxTree.RecordScope).ownerRecord.pointerType.typeDeclaration;
				END;
				td.name.GetString(n);
				Strings.Append(name,n); Strings.Append(name,".")
			ELSIF scope IS SyntaxTree.ProcedureScope THEN
				Scope(scope.outerScope);
				scope(SyntaxTree.ProcedureScope).ownerProcedure.name.GetString(n);
				Strings.Append(name,n); Strings.Append(name,".")
			END;
		END Scope;

	BEGIN
		name := "";
		Scope(symbol.scope);
		symbol.name.GetString(n);
		IF symbol IS SyntaxTree.Operator THEN (*! append some more bits to make discrimintation possible *)
		END;
		Strings.Append(name,n);
	END GetSymbolName;

	PROCEDURE Level*(t: SyntaxTree.Type): LONGINT;
	VAR level: LONGINT;
	BEGIN
		level := LEN(NumericType)-1;
		WHILE (level >= 0) & (NumericType[level] # t) DO DEC(level) END;
		RETURN level
	END Level;

	PROCEDURE ConvertSigned*(this: HUGEINT; bits: LONGINT): HUGEINT;
	VAR h: HUGEINT;
	BEGIN
		bits := 64-bits;
		h :=Runtime.AslH(this,bits);
		h := Runtime.AsrH(h,bits);
		RETURN h
	END ConvertSigned;

	PROCEDURE ConvertUnsigned*(this: HUGEINT; bits: LONGINT): HUGEINT;
	VAR h: HUGEINT;
	BEGIN
		bits := 64-bits;
		h := Runtime.LslH(this,bits);
		h := Runtime.LsrH(h,bits);
		RETURN h;
	END ConvertUnsigned;



	PROCEDURE MaxInteger*(system: System; type: SyntaxTree.Type): HUGEINT;
	VAR h: HUGEINT;
	BEGIN
		h := Runtime.AslH(1,system.SizeOf(type)-1);
		RETURN h-1
	END MaxInteger;

	PROCEDURE MinInteger*(system: System; type: SyntaxTree.Type): HUGEINT;
	VAR h: HUGEINT;
	BEGIN
		h := Runtime.AslH(1,system.SizeOf(type)-1);
		RETURN -h
	END MinInteger;

	PROCEDURE GetIntegerType*(system: System; this: HUGEINT): SyntaxTree.Type;

		PROCEDURE InBounds(type: SyntaxTree.Type): BOOLEAN;
		VAR m: HUGEINT;
		BEGIN
			m := Runtime.AslH(1,system.SizeOf(type)-1);
			RETURN (this < m) & (-this <= m)
		END InBounds;

	BEGIN
		IF InBounds(Shortint) THEN RETURN Shortint
		ELSIF InBounds(Integer) THEN RETURN Integer
		ELSIF InBounds(Longint) THEN RETURN Longint
		ELSE RETURN Hugeint
		END;
	END GetIntegerType;

	PROCEDURE NewIntegerValue*(system: System; position: LONGINT; hugeint: HUGEINT): SyntaxTree.Value;
	VAR value: SyntaxTree.IntegerValue;
	BEGIN
		value := SyntaxTree.NewIntegerValue(position,hugeint);
		value.SetType(GetIntegerType(system,hugeint));
		RETURN value
	END NewIntegerValue;

	PROCEDURE NewBooleanValue*(position: LONGINT; b: BOOLEAN): SyntaxTree.Value;
	VAR value: SyntaxTree.BooleanValue;
	BEGIN
		value := SyntaxTree.NewBooleanValue(position,b);
		value.SetType(Boolean);
		RETURN value
	END NewBooleanValue;

	PROCEDURE NewSetValue*(position: LONGINT; s: SET): SyntaxTree.Value;
	VAR value: SyntaxTree.SetValue;
	BEGIN
		value := SyntaxTree.NewSetValue(position,s);
		value.SetType(Set);
		RETURN value
	END NewSetValue;

	PROCEDURE NewCharacterValue*(position: LONGINT; c: CHAR): SyntaxTree.Value;
	VAR value: SyntaxTree.CharacterValue;
	BEGIN
		value := SyntaxTree.NewCharacterValue(position,c);
		value.SetType(Char);
		RETURN value
	END NewCharacterValue;

	PROCEDURE NewNilValue*(position: LONGINT): SyntaxTree.Value;
	VAR value: SyntaxTree.NilValue;
	BEGIN
		value := SyntaxTree.NewNilValue(position);
		value.SetType(Nil);
		RETURN value
	END NewNilValue;

	PROCEDURE BasicTypeDistance*(system: System; from, to: SyntaxTree.BasicType): LONGINT;
	VAR i, j: LONGINT;
	BEGIN
		IF from IS SyntaxTree.CharacterType THEN
			i := 0; j := LEN(CharacterType);
			WHILE (i < LEN(CharacterType)) & (CharacterType[i] # from) DO  INC(i)  END;
			REPEAT  DEC(j)  UNTIL (j < i) OR (CharacterType[j] = to);
		ELSE
			i := 0; j := LEN(NumericType);
			WHILE (i < LEN(NumericType)) & (NumericType[i] # from) DO  INC(i)  END;
			REPEAT  DEC(j)  UNTIL (j < i) OR (NumericType[j] = to);
		END;

		j := j-i;

		(* special rule for dialects that support things like SIZEOF(INTEGER) = SIZEOF(LONGINT) *)
		IF (j<0) & (from IS SyntaxTree.IntegerType) & (to IS SyntaxTree.IntegerType) THEN
			IF system.SizeOf(from) = system.SizeOf(to) THEN
				j := 0
			END;
		END;


		IF j<0 THEN j := MAX(LONGINT) END;
		RETURN j
	END BasicTypeDistance;

	PROCEDURE GetIdentifier*(symbol: LONGINT; case: LONGINT): SyntaxTree.Identifier;
	BEGIN
		IF (symbol >= 0) & (symbol < LEN(identifiers,1)) THEN
			RETURN identifiers[case,symbol]
		ELSE
			RETURN NIL
		END;
	END GetIdentifier;

	PROCEDURE InitIdentifiers;
	VAR i: LONGINT;

		PROCEDURE NewKeywordIdentifier(op: LONGINT);
		VAR str: Scanner.StringType;
		BEGIN
			Scanner.GetKeyword(Scanner.Uppercase,op,str);
			identifiers[Scanner.Uppercase,op] := SyntaxTree.NewIdentifier(-1,str);
			Scanner.GetKeyword(Scanner.Lowercase,op,str);
			identifiers[Scanner.Lowercase,op] := SyntaxTree.NewIdentifier(-1,str);
		END NewKeywordIdentifier;

		PROCEDURE NewBuiltinIdentifier(op: LONGINT; CONST name: Scanner.StringType);
		VAR nameL,nameU: Scanner.StringType;
		BEGIN
			ASSERT(op < LEN(identifiers[0]));
			Basic.Lowercase(name,nameL);
			Basic.Uppercase(name,nameU);
			identifiers[Scanner.Lowercase,op] := SyntaxTree.NewIdentifier(-1,nameL);
			identifiers[Scanner.Uppercase,op] := SyntaxTree.NewIdentifier(-1,nameU);
		END NewBuiltinIdentifier;

	BEGIN
		FOR i := 0 TO LEN(identifiers,1)-1 DO
			identifiers[Scanner.Uppercase,i] := NIL; identifiers[Scanner.Lowercase,i] := NIL;
		END;
		FOR i := 0 TO Scanner.EndOfText-1 DO
			NewKeywordIdentifier(i);
		END;
		NewBuiltinIdentifier(Abs,"ABS");
		NewBuiltinIdentifier(Ash,"ASH");
		NewBuiltinIdentifier(Cap,"CAP");
		NewBuiltinIdentifier(Chr,"CHR");
		NewBuiltinIdentifier(Entier,"ENTIER");
		NewBuiltinIdentifier(EntierH,"ENTIERH");
		NewBuiltinIdentifier(Len,"LEN");
		NewBuiltinIdentifier(Long,"LONG");
		NewBuiltinIdentifier(Max,"MAX");
		NewBuiltinIdentifier(Min,"MIN");
		NewBuiltinIdentifier(Odd,"ODD");
		NewBuiltinIdentifier(Ord,"ORD");
		NewBuiltinIdentifier(Short,"SHORT");
		NewBuiltinIdentifier(Sum,"SUM");
		NewBuiltinIdentifier(Dim,"DIM");
		NewBuiltinIdentifier(Dec,"DEC");
		NewBuiltinIdentifier(Excl,"EXCL");
		NewBuiltinIdentifier(Inc,"INC");
		NewBuiltinIdentifier(Incl,"INCL");

		identifiers[Scanner.Lowercase,Conversion] := SyntaxTree.NewIdentifier(-1,"@Convert");
		identifiers[Scanner.Uppercase,Conversion] := SyntaxTree.NewIdentifier(-1,"@Convert");
	END InitIdentifiers;

	(** initialize the global namespace *)
	PROCEDURE Init;
	BEGIN
		InitIdentifiers;
		(* names are not arbitrary, do not change unless you know what you do (compatibilty with paco!) *)
		SystemName := SyntaxTree.NewIdentifier(-1,"SYSTEM");
		systemName := SyntaxTree.NewIdentifier(-1,"system");
		SelfParameterName := SyntaxTree.NewIdentifier(-1,"@Self");
		ReturnParameterName := SyntaxTree.NewIdentifier(-1,"@ReturnParameter");
		PointerReturnName := SyntaxTree.NewIdentifier(-1,"@PtrReturnType");
		ResultName := SyntaxTree.NewIdentifier(-1,"RESULT");
		A2Name := SyntaxTree.NewIdentifier(-1,"A2");
		OberonName := SyntaxTree.NewIdentifier(-1,"Oberon");
		ArrayBaseName := SyntaxTree.NewIdentifier(-1,"OCArrayBase");
		RecordBodyName := SyntaxTree.NewIdentifier(-1,"@Body");
		ModuleBodyName := SyntaxTree.NewIdentifier(-1,"$$Body");


		(* types *)
		Char8 := NewCharacterType("Char8");
		Char := Char8;
		Char16 := NewCharacterType("Char16");
		Char32 := NewCharacterType("Char32");
		CharacterType[0] := Char8;
		CharacterType[1] := Char16;
		CharacterType[2] := Char32;

		Shortint := NewIntegerType("Shortint");
		Integer := NewIntegerType("Integer");
		Longint := NewIntegerType("Longint");
		Hugeint := NewIntegerType("Hugeint");
		Real := NewFloatType("Real");
		Longreal := NewFloatType("Longreal");
		NumericType[0] := Shortint;
		NumericType[1] := Integer;
		NumericType[2] := Longint;
		NumericType[3] := Hugeint;
		NumericType[4] := Real;
		NumericType[5] := Longreal;

		Boolean := NewBasicType("Boolean",{SyntaxTree.RealtimeFlag});
		Set := NewBasicType("Set",{SyntaxTree.RealtimeFlag});

		Any := NewBasicType("Any",{});
		RangeType := NewBasicType("RangeType",{SyntaxTree.RealtimeFlag});		

		Object := NewBasicType("ObjectType",{});
		Nil := NewBasicType("NilType",{SyntaxTree.RealtimeFlag});


		Address := NewBasicType("systemAddress",{SyntaxTree.RealtimeFlag});
		Size := NewBasicType("systemSize",{SyntaxTree.RealtimeFlag});
		Byte := NewBasicType("systemByte",{SyntaxTree.RealtimeFlag});
		All := NewBasicType("systemAll",{});
		Same := NewBasicType("systemSame",{});
	END Init;

BEGIN
	Init;
END OCGlobal.
