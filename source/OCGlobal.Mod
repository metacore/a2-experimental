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
	StringAligned*="ALIGNED";
	StringAlignStack*="ALIGNSTACK";

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
		Assert  Copy  Dec  Excl  Halt  Inc  Incl  New GetProcedure Connect Delegate
		Read Write
		(* global functions *)
		Abs  Ash  Cap  Chr  Entier  EntierH  Len  Long  Max  Min Odd  Ord  Short  Size
		Sum Dim First Last Step Lsl Lsr Asr
		(* system proper procedures *)
		systemGet  systemPut  systemMove  systemNew
		systemIncr Reshape
		systemZeroCopy systemTypeCode systemHalt
		systemPut8 systemPut16 systemPut32 systemPut64 systemTrace
		(* system functions *)
		systemAdr  systemBit  systemGet64  systemGet32  systemGet16  systemGet8
		systemLsh  systemRot  systemVal systemMsk systemNull

		Conversion
		end
		~
	*)
	(* global proper procedures *)
	Assert*= Scanner.EndOfText+1; Copy*= Assert+1; Dec*= Copy+1; Excl*= Dec+1; Halt*= Excl+1;
	Inc*= Halt+1; Incl*= Inc+1; New*= Incl+1; GetProcedure*= New+1; Connect*=GetProcedure+1; Delegate*=Connect+1;
	Receive*= Delegate+1; Send* = Receive+1;
	(* global functions *)
	Abs*= Send+1; Ash*= Abs+1; Cap*= Ash+1; Chr*= Cap+1; Entier*= Chr+1;
	EntierH*= Entier+1; Len*= EntierH+1; Long*= Len+1; Max*= Long+1; Min*= Max+1;
	Odd*= Min+1; Ord*= Odd+1; Short*= Ord+1; systemSizeOf*= Short+1; Sum*= systemSizeOf+1;
	Dim*= Sum+1; First*= Dim+1; Last*=First+1; Step*=Last+1; (* OLIVIER *)

	(* system proper procedures *)
	systemGet*= Step+1; (* OLIVIER *) systemPut*= systemGet+1; systemMove*= systemPut+1;
	systemNew*= systemMove+1;
	systemIncr*= systemNew+1; Reshape*= systemIncr+1; systemZeroCopy*= Reshape+1; systemTypeCode*= systemZeroCopy+1; systemHalt*= systemTypeCode+1;
	systemPut8*= systemHalt+1; systemPut16*= systemPut8+1; systemPut32*= systemPut16+1; systemPut64*= systemPut32+1;
	systemTrace*= systemPut64+1;

	(* system functions *)
	systemAdr*= systemTrace+1;
	systemBit*= systemAdr+1; systemGet64*= systemBit+1; systemGet32*= systemGet64+1; systemGet16*= systemGet32+1;
	systemGet8*= systemGet16+1; systemLsh*= systemGet8+1; systemRot*= systemLsh+1; systemVal*= systemRot+1; Conversion*= systemVal+1;
	systemHardwareAddress*=systemVal+1; systemMsk*=systemHardwareAddress+1;

	(* from ERA *)
	systemNull*=systemMsk+1; systemXOR*=systemNull+1; systemROR*=systemXOR+1; systemProc*=systemROR+1; systemStop* = systemProc + 1; LSL*=systemStop+1; LSR*=LSL+1; ASR*=LSR+1; Flt*=ASR+1; Floor*=Flt+1; Phi*=Floor+1;

	end= Floor+1;


VAR
	(* names *)
	SelfParameterName-,ReturnParameterName-,SystemName-,systemName-,PointerReturnName-, ResultName-,
	A2Name-,OberonName-,ArrayBaseName-,RecordBodyName-,ModuleBodyName-,
	NameWinAPI-,NameC-,NameUntraced-,NameDelegate-,NameInterrupt-,NameNoPAF-,NameFixed-,NameAligned-,NameStackAligned-,
	NameExclusive-,NameActive-,NamePriority-,NameSafe-,NameRealtime-: SyntaxTree.Identifier;

	identifiers: ARRAY 2 OF ARRAY end OF SyntaxTree.Identifier;

	(* some handy type variables for backend / checker implementers *)
	Boolean8, Boolean32: SyntaxTree.BooleanType;
	Set32: SyntaxTree.SetType;
	Integer8-, Integer16-, Integer32-, Integer64-: SyntaxTree.IntegerType;
	Character8-, Character16-, Character32-: SyntaxTree.CharacterType;
	Float32-, Float64-: SyntaxTree.FloatType;
	Byte8: SyntaxTree.ByteType;
	Byte32: SyntaxTree.ByteType;

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

		addressType-, sizeType-, shortintType-, integerType-, longintType-, hugeintType-, characterType-, setType-, booleanType-, anyType-,byteType-,
		realType-, longrealType-, allType-, objectType-, nilType-, arrayRangeType- (* OLIVIER *): SyntaxTree.Type;

		PROCEDURE &InitSystem*(dataUnit: LONGINT; addressSize, minVarAlign, maxVarAlign, minParAlign, maxParAlign, offsetFirstPar: LONGINT);
		VAR i: LONGINT;
		BEGIN
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
		VAR variable: SyntaxTree.Variable; offset,size: LONGINT; alignment: LONGINT; parameterOffset :LONGINT;
		BEGIN
			IF scope IS SyntaxTree.RecordScope THEN (* increasing indices *)
				RETURN GenerateRecordOffsets(scope(SyntaxTree.RecordScope).ownerRecord)
			ELSE (* module scope or procedure scope: decreasing indices *)
				ASSERT((scope IS SyntaxTree.ModuleScope) OR (scope IS SyntaxTree.ProcedureScope) OR (scope IS SyntaxTree.ActorScope)
				);
				offset := 0;
				IF scope IS SyntaxTree.ProcedureScope THEN
					parameterOffset := scope(SyntaxTree.ProcedureScope).ownerProcedure.type(SyntaxTree.ProcedureType).parameterOffset
				ELSE
					parameterOffset := 0
				END;

				variable := scope.firstVariable;
				WHILE (variable # NIL) DO
					size := SizeOf(variable.type.resolved);
					IF size < 0 THEN RETURN FALSE END;
					DEC(offset,size);
					alignment := AlignmentOf(SELF.variableAlignment,variable.type.resolved);
					Basic.Align(offset,-alignment);

					IF variable.alignment > 1 THEN
						DEC(offset, parameterOffset);
						Basic.Align(offset, -variable.alignment*dataUnit);
						INC(offset, parameterOffset);
					END;

					variable.SetOffset(offset);
					variable := variable.nextVariable;
				END;
			END;
			RETURN TRUE
		END GenerateVariableOffsets;

		PROCEDURE GenerateParameterOffsets*(procedure : SyntaxTree.Procedure; nestedProcedure: BOOLEAN): BOOLEAN;
		VAR offset,size: LONGINT;parameter: SyntaxTree.Parameter; procedureType: SyntaxTree.ProcedureType;
		BEGIN
			procedureType := procedure.type(SyntaxTree.ProcedureType);
			IF (procedure.isInline) THEN
				offset := 0
			ELSE
				offset := SELF.offsetFirstParameter;
			END;
			IF nestedProcedure THEN
				INC(offset,addressSize); (* parameter offset of static link *) (*! check alternative: add hidden parameter *)
			END;
			IF procedureType.callingConvention = SyntaxTree.OberonCallingConvention THEN
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
			procedureType.SetParameterOffset(offset);
			RETURN TRUE
		END GenerateParameterOffsets;

		PROCEDURE SizeOf*(type: SyntaxTree.Type): LONGINT;
		VAR size: LONGINT;
		BEGIN
			type := type.resolved;
			IF type IS SyntaxTree.BasicType THEN
				size := type.sizeInBits
			ELSIF type IS SyntaxTree.PointerType THEN
				size := addressSize
			ELSIF type IS SyntaxTree.ProcedureType THEN

				IF type(SyntaxTree.ProcedureType).isDelegate THEN
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
				(*
			ELSIF type IS SyntaxTree.ActorType THEN
				(* do not treat a record type like a pointer even if the Pointer field is set, this leads to problems in object files
					rather make sure that each reference type is a POINTER TO at least behind the secenes!
				*)
				ASSERT(SyntaxTree.Resolved IN type.state);
				size :=type(SyntaxTree.ActorType).sizeInBits;
				IF size < 0 THEN
					IF GenerateVariableOffsets(type(SyntaxTree.ActorType).actorScope) THEN
						IF type(SyntaxTree.ActorType).actorScope.lastVariable = NIL THEN
							size := 0
						ELSE
							size := ABS(type(SyntaxTree.ActorType).actorScope.lastVariable.offsetInBits);
						END;
					ELSE
						size := -1
					END;
				END;
				*)
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
				size := type(SyntaxTree.StringType).length * SizeOf(type(SyntaxTree.StringType).baseType);
			ELSIF type IS SyntaxTree.EnumerationType THEN
				size := addressSize
			ELSIF type = SyntaxTree.invalidType THEN size := 0
			ELSIF type IS SyntaxTree.QualifiedType THEN
				HALT(101); (* hint that unresolved type has been taken for type size computation *)
			ELSIF type IS SyntaxTree.PortType THEN
				size := addressSize
			ELSIF type IS SyntaxTree.ActorType THEN
				size := 0;
			(* OLIVIER *)
			ELSIF type IS SyntaxTree.ArrayRangeType THEN
				size := 3 * SizeOf(longintType);
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
				ELSIF IsOberonProcedure(par.ownerType) THEN
					RETURN SizeOf(par.type);
				ELSE RETURN addressSize
				END

			(* OLIVIER *)
			ELSIF par.type.resolved IS SyntaxTree.ArrayRangeType THEN
				IF par.kind = SyntaxTree.VarParameter THEN
					RETURN addressSize
				ELSE
					RETURN SizeOf(arrayRangeType) (* array range components are materialized on stack for both value and const parameters *)
				END

			ELSIF (par.kind IN {SyntaxTree.ConstParameter,SyntaxTree.VarParameter}) THEN
				IF (par.type.resolved IS SyntaxTree.RecordType) THEN
					IF IsOberonProcedure(par.ownerType) THEN
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
				result := SizeOf(type(SyntaxTree.StringType).baseType);
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

	(* OLIVIER *)
	PROCEDURE SetDefaultDeclarations*(system: System; minBits: LONGINT);
	BEGIN
		(* types *)
		system.longintType := Integer32;
		system.hugeintType := Integer64;
		system.realType := Float32;
		system.longrealType := Float64;
		system.setType := Set32;

		IF minBits = 32 THEN
			system.shortintType := Integer32;
			system.integerType := Integer32;
			system.booleanType := Boolean32;
			system.byteType := Byte32;
			system.characterType := Character32;
		ELSE
			ASSERT(minBits = 8); (* nothing else is currently implemented *)
			system.shortintType := Integer8;
			system.integerType := Integer16;
			system.booleanType := Boolean8;
			system.byteType := Byte8;
			system.characterType := Character8;
		END;

		system.allType := SyntaxTree.NewAllType(system.addressSize);
		system.anyType := SyntaxTree.NewAnyType(system.addressSize);
		system.objectType := SyntaxTree.NewObjectType(system.addressSize);
		system.nilType := SyntaxTree.NewNilType(system.addressSize);
		system.addressType := SyntaxTree.NewAddressType(system.addressSize);
		system.sizeType := SyntaxTree.NewSizeType(system.addressSize);
		system.arrayRangeType := SyntaxTree.NewArrayRangeType(3 * system.SizeOf(system.longintType)); (* OLIVIER *)

		(* type declarations *)
		DeclareType(system.byteType,"BYTE",system.systemScope);
		DeclareType(system.addressType,"ADDRESS",system.systemScope); (* mapped to longint *)
		DeclareType(system.sizeType,"SIZE",system.systemScope); (* mapped to longint *)
		DeclareType(system.allType,"ALL",system.systemScope);
		(*DeclareType(Same,"SAME",system.systemScope);*)

		(* system builtin procedures *)
		NewBuiltin(systemGet,"GET",system.systemScope,TRUE);
		NewBuiltin(systemPut,"PUT",system.systemScope,TRUE);
		NewBuiltin(systemMove,"MOVE",system.systemScope,TRUE);
		NewBuiltin(systemNew,"NEW",system.systemScope,FALSE);
		NewBuiltin(Reshape,"RESHAPE",system.globalScope,TRUE);
		NewBuiltin(systemZeroCopy,"ZEROCOPY",system.systemScope,TRUE);
		NewBuiltin(systemHalt,"HALT",system.systemScope,TRUE);
		NewBuiltin(systemPut64,"PUT64",system.systemScope,TRUE);
		NewBuiltin(systemPut32,"PUT32",system.systemScope,TRUE);
		NewBuiltin(systemPut16,"PUT16",system.systemScope,TRUE);
		NewBuiltin(systemPut8,"PUT8",system.systemScope,TRUE);
		NewBuiltin(systemAdr,"ADR",system.systemScope,TRUE);
		NewBuiltin(systemBit,"BIT",system.systemScope,TRUE);
		NewBuiltin(systemGet64,"GET64",system.systemScope,TRUE);
		NewBuiltin(systemGet32,"GET32",system.systemScope,TRUE);
		NewBuiltin(systemGet16,"GET16",system.systemScope,TRUE);
		NewBuiltin(systemGet8,"GET8",system.systemScope,TRUE);
		NewBuiltin(systemLsh,"LSH",system.systemScope,TRUE);
		NewBuiltin(systemRot,"ROT",system.systemScope,TRUE);
		NewBuiltin(systemVal,"VAL",system.systemScope,TRUE);
		NewBuiltin(systemIncr,"INCR",system.systemScope,TRUE);
		NewBuiltin(systemTypeCode,"TYPECODE",system.systemScope,TRUE);
		NewBuiltin(systemSizeOf,"SIZEOF",system.systemScope,TRUE);
		NewBuiltin(systemMsk,"MSK",system.systemScope,TRUE);

		(* Set up system types *)
		system.characterType := Character8;
		DeclareType(system.characterType,"CHAR",system.globalScope);
		DeclareType(Character8,"CHAR8",system.globalScope);
		DeclareType(Character16,"CHAR16",system.globalScope);
		DeclareType(Character32,"CHAR32",system.globalScope);
		DeclareType(system.arrayRangeType,"RANGE",system.globalScope); (* OLIVIER *)
		DeclareType(system.shortintType,"SHORTINT",system.globalScope);
		DeclareType(system.integerType,"INTEGER",system.globalScope);
		DeclareType(system.longintType,"LONGINT",system.globalScope);
		DeclareType(system.hugeintType,"HUGEINT",system.globalScope);
		DeclareType(system.realType,"REAL",system.globalScope);
		DeclareType(system.longrealType,"LONGREAL",system.globalScope);
		DeclareType(system.booleanType,"BOOLEAN",system.globalScope);
		DeclareType(system.setType,"SET",system.globalScope);
		DeclareType(system.anyType,"ANY",system.globalScope);
		DeclareType(system.objectType,"OBJECT",system.globalScope);

		(* global functions *)
		NewBuiltin(Abs,"ABS",system.globalScope,TRUE);
		NewBuiltin(Ash,"ASH",system.globalScope,TRUE);
		NewBuiltin(Cap,"CAP",system.globalScope,TRUE);
		NewBuiltin(Chr,"CHR",system.globalScope,TRUE);
		NewBuiltin(Entier,"ENTIER",system.globalScope,TRUE);
		NewBuiltin(EntierH,"ENTIERH",system.globalScope,TRUE);
		NewBuiltin(Len,"LEN",system.globalScope,TRUE);
		NewBuiltin(Long,"LONG",system.globalScope,TRUE);
		NewBuiltin(Max,"MAX",system.globalScope,TRUE);
		NewBuiltin(Min,"MIN",system.globalScope,TRUE);
		NewBuiltin(Odd,"ODD",system.globalScope,TRUE);
		NewBuiltin(Ord,"ORD",system.globalScope,TRUE);
		NewBuiltin(Short,"SHORT",system.globalScope,TRUE);
		NewBuiltin(Sum,"SUM",system.globalScope,TRUE);
		NewBuiltin(Dim,"DIM",system.globalScope,TRUE);

		(* OLIVIER *)
		NewBuiltin(First,"FIRST",system.globalScope,TRUE);
		NewBuiltin(Last,"LAST",system.globalScope,TRUE);
		NewBuiltin(Step,"STEP",system.globalScope,TRUE);

		(* global proper procedures *)
		NewBuiltin(Assert,"ASSERT",system.globalScope,TRUE);
		NewBuiltin(Copy,"COPY",system.globalScope,TRUE);
		NewBuiltin(Dec,"DEC",system.globalScope,TRUE);
		NewBuiltin(Excl,"EXCL",system.globalScope,TRUE);
		NewBuiltin(Halt,"HALT",system.globalScope,TRUE);
		NewBuiltin(Inc,"INC",system.globalScope,TRUE);
		NewBuiltin(Incl,"INCL",system.globalScope,TRUE);
		NewBuiltin(New,"NEW",system.globalScope,FALSE);
		NewBuiltin(GetProcedure,"GETPROCEDURE",system.globalScope,TRUE);
		NewBuiltin(systemTrace,"TRACE",system.globalScope,TRUE);
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
		SetDefaultDeclarations(system,8);
		SetDefaultOperators(system);
		RETURN system
	END DefaultSystem;

	PROCEDURE IsOberonProcedure*(type: SyntaxTree.Type): BOOLEAN;
	BEGIN
		RETURN (type IS SyntaxTree.ProcedureType) & (type(SyntaxTree.ProcedureType).callingConvention = SyntaxTree.OberonCallingConvention)
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

	PROCEDURE NewBuiltin0( id: LONGINT; CONST name: Scanner.StringType; in:  SyntaxTree.ModuleScope; realtime: BOOLEAN);
	VAR basic: SyntaxTree.Builtin; duplicate: BOOLEAN; type: SyntaxTree.ProcedureType;
	BEGIN
		basic := SyntaxTree.NewBuiltin(-1,SyntaxTree.NewIdentifier(-1,name),id);
		basic.SetAccess(SyntaxTree.ReadOnly);
		type := SyntaxTree.NewProcedureType(-1,in);
		type.SetRealtime(realtime);
		type.SetReturnType(SyntaxTree.invalidType); (* make incompatible to any procedure *)
		basic.SetType(type);
		basic.SetState(SyntaxTree.Resolved);
		in.EnterSymbol(basic,duplicate);
		in.AddBuiltin(basic);
		ASSERT(~duplicate);
	END NewBuiltin0;

	PROCEDURE NewBuiltin*(id: LONGINT; CONST name: Scanner.StringType; CONST scope: ARRAY OF SyntaxTree.ModuleScope; realtime: BOOLEAN);
	VAR nameL,nameU: Scanner.StringType;
	BEGIN
		Basic.Lowercase(name,nameL);
		Basic.Uppercase(name,nameU);
		NewBuiltin0(id,nameU,scope[Scanner.Uppercase],realtime);
		NewBuiltin0(id,nameL,scope[Scanner.Lowercase],realtime);
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
			Basic.Concat(fileName,prefix,"-",name);
		END;
	END ModuleFileName;

	PROCEDURE ContextFromName*(CONST fileName: ARRAY OF CHAR; VAR module,context: SyntaxTree.Identifier);
	VAR moduleName, contextName: Scanner.StringType; i,j: LONGINT;
	BEGIN
		i := 0; j := 0;
		WHILE (fileName[i] # 0X) & (fileName[i] # "-") DO
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

	PROCEDURE GetModuleName*(module: SyntaxTree.Module; VAR name: ARRAY OF CHAR);
	VAR n: SyntaxTree.String;
	BEGIN
		module.context.GetString(n);
		IF n# "A2" THEN Strings.Append(name,n);Strings.Append(name,"-") END;
		module.name.GetString(n);
		Strings.Append(name,n);
	END GetModuleName;

	PROCEDURE GetSymbolNameInScope*(symbol: SyntaxTree.Symbol; inScope: SyntaxTree.Scope; VAR name: ARRAY OF CHAR);
	VAR n: SyntaxTree.String; td: SyntaxTree.TypeDeclaration;
		PROCEDURE Scope(scope: SyntaxTree.Scope);
		BEGIN
			IF scope = NIL THEN (* do nothing, locally declared temporary symbol *)
			ELSIF scope = inScope THEN (* do not traverse further *)
			ELSIF scope IS SyntaxTree.ModuleScope THEN
				GetModuleName(scope.ownerModule, name);
				Strings.Append(name,".");
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
			ELSIF scope IS SyntaxTree.ActorScope THEN
				Scope(scope.outerScope);
				td := scope(SyntaxTree.ActorScope).ownerActor.typeDeclaration;
				td.name.GetString(n);
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
	END GetSymbolNameInScope;

	PROCEDURE GetSymbolName*(symbol: SyntaxTree.Symbol; VAR name: ARRAY OF CHAR);
	BEGIN GetSymbolNameInScope(symbol,NIL,name)
	END GetSymbolName;

	PROCEDURE Level*(t: SyntaxTree.Type): LONGINT;
	VAR level: LONGINT;
	BEGIN
		IF t IS SyntaxTree.IntegerType THEN
			CASE t.sizeInBits OF
				8: level := 0;
				|16: level := 1;
				|32: level := 2;
				|64: level := 3;
			END;
		ELSIF t IS SyntaxTree.FloatType THEN
			CASE t.sizeInBits OF
				32: level := 4;
				|64: level := 5;
			END
		ELSE HALT(100)
		END;
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

	PROCEDURE MaxInteger*(system: System; type: SyntaxTree.IntegerType): HUGEINT;
	VAR h: HUGEINT;
	BEGIN
		h := Runtime.AslH(1,system.SizeOf(type)-1);
		RETURN h-1
	END MaxInteger;

	PROCEDURE MinInteger*(system: System; type: SyntaxTree.IntegerType): HUGEINT;
	VAR h: HUGEINT;
	BEGIN
		h := Runtime.AslH(1,system.SizeOf(type)-1);
		RETURN -h
	END MinInteger;

	(*! make architecture  independent ! *)
	PROCEDURE MaxFloat*(system: System; type: SyntaxTree.FloatType): LONGREAL;
	BEGIN
		IF system.SizeOf(type) = 32 THEN RETURN MAX(REAL) ELSE RETURN MAX(LONGREAL) END;
	END MaxFloat;

	PROCEDURE MinFloat*(system: System; type: SyntaxTree.FloatType): LONGREAL;
	BEGIN
		IF system.SizeOf(type) = 32 THEN RETURN MIN(REAL) ELSE RETURN MIN(LONGREAL) END;
	END MinFloat;

	PROCEDURE GetIntegerType*(system: System; this: HUGEINT): SyntaxTree.IntegerType;

		PROCEDURE InBounds(type: SyntaxTree.Type): BOOLEAN;
		VAR m: HUGEINT;
		BEGIN
			m := Runtime.AslH(1,system.SizeOf(type)-1);
			RETURN (this < m) & (-this <= m)
		END InBounds;

	BEGIN
		IF InBounds(Integer8) THEN RETURN Integer8
		ELSIF InBounds(Integer16) THEN RETURN Integer16
		ELSIF InBounds(Integer32) THEN RETURN Integer32
		ELSE RETURN Integer64
		END;
	END GetIntegerType;

	PROCEDURE NewIntegerValue*(system: System; position: LONGINT; hugeint: HUGEINT): SyntaxTree.Value;
	VAR value: SyntaxTree.IntegerValue;
	BEGIN
		value := SyntaxTree.NewIntegerValue(position,hugeint);
		value.SetType(GetIntegerType(system,hugeint));
		RETURN value
	END NewIntegerValue;

	PROCEDURE NewBooleanValue*(system: System; position: LONGINT; b: BOOLEAN): SyntaxTree.Value;
	VAR value: SyntaxTree.BooleanValue;
	BEGIN
		value := SyntaxTree.NewBooleanValue(position,b);
		value.SetType(system.booleanType);
		RETURN value
	END NewBooleanValue;

	PROCEDURE NewSetValue*(system: System; position: LONGINT; s: SET): SyntaxTree.Value;
	VAR value: SyntaxTree.SetValue;
	BEGIN
		value := SyntaxTree.NewSetValue(position,s);
		value.SetType(system.setType);
		RETURN value
	END NewSetValue;

	PROCEDURE NewCharacterValue*(system: System; position: LONGINT; c: CHAR): SyntaxTree.Value;
	VAR value: SyntaxTree.CharacterValue;
	BEGIN
		value := SyntaxTree.NewCharacterValue(position,c);
		value.SetType(system.characterType);
		RETURN value
	END NewCharacterValue;

	PROCEDURE NewNilValue*(system: System; position: LONGINT): SyntaxTree.Value;
	VAR value: SyntaxTree.NilValue;
	BEGIN
		value := SyntaxTree.NewNilValue(position);
		value.SetType(system.anyType);
		RETURN value
	END NewNilValue;

	(* distance for assignment to <- from *)
	PROCEDURE BasicTypeDistance*(system: System; from, to: SyntaxTree.BasicType): LONGINT;
	VAR fromSize, toSize, distance: LONGINT;
	BEGIN
		fromSize := system.SizeOf(from); toSize := system.SizeOf(to);
		distance := -1;
		IF (from IS SyntaxTree.CharacterType) & (to IS SyntaxTree.CharacterType) OR
			(from IS SyntaxTree.IntegerType) & (to IS SyntaxTree.IntegerType) OR
			(from IS SyntaxTree.FloatType) & (to IS SyntaxTree.FloatType) THEN
			WHILE toSize >= fromSize DO
				toSize := toSize DIV 2; INC(distance);
			END;
		ELSIF (from IS SyntaxTree.IntegerType) & (to IS SyntaxTree.FloatType) THEN
			IF toSize = 64 THEN distance := 1 ELSE distance := 0 END;
			toSize := 64;
			WHILE toSize >= fromSize DO
				toSize := toSize DIV 2; INC(distance);
			END;
		END;
		IF distance < 0 THEN distance := MAX(LONGINT) END;
		RETURN distance
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

		NameWinAPI := SyntaxTree.NewIdentifier(-1, StringWinAPI);
		NameC := SyntaxTree.NewIdentifier(-1, StringC);
		NameUntraced := SyntaxTree.NewIdentifier(-1, StringUntraced);
		NameDelegate := SyntaxTree.NewIdentifier(-1, StringDelegate);
		NameInterrupt := SyntaxTree.NewIdentifier(-1, StringInterrupt);
		NameNoPAF := SyntaxTree.NewIdentifier(-1, StringNoPAF);
		NameFixed := SyntaxTree.NewIdentifier(-1, StringFixed);
		NameAligned := SyntaxTree.NewIdentifier(-1, StringAligned);
		NameStackAligned := SyntaxTree.NewIdentifier(-1, StringAlignStack);
		NameExclusive := SyntaxTree.NewIdentifier(-1, StringExclusive);
		NameActive := SyntaxTree.NewIdentifier(-1, StringActive);
		NamePriority := SyntaxTree.NewIdentifier(-1, StringPriority);
		NameSafe := SyntaxTree.NewIdentifier(-1, StringSafe);
		NameRealtime := SyntaxTree.NewIdentifier(-1, StringRealtime);


		(* types *)
		Boolean8 := SyntaxTree.NewBooleanType(8);
		Boolean32 := SyntaxTree.NewBooleanType(32);
		Set32 := SyntaxTree.NewSetType(32);
		Integer8 := SyntaxTree.NewIntegerType(8, TRUE);
		Integer16 := SyntaxTree.NewIntegerType(16, TRUE);
		Integer32 := SyntaxTree.NewIntegerType(32, TRUE);
		Integer64 := SyntaxTree.NewIntegerType(64, TRUE);
		Float32 := SyntaxTree.NewFloatType(32);
		Float64 := SyntaxTree.NewFloatType(64);
		Byte8 := SyntaxTree.NewByteType(8);
		Byte32 := SyntaxTree.NewByteType(32);
		Character8 := SyntaxTree.NewCharacterType(8);
		Character16 := SyntaxTree.NewCharacterType(16);
		Character32 := SyntaxTree.NewCharacterType(32);
	END Init;

BEGIN
	Init;
END OCGlobal.
