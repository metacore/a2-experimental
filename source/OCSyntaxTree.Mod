MODULE OCSyntaxTree;   (**  AUTHOR "fof & fn"; PURPOSE "Oberon Compiler: Abstract Syntax Tree";  **)
(* (c) fof ETHZ 2009 *)

(**
	note on documentation:
	Most objects in this module are commented with an informal Oberon syntax example indicating which variables of the respective object stand for what symbol /expression etc.
	This syntax example should not be confused with a profound description of the syntax in an EBNF form, which can rather be found in the parser module.
	The informal Oberon syntax is marked with << ... >>
**)

IMPORT
	Basic := OCBasic, Scanner := OCScanner, BitSets, Commands,StringPool (* , D := Debugging (* only for debuggging / counting *) *) ;

CONST
	(** general flags: used in statements, procedure types and symbols
		general flags are unique and may overlap with access flags only
		flag numbers have no meaning and are not used for object files etc., i.e. flag renumbering is possible without effect
	*)

	(* block modifier flags *)
	ActiveFlag*= 0; 				(** block is an active body **)
	ExclusiveFlag*=1;				(** block is exclusive **)
	SafeFlag*=2; 					(** block is safe (restartable) **)
	PriorityFlag*=3; 				(** block has priority **)
	RealtimeFlag*=4; 				(** block has realtime flag **)
	(* non-Oberon calling conventions *)
	WinAPIFlag*=5;
	CFlag*=6;
	(* other flags *)
	InlineFlag*=7;
	DelegateFlag*=8;
	UntracedFlag*=9;
	ConstructorFlag*=10;
	BodyProcedureFlag*=11;

	InterruptFlag*=12;
	NoPAFFlag*=13;
	FixedFlag*=14;

	(* statement flags *)
	UnreachableFlag*=15;
	(* modification flags *)
	WrittenFlag*=16;
	AccessedFlag*=17;
	MappedFlag*=18; (* for dataflow ports *)

	DataflowFlag*=19;

	(** Access Flags *)
	InternalRead* = 0;			(** can read symbol in same module *)
	InternalWrite* = 1;		(** can write symbol in same module *)
	ProtectedRead* = 2;		(** can read symbol in type extentions *)
	ProtectedWrite* = 3;		(** can write symbol in type extentions *)
	PublicRead* = 4;			(** can read everywhere *)
	PublicWrite* = 5;			(** can write everywhere *)

	Hidden* = {};
	Internal* = {InternalRead, InternalWrite};
	Protected* = {ProtectedRead, ProtectedWrite} ;
	Public* = {PublicRead, PublicWrite} ;
	ReadOnly* = {InternalRead, ProtectedRead,PublicRead};

	(** parameter forms *)
	ValueParameter* = 0;  VarParameter* = 1;  ConstParameter* = 2;
	InPort*=3; 	OutPort*=4;

	(** array forms *)
	Static*=1; (* ARRAY x OF .. / ARRAY [x] OF ... *)
	Open*=2; (* ARRAY OF ... / ARRAY [*] OF ... *)
	Tensor*=3; (* ARRAY [?] OF ... *)

	(** node states, important for checker to avoid cycles *)
	Undefined*={}; BeingResolved*=1; Resolved*=2; FingerPrinted*=3;

VAR
	(** debugging / counters *)

	nodeCount, listCount, identifierCount, qualifiedIdentifierCount, typeCount, basicTypeCount, typeDeclarationCount, arrayTypeCount, pointerTypeCount,
	portTypeCount, recordTypeCount, actorTypeCount,
	defintionTypeCount, procedureTypeCount, qualifiedTypeCount, typeDeclarationListCount, definitionCount, definitionTypeCount, expressionCount,
	expressionListCount, selectorCount,
	identifierDesignatorCount, indexDesignatorCount, parameterDesignatorCount, dereferenceDesignatorCount,
	bracketDesignatorCount, symbolDesignatorCount, supercallDesignatorCount, selfDesignatorCount,
	designatorCount, elementCount, setCount, mathArrayExpressionCount, mathArrayValueCount,
	binaryExpressionCount, unaryExpressionCount, valueCount, booleanValueCount, integerValueCount, setValueCount, realValueCount, hugeintValueCount, stringValueCount,
	nilValueCount, enumeratorValueCount, callerCount, assignmentCount, ifStatementCount, withStatementCount, casePartCount, ifPartCount, caseStatementCount, whileStatementCount, repeatStatementCount,
	forStatementCount, loopStatementCount, exitStatementCount, returnStatementCount, awaitStatementCount, definitionListCount, constantCount,
	constantListCount, variableCount, variableListCount, procedureCount, methodCount, procedureListCount, operatorCount, operatorListCount, parameterCount,
	parameterListCount, importCount, importListCount, statementSequenceCount, declarationSequenceCount, statementBlockCount, bodyCount,
	moduleCount: LONGINT;

TYPE
	SourceCode*= Scanner.SourceString;
	BinaryCode*= BitSets.BitSet;
	String*= Scanner.StringType;

	(** visitor pattern implementation *)
	(* to use this object in your implementation, copy and paste and replace "x: " by "x: SyntaxTree." *)
	Visitor* = OBJECT

		(** types *)
		PROCEDURE VisitType*(x: Type);
		BEGIN HALT(100) (* abstract *) END VisitType;

		PROCEDURE VisitBasicType*(x: BasicType);
		BEGIN HALT(100) (* abstract *) END VisitBasicType;

		PROCEDURE VisitCharacterType*(x: CharacterType);
		BEGIN HALT(100) END VisitCharacterType;

		PROCEDURE VisitIntegerType*(x: IntegerType);
		BEGIN HALT(100) END VisitIntegerType;

		PROCEDURE VisitFloatType*(x: FloatType);
		BEGIN HALT(100) END VisitFloatType;

		PROCEDURE VisitQualifiedType*(x: QualifiedType);
		BEGIN HALT(100) (* abstract *) END VisitQualifiedType;

		PROCEDURE VisitStringType*(x: StringType);
		BEGIN HALT(100) (* abstract *) END VisitStringType;

		PROCEDURE VisitEnumerationType*(x: EnumerationType);
		BEGIN HALT(100) (* abstract *) END VisitEnumerationType;

		PROCEDURE VisitRangeType*(x: RangeType);
		BEGIN HALT(100) (* abstract *) END VisitRangeType;

		PROCEDURE VisitArrayType*(x: ArrayType);
		BEGIN HALT(100) (* abstract *) END VisitArrayType;

		PROCEDURE VisitMathArrayType*(x: MathArrayType);
		BEGIN HALT(100) (* abstract *) END VisitMathArrayType;

		PROCEDURE VisitPointerType*(x: PointerType);
		BEGIN HALT(100) (* abstract *) END VisitPointerType;

		PROCEDURE VisitPortType*(x: PortType);
		BEGIN HALT(100) (* abstract *) END VisitPortType;

		PROCEDURE VisitRecordType*(x: RecordType);
		BEGIN HALT(100) (* abstract *) END VisitRecordType;

		PROCEDURE VisitActorType*(x: ActorType);
		BEGIN HALT(100) (* abstract *) END VisitActorType;

		PROCEDURE VisitProcedureType*(x: ProcedureType);
		BEGIN HALT(100) (* abstract *) END VisitProcedureType;

		(** expressions *)
		PROCEDURE VisitExpression*(x: Expression);
		BEGIN HALT(100) (* abstract *) END VisitExpression;

		PROCEDURE VisitSet*(x: Set);
		BEGIN HALT(100) (* abstract *) END VisitSet;

		PROCEDURE VisitMathArrayExpression*(x: MathArrayExpression);
		BEGIN HALT(100) (* abstract *) END VisitMathArrayExpression;

		PROCEDURE VisitUnaryExpression*(x: UnaryExpression);
		BEGIN HALT(100) (* abstract *) END VisitUnaryExpression;

		PROCEDURE VisitBinaryExpression*(x: BinaryExpression);
		BEGIN HALT(100) (* abstract *) END VisitBinaryExpression;

		PROCEDURE VisitRangeExpression*(x: RangeExpression);
		BEGIN HALT(100) (* abstract *) END VisitRangeExpression;

		PROCEDURE VisitTensorRangeExpression*(x: TensorRangeExpression);
		BEGIN HALT(100) (* abstract *) END VisitTensorRangeExpression;

		PROCEDURE VisitConversion*(x: Conversion);
		BEGIN HALT(100) (* abstract *) END VisitConversion;

		(** designators (expressions) *)
		PROCEDURE VisitDesignator*(x: Designator);
		BEGIN HALT(100) (* abstract *) END VisitDesignator;

		PROCEDURE VisitIdentifierDesignator*(x: IdentifierDesignator);
		BEGIN HALT(100) (* abstract *) END VisitIdentifierDesignator;

		PROCEDURE VisitSelectorDesignator*(x: SelectorDesignator);
		BEGIN HALT(100) (* abstract *) END VisitSelectorDesignator;

		PROCEDURE VisitParameterDesignator*(x: ParameterDesignator);
		BEGIN HALT(100) (* abstract *) END VisitParameterDesignator;

		PROCEDURE VisitArrowDesignator*(x: ArrowDesignator);
		BEGIN HALT(100) (* abstract *) END VisitArrowDesignator;

		PROCEDURE VisitBracketDesignator*(x: BracketDesignator);
		BEGIN HALT(100) (* abstract *) END VisitBracketDesignator;

		PROCEDURE VisitSymbolDesignator*(x: SymbolDesignator);
		BEGIN HALT(100) (* abstract *) END VisitSymbolDesignator;

		PROCEDURE VisitIndexDesignator*(x: IndexDesignator);
		BEGIN HALT(100) (* abstract *) END VisitIndexDesignator;

		PROCEDURE VisitProcedureCallDesignator*(x: ProcedureCallDesignator);
		BEGIN HALT(100) (* abstract *) END VisitProcedureCallDesignator;

		PROCEDURE VisitBuiltinCallDesignator*(x: BuiltinCallDesignator);
		BEGIN HALT(100) (* abstract *) END VisitBuiltinCallDesignator;

		PROCEDURE VisitTypeGuardDesignator*(x: TypeGuardDesignator);
		BEGIN HALT(100) (* abstract *) END VisitTypeGuardDesignator;

		PROCEDURE VisitDereferenceDesignator*(x: DereferenceDesignator);
		BEGIN HALT(100) (* abstract *) END VisitDereferenceDesignator;

		PROCEDURE VisitSupercallDesignator*(x: SupercallDesignator);
		BEGIN HALT(100) (* abstract *) END VisitSupercallDesignator;

		PROCEDURE VisitSelfDesignator*(x: SelfDesignator);
		BEGIN HALT(100) (* abstract *) END VisitSelfDesignator;

		(** values *)
		PROCEDURE VisitValue*(x: Value);
		BEGIN HALT(100) (* abstract *) END VisitValue;

		PROCEDURE VisitBooleanValue*(x: BooleanValue);
		BEGIN HALT(100) (* abstract *) END VisitBooleanValue;

		PROCEDURE VisitIntegerValue*(x: IntegerValue);
		BEGIN HALT(100) (* abstract *) END VisitIntegerValue;

		PROCEDURE VisitCharacterValue*(x: CharacterValue);
		BEGIN HALT(100) (* abstract *) END VisitCharacterValue;

		PROCEDURE VisitSetValue*(x: SetValue);
		BEGIN HALT(100) (* abstract *) END VisitSetValue;

		PROCEDURE VisitMathArrayValue*(x: MathArrayValue);
		BEGIN HALT(100) (* abstract *) END VisitMathArrayValue;

		PROCEDURE VisitRealValue*(x: RealValue);
		BEGIN HALT(100) (* abstract *) END VisitRealValue;

		PROCEDURE VisitStringValue*(x: StringValue);
		BEGIN HALT(100) (* abstract *) END VisitStringValue;

		PROCEDURE VisitNilValue*(x: NilValue);
		BEGIN HALT(100) (* abstract *) END VisitNilValue;

		PROCEDURE VisitEnumerationValue*(x: EnumerationValue);
		BEGIN HALT(100) (* abstract *) END VisitEnumerationValue;

		(** symbols *)
		PROCEDURE VisitSymbol*(x: Symbol);
		BEGIN HALT(100) (* abstract *) END VisitSymbol;

		PROCEDURE VisitTypeDeclaration*(x: TypeDeclaration);
		BEGIN HALT(100) (* abstract *) END VisitTypeDeclaration;

		PROCEDURE VisitConstant*(x: Constant);
		BEGIN HALT(100) (* abstract *) END VisitConstant;

		PROCEDURE VisitVariable*(x: Variable);
		BEGIN HALT(100) (* abstract *) END VisitVariable;

		PROCEDURE VisitParameter*(x: Parameter);
		BEGIN HALT(100) (* abstract *) END VisitParameter;

		PROCEDURE VisitProcedure*(x: Procedure);
		BEGIN HALT(100) (* abstract *) END VisitProcedure;

		PROCEDURE VisitBuiltin*(x: Builtin);
		BEGIN HALT(100) (* abstract *) END VisitBuiltin;

		PROCEDURE VisitOperator*(x: Operator);
		BEGIN HALT(100) (* abstract *) END VisitOperator;

		PROCEDURE VisitImport*(x: Import);
		BEGIN HALT(100) (* abstract *) END VisitImport;

		(** statements *)
		PROCEDURE VisitStatement*(x: Statement);
		BEGIN HALT(100) (* abstract *) END VisitStatement;

		PROCEDURE VisitProcedureCallStatement*(x: ProcedureCallStatement);
		BEGIN HALT(100) (* abstract *) END VisitProcedureCallStatement;

		PROCEDURE VisitAssignment*(x: Assignment);
		BEGIN HALT(100) (* abstract *) END VisitAssignment;

		PROCEDURE VisitIfStatement*(x: IfStatement);
		BEGIN HALT(100) (* abstract *) END VisitIfStatement;

		PROCEDURE VisitWithStatement*(x: WithStatement);
		BEGIN HALT(100) (* abstract *) END VisitWithStatement;

		PROCEDURE VisitCaseStatement*(x: CaseStatement);
		BEGIN HALT(100) (* abstract *) END VisitCaseStatement;

		PROCEDURE VisitWhileStatement*(x: WhileStatement);
		BEGIN HALT(100) (* abstract *) END VisitWhileStatement;

		PROCEDURE VisitRepeatStatement*(x: RepeatStatement);
		BEGIN HALT(100) (* abstract *) END VisitRepeatStatement;

		PROCEDURE VisitForStatement*(x: ForStatement);
		BEGIN HALT(100) (* abstract *) END VisitForStatement;

		PROCEDURE VisitLoopStatement*(x: LoopStatement);
		BEGIN HALT(100) (* abstract *) END VisitLoopStatement;

		PROCEDURE VisitExitStatement*(x: ExitStatement);
		BEGIN HALT(100) (* abstract *) END VisitExitStatement;

		PROCEDURE VisitReturnStatement*(x: ReturnStatement);
		BEGIN HALT(100) (* abstract *) END VisitReturnStatement;

		PROCEDURE VisitAwaitStatement*(x: AwaitStatement);
		BEGIN HALT(100) (* abstract *) END VisitAwaitStatement;

		PROCEDURE VisitStatementBlock*(x: StatementBlock);
		BEGIN HALT(100) (* abstract *) END VisitStatementBlock;

		PROCEDURE VisitCode*(x: Code);
		BEGIN HALT(100) (* abstract *) END VisitCode;

	END Visitor;

	Fingerprint*= RECORD
		shallow*,public*, private*: LONGINT;
		shallowAvailable*, deepAvailable*: BOOLEAN;
	END;

	(** identifiers in a program text **)
	Identifier* = OBJECT
		VAR
			name-: Basic.String;
			position-: LONGINT;

		PROCEDURE & InitIdentifier( position: LONGINT;  CONST id: ARRAY OF CHAR);
		BEGIN
			name := Basic.MakeString( id );
			SELF.position := position;
		END InitIdentifier;

		PROCEDURE Equals*(this: Identifier): BOOLEAN;
		BEGIN	RETURN (this # NIL) & Basic.StringEqual(this.name,name)
		END Equals;

		PROCEDURE GetString*(VAR name: ARRAY OF CHAR);
		BEGIN
			Basic.GetString(SELF.name,name);
		END GetString;

	END Identifier;

	(** qualified identifiers << Identifier.Identifier >> **)
	QualifiedIdentifier* = OBJECT
		VAR
			prefix-, suffix-: Identifier;   (* use string index instead ? *)

		PROCEDURE & InitQualifiedIdentifier( position: LONGINT;  prefix, suffix: Identifier);
		BEGIN
			ASSERT(suffix # NIL);
			SELF.prefix := prefix; SELF.suffix := suffix;
		END InitQualifiedIdentifier;

	END QualifiedIdentifier;

	(**** types ****)

	Type* = OBJECT
		VAR
			typeDeclaration-: TypeDeclaration; (* link to declaration (if any), needed for printing, debugging and symbol lookup *)
			scope-: Scope; (* scope where the type has been declared *)
			resolved-: Type; (* indirection to resolved type to preserve qualified types *)
			position-,endposition-: LONGINT;
			flags-, state-: SET;
			fingerprint-: Fingerprint;


		PROCEDURE & InitType*( position: LONGINT; flags: SET);
		BEGIN
			SELF.position := position; state := Undefined;
			SELF.flags := flags;
			typeDeclaration := NIL;
			scope := NIL;
			resolved := SELF;
			InitFingerprint(fingerprint)
		END InitType;

		PROCEDURE End*( position: LONGINT );
		BEGIN SELF.endposition := position;
		END End;

		PROCEDURE SetFingerprint*(CONST fp: Fingerprint);
		BEGIN
			SELF.fingerprint := fp
		END SetFingerprint;

		PROCEDURE SetState*(state: LONGINT);
		BEGIN	INCL(SELF.state,state);
		END SetState;

		PROCEDURE AddFlags*(flags: SET);
		BEGIN SELF.flags := SELF.flags + flags;
		END AddFlags;

		PROCEDURE SetTypeDeclaration*(typeDeclaration: TypeDeclaration);
		BEGIN SELF.typeDeclaration := typeDeclaration
		END SetTypeDeclaration;

		PROCEDURE SetScope*(scope: Scope);
		BEGIN SELF.scope := scope
		END SetScope;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitType(SELF)
		END Accept;

		PROCEDURE IsRealtime*(): BOOLEAN;
		BEGIN RETURN (RealtimeFlag IN flags);
		END IsRealtime;

	END Type;

	(* basic types, defined in global name space *)
	BasicType*= OBJECT(Type)
	VAR name-: Identifier;

		PROCEDURE & InitBasicType( position: LONGINT; name: Identifier; flags: SET);
		BEGIN
			InitType(position, flags);
			SELF.name := name;
		END InitBasicType;

		PROCEDURE SetTypeDeclaration*(typeDeclaration: TypeDeclaration);
		BEGIN HALT(100);
		END SetTypeDeclaration;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitBasicType(SELF)
		END Accept;

	END BasicType;

	(** <<CHAR, CHAR8, CHAR16, CHAR32>>
		character types
	**)
	CharacterType*=OBJECT(BasicType)

		PROCEDURE & InitCharacterType( position: LONGINT; name: Identifier);
		BEGIN
			InitBasicType(position,name,{RealtimeFlag});
		END InitCharacterType;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitCharacterType(SELF)
		END Accept;

	END CharacterType;

	(* number types: IntegerType or FloatType *)
	NumberType*=OBJECT(BasicType)

		PROCEDURE & InitNumberType( position: LONGINT; name: Identifier);
		BEGIN
			InitBasicType(position,name,{RealtimeFlag});
		END InitNumberType;

	END NumberType;

	(** <<SHORTINT, INTEGER, LONGINT, HUGEINT>>
		integer types
	**)
	IntegerType*= OBJECT (NumberType)

		PROCEDURE & InitIntegerType( position: LONGINT; name: Identifier);
		BEGIN
			InitNumberType(position,name);
		END InitIntegerType;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitIntegerType(SELF)
		END Accept;

	END IntegerType;

	(** <<REAL,LONGREAL>>
		real types: REAL, LONGREAL
	**)
	FloatType*= OBJECT (NumberType)

		PROCEDURE & InitFloatType( position: LONGINT; name: Identifier);
		BEGIN
			InitNumberType(position,name);
		END InitFloatType;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitFloatType(SELF)
		END Accept;

	END FloatType;

	(** <<qualifiedIdentifier = resolved>>
		named reference to a type
	**)
	QualifiedType* = OBJECT (Type)
		VAR
			qualifiedIdentifier-: QualifiedIdentifier;

		PROCEDURE & InitQualifiedType( position: LONGINT; scope: Scope;  qualifiedIdentifier: QualifiedIdentifier);
		BEGIN
			ASSERT(qualifiedIdentifier # NIL);
			InitType( position, {});
			SELF.scope := scope;
			SELF.qualifiedIdentifier := qualifiedIdentifier;
			resolved := NIL;
		END InitQualifiedType;

		PROCEDURE SetResolved*(resolved: Type);
		BEGIN SELF.resolved := resolved
		END SetResolved;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitQualifiedType(SELF)
		END Accept;

	END QualifiedType;

	(** string literal type **)
	StringType*= OBJECT(Type)
	VAR
		length-: LONGINT;

		PROCEDURE & InitStringType(position: LONGINT;  length: LONGINT);
		BEGIN
			InitType(position, {RealtimeFlag});
			SELF.length := length;
		END InitStringType;

		PROCEDURE SetLength*(length: LONGINT);
		BEGIN SELF.length := length
		END SetLength;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitStringType(SELF)
		END Accept;

	END StringType;

	(** enumeration type of the form <<enum (base) red,green,blue end>> **)
	EnumerationType*=OBJECT(Type)
	VAR
		enumerationScope-: EnumerationScope;
		enumerationBase-: Type;
		rangeLowest-,rangeHighest-: LONGINT;

		PROCEDURE &InitEnumerationType(position: LONGINT; scope: Scope; enumerationScope: EnumerationScope);
		BEGIN
			InitType(position, {RealtimeFlag});
			SELF.scope := scope;
			enumerationBase := NIL;
			rangeLowest := 0; rangeHighest := 0;
			SELF.enumerationScope := enumerationScope;
			enumerationScope.ownerEnumeration := SELF;
		END InitEnumerationType;

		PROCEDURE SetEnumerationBase*(base: Type);
		BEGIN enumerationBase := base
		END SetEnumerationBase;

		PROCEDURE SetRange*(lowest,highest: LONGINT);
		BEGIN rangeLowest := lowest; rangeHighest := highest;
		END SetRange;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitEnumerationType(SELF)
		END Accept;

	END EnumerationType;

	(** type of expresions of the form <<from .. to BY by>> **)
	RangeType*=OBJECT(Type)
	VAR
		commonType-: Type;

		PROCEDURE & InitRangeType(position: LONGINT; scope: Scope; commonType: Type);
		BEGIN
			InitType(position, {RealtimeFlag});
			SetScope(scope);
			SELF.commonType := commonType;
		END InitRangeType;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitRangeType(SELF)
		END Accept;

	END RangeType;

	(** <<ARRAY [length] OF baseType>> *)
	ArrayType* = OBJECT (Type)
		VAR
			arrayBase-: Type;
			length-: Expression;
			staticLength-: LONGINT;
			form-: LONGINT; (* redundant: (form = Open) = (staticLength = 0) else (form = Static) *)

		PROCEDURE & InitArrayType(position: LONGINT; scope: Scope;  form: LONGINT);
		BEGIN
			length := NIL; arrayBase := NIL; InitType(position, {}); staticLength := 0; SELF.form := form; SELF.scope := scope;
		END InitArrayType;

		PROCEDURE SetArrayBase*( type: Type );
		BEGIN
			arrayBase := type;
		END SetArrayBase;

		PROCEDURE SetLength*(length: Expression);
		BEGIN
			SELF.length := length;
			IF (length.resolved # NIL) & (length.resolved IS IntegerValue) THEN
				staticLength := length.resolved(IntegerValue).value
			END;
		END SetLength;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitArrayType(SELF)
		END Accept;

		PROCEDURE Child*(nr: LONGINT):Type;
		BEGIN
			IF nr = 0 THEN RETURN SELF;
			ELSIF nr = 1 THEN RETURN arrayBase.resolved;
			ELSE RETURN arrayBase.resolved(ArrayType).Child(nr-1);
			END;
		END Child;

	END ArrayType;

	(** <<ARRAY '[' length | '*' | '?' ']' OF baseType>> **)
	MathArrayType* = OBJECT (Type)
		VAR
			arrayBase-: Type;
			length-: Expression;
			staticLength-: LONGINT;
			staticIncrementInBits-: LONGINT;
			form-: LONGINT;

		PROCEDURE & InitMathArrayType(position: LONGINT;scope: Scope; form: LONGINT);
		BEGIN
			length := NIL; arrayBase := NIL; InitType(position, {}); staticLength := 0; staticIncrementInBits := 0; SELF.form := form; SELF.scope := scope;
		END InitMathArrayType;

		PROCEDURE SetArrayBase*( type: Type );
		BEGIN
			arrayBase := type;
		END SetArrayBase;

		PROCEDURE SetLength*(length: Expression);
		BEGIN
			SELF.length := length;
			IF (length # NIL) & (length.resolved # NIL) & (length.resolved IS IntegerValue) THEN
				staticLength := length.resolved(IntegerValue).value;
				form := Static;
			ELSIF length = NIL THEN
				form := Open;
			END;
		END SetLength;

		PROCEDURE SetIncrement*(increment: LONGINT);
		BEGIN staticIncrementInBits := increment
		END SetIncrement;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitMathArrayType(SELF)
		END Accept;

	END MathArrayType;

	(** <<POINTER TO pointerBase>> **)
	PointerType* = OBJECT (Type)
		VAR
			flagList-: Modifier; (* set by the parser *)
			pointerBase-: Type;

		PROCEDURE & InitPointerType(position: LONGINT; scope: Scope);
		BEGIN
			flagList := NIL;
			pointerBase := NIL;
			InitType(position, {});
			SELF.scope := scope;
		END InitPointerType;

		PROCEDURE SetFlagList*(flags: Modifier);
		BEGIN flagList := flags
		END SetFlagList;

		PROCEDURE SetPointerBase*( type: Type );
		BEGIN
			pointerBase := type;
		END SetPointerBase;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitPointerType(SELF)
		END Accept;

	END PointerType;

	(** << (SENDER | RECEIVER) of channelType **)
	PortType* = OBJECT (Type)
		VAR
			channelType-: Type;
			direction-: LONGINT;

		PROCEDURE & InitPortType(position: LONGINT; direction: LONGINT; channelType: Type; scope: Scope);
		BEGIN
			InitType(position, {});
			SELF.channelType := channelType;
			SELF.direction := direction;
			SELF.scope := scope;
		END InitPortType;

		PROCEDURE SetChannelType*(type: Type);
		BEGIN channelType := type
		END SetChannelType;


		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitPortType(SELF)
		END Accept;

	END PortType;

	(** <<[pointerType = POINTER TO] RECORD (baseType) .. END>>
		| <<[OBJECT (baseType) .. END>>
	**)
	RecordType* = OBJECT (Type)
		VAR
			recordScope-:RecordScope;
			baseType-: Type;
			pointerType-: PointerType; (* for support of A = POINTER TO RECORD ... END and B = POINTER TO RECORD (A) END; *)
			isObject-,isProtected: BOOLEAN;
			sizeInBits-: LONGINT; (* allocation size of this type in bits *)

		PROCEDURE & InitRecordType( position: LONGINT; scope: Scope; recordScope: RecordScope);
		BEGIN
			InitType( position, {});
			SELF.scope := scope;
			baseType := NIL;
			pointerType := NIL;
			SELF.recordScope := recordScope;
			ASSERT(recordScope # NIL);
			ASSERT(recordScope.ownerRecord = NIL); (* cannot register twice ! *)
			recordScope.ownerRecord := SELF;
			isObject := FALSE; isProtected := FALSE;
			sizeInBits := MIN(LONGINT);
		END InitRecordType;

		PROCEDURE SetBaseType*( type: Type );
		BEGIN
			baseType := type;
		END SetBaseType;

		PROCEDURE SetSize*(sizeInBits: LONGINT);
		BEGIN SELF.sizeInBits := sizeInBits
		END SetSize;

		PROCEDURE SetPointerType*(pointerType: PointerType);
		BEGIN SELF.pointerType := pointerType
		END SetPointerType;

		PROCEDURE IsObject*(isObject: BOOLEAN);
		BEGIN SELF.isObject := isObject
		END IsObject;

		PROCEDURE IsProtected*(): BOOLEAN;
		VAR base: RecordType;
		BEGIN
			IF isProtected THEN RETURN TRUE END;
			base := GetBaseRecord();
			IF base # NIL THEN RETURN base.IsProtected() END;
			RETURN FALSE
		END IsProtected;

		PROCEDURE SetProtected*(protected: BOOLEAN);
		BEGIN SELF.isProtected := protected
		END SetProtected;

		PROCEDURE Level*():LONGINT;
		VAR type: RecordType; res: LONGINT;
		BEGIN
			type := SELF;
			res := 0;
			WHILE (type # NIL) & (type.baseType # NIL) DO
				INC(res);
				type := type.GetBaseRecord();
			END;
			RETURN res;
		END Level;

		PROCEDURE GetBaseRecord*():RecordType;
		BEGIN
			IF baseType = NIL THEN RETURN NIL; END;
			IF baseType.resolved IS RecordType THEN
				RETURN baseType.resolved(RecordType);
			ELSIF baseType.resolved IS PointerType THEN
				IF baseType.resolved(PointerType).pointerBase.resolved # NIL THEN
					RETURN baseType.resolved(PointerType).pointerBase.resolved(RecordType);
				END;
			END;
			RETURN NIL;
		END GetBaseRecord;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitRecordType(SELF)
		END Accept;

	END RecordType;

	ActorType*=OBJECT (Type)
	VAR
		firstParameter-,lastParameter-: Parameter; numberParameters-: LONGINT;  (* parameters *)
		actorScope-: Scope;

		PROCEDURE &InitActorType(position: LONGINT; scope, actorScope: Scope);
		BEGIN
			InitType(position,{});
			SELF.scope := scope;
			numberParameters := 0; firstParameter := NIL; lastParameter := NIL;
			SELF.actorScope := actorScope;
		END InitActorType;

		PROCEDURE AddParameter*(p: Parameter);
		BEGIN
			ASSERT(p # NIL);
			IF lastParameter= NIL THEN firstParameter := p ELSE lastParameter.nextParameter := p; p.prevParameter := lastParameter; END;
			lastParameter := p;
			INC(numberParameters);
		END AddParameter;

		PROCEDURE FindParameter*(identifier: Identifier): Parameter;
		VAR p: Parameter;
		BEGIN
			p := firstParameter;
			WHILE(p#NIL) & (p.name.name # identifier.name) DO p := p.nextParameter END;
			RETURN p;
		END FindParameter;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitActorType(SELF)
		END Accept;

	END ActorType;

	(** <<procedureType = PROCEDURE [{DELEGATE}] (firstParameter .. lastParameter): returnType>>
		also used as type for procedures
	**)
	ProcedureType* = OBJECT (Type)
		VAR
			flagList-: Modifier; (* set by the parser *)
			returnType-: Type;
			returnParameter-: Parameter;
			firstParameter-,lastParameter-: Parameter; numberParameters-, numberHiddenParameters-: LONGINT;  (* parameters *)

		PROCEDURE & InitProcedureType( position: LONGINT; scope: Scope);
		BEGIN
			InitType( position, {} );
			SELF.scope := scope;
			flagList := NIL;
			firstParameter := NIL; lastParameter := NIL; numberParameters := 0; numberHiddenParameters := 0;
			returnType := NIL; returnParameter := NIL;
			flags := {};
		END InitProcedureType;

		PROCEDURE HasFlag*(flag: LONGINT): BOOLEAN;
		BEGIN RETURN flag IN flags
		END HasFlag;

		PROCEDURE SetFlagList*(flags: Modifier);
		BEGIN flagList := flags
		END SetFlagList;

		PROCEDURE AddParameter*(p: Parameter);
		BEGIN
			ASSERT(p # NIL);
			IF lastParameter= NIL THEN firstParameter := p ELSE lastParameter.nextParameter := p; p.prevParameter := lastParameter; END;
			lastParameter := p;
			INC(numberParameters);
			IF p.access = {} THEN INC(numberHiddenParameters) ELSE ASSERT(numberHiddenParameters = 0) (* hidden parameters must occur at the end *) END;
		END AddParameter;

		PROCEDURE RevertParameters*;
		VAR this,next: Parameter; pnum: LONGINT;
		BEGIN
			pnum := numberParameters;
			IF lastParameter # NIL THEN
				this := lastParameter;
				lastParameter := NIL;
				firstParameter := NIL;
				numberParameters := 0;
				WHILE this # NIL DO
					next := this.prevParameter;
					this.prevParameter := NIL; this.nextParameter := NIL;
					AddParameter(this);
					this := next;
				END;
			END;
			ASSERT(pnum = numberParameters);
		END RevertParameters;

		PROCEDURE SetReturnType*( type: Type );
		BEGIN
			returnType := type;
		END SetReturnType;

		PROCEDURE SetReturnParameter*(parameter: Parameter);
		BEGIN
			returnParameter := parameter
		END SetReturnParameter;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitProcedureType(SELF)
		END Accept;

	END ProcedureType;

	(**** expressions ****)

	Expression* = OBJECT
		VAR
			type-: Type; (* the expression's type. Resolved by checker *)
			assignable-: BOOLEAN;  (* expression can be assigned to (or used as var-parameter): expression := ... *)
			position-,endposition-: LONGINT;
			state-: SET;
			resolved-: Value;


		PROCEDURE End*( position: LONGINT );
		BEGIN SELF.endposition := position;
		END End;

		PROCEDURE SetState*(state: LONGINT);
		BEGIN	INCL(SELF.state,state);
		END SetState;

		PROCEDURE &InitExpression(position: LONGINT);
		BEGIN	SELF.position := position; state := Undefined; type := NIL; assignable := FALSE; resolved := NIL;
		END InitExpression;

		PROCEDURE SetType*(type: Type);
		BEGIN
			SELF.type := type;
		END SetType;

		PROCEDURE SetResolved*(value: Value);
		BEGIN SELF.resolved := value
		END SetResolved;

		PROCEDURE SetAssignable*(assignable: BOOLEAN);
		BEGIN SELF.assignable := assignable
		END SetAssignable;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitExpression(SELF)
		END Accept;

	END Expression;

	(** <<expression, expression, ...>> **)
	ExpressionList* = OBJECT
		VAR list: Basic.List;

		PROCEDURE & InitList;
		BEGIN NEW( list );
		END InitList;

		PROCEDURE Length*( ): LONGINT;
		BEGIN RETURN list.Length();
		END Length;

		PROCEDURE AddExpression*( d: Expression );
		BEGIN list.Add(d)
		END AddExpression;

		PROCEDURE GetExpression*( index: LONGINT ): Expression;
		VAR p: ANY;
		BEGIN
			p := list.Get(index); RETURN p(Expression);
		END GetExpression;

		PROCEDURE SetExpression*(index: LONGINT; expression: Expression);
		BEGIN list.Set(index,expression)
		END SetExpression;

		PROCEDURE RemoveExpression*(i: LONGINT);
		BEGIN list.RemoveByIndex(i);
		END RemoveExpression;

		PROCEDURE Revert*;
		VAR i,j,last: LONGINT; ei,ej: ANY;
		BEGIN
			last := Length()-1;
			FOR i := 0 TO last DO
				j := last-i;
				ei := list.Get(i);
				ej := list.Get(j);
				list.Set(i,ej);
				list.Set(j,ei);
			END;
		END Revert;

	END ExpressionList;

	(** << {elements} >>  **)
	Set* = OBJECT (Expression)
		VAR elements-: ExpressionList; (* an element of the form from .. to is represented as a RangeExpression *)

		PROCEDURE & InitSet( position: LONGINT );
		BEGIN
			InitExpression( position );
			elements := NewExpressionList();
		END InitSet;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitSet(SELF)
		END Accept;

	END Set;

	(** << [elements] >>  **)
	MathArrayExpression* = OBJECT (Expression)
		VAR elements-: ExpressionList; (* an element of the form from .. to is represented as a RangeExpression *)

		PROCEDURE & InitMathArrayExpression( position: LONGINT );
		BEGIN
			InitExpression( position );
			elements := NewExpressionList();
		END InitMathArrayExpression;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitMathArrayExpression(SELF)
		END Accept;

	END MathArrayExpression;

	(** <<operator left>> **)
	UnaryExpression* = OBJECT (Expression)
		VAR
			left-: Expression;
			operator-: LONGINT;  (* one of Scanner.Minus ... Scanner.Not *)

		PROCEDURE & InitUnaryExpression( position: LONGINT;  operand: Expression;  operator: LONGINT );
		BEGIN
			InitExpression( position );  SELF.left := operand;  SELF.operator := operator;
		END InitUnaryExpression;

		PROCEDURE SetLeft*(left: Expression);
		BEGIN SELF.left := left
		END SetLeft;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitUnaryExpression(SELF)
		END Accept;

	END UnaryExpression;

	(** <<left operator right>> **)
	BinaryExpression* = OBJECT (Expression)
		VAR
			left-, right-: Expression;
			operator-: LONGINT;  (* one of Scanner.Equal ... Scanner.Minus *)

		PROCEDURE & InitBinaryExpression( position: LONGINT;  left, right: Expression;  operator: LONGINT );
		BEGIN
			InitExpression( position );  SELF.left := left;  SELF.right := right;  SELF.operator := operator;
		END InitBinaryExpression;

		PROCEDURE SetLeft*(left: Expression);
		BEGIN SELF.left := left
		END SetLeft;

		PROCEDURE SetRight*(right: Expression);
		BEGIN SELF.right := right
		END SetRight;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitBinaryExpression(SELF)
		END Accept;

	END BinaryExpression;


	(** <<from .. to BY by>> **)
	RangeExpression*= OBJECT (Expression)
	VAR
		from-,to-,by-: Expression;

		PROCEDURE &InitRangeExpression(position: LONGINT; from,to,by: Expression);
		BEGIN
			InitExpression(position);
			SELF.from := from; SELF.to := to; SELF.by := by;
		END InitRangeExpression;

		PROCEDURE SetFrom*(from: Expression);
		BEGIN SELF.from := from
		END SetFrom;

		PROCEDURE SetTo*(to: Expression);
		BEGIN SELF.to := to
		END SetTo;

		PROCEDURE SetBy*(from: Expression);
		BEGIN SELF.by := by
		END SetBy;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitRangeExpression(SELF)
		END Accept;

	END RangeExpression;

	(** << ? >> **)
	TensorRangeExpression*=OBJECT (Expression);

		PROCEDURE &InitTensorRangeExpression(position: LONGINT);
		BEGIN
			InitExpression(position);
		END InitTensorRangeExpression;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitTensorRangeExpression(SELF)
		END Accept;

	END TensorRangeExpression;



	(** convert expression from expression.type to Conversion.type **)
	Conversion* = OBJECT (Expression)
		VAR
			expression-: Expression;
			typeExpression-: Expression; (* for printout *)

		PROCEDURE & InitConversion( position: LONGINT;  expression: Expression; type: Type; typeExpression: Expression);
		BEGIN
			InitExpression( position );  SELF.expression := expression;  SELF.typeExpression := typeExpression; SELF.type := type;
		END InitConversion;

		PROCEDURE SetExpression*(expression: Expression);
		BEGIN SELF.expression := expression
		END SetExpression;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitConversion(SELF)
		END Accept;

	END Conversion;

	(**** designators ****)

	(** abstract **)
	Designator* = OBJECT(Expression)
		VAR
			left-: Expression; (* currently only designators are allowed but for later purposes ... (as for example (a+b).c) *)

		PROCEDURE &InitDesignator(position: LONGINT);
		BEGIN InitExpression(position);  left := NIL
		END InitDesignator;

		PROCEDURE SetLeft*(expression: Expression);
		BEGIN left := expression
		END SetLeft;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitDesignator(SELF)
		END Accept;

	END Designator;


	(*** first phase (parse time) designators ***)

	(** <<identifier>>
		may designate any symbol such as Variable, TypeDeclaration, Procedure
	**)
	IdentifierDesignator* = OBJECT(Designator)
		VAR identifier-: Identifier;

		PROCEDURE &InitIdentifierDesignator(position: LONGINT; id: Identifier);
		BEGIN InitDesignator(position); identifier := id
		END InitIdentifierDesignator;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitIdentifierDesignator(SELF)
		END Accept;

	END IdentifierDesignator;

	(** <<left.identifier>>
		may designate a record / module element (constant, type, variable, procedure)
	**)
	SelectorDesignator* = OBJECT (Designator)
		VAR identifier-: Identifier;

		PROCEDURE & InitSelector(position: LONGINT; left: Designator; identifier: Identifier);
		BEGIN   InitDesignator(position); SELF.left := left; SELF.identifier := identifier;
		END InitSelector;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitSelectorDesignator(SELF)
		END Accept;

	END SelectorDesignator;


	(** <<left(arg1, arg2, ...)>>
		may designate a function call or a type guard
	**)
	ParameterDesignator* = OBJECT(Designator)
		VAR parameters-: ExpressionList;

		PROCEDURE &InitParameterDesignator(position: LONGINT; left: Designator; parameters: ExpressionList);
		BEGIN InitDesignator(position); SELF.left := left; SELF.parameters := parameters
		END InitParameterDesignator;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitParameterDesignator(SELF)
		END Accept;

	END ParameterDesignator;


	(** <<left^>>
		may designate a pointer dereference or a method supercall
	**)
	ArrowDesignator* = OBJECT (Designator)

		PROCEDURE &InitArrowDesignator(position: LONGINT; left: Designator);
		BEGIN InitDesignator(position); SELF.left := left;
		END InitArrowDesignator;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitArrowDesignator(SELF)
		END Accept;

	END ArrowDesignator;

	(** <<left[parameters]>>
		designates an index designator
	**)
	BracketDesignator* = OBJECT(Designator)
		VAR parameters-: ExpressionList;

		PROCEDURE &InitBracketDesignator(position: LONGINT; left: Designator; parameters: ExpressionList);
		BEGIN InitDesignator(position); SELF.left := left; SELF.parameters := parameters;
		END InitBracketDesignator;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitBracketDesignator(SELF)
		END Accept;

	END BracketDesignator;

	(*** second phase (after checker) designators ***)

	(** symbol designator emerged from IdentifierDesignator or from Selector **)
	SymbolDesignator* = OBJECT(Designator)
	VAR
		symbol-: Symbol;

		PROCEDURE &InitSymbolDesignator(position: LONGINT; left: Designator; symbol: Symbol);
		BEGIN
			InitDesignator(position);
			SELF.left := left;
			SELF.symbol := symbol;
		END InitSymbolDesignator;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN
			position := SELF.position; v.VisitSymbolDesignator(SELF);
		END Accept;

		PROCEDURE SetSymbol*(s: Symbol);
		BEGIN SELF.symbol := s;
		END SetSymbol;

	END SymbolDesignator;

	(** <<left[parameters]>>
		(ranged) indexer
	**)
	IndexDesignator* = OBJECT(Designator)
		VAR
			parameters-: ExpressionList;
			hasRange-: BOOLEAN;

		PROCEDURE &InitIndexDesignator(position: LONGINT; left: Designator);
		BEGIN
			InitDesignator(position);
			SELF.left := left;
			parameters := NewExpressionList();
			hasRange := FALSE;
		END InitIndexDesignator;

		PROCEDURE HasRange*;
		BEGIN hasRange := TRUE;
		END HasRange;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitIndexDesignator(SELF)
		END Accept;

	END IndexDesignator;

	(** <<left(parameters)>>
		procedure call
	**)
	ProcedureCallDesignator*= OBJECT (Designator)
		VAR parameters-: ExpressionList;

		PROCEDURE & InitProcedureCallDesignator(position: LONGINT; left: Designator;  parameters: ExpressionList);
		BEGIN
			InitDesignator(position); SELF.left := left; SELF.parameters := parameters;
		END InitProcedureCallDesignator;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitProcedureCallDesignator(SELF)
		END Accept;

	END ProcedureCallDesignator;

	(** <<procedure(parameters)>>
		builtin procedure call **)
	BuiltinCallDesignator*= OBJECT (Designator) (*! should this be an extension of a procedure call designator ? *)
		VAR
			id-: LONGINT;
			parameters-: ExpressionList;
			hiddenVariable-: Designator; (* trick for new statement *)

		PROCEDURE & InitBuiltinCallDesignator(position: LONGINT; id: LONGINT; parameters: ExpressionList);
		BEGIN
			InitDesignator(position); SELF.parameters := parameters; SELF.id := id;hiddenVariable := NIL;
		END InitBuiltinCallDesignator;

		PROCEDURE SetHiddenVariable*(hidden: Designator);
		BEGIN SELF.hiddenVariable := hidden
		END SetHiddenVariable;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitBuiltinCallDesignator(SELF)
		END Accept;

	END BuiltinCallDesignator;

	(** <<left(type)>>
		resolved parameter designator, designates a type guard
	**)
	TypeGuardDesignator* = OBJECT(Designator)
	VAR
		typeExpression-: Expression; (* for printing only *)

		PROCEDURE &InitTypeGuardDesignator(position: LONGINT; left: Designator; type: Type);
		BEGIN InitDesignator(position); SELF.left := left; SELF.type := type; typeExpression := NIL;
		END InitTypeGuardDesignator;

		PROCEDURE SetTypeExpression*(typeExpression: Expression);
		BEGIN SELF.typeExpression := typeExpression
		END SetTypeExpression;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitTypeGuardDesignator(SELF)
		END Accept;

	END TypeGuardDesignator;

	(** <<left^>> resolved as dereference operation on pointer variable left **)
	DereferenceDesignator*= OBJECT (Designator)

		PROCEDURE &InitDereferenceDesignator(position: LONGINT; left: Designator);
		BEGIN InitDesignator(position); SELF.left := left;
		END InitDereferenceDesignator;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitDereferenceDesignator(SELF)
		END Accept;

	END DereferenceDesignator;

	(** <<left^>> resolved as supercall operation on method left **)
	SupercallDesignator*= OBJECT (Designator)

		PROCEDURE &InitSupercallDesignator(position: LONGINT; left: Designator);
		BEGIN InitDesignator(position); SELF.left := left;
		END InitSupercallDesignator;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitSupercallDesignator(SELF)
		END Accept;

	END SupercallDesignator;

	(**  <<SELF.x>> **)
	SelfDesignator*= OBJECT (Designator)

		PROCEDURE &InitSelfDesignator(position: LONGINT);
		BEGIN InitDesignator(position);
		END InitSelfDesignator;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitSelfDesignator(SELF)
		END Accept;

	END SelfDesignator;

	(**** values ****)

	Value* = OBJECT (Expression)
	VAR fingerprint-: Fingerprint;

		PROCEDURE &InitValue(position: LONGINT);
		BEGIN SELF.position := position; resolved := SELF; InitFingerprint(fingerprint);
		END InitValue;

		PROCEDURE SetFingerprint*(CONST fp: Fingerprint);
		BEGIN
			SELF.fingerprint := fp
		END SetFingerprint;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitValue(SELF)
		END Accept;

		PROCEDURE Equals*(v: Value):BOOLEAN;
		BEGIN HALT(100); (* abstract *) RETURN FALSE; END Equals;

	END Value;

	(** <<value = TRUE , FALSE>> **)
	BooleanValue* = OBJECT (Value)
		VAR
			value-: BOOLEAN;

		PROCEDURE & InitBooleanValue(position: LONGINT; value: BOOLEAN);
		BEGIN
			InitValue(position);  SELF.value := value;
		END InitBooleanValue;

		PROCEDURE SetValue*(value: BOOLEAN);
		BEGIN	SELF.value := value
		END SetValue;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitBooleanValue(SELF)
		END Accept;

		PROCEDURE Equals*(v: Value):BOOLEAN;
		BEGIN RETURN (v IS BooleanValue) & (v(BooleanValue).value = value); END Equals;

	END BooleanValue;

	(** <<value = 123456>> **)
	IntegerValue* = OBJECT (Value)
		VAR
			hvalue-: HUGEINT;
			value-: LONGINT;

		PROCEDURE & InitIntegerValue(position: LONGINT; hvalue: HUGEINT);
		BEGIN
			InitValue(position);  SELF.hvalue := hvalue; SELF.value := SHORT(hvalue);
		END InitIntegerValue;

		PROCEDURE SetValue*(hvalue: HUGEINT);
		BEGIN	SELF.hvalue := hvalue; SELF.value := SHORT(hvalue);
		END SetValue;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitIntegerValue(SELF)
		END Accept;

		PROCEDURE Equals*(v: Value):BOOLEAN;
		BEGIN RETURN (v IS IntegerValue) & (v(IntegerValue).value = value); END Equals;

	END IntegerValue;

	(** <<value =  'c',  65X>> **)
	CharacterValue*= OBJECT(Value)
		VAR
			value-: CHAR; (* potential for extension to support CHAR16 and CHAR32 *)

		PROCEDURE & InitCharacterValue(position:LONGINT; value: CHAR);
		BEGIN
			InitValue(position);  SELF.value := value;
		END InitCharacterValue;

		PROCEDURE SetValue*(value: CHAR);
		BEGIN	SELF.value := value
		END SetValue;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitCharacterValue(SELF)
		END Accept;

		PROCEDURE Equals*(v: Value):BOOLEAN;
		BEGIN RETURN (v IS CharacterValue) & (v(CharacterValue).value = value); END Equals;

	END CharacterValue;

	(** <<value =  {1,2,3..5}>> **)
	SetValue* = OBJECT (Value)
		VAR
			value-: SET;

		PROCEDURE & InitSetValue(position: LONGINT; value: SET);
		BEGIN
			InitValue(position);  SELF.value := value;
		END InitSetValue;

		PROCEDURE SetValue*(value: SET);
		BEGIN	SELF.value := value
		END SetValue;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitSetValue(SELF)
		END Accept;

	END SetValue;

		(** << [elements] >>  **)
	MathArrayValue* = OBJECT (Value)
		VAR array-: MathArrayExpression; (* an element of the form from .. to is represented as a RangeExpression *)

		PROCEDURE & InitMathArrayValue(position: LONGINT);
		BEGIN
			InitValue(position);
			array := NIL;
		END InitMathArrayValue;

		PROCEDURE SetArray*(array: MathArrayExpression);
		BEGIN SELF.array := array
		END SetArray;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitMathArrayValue(SELF)
		END Accept;

	END MathArrayValue;

	(** <<value = 1.2345E01>> **)
	RealValue* = OBJECT (Value)
		VAR
			value-: LONGREAL;
			subtype-: LONGINT; (* accuracy information: REAL vs. LONGREAL *)

		PROCEDURE & InitRealValue(position: LONGINT; value: LONGREAL);
		BEGIN
			InitValue(position);  SELF.value := value; SELF.subtype := 0;
		END InitRealValue;

		PROCEDURE SetValue*(value: LONGREAL);
		BEGIN	SELF.value := value
		END SetValue;

		PROCEDURE SetSubtype*(subtype: LONGINT);
		BEGIN SELF.subtype := subtype;
		END SetSubtype;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitRealValue(SELF)
		END Accept;

		PROCEDURE Equals*(v: Value):BOOLEAN;
		BEGIN RETURN (v IS RealValue) & (v(RealValue).value = value); END Equals;

	END RealValue;

	(** <<value = "string">> **)
	StringValue* = OBJECT (Value)
		VAR
			value-: Scanner.StringType;
			length-: LONGINT;

		PROCEDURE & InitStringValue(position: LONGINT; CONST value: ARRAY OF CHAR);
		BEGIN
			InitValue(position);  COPY(value,SELF.value);
			length := 0;
			WHILE (length<LEN(value)) & (value[length] # 0X) DO
				INC(length);
			END;
			IF length < LEN(value) THEN INC(length) END
		END InitStringValue;

		PROCEDURE SetValue*(CONST value: Scanner.StringType);
		BEGIN	SELF.value := value
		END SetValue;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitStringValue(SELF)
		END Accept;

		PROCEDURE Equals*(v: Value):BOOLEAN;
		BEGIN RETURN (v IS StringValue) & (v(StringValue).value = value); END Equals;

	END StringValue;

	(** <<value = NIL>> **)
	NilValue* = OBJECT (Value)

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitNilValue(SELF)
		END Accept;

		PROCEDURE Equals*(v: Value):BOOLEAN;
		BEGIN RETURN (v IS NilValue); END Equals;

	END NilValue;

	(** <<value = enum.x >> **)
	EnumerationValue* = OBJECT (Value)
	VAR
		value-: LONGINT;

		PROCEDURE & InitEnumerationValue(position: LONGINT; value: LONGINT);
		BEGIN
			InitValue(position);  SELF.value := value;
		END InitEnumerationValue;

		PROCEDURE SetValue*(value: LONGINT);
		BEGIN SELF.value := value
		END SetValue;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitEnumerationValue(SELF)
		END Accept;

		PROCEDURE Equals*(v: Value):BOOLEAN;
		BEGIN RETURN (v IS EnumerationValue) & (v(EnumerationValue).value = value); END Equals;

	END EnumerationValue;

	(**** symbols ****)

	Symbol*= OBJECT
	VAR
		nextSymbol-: Symbol;

		name-: Identifier; (* constant / variable / parameter / type name / module name *)
		access-,flags-: SET; (* access flags (exported, readonly etc.) *)
		type-: Type; (* type of constant / variable / parameter / procedure return type *)
		scope-:Scope; (* container of symbol *)
		offsetInBits-: LONGINT; (* offset in stack or heap, in bits *)

		position-: LONGINT; state-: SET;
		fingerprint-: Fingerprint;

		PROCEDURE & InitSymbol(position: LONGINT; name:Identifier);
		BEGIN
			SELF.position := position; state := Undefined;
			nextSymbol := NIL;
			SELF.name := name;
			scope:= NIL;
			type := NIL;
			access := Internal;
			state := Undefined;
			flags := {};
			offsetInBits := MIN(LONGINT);
			InitFingerprint(fingerprint);
		END InitSymbol;

		PROCEDURE SetFingerprint*(CONST fp: Fingerprint);
		BEGIN
			SELF.fingerprint := fp
		END SetFingerprint;

		PROCEDURE SetState*(state: LONGINT);
		BEGIN	INCL(SELF.state,state);
		END SetState;

		PROCEDURE SetScope*(scope: Scope);
		BEGIN	SELF.scope := scope
		END SetScope;

		PROCEDURE AddFlags*(flags: SET);
		BEGIN SELF.flags := SELF.flags + flags
		END AddFlags;

		PROCEDURE HasFlag*(flag: LONGINT): BOOLEAN;
		BEGIN RETURN flag IN flags
		END HasFlag;

		PROCEDURE SetType*(type: Type);
		BEGIN
			SELF.type := type;
		END SetType;

		PROCEDURE SetNext*(symbol: Symbol);
		BEGIN SELF.nextSymbol := symbol; END SetNext;

		PROCEDURE SetAccess*(access: SET);
		BEGIN
			(* consistency guarantee *)
			IF PublicWrite IN access THEN ASSERT(ProtectedWrite IN access)  END;
			IF ProtectedWrite IN access THEN ASSERT(InternalWrite IN access) END;
			IF PublicRead IN access THEN ASSERT(ProtectedRead IN access)  END;
			IF ProtectedRead IN access THEN ASSERT(InternalRead IN access)END;
			SELF.access := access;
		END SetAccess;

		PROCEDURE SetOffset*(ofs: LONGINT);
		BEGIN offsetInBits := ofs
		END SetOffset;

		PROCEDURE MarkUsed*;
		BEGIN
			INCL(flags, AccessedFlag);
		END MarkUsed;

		PROCEDURE MarkWritten*;
		BEGIN
			INCL(flags, WrittenFlag);
		END MarkWritten;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitSymbol(SELF)
		END Accept;

	END Symbol;

	(**
		<<TYPE name = declaredType>>
		TypeDeclaration symbol represents a type declaration of the form TYPE name  = declaredType.
		Note that the declared type is not stored in the symbol's type field but rather in the declaredType field.
		The type of a type declaration is set to "typeDeclarationType" in the semantic checker
	**)
	TypeDeclaration*= OBJECT(Symbol)
	VAR
		nextTypeDeclaration-: TypeDeclaration;
		declaredType-: Type;

		PROCEDURE &InitTypeDeclaration(position: LONGINT; name: Identifier);
		BEGIN
			InitSymbol(position,name);
			nextTypeDeclaration := NIL;
			declaredType := NIL;
			type := typeDeclarationType;
		END InitTypeDeclaration;

		PROCEDURE SetDeclaredType*(type: Type);
		BEGIN
			declaredType := type;
			IF ~(type IS BasicType) THEN
				type.typeDeclaration := SELF;
			END;
		END SetDeclaredType;

		PROCEDURE SetType*(type: Type);
		BEGIN
			ASSERT(type = typeDeclarationType);
		END SetType;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitTypeDeclaration(SELF)
		END Accept;

	END TypeDeclaration;


	(** <<CONST name = value >>
		Constant declaration symbol. Represents a constant being defined in the form CONST name  =  value
		The type of the constant is stored in the type field and is resolved by the semantic checker.
	**)
	Constant* = OBJECT (Symbol)
	VAR
		value-: Expression;
		nextConstant-: Constant;

		PROCEDURE & InitConstant( position: LONGINT;  name: Identifier );
		BEGIN
			InitSymbol(position,name);
			value := NIL;
			nextConstant := NIL;
		END InitConstant;

		PROCEDURE SetValue*( value: Expression );
		BEGIN
			SELF.value := value;
		END SetValue;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitConstant(SELF)
		END Accept;

	END Constant;

	(** <<VAR name: type >>
		Variable declaration symbol. Represents a variable defined in the form VAR name: Type.
		The type of the variable is stored in the symbol's type field and is resolved by the semantic checker.
	**)
	Variable* = OBJECT (Symbol)
	VAR
		nextVariable-: Variable;
		flagList-: Modifier;

		PROCEDURE & InitVariable( position: LONGINT;  name: Identifier);
		BEGIN
			InitSymbol(position,name);
			nextVariable := NIL;
			flagList := NIL;
		END InitVariable;

		PROCEDURE SetFlag*(flag: Modifier);
		BEGIN SELF.flagList := flag;
		END SetFlag;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitVariable(SELF)
		END Accept;

	END Variable;

	(** << [VAR | CONST] name: type >>
		Parameter declaration symbol. Represents a parameter in the form [VAR | CONST] name: Type.
		The parameter's type is stored in the symbol's type field and is resolved by the semantic checker.
	**)
	Parameter* = OBJECT (Symbol)
	VAR
		nextParameter-, prevParameter-: Parameter;
		flagList-: Modifier;

		kind-: LONGINT;   (* ValueParameter, ConstParameter, VarParameter *)
		ownerType-: Type;

		PROCEDURE & InitParameter( position: LONGINT;  ownerType: Type ; name: Identifier; kind: LONGINT);
		BEGIN
			InitSymbol( position, name );
			SELF.kind := kind;
			IF kind = ConstParameter THEN access := access * ReadOnly  END;
			nextParameter := NIL;
			SELF.ownerType := ownerType;
			flagList := NIL;
		END InitParameter;

		PROCEDURE SetFlag*(flag: Modifier);
		BEGIN SELF.flagList := flag;
		END SetFlag;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitParameter(SELF)
		END Accept;

		PROCEDURE SetKind*(kind: LONGINT);
		BEGIN SELF.kind := kind; END SetKind;

	END Parameter;


	(** Procedure declaration symbol. Represents a procedure being defined in the form PROCEDURE name(parameters): returnType;
		Note that the type of a procedure is a ProcedureType (and not the return type of the procedure).
		Parameters, local variables, constants and type declarations are stored in the procedureScope field.
	**)
	Procedure* = OBJECT (Symbol)
		VAR
			nextProcedure-: Procedure;
			procedureScope- : ProcedureScope;
			super-: Procedure;
			level-, methodNumber-: LONGINT;

		PROCEDURE & InitProcedure( position: LONGINT;  name: Identifier; scope: ProcedureScope);
		BEGIN
			InitSymbol(position,name);
			nextProcedure := NIL;
			procedureScope := scope;
			ASSERT(scope.ownerProcedure = NIL); (* cannot register twice ! *)
			scope.ownerProcedure := SELF;
			super := NIL;
			level := 0;
			methodNumber := -1;
		END InitProcedure;

		PROCEDURE SetSuper*(super: Procedure);
		BEGIN
			SELF.super := super
		END SetSuper;

		PROCEDURE SetLevel*(level: LONGINT);
		BEGIN SELF.level := level
		END SetLevel;

		PROCEDURE SetMethodNumber*(methodNumber: LONGINT);
		BEGIN SELF.methodNumber := methodNumber
		END SetMethodNumber;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitProcedure(SELF)
		END Accept;

	END Procedure;


	(** Builtin symbol stands for a builtin procedure. Is resolved by the semantic checker. **)
	Builtin* = OBJECT (Symbol)
	VAR
		nextBuiltin-: Builtin;
		id-: LONGINT;

		PROCEDURE & InitBuiltin(position: LONGINT; name:Identifier; id: LONGINT);
		BEGIN
			InitSymbol(position,name); SELF.id := id;
		END InitBuiltin;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitBuiltin(SELF)
		END Accept;

	END Builtin;

	Operator* = OBJECT (Procedure)
	VAR
		nextOperator-: Operator;

		PROCEDURE & InitOperator(position: LONGINT; name: Identifier; scope: ProcedureScope);
		BEGIN
			InitProcedure(position,name,scope);
			nextOperator := NIL;
		END InitOperator;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitOperator(SELF)
		END Accept;

	END Operator;

	Import* = OBJECT (Symbol)
		VAR
			nextImport-: Import;
			module-: Module;
			moduleName-: Identifier;
			context-: Identifier;
			direct-: BOOLEAN; (* direct import *)

		PROCEDURE & InitImport( position: LONGINT;  name, moduleName: Identifier; direct: BOOLEAN );
		BEGIN
			InitSymbol(position,name);
			SELF.direct := direct;
			module := NIL;
			context := NIL;
			SELF.moduleName := moduleName;
			type := importType;
		END InitImport;

		PROCEDURE SetType*(type: Type);
		BEGIN
			ASSERT(type = importType);
		END SetType;

		PROCEDURE SetModule*(module: Module);
		BEGIN
			SELF.module := module;
		END SetModule;

		PROCEDURE SetModuleName*(moduleName: Identifier);
		BEGIN SELF.moduleName := moduleName
		END SetModuleName;

		PROCEDURE SetContext*(context: Identifier);
		BEGIN
			SELF.context := context
		END SetContext;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitImport(SELF)
		END Accept;

	END Import;

	StatementSequence* = OBJECT
		VAR
			list: Basic.List;

		PROCEDURE & InitList;
		BEGIN NEW( list );
		END InitList;

		PROCEDURE Length*( ): LONGINT;
		BEGIN RETURN list.Length();
		END Length;

		PROCEDURE AddStatement*( statement: Statement);
		BEGIN list.Add( statement );
		END AddStatement;

		PROCEDURE PrependStatement*( statement: Statement);
		BEGIN list.Prepend( statement );
		END PrependStatement;

		PROCEDURE HasStatement*( statement: Statement):BOOLEAN;
		BEGIN RETURN list.Contains(statement);
		END HasStatement;

		PROCEDURE GetStatement*( index: LONGINT ): Statement;
		VAR p: ANY;
		BEGIN p := list.Get( index );  RETURN p( Statement );
		END GetStatement;

		PROCEDURE SetStatement*(index: LONGINT; statement: Statement);
		BEGIN
			list.Set(index,statement);
		END SetStatement;

		PROCEDURE RemoveStatement*(statement: Statement);
		BEGIN
			list.Remove(statement);
		END RemoveStatement;

		PROCEDURE InsertBefore*(search, new: Statement);
		BEGIN
			list.Insert(list.IndexOf(search), new);
		END InsertBefore;

	END StatementSequence;

	(**** statements ****)

	Statement*= OBJECT
	VAR outer-: Statement;
		position-: LONGINT;
		flags-: SET;

		PROCEDURE & InitStatement(position: LONGINT; outer: Statement);
		BEGIN
			SELF.position := position;
			SELF.outer := outer;
			flags := {};
		END InitStatement;

		PROCEDURE AddFlags*(flags: SET);
		BEGIN SELF.flags := SELF.flags + flags
		END AddFlags;

		PROCEDURE HasFlag*(flag: LONGINT): BOOLEAN;
		BEGIN RETURN flag IN flags
		END HasFlag;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitStatement(SELF)
		END Accept;

	END Statement;

	(** << call(...) >> **)
	ProcedureCallStatement*= OBJECT(Statement)
		VAR call-: Designator;

		PROCEDURE & InitProcedureCallStatement(position: LONGINT; call: Designator; outer: Statement);
		BEGIN	InitStatement(position,outer); SELF.call := call;
		END InitProcedureCallStatement;

		PROCEDURE SetCall*(call: Designator);
		BEGIN	SELF.call := call;
		END SetCall;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitProcedureCallStatement(SELF)
		END Accept;

	END ProcedureCallStatement;

	(** << left := right >> **)
	Assignment* = OBJECT (Statement)
	VAR left-: Designator; right-: Expression;

		PROCEDURE & InitAssignment( position: LONGINT;  left: Designator;  right: Expression; outer: Statement );
		BEGIN
			InitStatement( position,outer );  SELF.left := left;  SELF.right := right;
		END InitAssignment;

		PROCEDURE SetLeft*(left: Designator);
		BEGIN SELF.left := left
		END SetLeft;

		PROCEDURE SetRight*(right: Expression);
		BEGIN SELF.right := right
		END SetRight;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitAssignment(SELF)
		END Accept;

	END Assignment;

	(** << ... condition THEN statements ... >> **)
	IfPart*= OBJECT
	VAR
		condition-: Expression;
	 	statements-: StatementSequence;

	 	PROCEDURE & InitIfPart;
	 	BEGIN
	 		statements := NIL; condition := NIL;
	 	END InitIfPart;

	 	PROCEDURE SetCondition*(condition: Expression);
	 	BEGIN SELF.condition := condition
	 	END SetCondition;

	 	PROCEDURE SetStatements*(statements: StatementSequence);
	 	BEGIN SELF.statements := statements
	 	END SetStatements;

	 END IfPart;

	(** << IF ifPart {ELSIF elsifParts} ELSE elseParts >> **)
	IfStatement* = OBJECT (Statement)
		VAR
			ifPart-: IfPart;
			elsifParts: Basic.List;
			elsePart-: StatementSequence;

		PROCEDURE & InitIfStatement( position: LONGINT ; outer: Statement);
		BEGIN
			InitStatement( position,outer ); ifPart := NewIfPart(); elsePart := NIL;  elsifParts := NIL;
		END InitIfStatement;

		PROCEDURE SetElsePart*( elsePart: StatementSequence );
		BEGIN
			SELF.elsePart := elsePart;
		END SetElsePart;

		PROCEDURE AddElsifPart*( elsifPart: IfPart );
		BEGIN
			IF elsifParts = NIL THEN NEW(elsifParts);  END;
			elsifParts.Add( elsifPart );
		END AddElsifPart;

		PROCEDURE GetElsifPart*( i: LONGINT ): IfPart;
		VAR a: ANY;
		BEGIN a := elsifParts.Get( i );  RETURN a( IfPart )
		END GetElsifPart;

		PROCEDURE ElsifParts*( ): LONGINT;
		BEGIN
			IF elsifParts = NIL THEN RETURN 0 ELSE RETURN elsifParts.Length();  END;
		END ElsifParts;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitIfStatement(SELF)
		END Accept;

	END IfStatement;

	(** << WITH variable : type DO statements END >> **)
	WithStatement* = OBJECT (Statement)
		VAR
			variable-: Designator;
			type-: Designator;
			statements-: StatementSequence;

		PROCEDURE & InitWithStatement( position: LONGINT; outer: Statement );
		BEGIN
			InitStatement( position,outer );
		END InitWithStatement;

		PROCEDURE SetVariable*( variable: Designator);
		BEGIN
			SELF.variable := variable
		END SetVariable;

		PROCEDURE SetType*( type: Designator );
		BEGIN
			SELF.type := type
		END SetType;

		PROCEDURE SetStatements*( statements: StatementSequence );
		BEGIN
			SELF.statements := statements;
		END SetStatements;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitWithStatement(SELF)
		END Accept;

	END WithStatement;


	CaseConstant*= POINTER TO RECORD min*,max*: LONGINT; next*: CaseConstant END;

	(** << elements : statements >> **)
	CasePart* = OBJECT
		VAR
			elements-: ExpressionList; (* expression list inserted by the parser *)
			firstConstant-: CaseConstant; (* expression list resolved to int32s, inserted by checker *)
			statements-: StatementSequence;

		PROCEDURE & InitCasePart;
		BEGIN
			elements := NewExpressionList(); firstConstant := NIL;
		END InitCasePart;

		PROCEDURE SetStatements*( statements: StatementSequence );
		BEGIN
			SELF.statements := statements;
		END SetStatements;

		PROCEDURE SetConstants*(firstConstant: CaseConstant);
		BEGIN SELF.firstConstant := firstConstant
		END SetConstants;

	END CasePart;

	(** << CASE varaible OF caseParts ELSE elsePart >> **)
	CaseStatement* = OBJECT (Statement)
		VAR
			variable-: Expression;
			elsePart-: StatementSequence;
			caseParts-: Basic.List;
			min-,max-: LONGINT;

		PROCEDURE & InitCaseStatement( position: LONGINT ; outer: Statement);
		BEGIN
			InitStatement(position,outer );  variable := NIL;  elsePart := NIL;  caseParts := NIL;
			min := MAX(LONGINT); max := MIN(LONGINT);
		END InitCaseStatement;

		PROCEDURE SetVariable*( expression: Expression );
		BEGIN SELF.variable := expression;
		END SetVariable;

		PROCEDURE SetElsePart*( elsePart: StatementSequence );
		BEGIN SELF.elsePart := elsePart;
		END SetElsePart;

		PROCEDURE AddCasePart*( casePart: CasePart );
		BEGIN
			IF caseParts = NIL THEN NEW(caseParts);  END;
			caseParts.Add( casePart );
		END AddCasePart;

		PROCEDURE GetCasePart*( i: LONGINT ): CasePart;
		VAR a: ANY;
		BEGIN a := caseParts.Get( i );  RETURN a( CasePart )
		END GetCasePart;

		PROCEDURE CaseParts*( ): LONGINT;
		BEGIN
			IF caseParts = NIL THEN RETURN 0 ELSE RETURN caseParts.Length();  END;
		END CaseParts;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitCaseStatement(SELF)
		END Accept;

		PROCEDURE MaxConstant*(): LONGINT;
		VAR val,i: LONGINT; part: CasePart; const: CaseConstant;
		BEGIN
			val := -1;
			FOR i := 0 TO CaseParts() - 1 DO
				part := GetCasePart(i);
				const := part.firstConstant;
				WHILE(const # NIL) DO
					IF const.max > val THEN val := const.max; END;
					const := const.next;
				END;
			END;
			RETURN val;
		END MaxConstant;

		PROCEDURE SetMinMax*(min,max: LONGINT);
		BEGIN
			SELF.min := min; SELF.max := max;
		END SetMinMax;


	END CaseStatement;

	(** << WHILE condition DO statements END >> **)
	WhileStatement* = OBJECT (Statement)
		VAR
			condition-: Expression;
			statements-: StatementSequence;

		PROCEDURE & InitWhileStatement( position: LONGINT ; outer: Statement);
		BEGIN
			InitStatement( position,outer );  condition := NIL;  statements := NIL;
		END InitWhileStatement;

		PROCEDURE SetCondition*( condition: Expression );
		BEGIN
			SELF.condition := condition
		END SetCondition;

		PROCEDURE SetStatements*( statements: StatementSequence );
		BEGIN
			SELF.statements := statements;
		END SetStatements;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitWhileStatement(SELF)
		END Accept;

	END WhileStatement;

	(** << REPEAT statements UNTIL condition >> **)
	RepeatStatement* = OBJECT (Statement)
		VAR
			condition-: Expression;
			statements-: StatementSequence;

		PROCEDURE & InitRepeatStatement( position: LONGINT; outer: Statement );
		BEGIN
			InitStatement( position,outer );  condition := NIL;  statements := NIL;
		END InitRepeatStatement;

		PROCEDURE SetCondition*( condition: Expression );
		BEGIN
			SELF.condition := condition
		END SetCondition;

		PROCEDURE SetStatements*( statements: StatementSequence );
		BEGIN
			SELF.statements := statements;
		END SetStatements;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitRepeatStatement(SELF)
		END Accept;

	END RepeatStatement;

	(** << FOR variable := from TO to BY by DO statements END >> **)
	ForStatement* = OBJECT (Statement)
		VAR
			variable-,temporary-: Designator;
			from-, to-, by-: Expression;
			statements-: StatementSequence;

		PROCEDURE & InitForStatement( position: LONGINT; outer: Statement );
		BEGIN
			InitStatement( position,outer );  variable := NIL; temporary := NIL;  from := NIL;  to := NIL;  by := NIL; statements := NIL;
		END InitForStatement;

		PROCEDURE SetVariable*( variable: Designator);
		BEGIN
			SELF.variable := variable
		END SetVariable;

		PROCEDURE SetFrom*( from: Expression );
		BEGIN
			SELF.from := from
		END SetFrom;

		PROCEDURE SetTo*( to: Expression );
		BEGIN
			SELF.to := to
		END SetTo;

		PROCEDURE SetTemporary*(temporary: Designator);
		BEGIN SELF.temporary := temporary;
		END SetTemporary;


		PROCEDURE SetBy*( by: Expression );
		BEGIN SELF.by := by
		END SetBy;

		PROCEDURE SetStatements*( statements: StatementSequence );
		BEGIN SELF.statements := statements;
		END SetStatements;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitForStatement(SELF)
		END Accept;

	END ForStatement;

	(** << LOOP statements END >> **)
	LoopStatement* = OBJECT (Statement)
		VAR statements-: StatementSequence;

		PROCEDURE & InitLoopStatement( position: LONGINT ; outer: Statement);
		BEGIN
			InitStatement( position ,outer);  statements := NIL;
		END InitLoopStatement;

		PROCEDURE SetStatements*( statements: StatementSequence );
		BEGIN SELF.statements := statements;
		END SetStatements;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitLoopStatement(SELF)
		END Accept;

	END LoopStatement;

	(** << EXIT >> **)
	ExitStatement* = OBJECT (Statement)

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitExitStatement(SELF)
		END Accept;

	END ExitStatement;

	(** << RETURN returnValue >> **)
	ReturnStatement* = OBJECT (Statement)
		VAR returnValue-: Expression; (* strictly speaking this is not a value but this term is in common use here *)

		PROCEDURE & InitReturnStatement( position: LONGINT ; outer: Statement);
		BEGIN
			InitStatement( position,outer );  returnValue := NIL
		END InitReturnStatement;

		PROCEDURE SetReturnValue*( returnValue: Expression );
		BEGIN SELF.returnValue := returnValue
		END SetReturnValue;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitReturnStatement(SELF)
		END Accept;

	END ReturnStatement;

	(** << AWAIT condition >> **)
	AwaitStatement* = OBJECT (Statement)
		VAR condition-: Expression;

		PROCEDURE & InitAwaitStatement( position: LONGINT; outer: Statement );
		BEGIN
			InitStatement( position,outer );  condition := NIL
		END InitAwaitStatement;

		PROCEDURE SetCondition*( condition: Expression );
		BEGIN SELF.condition := condition
		END SetCondition;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitAwaitStatement(SELF)
		END Accept;

	END AwaitStatement;

	(* << Identifier ( Expression) >> *)
	Modifier*= OBJECT
	VAR identifier-: Identifier; expression-: Expression; nextModifier-: Modifier;

		PROCEDURE & InitModifier(identifier: Identifier; expression: Expression);
		BEGIN
			SELF.identifier := identifier; SELF.expression := expression; nextModifier := NIL;
		END InitModifier;

		PROCEDURE SetNext*(modifier: Modifier);
		BEGIN	nextModifier := modifier
		END SetNext;

	END Modifier;

	(** << BEGIN {Modifier, Modifier ... }  statements END >> **)
	StatementBlock* = OBJECT (Statement)
		VAR
			statements-: StatementSequence;
			blockModifiers-: Modifier;

		PROCEDURE & InitStatementBlock( position: LONGINT ; outer: Statement);
		BEGIN
			InitStatement( position ,outer);  statements := NIL;  blockModifiers := NIL;
		END InitStatementBlock;

		PROCEDURE SetModifier*(modifier: Modifier);
		BEGIN
			blockModifiers := modifier;
		END SetModifier;

		PROCEDURE SetStatementSequence*( statements: StatementSequence );
		BEGIN SELF.statements := statements;
		END SetStatementSequence;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitStatementBlock(SELF)
		END Accept;

	END StatementBlock;


	(** << CODE {flags} {character}  END >> **)
	Code*= OBJECT(Statement)
	VAR
		sourceCode-: SourceCode; sourceCodeLength-: LONGINT;
		inlineCode-: BinaryCode;

		PROCEDURE & InitCode(position: LONGINT; outer: Statement);
		BEGIN
			InitStatement(position,outer);
			inlineCode := NIL;
			sourceCode := NIL; sourceCodeLength := 0;
		END InitCode;

		PROCEDURE SetSourceCode*(source: SourceCode; length: LONGINT);
		BEGIN sourceCode := source; sourceCodeLength := length;
			ASSERT(sourceCodeLength <= LEN(source));
		END SetSourceCode;

		PROCEDURE SetBinaryCode*(code: BinaryCode);
		BEGIN
			inlineCode := code;
		END SetBinaryCode;

		PROCEDURE Accept*(v: Visitor);
		VAR position: LONGINT;
		BEGIN position := SELF.position; v.VisitCode(SELF)
		END Accept;

	END Code;

	(** << BEGIN {flags} statements FINALLY statements END >> **)
	Body*= OBJECT(StatementBlock)
	VAR
		finally-: StatementSequence;
		priority-: Expression; (* set by checker *)
		fixed-: BOOLEAN;
		alignment-: LONGINT; (* set by checker *)
		inScope-: ProcedureScope;
		code-: Code;

		PROCEDURE & InitBody(position: LONGINT; scope: ProcedureScope);
		BEGIN
			InitStatementBlock(position,NIL); finally := NIL; priority := NIL; inScope := scope; code := NIL;
			alignment := 0; fixed :=FALSE;
		END InitBody;

		PROCEDURE SetFinally*( finally: StatementSequence );
		BEGIN SELF.finally := finally
		END SetFinally;

		PROCEDURE SetPriority*(expression: Expression);
		BEGIN priority := expression
		END SetPriority;

		PROCEDURE SetAlignment*(fix: BOOLEAN; alignAt: LONGINT);
		BEGIN
			SELF.fixed := fix; alignment := alignAt;
		END SetAlignment;

		PROCEDURE SetCode*(code: Code);
		BEGIN SELF.code := code;
		END SetCode;

	END Body;

	(** (* comment *) **)
	Comment*=OBJECT
	VAR position-: LONGINT;
		source-: Scanner.SourceString; (* currently: POINTER TO ARRAY OF CHAR *)
		scope-: Scope;
		prevSymbol-,nextSymbol-: Symbol;
		nextComment-: Comment;

		PROCEDURE & InitComment(pos: LONGINT; scope: Scope; CONST s: ARRAY OF CHAR; length: LONGINT);
		VAR i: LONGINT;
		BEGIN
			SELF.scope := scope;
			NEW(source,length);
			FOR i := 0 TO length-1 DO
				source[i] := s[i];
			END;
			SELF.position := pos;
			nextComment := NIL;
			prevSymbol := NIL;
			nextSymbol := NIL;
		END InitComment;

		PROCEDURE SetPreviousSymbol*(symbol: Symbol);
		BEGIN
			prevSymbol := symbol
		END SetPreviousSymbol;

		PROCEDURE SetNextSymbol*(symbol: Symbol);
		BEGIN
			nextSymbol := symbol
		END SetNextSymbol;


	END Comment;


	(**** building blocks ****)

	Scope*=OBJECT
		VAR
		firstSymbol-: Symbol; numberSymbols-: LONGINT; (* all symbols in scope (sorted) *)

		firstConstant-,lastConstant-: Constant;  numberConstants-: LONGINT; (* constants *)
		firstTypeDeclaration-,lastTypeDeclaration-: TypeDeclaration; numberTypeDeclarations-: LONGINT; (* type declarations *)
		firstVariable-,lastVariable-: Variable; numberVariables-: LONGINT;  (* variables *)
		firstProcedure-,lastProcedure-: Procedure; numberProcedures-: LONGINT;  (* procedures *)

		outerScope-: Scope; nextScope-: Scope;

		ownerModule-: Module;


		PROCEDURE & InitScope(outer: Scope);
		BEGIN
			firstSymbol := NIL; numberSymbols := 0;
			firstConstant := NIL; lastConstant := NIL; numberConstants := 0;
			firstTypeDeclaration := NIL; lastTypeDeclaration := NIL; numberTypeDeclarations := 0;
			firstVariable := NIL; lastVariable := NIL; numberVariables := 0;
			firstProcedure := NIL; lastProcedure := NIL; numberProcedures := 0;
			outerScope := outer;
			IF outer # NIL THEN
				ownerModule := outer.ownerModule
			ELSE
				ownerModule := NIL;
			END;
			nextScope := NIL;
		END InitScope;

		(** Enter a symbol in the scope, aplhabetically sorted, duplicate = TRUE if multiply identifier *)
		PROCEDURE EnterSymbol*(symbol: Symbol; VAR duplicate: BOOLEAN);
		VAR p,q: Symbol; name,nextname: Scanner.StringType;
		BEGIN
			ASSERT(symbol.nextSymbol = NIL,101); (* symbol may only be present in one scope at a time ! *)
			ASSERT(symbol.scope = NIL,102);
			ASSERT(symbol.name # NIL,103);

			p := firstSymbol; q := NIL;
			WHILE (p # NIL) & (StringPool.CompareString(p.name.name,symbol.name.name)<0) DO q := p; p := p.nextSymbol END;
			IF (p#NIL) & (symbol.name.name = p.name.name) THEN
				duplicate := TRUE;
			ELSE
				duplicate := FALSE
			END;
			symbol.nextSymbol := p;
			IF q = NIL THEN firstSymbol := symbol ELSE q.nextSymbol := symbol END;
			symbol.SetScope(SELF);

			p := firstSymbol;
			WHILE(p.nextSymbol # NIL) DO
				p.nextSymbol.name.GetString(nextname);
				p.name.GetString(name);
				ASSERT(nextname >= name);
				p := p.nextSymbol;
			END;

			INC(numberSymbols);
		END EnterSymbol;

		(** Find symbol by name *)
		PROCEDURE FindSymbol*(identifier: Identifier): Symbol;
		VAR p: Symbol;
		BEGIN
			IF identifier # NIL THEN
				p := firstSymbol;
				WHILE(p#NIL) & ((p.name.name # identifier.name) OR (p IS Operator)) DO p := p.nextSymbol END;
			END;
			RETURN p;
		END FindSymbol;

		PROCEDURE AddConstant*(c: Constant);
		BEGIN
			ASSERT(c # NIL);
			IF lastConstant= NIL THEN firstConstant := c ELSE lastConstant.nextConstant := c END;
			lastConstant := c;
			INC(numberConstants);
		END AddConstant;

		PROCEDURE FindConstant*(identifier: Identifier): Constant;
		VAR p: Constant;
		BEGIN
			p := firstConstant;
			WHILE(p#NIL) & (p.name.name # identifier.name) DO p := p.nextConstant END;
			RETURN p;
		END FindConstant;

		PROCEDURE AddTypeDeclaration*(t: TypeDeclaration);
		BEGIN
			ASSERT(t # NIL);
			IF lastTypeDeclaration= NIL THEN firstTypeDeclaration := t ELSE lastTypeDeclaration.nextTypeDeclaration := t END;
			INC(numberTypeDeclarations);
			lastTypeDeclaration := t;
		END AddTypeDeclaration;

		PROCEDURE FindTypeDeclaration*(identifier: Identifier): TypeDeclaration;
		VAR p: TypeDeclaration;
		BEGIN
			p := firstTypeDeclaration;
			WHILE(p#NIL) & (p.name.name # identifier.name) DO p := p.nextTypeDeclaration END;
			RETURN p;
		END FindTypeDeclaration;

		PROCEDURE AddVariable*(v: Variable);
		BEGIN
			ASSERT(v # NIL);
			IF lastVariable= NIL THEN firstVariable := v ELSE lastVariable.nextVariable := v END;
			INC(numberVariables);
			lastVariable := v;
		END AddVariable;

		PROCEDURE FindVariable*(identifier: Identifier): Variable;
		VAR p: Variable;
		BEGIN
			p := firstVariable;
			WHILE(p#NIL) & (p.name.name # identifier.name) DO p := p.nextVariable END;
			RETURN p;
		END FindVariable;

		PROCEDURE AddProcedure*(p: Procedure);
		BEGIN
			ASSERT(p # NIL);
			IF lastProcedure= NIL THEN firstProcedure := p ELSE lastProcedure.nextProcedure := p END;
			INC(numberProcedures);
			lastProcedure := p;
		END AddProcedure;

		PROCEDURE FindProcedure*(identifier: Identifier): Procedure;
		VAR p: Procedure;
		BEGIN
			p := firstProcedure;
			WHILE (p#NIL) & ((p.name.name # identifier.name) OR (p IS Operator)) DO p := p.nextProcedure END;
			RETURN p;
		END FindProcedure;

		PROCEDURE FindMethod*(number: LONGINT): Procedure;
		VAR p: Procedure;
		BEGIN
			p := firstProcedure;
			WHILE (p# NIL) & (p.methodNumber # number) DO
				p := p.nextProcedure
			END;
			RETURN p;
		END FindMethod;


		PROCEDURE Level*(): LONGINT;
		VAR scope: Scope; level: LONGINT;
		BEGIN
			level := 0;
			scope := SELF;
			WHILE(scope.outerScope # NIL) DO
				scope := scope.outerScope;
				INC(level);
			END;
			RETURN level;
		END Level;

	END Scope;

	ProcedureScope*=OBJECT (Scope)
		VAR
		ownerProcedure-: Procedure;
		body-: Body;

		PROCEDURE & InitProcedureScope(outer: Scope);
		BEGIN
			InitScope(outer);
			ownerProcedure := NIL;
			body := NIL;
		END InitProcedureScope;

		PROCEDURE SetBody*(body: Body);
		BEGIN
			SELF.body := body;
		END SetBody;

	END ProcedureScope;


	EnumerationScope*= OBJECT(Scope)
	VAR
		ownerEnumeration-: EnumerationType;

		(** Find symbol by name *)
		PROCEDURE FindSymbol*(identifier: Identifier): Symbol;
		VAR p: Symbol; base: Type;
		BEGIN
			p := FindSymbol^(identifier);
			IF p = NIL THEN
				base := ownerEnumeration.enumerationBase;
				IF (base # NIL) & (base.resolved IS EnumerationType) THEN
					p := base.resolved(EnumerationType).enumerationScope.FindSymbol(identifier)
				END;
			END;
			RETURN p;
		END FindSymbol;

		PROCEDURE &InitEnumerationScope(outer: Scope);
		BEGIN
			InitScope(outer);
			ownerEnumeration := NIL; (* must be set by EnumerationType *)
		END InitEnumerationScope;

	END EnumerationScope;

	RecordScope*= OBJECT(Scope)
		VAR
			ownerRecord-: RecordType;
			bodyProcedure-: Procedure;
			constructor-: Procedure;
			numberMethods-: LONGINT;
			firstParameter-,lastParameter-: Parameter; numberParameters-: LONGINT;  (* parameters for dataflow programming*)

		PROCEDURE & InitRecordScope(outer: Scope);
		BEGIN
			InitScope(outer);
			ownerRecord := NIL;
			numberMethods := 0;
			bodyProcedure := NIL;
			constructor := NIL;
		END InitRecordScope;

		PROCEDURE SetBodyProcedure*(body: Procedure);
		BEGIN SELF.bodyProcedure := body;
		END SetBodyProcedure;

		PROCEDURE SetConstructor*(body: Procedure);
		BEGIN SELF.constructor := body
		END SetConstructor;

		PROCEDURE SetNumberMethods*(numberMethods: LONGINT);
		BEGIN SELF.numberMethods := numberMethods;
		END SetNumberMethods;

		(** Find symbol by name *)
		PROCEDURE FindSymbol*(identifier: Identifier): Symbol;
		VAR p: Symbol; base: RecordType;
		BEGIN
			p := FindSymbol^(identifier);
			IF p = NIL THEN
				base := ownerRecord.GetBaseRecord();
				IF (base # NIL) THEN
					p := base.recordScope.FindSymbol(identifier)
				END;
			END;
			RETURN p;
		END FindSymbol;

		PROCEDURE FindConstant*(identifier: Identifier): Constant;
		VAR p: Constant; base: RecordType;
		BEGIN
			p := FindConstant^(identifier);
			IF p = NIL THEN
				base := ownerRecord.GetBaseRecord();
				IF (base # NIL) THEN
					p := base.recordScope.FindConstant(identifier)
				END;
			END;
			RETURN p;
		END FindConstant;

		PROCEDURE FindTypeDeclaration*(identifier: Identifier): TypeDeclaration;
		VAR p: TypeDeclaration; base: RecordType;
		BEGIN
			p := FindTypeDeclaration^(identifier);
			IF p = NIL THEN
				base := ownerRecord.GetBaseRecord();
				IF (base # NIL) THEN
					p := base.recordScope.FindTypeDeclaration(identifier)
				END;
			END;
			RETURN p;
		END FindTypeDeclaration;

		PROCEDURE FindVariable*(identifier: Identifier): Variable;
		VAR p: Variable; base: RecordType;
		BEGIN
			p := FindVariable^(identifier);
			IF p = NIL THEN
				base := ownerRecord.GetBaseRecord();
				IF (base # NIL) THEN
					p := base.recordScope.FindVariable(identifier)
				END;
			END;
			RETURN p;
		END FindVariable;

		PROCEDURE FindProcedure*(identifier: Identifier): Procedure;
		VAR p: Procedure; base: RecordType;
		BEGIN
			p := FindProcedure^(identifier);
			IF p = NIL THEN
				base := ownerRecord.GetBaseRecord();
				IF (base # NIL) THEN
					p := base.recordScope.FindProcedure(identifier)
				END;
			END;
			RETURN p;
		END FindProcedure;

		PROCEDURE FindMethod*(number: LONGINT): Procedure;
		VAR p: Procedure; base: RecordType;
		BEGIN
			p := FindMethod^(number);
			IF p = NIL THEN
				base := ownerRecord.GetBaseRecord();
				IF (base # NIL) THEN
					p := base.recordScope.FindMethod(number)
				END;
			END;
			RETURN p;
		END FindMethod;

	END RecordScope;

	ActorScope*=OBJECT (Scope)
		VAR
		ownerActor-: ActorType;
		bodyProcedure-: Procedure;
		firstImport, lastImport: Import; numberImports: LONGINT;

		PROCEDURE & InitActorScope(outer: Scope);
		BEGIN
			InitScope(outer);
			ownerActor := NIL;
			bodyProcedure := NIL;
			numberImports := 0;
			firstImport := NIL; lastImport := NIL;
		END InitActorScope;

		PROCEDURE SetOwnerActor*(owner: ActorType);
		BEGIN
			ownerActor := owner
		END SetOwnerActor;

		PROCEDURE SetBodyProcedure*(bodyProcedure: Procedure);
		BEGIN
			SELF.bodyProcedure := bodyProcedure;
		END SetBodyProcedure;

		PROCEDURE FindImport*(identifier: Identifier): Import;
		VAR p: Import;
		BEGIN
			p := firstImport;
			WHILE(p#NIL) & (p.name.name # identifier.name) DO p := p.nextImport END; (* finds imports and re-imports! *)
			RETURN p;
		END FindImport;

		PROCEDURE AddImport*(module: Module);
		VAR import: Import;
		BEGIN
			IF FindImport(module.name) = NIL THEN
				import := NewImport(0,module.name, module.name, TRUE);
				IF lastImport= NIL THEN firstImport:= import ELSE lastImport.nextImport := import END;
				lastImport := import;
			END;
			INC(numberImports);
		END AddImport;

	END ActorScope;


	(**
		<<
		IMPORT firstImport .. lastImport;
		...
		firstOperator ... lastOperator
		....
		>>
	**)

	ModuleScope*= OBJECT(Scope)
		VAR
		firstImport-,lastImport-: Import; numberImports: LONGINT; (* imported modules *)
		firstOperator-,lastOperator-: Operator; numberOperators: LONGINT; (* defined operators *)
		firstBuiltin-,lastBuiltin-: Builtin; numberBuiltins: LONGINT; (* defined builtins, only for global and system module *)

		firstComment-,lastComment-: Comment; numberComments-: LONGINT; (* comments *)
		bodyProcedure-: Procedure;

		PROCEDURE & InitModuleScope;
		BEGIN
			InitScope(NIL);
			firstComment := NIL; lastComment := NIL; numberComments := 0;
			firstImport:= NIL; lastImport := NIL; numberImports := 0;
			firstOperator := NIL; lastOperator := NIL; numberOperators := 0;
		END InitModuleScope;

		PROCEDURE SetBodyProcedure*(body: Procedure);
		BEGIN SELF.bodyProcedure := body;
		END SetBodyProcedure;

		PROCEDURE SetGlobalScope*(outer: Scope);
		BEGIN
			SELF.outerScope := outer;
		END SetGlobalScope;

		PROCEDURE AddBuiltin*(p: Builtin);
		BEGIN
			ASSERT(p # NIL);
			IF lastBuiltin= NIL THEN firstBuiltin := p ELSE lastBuiltin.nextBuiltin := p END;
			INC(numberBuiltins);
			lastBuiltin := p;
		END AddBuiltin;

		PROCEDURE AddOperator*(p: Operator);
		BEGIN
			ASSERT(p # NIL);
			IF lastOperator= NIL THEN firstOperator := p ELSE lastOperator.nextOperator := p END;
			INC(numberOperators);
			lastOperator := p;
		END AddOperator;

		PROCEDURE FindOperator*(identifier: Identifier): Operator;
		VAR p: Operator;
		BEGIN
			p := firstOperator;
			WHILE(p#NIL) & (p.name.name # identifier.name) DO p := p.nextOperator END;
			RETURN p;
		END FindOperator;

		PROCEDURE AddImport*(i: Import);
		BEGIN
			ASSERT(i # NIL);
			ASSERT(i.nextImport = NIL);
			IF lastImport= NIL THEN firstImport:= i ELSE lastImport.nextImport := i END;
			lastImport := i;
			INC(numberImports);
		END AddImport;

		PROCEDURE FindImport*(identifier: Identifier): Import;
		VAR p: Import;
		BEGIN
			p := firstImport;
			WHILE(p#NIL) & (p.name.name # identifier.name) DO p := p.nextImport END; (* finds imports and re-imports! *)
			RETURN p;
		END FindImport;

		PROCEDURE GetImport*( index: LONGINT ): Import;
		VAR import: Import;
		BEGIN
			import := firstImport;
			WHILE(import # NIL) & (index > 0) DO
				import := import.nextImport;
				DEC(index);
			END;
			RETURN import;
		END GetImport;

		PROCEDURE AddComment*(comment: Comment);
		BEGIN
			ASSERT(comment # NIL);
			IF lastComment= NIL THEN firstComment := comment ELSE lastComment.nextComment := comment END;
			INC(numberComments);
			lastComment := comment;
		END AddComment;

		PROCEDURE ImportByModuleName*(moduleName,context: Identifier): Import;
		VAR p: Import;
		BEGIN
			p := firstImport;
			WHILE(p#NIL) & ~(moduleName.Equals(p.moduleName) & context.Equals(p.context)) DO p := p.nextImport END;
			RETURN p;
		END ImportByModuleName;

		PROCEDURE RemoveImporters*(moduleName,context: Identifier);
		VAR this: Import;

			PROCEDURE Check(p: Import): BOOLEAN;
			VAR result: BOOLEAN;
			BEGIN
				IF moduleName.Equals(p.moduleName) & context.Equals(p.context) THEN
					result := TRUE
				ELSE
					result := p.module.moduleScope.ImportByModuleName(moduleName,context) # NIL;
				END;
				RETURN result
			END Check;

		BEGIN
			WHILE(firstImport # NIL) & Check(firstImport) DO
				firstImport := firstImport.nextImport;
				DEC(numberImports);
			END;
			IF firstImport = NIL THEN lastImport := NIL
			ELSE
				this :=firstImport;
				WHILE(this.nextImport # NIL) DO
					IF Check(this.nextImport) THEN
						this.nextImport := this.nextImport.nextImport;
						DEC(numberImports);
					ELSE
						this := this.nextImport
					END;
				END;
				lastImport := this;
			END;
		END RemoveImporters;


	END ModuleScope;


	(* << MODULE name ['in' context] moduleScope name '.' >>  *)
	Module* = OBJECT (Symbol)
		VAR
			sourceName-: Scanner.StringType;
			moduleScope-: ModuleScope;
			context-:Identifier; (* modules context *)
			case-: LONGINT; (* module notation in lower or upper case, important for printout and operators *)
			firstScope-,lastScope-: Scope; numberScopes-: LONGINT; (* list of all scopes for checker / backend traversal etc. *)

		PROCEDURE & InitModule( CONST sourceName: ARRAY OF CHAR; position: LONGINT; name: Identifier; scope: ModuleScope; case: LONGINT);
		BEGIN
			InitSymbol(position,name);
			COPY (sourceName, SELF.sourceName);
			moduleScope := scope;
			ASSERT(scope.ownerModule = NIL); (* cannot register twice ! *)
			scope.ownerModule := SELF;
			context := NIL;
			SELF.case := case;
			firstScope := NIL; lastScope := NIL; numberScopes := 0;
			SetType(moduleType);
		END InitModule;

		PROCEDURE SetContext*(context: Identifier);
		BEGIN	SELF.context := context;
		END SetContext;

		PROCEDURE SetName*(name: Identifier);
		BEGIN SELF.name := name
		END SetName;

		PROCEDURE AddScope*(c: Scope);
		BEGIN
			IF lastScope= NIL THEN firstScope := c ELSE lastScope.nextScope := c END;
			lastScope := c;
			INC(numberScopes);
		END AddScope;

	END Module;

VAR
	(* invalid items used, for example, by parser and checker *)
	invalidString-: Basic.String;
	invalidIdentifier-: Identifier;
	invalidQualifiedIdentifier-: QualifiedIdentifier;
	invalidType-: Type;
	invalidExpression-: Expression; (* mapped to invalidDesignator for better error handling in checker *)
	invalidDesignator-: Designator;
	invalidValue-: Value;
	invalidSymbol-: Symbol;

	anonymous-: Basic.String;
	anonymousIdentifier-: Identifier;
	importType-: Type;
	typeDeclarationType-: Type;
	moduleType-: Type;

	PROCEDURE InitFingerprint*(VAR fingerprint: Fingerprint);
	BEGIN
		fingerprint.shallowAvailable := FALSE;
		fingerprint.deepAvailable := FALSE;
		fingerprint.shallow := 0;
		fingerprint.private := 0;
		fingerprint.public := 0;
	END InitFingerprint;

	PROCEDURE NewModule*( CONST sourceName: ARRAY OF CHAR; position: LONGINT;  name: Identifier;scope: ModuleScope; case: LONGINT ): Module;
	VAR module: Module;
	BEGIN
		INC( moduleCount );  NEW( module, sourceName, position, name, scope, case);  RETURN module;
	END NewModule;

	PROCEDURE NewComment*(position: LONGINT; scope: Scope; CONST source: ARRAY OF CHAR; length: LONGINT): Comment;
	VAR comment: Comment;
	BEGIN
		NEW(comment,position,scope,source,length); RETURN comment;
	END NewComment;

	PROCEDURE NewImport*( position: LONGINT;  alias, name: Identifier; direct: BOOLEAN): Import;
	VAR import: Import;
	BEGIN
		INC( importCount );  NEW( import, position, alias, name, direct );  RETURN import
	END NewImport;

	PROCEDURE NewConstant*( position: LONGINT;  name: Identifier ): Constant;
	VAR constant: Constant;
	BEGIN
		INC( constantCount );  NEW( constant, position, name );  RETURN constant
	END NewConstant;

	PROCEDURE NewProcedure*( position: LONGINT;  name: Identifier; scope: ProcedureScope ): Procedure;
	VAR procedure: Procedure;
	BEGIN
		INC( procedureCount );  NEW( procedure, position, name, scope);  RETURN procedure
	END NewProcedure;

	PROCEDURE NewBuiltin*(position: LONGINT; name: Identifier; id: LONGINT): Builtin;
	VAR builtin: Builtin;
	BEGIN
		NEW(builtin,position,name,id); RETURN builtin
	END NewBuiltin;

	PROCEDURE NewOperator*( position: LONGINT;  name: Identifier; scope: ProcedureScope): Operator;
	VAR operator: Operator;
	BEGIN
		INC( operatorCount );  NEW( operator, position, name, scope);  RETURN operator
	END NewOperator;

	PROCEDURE NewType*(): Type;  (* for error handling: invalid Type, is realtime type *)
	VAR type: Type;
	BEGIN
		INC( typeCount );  NEW( type, -1, {RealtimeFlag});  RETURN type
	END NewType;

	PROCEDURE NewBasicType*(position: LONGINT; name: Identifier; flags: SET): BasicType;
	VAR basicType: BasicType;
	BEGIN
		INC(basicTypeCount); NEW(basicType, position, name, flags); RETURN basicType;
	END NewBasicType;

	PROCEDURE NewCharacterType*(position: LONGINT;name: Identifier): CharacterType;
	VAR basicType: CharacterType;
	BEGIN
		INC(basicTypeCount); NEW(basicType, position, name); RETURN basicType;
	END NewCharacterType;

	PROCEDURE NewIntegerType*(position: LONGINT; name: Identifier): IntegerType;
	VAR basicType: IntegerType;
	BEGIN
		INC(basicTypeCount); NEW(basicType, position, name); RETURN basicType;
	END NewIntegerType;

	PROCEDURE NewFloatType*(position: LONGINT; name: Identifier): FloatType;
	VAR basicType: FloatType;
	BEGIN
		INC(basicTypeCount); NEW(basicType, position, name); RETURN basicType;
	END NewFloatType;

	PROCEDURE NewTypeDeclaration*(position: LONGINT; name: Identifier): TypeDeclaration;
	VAR typeDeclaration: TypeDeclaration;
	BEGIN
		ASSERT(~name.Equals(NewIdentifier(-1,"")));
		INC(typeDeclarationCount); NEW(typeDeclaration,position,name); RETURN typeDeclaration
	END NewTypeDeclaration;

	PROCEDURE NewStringType*( position: LONGINT; length: LONGINT): StringType;
	VAR stringType: StringType;
	BEGIN
		NEW( stringType, position, length);  RETURN stringType;
	END NewStringType;

	PROCEDURE NewEnumerationType*( position: LONGINT; scope: Scope; enumerationScope: EnumerationScope): EnumerationType;
	VAR enumerationType: EnumerationType;
	BEGIN
		NEW( enumerationType, position, scope, enumerationScope);  RETURN enumerationType;
	END NewEnumerationType;

	PROCEDURE NewRangeType*(position: LONGINT; scope: Scope; commonType: Type): RangeType;
	VAR rangeType: RangeType;
	BEGIN
		NEW(rangeType,position,scope,commonType); RETURN rangeType
	END NewRangeType;

	PROCEDURE NewArrayType*( position: LONGINT; scope: Scope; form: LONGINT): ArrayType;
	VAR arrayType: ArrayType;
	BEGIN
		INC( arrayTypeCount );  NEW( arrayType, position,scope, form);  RETURN arrayType;
	END NewArrayType;

	PROCEDURE NewMathArrayType*( position: LONGINT; scope: Scope; form: LONGINT): MathArrayType;
	VAR mathArrayType: MathArrayType;
	BEGIN
		INC( arrayTypeCount );  NEW( mathArrayType,  position,scope,form);  RETURN mathArrayType;
	END NewMathArrayType;

	PROCEDURE NewPointerType*( position: LONGINT; scope: Scope): PointerType;
	VAR pointerType: PointerType;
	BEGIN
		INC( pointerTypeCount );  NEW( pointerType, position,scope);  RETURN pointerType;
	END NewPointerType;

	PROCEDURE NewPortType*( position: LONGINT; direction: LONGINT; channelType: Type; scope: Scope): PortType;
	VAR portType: PortType;
	BEGIN
		INC( portTypeCount );  NEW( portType, position, direction, channelType, scope);  RETURN portType;
	END NewPortType;

	PROCEDURE NewRecordType*( position: LONGINT; scope: Scope; recordScope: RecordScope): RecordType;
	VAR recordType: RecordType;
	BEGIN
		INC( recordTypeCount );  NEW( recordType, position, scope, recordScope);  RETURN recordType
	END NewRecordType;

	PROCEDURE NewActorType*(position: LONGINT; scope, actorScope: Scope): ActorType;
	VAR actorType: ActorType;
	BEGIN
		NEW(actorType, position, scope, actorScope); RETURN actorType;
	END NewActorType;

	PROCEDURE NewProcedureType*( position: LONGINT; scope: Scope): ProcedureType;
	VAR procedureType: ProcedureType;
	BEGIN
		INC( procedureTypeCount );  NEW( procedureType, position,scope);  RETURN procedureType;
	END NewProcedureType;

	PROCEDURE NewQualifiedType*( position: LONGINT;   scope: Scope; qualifiedIdentifier: QualifiedIdentifier): QualifiedType;
	VAR qualifiedType: QualifiedType;
	BEGIN
		INC( qualifiedTypeCount );  NEW( qualifiedType, position,scope,qualifiedIdentifier );  RETURN qualifiedType
	END NewQualifiedType;

	PROCEDURE NewSymbol*(name: Identifier): Symbol; (* for error handling: invalid Symbol *)
	VAR symbol: Symbol;
	BEGIN
		NEW(symbol,-1,name); RETURN symbol
	END NewSymbol;

	PROCEDURE NewVariable*( position: LONGINT;  name: Identifier): Variable;
	VAR variable: Variable;
	BEGIN
		INC( variableCount );  NEW( variable, position, name );  RETURN variable
	END NewVariable;

	PROCEDURE NewQualifiedIdentifier*( position: LONGINT;  prefix, suffix: Identifier ): QualifiedIdentifier;
	VAR qualifiedIdentifier: QualifiedIdentifier;
	BEGIN
		ASSERT(suffix # NIL);
		INC( qualifiedIdentifierCount );  NEW( qualifiedIdentifier, position, prefix, suffix );  RETURN qualifiedIdentifier
	END NewQualifiedIdentifier;

	PROCEDURE NewIdentifier*( position: LONGINT;  CONST name: ARRAY OF CHAR): Identifier;
	VAR identifier: Identifier;
	BEGIN
		INC( identifierCount );  NEW( identifier, position, name);
		RETURN identifier
	END NewIdentifier;

	PROCEDURE NewParameter*( position: LONGINT; ownerType:Type ;  name: Identifier; passAs: LONGINT): Parameter;
	VAR parameter: Parameter;
	BEGIN
		INC( parameterCount );  NEW( parameter, position, ownerType, name, passAs);  RETURN parameter;
	END NewParameter;

	PROCEDURE NewExpressionList*(): ExpressionList;
	VAR expressionList: ExpressionList;
	BEGIN
		INC( expressionListCount );  NEW(expressionList);  RETURN expressionList
	END NewExpressionList;

	PROCEDURE NewDesignator*(): Designator; (* for error handling: invalid Designator *)
	VAR designator: Designator;
	BEGIN
		NEW(designator,-1); RETURN designator;
	END NewDesignator;

	PROCEDURE NewIdentifierDesignator*( position: LONGINT; identifier: Identifier): IdentifierDesignator;
	VAR identifierDesignator: IdentifierDesignator;
	BEGIN
		INC( identifierDesignatorCount);  NEW( identifierDesignator, position, identifier );  RETURN identifierDesignator
	END NewIdentifierDesignator;

	PROCEDURE NewSelectorDesignator*( position: LONGINT;  left: Designator; name: Identifier ): SelectorDesignator;
	VAR selectorDesignator: SelectorDesignator;
	BEGIN
		INC( selectorCount );  NEW( selectorDesignator, position, left, name );  RETURN selectorDesignator
	END NewSelectorDesignator;

	PROCEDURE NewParameterDesignator*( position: LONGINT; left: Designator; expressionList: ExpressionList ): ParameterDesignator;
	VAR parameterDesignator: ParameterDesignator;
	BEGIN
		INC( parameterDesignatorCount );  NEW( parameterDesignator,position, left, expressionList );  RETURN parameterDesignator
	END NewParameterDesignator;

	PROCEDURE NewArrowDesignator*( position: LONGINT; left: Designator ): ArrowDesignator;
	VAR dereferenceDesignator: ArrowDesignator;
	BEGIN
		INC( dereferenceDesignatorCount );  NEW( dereferenceDesignator, position, left );  RETURN dereferenceDesignator;
	END NewArrowDesignator;

	PROCEDURE NewBracketDesignator*( position: LONGINT; left: Designator; expressionList: ExpressionList ): BracketDesignator;
	VAR bracketDesignator: BracketDesignator;
	BEGIN
		INC( bracketDesignatorCount );  NEW( bracketDesignator, position, left, expressionList );  RETURN bracketDesignator
	END NewBracketDesignator;

	PROCEDURE NewSymbolDesignator*( position: LONGINT; left: Designator; symbol: Symbol ): SymbolDesignator;
	VAR symbolDesignator: SymbolDesignator;
	BEGIN
		INC( symbolDesignatorCount );  NEW( symbolDesignator, position, left, symbol); RETURN symbolDesignator
	END NewSymbolDesignator;

	PROCEDURE NewIndexDesignator*( position: LONGINT; left: Designator): IndexDesignator;
	VAR indexDesignator: IndexDesignator;
	BEGIN
		INC( indexDesignatorCount );  NEW( indexDesignator, position, left);  RETURN indexDesignator
	END NewIndexDesignator;

	PROCEDURE NewProcedureCallDesignator*(position: LONGINT; left: Designator; parameters: ExpressionList): ProcedureCallDesignator;
	VAR procedureCallDesignator: ProcedureCallDesignator;
	BEGIN
		NEW(procedureCallDesignator, position, left, parameters); RETURN procedureCallDesignator
	END NewProcedureCallDesignator;

	PROCEDURE NewBuiltinCallDesignator*(position: LONGINT; id: LONGINT; parameters: ExpressionList): BuiltinCallDesignator;
	VAR builtinCallDesignator: BuiltinCallDesignator;
	BEGIN
		NEW(builtinCallDesignator, position, id, parameters); RETURN builtinCallDesignator
	END NewBuiltinCallDesignator;

	PROCEDURE NewTypeGuardDesignator*(position: LONGINT; left: Designator; type: Type): TypeGuardDesignator;
	VAR guardDesignator: TypeGuardDesignator;
	BEGIN
		NEW(guardDesignator,position,left,type); RETURN guardDesignator;
	END NewTypeGuardDesignator;

	PROCEDURE NewDereferenceDesignator*( position: LONGINT; left: Designator): DereferenceDesignator;
	VAR dereferenceDesignator: DereferenceDesignator;
	BEGIN
		INC( dereferenceDesignatorCount );  NEW( dereferenceDesignator, position, left);  RETURN dereferenceDesignator
	END NewDereferenceDesignator;

	PROCEDURE NewSupercallDesignator*( position: LONGINT; left: Designator): SupercallDesignator;
	VAR supercallDesignator: SupercallDesignator;
	BEGIN
		INC( supercallDesignatorCount );  NEW( supercallDesignator, position, left);  RETURN supercallDesignator
	END NewSupercallDesignator;

	PROCEDURE NewSelfDesignator*( position: LONGINT): SelfDesignator;
	VAR selfDesignator: SelfDesignator;
	BEGIN
		INC( selfDesignatorCount );  NEW( selfDesignator, position);  RETURN selfDesignator
	END NewSelfDesignator;

	PROCEDURE NewExpression*(): Expression; (* for error handling: invalid Expression *)
	VAR expression: Expression;
	BEGIN
		NEW(expression,-1); RETURN expression;
	END NewExpression;

	PROCEDURE NewElement*( position: LONGINT;  from,to: Expression ): Expression;
	BEGIN
			IF from = to THEN RETURN from
			ELSE RETURN NewRangeExpression(position,from,to,NIL)
			END;
	END NewElement;

	PROCEDURE NewSet*( position: LONGINT ): Set;
	VAR set: Set;
	BEGIN INC( setCount );  NEW( set, position );  RETURN set
	END NewSet;

	PROCEDURE NewMathArrayExpression*( position: LONGINT ): MathArrayExpression;
	VAR mathArrayExpression: MathArrayExpression;
	BEGIN INC( mathArrayExpressionCount );  NEW( mathArrayExpression, position );  RETURN mathArrayExpression
	END NewMathArrayExpression;

	PROCEDURE NewBinaryExpression*( position: LONGINT;  left, right: Expression;  operator: LONGINT ): BinaryExpression;
	VAR binaryExpression: BinaryExpression;
	BEGIN
		INC( binaryExpressionCount );  NEW( binaryExpression, position, left, right, operator );  RETURN binaryExpression;
	END NewBinaryExpression;

	PROCEDURE NewRangeExpression*(position: LONGINT; from,to,by: Expression): RangeExpression;
	VAR rangeExpression: RangeExpression;
	BEGIN
		NEW(rangeExpression,position,from,to,by); RETURN rangeExpression
	END NewRangeExpression;

	PROCEDURE NewTensorRangeExpression*(position: LONGINT): TensorRangeExpression;
	VAR tensorRangeExpression: TensorRangeExpression;
	BEGIN
		NEW(tensorRangeExpression,position); RETURN tensorRangeExpression
	END NewTensorRangeExpression;


	PROCEDURE NewUnaryExpression*( position: LONGINT;  operand: Expression;  operator: LONGINT ): UnaryExpression;
	VAR unaryExpression: UnaryExpression;
	BEGIN
		INC( unaryExpressionCount );  NEW( unaryExpression, position, operand, operator );  RETURN unaryExpression;
	END NewUnaryExpression;

	PROCEDURE NewConversion*( position: LONGINT;  expression: Expression; type: Type; typeExpression: Expression): Conversion;
	VAR conversion: Conversion;
	BEGIN
		ASSERT(type # NIL);
		NEW( conversion, position, expression,type, typeExpression );  RETURN conversion;
	END NewConversion;

	PROCEDURE NewValue*(): Value;(* for error handling: invalid Value *)
	VAR value: Value;
	BEGIN
		NEW(value,-1); RETURN value;
	END NewValue;

	PROCEDURE NewIntegerValue*( position: LONGINT;  value: HUGEINT): IntegerValue;
	VAR integerValue: IntegerValue;
	BEGIN
		INC( integerValueCount );  NEW( integerValue, position, value);  RETURN integerValue;
	END NewIntegerValue;

	PROCEDURE NewCharacterValue*( position: LONGINT;  value: CHAR): CharacterValue;
	VAR characterValue: CharacterValue;
	BEGIN
		INC( integerValueCount );  NEW( characterValue, position, value);  RETURN characterValue;
	END NewCharacterValue;

	PROCEDURE NewSetValue*(position: LONGINT; value: SET): SetValue;
	VAR setValue: SetValue;
	BEGIN
		INC(setValueCount); NEW(setValue, position, value); RETURN setValue
	END NewSetValue;

	PROCEDURE NewMathArrayValue*( position: LONGINT ): MathArrayValue;
	VAR mathArrayValue: MathArrayValue;
	BEGIN INC( mathArrayValueCount );  NEW( mathArrayValue, position );  RETURN mathArrayValue
	END NewMathArrayValue;

	PROCEDURE NewRealValue*( position: LONGINT;  value: LONGREAL): RealValue;
	VAR realValue: RealValue;
	BEGIN
		INC( realValueCount );  NEW( realValue, position, value);  RETURN realValue
	END NewRealValue;

	PROCEDURE NewStringValue*( position: LONGINT;  CONST value: ARRAY OF CHAR): StringValue;
	VAR stringValue: StringValue;
	BEGIN
		INC( stringValueCount );  NEW( stringValue, position, value );  RETURN stringValue
	END NewStringValue;

	PROCEDURE NewBooleanValue*( position: LONGINT;  value: BOOLEAN): BooleanValue;
	VAR booleanValue: BooleanValue;
	BEGIN
		INC( booleanValueCount );  NEW( booleanValue, position, value );  RETURN booleanValue;
	END NewBooleanValue;

	PROCEDURE NewNilValue*( position: LONGINT ): NilValue;
	VAR nilValue: NilValue;
	BEGIN
		INC( nilValueCount );  NEW( nilValue, position );  RETURN nilValue
	END NewNilValue;

	PROCEDURE NewEnumerationValue*( position: LONGINT; value: LONGINT ): EnumerationValue;
	VAR enumeratorValue: EnumerationValue;
	BEGIN
		INC( enumeratorValueCount );  NEW( enumeratorValue, position, value );  RETURN enumeratorValue
	END NewEnumerationValue;

	PROCEDURE NewStatement*(outer: Statement): Statement; (* for error handling: invalid Statement *)
	VAR statement: Statement;
	BEGIN NEW(statement,-1,outer); RETURN statement;
	END NewStatement;

	PROCEDURE NewStatementSequence*(): StatementSequence;
	VAR statementSequence: StatementSequence;
	BEGIN
		INC( statementSequenceCount );  NEW( statementSequence);  RETURN statementSequence
	END NewStatementSequence;

	PROCEDURE NewModifier*(identifier: Identifier; expression: Expression): Modifier;
	VAR blockModifier: Modifier;
	BEGIN
		NEW(blockModifier,identifier,expression); RETURN blockModifier
	END NewModifier;

	PROCEDURE NewStatementBlock*( position: LONGINT ; outer: Statement): StatementBlock;
	VAR statementBlock: StatementBlock;
	BEGIN
		INC( statementBlockCount );  NEW( statementBlock, position, outer );  RETURN statementBlock
	END NewStatementBlock;

	PROCEDURE NewBody*( position: LONGINT ; scope: ProcedureScope): Body;
	VAR body: Body;
	BEGIN
		INC( bodyCount );  NEW( body, position,scope );  RETURN body
	END NewBody;

	PROCEDURE NewIfPart*(): IfPart;
	VAR ifPart: IfPart;
	BEGIN
		INC( ifPartCount );  NEW( ifPart);  RETURN ifPart
	END NewIfPart;

	PROCEDURE NewIfStatement*( position: LONGINT ; outer: Statement): IfStatement;
	VAR ifStatement: IfStatement;
	BEGIN
		INC( ifStatementCount );   NEW( ifStatement, position,outer );  RETURN ifStatement
	END NewIfStatement;

	PROCEDURE NewAssignment*( position: LONGINT;  left: Designator; right: Expression; outer: Statement): Assignment;
	VAR assignment: Assignment;
	BEGIN
		INC( assignmentCount );  NEW( assignment, position, left, right,outer );  RETURN assignment
	END NewAssignment;

	PROCEDURE NewProcedureCallStatement*(position: LONGINT; call: Designator; outer: Statement): ProcedureCallStatement;
	VAR caller: ProcedureCallStatement;
	BEGIN
		INC(callerCount); NEW(caller,position,call,outer); RETURN caller
	END NewProcedureCallStatement;

	PROCEDURE NewCaseStatement*( position: LONGINT ; outer: Statement): CaseStatement;
	VAR caseStatement: CaseStatement;
	BEGIN
		INC( caseStatementCount );  NEW( caseStatement, position,outer );  RETURN caseStatement
	END NewCaseStatement;

	PROCEDURE NewCasePart*(): CasePart;
	VAR casePart: CasePart;
	BEGIN
		INC( casePartCount );  NEW( casePart);  RETURN casePart
	END NewCasePart;

	PROCEDURE NewWithStatement*( position: LONGINT; outer: Statement): WithStatement;
	VAR withStatement: WithStatement;
	BEGIN
		INC( withStatementCount );  NEW( withStatement, position, outer );  RETURN withStatement
	END NewWithStatement;

	PROCEDURE NewWhileStatement*( position: LONGINT ; outer: Statement): WhileStatement;
	VAR whileStatement: WhileStatement;
	BEGIN
		INC( whileStatementCount );  NEW( whileStatement, position,outer );  RETURN whileStatement
	END NewWhileStatement;

	PROCEDURE NewRepeatStatement*( position: LONGINT ; outer: Statement): RepeatStatement;
	VAR repeatStatement: RepeatStatement;
	BEGIN
		INC( repeatStatementCount );  NEW( repeatStatement, position ,outer);  RETURN repeatStatement
	END NewRepeatStatement;

	PROCEDURE NewForStatement*( position: LONGINT; outer: Statement ): ForStatement;
	VAR forStatement: ForStatement;
	BEGIN
		INC( forStatementCount );  NEW( forStatement, position,outer );  RETURN forStatement
	END NewForStatement;

	PROCEDURE NewLoopStatement*( position: LONGINT ; outer: Statement): LoopStatement;
	VAR loopStatement: LoopStatement;
	BEGIN
		INC( loopStatementCount );  NEW( loopStatement, position ,outer);  RETURN loopStatement
	END NewLoopStatement;

	PROCEDURE NewExitStatement*( position: LONGINT ; outer: Statement): ExitStatement;
	VAR exitStatement: ExitStatement;
	BEGIN
		INC( exitStatementCount );  NEW( exitStatement, position, outer);  RETURN exitStatement
	END NewExitStatement;

	PROCEDURE NewReturnStatement*( position: LONGINT; outer: Statement ): ReturnStatement;
	VAR returnStatement: ReturnStatement;
	BEGIN
		INC( returnStatementCount );  NEW( returnStatement, position,outer );  RETURN returnStatement
	END NewReturnStatement;

	PROCEDURE NewAwaitStatement*( position: LONGINT; outer: Statement ): AwaitStatement;
	VAR awaitStatement: AwaitStatement;
	BEGIN
		INC( awaitStatementCount );  NEW( awaitStatement, position, outer );  RETURN awaitStatement
	END NewAwaitStatement;

	PROCEDURE NewCode*(position: LONGINT; outer: Statement): Code;
	VAR code: Code;
	BEGIN
		NEW(code,position,outer); RETURN code
	END NewCode;

	PROCEDURE NewProcedureScope*(outer: Scope): ProcedureScope;
	VAR scope: ProcedureScope;
	BEGIN	NEW(scope,outer); RETURN scope
	END NewProcedureScope;

	PROCEDURE NewModuleScope*(): ModuleScope;
	VAR scope: ModuleScope;
	BEGIN	NEW(scope); RETURN scope
	END NewModuleScope;

	PROCEDURE NewRecordScope*(outer: Scope): RecordScope;
	VAR scope: RecordScope;
	BEGIN	NEW(scope,outer); RETURN scope
	END NewRecordScope;

	PROCEDURE NewActorScope*(outer: Scope): ActorScope;
	VAR scope: ActorScope;
	BEGIN	NEW(scope,outer); RETURN scope
	END NewActorScope;

	PROCEDURE NewEnumerationScope*(outer: Scope): EnumerationScope;
	VAR scope: EnumerationScope;
	BEGIN NEW(scope,outer); RETURN scope
	END NewEnumerationScope;

	PROCEDURE LogCounters*(context: Commands.Context);

		PROCEDURE FixedStringInt(CONST s: ARRAY OF CHAR; int: LONGINT);
		VAR i: LONGINT;
		BEGIN
			context.out.String(s);
			i := 0;
			WHILE s[i] # 0X DO
				INC(i);
			END;
			WHILE(i<20) DO
				context.out.Char(" ");
				INC(i);
			END;
			context.out.Int(int,10);
			context.out.Ln;
		END FixedStringInt;

	BEGIN
		FixedStringInt("nodeCount ", nodeCount );
		FixedStringInt("listCount ",listCount  );
		FixedStringInt("identifierCount ",identifierCount  );
		FixedStringInt("qualifiedIdentifierCount ", qualifiedIdentifierCount );
		FixedStringInt("typeCount ", typeCount );
		FixedStringInt("basicTypeCount ", basicTypeCount );
		FixedStringInt("arrayTypeCount ", arrayTypeCount );
		FixedStringInt("pointerTypeCount ", pointerTypeCount );
		FixedStringInt("portTypeCount ", portTypeCount );
		FixedStringInt("recordTypeCount ",recordTypeCount  );
		FixedStringInt("actorTypeCount ",actorTypeCount  );
		FixedStringInt("defintionTypeCount ",defintionTypeCount  );
		FixedStringInt("procedureTypeCount ", procedureTypeCount );
		FixedStringInt("qualifiedTypeCount ",qualifiedTypeCount  );
		FixedStringInt("typeDeclarationListCount ",typeDeclarationListCount  );
		FixedStringInt("definitionCount ",definitionCount  );
		FixedStringInt("definitionTypeCount ",definitionTypeCount  );
		FixedStringInt("expressionCount ", expressionCount );
		FixedStringInt("expressionListCount ", expressionListCount );
		FixedStringInt("selectorCount ",selectorCount  );
		FixedStringInt("indexDesignatorCount ",indexDesignatorCount  );
		FixedStringInt("parameterDesignatorCount ",parameterDesignatorCount  );
		FixedStringInt("dereferenceDesignatorCount ",dereferenceDesignatorCount  );
		FixedStringInt("supercallDesignatorCount ",supercallDesignatorCount  );
		FixedStringInt("selfDesignatorCount ",selfDesignatorCount  );
		FixedStringInt("designatorCount ",designatorCount  );
		FixedStringInt("elementCount ", elementCount );
		FixedStringInt("setCount ",setCount  );
		FixedStringInt("mathArrayExpressionCount ",mathArrayExpressionCount  );
		FixedStringInt("mathArrayValueCount ",mathArrayValueCount  );
		FixedStringInt("binaryExpressionCount ", binaryExpressionCount );
		FixedStringInt("unaryExpressionCount ",unaryExpressionCount  );
		FixedStringInt("valueCount ",valueCount  );
		FixedStringInt("booleanValueCount ",booleanValueCount  );
		FixedStringInt("integerValueCount ", integerValueCount );
		FixedStringInt("setValueCount", setValueCount);
		FixedStringInt("realValueCount ", realValueCount );
		FixedStringInt("hugeintValueCount ",hugeintValueCount  );
		FixedStringInt("stringValueCount ",stringValueCount  );
		FixedStringInt("nilValueCount ",nilValueCount  );
		FixedStringInt("enumeratorValueCount ",enumeratorValueCount  );
		FixedStringInt("callerCount",callerCount);
		FixedStringInt("assignmentCount ",assignmentCount  );
		FixedStringInt("ifStatementCount ",ifStatementCount  );
		FixedStringInt("withStatementCount ",withStatementCount  );
		FixedStringInt("ifPartCount ",ifPartCount  );
		FixedStringInt("casePartCount ",casePartCount  );
		FixedStringInt("caseStatementCount ",caseStatementCount  );
		FixedStringInt("whileStatementCount ",whileStatementCount  );
		FixedStringInt("repeatStatementCount ",repeatStatementCount  );
		FixedStringInt("forStatementCount ",forStatementCount  );
		FixedStringInt("loopStatementCount ",loopStatementCount  );
		FixedStringInt("exitStatementCount ",exitStatementCount  );
		FixedStringInt("returnStatementCount ", returnStatementCount );
		FixedStringInt("awaitStatementCount ",awaitStatementCount  );
		FixedStringInt("typeDeclarationCount", typeDeclarationCount);
		FixedStringInt("definitionListCount ", definitionListCount );
		FixedStringInt("constantCount ",constantCount  );
		FixedStringInt("constantListCount ",constantListCount  );
		FixedStringInt("variableCount ",variableCount  );
		FixedStringInt("variableListCount ",variableListCount  );
		FixedStringInt("procedureCount ",procedureCount  );
		FixedStringInt("methodCount ",methodCount  );
		FixedStringInt("procedureListCount ", procedureListCount );
		FixedStringInt("operatorCount ", operatorCount );
		FixedStringInt("operatorListCount ",operatorListCount  );
		FixedStringInt("parameterCount ", parameterCount );
		FixedStringInt("parameterListCount ",parameterListCount  );
		FixedStringInt("importCount ",importCount  );
		FixedStringInt("importListCount ",importListCount  );
		FixedStringInt("statementSequenceCount ",statementSequenceCount  );
		FixedStringInt("declarationSequenceCount ",declarationSequenceCount  );
		FixedStringInt("statementBlockCount ",statementBlockCount );
		FixedStringInt("bodyCount ", bodyCount );
		FixedStringInt("moduleCount ", moduleCount );
	END LogCounters;

	PROCEDURE Init;
	BEGIN

		invalidString := Basic.MakeString("@invalidString");
		invalidIdentifier := NewIdentifier(-1,"@invalidString");
		invalidQualifiedIdentifier := NewQualifiedIdentifier(-1,NIL,invalidIdentifier);
		invalidType := NewType();
		invalidDesignator := NewDesignator();
		invalidDesignator.SetType(invalidType);
		invalidExpression := invalidDesignator;
		invalidValue := NewValue();
		invalidSymbol := NewSymbol(NewIdentifier(-1,""));
		invalidSymbol.SetType(invalidType);

		importType := NewType();
		importType.SetState(Resolved);
		typeDeclarationType := NewType();
		typeDeclarationType.SetState(Resolved);
		moduleType := NewType();
		moduleType.SetState(Resolved);
		anonymous := Basic.MakeString("");
		anonymousIdentifier := NewIdentifier(-1,"");



		(* debugging *)
		nodeCount := 0;  listCount := 0;  identifierCount := 0;  qualifiedIdentifierCount := 0;
		typeCount := 0; basicTypeCount := 0;  typeDeclarationCount := 0;  arrayTypeCount := 0;  pointerTypeCount := 0; portTypeCount := 0;
		recordTypeCount := 0; actorTypeCount := 0;
		defintionTypeCount := 0;  procedureTypeCount := 0;
		qualifiedTypeCount := 0;  typeDeclarationListCount := 0;  definitionCount := 0;  definitionTypeCount := 0;  expressionCount := 0;
		expressionListCount := 0;  selectorCount := 0;  indexDesignatorCount := 0;  parameterDesignatorCount := 0;
		dereferenceDesignatorCount := 0;  supercallDesignatorCount := 0; selfDesignatorCount := 0;
		designatorCount := 0;  elementCount := 0;  setCount := 0; mathArrayExpressionCount := 0; mathArrayValueCount := 0;   binaryExpressionCount := 0;
		unaryExpressionCount := 0;  valueCount := 0;  booleanValueCount := 0;  integerValueCount := 0;  setValueCount := 0; realValueCount := 0;
		hugeintValueCount := 0;  stringValueCount := 0;  nilValueCount := 0; enumeratorValueCount := 0;  callerCount := 0; assignmentCount := 0;  ifStatementCount := 0;
		withStatementCount := 0;  casePartCount := 0; ifPartCount := 0;  caseStatementCount := 0;  whileStatementCount := 0;  repeatStatementCount := 0;
		forStatementCount := 0;  loopStatementCount := 0;  exitStatementCount := 0;  returnStatementCount := 0;
		awaitStatementCount := 0;  definitionListCount := 0;  constantCount := 0;  constantListCount := 0;  variableCount := 0;
		variableListCount := 0;  procedureCount := 0; methodCount := 0;   procedureListCount := 0;  operatorCount := 0;  operatorListCount := 0;
		parameterCount := 0;  parameterListCount := 0;  importCount := 0;  importListCount := 0;  statementSequenceCount := 0;
		declarationSequenceCount := 0;  statementBlockCount := 0;  bodyCount := 0;  moduleCount := 0;

	END Init;


BEGIN
	Init;

END OCSyntaxTree.

