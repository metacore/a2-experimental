MODULE OCIntermediateBackend; (** AUTHOR ""; PURPOSE ""; *)

IMPORT Basic := OCBasic, SyntaxTree := OCSyntaxTree, SemanticChecker := OCSemanticChecker, Backend := OCBackend, Global := OCGlobal,
	WMUtilities,Scanner := OCScanner, IntermediateCode := OCIntermediateCode, Sections := OCSections, Printout := OCPrintout,
	SYSTEM, Diagnostics, Strings, Options, Streams, Compiler, Formats := OCFormats, SymbolFileFormat := OCTextualSymbolFile, D := Debugging,
	Fingerprinter := OCFingerprinter;


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
		IndexCheckTrap* = 7; (* generated when an index is out of array bounds *)
		AssertTrap* = 8; (* generated when an assert fails *)
		ArraySizeTrap* = 9;
		ArrayFormTrap*=10; (* indicates that array cannot be (re-)allocated since shape, type or size does not match *)
		SetElementTrap*=11; (* indicates that a set element is out of MIN(SET)...MAX(SET) *)
		NegativeDivisorTrap*=12;

		Trace = FALSE;
		TraceRegisters=TRUE;

		ArrayAlignment = 8*8;			(* first array element of ArrayBlock and first data element of SystemBlock must be aligned to 0 MOD ArrayAlignment *)

		(** system call numbers  *)
		NumberSystemCalls* = 12;
		SysNewRec* = 0;  SysNewArr* = 1;  SysNewSys* = 2;  SysCaseTable* = 3;  SysProcAddr* = 4;
		SysLock* = 5;  SysUnlock* = 6;  SysStart* = 7;  SysAwait* = 8; SysInterfaceLookup* = 9;
		SysRegisterInterface* = 10; SysGetProcedure* = 11;

		DefaultRuntimeModuleName ="Runtime";

		suppressModuleRegistration=FALSE;


TYPE
	SupportedProcedure= PROCEDURE {DELEGATE} (CONST instr: IntermediateCode.Instruction; VAR moduleName,procedureName: ARRAY OF CHAR): BOOLEAN;

	Operand = RECORD
		mode: SHORTINT;
		op: IntermediateCode.Operand;
		tag: IntermediateCode.Operand;
		dimOffset: LONGINT;
	END;

	Fixup= POINTER TO RECORD
		pc: LONGINT;
		nextFixup: Fixup;
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
		implementationVisitor: ImplementationVisitor;
		system: Global.System;
		currentScope: SyntaxTree.Scope;
		module: Sections.Module;
		moduleSelf: SyntaxTree.Variable;
		dump: BOOLEAN;

		PROCEDURE & Init(system: Global.System; implementationVisitor: ImplementationVisitor; diagnostics: Diagnostics.Diagnostics; dump: BOOLEAN);
		BEGIN
			currentScope := NIL; module := NIL; moduleSelf := NIL;
			SELF.system := system; SELF.implementationVisitor := implementationVisitor;
			SELF.dump := dump
		END Init;

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

		PROCEDURE VisitRangeType(x: SyntaxTree.RangeType);
		BEGIN (* no code emission *)   END VisitRangeType;

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
		VAR name: SyntaxTree.String; irv: IntermediateCode.Section;
		BEGIN
			IF currentScope IS SyntaxTree.ModuleScope THEN
				(* code section for variable *)
				Global.GetSymbolName(x,name);
				irv := IntermediateCode.NewSection(module.sections,Sections.VarSection,name,x,dump);
				irv.SetOffset(ToMemoryUnits(system,x.offsetInBits));
				irv.Emit(Reserve(ToMemoryUnits(system,system.SizeOf(x.type))));
				CheckTypeDeclaration(implementationVisitor, module,x.type,dump,implementationVisitor.newObjectFile);
			ELSIF currentScope IS SyntaxTree.RecordScope THEN
			END;
			(* do not call Type(x.type) here as this must already performed in the type declaration section ! *)
		END VisitVariable;

		PROCEDURE VisitTypeDeclaration(x: SyntaxTree.TypeDeclaration);
		BEGIN
			Type(x.declaredType); (* => code in objects *)
			IF x.declaredType.resolved IS SyntaxTree.PointerType THEN
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

			currentScope := prevScope;
		END Scope;

		PROCEDURE Procedure(x: SyntaxTree.Procedure);
		VAR scope: SyntaxTree.ProcedureScope;
			prevScope: SyntaxTree.Scope;
			inline: BOOLEAN;
			procedureType: SyntaxTree.ProcedureType;
			procedure: SyntaxTree.Procedure;
			pc: LONGINT;
			stackSize: LONGINT;
			parSize: LONGINT;
			name: SyntaxTree.String; ir: IntermediateCode.Section;
			null,size,fp: IntermediateCode.Operand;
			result: Operand;
			cc: LONGINT;

			PROCEDURE Parameters;
			VAR parameter: SyntaxTree.Parameter; procedureType: SyntaxTree.ProcedureType;
			BEGIN
				procedureType := x.type(SyntaxTree.ProcedureType);
				(* IF x.access * SyntaxTree.Public # {} THEN *) (*! why all types? ref section ? *)
					parameter := procedureType.firstParameter;
					WHILE parameter # NIL DO
						CheckTypeDeclaration(implementationVisitor, module,parameter.type,dump,implementationVisitor.newObjectFile); (* we have to re-export a type, i.e. it has to be present in the list of symbols *)
						parameter := parameter.nextParameter;
					END;
				(* END; *)
			END Parameters;

		BEGIN
			(*
			IF Trace & (dump # NIL) THEN dump.String("DeclarationVisitor:Procedure"); dump.Ln END;
			*)
			(* code section for this procedure *)
			scope := x.procedureScope;
			prevScope := currentScope;
			currentScope := scope;

			Global.GetSymbolName(x,name);
			IF (scope.body # NIL) & (x.HasFlag(SyntaxTree.InlineFlag)) THEN
				inline := TRUE;
				ir := IntermediateCode.NewSection(module.sections,Sections.InlineCodeSection,name,x,dump);
			ELSIF x = module.module.moduleScope.bodyProcedure THEN
				inline := FALSE;
				ir := IntermediateCode.NewSection(module.sections,Sections.BodyCodeSection,name,x,dump);
				ASSERT(Sections.CodeSection # Sections.BodyCodeSection,100);
			ELSE
				inline := FALSE;
				ir := IntermediateCode.NewSection(module.sections,Sections.CodeSection,name,x,dump);
			END;

			procedureType := x.type(SyntaxTree.ProcedureType);
			IF SyntaxTree.WinAPIFlag IN procedureType.flags THEN cc := SyntaxTree.WinAPIFlag
			ELSIF SyntaxTree.CFlag IN procedureType.flags THEN cc := SyntaxTree.CFlag
			ELSIF SyntaxTree.InterruptFlag IN procedureType.flags THEN cc := SyntaxTree.InterruptFlag
			ELSIF SyntaxTree.NoPAFFlag IN procedureType.flags THEN cc := SyntaxTree.NoPAFFlag
			ELSIF SyntaxTree.InlineFlag IN procedureType.flags THEN cc := SyntaxTree.InlineFlag
			ELSE cc := 0
			END;

			IF scope.body # NIL THEN
				IF ~inline THEN
					pc := ir.pc;
					IF scope.lastVariable = NIL THEN
						stackSize := 0
					ELSE
						stackSize := scope.lastVariable.offsetInBits;
						IF stackSize <0 THEN stackSize := -stackSize END;
						Basic.Align(stackSize,system.AlignmentOf(system.parameterAlignment,Global.Byte));  (* round up to parameter alignment *)
					END;
					ir.Emit(Nop()); (* placeholder for stack frame check *)
					ir.Emit(Nop()); (* placeholder for stack frame check (2) *)
					ir.Emit(Nop()); (* placeholder for enter *)
					ir.Emit(Nop()); (* placeholder for fill *)
					ir.EnterValidPAF;
				END;

				implementationVisitor.tagsAvailable := x.flags * {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag} = {};

				implementationVisitor.Body(scope.body,currentScope,ir,x = module.module.moduleScope.bodyProcedure);

				IF ~inline & (cc#SyntaxTree.NoPAFFlag) THEN
					IF scope.lastVariable # NIL THEN
						stackSize := scope.lastVariable.offsetInBits;
						IF stackSize <0 THEN stackSize := -stackSize END;
						Basic.Align(stackSize,system.AlignmentOf(system.parameterAlignment,Global.Byte));  (* round up to parameter alignment *)
					END;
				END;

				IF ~inline  & (cc#SyntaxTree.NoPAFFlag) THEN
					IF stackSize > 4*1024-256 THEN (* stack frame potentially larger than page size *) (*! get page size from backend *)
						IF implementationVisitor.GetRuntimeProcedure(implementationVisitor.runtimeModuleName,"EnsureAllocatedStack",procedure,TRUE) THEN
							size := IntermediateCode.Immediate(GetType(system,Global.Address),ToMemoryUnits(system,stackSize+256));
							ir.EmitAt(pc,Push(size));
							implementationVisitor.StaticCallOperand(result,procedure);
							ir.EmitAt(pc+1,Call(result.op,ProcedureParametersSize(system,procedure)));
						END;
					END;
					ir.EmitAt(pc+2,Enter(cc,ToMemoryUnits(system,stackSize))); (*!!*)
					IF stackSize > 0 THEN
						IF (stackSize MOD system.addressSize = 0) THEN
							null := IntermediateCode.Immediate(GetType(system,Global.Address),0);
							fp := IntermediateCode.Register(GetType(system,Global.Address),IntermediateCode.FP);
							IntermediateCode.AddOffset(fp,ToMemoryUnits(system,-system.addressSize));
							size := IntermediateCode.Immediate(GetType(system,Global.Address),stackSize DIV system.addressSize);
						ELSE
							null := IntermediateCode.Immediate(int8,0);
							fp := IntermediateCode.Register(GetType(system,Global.Address),IntermediateCode.FP);
							IntermediateCode.AddOffset(fp,ToMemoryUnits(system,-null.type.sizeInBits));
							size := IntermediateCode.Immediate(GetType(system,Global.Address),stackSize DIV null.type.sizeInBits);
						END;
						ir.EmitAt(pc+3,Fill(fp,null,size,TRUE));
					END;

					ir.ExitValidPAF;

					parSize := ProcedureParametersSize(system,x);
					IF (procedureType.returnType = NIL) OR (scope.body.code # NIL)  THEN
						ir.Emit(Leave(cc));
						ir.Emit(Return(parSize));
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
				ir.Emit(Return(parSize));
			END;
			Scope(scope);
			Parameters;
			currentScope := prevScope;
		END Procedure;

		(** entry function to visit a complete module *)
		PROCEDURE Module(x: SyntaxTree.Module; module: Sections.Module);
		VAR
			ir: IntermediateCode.Section; op: IntermediateCode.Operand; name: SyntaxTree.String;

			PROCEDURE EnsureBodyProcedure;
			VAR procedure: SyntaxTree.Procedure; procedureScope: SyntaxTree.ProcedureScope;
			BEGIN
				procedure := x.moduleScope.bodyProcedure;
				IF procedure = NIL THEN (* artificially add body procedure if not existing. Really needed? *)
					procedureScope := SyntaxTree.NewProcedureScope(module.module.moduleScope);
					procedure := SyntaxTree.NewProcedure(-1,SyntaxTree.NewIdentifier(-1,"$$BODY"), procedureScope);
					procedure.SetScope(module.module.moduleScope);
					procedure.SetType(SyntaxTree.NewProcedureType(-1,module.module.moduleScope));
					procedure.SetAccess(SyntaxTree.Hidden);
					module.module.moduleScope.SetBodyProcedure(procedure);
					module.module.moduleScope.AddProcedure(procedure);
				END;
			END EnsureBodyProcedure;

			PROCEDURE AddModuleBodyCallStub; (* code that is only necessary for static linkers *)
			VAR procedure: SyntaxTree.Procedure; procedureScope: SyntaxTree.ProcedureScope; name: SyntaxTree.String;
			BEGIN
				ASSERT (x.moduleScope.bodyProcedure # NIL);
				procedureScope := SyntaxTree.NewProcedureScope(module.module.moduleScope);
				procedure := SyntaxTree.NewProcedure(-1,SyntaxTree.NewIdentifier(-1,"$$BODYSTUB"), procedureScope);
				procedure.SetScope(module.module.moduleScope);
				procedure.SetType(SyntaxTree.NewProcedureType(-1,module.module.moduleScope));
				procedure.SetAccess(SyntaxTree.Hidden);
				Global.GetSymbolName (procedure,name);
				ir := IntermediateCode.NewSection(module.sections,Sections.InitCodeSection,name,procedure,dump);
				Global.GetSymbolName (x.moduleScope.bodyProcedure,name);
				IntermediateCode.InitAddress(op, GetType(system,Global.Address), IntermediateCode.NewSection(module.sections,Sections.BodyCodeSection,name,x.moduleScope.bodyProcedure,dump) , 0);
				ir.Emit(Call(op, 0));
			END AddModuleBodyCallStub;

		BEGIN
			ASSERT(x # NIL); ASSERT(module # NIL);
			SELF.module := module;

			IF ~implementationVisitor.newObjectFile THEN
				module.module.name.GetString(name); Strings.Append(name,"."); Strings.Append(name,"@moduleSelf");
				moduleSelf := SyntaxTree.NewVariable(0,SyntaxTree.NewIdentifier(-1,"@moduleSelf"));
				moduleSelf.SetType(Global.Any);
				moduleSelf.SetScope(x.moduleScope);
				moduleSelf.AddFlags({SyntaxTree.UntracedFlag});
				ir := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,moduleSelf,dump);  ir.SetOffset(0);
				IntermediateCode.InitImmediate(op,GetType(system,Global.Address),0);
				ir.Emit(Data(op));
			END;


			implementationVisitor.module := module;
			implementationVisitor.moduleScope := x.moduleScope;
			implementationVisitor.moduleSelf := moduleSelf;

			EnsureBodyProcedure; (* currently needed in Oberon, remove ? *)

			AddModuleBodyCallStub;

			Scope(x.moduleScope);
		END Module;

	END DeclarationVisitor;

	Register = RECORD count: LONGINT; type: IntermediateCode.Type END;
	Registers= ARRAY 32 OF Register;

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
		diagnostics : Diagnostics.Diagnostics;
		error: BOOLEAN;
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
		usedRegisters: Registers;

		(* useful operands and types *)
		nil,fp,sp,true,false: IntermediateCode.Operand;
		bool,addressType,setType: IntermediateCode.Type;

		commentPrintout: Printout.Printer;
		dump: Streams.Writer;
		tagsAvailable : BOOLEAN;
		supported: SupportedProcedure;
		emitLabels: BOOLEAN;
		runtimeModuleName : SyntaxTree.String;
		newObjectFile: BOOLEAN;


		PROCEDURE & Init(system: Global.System; checker: SemanticChecker.Checker; supportedProcedure: SupportedProcedure; emitLabels: BOOLEAN; CONST runtime: SyntaxTree.String; diagnostics: Diagnostics.Diagnostics;
			newObjectFile: BOOLEAN);
		VAR i: LONGINT;
		BEGIN
			SELF.system := system;
			SELF.runtimeModuleName := runtime;

			currentScope := NIL;
			hiddenPointerType := NIL;
			delegatePointerType := NIL;

			awaitProcCounter := 0;
			labelId := 0; constId := 0; labelId := 0;
			SELF.checker := checker;
			SELF.diagnostics := diagnostics;
			error := FALSE;
			position := Diagnostics.Invalid;
			conditional := FALSE;
			locked := FALSE;
			InitOperand(result,ModeUndefined);
			addressType := GetType(system,Global.Address);
			setType := GetType(system,Global.Set);
			fp := IntermediateCode.Register(addressType,IntermediateCode.FP);
			sp := IntermediateCode.Register(addressType,IntermediateCode.SP);
			nil := IntermediateCode.Immediate(addressType,0);
			FOR i := 0 TO LEN(usedRegisters)-1 DO
				usedRegisters[i].count := 0
			END;
			IntermediateCode.InitOperand(destination);
			tagsAvailable := TRUE;
			supported := supportedProcedure;
			SELF.emitLabels := emitLabels;
			IntermediateCode.InitOperand(arrayDestinationTag);

			bool := GetType(system,Global.Boolean);
			IntermediateCode.InitImmediate(false,bool,0);
			IntermediateCode.InitImmediate(true,bool,1);

			SELF.newObjectFile := newObjectFile;

		END Init;

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
		BEGIN
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
				dump.Update;
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
		BEGIN
			type := type.resolved;
			IF operand.mode = ModeReference THEN
				MakeMemory(mem,operand.op,GetType(system,type),0);
				ReleaseIntermediateOperand(operand.op);
				operand.op := mem;
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
			ASSERT((op.mode = ModeReference) OR (x.type.resolved = Global.Nil)); (* special case: winapi NIL parameter on references *)
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

		(** registers **)

		PROCEDURE AcquireRegister(type: IntermediateCode.Type): SHORTINT;
		VAR i: SHORTINT;
		BEGIN
			i := 1;
			WHILE (i < LEN(usedRegisters)) & (usedRegisters[i].count # 0) DO
				INC(i)
			END;
			Assert(i<LEN(usedRegisters),"not enough virtual registers");
			usedRegisters[i].type := type;
			IF TraceRegisters & (dump # NIL) THEN dump.String("acquire register: "); END;
			UseRegister(i);
			RETURN i
		END AcquireRegister;

		PROCEDURE UseRegister(i: SHORTINT);
		BEGIN
			INC(usedRegisters[i].count);
			IF TraceRegisters & (dump # NIL) THEN
				dump.String("use register: ");
				IntermediateCode.DumpType(dump,usedRegisters[i].type);
				IntermediateCode.DumpRegister(dump,i);
				dump.String("(");
				dump.Int(usedRegisters[i].count,1);
				dump.String(")");
				dump.Ln; dump.Update
			END;
		END UseRegister;

		PROCEDURE ReleaseRegister(i: SHORTINT);
		BEGIN
			(*
			Assert (usedRegisters[i] > 0,"release on unused register");
			*)
			DEC(usedRegisters[i].count);
			IF TraceRegisters & (dump # NIL) THEN
				dump.String("release register:");
				IntermediateCode.DumpType(dump,usedRegisters[i].type);
				IntermediateCode.DumpRegister(dump,i);
				dump.String("(");
				dump.Int(usedRegisters[i].count,1);
				dump.String(")");
				dump.Ln; dump.Update
			END;
			IF (usedRegisters[i].count < 0) THEN
				Error("compiler implementation error: release on unused register");
				usedRegisters[i].count := 0;
			END;
		END ReleaseRegister;

		PROCEDURE ReleaseIntermediateOperand(CONST op: IntermediateCode.Operand);
		BEGIN
			IF (op.register > 0) THEN ReleaseRegister(op.register) END;
		END ReleaseIntermediateOperand;

		PROCEDURE UseIntermediateOperand(CONST op: IntermediateCode.Operand);
		BEGIN
			IF (op.register > 0) THEN UseRegister(op.register) END;
		END UseIntermediateOperand;

		PROCEDURE ReleaseOperand(CONST op: Operand);
		BEGIN
			ReleaseIntermediateOperand(op.op);
			ReleaseIntermediateOperand(op.tag);
		END ReleaseOperand;

		PROCEDURE UseOperand(CONST op: Operand);
		BEGIN
			UseIntermediateOperand(op.op);
			UseIntermediateOperand(op.tag);
		END UseOperand;

		(* save registers marked in array "markedRegisters" to the stack
			remove entries from array "markedRegisters" and save to array "saved" (=> recursion possible)
		*)
		PROCEDURE SaveRegisters(VAR saved: Registers);
		VAR i: SHORTINT; op: IntermediateCode.Operand;
		BEGIN
			FOR i := 1 TO LEN(usedRegisters)-1 DO
				IF usedRegisters[i].count > 0 THEN
					IntermediateCode.InitRegister(op,usedRegisters[i].type,i);
					saved[i] := usedRegisters[i];
					IF TraceRegisters & (dump # NIL) THEN
						dump.String("save register: ");
						IntermediateCode.DumpType(dump,usedRegisters[i].type);
						IntermediateCode.DumpRegister(dump,i);
					END;
					Emit(Push(op));
				ELSE
					ASSERT(usedRegisters[i].count = 0);
					saved[i].count := 0
				END;
				usedRegisters[i].count := 0;
			END;
		END SaveRegisters;

		(* restore registers from array saved and re-enter into array markedRegisters (recursion possible) *)
		PROCEDURE RestoreRegisters(CONST saved: Registers);
		VAR i: SHORTINT; op: IntermediateCode.Operand;
		BEGIN
			FOR i := LEN(usedRegisters)-1 TO 1 BY -1 DO
				IF usedRegisters[i].count > 0 THEN ErrorI("register not released:",i)
				ELSIF usedRegisters[i].count < 0 THEN ErrorI("register released too often:",i);
				END;
				(*
				Assert(usedRegisters[i].count = 0,"restore registers after register has been acquired");
				*)
				IF saved[i].count > 0  THEN
					IntermediateCode.InitRegister(op,saved[i].type,i);
					usedRegisters[i] := saved[i];
					IF TraceRegisters & (dump # NIL) THEN
						dump.String("restore register: ");
						IntermediateCode.DumpType(dump,usedRegisters[i].type);
						IntermediateCode.DumpRegister(dump,i);
						dump.String("(");
						dump.Int(usedRegisters[i].count,1);
						dump.String(")");
					END;
					Emit(Pop(op));
				END;
			END;
		END RestoreRegisters;

		PROCEDURE CheckRegistersFree;
		VAR i: SHORTINT;
		BEGIN
			FOR i := 0 TO LEN(usedRegisters)-1 DO
				IF usedRegisters[i].count # 0 THEN
					IF (dump # NIL) THEN
						dump.String("implementation error: register not released: ");
						IntermediateCode.DumpType(dump,usedRegisters[i].type);
						IntermediateCode.DumpRegister(dump,i);
						dump.String("(");
						dump.Int(usedRegisters[i].count,1);
						dump.String(")");
						dump.Ln;
						dump.Update;
					END;
					Error("register not released");
					usedRegisters[i].count := 0
				END;
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
				ELSE
					IntermediateCode.InitRegister(new,type,AcquireRegister(type));
					ReleaseIntermediateOperand(operand);
				END;
				Emit(Conv(new,operand));
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
		PROCEDURE VisitSet(x: SyntaxTree.Set);
		VAR left,right,res: Operand; e: SyntaxTree.Expression; i: LONGINT; temp,allBits,noBits,one,size: IntermediateCode.Operand;
			dest: IntermediateCode.Operand;

			PROCEDURE CheckSetElement(o: Operand);
			VAR max: IntermediateCode.Operand;
			BEGIN
				IF o.op.mode # IntermediateCode.ModeImmediate THEN (* otherwise it's the job of the checker *)
					IntermediateCode.InitImmediate(max,setType,setType.sizeInBits (* number of bits in set *) -1);
					TrapC(BrgeL,max,o.op,SetElementTrap);
				END;
			END CheckSetElement;

		BEGIN
			IF Trace THEN TraceEnter("VisitSet") END;
			dest := destination; destination := emptyOperand;
			InitOperand(res,ModeValue);
			IntermediateCode.InitImmediate(allBits,setType,-1);  (* bit mask 111...11111 *)
			IntermediateCode.InitImmediate(noBits,setType,0);  (* bit mask 0...0 *)
			IntermediateCode.InitImmediate(one,setType,1);
			IntermediateCode.InitRegister(res.op,setType,AcquireRegister(setType));
			Emit(Mov(res.op,noBits));
			FOR i := 0 TO x.elements.Length()-1 DO
				e := x.elements.GetExpression(i);
				IF (e IS SyntaxTree.RangeExpression) THEN
					Evaluate(e,left); right := left; right.op := left.tag; IntermediateCode.InitOperand(left.tag); IntermediateCode.InitOperand(right.tag);
					Convert(right.op,setType); Convert(left.op,setType);
					(* perform bitshifts of 111111111111 by left and right and perform AND operation *)
					CheckSetElement(left);
					Reuse1(temp,left.op);
					Emit(Shl(temp,allBits,left.op));
					ReleaseIntermediateOperand(left.op);
					left.op := temp;
					CheckSetElement(right);
					IF (right.op.mode = IntermediateCode.ModeImmediate) & (right.op.symbol = NIL) THEN
						IntermediateCode.InitImmediate(right.op,right.op.type,left.op.type.sizeInBits-1-right.op.intValue);
						Reuse1(temp,right.op);
					ELSE
						Reuse1(temp,right.op);
						IntermediateCode.InitImmediate(size,right.op.type,left.op.type.sizeInBits-1);
						Emit(Sub(temp,size,right.op));
					END;
					Emit(Shr(temp,allBits,right.op));
					ReleaseIntermediateOperand(right.op);
					right.op := temp;
					Reuse2(temp,left.op,right.op);
					Emit(And(temp,left.op,right.op));
					Emit(Or(res.op,res.op,temp));
					ReleaseIntermediateOperand(temp);
					ReleaseOperand(left);
					ReleaseOperand(right);
				ELSE
					Evaluate(e,left);
					Convert(left.op,setType);
					CheckSetElement(left);
					Reuse1(temp,left.op);
					Emit(Shl(temp,one,left.op));
					Emit(Or(res.op,res.op,left.op));
					ReleaseIntermediateOperand(temp);
					ReleaseOperand(left);
				END;
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
			variable := GetTemporaryVariable(x.type,x.position);
			designator := SyntaxTree.NewSymbolDesignator(-1,NIL,variable);
			designator.SetType(variable.type);
			dim := SemanticChecker.Dimension(x.type,{SyntaxTree.Static});
			index := SyntaxTree.NewIndexDesignator(x.position,designator);
			FOR i := 0 TO dim-1 DO
				element := SyntaxTree.NewIntegerValue(x.position,0);
				element.SetType(Global.Longint);
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
				IF type = Global.Set THEN
					Emit(Not(result.op,operand.op));
				ELSIF type IS SyntaxTree.NumberType THEN
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
			BrL(falseL);
			ReleaseIntermediateOperand(left); ReleaseIntermediateOperand(right);
		END TypeTest;

		PROCEDURE Error(CONST s: ARRAY OF CHAR);
		BEGIN
			IF diagnostics # NIL THEN
				diagnostics.Error(module.module.sourceName,position,Diagnostics.Invalid,s);
			END;
			IF dump # NIL THEN
				dump.String(s); dump.Ln;
			END;
			error := TRUE;
		END Error;

		PROCEDURE ErrorI(CONST s: ARRAY OF CHAR; i: LONGINT);
		VAR msg: SyntaxTree.String;
		BEGIN
			COPY(s,msg);
			Basic.AppendNumber(msg,i);
			Error(msg);
		END ErrorI;

		PROCEDURE AddImport(CONST moduleName: ARRAY OF CHAR; VAR module: SyntaxTree.Module; force: BOOLEAN): BOOLEAN;
		VAR import: SyntaxTree.Import;
			s: Scanner.StringType;
			selfName: SyntaxTree.String;
		BEGIN
			moduleScope.ownerModule.name.GetString(selfName);
			IF moduleName = selfName THEN
				module := moduleScope.ownerModule
			ELSE
				import := moduleScope.ImportByModuleName(SyntaxTree.NewIdentifier(-1,moduleName),SyntaxTree.NewIdentifier(-1,"A2"));
				IF import = NIL THEN
					import := SyntaxTree.NewImport(-1,SyntaxTree.NewIdentifier(-1,moduleName),SyntaxTree.NewIdentifier(-1,moduleName),TRUE);
					import.SetContext(SyntaxTree.NewIdentifier(-1,"A2"));
					IF ~checker.AddImport(moduleScope.ownerModule,import) OR (import.module = NIL) THEN
						IF force THEN
							s := "Module ";
							Strings.Append(s,moduleName);
							Strings.Append(s," cannot be imported.");
							Error(s);
						END;
						RETURN FALSE
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
			saved: Registers;
			s: Scanner.StringType;
			reg: IntermediateCode.Operand;
			prevResult: Operand;
		BEGIN
			IF AddImport(moduleName,machine,TRUE) THEN
				IF x.op1.register > 0 THEN
					ReleaseRegister(x.op1.register); (* avoid push on acquired but not yet set destination register *)
				END;
				SaveRegisters(saved);
				procedure := machine.moduleScope.FindProcedure(SyntaxTree.NewIdentifier(-1,procedureName));
				IF procedure = NIL THEN
					s := "Instruction not supported on target, emulation procedure ";
					Strings.Append(s,moduleName);
					Strings.Append(s,".");
					Strings.Append(s,procedureName);
					Strings.Append(s," not present");
					Error(s);
				ELSE
					IF x.op2.mode # IntermediateCode.Undefined THEN
						Emit(Push(x.op2));
					END;
					IF x.op3.mode # IntermediateCode.Undefined THEN
						Emit(Push(x.op3));
					END;
					prevResult := result;
					StaticCallOperand(result,procedure);
					Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
					result := prevResult;
				END;
				RestoreRegisters(saved);
				IF x.op1.register > 0 THEN
					UseRegister(x.op1.register);
				END;
				IntermediateCode.InitRegister(reg,x.op1.type,IntermediateCode.Result);
				Emit(Mov(x.op1,reg));
			END;
		END Emulate;

		PROCEDURE SysCall(nr: LONGINT);
		VAR op: IntermediateCode.Operand; name: SyntaxTree.String; section: IntermediateCode.Section;
		BEGIN
			systemCalls[nr].name.GetString(name);
			section := IntermediateCode.NewSection(module.systemCalls,Sections.CodeSection,name,systemCalls[nr],commentPrintout # NIL);
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
			IntermediateCode.InitRegister(result.op,GetType(system,x.type),AcquireRegister(GetType(system,x.type)));
			Emit(Mov(result.op,true));
			BrL(exit);
			SetLabel(falseL);
			Emit(Mov(result.op,false));
			SetLabel(exit);
		END ConditionToValue;

		PROCEDURE ValueToCondition(VAR op: Operand);
		BEGIN
			LoadValue(op,Global.Boolean);
			BrneL(trueLabel,op.op, false);
			BrL(falseLabel);
			ReleaseOperand(op);
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

		PROCEDURE GetRuntimeProcedure(CONST moduleName, procedureName: ARRAY OF CHAR; VAR procedure: SyntaxTree.Procedure; force: BOOLEAN): BOOLEAN;
		VAR runtimeModule: SyntaxTree.Module; s: Scanner.StringType;
		BEGIN
			IF AddImport(moduleName,runtimeModule,force) THEN
				procedure := runtimeModule.moduleScope.FindProcedure(SyntaxTree.NewIdentifier(-1,procedureName));
				IF procedure = NIL THEN
					s := "Procedure ";
					Strings.Append(s,moduleName);
					Strings.Append(s,".");
					Strings.Append(s,procedureName);
					Strings.Append(s," not present");
					Error(s);
					RETURN FALSE
				ELSE
					RETURN TRUE
				END;
			ELSE RETURN FALSE
			END;
		END GetRuntimeProcedure;

		PROCEDURE GetModulesModule(): IntermediateCode.Section;
		VAR importedModule: SyntaxTree.Module; source: IntermediateCode.Section; symbol: SyntaxTree.Symbol; name: ARRAY 32 OF CHAR;
		BEGIN
			name := "Modules.Module";
			IF AddImport("Modules",importedModule, FALSE) THEN
				symbol := importedModule.moduleScope.FindTypeDeclaration(SyntaxTree.NewIdentifier(-1,"Module"));
				IF symbol = NIL THEN
					Error(" not present in module Modules");
				END;
			ELSE symbol := NIL;
			END;
			IF importedModule = moduleScope.ownerModule THEN
				source := IntermediateCode.NewSection(module.sections, Sections.ConstSection, name, symbol, commentPrintout # NIL);
			ELSE
				source := IntermediateCode.NewSection(module.importedSymbols, Sections.ConstSection, name, symbol, commentPrintout # NIL);
			END;
			RETURN source
		END GetModulesModule;


		PROCEDURE CallThis(CONST moduleName, procedureName: ARRAY OF CHAR);
		VAR procedure: SyntaxTree.Procedure; result: Operand; reg: IntermediateCode.Operand; source: IntermediateCode.Section;
			name: SyntaxTree.String;
		BEGIN
			IF GetRuntimeProcedure(moduleName,procedureName,procedure,FALSE) THEN (* ready for dynamic linking *)
				StaticCallOperand(result,procedure);
				Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
				ReleaseOperand(result);
			ELSE (* only static linking possible *)
				COPY(moduleName, name); Strings.Append(name,"."); Strings.Append(name,procedureName);
				source := IntermediateCode.NewSection(module.importedSymbols, Sections.CodeSection,name, NIL,commentPrintout # NIL);
				IntermediateCode.InitAddress(reg, addressType, source , 0);
				Emit(Call(reg, 0));
			END;
		END CallThis;

		PROCEDURE CallThis2(CONST moduleName, procedureName,altModuleName, altProcedureName: ARRAY OF CHAR);
		VAR procedure: SyntaxTree.Procedure; result: Operand; reg: IntermediateCode.Operand; source: IntermediateCode.Section;
			name: SyntaxTree.String;
		BEGIN
			IF GetRuntimeProcedure(moduleName,procedureName,procedure,FALSE) THEN (* ready for dynamic linking *)
				StaticCallOperand(result,procedure);
				Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
				ReleaseOperand(result);
			ELSE (* only static linking possible *)
				COPY(altModuleName, name); Strings.Append(name,"."); Strings.Append(name,altProcedureName);
				source := IntermediateCode.NewSection(module.importedSymbols, Sections.CodeSection,name, NIL,commentPrintout # NIL);
				IntermediateCode.InitAddress(reg, addressType, source , 0);
				Emit(Call(reg, 0));
			END;
		END CallThis2;






		PROCEDURE CompareString(br: ConditionalBranch; leftExpression,rightExpression: SyntaxTree.Expression);
		VAR
			left,right: Operand;
			leftSize, rightSize: IntermediateCode.Operand;
			procedure: SyntaxTree.Procedure;
			saved: Registers;
			reg: IntermediateCode.Operand;
			procedureName: SyntaxTree.String;
		BEGIN
			procedureName := "CompareString";

			IF GetRuntimeProcedure(runtimeModuleName,procedureName,procedure,TRUE) THEN
				SaveRegisters(saved);
				Designate(leftExpression,left);
				leftSize := GetDynamicSize(leftExpression.type,left.tag);
				Emit(Push(leftSize));
				Emit(Push(left.op));
				ReleaseOperand(left);
				ReleaseIntermediateOperand(leftSize);

				Designate(rightExpression,right);
				rightSize := GetDynamicSize(rightExpression.type,right.tag);
				Emit(Push(rightSize));
				Emit(Push(right.op));
				ReleaseOperand(right);
				ReleaseIntermediateOperand(rightSize);

				StaticCallOperand(result,procedure);
				Emit(Call(result.op,ProcedureParametersSize(system,procedure)));
				RestoreRegisters(saved); (* must be done before use of result, might be jumped over otherwise *)
				IntermediateCode.InitRegister(reg,int8,IntermediateCode.Result);

				br(trueLabel,reg,IntermediateCode.Immediate(int8,0));
				BrL(falseLabel);
				ReleaseOperand(result);
			END;
		END CompareString;

		PROCEDURE CopyString(leftExpression,rightExpression: SyntaxTree.Expression);
		VAR
			left,right: Operand;
			leftSize, rightSize: IntermediateCode.Operand;
			procedure: SyntaxTree.Procedure;
			saved: Registers;
			procedureName: SyntaxTree.String;
		BEGIN
			procedureName := "CopyString";

			IF GetRuntimeProcedure(runtimeModuleName,procedureName,procedure,TRUE) THEN
				SaveRegisters(saved);
				Designate(leftExpression,left);
				leftSize := GetDynamicSize(leftExpression.type,left.tag);
				Emit(Push(leftSize));
				Emit(Push(left.op));
				ReleaseOperand(left);
				ReleaseIntermediateOperand(leftSize);

				Designate(rightExpression,right);
				rightSize := GetDynamicSize(rightExpression.type,right.tag);
				Emit(Push(rightSize));
				Emit(Push(right.op));
				ReleaseOperand(right);
				ReleaseIntermediateOperand(rightSize);

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
				IF leftType = Global.Set THEN
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
				IF leftType = Global.Set THEN
					InitOperand(result,ModeValue);
					Reuse1(result.op,right.op);
					Emit(Not(result.op,right.op));
					Emit(And(result.op,result.op,left.op));
				ELSE
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(Sub(result.op,left.op,right.op));
				END;
				ReleaseOperand(left); ReleaseOperand(right);
			|Scanner.Times:
				Evaluate(x.left,left);
				Evaluate(x.right,right);
				IF leftType = Global.Set THEN
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(And(result.op,left.op,right.op));
				ELSIF (x.type.resolved IS SyntaxTree.IntegerType) & IsIntegerConstant(x.right,value) & PowerOf2(value,exp) THEN
					InitOperand(result,ModeValue);
					Reuse1a(result.op,left.op,dest);
					IntermediateCode.InitImmediate(right.op,GetType(system,rightType),exp);
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
					IntermediateCode.InitImmediate(right.op,GetType(system,rightType),exp);
					Emit(Shr(result.op,left.op,right.op));
				ELSE
					IF (x.type.resolved IS SyntaxTree.IntegerType) & (x.right.resolved = NIL) THEN (* divisor negative check *)
						exit := NewLabel();
						IntermediateCode.InitImmediate(zero,GetType(system,rightType),0);
						BrltL(exit,zero,right.op);
						Emit(Trap(NegativeDivisorTrap));
						SetLabel(exit);
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
					IntermediateCode.InitImmediate(right.op,GetType(system,x.type),value-1);
					InitOperand(result,ModeValue);
					Reuse1a(result.op,left.op,dest);
					Emit(And(result.op,left.op,right.op));
				ELSE
					IF (x.type.resolved IS SyntaxTree.IntegerType) & (x.right.resolved = NIL) THEN (* divisor negative check *)
						exit := NewLabel();
						IntermediateCode.InitImmediate(zero,GetType(system,rightType),0);
						BrltL(exit,zero,right.op);
						Emit(Trap(NegativeDivisorTrap));
						SetLabel(exit);
					END;
					InitOperand(result,ModeValue);
					Reuse2a(result.op,left.op,right.op,dest);
					Emit(Mod(result.op,left.op,right.op));
				END;
				ReleaseOperand(left); ReleaseOperand(right);
			|Scanner.Slash:
				Evaluate(x.left,left);
				Evaluate(x.right,right);
				IF leftType = Global.Set THEN
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
					BrneL(falseLabel,left.op,right.op); (* inverse evaluation to optimize jumps for true case *)
					BrL(trueLabel);
					ReleaseOperand(left); ReleaseOperand(right);
				END;
			|Scanner.LessEqual:
				IF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BrgeL,x.right,x.left);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					IF leftType = Global.Set THEN (* left subsetequal right: left \cap right = left  *)
						Reuse1(temp.op,right.op);
						Emit(And(temp.op,left.op,right.op));
						BreqL(trueLabel,temp.op,left.op);
						BrL(falseLabel);
						ReleaseOperand(temp);
					ELSE
						BrltL(falseLabel,right.op,left.op); (* inverse evaluation to optimize jumps for true case *)
						BrL(trueLabel);
					END;
					ReleaseOperand(left); ReleaseOperand(right);
				END;
			|Scanner.Less:
				IF leftType = Global.Set THEN (* left < right <=> left <= right & left # right *)
					leftExpression := SyntaxTree.NewBinaryExpression(-1,x.left,x.right,Scanner.LessEqual);
					leftExpression.SetType(Global.Boolean);
					rightExpression := SyntaxTree.NewBinaryExpression(-1,x.left,x.right,Scanner.Unequal);
					rightExpression.SetType(Global.Boolean);
					leftExpression := SyntaxTree.NewBinaryExpression(-1,leftExpression,rightExpression,Scanner.And);
					leftExpression.SetType(Global.Boolean);
					Expression(leftExpression);
				ELSIF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BrltL,x.left,x.right);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					BrgeL(falseLabel,left.op,right.op); (* inverse evaluation to optimize jumps for true case *)
					BrL(trueLabel);
					ReleaseOperand(left); ReleaseOperand(right);
				END;
			|Scanner.Greater:
				IF leftType = Global.Set THEN (* left > right <=> left >= right & left # right  *)
					leftExpression := SyntaxTree.NewBinaryExpression(-1,x.left,x.right,Scanner.GreaterEqual);
					leftExpression.SetType(Global.Boolean);
					rightExpression := SyntaxTree.NewBinaryExpression(-1,x.left,x.right,Scanner.Unequal);
					rightExpression.SetType(Global.Boolean);
					leftExpression := SyntaxTree.NewBinaryExpression(-1,leftExpression,rightExpression,Scanner.And);
					leftExpression.SetType(Global.Boolean);
					Expression(leftExpression);
				ELSIF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BrltL,x.right,x.left);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					BrgeL(falseLabel, right.op,left.op); (* inverse evaluation to optimize jumps for true case *)
					BrL(trueLabel);
					ReleaseOperand(left); ReleaseOperand(right);
				END;
			|Scanner.GreaterEqual:
				IF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BrgeL,x.left,x.right);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					IF leftType = Global.Set THEN (* left supsetequal right: left \cap right = right *)
						Reuse1(temp.op,left.op);
						Emit(And(temp.op,left.op,right.op));
						BreqL(trueLabel, temp.op,right.op);
						BrL(falseLabel);
						ReleaseOperand(temp);
					ELSE
						BrltL(falseLabel, left.op,right.op); (* inverse evaluation to optimize jumps for true case *)
						BrL(trueLabel);
					END;
					ReleaseOperand(left); ReleaseOperand(right);
				END;
			|Scanner.Unequal:
				IF ~conditional THEN ConditionToValue(x);
				ELSIF (leftType IS SyntaxTree.ArrayType) OR (leftType IS SyntaxTree.StringType) THEN (* string comparison *)
					CompareString(BrneL,x.left,x.right);
				ELSE
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					BreqL(falseLabel,left.op,right.op); (* inverse evaluation to optimize jumps for true case *)
					BrL(trueLabel);
					ReleaseOperand(left); ReleaseOperand(right);
				END;
			|Scanner.In:
				IF ~conditional THEN ConditionToValue(x);
				ELSE
					ASSERT(rightType.resolved = Global.Set);
					Evaluate(x.left,left);
					Evaluate(x.right,right);
					Convert(left.op,setType);
					Reuse1(temp.op,left.op);
					IntermediateCode.InitImmediate(one,setType,1);
					Emit(Shl(temp.op,one,left.op));
					Emit(And(temp.op,temp.op,right.op));
					IntermediateCode.InitImmediate(zero,setType,0);
					BrneL(trueLabel,temp.op,zero);
					BrL(falseLabel);
					ReleaseOperand(left); ReleaseOperand(right); ReleaseOperand(temp);
				END;
			ELSE
				HALT(100);
			END;
			destination := dest;
			IF Trace THEN TraceExit("VisitBinaryExpression") END;
		END VisitBinaryExpression;

		PROCEDURE VisitRangeExpression(x: SyntaxTree.RangeExpression);
		VAR from,to: Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitRangeExpression") END;
			IF x.from = NIL THEN
				InitOperand(from,ModeValue);
				from.op := IntermediateCode.Immediate(int32,0)
			ELSE
				Evaluate(x.from,from);
			END;
			IF x.to = NIL THEN
				InitOperand(to,ModeValue);
				(* must be catched by IndexDesignator
				to.op := IntermediateCode.Immediate(int32,MAX(LONGINT));
				*)
			ELSE
				Evaluate(x.to,to);
			END;
			InitOperand(result,ModeValue);
			result.op := from.op;
			result.tag := to.op;
			UseOperand(result); ReleaseOperand(from); ReleaseOperand(to);
			IF Trace THEN TraceExit("Visitp") END;
		END VisitRangeExpression;

		PROCEDURE VisitTensorRangeExpression*(x: SyntaxTree.TensorRangeExpression);
		BEGIN
			HALT(100); (* should never be evaluated *)
		END VisitTensorRangeExpression;

		PROCEDURE VisitConversion(x: SyntaxTree.Conversion);
		VAR old: Operand; dest: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitConversion") END;
			dest := destination; destination := emptyOperand;
			Evaluate(x.expression,old);
			InitOperand(result,ModeValue);
			result.op := old.op;
			Convert(result.op,GetType(system,x.type));
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
			IF tagsAvailable THEN
				TrapC(BrltL,index,length,IndexCheckTrap);
			END;
		END BoundCheck;

		PROCEDURE DimensionCheck(base,dim: IntermediateCode.Operand; op: ConditionalBranch );
		VAR d: IntermediateCode.Operand;
		BEGIN
			MakeMemory(d,base,dim.type,ToMemoryUnits(system,MathDimOffset * addressType.sizeInBits));
			TrapC(op,dim,d,ArraySizeTrap);
			ReleaseIntermediateOperand(d);
		END DimensionCheck;

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

			IF (conditional)  & (type.resolved = Global.Boolean)  THEN
				ValueToCondition(result); (*! wrong as the result of an index designator is always an address *)
			END;
		END MathIndexDesignator;

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

		BEGIN
			type := x.left.type.resolved;
			maxDim := x.parameters.Length()-1;
			FOR i := 0 TO maxDim DO
				e := x.parameters.GetExpression(i);
				Evaluate(e,index);
				Convert(index.op,addressType);
				IF i = 0 THEN
					ReuseCopy(res,index.op);
				ELSE
					Emit(Add(res,res,index.op));
				END;

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
					Emit(Mul(res,res,length));
				END;
			END;
			IF (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form # SyntaxTree.Static) THEN
				size := StaticSize(type);
				IF size # 1 THEN
					length := IntermediateCode.Immediate(addressType,size);
					Emit(Mul(res,res,length));
				END;
			END;
			Emit(Add(res,res,array.op));
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

			IF (conditional)  & (type.resolved = Global.Boolean)  THEN
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
			moduleName, procedureName: SyntaxTree.String; arrayBase: SyntaxTree.Module; saved: Registers; s: SyntaxTree.String;
			procedure: SyntaxTree.Procedure;
			parameters: SyntaxTree.ExpressionList; e: SyntaxTree.Expression;
			prefixIndices, prefixRanges, suffixIndices, suffixRanges,i : LONGINT; tensorFound: BOOLEAN;
		BEGIN
			variable := GetTemporaryVariable(expression.left.type,expression.position);
			parameters := expression.parameters;

			moduleName := "OCArrayBase";
			procedureName := "CopyDescriptor";
			IF AddImport(moduleName,arrayBase,TRUE) THEN
				SaveRegisters(saved);
				procedure := arrayBase.moduleScope.FindProcedure(SyntaxTree.NewIdentifier(-1,procedureName));
				IF procedure = NIL THEN
					s := "procedure ";
					Strings.Append(s,moduleName);
					Strings.Append(s,".");
					Strings.Append(s,procedureName);
					Strings.Append(s," not present");
					Error(s);
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

		PROCEDURE PushParameter(expression: SyntaxTree.Expression; parameter: SyntaxTree.Parameter; flags: SET);
		VAR type: SyntaxTree.Type; baseReg,tmp: IntermediateCode.Operand; size: LONGINT; operand,tmpOperand: Operand; variableOp: Operand;
			descriptorType: SyntaxTree.Type; variable: SyntaxTree.Variable; dim,i: LONGINT; dimOp: IntermediateCode.Operand; baseType: SyntaxTree.Type;

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


			IF IsArrayOfSystemByte(parameter.type) THEN
				Designate(expression,operand);
				tmp := GetDynamicSize(type,operand.tag);
				ReleaseIntermediateOperand(operand.tag);
				operand.tag := tmp;
				IF flags * {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag} = {} THEN
					Emit(Push(operand.tag));
				END;
				Emit(Push(operand.op));
			ELSIF IsOpenArray(parameter.type) THEN
				Designate(expression,operand);
				baseReg := operand.tag;
				IF flags * {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag} = {} THEN
					PushArrayLens(parameter.type,type,operand.dimOffset+DynamicDim(parameter.type)-1);
				END;
				Emit(Push(operand.op)); (* address of the array *)
			ELSIF parameter.type.resolved IS SyntaxTree.MathArrayType THEN
				(* case 1 *)
				IF (parameter.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Open) & (parameter.kind IN {SyntaxTree.ValueParameter, SyntaxTree.ConstParameter}) THEN
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
					(* case 1d *)
					ELSIF type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
						Designate(expression,operand);
						Dereference(operand,type.resolved);
						DimensionCheck(operand.tag, IntermediateCode.Immediate(int32,dim),BreqL);
						Emit(Copy(arrayDestinationTag,operand.tag,IntermediateCode.Immediate(addressType,size)));
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
						variable := GetTemporaryVariable(descriptorType,expression.position);
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
							variable := GetTemporaryVariable(descriptorType,expression.position);
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
						variable := GetTemporaryVariable(descriptorType,expression.position);
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
							LoadValue(variableOp,Global.Address);
						ELSE
							descriptorType := GetMathArrayDescriptorType(dim);
							variable := GetTemporaryVariable(descriptorType,expression.position);
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
							variable := GetTemporaryVariable(descriptorType,expression.position);
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
						variable := GetTemporaryVariable(descriptorType,expression.position);
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
							LoadValue(variableOp,Global.Address);
						ELSE
							descriptorType := GetMathArrayDescriptorType(dim);
							variable := GetTemporaryVariable(descriptorType,expression.position);
							Symbol(variable,variableOp);
						END;
						arrayDestinationTag := variableOp.op;
						ReuseCopy(arrayDestinationTag,arrayDestinationTag);
						arrayDestinationDimension := 0;
						Designate(expression,operand);
						IF type(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
							Symbol(variable,variableOp);
						ELSE
							variable := GetTemporaryVariable(parameter.type.resolved,expression.position+1);
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
							variable := GetTemporaryVariable(descriptorType,expression.position);
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
						variable := GetTemporaryVariable(parameter.type.resolved,expression.position+1);
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
						variable := GetTemporaryVariable(descriptorType,expression.position);
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
						variable := GetTemporaryVariable(parameter.type.resolved,expression.position+1);
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
						size := ToMemoryUnits(system,system.SizeOf(type));
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
						IF flags * {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag} = {} THEN
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
					IF  flags * {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag} = {} THEN
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
			ReleaseOperand(operand);
			IF Trace THEN TraceExit("PushParameter") END;
		END PushParameter;

		PROCEDURE VisitProcedureCallDesignator(x: SyntaxTree.ProcedureCallDesignator);
		VAR parameters: SyntaxTree.ExpressionList; i, parametersSize: LONGINT;
			procedureType: SyntaxTree.ProcedureType;
			formalParameter: SyntaxTree.Parameter;
			symbol: SyntaxTree.Symbol;
			noPush: Label;
			returnTypeSize,returnTypeOffset: LONGINT;
			structuredReturnType: BOOLEAN;
			reg,size: IntermediateCode.Operand;
			operand: Operand;
			saved: Registers;
			dest : IntermediateCode.Operand; variable: SyntaxTree.Variable;
			d: SyntaxTree.Expression;
		BEGIN
			IF Trace THEN TraceEnter("VisitProcedureCallDesignator") END;
			dest := destination; destination := emptyOperand;
			SaveRegisters(saved);

			procedureType := x.left.type.resolved(SyntaxTree.ProcedureType);
			parameters := x.parameters;

			IF (procedureType.returnType # NIL)
				& ~(procedureType.returnType.resolved IS SyntaxTree.BasicType)
				& ~(procedureType.returnType.resolved IS SyntaxTree.ProcedureType)
				& ~(procedureType.returnType.resolved IS SyntaxTree.PointerType)
				& ~((procedureType.returnType.resolved IS SyntaxTree.RecordType) & (procedureType.returnType.resolved(SyntaxTree.RecordType).pointerType # NIL))
			THEN
				variable := GetTemporaryVariable(procedureType.returnType,x.position);
				returnTypeOffset := variable.offsetInBits;
				structuredReturnType := TRUE;
				returnTypeSize := system.SizeOf(procedureType.returnType.resolved);
				(*
				currentSize := currentSize + returnTypeSize;
				IF currentSize > maxSize THEN maxSize := currentSize END;
				returnTypeOffset := -currentSize;
				*)
			ELSE
				structuredReturnType := FALSE;
			END;
			IF structuredReturnType THEN
				reg := fp; IntermediateCode.AddOffset(reg,ToMemoryUnits(system,returnTypeOffset));
				size := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,returnTypeSize));
				d := SyntaxTree.NewSymbolDesignator(-1,NIL,variable);
				d.SetType(variable.type);
				IF procedureType.returnParameter # NIL THEN
					PushParameter(d,procedureType.returnParameter,procedureType.flags)
				ELSE
			 		Emit(Push(size));
			 		Emit(Push(reg));
		 		END;
		 	END;

			IF procedureType.flags * {SyntaxTree.CFlag,SyntaxTree.WinAPIFlag} # {}  THEN
				formalParameter := procedureType.lastParameter;
				FOR i := parameters.Length()-1 TO 0 BY -1 DO
					PushParameter(parameters.GetExpression(i), formalParameter,procedureType.flags);
					formalParameter := formalParameter.prevParameter;
				END;
			ELSE
				formalParameter := procedureType.firstParameter;
				FOR i := 0 TO parameters.Length()-1 DO
					PushParameter(parameters.GetExpression(i), formalParameter,procedureType.flags);
					formalParameter := formalParameter.nextParameter;
				END;
			END;

			IF x.left IS SyntaxTree.SupercallDesignator THEN
				symbol := x.left(SyntaxTree.SupercallDesignator).left(SyntaxTree.SymbolDesignator).symbol;
			ELSIF x.left IS SyntaxTree.IndexDesignator THEN
				symbol := x.left(SyntaxTree.IndexDesignator).left(SyntaxTree.SymbolDesignator).symbol;
			ELSE
				symbol := x.left(SyntaxTree.SymbolDesignator).symbol;
			END;

			Evaluate(x.left,operand);
			IF symbol IS SyntaxTree.Procedure THEN
				IF (symbol.scope IS SyntaxTree.ProcedureScope) THEN (* nested procedure *)
					GetBaseRegister(reg,currentScope,symbol.scope); (* static link, may be fp or [fp+8] (if nested proc calls itself) *)
					Emit(Push(reg));
					ReleaseIntermediateOperand(reg);
				END;
				(*! done in frontend, better do it here?
				IF SemanticChecker.ContainsPointer(procedureType.returnType) THEN
					IF (procedureType.returnType.resolved IS SyntaxTree.RecordType) &(procedureType.returnType.resolved(SyntaxTree.RecordType).pointerType=NIL) THEN
						Emit(Push(nil)); (*! replace by record type descriptor *)
					END;
					Emit(Push(nil)); (*! replace by pointer *)
				END;
				*)

				IF x.left IS SyntaxTree.SupercallDesignator THEN
					Emit(Push(operand.tag));
					parametersSize := ProcedureParametersSize(system,symbol(SyntaxTree.Procedure));
				ELSIF (SyntaxTree.DelegateFlag IN procedureType.flags) THEN
					Emit(Push(operand.tag));
					parametersSize := ProcedureParametersSize(system,symbol(SyntaxTree.Procedure));
				ELSE
					parametersSize := ProcedureParametersSize(system,symbol(SyntaxTree.Procedure));
				END;
			ELSIF (symbol IS SyntaxTree.Variable) OR (symbol IS SyntaxTree.Parameter) THEN
				(*! done in frontend, better do it here?
				IF SemanticChecker.ContainsPointer(procedureType.returnType) THEN
					Emit(Push(nil)); (*! replace by pointer *)
					IF (procedureType.returnType.resolved IS SyntaxTree.RecordType)  &(procedureType.returnType.resolved(SyntaxTree.RecordType).pointerType=NIL) THEN
						Emit(Push(nil)); (*! replace by pointer *)
					END;
				END;
				*)
				IF (SyntaxTree.DelegateFlag IN procedureType.flags) THEN
					noPush := NewLabel();
					BreqL(noPush,operand.tag,nil);
					Emit(Push(operand.tag));
					SetLabel(noPush);
				END;
				parametersSize := ParametersSize(system,procedureType,FALSE);
			ELSE HALT(200);
			END;
			Emit(Call(operand.op,parametersSize));
			ReleaseOperand(operand);
			IF SyntaxTree.CFlag IN procedureType.flags THEN
				size := IntermediateCode.Immediate(addressType,parametersSize);
				Emit(Add(sp,sp,size));
			END;
			RestoreRegisters(saved);
			IF procedureType.returnType # NIL THEN
				IF structuredReturnType THEN
					(*
					size := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.addressSize*2));
					*)
					(* done in callee ...
					Emit(Add(sp,sp,size));
					*)
					IF procedureType.returnParameter # NIL THEN
						size := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOfParameter(procedureType.returnParameter)));
						Emit(Add(sp,sp,size));
					END;
					InitOperand(result,ModeReference);
					Symbol(variable,result);
					(*
					reg := fp;
					IntermediateCode.AddOffset(reg,ToMemoryUnits(system,returnTypeOffset));
					result.op := reg;
					IF procedureType.returnType.resolved IS SyntaxTree.RecordType THEN
						result.tag := TypeDescriptorAdr(procedureType.returnType.resolved);
					END;
					*)
				ELSE
					InitOperand(result,ModeValue);
					IntermediateCode.InitRegister(reg,GetType(system,procedureType.returnType),IntermediateCode.Result);
					IntermediateCode.InitRegister(result.op,GetType(system,procedureType.returnType),AcquireRegister(GetType(system,procedureType.returnType)));
					Emit(Mov(result.op,reg));
					IF IsDelegate(procedureType.returnType) THEN
						IntermediateCode.InitRegister(reg,addressType,IntermediateCode.Result2);
						IntermediateCode.InitRegister(result.tag,addressType,AcquireRegister(addressType));
						Emit(Mov(result.tag,reg));
					END;
				END;
			END;

			IF conditional & (procedureType.returnType # NIL) & (procedureType.returnType.resolved = Global.Boolean) THEN
				ValueToCondition(result);
			END;
			destination := dest;
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
					variable := SyntaxTree.NewVariable(-1,SyntaxTree.NewIdentifier(-1,"@Any"));
					variable.SetType(Global.Any);
					scope.AddVariable(variable);
					hiddenPointerType := SyntaxTree.NewRecordType(-1,NIL,scope);
					typeDeclaration := SyntaxTree.NewTypeDeclaration(-1,SyntaxTree.NewIdentifier(-1,"@HdPtrDesc"));
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
					variable := SyntaxTree.NewVariable(-1,SyntaxTree.NewIdentifier(-1,"@Procedure"));
					variable.SetType(SyntaxTree.NewProcedureType(-1,NIL));
					scope.AddVariable(variable);
					variable := SyntaxTree.NewVariable(-1,SyntaxTree.NewIdentifier(-1,"@Any"));
					variable.SetType(Global.Any);
					scope.AddVariable(variable);
					delegatePointerType := SyntaxTree.NewRecordType(-1,NIL,scope);
					typeDeclaration := SyntaxTree.NewTypeDeclaration(-1,SyntaxTree.NewIdentifier(-1,"@Delegate"));
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
				name: SyntaxTree.String; op: IntermediateCode.Operand;
			BEGIN (* no code emission *)
				source := NIL;
				x := x.resolved;
				IF (x = Global.Any) OR (x IS SyntaxTree.PointerType) THEN
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
					Global.GetSymbolName(td,name);
					IF (td.scope = NIL) OR (td.scope.ownerModule = module.module) THEN
						CheckTypeDeclaration(SELF, module,x,commentPrintout # NIL, newObjectFile);
						source := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,td,commentPrintout # NIL);
					ELSE
						source := IntermediateCode.NewSection(module.importedSymbols,Sections.ConstSection,name,td,commentPrintout # NIL);
					END;
					offset := ToMemoryUnits(system,(1+x(SyntaxTree.RecordType).recordScope.numberMethods+16+1)*system.addressSize);
				ELSE
					source := module.sections.FindBySymbol(td);
					IF source = NIL THEN
						null := 0;
						Global.GetSymbolName(td,name);
						source := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,td,commentPrintout # NIL);
						IntermediateCode.InitImmediate(op,addressType,0);
						source(IntermediateCode.Section).Emit(Data(op));
						source.SetReferenced(FALSE);
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

		PROCEDURE SystemTrace(x: SyntaxTree.Expression);
		VAR
			traceModule: SyntaxTree.Module;
			procedure: SyntaxTree.Procedure;
			s,msg: Scanner.StringType;
			res: Operand;
			sv: SyntaxTree.StringValue;
			type: SyntaxTree.Type;
			recordType: SyntaxTree.RecordType;
			printout: Printout.Printer;
			stringWriter: Streams.StringWriter;
		CONST moduleName="KernelLog";

			PROCEDURE GetProcedure(CONST procedureName: ARRAY OF CHAR): BOOLEAN;
			BEGIN
				procedure := traceModule.moduleScope.FindProcedure(SyntaxTree.NewIdentifier(-1,procedureName));
				IF procedure = NIL THEN
					s := "procedure ";
					Strings.Append(s,moduleName);
					Strings.Append(s,".");
					Strings.Append(s,procedureName);
					Strings.Append(s," not present");
					Error(s);
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
					type := SyntaxTree.NewStringType(-1,Strings.Length(s));
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
			IF AddImport(moduleName,traceModule,TRUE) THEN
				module.module.name.GetString(s);
				COPY(s,msg);
				Strings.Append(msg,"@");
				Strings.IntToStr(x.position,s);
				Strings.Append(msg,s);
				Strings.Append(msg,": ");
				NEW(stringWriter,LEN(s));
				printout := Printout.NewPrinter(stringWriter,Printout.SourceCode,FALSE);
				printout.Expression(x);
				stringWriter.Get(s);
				Strings.Append(msg,s);
				Strings.Append(msg,"= ");
				String(msg);
				IF SemanticChecker.IsStringType(x.type) THEN
					Designate(x,res);
					StringOperand(res.op,res.tag);
				ELSE
					Evaluate(x,res);
					IF x.type.resolved IS SyntaxTree.IntegerType THEN
						IF res.op.type.sizeInBits = IntermediateCode.Bits64 THEN
							Hex64(res.op); String("H");
						ELSE
							IF res.op.type.sizeInBits < IntermediateCode.Bits32 THEN
								Convert(res.op,int32);
							END;
							Integer(res.op);
						END;
					ELSIF x.type.resolved = Global.Boolean THEN
						Boolean(res.op);
					ELSIF x.type.resolved = Global.Set THEN
						Set(res.op);
					ELSIF x.type.resolved IS SyntaxTree.FloatType THEN
						IF res.op.type.sizeInBits = IntermediateCode.Bits32 THEN
							Convert(res.op,float64);
						END;
						Float(res.op);
					ELSIF x.type.resolved = Global.Char8 THEN
						Char(res.op);
					ELSIF x.type.resolved = Global.Address THEN
						Address(res.op);String("H");
					ELSIF (x.type.resolved IS SyntaxTree.PointerType) OR IsPointerToRecord(x.type,recordType) THEN
						Address(res.op);String("H");
					ELSE HALT(200);
					END;
				END;
				ReleaseOperand(res);
				Ln;
			END;
		END SystemTrace;

		PROCEDURE InitVariable(VAR variable: SyntaxTree.Variable);
		VAR type,baseType: SyntaxTree.Type; operand: Operand; imm: IntermediateCode.Operand; dim: LONGINT;
		BEGIN
			type := variable.type.resolved;
			IF (type IS SyntaxTree.MathArrayType) THEN
				WITH type: SyntaxTree.MathArrayType DO
					IF type.form = SyntaxTree.Open THEN
						Symbol(variable,operand);
						dim := DynamicDim(type);
						imm := IntermediateCode.Immediate(addressType,dim);
						PutMathArrayField(operand.tag,imm,MathDimOffset);
						baseType := SemanticChecker.ArrayBase(type,dim);
						imm := IntermediateCode.Immediate(addressType,ToMemoryUnits(system,system.SizeOf(baseType)));
						PutMathArrayField(operand.tag,imm,MathElementSizeOffset);
						ReleaseOperand(operand); ReleaseIntermediateOperand(imm);
					END;
				END;
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

		PROCEDURE PutMathArrayField(base,value: IntermediateCode.Operand; offset: LONGINT);
		VAR mem: IntermediateCode.Operand;
		BEGIN
			offset := ToMemoryUnits(system,offset*addressType.sizeInBits);
			MakeMemory(mem,base,addressType,offset);
			Emit(Mov(mem,value));
			ReleaseIntermediateOperand(mem);
		END PutMathArrayField;

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
			IF check & (type.form = SyntaxTree.Tensor) THEN
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
				TrapC(BrltL,dim,IntermediateCode.Immediate(addressType,SemanticChecker.Dimension(type,{SyntaxTree.Open,SyntaxTree.Static})), IndexCheckTrap);

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
		PROCEDURE GetTemporaryVariable(type: SyntaxTree.Type; index: LONGINT): SyntaxTree.Variable;
		VAR name: SyntaxTree.Identifier; string: Scanner.StringType ; variable: SyntaxTree.Symbol;
		scope: SyntaxTree.Scope; duplicate: BOOLEAN; offset: LONGINT;
		BEGIN
			COPY("@hiddenVar",string);
			Basic.AppendNumber(string,SYSTEM.VAL(LONGINT,type));
			IF index # 0 THEN
				Strings.Append(string,":");
				Basic.AppendNumber(string,index);
			END;
			name := SyntaxTree.NewIdentifier(index,string);
			scope := currentScope;
			variable := currentScope.FindVariable(name);
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
				variable := SyntaxTree.NewVariable(-1,SyntaxTree.NewIdentifier(-1,name));
				variable.SetType(type);
				recordScope.AddVariable(variable);
			END AddVariable;
		BEGIN
			name := "@ArrayDescriptor";
			Basic.AppendNumber(name,dimensions);
			identifier := SyntaxTree.NewIdentifier(-1,name);
			parentScope := module.module.moduleScope;
			symbol := parentScope.FindSymbol(identifier);
			IF symbol # NIL THEN
				typeDeclaration := symbol(SyntaxTree.TypeDeclaration);
				type := typeDeclaration.declaredType;
			ELSE
				typeDeclaration := SyntaxTree.NewTypeDeclaration(-1,SyntaxTree.NewIdentifier(-1,name));
				recordScope := SyntaxTree.NewRecordScope(parentScope);
				recordType := SyntaxTree.NewRecordType( -1, parentScope, recordScope);
				recordType.SetTypeDeclaration(typeDeclaration);
				recordType.SetState(SyntaxTree.Resolved);
				typeDeclaration.SetDeclaredType(recordType);
				AddVariable("@ptr",Global.Any);
				AddVariable("@adr",Global.Address);
				AddVariable("@flags",Global.Address);
				AddVariable("@dim",Global.Address);
				AddVariable("@elementSize",Global.Address);
				FOR i := 0 TO dimensions-1  DO
					name := "@len";
					Basic.AppendNumber(name,i);
					AddVariable(name,Global.Address);
					name := "@incr";
					Basic.AppendNumber(name,i);
					AddVariable(name,Global.Address);
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
		VAR p0,p1,p2,parameter: SyntaxTree.Expression; len,val: LONGINT; l,r: Operand; res,adr,reg: IntermediateCode.Operand; type: SyntaxTree.Type;
		constructor: SyntaxTree.Procedure; s0,s1,s2: Operand; hint: HUGEINT;
		i: LONGINT; formalParameter: SyntaxTree.Parameter;
		tmp:IntermediateCode.Operand;
		size: LONGINT; dim,openDim: LONGINT; pointer: IntermediateCode.Operand; t,t0,t1,t2: SyntaxTree.Type; trueL,falseL,ignore: Label;
		exit,else,end: Label; procedureType: SyntaxTree.ProcedureType;
		name: SyntaxTree.String; symbol: Sections.Section; operand: Operand;
		dest: IntermediateCode.Operand;
		staticLength: LONGINT; itype: IntermediateCode.Type;
		convert,isTensor: BOOLEAN;
		flags: SET;

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
				CallBodies(self,type(SyntaxTree.RecordType).baseType);
				recordScope := type(SyntaxTree.RecordType).recordScope;
				IF recordScope.bodyProcedure # NIL THEN
					procedure := recordScope.bodyProcedure;
					body := procedure.procedureScope.body;
					Emit(Push(self));
					IF body.HasFlag(SyntaxTree.ActiveFlag) THEN
						StaticCallOperand(result,procedure);
						Emit(Push(result.op));
						IF body.priority # NIL THEN Evaluate(body.priority,op); priority := op.op;
							Convert(priority,int32);
						ELSE priority := IntermediateCode.Immediate(int32,0)
						END;
						Emit(Push(priority));
						ReleaseIntermediateOperand(priority);
						flags := 0;
						IF body.HasFlag(SyntaxTree.SafeFlag) THEN
							flags := 1;
						END;
						Emit(Push(IntermediateCode.Immediate(GetType(system,Global.Set),flags)));
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
				ELSIF type.resolved = Global.Any THEN Emit(Push(IntermediateCode.Immediate(addressType,1)))
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
				IF (s1.op.mode # IntermediateCode.ModeImmediate) THEN
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
					BrgeL(exit,s1.op,IntermediateCode.Immediate(GetType(system,p1.type),0));
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
				ignore := NewLabel();
				BrltL(ignore, reg,IntermediateCode.Immediate(GetType(system,Global.Char),ORD("a")));
				BrltL(ignore,IntermediateCode.Immediate(GetType(system,Global.Char),ORD("z")),reg);
				Emit(And(reg,reg,IntermediateCode.Immediate(GetType(system,Global.Char),5FH)));
				SetLabel(ignore);
				ReleaseIntermediateOperand(result.op);
				result.op := reg;
			(* ---- CHR ----- *)
			|Global.Chr:
				Evaluate(p0,result);
				Convert(result.op,GetType(system,x.type));
			|Global.Entier, Global.EntierH:
				Evaluate(p0,result);
				Convert(result.op,GetType(system,x.type));
			(* ---- MIN and MAX ----- *)
			|Global.Max,Global.Min:
				Evaluate(p0,s0);
				Evaluate(p1,s1);
				Reuse2(res,s0.op,s1.op);
				else := NewLabel();
				IF x.id = Global.Max THEN BrltL(else,s0.op,s1.op);
				ELSE BrltL(else,s1.op,s0.op) END;
				Emit(Mov(res,s0.op));
				end := NewLabel();
				BrL(end);
				SetLabel(else);
				Emit(MovReplace(res,s1.op));
				SetLabel(end);
				ReleaseOperand(s0); ReleaseOperand(s1);
				InitOperand(result,ModeValue);
				result.op := res;
			(* ---- ODD ----- *)
			|Global.Odd:
				IF ~conditional THEN
					ConditionToValue(x)
				ELSE
					Evaluate(p0,result);
					res := IntermediateCode.Immediate(GetType(system,p0.type),1);
					Reuse1(res,result.op);
					Emit(And(res,result.op,IntermediateCode.Immediate(GetType(system,p0.type),1)));
					ReleaseIntermediateOperand(result.op);
					result.op := res;
					BreqL(trueLabel,IntermediateCode.Immediate(GetType(system,p0.type),1),result.op);
					BrL(falseLabel);
					ReleaseOperand(result);
				END;
			(* ---- ORD ----- *)
			|Global.Ord:
				Evaluate(p0,result);
				Convert(result.op,GetType(system,x.type));
			(* ---- SHORT, LONG ----- *)
			|Global.Short, Global.Long:
				Evaluate(p0,result);
				Convert(result.op,GetType(system,x.type));
			(* ---- HALT, SYSTEM.HALT----- *)
			|Global.Halt, Global.systemHalt:
				Evaluate(p0,result);
				ASSERT(result.op.mode = IntermediateCode.ModeImmediate);
				Emit(Trap(SHORT(result.op.intValue)));
			(* ---- ASSERT ----- *)
			|Global.Assert:
				trueL := NewLabel();
				falseL := NewLabel();
				Condition(p0,trueL,falseL);

				IF p1 = NIL THEN val := AssertTrap
				ELSE val := p1.resolved(SyntaxTree.IntegerValue).value;
				END;

				SetLabel(falseL);
				Emit(Trap(val));
				SetLabel(trueL);

				(*
				Emit(TrapC(result.op,val);
				*)
			(* ---- INC, DEC----- *)
			|Global.Inc,Global.Dec:
				Expression(p0); adr := result.op;
				LoadValue(result,p0.type); l := result;
				IF p1 = NIL THEN r.op := IntermediateCode.Immediate(GetType(system,p0.type),1);
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
				Convert(result.op,GetType(system, x.type));
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
					IF x.hiddenVariable # NIL THEN
						Designate(x.hiddenVariable,l)
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
					IF (SyntaxTree.RealtimeFlag IN type.flags) THEN Emit(Push(true));
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

					(* call initializer *)
					constructor := GetConstructor(p0.type.resolved(SyntaxTree.PointerType).pointerBase.resolved(SyntaxTree.RecordType));
					IF constructor # NIL THEN
						(*! should be unified with ProcedureCallDesignator *)
						formalParameter := constructor.type(SyntaxTree.ProcedureType).firstParameter;
						FOR i := 1 TO x.parameters.Length()-1 DO
							PushParameter(x.parameters.GetExpression(i), formalParameter,{});
							formalParameter := formalParameter.nextParameter;
						END;
						(* static call of the constructor *)
						Emit(Push(pointer));
						ReleaseIntermediateOperand(pointer);
						Global.GetSymbolName(constructor,name);
						ASSERT(~constructor.HasFlag(SyntaxTree.InlineFlag));
						IF constructor.scope.ownerModule # module.module THEN
							symbol := IntermediateCode.NewSection(module.importedSymbols,Sections.CodeSection,name,constructor,commentPrintout # NIL);
						ELSE
							symbol := IntermediateCode.NewSection(module.sections,Sections.CodeSection,name,constructor,commentPrintout # NIL);
						END;
						Emit(Call(IntermediateCode.Address(addressType, symbol,0),ProcedureParametersSize(system,constructor)));
					ELSE
						ReleaseIntermediateOperand(pointer);
					END;

					IntermediateCode.InitRegister(pointer,addressType,AcquireRegister(addressType));
					Emit(Pop(pointer));

					IF x.hiddenVariable # NIL THEN
						Designate(p0,l);
						ToMemory(l.op,addressType,0);
						Emit(Mov(l.op,pointer));
						ReleaseOperand(l);
					END;

					(* call bodies *)
					CallBodies(pointer,p0.type);
					ReleaseIntermediateOperand(pointer);

					IF x.hiddenVariable # NIL THEN
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
							IF r.op.mode # IntermediateCode.ModeImmediate THEN
								IntermediateCode.InitImmediate(tmp,GetType(system,parameter.type),0);
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
						IF (SyntaxTree.RealtimeFlag IN type.flags) THEN Emit(Push(true));
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
						IF (SyntaxTree.RealtimeFlag IN type.flags) THEN Emit(Push(true));
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
						IF r.op.mode # IntermediateCode.ModeImmediate THEN
							IntermediateCode.InitImmediate(tmp,GetType(system,parameter.type),0);
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
					IF SemanticChecker.ContainsPointer(type) THEN
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
						size := ToMemoryUnits(system,system.SizeOf(type));
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
					IntermediateCode.InitImmediate(tmp,addressType,ToMemoryUnits(system,system.SizeOf(type)));
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

				ELSE (* no pointer to record, no pointer to array *)
					HALT(200);
				END;
			(* ---- SYSTEM.ADR----- *)
			|Global.systemAdr:
				Designate(p0,s0);
				s0.mode := ModeValue;
				Convert(s0.op,GetType(system,x.type));
				result := s0;
			(* ---- SYSTEM.BIT ----- *)
			|Global.systemBit: HALT(200);
			(* ---- SYSTEM.GET8|16|32|64 ----- *)
			|Global.systemGet8, Global.systemGet16, Global.systemGet32, Global.systemGet64:
				Evaluate(p0,s0);
				MakeMemory(res,s0.op,GetType(system,x.type),0);
				ReleaseOperand(s0);
				InitOperand(result,ModeValue);
				result.op := res;

			(* ---- SYSTEM.VAL ----- *)
			|Global.systemVal:
				Expression(p1);
				s1 := result;
				type :=p0(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType;
				IF s1.mode = ModeReference THEN
					IF (type IS SyntaxTree.RecordType) THEN
						ReleaseIntermediateOperand(s1.tag);
						s1.tag := TypeDescriptorAdr(type);
						IF ~newObjectFile THEN
							IntermediateCode.MakeMemory(s1.tag,addressType);
						END;
						UseIntermediateOperand(s1.tag);
					END;
				ELSE
					Convert(s1.op, GetType(system,type));
				END;
				result := s1;
			(* ---- SYSTEM.GET ----- *)
			|Global.systemGet:
				Evaluate(p0,s0); (* adr *)
				Designate(p1,s1); (* variable *)
				ToMemory(s0.op,GetType(system,p1.type),0);
				ToMemory(s1.op,GetType(system,p1.type),0);
				Emit(Mov(s1.op,s0.op));
				ReleaseOperand(s1);
				ReleaseOperand(s0);
			(* ---- SYSTEM.PUT 8|16|32|64 ----- *)
			|Global.systemPut, Global.systemPut64, Global.systemPut32, Global.systemPut16, Global.systemPut8:
				Evaluate(p0,s0); (*  *)
				Evaluate(p1,s1); (* variable *)
				MakeMemory(res,s0.op,GetType(system,p1.type),0);
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
				Convert(result.op,GetType(system, x.type));
			(* ---- SUM ----- *)
			|Global.Sum: HALT(200);
			(* ---- DIM ----- *)
			|Global.Dim:
				Designate(p0,s0);
				IF p0.type.resolved(SyntaxTree.MathArrayType).form = SyntaxTree.Tensor THEN
					Dereference(s0,p0.type.resolved);
				END;
				MathArrayDim(p0.type.resolved(SyntaxTree.MathArrayType),s0.tag,result);
				ReleaseOperand(s0);
			(* ---- RESHAPE ----- *)
			|Global.systemReshape: HALT(200);
			(* ---- SYSTEM.ZEROCOPY----- *)
			|Global.systemZeroCopy: HALT(200);
			(* ---- SYSTEM.TYPECODE ----- *)
			|Global.systemTypeCode:
				type := p0(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType;
				IF type.resolved IS SyntaxTree.PointerType THEN
					type := type.resolved(SyntaxTree.PointerType).pointerBase;
				END;
				result.op := TypeDescriptorAdr(type);
				IF ~newObjectFile THEN
					ToMemory(result.op,GetType(system,x.type),0);
				ELSE Convert(result.op, GetType(system,x.type));
				END;
				result.mode := ModeValue;
			(* ---- SYSTEM.TRACE ----- *)
			|Global.systemTrace:
				SystemTrace(p0);
			ELSE (* function not yet implemented *)
				HALT(200)
			END;
			destination := dest;
			IF Trace THEN TraceExit("VisitBuiltinCallDesignator") END;
		END VisitBuiltinCallDesignator;

		PROCEDURE VisitTypeGuardDesignator(x: SyntaxTree.TypeGuardDesignator);
		VAR trueL,falseL: Label; recordType: SyntaxTree.RecordType; dest: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitTypeGuardDesignator") END;
			dest := destination; destination := emptyOperand;

			IF x.left.type.resolved = x.type.resolved THEN (* always true: do nothing *)
			ELSE
				trueL := NewLabel();
				falseL := NewLabel();
				Expression(x.left);
				IF IsPointerToRecord(x.left.type,recordType) THEN
					Dereference(result,recordType);
				END;
				TypeTest(result.tag,x.type,trueL,falseL);
				SetLabel(falseL);
				Emit(Trap(TypeCheckTrap));
				SetLabel(trueL);
				ReleaseOperand(result);
			END;
			Expression(x.left);
			destination := dest;
			IF Trace THEN TraceExit("VisitTypeGuardDesignator") END;
		END VisitTypeGuardDesignator;

		PROCEDURE Dereference(VAR operand: Operand; type: SyntaxTree.Type);
		VAR dereferenced: IntermediateCode.Operand; arrayDataOffset: LONGINT;
		BEGIN
			LoadValue(operand,Global.Address); (* in case operand is not a value yet *)
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
			IntermediateCode.InitImmediate(result.op,GetType(system,x.type),x.hvalue);
		END VisitIntegerValue;

		PROCEDURE VisitCharacterValue(x: SyntaxTree.CharacterValue);
		BEGIN
			IF Trace THEN TraceEnter("VisitCharacterValue") END;
			InitOperand(result,ModeValue);
			IntermediateCode.InitImmediate(result.op,GetType(system,x.type),ORD(x.value));
		END VisitCharacterValue;

		PROCEDURE VisitSetValue(x: SyntaxTree.SetValue);
		BEGIN
			IF Trace THEN TraceEnter("VisitSetValue") END;
			InitOperand(result,ModeValue);
			IntermediateCode.InitImmediate(result.op,GetType(system,x.type),SYSTEM.VAL(LONGINT,x.value));
		END VisitSetValue;

		PROCEDURE VisitMathArrayValue(x: SyntaxTree.MathArrayValue);
		VAR  irv: IntermediateCode.Section; name: SyntaxTree.String;

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
			IF Trace THEN TraceEnter("VisitStringValue") END;
			IF ~TryConstantDeclaration() THEN
				IF constantDeclaration = NIL THEN constantDeclaration:=BuildConstant(module.module,x,constId) END;
				Global.GetSymbolName(constantDeclaration,name);
				irv := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,constantDeclaration,commentPrintout # NIL);
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
				constant := module.sections.FindBySymbol(constantDeclaration);
				IF constant # NIL THEN
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
			IntermediateCode.InitFloatImmediate(result.op,GetType(system,x.type),x.value);
		END VisitRealValue;

		PROCEDURE VisitStringValue(x: SyntaxTree.StringValue);
		VAR  i: LONGINT; name: SyntaxTree.String;
			irv: IntermediateCode.Section; op: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitStringValue") END;
			IF ~TryConstantDeclaration() THEN
				IF constantDeclaration = NIL THEN constantDeclaration:=BuildConstant(module.module,x,constId) END;
				Global.GetSymbolName(constantDeclaration,name);
				irv := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,constantDeclaration,commentPrintout # NIL);
				FOR i := 0 TO x.length-1 DO
					IntermediateCode.InitImmediate(op,GetType(system,Global.Char),ORD(x.value[i]));
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
			result.op := IntermediateCode.Immediate(GetType(system,x.type),0);
			result.tag := IntermediateCode.Immediate(GetType(system,x.type),0);
		END VisitNilValue;

		PROCEDURE VisitEnumerationValue(x: SyntaxTree.EnumerationValue);
		BEGIN
			IF Trace THEN TraceEnter("VisitEnumerationValue") END;
			InitOperand(result,ModeValue);
			result.op := IntermediateCode.Immediate(GetType(system,x.type),x.value);
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
		VAR symbol: Sections.Section;  type: SyntaxTree.Type; name: Scanner.StringType; temp: IntermediateCode.Operand;
		BEGIN
			IF Trace THEN TraceEnter("VisitVariable") END;
			type := x.type.resolved;
			IF (x.scope IS SyntaxTree.ProcedureScope) THEN (* local variable (potentially via nested procedure) *)
				InitOperand(result,ModeReference);
				GetBaseRegister(result.op,currentScope,x.scope);
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,x.offsetInBits));
			ELSIF x.scope = moduleScope THEN (* global variable *)
				InitOperand(result,ModeReference);
				Global.GetSymbolName(x,name);
				symbol := IntermediateCode.NewSection(module.sections,Sections.VarSection,name,x,commentPrintout # NIL);
				IntermediateCode.InitAddress(result.op, addressType, symbol, 0);
			ELSIF x.scope IS SyntaxTree.ModuleScope THEN (* global variable in imported module *)
				InitOperand(result,ModeReference);
				Global.GetSymbolName(x,name);
				(*! check for new object file, correct? *)
				symbol := IntermediateCode.NewSection(module.importedSymbols,Sections.VarSection,name,x,commentPrintout # NIL);
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

			IF conditional & (x.type.resolved = Global.Boolean) THEN
				ValueToCondition(result);
			ELSIF type IS SyntaxTree.ProcedureType THEN
				ReleaseIntermediateOperand(result.tag);
				IF SyntaxTree.DelegateFlag IN type(SyntaxTree.ProcedureType).flags THEN
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
		VAR type: SyntaxTree.Type; basereg, mem: IntermediateCode.Operand;
		BEGIN
			type := x.type.resolved;
			IF Trace THEN TraceEnter("VisitParameter") END;

			GetBaseRegister(basereg,currentScope,x.scope);
			InitOperand(result,ModeReference);
			result.op := basereg;

			IF IsOpenArray(type) THEN
				result.tag := basereg;
				IntermediateCode.AddOffset(result.op,ToMemoryUnits(system,x.offsetInBits));
				IntermediateCode.MakeMemory(result.op,addressType);
				IF IsOberonProcedure(x.procedureType) THEN
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

			IF conditional & (x.type.resolved = Global.Boolean) THEN
				ValueToCondition(result);
			ELSIF type IS SyntaxTree.ProcedureType THEN
				ReleaseIntermediateOperand(result.tag);
				IF SyntaxTree.DelegateFlag IN type(SyntaxTree.ProcedureType).flags THEN
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
		VAR source: IntermediateCode.Section; tag,reg: IntermediateCode.Operand; name: SyntaxTree.String; sectionType: SHORTINT;
		BEGIN
			IF Trace THEN TraceEnter("StaticCallOperand") END;
			tag := nil;
			Global.GetSymbolName(x,name);
			IF x.HasFlag(SyntaxTree.InlineFlag) THEN
				sectionType := Sections.InlineCodeSection;
			ELSE
				sectionType := Sections.CodeSection;
			END;
			IF (x.scope.ownerModule = module.module) THEN
				source := IntermediateCode.NewSection(module.sections,sectionType,name,x,commentPrintout # NIL);
			ELSIF (sectionType = Sections.InlineCodeSection) & (x.procedureScope.body.code.sourceCode # NIL) THEN
				source := IntermediateCode.NewSection(module.sections,sectionType,name,x,commentPrintout # NIL);
				IF source.pc = 0 THEN (* no code yet *)
					source.Emit(Asm(x.procedureScope.body.code.sourceCode,x.position));
				END;
			ELSE
				source := IntermediateCode.NewSection(module.importedSymbols,sectionType,name,x,commentPrintout # NIL);
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
			IF SyntaxTree.DelegateFlag IN x.type(SyntaxTree.ProcedureType).flags THEN
				DynamicCallOperand(result,x);
			ELSIF x.HasFlag(SyntaxTree.InlineFlag) THEN
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
			arrayBase: SyntaxTree.Module; saved: Registers;  procedure: SyntaxTree.Procedure; parameter: SyntaxTree.Parameter;
			size: LONGINT; rightKind: LONGINT;
		CONST moduleName = "OCArrayBase";

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
				SaveRegisters(saved);
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

				procedure := arrayBase.moduleScope.FindProcedure(SyntaxTree.NewIdentifier(-1,procedureName));
				IF procedure = NIL THEN
					s := "Instruction not supported on target, emulation procedure ";
					Strings.Append(s,moduleName);
					Strings.Append(s,".");
					Strings.Append(s,procedureName);
					Strings.Append(s," not present");
					Error(s);
				ELSE
					parameter := SyntaxTree.NewParameter(left.position,procedure.type(SyntaxTree.ProcedureType),SyntaxTree.NewIdentifier(0,"temp"), SyntaxTree.VarParameter);
					parameter.SetType(leftType);
					parameter.SetAccess(SyntaxTree.Internal);
					PushParameter(left,parameter,{});
					parameter.SetKind(rightKind);
					PushParameter(right,parameter,{});
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
		VAR leftO,rightO: Operand; mem: IntermediateCode.Operand;leftType,rightType: SyntaxTree.Type; size: LONGINT;
		BEGIN
			ASSERT(left.type # NIL); ASSERT(right.type # NIL);
			leftType := left.type.resolved; rightType:= right.type.resolved;

			IF (leftType IS SyntaxTree.BasicType) OR (leftType IS SyntaxTree.PointerType) OR (leftType IS SyntaxTree.EnumerationType) THEN
				Designate(left,leftO);
				MakeMemory(mem,leftO.op,GetType(system,left.type),0);
				destination := mem;
				ReleaseOperand(leftO);
				(* rightO := leftO;*)
				Evaluate(right,rightO);
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
				IF SyntaxTree.DelegateFlag IN leftType(SyntaxTree.ProcedureType).flags THEN
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


		PROCEDURE VisitWithStatement(x: SyntaxTree.WithStatement);
		VAR trueL,falseL: Label; res: Operand; recordType: SyntaxTree.RecordType;
		BEGIN
			IF Trace THEN TraceEnter("VisitWithStatement") END;
			IF x.variable.type.resolved = x.type(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType.resolved THEN
				(* always true, do nothing *)
			ELSE
				Designate(x.variable,res);
				trueL := NewLabel();
				falseL := NewLabel();
				IF IsPointerToRecord(x.variable.type,recordType) THEN
					Dereference(res,recordType)
				END;
				TypeTest(res.tag,x.type(SyntaxTree.SymbolDesignator).symbol(SyntaxTree.TypeDeclaration).declaredType,trueL,falseL);
				SetLabel(falseL);
				Emit(Trap(WithTrap));
				SetLabel(trueL);
				ReleaseOperand(res);
			END;
			StatementSequence(x.statements);
			IF Trace THEN TraceExit("VisitWithStatement") END;
		END VisitWithStatement;

		PROCEDURE VisitCaseStatement(x: SyntaxTree.CaseStatement);
		VAR var: Operand; jmp,res,op,tmp: IntermediateCode.Operand; j,i,size: LONGINT; part: SyntaxTree.CasePart; constant: SyntaxTree.CaseConstant;
			out,else: Label; label: Label;
			fixups: POINTER TO ARRAY OF Label; section: IntermediateCode.Section; name: SyntaxTree.String;
		BEGIN
			(*! split case statement into if-elsif statements for large case label lists *)
			IF Trace THEN TraceEnter("VisitCaseStatement") END;
			Evaluate(x.variable,var);
			ReuseCopy(tmp,var.op);
			ReleaseIntermediateOperand(var.op);
			var.op := tmp;
			Emit(Sub(var.op,var.op,IntermediateCode.Immediate(GetType(system,x.variable.type),x.min)));
			Convert(var.op,addressType);
			size := x.max-x.min+1;
			else := NewLabel();
			BrgeL(else,var.op,IntermediateCode.Immediate(addressType,size));
			UniqueId(name,module.module,"case",caseId);
			NEW(fixups,size); FOR i := 0 TO size-1 DO fixups[i] := NIL END;
			NEW(section,Sections.ConstSection,name,SyntaxTree.NewSymbol(SyntaxTree.NewIdentifier(-1,name)),commentPrintout # NIL);
			module.caseTables.Add(section);
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
			ELSE
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
		VAR binary: SyntaxTree.BinaryExpression; start,true,false : Label; cmp: LONGINT; by: HUGEINT;
		BEGIN
			IF Trace THEN TraceEnter("VisitForStatement") END;
			true := NewLabel();
			false := NewLabel();
			start := NewLabel();

			Assign(x.variable,x.from);
			Assign(x.temporary,x.to);
			IF x.by = NIL THEN by := 1 ELSE by := x.by.resolved(SyntaxTree.IntegerValue).hvalue END;
			IF by > 0 THEN
				cmp := Scanner.LessEqual
			ELSE
				cmp := Scanner.GreaterEqual
			END;
			binary := SyntaxTree.NewBinaryExpression(0,x.variable,x.temporary,cmp);
			binary.SetType(Global.Boolean);

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
			IF locked  THEN (* check if we jump out of an exclusive block *)
				outer := x.outer;
				WHILE ~(outer IS SyntaxTree.LoopStatement) & ~(SyntaxTree.ExclusiveFlag IN outer.flags) DO
					outer := outer.outer;
				END;
				IF SyntaxTree.ExclusiveFlag IN outer.flags THEN
					Lock(FALSE);
				END;
			END;
			BrL(currentLoop);
			IF Trace THEN TraceExit("VisitExitStatement") END;
		END VisitExitStatement;

		PROCEDURE VisitReturnStatement(x: SyntaxTree.ReturnStatement);
		VAR expression: SyntaxTree.Expression; type: SyntaxTree.Type; res: Operand;
			parameter: SyntaxTree.Parameter; left: IntermediateCode.Operand; right: Operand; parSize: LONGINT;
			size: IntermediateCode.Operand; returnTypeOffset: LONGINT; delegate: BOOLEAN;
			cc: LONGINT; procedure: SyntaxTree.Procedure;
			parameterDesignator: SyntaxTree.Expression;
			procedureType: SyntaxTree.ProcedureType;
		BEGIN
			IF Trace THEN TraceEnter("VisitReturnStatement") END;
			expression := x.returnValue;
			IF expression # NIL THEN
				procedureType := currentScope(SyntaxTree.ProcedureScope).ownerProcedure.type(SyntaxTree.ProcedureType);
				type := expression.type.resolved;
				IF (expression IS SyntaxTree.SymbolDesignator) & (expression(SyntaxTree.SymbolDesignator).symbol = procedureType.returnParameter) THEN
					(* no assignment, it is assumed that result has been written to return parameter via RET parameter *)
				ELSIF (type IS SyntaxTree.BasicType) OR (type IS SyntaxTree.ProcedureType) OR (type IS SyntaxTree.PointerType) THEN
					Evaluate(expression,res);
					delegate := (type IS SyntaxTree.ProcedureType) & (SyntaxTree.DelegateFlag IN type(SyntaxTree.ProcedureType).flags);
					IF locked THEN
						Emit(Push(res.op));
						IF delegate THEN Emit(Push(res.tag)) END;
						ReleaseOperand(res);
						Lock(FALSE);
						IF delegate THEN Emit(Pop(IntermediateCode.Register(GetType(system,type),IntermediateCode.Result2))); END;
						Emit(Pop(IntermediateCode.Register(GetType(system,type),IntermediateCode.Result)));
					ELSE
						Emit(Mov(IntermediateCode.Register(GetType(system,type),IntermediateCode.Result),res.op));
						IF delegate THEN
							Emit(Mov(IntermediateCode.Register(GetType(system,type),IntermediateCode.Result2),res.tag));
						END;
						ReleaseOperand(res);
					END;
				ELSIF (type IS SyntaxTree.RecordType) OR (type IS SyntaxTree.ArrayType) THEN
					ASSERT((type IS SyntaxTree.RecordType) OR (type(SyntaxTree.ArrayType).form = SyntaxTree.Static));
					(* parameter := currentScope(SyntaxTree.ProcedureScope).FindParameter(Global.ReturnParameterName); *)
					parameter :=procedureType.firstParameter;
					IF parameter# NIL THEN
						returnTypeOffset := parameter.offsetInBits + system.SizeOfParameter(parameter);
						INC(returnTypeOffset,(-returnTypeOffset) MOD system.AlignmentOf(system.parameterAlignment,parameter.type));
					ELSE
						returnTypeOffset := system.offsetFirstParameter
					END;
					left := IntermediateCode.Memory(addressType,fp,ToMemoryUnits(system,returnTypeOffset));
					size :=IntermediateCode.Memory(addressType,fp,ToMemoryUnits(system,returnTypeOffset+system.addressSize));
					Designate(expression,right);
					Emit(Copy(left,right.op,size));
					ReleaseIntermediateOperand(left); ReleaseOperand(right);
					IF locked THEN Lock(FALSE) END;
				ELSIF (type IS SyntaxTree.MathArrayType) THEN
					parameter := procedureType.returnParameter;
					checker.SetCurrentScope(currentScope);
					parameterDesignator :=checker.NewSymbolDesignator(expression.position,NIL,parameter);
					AssignMathArray(parameterDesignator,expression);
					(*
					operatorCall := checker.NewOperatorCall(expression.position,Scanner.Becomes,parameterDesignator,expression,NIL);
					Expression(operatorCall);
					*)
				ELSE
					HALT(200);
				END;
			ELSIF locked THEN Lock(FALSE)
			END;
			procedure := currentScope(SyntaxTree.ProcedureScope).ownerProcedure;
			parSize := ProcedureParametersSize(system,procedure);

			IF SyntaxTree.WinAPIFlag IN procedure.type(SyntaxTree.ProcedureType).flags THEN cc := SyntaxTree.WinAPIFlag
			ELSIF SyntaxTree.CFlag IN procedure.type(SyntaxTree.ProcedureType).flags THEN cc := SyntaxTree.CFlag
			ELSE cc := 0
			END;

			Emit(Leave(cc));
			Emit(Return(parSize));
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
			identifier := SyntaxTree.NewIdentifier(x.position,name);
			INC(awaitProcCounter);
			ASSERT(currentScope IS SyntaxTree.ProcedureScope);
			procedureScope := SyntaxTree.NewProcedureScope(currentScope);
			ASSERT(procedureScope.outerScope IS SyntaxTree.ProcedureScope);
			procedure := SyntaxTree.NewProcedure(x.position,identifier,procedureScope);
			procedure.SetAccess(SyntaxTree.Hidden);
			procedure.SetScope(currentScope);
			procedureType := SyntaxTree.NewProcedureType(x.position,currentScope);
			procedureType.SetReturnType(Global.Boolean);
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
			call: IntermediateCode.Operand; label: Label; name: SyntaxTree.String;
		BEGIN
			IF Trace THEN TraceEnter("VisitAwaitStatement") END;
			proc := MakeAwaitProcedure(x);
			Emit(Push(fp));
			Global.GetSymbolName(proc,name);
			symbol := IntermediateCode.NewSection(module.sections,Sections.CodeSection,name,proc,commentPrintout # NIL);
			IntermediateCode.InitAddress(call,addressType,symbol,0);
			Emit(Call(call,ProcedureParametersSize(system,proc)));
			IntermediateCode.InitRegister(res,GetType(system,Global.Boolean),IntermediateCode.Result);
			InitOperand(result,ModeValue);
			result.op := res;
			label := NewLabel();
			BreqL(label, result.op, true);
			symbol := IntermediateCode.NewSection(module.sections,Sections.CodeSection,name,proc,commentPrintout # NIL);
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
				dump.Ln;
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

			IF SyntaxTree.ExclusiveFlag IN x.flags THEN Lock(TRUE); ASSERT(~locked);  locked := TRUE; END;
			IF x.statements # NIL THEN
				StatementSequence(x.statements);
			END;
			IF SyntaxTree.ExclusiveFlag IN x.flags THEN Lock(FALSE); ASSERT(locked); locked := FALSE; END;
			IF Trace THEN TraceExit("VisitStatementBlock") END;
		END VisitStatementBlock;

		PROCEDURE VisitCode(x: SyntaxTree.Code);
		VAR (*  inline: Sections.Assembly; symbol: SyntaxTree.Symbol; *)
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
						IntermediateCode.MakeMemory(par,addressType);
						Emit(Mov(par,sp));
						ReleaseOperand(op);
						ReleaseIntermediateOperand(size);
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
		VAR prevScope: SyntaxTree.Scope; procedureType: SyntaxTree.ProcedureType;
			end: Label;
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


			prevScope := currentScope;
			currentScope := scope;
			procedureType := scope(SyntaxTree.ProcedureScope).ownerProcedure.type(SyntaxTree.ProcedureType);
			IF newObjectFile & moduleBody & ~suppressModuleRegistration THEN
				PushSelfPointer();
				(*
				moduleSection := ModuleSection(module);
				moduleOffset := moduleSection.pc;
				op := IntermediateCode.Address(addressType, moduleSection, moduleOffset);
				Emit(Push(op));
				*)
				CallThis2("Modules","PublishThis","Runtime","InsertModule");
				end := NewLabel();
				BrneL(end, IntermediateCode.Register(bool,IntermediateCode.Result),true);
			END;
			IF x # NIL THEN
				section.SetAlignment(x.fixed, x.alignment);

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

	IntermediateBackend*= OBJECT (Backend.Backend)
	VAR
		trace-: BOOLEAN;
		traceString-: SyntaxTree.String;
		runtimeModuleName-: SyntaxTree.String;
		newObjectFile-: BOOLEAN;

		PROCEDURE &InitIntermediateBackend*;
		BEGIN
			InitBackend; runtimeModuleName := DefaultRuntimeModuleName;
		END InitIntermediateBackend;

		PROCEDURE Supported*(CONST instr: IntermediateCode.Instruction; VAR moduleName,procedureName: ARRAY OF CHAR): BOOLEAN;
		BEGIN
			moduleName := ""; procedureName := "";
			RETURN TRUE
		END Supported;

		PROCEDURE GenerateIntermediate*(x: SyntaxTree.Module): Sections.Module;
		VAR
			declarator: DeclarationVisitor;
			implementationVisitor: ImplementationVisitor;
			module: Sections.Module;

		BEGIN
			ResetError;
			NEW(module,x,system); (* backend structures *)
			NEW(implementationVisitor,system,checker,Supported, Compiler.FindPC IN flags, runtimeModuleName, diagnostics, newObjectFile);
			NEW(declarator,system,implementationVisitor,diagnostics,trace);
			declarator.Module(x,module);

			IF newObjectFile THEN
				MetaModule(implementationVisitor,module);
			END;

			IF implementationVisitor.error THEN Error("","") END;
			RETURN module
		END GenerateIntermediate;

		(* Work on a module *)
		PROCEDURE Module(x: SyntaxTree.Module): Formats.GeneratedModule;
		VAR
			dump: WMUtilities.WindowWriter;
			module: Sections.Module;

			traceName: SyntaxTree.String;
		BEGIN
			module := GenerateIntermediate(x);
			IF trace THEN
				traceName := "intermediate code trace: ";
				Strings.Append(traceName,traceString);
				NEW(dump,traceName,600,400,FALSE);
				IF (traceString="") OR (traceString="*") THEN
					module.Dump(dump);
					dump.Update
				ELSE
					Sections.DumpFiltered(dump,module,traceString);
				END
			END;

			RETURN module
		END Module;

		PROCEDURE DefineOptions(options: Options.Options);
		BEGIN
			DefineOptions^(options);
			options.Add(0X,"trace",Options.String);
			options.Add(0X,"runtime",Options.String);
			options.Add(0X,"newObjectFile",Options.Flag);
		END DefineOptions;

		PROCEDURE GetOptions(options: Options.Options);
		VAR name: SyntaxTree.String;
		BEGIN
			GetOptions^(options);
			trace := options.GetString("trace",traceString);
			newObjectFile := options.GetFlag("newObjectFile");
			IF options.GetString("runtime",name) THEN
				runtimeModuleName := name
			END;
		END GetOptions;

		PROCEDURE SetRuntimeModuleName*(CONST name: ARRAY OF CHAR);
		BEGIN
			COPY(name, runtimeModuleName);
		END SetRuntimeModuleName;

		PROCEDURE DefaultSymbolFileFormat(): Formats.SymbolFileFormat;
		BEGIN RETURN SymbolFileFormat.Get()
		END DefaultSymbolFileFormat;

	END IntermediateBackend;

	VAR int8, int16, int32, int64, uint8, uint16, uint32, uint64, float32, float64: IntermediateCode.Type;
		emptyOperand: IntermediateCode.Operand;
		systemCalls: ARRAY NumberSystemCalls OF SyntaxTree.Symbol;

	PROCEDURE Assert(cond: BOOLEAN; CONST reason: ARRAY OF CHAR);
	BEGIN ASSERT(cond);
	END Assert;

	PROCEDURE UnsignedIntegerType(bits: LONGINT): IntermediateCode.Type;
	BEGIN
		IF bits = 8 THEN RETURN uint8
		ELSIF bits=16 THEN RETURN uint16
		ELSIF bits=32 THEN RETURN uint32
		ELSIF bits=64 THEN RETURN uint64
		ELSE HALT(200)
		END;
	END UnsignedIntegerType;

	PROCEDURE SignedIntegerType(bits: LONGINT): IntermediateCode.Type;
	BEGIN
		IF bits = 8 THEN RETURN int8
		ELSIF bits=16 THEN RETURN int16
		ELSIF bits=32 THEN RETURN int32
		ELSIF bits=64 THEN RETURN int64
		ELSE HALT(200)
		END;
	END SignedIntegerType;

	PROCEDURE FloatType(bits: LONGINT): IntermediateCode.Type;
	BEGIN
		IF bits=32 THEN RETURN float32
		ELSIF bits=64 THEN RETURN float64
		ELSE HALT(200)
		END;
	END FloatType;

	PROCEDURE ReusableRegister(op: IntermediateCode.Operand): BOOLEAN;
	BEGIN
		RETURN (op.mode = IntermediateCode.ModeRegister) & (op.register > 0) & (op.offset = 0);
	END ReusableRegister;

	PROCEDURE MetaHeapBlock(module: Sections.Module; section: IntermediateCode.Section; dataAdrOffset: LONGINT);
	BEGIN
		INC(dataAdrOffset,6);
		MetaInfo(section,"headerAdr");
		MetaAddress(module,section,0);
		MetaInfo(section,"typeDesc");
		MetaAddress(module,section,0);
		MetaInfo(section,"mark: LONGINT;");
		MetaLongint(module,section,-1);
		MetaInfo(section,"dataAdr-: SYSTEM.ADDRESS");
		MetaSymbol(module,section,section,dataAdrOffset,0);
		MetaInfo(section,"size-: SYSTEM.SIZE");
		MetaAddress(module,section,0);
		MetaInfo(section,"nextRealtime: HeapBlock;"); 
		MetaAddress(module,section,0);
	END MetaHeapBlock;

	PROCEDURE MetaProtectedHeapBlock(module: Sections.Module; section: IntermediateCode.Section; dataAdrOffset: LONGINT);
	VAR i: LONGINT;
	BEGIN
		INC(dataAdrOffset,14);
		MetaHeapBlock(module,section,dataAdrOffset);
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
		IF section.comments # NIL THEN section.comments.String(s); section.comments.Ln END;
	END MetaInfo;

	PROCEDURE MetaAddress(module: Sections.Module; section: IntermediateCode.Section; value: LONGINT);
	VAR op: IntermediateCode.Operand;
	BEGIN
		IntermediateCode.InitImmediate(op,GetType(module.system, Global.Address),value);
		section.Emit(Data(op));
	END MetaAddress;

	PROCEDURE MetaSet(module: Sections.Module; section: IntermediateCode.Section; value: SET);
	VAR op: IntermediateCode.Operand;
	BEGIN
		IntermediateCode.InitImmediate(op,GetType(module.system, Global.Longint),SYSTEM.VAL(LONGINT,value));
		section.Emit(Data(op));
	END MetaSet;

	PROCEDURE MetaLongint(module: Sections.Module; section: IntermediateCode.Section; value: LONGINT);
	VAR op: IntermediateCode.Operand;
	BEGIN
		IntermediateCode.InitImmediate(op,GetType(module.system, Global.Longint),value);
		section.Emit(Data(op));
	END MetaLongint;

	PROCEDURE PatchLongint(module: Sections.Module; section: IntermediateCode.Section; pc: LONGINT; value: LONGINT);
	VAR op,noOperand: IntermediateCode.Operand;
	BEGIN
		IntermediateCode.InitOperand(noOperand);
		IntermediateCode.InitImmediate(op,GetType(module.system, Global.Longint),value);
		section.PatchOperands(pc,op,noOperand,noOperand);
	END PatchLongint;

	PROCEDURE MetaBoolean(module: Sections.Module; section: IntermediateCode.Section; value: BOOLEAN);
	VAR op: IntermediateCode.Operand; intValue: LONGINT;
	BEGIN
		IF value = FALSE THEN intValue := 0 ELSE intValue :=1 END;
		IntermediateCode.InitImmediate(op,GetType(module.system, Global.Boolean),intValue);
		section.Emit(Data(op));
	END MetaBoolean;

	PROCEDURE MetaChar(module: Sections.Module; section: IntermediateCode.Section; char: CHAR);
	VAR op: IntermediateCode.Operand;
	BEGIN
		IntermediateCode.InitImmediate(op,GetType(module.system, Global.Char),ORD(char));
		section.Emit(Data(op));
	END MetaChar;

	PROCEDURE MetaString(module: Sections.Module; section: IntermediateCode.Section; CONST str: ARRAY OF CHAR);
	VAR i: LONGINT;
	BEGIN
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
			IntermediateCode.InitAddress(op, GetType(module.system, Global.Address), symbol, virtualOffset);
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
		IF type = Global.Any THEN
			MetaSymbol(module,section, symbol, 0, (offset ));
			INC(numberPointers);

			IF Trace THEN D.Str("ptr at offset="); D.Int(offset,1); D.Ln; END;
		ELSIF type IS SyntaxTree.PointerType THEN
			MetaSymbol(module,section, symbol, 0, (offset )); INC(numberPointers);
			IF Trace THEN D.Str("ptr at offset="); D.Int(offset,1);D.Ln;  END;
		ELSIF (type IS SyntaxTree.ProcedureType) & (SyntaxTree.DelegateFlag IN type(SyntaxTree.ProcedureType).flags) THEN
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
					IF ~(SyntaxTree.UntracedFlag IN variable.flags) THEN
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
		fingerprinter: Fingerprinter.Fingerprinter; symbol: Sections.Section): BOOLEAN;
	VAR fingerprint: SyntaxTree.Fingerprint;
	BEGIN
		IF (symbol # NIL) & (symbol.symbol # NIL) & (symbol.type # Sections.InitCodeSection)
			& (symbol.type # Sections.InlineCodeSection)
		THEN
			fingerprint := fingerprinter.SymbolFP(symbol.symbol);
			MetaLongint(module,source,fingerprint.shallow);
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
	VAR sizePC: LONGINT; section: Sections.Section;		fingerprinter : Fingerprinter.Fingerprinter;
	BEGIN
		NEW(fingerprinter, module.system);
		size := 0;
		MetaArray(module,source,sizePC);

		section := module.sections.first;
		WHILE section # NIL DO
			IF MetaExportDesc(module,source,fingerprinter,section) THEN INC(size) END;
			section := section.nextSection;
		END;
		PatchLongint(module,source,sizePC,size);
	END MetaExportDescArray;

	PROCEDURE MetaExceptionArray(module: Sections.Module; source: IntermediateCode.Section);
	VAR p: Sections.Section; finallyPC, sizePC, size: LONGINT;
	BEGIN
		MetaInfo(source, "exception table offsets array descriptor");
		size := 0;
		MetaArray(module,source,sizePC);
		MetaInfo(source, "exception table content");
		p := module.sections.first;
		WHILE p # NIL DO
			IF p.type = Sections.CodeSection THEN
				finallyPC := p(IntermediateCode.Section).finally;
				IF finallyPC>=0 THEN
					MetaSymbol(module, source, p, 0,0);
					MetaSymbol(module, source, p, finallyPC, 0);
					MetaSymbol(module, source,p, finallyPC,0);
					INC(size);
				END;
			END;
			p := p.nextSection
		END;
		PatchLongint(module,source,sizePC,size);
		END MetaExceptionArray;

		PROCEDURE MetaName(module: Sections.Module; section: IntermediateCode.Section; CONST name: ARRAY OF CHAR);
		VAR i: LONGINT; ch: CHAR;
		BEGIN
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

		VAR size: LONGINT; s: Sections.Section; sizePC: LONGINT;

			PROCEDURE BaseType(arrayOf: BOOLEAN; type: SyntaxTree.Type);
			VAR char: CHAR;
			BEGIN
				IF type  = Global.Byte THEN char := rfByte
				ELSIF type = Global.Boolean THEN char := rfBoolean
				ELSIF type = Global.Char8 THEN char := rfChar8
				ELSIF type = Global.Char16 THEN char := rfChar16
				ELSIF type = Global.Char32 THEN char := rfChar32
				ELSIF type = Global.Shortint THEN char := rfShortint
				ELSIF type = Global.Integer THEN char := rfInteger
				ELSIF type = Global.Longint THEN char := rfLongint
				ELSIF type = Global.Address THEN char := rfLongint
				ELSIF type = Global.Size THEN char := rfLongint
				ELSIF type = Global.Hugeint THEN char := rfHugeint
				ELSIF type = Global.Real THEN char := rfReal
				ELSIF type = Global.Longreal THEN char := rfLongreal
				ELSIF type = Global.Set THEN char := rfSet
				ELSIF type = Global.Any THEN char := rfPointer
				ELSIF type = Global.Object THEN char := rfPointer
				ELSIF type IS SyntaxTree.PointerType THEN char := rfPointer
				ELSIF type IS SyntaxTree.ProcedureType THEN char := rfDelegate
				ELSE ASSERT(arrayOf); char := rfPointer; (*RETURN (* ARRAY OF unknown (record): do not write anything *)*)
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
				destination := module.sections.FindBySymbol(type.typeDeclaration);
				IF destination = NIL THEN
					destination := module.importedSymbols.FindBySymbol(type.typeDeclaration)
				END;
				IF destination = NIL THEN
					(* imported unused record type *)
					MetaChar(module,section,0X); (* nil type *)
					INC(size);
					type.typeDeclaration.name.GetString(name);
					(*
					this happens when a symbol from a different module is used but the type desciptor is not necessary to be present in the current module
					D.Str("Warning: Unreferenced record type encountered: "); D.String(name); D.String(" unused? "); D.Ln;
					*)
				ELSE
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
				IF type.arrayBase.resolved IS SyntaxTree.MathArrayType THEN
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
					BaseType(FALSE,Global.Longint)
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
				variable.name.GetString(name);
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
				variable.name.GetString(name);
				Type(variable.type);
				MetaLongint(module,section,(variable.offsetInBits DIV 8));
				INC(size,4);
				variable.name.GetString(name);
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
				ELSE typeDeclaration.name.GetString(name)
				END;
			END DeclarationName;


			PROCEDURE Procedure(s: Sections.Section);
			VAR procedure: SyntaxTree.Procedure; procedureType: SyntaxTree.ProcedureType;
				 parameter: SyntaxTree.Parameter; variable: SyntaxTree.Variable;
				 name,recordName: ARRAY 256 OF CHAR;
				 record: SyntaxTree.RecordType;  i: LONGINT;
			BEGIN
				procedure := s.symbol(SyntaxTree.Procedure); (*! check for variable or type symbol for object body *)
				procedure.name.GetString(name);
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

			s := module.sections.first;
			WHILE s # NIL DO
				IF (s.type # Sections.InitCodeSection) & (s.symbol = module.module.moduleScope.bodyProcedure) THEN
					Scope(s) (*! must be first procedure in ref section *)
				END;
				s := s.nextSection;
			END;

			s := module.sections.first;
			WHILE s # NIL DO
				IF (s.symbol = module.module.moduleScope.bodyProcedure) THEN (* already done, see above *)
				ELSIF (s.type # Sections.InitCodeSection) & (s.symbol # NIL) & (s.symbol IS SyntaxTree.Procedure) & ~s.symbol(SyntaxTree.Procedure).HasFlag(SyntaxTree.InlineFlag) THEN
					Procedure(s)
				END;
				s := s.nextSection;
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
	VAR p: Sections.Section;  sizePC, numberCommands: LONGINT;
		procedure : SyntaxTree.Procedure; procedureType: SyntaxTree.ProcedureType;
		name: ARRAY 32 OF CHAR; numberParameters: LONGINT;

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
				numberParameters := procedureType.numberParameters - procedureType.numberHiddenParameters;
				RETURN
					(numberParameters = 0) & TypeAllowed(procedureType.returnType) OR
					(numberParameters = 1) & TypeAllowed(procedureType.firstParameter.type) & TypeAllowed(procedureType.returnType) OR
					(numberParameters = 1) & (procedureType.firstParameter.type.resolved = Global.Any) & (procedureType.returnType # NIL) & (procedureType.returnType.resolved = Global.Any);
			END GetProcedureAllowed;

			PROCEDURE WriteType(type : SyntaxTree.Type);
			VAR typeDeclaration: SyntaxTree.TypeDeclaration; section: Sections.Section;
				name: SyntaxTree.String;
			BEGIN
				IF type = NIL THEN
					MetaAddress(module,source,0);
				ELSIF (type.resolved = Global.Any) OR (type.resolved = Global.Object) THEN
					MetaAddress(module,source,1);
				ELSE
					type := type.resolved;
					IF type IS SyntaxTree.PointerType THEN
						type := type(SyntaxTree.PointerType).pointerBase.resolved;
					END;
					typeDeclaration := type.typeDeclaration; (* must be non-nil *)
					IF (typeDeclaration.scope = NIL) OR (typeDeclaration.scope.ownerModule = module.module) THEN
						typeDeclaration.name.GetString(name);
						section := module.sections.FindBySymbol(type.typeDeclaration);
					ELSE
						Global.GetSymbolName(typeDeclaration,name);
						section := IntermediateCode.NewSection(module.importedSymbols,Sections.ConstSection,name,typeDeclaration, source.comments # NIL);
					END;
					MetaSymbol(module,source,section, 0, ToMemoryUnits(module.system,(1 + type(SyntaxTree.RecordType).recordScope.numberMethods+16+1)*module.system.addressSize));
				END;
			END WriteType;

	BEGIN
		MetaInfo(source, "command array descriptor");
		MetaArray(module,source,sizePC);
		numberCommands := 0;
		MetaInfo(source, "command array content");
		p := module.sections.first;
		WHILE(p # NIL) DO
			IF (p.symbol # NIL) & (p.symbol IS SyntaxTree.Procedure)  THEN
				procedure := p.symbol(SyntaxTree.Procedure);
				procedureType := procedure.type(SyntaxTree.ProcedureType);
				IF (SyntaxTree.PublicRead IN procedure.access) & ~(SyntaxTree.InlineFlag IN procedureType.flags) & ~(SyntaxTree.DelegateFlag IN procedureType.flags) & GetProcedureAllowed() THEN
					procedure.name.GetString(name);
					MetaName(module,source,name);
					numberParameters := procedureType.numberParameters-procedureType.numberHiddenParameters;
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
			END;
			p := p.nextSection;
		END;
		PatchLongint(module,source,sizePC,numberCommands);
	END MetaCommandArray;

	PROCEDURE MetaTypeInfoSection(module: Sections.Module; source: IntermediateCode.Section);
	VAR p: Sections.Section; sizePC, size: LONGINT;
	BEGIN
		MetaInfo(source, "command array descriptor");
		size := 0;
		MetaArray(module,source,sizePC);
		p := module.sections.first;
		WHILE p # NIL DO
			WITH p: IntermediateCode.Section DO
				IF Strings.EndsWith("@Info",p.name) THEN
					MetaSymbol(module,source,p,0,0);
					INC(size);
				END;
			END;
			p := p.nextSection;
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
	VAR destination: Sections.Section;
		pointerArraySizePC, procArraySizePC, pointerArraySize: LONGINT;

		PROCEDURE PointerOffsets(destination : IntermediateCode.Section);
		VAR numberPointers: LONGINT; procedure: SyntaxTree.Procedure; procedureType: SyntaxTree.ProcedureType;
			variable: SyntaxTree.Variable; parameter: SyntaxTree.Parameter;
		BEGIN
			MetaInfo(procArray,"pcFrom");
			MetaSymbol(module,procArray,destination,0,0);
			MetaInfo(procArray,"pcTo");
			MetaSymbol(module,procArray,destination,destination.pc,0);
			MetaInfo(procArray,"pcStatementBegin");
			MetaSymbol(module,procArray,destination,destination.validPAFEnter,0);
			MetaInfo(procArray,"pcStatementEnd");
			MetaSymbol(module,procArray,destination,destination.validPAFExit,0);
			MetaInfo(pointerArray,destination.name);
			procedure := destination.symbol(SyntaxTree.Procedure);
			procedureType := procedure.type(SyntaxTree.ProcedureType);
			variable := procedure.procedureScope.firstVariable;
			WHILE(variable # NIL) DO
				MetaPointers(variable.offsetInBits DIV 8, NIL, module, pointerArray, variable.type, numberPointers);
				variable := variable.nextVariable
			END;
			parameter := procedureType.firstParameter;
			WHILE(parameter # NIL) DO
				MetaPointers(parameter.offsetInBits DIV 8, NIL, module, pointerArray, parameter.type, numberPointers);
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

		destination := module.sections.first; procArraySize := 0;
		WHILE(destination # NIL) DO
			IF (destination.type IN {Sections.CodeSection, Sections.BodyCodeSection}) & (destination.symbol # NIL) & (destination.symbol IS SyntaxTree.Procedure) & ~destination.symbol(SyntaxTree.Procedure).HasFlag(SyntaxTree.InlineFlag) THEN
				PointerOffsets(destination(IntermediateCode.Section));
				INC(procArraySize);
			END;
			destination := destination.nextSection;
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
	VAR name: ARRAY 128 OF CHAR; moduleSection,moduleTD: IntermediateCode.Section; offset: LONGINT; 
	BEGIN
		module.module.name.GetString(name);
		Strings.Append(name,".@Module");
		moduleSection := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,NIL,TRUE);
		IF moduleSection.pc = 0 THEN
			MetaProtectedHeapBlock(module,moduleSection,2);
			MetaInfo(moduleSection, "HeapBlock");
			MetaSymbol(module,moduleSection,moduleSection,2,0);
			MetaInfo(moduleSection, "TypeDescriptor");
			moduleTD := implementationVisitor.GetModulesModule();

			
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

		PROCEDURE HeapBlock(CONST suffix: ARRAY OF CHAR; VAR offset: LONGINT): IntermediateCode.Section;
		VAR name: ARRAY 128 OF CHAR; section: IntermediateCode.Section;
		BEGIN
			COPY(moduleName,name);
			Strings.Append(name,suffix);
			section := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,NIL,TRUE);
			MetaHeapBlock(module,section,2);
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
		module.module.name.GetString(moduleName);
		exportDescArray := HeapBlock(".@ExportDescArray",exportDescArrayOffset);
		MetaExportDescArray(module,exportDescArray, exportDescSize);
		pointerSection := HeapBlock(".@PointerArray",pointerSectionOffset);
		MetaPointerArray(module,pointerSection,module.module.moduleScope, numberPointers);
		commandsSection := HeapBlock(".@CommandArray",commandsSectionOffset);
		MetaCommandArray(module,commandsSection);
		exceptionSection := HeapBlock(".@ExceptionArray",exceptionSectionOffset);
		MetaExceptionArray(module,exceptionSection);
		typeInfoSection := HeapBlock(".@TypeInfoArray",typeInfoSectionOffset);
		MetaTypeInfoSection(module,typeInfoSection);
		referenceSection := HeapBlock(".@References",referenceSectionOffset);
		MetaReferences(module,referenceSection);
		procTableSection := HeapBlock(".@ProcTable",procTableSectionOffset);
		ptrTableSection := HeapBlock(".@PtrTable",ptrTableSectionOffset);
		MetaPointersInProcTables(module,procTableSection,ptrTableSection,numberProcs,maxPointers);
		emptyArraySection := HeapBlock(".@EmptyArray",emptyArraySectionOffset);
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
				symbol := module.sections.FindBySymbol(variable);
				MetaPointers(0,symbol, module,source,variable.type,numberPointers);
				variable := variable.nextVariable;
			END;
		END;
		PatchLongint(module,source,pc,numberPointers);
	END MetaPointerArray;


	PROCEDURE CheckTypeDeclaration(implementationVisitor: ImplementationVisitor; module: Sections.Module; x: SyntaxTree.Type; dump,newObjectFile: BOOLEAN);
	VAR recordType: SyntaxTree.RecordType;
		tir: IntermediateCode.Section; op: IntermediateCode.Operand; name: SyntaxTree.String; td: SyntaxTree.TypeDeclaration;
		section: Sections.Section;

		PROCEDURE NewTypeDescriptorInfo(tag: Sections.Section; offset: LONGINT; isProtected: BOOLEAN): Sections.Section;
		VAR name: SyntaxTree.String;source: IntermediateCode.Section;
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
				Global.GetSymbolName(td,name);
				Strings.Append(name,"@Info");
				source := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,NIL,dump);
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
				Global.GetSymbolName(td,name);
				MetaName(module,source,name);
				source.SetReferenced(FALSE);
				RETURN source;
		END NewTypeDescriptorInfo;

		PROCEDURE GetSection(x: SyntaxTree.Procedure): Sections.Section;
		VAR source: IntermediateCode.Section; sectionType: SHORTINT;
		BEGIN
			Global.GetSymbolName(x,name);
			IF x.HasFlag(SyntaxTree.InlineFlag) THEN
				sectionType := Sections.InlineCodeSection;
			ELSE
				sectionType := Sections.CodeSection;
			END;
			IF (x.scope.ownerModule = module.module) THEN
				source := IntermediateCode.NewSection(module.sections,sectionType,name,x,dump);
			ELSIF (sectionType = Sections.InlineCodeSection) & (x.procedureScope.body.code.sourceCode # NIL) THEN
				HALT(200);
			ELSE
				source := IntermediateCode.NewSection(module.importedSymbols,sectionType,name,x,dump);
			END;
			RETURN source
		END GetSection;

		PROCEDURE NewTypeDescriptor;
		VAR name: SyntaxTree.String; op: IntermediateCode.Operand; source: IntermediateCode.Section;
			i,methods: LONGINT;
			procedure: SyntaxTree.Procedure;
			baseRecord: SyntaxTree.RecordType; baseTD: SyntaxTree.TypeDeclaration;
			numberPointers: LONGINT;  padding,offset: LONGINT;
		CONST MPO=-40000000H;
		BEGIN
				Global.GetSymbolName(td,name);
				source := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,td,dump);

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
				IntermediateCode.InitImmediate(op,GetType(module.system, Global.Address),MPO-4);
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
					Global.GetSymbolName(baseTD,name);
					IF (baseTD.scope = NIL) OR (baseTD.scope.ownerModule = module.module) THEN
						tir := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,baseTD,dump);
					ELSE
						tir := IntermediateCode.NewSection(module.importedSymbols, Sections.ConstSection,name,baseTD,dump);
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
				MetaInfo(source, "padding");
				FOR i := 1 TO padding DO MetaAddress(module,source,0) END;
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

			section :=module.sections.FindBySymbol(td);
			IF (section = NIL) OR (section(IntermediateCode.Section).pc = 0) THEN
				IF newObjectFile THEN
					IF (td.scope = NIL) OR (td.scope.ownerModule = module.module) THEN
						NewTypeDescriptor
					END;
				ELSE
					(* data section in intermediate code *)
					Global.GetSymbolName(td,name);
					tir := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,td,dump);
					IntermediateCode.InitImmediate(op,GetType(module.system, Global.Address),0);
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
		op.dimOffset := 0;
	END InitOperand;

	PROCEDURE GetType(system: Global.System; type: SyntaxTree.Type): IntermediateCode.Type;
	BEGIN
		type := type.resolved;
		IF type IS SyntaxTree.CharacterType THEN
			ASSERT((type = Global.Char8) OR (type=Global.Char16) OR (type=Global.Char32));
			RETURN UnsignedIntegerType(system.SizeOf(type))
		ELSIF type IS SyntaxTree.IntegerType THEN
			ASSERT((type = Global.Shortint) OR (type = Global.Integer) OR (type = Global.Longint ) OR (type = Global.Hugeint));
			RETURN SignedIntegerType(system.SizeOf(type))
		ELSIF type IS SyntaxTree.FloatType THEN
			ASSERT((type = Global.Real) OR (type=Global.Longreal));
			RETURN FloatType(system.SizeOf(type))
		ELSIF type IS SyntaxTree.BasicType THEN
			IF type = Global.Size THEN RETURN SignedIntegerType(system.SizeOf(type))
			ELSE
				ASSERT( (type = Global.Address) OR (type = Global.Byte) OR (type = Global.Set) OR (type = Global.Boolean) OR (type = Global.Nil)
				OR (type = Global.Object) OR (type = Global.Any));
				RETURN UnsignedIntegerType(system.SizeOf(type))
			END;
		ELSIF type IS SyntaxTree.PointerType THEN
			RETURN GetType(system,Global.Address)
		ELSIF type IS SyntaxTree.EnumerationType THEN
			RETURN int32
		ELSIF type IS SyntaxTree.ProcedureType THEN
			RETURN GetType(system,Global.Address)
		ELSIF type IS SyntaxTree.MathArrayType THEN
			ASSERT(type(SyntaxTree.MathArrayType).form IN {SyntaxTree.Static, SyntaxTree.Tensor});
			RETURN GetType(system,Global.Address);
		ELSE
 			HALT(100);
		END;
	END GetType;

	PROCEDURE UniqueId(VAR name: ARRAY OF CHAR; module: SyntaxTree.Module; CONST base: ARRAY OF CHAR; VAR number: LONGINT);
	VAR n: SyntaxTree.String;
	BEGIN
		COPY(base,n);
		module.name.GetString(name); Strings.Append(name,"."); Strings.Append(name,"@"); Strings.Append(name,n); Basic.AppendNumber(name,number);
		INC(number);
	END UniqueId;

	PROCEDURE BuildConstant(module: SyntaxTree.Module; value: SyntaxTree.Value; VAR adr: LONGINT): SyntaxTree.Constant;
	VAR name: Scanner.StringType; constant: SyntaxTree.Constant;
	BEGIN
		name := "const";
		UniqueId(name,module,name,adr);
		constant := SyntaxTree.NewConstant(-1,SyntaxTree.NewIdentifier(-1,name));
		constant.SetValue(value);
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

	PROCEDURE IsOberonProcedure(type: SyntaxTree.ProcedureType): BOOLEAN;
	BEGIN
		RETURN type.flags * {SyntaxTree.WinAPIFlag,SyntaxTree.CFlag} = {}
	END IsOberonProcedure;

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
		ELSIF type = Global.Object THEN
			RETURN TRUE
		ELSIF type = Global.Any THEN
			RETURN TRUE (*! potentially is a pointer to record, treat it this way?? *)
		ELSE
			HALT(200)
		END;
	END IsPointerToRecord;

	PROCEDURE IsArrayOfSystemByte(type: SyntaxTree.Type): BOOLEAN;
	BEGIN
		type := type.resolved;
		RETURN (type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form = SyntaxTree.Open)
		& (type(SyntaxTree.ArrayType).arrayBase.resolved = Global.Byte);
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
		RETURN (type IS SyntaxTree.ProcedureType) & (SyntaxTree.DelegateFlag IN type(SyntaxTree.ProcedureType).flags)
	END IsDelegate;

	PROCEDURE DynamicDim(type:SyntaxTree.Type): LONGINT;
	VAR i: LONGINT;
	BEGIN
		i := 0; type := type.resolved;
		WHILE(type IS SyntaxTree.ArrayType) & (type(SyntaxTree.ArrayType).form # SyntaxTree.Static) DO
			INC(i);
			type := type(SyntaxTree.ArrayType).arrayBase.resolved;
		END;
		WHILE(type IS SyntaxTree.MathArrayType) & (type(SyntaxTree.MathArrayType).form # SyntaxTree.Static) DO
			INC(i);
			type := type(SyntaxTree.MathArrayType).arrayBase.resolved;
		END;
		RETURN i
	END DynamicDim;

	PROCEDURE ParametersSize(system: Global.System; procedureType: SyntaxTree.ProcedureType; isNested: BOOLEAN): LONGINT;
	VAR parSize: LONGINT; parameter: SyntaxTree.Parameter;
	BEGIN
		parSize := 0;
		parameter :=procedureType.lastParameter;
		WHILE (parameter # NIL) DO
			INC(parSize,system.SizeOfParameter(parameter));
			parSize := parSize + (-parSize) MOD system.addressSize;
			parameter := parameter.prevParameter;
		END;
		(*
		IF procedureType.HasFlag(SyntaxTree.DelegateFlag) THEN INC(parSize,system.addressSize) END; (* method => self pointer *)
			NO, SELF is encoded as regular parameter
		*)
		IF isNested THEN INC(parSize,system.addressSize) END; (* nested procedure => static base *)
		IF (procedureType.returnType # NIL) & ~(procedureType.returnType.resolved IS SyntaxTree.BasicType)
				& ~(procedureType.returnType.resolved IS SyntaxTree.ProcedureType)
				& ~(procedureType.returnType.resolved IS SyntaxTree.PointerType)
				& ~((procedureType.returnType.resolved IS SyntaxTree.RecordType) & (procedureType.returnType.resolved(SyntaxTree.RecordType).pointerType # NIL))
		THEN
			IF procedureType.returnParameter = NIL THEN (* otherwise handled by caller *)
				parSize := parSize + 2*system.addressSize
			END
		END;

		RETURN ToMemoryUnits(system,parSize)
	END ParametersSize;

	PROCEDURE IsNested(procedure: SyntaxTree.Procedure): BOOLEAN;
	BEGIN
		RETURN procedure.scope IS SyntaxTree.ProcedureScope
	END IsNested;


	PROCEDURE ProcedureParametersSize(system: Global.System; procedure: SyntaxTree.Procedure): LONGINT;
	BEGIN
		RETURN ParametersSize(system,procedure.type(SyntaxTree.ProcedureType),IsNested(procedure));
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

	PROCEDURE Return(parSize: LONGINT): IntermediateCode.Instruction;
 	VAR op1: IntermediateCode.Operand;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IntermediateCode.InitNumber(op1,parSize);
		IntermediateCode.InitInstruction(instruction,IntermediateCode.return,op1,emptyOperand,emptyOperand);
		RETURN instruction
	END Return;

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

	PROCEDURE Fill(dest,src,size: IntermediateCode.Operand; down: BOOLEAN):IntermediateCode.Instruction;
	VAR instruction: IntermediateCode.Instruction;
	BEGIN
		IF down THEN
			IntermediateCode.InitInstruction(instruction,IntermediateCode.filldown,dest,src,size);
		ELSE
			IntermediateCode.InitInstruction(instruction,IntermediateCode.fillup,dest,src,size);
		END;
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
		WHILE (pc<data.pc) & ~ProvidesValue(data.instr[pc],vop) DO
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
			name := "$SystemCall";
			Basic.AppendNumber(name,i);
			systemCalls[i] := SyntaxTree.NewSymbol(SyntaxTree.NewIdentifier(-1,name));
		END;
	END Init;


BEGIN
	Init;

END OCIntermediateBackend.
