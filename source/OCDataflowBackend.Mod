MODULE OCDataflowBackend; (** AUTHOR ""; PURPOSE ""; *)

IMPORT SyntaxTree := OCSyntaxTree, SemanticChecker := OCSemanticChecker, Backend := OCBackend, Global := OCGlobal,
 	Diagnostics, Strings, Options, Formats := OCFormats, SymbolFileFormat := OCTextualSymbolFile, D := Debugging,
	Dataflow := OCDataflow, Basic := OCBasic;

TYPE

	DeclarationVisitor* =OBJECT(SyntaxTree.Visitor)
	VAR
		backend: Backend.Backend;
		implementationVisitor: ImplementationVisitor;
		system: Global.System;
		currentScope: SyntaxTree.Scope;
		module: SyntaxTree.Module;

		PROCEDURE & Init*(system: Global.System; implementationVisitor: ImplementationVisitor; backend: Backend.Backend);
		BEGIN
			currentScope := NIL;
			SELF.system := system; SELF.implementationVisitor := implementationVisitor;
			SELF.backend := backend;
		END Init;

		PROCEDURE Error(position: LONGINT; CONST s: ARRAY OF CHAR);
		BEGIN
			backend.Error("", position, Diagnostics.Invalid, s);
		END Error;

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
		BEGIN (* no further traversal to x.resolved necessary since type descriptor and code will be inserted at "original" position ? *)
		END VisitQualifiedType;

		PROCEDURE VisitStringType(x: SyntaxTree.StringType);
		BEGIN (* no code emission *)   END VisitStringType;

		PROCEDURE VisitRangeType(x: SyntaxTree.RangeType);
		BEGIN (* no code emission *)   END VisitRangeType;

		PROCEDURE VisitArrayType(x: SyntaxTree.ArrayType);
		BEGIN (* no code emission *)   END VisitArrayType;

		PROCEDURE VisitMathArrayType(x: SyntaxTree.MathArrayType);
		BEGIN
		END VisitMathArrayType;

		PROCEDURE VisitPointerType(x: SyntaxTree.PointerType);
		BEGIN	END VisitPointerType;

		PROCEDURE VisitRecordType(x: SyntaxTree.RecordType);
		BEGIN	END VisitRecordType;

		PROCEDURE VisitActorType(x: SyntaxTree.ActorType);
		BEGIN	END VisitActorType;

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
		BEGIN	Procedure(x);
		END VisitOperator;

		PROCEDURE VisitVariable(x: SyntaxTree.Variable);
		BEGIN	END VisitVariable;

		PROCEDURE VisitTypeDeclaration(x: SyntaxTree.TypeDeclaration);
		BEGIN	END VisitTypeDeclaration;

		PROCEDURE VisitConstant(x: SyntaxTree.Constant);
		BEGIN	END VisitConstant;


		PROCEDURE Scope(x: SyntaxTree.Scope);
		VAR procedure: SyntaxTree.Procedure;
			constant: SyntaxTree.Constant;
			variable: SyntaxTree.Variable;
			prevScope: SyntaxTree.Scope;  typeDeclaration: SyntaxTree.TypeDeclaration;
		BEGIN
			IF x IS SyntaxTree.ActorScope THEN implementationVisitor.currentActorScope := x(SyntaxTree.ActorScope) END;
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

			IF x IS SyntaxTree.ActorScope THEN implementationVisitor.currentActorScope := NIL END;
			currentScope := prevScope;
		END Scope;

		PROCEDURE DataflowBody(x: SyntaxTree.Body);
		BEGIN
			implementationVisitor.VisitStatementBlock(x);
		END DataflowBody;

		PROCEDURE Procedure(x: SyntaxTree.Procedure);
		VAR
			scope: SyntaxTree.ProcedureScope;
			prevScope: SyntaxTree.Scope;
			inline: BOOLEAN;
			name: SyntaxTree.String;
		BEGIN
			(*
			IF Trace & (dump # NIL) THEN dump.String("DeclarationVisitor:Procedure"); dump.Ln END;
			*)
			(* code section for this procedure *)
			scope := x.procedureScope;
			prevScope := currentScope;
			currentScope := scope;

			Global.GetSymbolName(x,name);
			IF x = module.moduleScope.bodyProcedure THEN
				inline := FALSE;
				IF (scope.body # NIL) & (SyntaxTree.DataflowFlag IN scope.body.flags) THEN
					DataflowBody(scope.body);
				END;
			END
		END Procedure;

		(** entry function to visit a complete module *)
		PROCEDURE Module*(x: SyntaxTree.Module);
		BEGIN
			ASSERT(x # NIL); module := x;
			implementationVisitor.moduleScope := x.moduleScope;
			Scope(x.moduleScope);
		END Module;

	END DeclarationVisitor;


	ImplementationVisitor*=OBJECT(SyntaxTree.Visitor)
	VAR
		system: Global.System;
		moduleScope : SyntaxTree.ModuleScope; (* shortcut for module.module.moduleScope *)

		checker: SemanticChecker.Checker;
		backend: Backend.Backend;
		position: LONGINT;

		(* variables for hand over of variables /  temporary state *)
		currentScope: SyntaxTree.Scope;
		currentActorScope: SyntaxTree.ActorScope;

		PROCEDURE & Init*(system: Global.System; checker: SemanticChecker.Checker; backend: Backend.Backend);
		BEGIN
			SELF.system := system;
			SELF.checker := checker;
			SELF.backend := backend;

			currentScope := NIL;
			currentActorScope := NIL;
		END Init;

		PROCEDURE Error(position: LONGINT; CONST s: ARRAY OF CHAR);
		BEGIN
			backend.Error("",position,Diagnostics.Invalid,s);
		END Error;

		PROCEDURE Symbol(x: SyntaxTree.Symbol);
		BEGIN
			position := x.position;
			x.Accept(SELF);
		END Symbol;

		PROCEDURE Expression(x: SyntaxTree.Expression);
		BEGIN
			position := x.position;
			IF x.resolved # NIL THEN
				x.resolved.Accept(SELF)
			ELSE
				x.Accept(SELF)
			END;
		END Expression;

		PROCEDURE Statement(x: SyntaxTree.Statement);
		BEGIN
			position := x.position;
			x.Accept(SELF);
		END Statement;

		(** expressions *)
		PROCEDURE VisitSet(x: SyntaxTree.Set);
		BEGIN
		END VisitSet;

		PROCEDURE VisitMathArrayExpression(x: SyntaxTree.MathArrayExpression);
		BEGIN
		END VisitMathArrayExpression;

		PROCEDURE VisitUnaryExpression(x: SyntaxTree.UnaryExpression);
		BEGIN
		END VisitUnaryExpression;

		PROCEDURE VisitBinaryExpression(x: SyntaxTree.BinaryExpression);
		BEGIN
		END VisitBinaryExpression;

		PROCEDURE VisitRangeExpression(x: SyntaxTree.RangeExpression);
		BEGIN
		END VisitRangeExpression;

		PROCEDURE VisitTensorRangeExpression*(x: SyntaxTree.TensorRangeExpression);
		BEGIN
		END VisitTensorRangeExpression;

		PROCEDURE VisitConversion(x: SyntaxTree.Conversion);
		BEGIN
		END VisitConversion;

		PROCEDURE VisitTypeDeclaration(x: SyntaxTree.TypeDeclaration);
		BEGIN
		END VisitTypeDeclaration;

		(** designators (expressions) *)
		PROCEDURE VisitSymbolDesignator(x: SyntaxTree.SymbolDesignator);
		BEGIN
		END VisitSymbolDesignator;

		PROCEDURE VisitIndexDesignator(x: SyntaxTree.IndexDesignator);
		BEGIN
		END VisitIndexDesignator;

		PROCEDURE VisitProcedureCallDesignator(x: SyntaxTree.ProcedureCallDesignator);
		BEGIN
		END VisitProcedureCallDesignator;

		PROCEDURE VisitBuiltinCallDesignator(x: SyntaxTree.BuiltinCallDesignator);
		VAR p0,p1,p2: SyntaxTree.Expression;
		core,core1,core2: Dataflow.Core;
		port,port1,port2: Dataflow.Port;
		channel: Dataflow.Channel;
		type,t0,t1,t2: SyntaxTree.Type;
		name,name1,name2: SyntaxTree.String;
		formalParameter: SyntaxTree.Parameter;
		i,j,len,direction: LONGINT;
		parameterType: SyntaxTree.Type;

			PROCEDURE GetNumber(p: SyntaxTree.Expression): LONGINT;
			BEGIN
				IF (p.resolved# NIL) & (p.resolved IS SyntaxTree.IntegerValue) THEN RETURN p.resolved(SyntaxTree.IntegerValue).value END;
			END GetNumber;


			PROCEDURE GetPort(p: SyntaxTree.Expression): Dataflow.Port;
			VAR name1,name2: SyntaxTree.String; port: Dataflow.Port; number: LONGINT;
			BEGIN
				port := NIL;
				IF p IS SyntaxTree.IndexDesignator THEN
					number := GetNumber(p(SyntaxTree.IndexDesignator).parameters.GetExpression(0));
					p := p(SyntaxTree.IndexDesignator).left;
				ELSE
					number := -1
				END;

				Global.GetSymbolName(p(SyntaxTree.SymbolDesignator).left(SyntaxTree.SymbolDesignator).symbol,name1);
				p(SyntaxTree.SymbolDesignator).symbol.name.GetString(name2);
				core := Dataflow.FindCore(backend.dataflowSpecification.cores,name1);
				IF core = NIL THEN
					Error(p.position,"core not allocated");
				ELSE
					Strings.Append(name1,"."); Strings.Append(name1,name2);
					IF number # -1 THEN Strings.Append(name1,"["); Basic.AppendNumber(name1,number); Strings.Append(name1,"]"); END;
					port := Dataflow.FindPort(core.ports,name1);
					IF port = NIL THEN Error(p.position,"outport not available") END;
				END;
				RETURN port
			END GetPort;

		BEGIN
			p0 := NIL; p1 := NIL; p2 := NIL; len := x.parameters.Length();
			IF len > 0 THEN p0 := x.parameters.GetExpression(0); t0 := p0.type.resolved END;
			IF len > 1 THEN p1 := x.parameters.GetExpression(1); t1 := p1.type.resolved END;
			IF len > 2 THEN p2 := x.parameters.GetExpression(2); t2 := p2.type.resolved END;

			CASE x.id OF

			|Global.New:
				(*! the following code is only correct for "standard" Oberon calling convention *)
				type := p0.type.resolved;
				IF type IS SyntaxTree.ActorType THEN
					IF backend.dataflowSpecification = NIL THEN Error(p0.position,"no dataflow specification available"); RETURN END;
					(* generate actor by calling method on dataflow specification *)
					p0(SyntaxTree.SymbolDesignator).symbol.MarkUsed;
					Global.GetSymbolName(p0(SyntaxTree.SymbolDesignator).symbol,name);
					IF type.typeDeclaration # NIL THEN
						Global.GetSymbolName(type.typeDeclaration,name1)
					ELSE
						ASSERT(type(SyntaxTree.ActorType).actorScope IS SyntaxTree.ModuleScope);
						Global.GetSymbolName(type(SyntaxTree.ActorType).actorScope.ownerModule,name1);
					END;
					core := backend.dataflowSpecification.NewCore(name,name1);

					AddModules(core,type(SyntaxTree.ActorType).actorScope, type(SyntaxTree.ActorType).actorScope.ownerModule);

					formalParameter := type(SyntaxTree.ActorType).firstParameter; j := 0;
					WHILE formalParameter # NIL DO
						COPY(name,name2);
						Strings.Append(name2,".");
						formalParameter.name.GetString(name1);
						Strings.Append(name2,name1);
						parameterType := formalParameter.type.resolved;

						IF SemanticChecker.IsStaticArray(parameterType,parameterType,len) THEN
							direction := parameterType(SyntaxTree.PortType).direction;
							IF direction = SyntaxTree.OutPort THEN
								direction := Dataflow.Out
							ELSIF direction = SyntaxTree.InPort THEN
								direction := Dataflow.In
							END;
							FOR i := 0 TO len-1 DO
								COPY(name2,name1);
								Strings.Append(name1,"[");
								Basic.AppendNumber(name1,i);
								Strings.Append(name1,"]");
								port := core.NewPort(name1,direction,backend.dataflowSpecification.GetPortAddress(j));
								INC(j);
							END;
						ELSE
							COPY(name2,name1);
							direction := parameterType(SyntaxTree.PortType).direction;
							IF direction = SyntaxTree.OutPort THEN
								direction := Dataflow.Out
							ELSIF direction = SyntaxTree.InPort THEN
								direction := Dataflow.In
							END;
							port := core.NewPort(name1,direction,backend.dataflowSpecification.GetPortAddress(j));
							INC(j);
						END;
						formalParameter := formalParameter.nextParameter;
					END;
				ELSE
					HALT(200);
				END;
			(* ----- CONNECT ------*)
			|Global.Connect:
				port1 := GetPort(p0);
				port2 := GetPort(p1);
				(*
				Global.GetSymbolName(p0(SyntaxTree.SymbolDesignator).left(SyntaxTree.SymbolDesignator).symbol,name1);
				Global.GetSymbolName(p1(SyntaxTree.SymbolDesignator).left(SyntaxTree.SymbolDesignator).symbol,name2);
				p0(SyntaxTree.SymbolDesignator).symbol.MarkUsed;
				p1(SyntaxTree.SymbolDesignator).symbol.MarkUsed;
				p0(SyntaxTree.SymbolDesignator).symbol.name.GetString(name);
				core1 := Dataflow.FindCore(backend.dataflowSpecification.cores,name1);
				IF core1 = NIL THEN Error(p0.position,"core not allocated")
				ELSE
					Strings.Append(name1,"."); Strings.Append(name1,name);
					port1 := Dataflow.FindPort(core1.ports,name1);
					IF port1 = NIL THEN Error(p0.position,"outport not available") END;
				END;
				p1(SyntaxTree.SymbolDesignator).symbol.name.GetString(name);
				core2 := Dataflow.FindCore(backend.dataflowSpecification.cores,name2);
				IF core2 = NIL THEN Error(p1.position,"core not allocated")
				ELSE
					Strings.Append(name2,"."); Strings.Append(name2,name);
					port2 := Dataflow.FindPort(core2.ports,name2);
					IF port2 = NIL THEN Error(p1.position,"inport not available") END;
				END;
				*)
				IF (port1#NIL) & (port2#NIL) THEN
					channel := backend.dataflowSpecification.NewChannel(port1,port2);
				END;
			ELSE (* function not yet implemented *)
				Error(position,"not yet implemented");
			END;
		END VisitBuiltinCallDesignator;

		PROCEDURE VisitTypeGuardDesignator(x: SyntaxTree.TypeGuardDesignator);
		BEGIN
		END VisitTypeGuardDesignator;

		PROCEDURE VisitDereferenceDesignator(x: SyntaxTree.DereferenceDesignator);
		BEGIN
		END VisitDereferenceDesignator;

		PROCEDURE VisitSupercallDesignator(x: SyntaxTree.SupercallDesignator);
		BEGIN
		END VisitSupercallDesignator;

		PROCEDURE VisitSelfDesignator(x: SyntaxTree.SelfDesignator);
		BEGIN
		END VisitSelfDesignator;

		(** values *)
		PROCEDURE VisitBooleanValue(x: SyntaxTree.BooleanValue);
		END VisitBooleanValue;

		PROCEDURE VisitIntegerValue(x: SyntaxTree.IntegerValue);
		BEGIN
		END VisitIntegerValue;

		PROCEDURE VisitCharacterValue(x: SyntaxTree.CharacterValue);
		BEGIN
		END VisitCharacterValue;

		PROCEDURE VisitSetValue(x: SyntaxTree.SetValue);
		BEGIN
		END VisitSetValue;

		PROCEDURE VisitMathArrayValue(x: SyntaxTree.MathArrayValue);
		BEGIN
		END VisitMathArrayValue;

		PROCEDURE VisitConstant(x: SyntaxTree.Constant);
		BEGIN
			x.value.resolved.Accept(SELF);
		END VisitConstant;

		PROCEDURE VisitRealValue(x: SyntaxTree.RealValue);
		BEGIN
		END VisitRealValue;

		PROCEDURE VisitStringValue(x: SyntaxTree.StringValue);
		BEGIN
		END VisitStringValue;

		PROCEDURE VisitNilValue(x: SyntaxTree.NilValue);
		BEGIN
		END VisitNilValue;

		PROCEDURE VisitEnumerationValue(x: SyntaxTree.EnumerationValue);
		BEGIN
		END VisitEnumerationValue;

		(** symbols *)

		PROCEDURE VisitImport(x: SyntaxTree.Import);
		BEGIN (* nothing to be done, might however be called via some designator module.procedure *)
		END VisitImport;

		PROCEDURE VisitVariable(x: SyntaxTree.Variable);
		BEGIN
		END VisitVariable;

		PROCEDURE VisitParameter(x: SyntaxTree.Parameter);
		BEGIN
		END VisitParameter;

		PROCEDURE VisitProcedure(x: SyntaxTree.Procedure);
		BEGIN
		END VisitProcedure;

		PROCEDURE VisitOperator(x: SyntaxTree.Operator);
		BEGIN
		END VisitOperator;

		(** statements *)

		PROCEDURE VisitProcedureCallStatement(x: SyntaxTree.ProcedureCallStatement);
		BEGIN
			Expression(x.call);
		END VisitProcedureCallStatement;

		PROCEDURE VisitAssignment(x: SyntaxTree.Assignment);
		BEGIN
		END VisitAssignment;

		PROCEDURE VisitIfStatement(x: SyntaxTree.IfStatement);
		BEGIN
		END VisitIfStatement;

		PROCEDURE VisitWithStatement(x: SyntaxTree.WithStatement);
		BEGIN
		END VisitWithStatement;

		PROCEDURE VisitCaseStatement(x: SyntaxTree.CaseStatement);
		BEGIN
		END VisitCaseStatement;

		PROCEDURE VisitWhileStatement(x: SyntaxTree.WhileStatement);
		BEGIN
		END VisitWhileStatement;

		PROCEDURE VisitRepeatStatement(x: SyntaxTree.RepeatStatement);
		BEGIN
		END VisitRepeatStatement;

		PROCEDURE VisitForStatement(x: SyntaxTree.ForStatement);
		BEGIN
		END VisitForStatement;

		PROCEDURE VisitLoopStatement(x: SyntaxTree.LoopStatement);
		BEGIN
		END VisitLoopStatement;

		PROCEDURE VisitExitStatement(x: SyntaxTree.ExitStatement);
		BEGIN
		END VisitExitStatement;

		PROCEDURE VisitReturnStatement(x: SyntaxTree.ReturnStatement);
		BEGIN
		END VisitReturnStatement;

		PROCEDURE VisitAwaitStatement(x: SyntaxTree.AwaitStatement);
		BEGIN
		END VisitAwaitStatement;

		PROCEDURE StatementSequence(x: SyntaxTree.StatementSequence);
		VAR statement: SyntaxTree.Statement;  i: LONGINT; (* pos: LONGINT; *)
		BEGIN
			FOR i := 0 TO x.Length() - 1 DO
				statement := x.GetStatement( i );
				Statement(statement);
			END;
		END StatementSequence;

		PROCEDURE VisitStatementBlock(x: SyntaxTree.StatementBlock);
		BEGIN
			IF x.statements # NIL THEN
				StatementSequence(x.statements);
			END;
		END VisitStatementBlock;

	END ImplementationVisitor;

	DataflowBackend*= OBJECT (Backend.Backend)
	VAR

		PROCEDURE &InitDataflowBackend*;
		BEGIN
			InitBackend;
		END InitDataflowBackend;

		(* Work on a module *)
		PROCEDURE Module(x: SyntaxTree.Module): Formats.GeneratedModule;
		VAR
			declarationVisitor: DeclarationVisitor;
			implementationVisitor: ImplementationVisitor;
			name, instructionSet: SyntaxTree.String;
		BEGIN
			ResetError;
			Global.GetSymbolName(x,name);
			GetDescription(instructionSet);
			IF dataflowSpecification # NIL THEN dataflowSpecification.Init(name,instructionSet,diagnostics) END;
			NEW(implementationVisitor,system,checker,SELF);
			NEW(declarationVisitor,system,implementationVisitor,SELF);
			declarationVisitor.Module(x);

			RETURN NIL
		END Module;

		PROCEDURE DefineOptions(options: Options.Options);
		BEGIN
			DefineOptions^(options);
		END DefineOptions;

		PROCEDURE GetOptions(options: Options.Options);
		VAR name: SyntaxTree.String;
		BEGIN
			GetOptions^(options);
		END GetOptions;

		PROCEDURE DefaultSymbolFileFormat(): Formats.SymbolFileFormat;
		BEGIN RETURN SymbolFileFormat.Get()
		END DefaultSymbolFileFormat;

	END DataflowBackend;

	PROCEDURE GetDataflowSpecification(CONST name: ARRAY OF CHAR): Dataflow.Specification;
	VAR
		procname: ARRAY 256 OF CHAR;
		factory: PROCEDURE (): Dataflow.Specification;
		specification: Dataflow.Specification;
	BEGIN
		specification := NIL;
		IF Strings.Length(name) > 0 THEN
			GETPROCEDURE(name,"Get", factory); (* try long name for example -G=OCBinaryObjectFile *)
			IF factory = NIL THEN (* try short name for example -G=Binary*)
				procname := "OC";
				Strings.Append(procname, name);
				GETPROCEDURE(procname,"Get", factory);
			END;
			IF factory # NIL THEN
				specification := factory();
				ASSERT(specification # NIL);
			END;
		END;
		RETURN specification
	END GetDataflowSpecification;

	PROCEDURE AddModules(core: Dataflow.Core; scope: SyntaxTree.Scope; x: SyntaxTree.Module);

		PROCEDURE AddImport(x: SyntaxTree.Module);
		VAR module: Dataflow.Module; VAR name: SyntaxTree.String; device: Dataflow.Device;
		BEGIN
			IF ~Global.IsSystemModule(x) THEN
				x.name.GetString(name);
				IF ~(scope IS SyntaxTree.ActorScope) OR (scope(SyntaxTree.ActorScope).FindImport(x.name)#NIL) THEN
					device := Dataflow.FindDevice(core.specification.supportedDevices,name);
					IF device # NIL THEN
						device := core.NewDevice(device.name,device.adr)
					END;
				END;

				 IF (Dataflow.FindModule(core.modules,name) = NIL) THEN
					module := core.NewModule(name,"");
				END;
			END;
		END AddImport;

		PROCEDURE TraverseImports(x: SyntaxTree.Module);
		VAR import: SyntaxTree.Import; name: SyntaxTree.String;
		BEGIN
			import := x.moduleScope.firstImport;
			WHILE import # NIL DO
				TraverseImports(import.module);
				import := import.nextImport;
			END;
			x.name.GetString(name);
			AddImport(x);
		END TraverseImports;

	BEGIN
		TraverseImports(x);
	END AddModules;

	PROCEDURE Assert(cond: BOOLEAN; CONST reason: ARRAY OF CHAR);
	BEGIN ASSERT(cond);
	END Assert;

	PROCEDURE Get*(): Backend.Backend;
	VAR backend: DataflowBackend;
	BEGIN NEW(backend); RETURN backend
	END Get;

	PROCEDURE Init;
	BEGIN
	END Init;

BEGIN
	Init;
END OCDataflowBackend.
