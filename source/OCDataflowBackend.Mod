MODULE OCDataflowBackend; (** AUTHOR ""; PURPOSE ""; *)

IMPORT SyntaxTree := OCSyntaxTree, SemanticChecker := OCSemanticChecker, Backend := OCBackend, Global := OCGlobal,
 	Diagnostics, Strings, Options, Formats := OCFormats, SymbolFileFormat := OCTextualSymbolFile,
	Dataflow := OCDataflow, Basic := OCBasic;

CONST
	NotYetImplemented = "not yet implemented";
TYPE

	Value*=OBJECT
	VAR
		value: LONGINT; (* currently only support for integer values *)

		PROCEDURE &Init;
		BEGIN
			value := 0;
		END Init;

	END Value;

	Scope*=OBJECT
	VAR hashTable: Basic.HashTable;

		PROCEDURE &InitScope;
		BEGIN
			NEW(hashTable,32);
		END InitScope;

		PROCEDURE Put(symbol: SyntaxTree.Symbol; value: Value);
		BEGIN
			hashTable.Put(symbol, value);
		END Put;

		PROCEDURE Get(symbol: SyntaxTree.Symbol): Value;
		VAR a: ANY; value: Value;
		BEGIN
			a := hashTable.Get(symbol);
			IF a = NIL THEN NEW(value); Put(symbol, value) ELSE value := a(Value) END;
			RETURN value
		END Get;

	END Scope;

	Scopes= OBJECT
		VAR hashTable: Basic.HashTable;

		PROCEDURE &InitScopes;
		BEGIN
			NEW(hashTable,32);
		END InitScopes;

		PROCEDURE Put(s: SyntaxTree.Scope; scope: Scope);
		BEGIN
			hashTable.Put(s, scope);
		END Put;

		PROCEDURE Get(s: SyntaxTree.Scope): Scope;
		VAR a: ANY; scope: Scope;
		BEGIN
			a := hashTable.Get(s);
			IF a = NIL THEN NEW(scope); Put(s,scope) ELSE scope := a(Scope) END;
			RETURN scope
		END Get;

		END Scopes;


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

		(*
		PROCEDURE Error(position: LONGINT; CONST s: ARRAY OF CHAR);
		BEGIN
			backend.Error("", position, Diagnostics.Invalid, s);
		END Error;
		*)

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

		scopes: Scopes;

		resultScope: Scope;
		resultValue: Value;

		PROCEDURE & Init*(system: Global.System; checker: SemanticChecker.Checker; backend: Backend.Backend);
		BEGIN
			SELF.system := system;
			SELF.checker := checker;
			SELF.backend := backend;

			currentScope := NIL;
			currentActorScope := NIL;
			NEW(scopes);
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
			resultValue := NIL;
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
			Error(position,NotYetImplemented);
		END VisitSet;

		PROCEDURE VisitMathArrayExpression(x: SyntaxTree.MathArrayExpression);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitMathArrayExpression;

		PROCEDURE VisitUnaryExpression(x: SyntaxTree.UnaryExpression);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitUnaryExpression;

		PROCEDURE VisitBinaryExpression(x: SyntaxTree.BinaryExpression);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitBinaryExpression;

		PROCEDURE VisitRangeExpression(x: SyntaxTree.RangeExpression);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitRangeExpression;

		PROCEDURE VisitTensorRangeExpression*(x: SyntaxTree.TensorRangeExpression);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitTensorRangeExpression;

		PROCEDURE VisitConversion(x: SyntaxTree.Conversion);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitConversion;

		PROCEDURE VisitTypeDeclaration(x: SyntaxTree.TypeDeclaration);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitTypeDeclaration;

		(** designators (expressions) *)
		PROCEDURE VisitSymbolDesignator(x: SyntaxTree.SymbolDesignator);
		BEGIN
			Symbol(x.symbol);
		END VisitSymbolDesignator;

		PROCEDURE VisitIndexDesignator(x: SyntaxTree.IndexDesignator);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitIndexDesignator;

		PROCEDURE VisitProcedureCallDesignator(x: SyntaxTree.ProcedureCallDesignator);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitProcedureCallDesignator;

		PROCEDURE VisitBuiltinCallDesignator(x: SyntaxTree.BuiltinCallDesignator);
		VAR p0,p1,p2: SyntaxTree.Expression;
		core: Dataflow.Core;
		port,port1,port2: Dataflow.Port;
		channel: Dataflow.Channel;
		type,t0,t1,t2: SyntaxTree.Type;
		coreName, typeName, portName, name: SyntaxTree.String;
		formalParameter: SyntaxTree.Parameter;
		i,j,len,direction: LONGINT;
		parameterType: SyntaxTree.Type;
		CONST FullName= TRUE;

			PROCEDURE AppendIndex(VAR name: ARRAY OF CHAR; index: LONGINT);
			BEGIN
				Strings.Append(name,"["); Basic.AppendNumber(name,index); Strings.Append(name,"]");
			END AppendIndex;

			PROCEDURE Index(VAR e: SyntaxTree.Expression; VAR suffix: ARRAY OF CHAR);
			BEGIN
				IF e IS SyntaxTree.IndexDesignator THEN
					IF e(SyntaxTree.IndexDesignator).parameters.Length() # 1 THEN Error(e.position,"unsupported array dimension") END;
					Expression(e(SyntaxTree.IndexDesignator).parameters.GetExpression(0));
					suffix := ""; AppendIndex(suffix,resultValue.value);
					e := e(SyntaxTree.IndexDesignator).left;
				END;
			END Index;

			PROCEDURE GetCoreName(e: SyntaxTree.Expression; VAR coreName, typeName: ARRAY OF CHAR): BOOLEAN;
			VAR suffix: SyntaxTree.String; type: SyntaxTree.Type;
			BEGIN
				suffix := ""; type := e.type;
				Index(e,suffix);
				IF ~(e IS SyntaxTree.SymbolDesignator) THEN Error(e.position,"unsupported designator"); RETURN FALSE END;
				IF FullName THEN
					Global.GetSymbolName(e(SyntaxTree.SymbolDesignator).symbol, coreName);
				ELSE
					e(SyntaxTree.SymbolDesignator).symbol.name.GetString(coreName);
				END;
				Strings.Append(coreName, suffix);
				Global.GetSymbolName(type.typeDeclaration,typeName);
				RETURN TRUE
			END GetCoreName;


			PROCEDURE GetPort(p: SyntaxTree.Expression): Dataflow.Port;
			VAR name, coreName, typeName: SyntaxTree.String; port: Dataflow.Port; suffix: SyntaxTree.String;
			BEGIN
				Index(p, suffix);
				port := NIL;
				IF GetCoreName(p(SyntaxTree.SymbolDesignator).left, coreName, typeName) THEN
					p(SyntaxTree.SymbolDesignator).symbol.name.GetString(portName);
					core := Dataflow.FindCore(backend.dataflowSpecification.cores,coreName);
					IF core = NIL THEN
						Error(p.position,"core not allocated");
					ELSE
						IF FullName THEN
							COPY(coreName, name);
							Strings.Append(name,"."); Strings.Append(name,portName);
						ELSE
							COPY(portName, name);
						END;
						Strings.Append(name,suffix);
						port := Dataflow.FindPort(core.ports,name);
						IF port = NIL THEN Error(p.position,"outport not available") END;
					END;
				END;
				RETURN port
			END GetPort;

			PROCEDURE Direction(direction: LONGINT): LONGINT;
			BEGIN
				IF direction = SyntaxTree.OutPort THEN RETURN Dataflow.Out
				ELSIF direction = SyntaxTree.InPort THEN RETURN Dataflow.In
				ELSE HALT(100);
				END;
			END Direction;


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
					(* generate actor by calling method on dataflow specification *)
					IF GetCoreName(p0,coreName, typeName) THEN
						core := backend.dataflowSpecification.NewCore(coreName, typeName);
						AddModules(core,type(SyntaxTree.ActorType).actorScope, type(SyntaxTree.ActorType).actorScope.ownerModule);

						formalParameter := type(SyntaxTree.ActorType).firstParameter; j := 0;
						WHILE formalParameter # NIL DO
							IF FullName THEN
								COPY(coreName, portName);
								Strings.Append(portName,".");
							ELSE
								portName := ""
							END;
							formalParameter.name.GetString(name);
							Strings.Append(portName,name);
							parameterType := formalParameter.type.resolved;

							IF SemanticChecker.IsStaticArray(parameterType,parameterType,len) THEN
								direction := Direction(parameterType(SyntaxTree.PortType).direction);
								FOR i := 0 TO len-1 DO
									COPY(portName,name);
									AppendIndex(name,i);
									port := core.NewPort(name,direction,backend.dataflowSpecification.GetPortAddress(j));
									INC(j);
								END;
							ELSE
								direction := Direction(parameterType(SyntaxTree.PortType).direction);
								port := core.NewPort(portName,direction,backend.dataflowSpecification.GetPortAddress(j));
								INC(j);
							END;
							formalParameter := formalParameter.nextParameter;
						END;
					END;
				ELSE
					Error(x.position,NotYetImplemented)
				END;
			(* ----- CONNECT ------*)
			|Global.Connect:
				port1 := GetPort(p0);
				port2 := GetPort(p1);
				IF (port1#NIL) & (port2#NIL) THEN
					channel := backend.dataflowSpecification.NewChannel(port1,port2);
				END;
			ELSE (* function not yet implemented *)
				Error(position,NotYetImplemented);
			END;
		END VisitBuiltinCallDesignator;

		PROCEDURE VisitTypeGuardDesignator(x: SyntaxTree.TypeGuardDesignator);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitTypeGuardDesignator;

		PROCEDURE VisitDereferenceDesignator(x: SyntaxTree.DereferenceDesignator);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitDereferenceDesignator;

		PROCEDURE VisitSupercallDesignator(x: SyntaxTree.SupercallDesignator);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitSupercallDesignator;

		PROCEDURE VisitSelfDesignator(x: SyntaxTree.SelfDesignator);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitSelfDesignator;

		(** values *)
		PROCEDURE VisitBooleanValue(x: SyntaxTree.BooleanValue);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitBooleanValue;

		PROCEDURE VisitIntegerValue(x: SyntaxTree.IntegerValue);
		VAR value: Value;
		BEGIN
			NEW(value);
			value.value := x.value;
			resultValue := value;
		END VisitIntegerValue;

		PROCEDURE VisitCharacterValue(x: SyntaxTree.CharacterValue);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitCharacterValue;

		PROCEDURE VisitSetValue(x: SyntaxTree.SetValue);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitSetValue;

		PROCEDURE VisitMathArrayValue(x: SyntaxTree.MathArrayValue);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitMathArrayValue;

		PROCEDURE VisitConstant(x: SyntaxTree.Constant);
		BEGIN
			x.value.resolved.Accept(SELF);
		END VisitConstant;

		PROCEDURE VisitRealValue(x: SyntaxTree.RealValue);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitRealValue;

		PROCEDURE VisitStringValue(x: SyntaxTree.StringValue);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitStringValue;

		PROCEDURE VisitNilValue(x: SyntaxTree.NilValue);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitNilValue;

		PROCEDURE VisitEnumerationValue(x: SyntaxTree.EnumerationValue);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitEnumerationValue;

		(** symbols *)

		PROCEDURE VisitImport(x: SyntaxTree.Import);
		BEGIN (* nothing to be done, might however be called via some designator module.procedure *)
		END VisitImport;

		PROCEDURE VisitVariable(x: SyntaxTree.Variable);
		BEGIN
			IF x.type.resolved IS SyntaxTree.IntegerType THEN
				resultScope := scopes.Get(x.scope);
				resultValue := resultScope.Get(x);
			END;
		END VisitVariable;

		PROCEDURE VisitParameter(x: SyntaxTree.Parameter);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitParameter;

		PROCEDURE VisitProcedure(x: SyntaxTree.Procedure);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitProcedure;

		PROCEDURE VisitOperator(x: SyntaxTree.Operator);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitOperator;

		(** statements *)

		PROCEDURE VisitProcedureCallStatement(x: SyntaxTree.ProcedureCallStatement);
		BEGIN
			Expression(x.call);
		END VisitProcedureCallStatement;

		PROCEDURE VisitAssignment(x: SyntaxTree.Assignment);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitAssignment;

		PROCEDURE VisitIfStatement(x: SyntaxTree.IfStatement);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitIfStatement;

		PROCEDURE VisitWithStatement(x: SyntaxTree.WithStatement);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitWithStatement;

		PROCEDURE VisitCaseStatement(x: SyntaxTree.CaseStatement);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitCaseStatement;

		PROCEDURE VisitWhileStatement(x: SyntaxTree.WhileStatement);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitWhileStatement;

		PROCEDURE VisitRepeatStatement(x: SyntaxTree.RepeatStatement);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitRepeatStatement;

		PROCEDURE VisitForStatement(x: SyntaxTree.ForStatement);
		VAR variable, from, to: Value; value: LONGINT;
		BEGIN
			Expression(x.from);
			from := resultValue;
			Expression(x.to);
			to := resultValue;
			Expression(x.variable);
			variable := resultValue;

			FOR value := from.value TO to.value DO
				variable.value := value;
				StatementSequence(x.statements)
			END;
		END VisitForStatement;

		PROCEDURE VisitLoopStatement(x: SyntaxTree.LoopStatement);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitLoopStatement;

		PROCEDURE VisitExitStatement(x: SyntaxTree.ExitStatement);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitExitStatement;

		PROCEDURE VisitReturnStatement(x: SyntaxTree.ReturnStatement);
		BEGIN
			Error(position,NotYetImplemented);
		END VisitReturnStatement;

		PROCEDURE VisitAwaitStatement(x: SyntaxTree.AwaitStatement);
		BEGIN
			Error(position,NotYetImplemented);
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
		BEGIN
			GetOptions^(options);
		END GetOptions;

		PROCEDURE DefaultSymbolFileFormat(): Formats.SymbolFileFormat;
		BEGIN RETURN SymbolFileFormat.Get()
		END DefaultSymbolFileFormat;

	END DataflowBackend;

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
