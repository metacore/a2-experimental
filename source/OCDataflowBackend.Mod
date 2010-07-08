MODULE OCDataflowBackend; (** AUTHOR ""; PURPOSE ""; *)

IMPORT SyntaxTree := OCSyntaxTree, SemanticChecker := OCSemanticChecker, Backend := OCBackend, Global := OCGlobal,
 	Diagnostics, Strings, Options, Formats := OCFormats, SymbolFileFormat := OCTextualSymbolFile,
	Dataflow := OCDataflow, Basic := OCBasic, Scanner := OCScanner, Streams, Printout := OCPrintout;

CONST
	NotYetImplemented = "not yet implemented";
	FullName= TRUE;
TYPE

	Value*=OBJECT
	VAR
		type: SyntaxTree.Type;
		integer: LONGINT;
		boolean: BOOLEAN;
		string: SyntaxTree.String;

		PROCEDURE &Init(type: SyntaxTree.Type);
		BEGIN
			integer := 0; boolean := FALSE; SELF.type := type;
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
			IF a = NIL THEN NEW(value,symbol.type); Put(symbol, value) ELSE value := a(Value) END;
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

		PROCEDURE VisitNetworkType(x: SyntaxTree.NetworkType);
		BEGIN
			Scope(x.networkScope);
		END VisitNetworkType;

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
		VAR type, baseType: SyntaxTree.Type; i,len: LONGINT;

			PROCEDURE MakeCore(symbol: SyntaxTree.Symbol; type: SyntaxTree.ActorType; index: LONGINT);
			VAR coreName, typeName, portName, name: SyntaxTree.String;
				core: Dataflow.Core; formalParameter: SyntaxTree.Parameter; i,portIndex: LONGINT;
				parameterType: SyntaxTree.Type; direction, len: LONGINT;
				port: Dataflow.Port;
			BEGIN
				Global.GetSymbolName(symbol,coreName);
				Global.GetSymbolName(type.typeDeclaration,typeName);
				IF index >= 0 THEN
					AppendIndex(coreName,index);
				END;
				core := backend.dataflowSpecification.NewCore(coreName, typeName);
				AddModules(core,type.actorScope, type.actorScope.ownerModule);

				formalParameter := type.firstParameter; portIndex := 0;
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
							port := core.NewPort(name,direction,backend.dataflowSpecification.GetPortAddress(portIndex));
							INC(portIndex);
						END;
					ELSE
						direction := Direction(parameterType(SyntaxTree.PortType).direction);
						port := core.NewPort(portName,direction,backend.dataflowSpecification.GetPortAddress(portIndex));
						INC(portIndex);
					END;
					formalParameter := formalParameter.nextParameter;
				END;
			END MakeCore;

		BEGIN
			(*
			IF currentScope IS SyntaxTree.NetworkScope THEN
				type := x.type.resolved;
				IF ~SemanticChecker.IsStaticArray(type,baseType,len) THEN len := -1; baseType := type END;

				baseType := baseType.resolved;
				IF (baseType IS SyntaxTree.ActorType) THEN
					IF len = -1 THEN
						MakeCore(x,baseType(SyntaxTree.ActorType),-1);
					ELSE
						FOR i := 0 TO len-1 DO
							MakeCore(x,baseType(SyntaxTree.ActorType),i);
						END
					END;
				END;
			END;
			*)
		END VisitVariable;

		PROCEDURE VisitTypeDeclaration(x: SyntaxTree.TypeDeclaration);
		BEGIN
			x.declaredType.Accept(SELF)
		END VisitTypeDeclaration;

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
			implementationVisitor.currentScope := currentScope;
			implementationVisitor.VisitStatementBlock(x);
		END DataflowBody;

		PROCEDURE Procedure(x: SyntaxTree.Procedure);
		VAR
			scope: SyntaxTree.ProcedureScope;
			networkScope: SyntaxTree.NetworkScope;
			prevScope: SyntaxTree.Scope;
			inline: BOOLEAN;
			name: SyntaxTree.String;
		BEGIN
			(*
			IF Trace & (dump # NIL) THEN dump.String("DeclarationVisitor:Procedure"); dump.Ln END;
			*)
			(* code section for this procedure *)
			prevScope := currentScope;
			scope := x.procedureScope;
			currentScope := scope;

			Global.GetSymbolName(x,name);
			IF x = module.moduleScope.bodyProcedure THEN
				inline := FALSE;
				IF (scope.body # NIL) & (SyntaxTree.DataflowFlag IN scope.body.flags) THEN
					DataflowBody(scope.body);
				END;
			ELSIF InNetworkScope(scope, networkScope) & (x = networkScope.bodyProcedure) THEN
				DataflowBody(scope.body);
			END;
			currentScope := prevScope;
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
		error: BOOLEAN;
		exit: BOOLEAN;

		PROCEDURE & Init*(system: Global.System; checker: SemanticChecker.Checker; backend: Backend.Backend);
		BEGIN
			SELF.system := system;
			SELF.checker := checker;
			SELF.backend := backend;

			currentScope := NIL;
			currentActorScope := NIL;
			NEW(scopes);
			error := FALSE;
		END Init;

		PROCEDURE Error(position: LONGINT; CONST s: ARRAY OF CHAR);
		BEGIN
			backend.Error(moduleScope.ownerModule.sourceName,position,Diagnostics.Invalid,s);
			error := TRUE;
		END Error;

		PROCEDURE Symbol(x: SyntaxTree.Symbol);
		BEGIN
			IF error THEN RETURN END;
			position := x.position;
			x.Accept(SELF);
		END Symbol;

		PROCEDURE Expression(x: SyntaxTree.Expression);
		BEGIN
			IF error THEN RETURN END;
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
			IF error THEN RETURN END;
			position := x.position;
			x.Accept(SELF);
		END Statement;

		PROCEDURE Evaluate(x: SyntaxTree.Expression; VAR value: Value);
		BEGIN
			Expression(x);
			IF resultValue = NIL THEN Error(position,"could not evaluate"); END;
			value := resultValue
		END Evaluate;

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
		VAR leftValue: Value;
			PROCEDURE NewBoolean(b: BOOLEAN);
			BEGIN
				NEW(resultValue, Global.Boolean); resultValue.boolean := b
			END NewBoolean;

			PROCEDURE NewInteger(i: LONGINT);
			BEGIN
				NEW(resultValue, x.type); resultValue.integer := i;
			END NewInteger;
		BEGIN
			Evaluate(x.left, leftValue); IF error THEN RETURN END;
			IF x.left.type.resolved IS SyntaxTree.IntegerType THEN
				CASE x.operator OF
				Scanner.Minus: NewInteger(-leftValue.integer);
				ELSE
					Error(position,NotYetImplemented);
				END;
			ELSIF x.left.type.resolved = Global.Boolean THEN
				CASE x.operator OF
				Scanner.Not: NewBoolean(~leftValue.boolean)
				ELSE
					Error(position,NotYetImplemented);
				END;
			ELSE
				Error(position,NotYetImplemented);
			END;
		END VisitUnaryExpression;

		PROCEDURE VisitBinaryExpression(x: SyntaxTree.BinaryExpression);
		VAR leftValue, rightValue: Value;
			PROCEDURE NewBoolean(b: BOOLEAN);
			BEGIN
				NEW(resultValue, Global.Boolean); resultValue.boolean := b
			END NewBoolean;

			PROCEDURE NewInteger(i: LONGINT);
			BEGIN
				NEW(resultValue, x.type); resultValue.integer := i;
			END NewInteger;

		BEGIN
			Evaluate(x.left, leftValue); IF error THEN RETURN END;
			Evaluate(x.right, rightValue); IF error THEN RETURN END;
			IF x.left.type.resolved IS SyntaxTree.IntegerType THEN
				CASE x.operator OF
				Scanner.Equal: NewBoolean(leftValue.integer = rightValue.integer);
				|Scanner.Unequal: NewBoolean(leftValue.integer # rightValue.integer);
				|Scanner.Less: NewBoolean(leftValue.integer < rightValue.integer);
				|Scanner.LessEqual: NewBoolean(leftValue.integer <= rightValue.integer);
				|Scanner.Greater: NewBoolean(leftValue.integer > rightValue.integer);
				|Scanner.GreaterEqual: NewBoolean(leftValue.integer >= rightValue.integer);
				|Scanner.Plus: NewInteger(leftValue.integer + rightValue.integer);
				|Scanner.Minus: NewInteger(leftValue.integer + rightValue.integer);
				|Scanner.Times: NewInteger(leftValue.integer * rightValue.integer);
				|Scanner.Div: NewInteger(leftValue.integer DIV rightValue.integer);
				|Scanner.Mod: NewInteger(leftValue.integer DIV rightValue.integer);
				ELSE
					Error(x.position, NotYetImplemented);
				END;
			ELSIF x.left.type.resolved = Global.Boolean THEN
				CASE x.operator OF
				Scanner.Equal: NewBoolean(leftValue.boolean = rightValue.boolean);
				|Scanner.Unequal: NewBoolean(leftValue.boolean # rightValue.boolean);
				|Scanner.Or: NewBoolean(leftValue.boolean OR rightValue.boolean);
				|Scanner.And: NewBoolean(leftValue.boolean & rightValue.boolean);
				ELSE
					Error(x.position, NotYetImplemented);
				END;
			ELSE
				Error(x.position,NotYetImplemented)
			END;
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
		VAR integer: HUGEINT; type: SyntaxTree.Type; value: Value;
		BEGIN
			Evaluate(x.expression, value);
			type := x.type.resolved;
			IF (type = Global.Shortint) OR (type = Global.Integer) OR (type = Global.Longint) (* OR (type= Global.Hugeint) *)
				OR (type = system.sizeType) THEN
				integer := Global.ConvertSigned(value.integer,system.SizeOf(type));
				NEW(resultValue, type);
				resultValue.integer := SHORT(integer)
			ELSE
				Error(position,NotYetImplemented);
			END;
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
		networkScope: SyntaxTree.NetworkScope;

			PROCEDURE Index(VAR e: SyntaxTree.Expression; VAR suffix: ARRAY OF CHAR);
			BEGIN
				IF e IS SyntaxTree.IndexDesignator THEN
					IF e(SyntaxTree.IndexDesignator).parameters.Length() # 1 THEN Error(e.position,"unsupported array dimension") END;
					Expression(e(SyntaxTree.IndexDesignator).parameters.GetExpression(0));
					suffix := ""; AppendIndex(suffix,resultValue.integer);
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




		BEGIN
			p0 := NIL; p1 := NIL; p2 := NIL; len := x.parameters.Length();
			IF len > 0 THEN p0 := x.parameters.GetExpression(0); t0 := p0.type.resolved END;
			IF len > 1 THEN p1 := x.parameters.GetExpression(1); t1 := p1.type.resolved END;
			IF len > 2 THEN p2 := x.parameters.GetExpression(2); t2 := p2.type.resolved END;

			CASE x.id OF
			|Global.New:
				type := p0.type.resolved;
				(*IF InNetworkScope(currentScope,networkScope) THEN
					Error(x.position,"forbidden NEW statement in network scope");
				ELS
				*)
				IF type IS SyntaxTree.ActorType THEN
					(* generate actor by calling method on dataflow specification *)
					IF GetCoreName(p0,coreName, typeName) THEN
						core := Dataflow.FindCore(backend.dataflowSpecification.cores,coreName);
						IF core # NIL THEN 
							Error(p0.position,"forbidden double instantiation of core");
						ELSE
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
					END;
				ELSE
					Error(x.position,NotYetImplemented)
				END;
			(* ----- CONNECT ------*)
			|Global.Connect:
				port1 := GetPort(p0);
				port2 := GetPort(p1);
				IF (port1#NIL) & (port2#NIL) THEN
					IF Dataflow.FindChannelByPort(backend.dataflowSpecification.channels,port1) # NIL THEN
						Error(p0.position,"port already connected");
					ELSIF Dataflow.FindChannelByPort(backend.dataflowSpecification.channels,port2) # NIL THEN
						Error(p1.position,"port already connected");
					ELSE
						channel := backend.dataflowSpecification.NewChannel(port1,port2);
					END;
				END;
			|Global.systemTrace:
				SystemTrace(x.parameters);
			ELSE (* function not yet implemented *)
				Error(position,NotYetImplemented);
			END;
		END VisitBuiltinCallDesignator;

		PROCEDURE SystemTrace(x: SyntaxTree.ExpressionList);
		VAR
			stringWriter: Streams.StringWriter;
			s: SyntaxTree.String;
			printout: Printout.Printer;
			value: Value;
			expression: SyntaxTree.Expression;
			i: LONGINT;

			PROCEDURE String(CONST s: ARRAY OF CHAR);
			BEGIN
				stringWriter.String(s);
			END String;

			PROCEDURE Integer(i: LONGINT);
			BEGIN
				stringWriter.Int(i,1);
			END Integer;

			PROCEDURE Boolean(b: BOOLEAN);
			BEGIN
				IF b THEN stringWriter.String("TRUE") ELSE stringWriter.String("FALSE") END;
			END Boolean;


		BEGIN
			NEW(stringWriter,LEN(s));
			printout := Printout.NewPrinter(stringWriter,Printout.SourceCode,FALSE);
			FOR i := 0 TO x.Length()-1 DO
				expression := x.GetExpression(i);
				IF ~(expression IS SyntaxTree.StringValue) THEN
					printout.Expression(expression);
					stringWriter.String("= ");
				END;
				Evaluate(expression,value);
				IF error THEN RETURN END;
				IF expression.type.resolved IS SyntaxTree.IntegerType THEN
					Integer(value.integer);
				ELSIF expression.type.resolved = Global.Boolean THEN
					Boolean(value.boolean);
				ELSIF expression.type.resolved IS SyntaxTree.StringType THEN
					String(value.string);
				ELSE Error(expression.position,NotYetImplemented);
				END;
				stringWriter.String("; ");
			END;
			stringWriter.Get(s);
			expression := x.GetExpression(0);
			backend.diagnostics.Information(moduleScope.ownerModule.sourceName,expression.position, Diagnostics.Invalid,s);
		END SystemTrace;

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
		VAR value: Value;
		BEGIN
			NEW(value, x.type);
			value.boolean := x.value;
			resultValue := value;
		END VisitBooleanValue;

		PROCEDURE VisitIntegerValue(x: SyntaxTree.IntegerValue);
		VAR value: Value;
		BEGIN
			NEW(value,x.type);
			value.integer := x.value;
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
			NEW(resultValue, x.type);
			COPY(x.value, resultValue.string);
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
		VAR leftValue, rightValue: Value;
		BEGIN
			IF (x.left.type.resolved IS SyntaxTree.IntegerType) OR (x.left.type.resolved = Global.Boolean) THEN
				Evaluate(x.left, leftValue);
				Evaluate(x.right, rightValue);
				leftValue.integer := rightValue.integer;
				leftValue.boolean := rightValue.boolean;
			ELSE
				Error(position,NotYetImplemented);
			END;
		END VisitAssignment;

		PROCEDURE Condition(x: SyntaxTree.Expression): BOOLEAN;
		BEGIN
			Expression(x); ASSERT(resultValue # NIL); ASSERT(resultValue.type.resolved = Global.Boolean);
			RETURN resultValue.boolean
		END Condition;

		PROCEDURE VisitIfStatement(x: SyntaxTree.IfStatement);
		VAR done: BOOLEAN; elsif: SyntaxTree.IfPart; elsifs: LONGINT; i: LONGINT;

			PROCEDURE IfPart(if: SyntaxTree.IfPart);
			BEGIN
				IF Condition(if.condition) THEN
					StatementSequence(if.statements);
					done := TRUE;
				END;
			END IfPart;

		BEGIN
			done := FALSE;
			IfPart(x.ifPart);
			elsifs := x.ElsifParts();
			FOR i := 0 TO elsifs-1 DO
				IF ~done THEN
					elsif := x.GetElsifPart(i);
					IfPart(elsif);
				END;
			END;
			IF ~done & (x.elsePart # NIL) THEN
				StatementSequence(x.elsePart);
			END;
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
			WHILE ~error & Condition(x.condition) DO
				StatementSequence(x.statements)
			END;
		END VisitWhileStatement;

		PROCEDURE VisitRepeatStatement(x: SyntaxTree.RepeatStatement);
		BEGIN
			REPEAT
				StatementSequence(x.statements)
			UNTIL error OR Condition(x.condition);
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

			FOR value := from.integer TO to.integer DO
				IF error THEN RETURN END;
				variable.integer := value;
				StatementSequence(x.statements);
			END;
		END VisitForStatement;

		PROCEDURE VisitLoopStatement(x: SyntaxTree.LoopStatement);
		VAR prevExit: BOOLEAN;
		BEGIN
			prevExit := exit;
			exit := FALSE;
			LOOP
				StatementSequence(x.statements);
				IF exit OR error THEN EXIT END;
			END;
			exit := prevExit;
		END VisitLoopStatement;

		PROCEDURE VisitExitStatement(x: SyntaxTree.ExitStatement);
		BEGIN
			exit := TRUE;
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
			i := 0;
			WHILE ~exit & ~error &  (i< x.Length()) DO
				statement := x.GetStatement( i );
				Statement(statement);
				INC(i);
			END;
		END StatementSequence;

		PROCEDURE VisitStatementBlock(x: SyntaxTree.StatementBlock);
		BEGIN
			IF (x.statements # NIL) THEN
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

	PROCEDURE InNetworkScope(scope: SyntaxTree.Scope; VAR networkScope: SyntaxTree.NetworkScope): BOOLEAN;
	BEGIN
		WHILE (scope # NIL) & ~(scope IS SyntaxTree.NetworkScope) DO
			scope := scope.outerScope
		END;
		IF scope = NIL THEN
			networkScope := NIL;
			RETURN FALSE
		ELSE
			networkScope := scope(SyntaxTree.NetworkScope);
			RETURN TRUE
		END;
	END InNetworkScope;

	PROCEDURE AppendIndex(VAR name: ARRAY OF CHAR; index: LONGINT);
	BEGIN
		Strings.Append(name,"["); Basic.AppendNumber(name,index); Strings.Append(name,"]");
	END AppendIndex;

	PROCEDURE Direction(direction: LONGINT): LONGINT;
	BEGIN
		IF direction = SyntaxTree.OutPort THEN RETURN Dataflow.Out
		ELSIF direction = SyntaxTree.InPort THEN RETURN Dataflow.In
		ELSE HALT(100);
		END;
	END Direction;

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
