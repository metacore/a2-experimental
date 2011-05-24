MODULE FoxActiveCellsBackend; (** AUTHOR ""; PURPOSE ""; *)

IMPORT SyntaxTree := FoxSyntaxTree, SemanticChecker := FoxSemanticChecker, Backend := FoxBackend, Global := FoxGlobal,
 	Diagnostics, Strings, Options, Formats := FoxFormats, SymbolFileFormat := FoxTextualSymbolFile,
	ActiveCells := FoxActiveCells, Basic := FoxBasic, Scanner := FoxScanner, Streams, Printout := FoxPrintout;

CONST
	NotYetImplemented = "not yet implemented";
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
		currentActiveCellsScope: ActiveCells.Scope;
		module: SyntaxTree.Module;

		PROCEDURE & Init*(system: Global.System; implementationVisitor: ImplementationVisitor; backend: Backend.Backend);
		BEGIN
			currentScope := NIL;
			SELF.system := system; SELF.implementationVisitor := implementationVisitor;
			SELF.backend := backend;
			currentActiveCellsScope := backend.activeCellsSpecification;
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

		PROCEDURE VisitArrayRangeType(x: SyntaxTree.RangeType);
		BEGIN (* no code emission *)   END VisitArrayRangeType;

		PROCEDURE VisitArrayType(x: SyntaxTree.ArrayType);
		BEGIN (* no code emission *)   END VisitArrayType;

		PROCEDURE VisitMathArrayType(x: SyntaxTree.MathArrayType);
		BEGIN
		END VisitMathArrayType;

		PROCEDURE VisitPointerType(x: SyntaxTree.PointerType);
		BEGIN	END VisitPointerType;

		PROCEDURE VisitRecordType(x: SyntaxTree.RecordType);
		BEGIN	END VisitRecordType;

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
			WHILE (this # NIL) & (this.identifier# id) DO
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

		PROCEDURE VisitCellType(x: SyntaxTree.CellType);
		VAR componentName, parameterName, name: SyntaxTree.String; instanceType: ActiveCells.Type;
			parameter: SyntaxTree.Parameter; parameterType: SyntaxTree.Type; portIndex,i,direction,len: LONGINT;
			port: ActiveCells.Port;
			prevActiveCellsScope : ActiveCells.Scope;
			dataMemorySize, codeMemorySize: LONGINT;
		BEGIN
			prevActiveCellsScope := currentActiveCellsScope;
			x.typeDeclaration.GetName(componentName);
			instanceType := currentActiveCellsScope.NewType(componentName); (*backend.activeCellsSpecification.NewType(componentName);*)
			IF HasValue(x.modifiers,Global.StringDataMemorySize,dataMemorySize) THEN
				instanceType.SetDataMemorySize(dataMemorySize);
			END;
			IF HasValue(x.modifiers,Global.StringCodeMemorySize,codeMemorySize) THEN
				instanceType.SetInstructionMemorySize(codeMemorySize)
			END;

			currentActiveCellsScope := instanceType;
			parameter := x.firstParameter;
			portIndex := 0;
			WHILE parameter # NIL DO
				parameter.GetName(parameterName);
				parameterType := parameter.type.resolved;
				IF SemanticChecker.IsStaticArray(parameterType,parameterType,len) THEN
					direction := Direction(parameterType(SyntaxTree.PortType).direction);
					FOR i := 0 TO len-1 DO
						COPY(parameterName,name);
						AppendIndex(name,i);
						port := instanceType.NewPort(name,direction,backend.activeCellsSpecification.GetPortAddress(portIndex));
						port.SetWidth(parameterType(SyntaxTree.PortType).sizeInBits);
						INC(portIndex);
					END;
				ELSE
					direction := Direction(parameterType(SyntaxTree.PortType).direction);
					port := instanceType.NewPort(parameterName,direction,backend.activeCellsSpecification.GetPortAddress(portIndex));
					port.SetWidth(parameterType(SyntaxTree.PortType).sizeInBits);
					INC(portIndex);
				END;
				parameter := parameter.nextParameter;
			END;
			Scope(x.cellScope);
			currentActiveCellsScope := prevActiveCellsScope;
			AddModules(instanceType,x.cellScope);
		END VisitCellType;

		PROCEDURE VisitProcedureType(x: SyntaxTree.ProcedureType);
		BEGIN (* no code emission *)   END VisitProcedureType;

		PROCEDURE VisitEnumerationType(x: SyntaxTree.EnumerationType);
		BEGIN (* no code emission, exported enumeration type values should be included in symbol file *)
		END VisitEnumerationType;

		(* symbols *)
		PROCEDURE VisitImport(x: SyntaxTree.Import);
		VAR name: SyntaxTree.String;
		BEGIN
			x.module.GetName(name);
			backend.activeCellsSpecification.AddImport(name);
		END VisitImport;

		PROCEDURE VisitProcedure(x: SyntaxTree.Procedure);
		BEGIN
			Procedure(x);
		END VisitProcedure;

		PROCEDURE VisitOperator(x: SyntaxTree.Operator);
		BEGIN	Procedure(x);
		END VisitOperator;

		PROCEDURE VisitVariable(x: SyntaxTree.Variable);
		BEGIN
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
			import: SyntaxTree.Import;
			prevScope: SyntaxTree.Scope;  typeDeclaration: SyntaxTree.TypeDeclaration;
		BEGIN
			IF x IS SyntaxTree.CellScope THEN implementationVisitor.currentCellScope := x(SyntaxTree.CellScope) END;
			prevScope := currentScope;
			currentScope := x;
			(* constants treated in implementation visitor  *)

			IF x IS SyntaxTree.ModuleScope THEN
				import := x(SyntaxTree.ModuleScope).firstImport;
				WHILE import # NIL DO
					VisitImport(import); import := import.nextImport
				END;
			END;

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

		PROCEDURE CellNetBody(x: SyntaxTree.Body);
		BEGIN
			implementationVisitor.currentScope := currentScope;
			implementationVisitor.currentActiveCellsScope := currentActiveCellsScope;
			implementationVisitor.VisitStatementBlock(x);
		END CellNetBody;

		PROCEDURE Procedure(x: SyntaxTree.Procedure);
		VAR
			scope: SyntaxTree.ProcedureScope;
			prevScope: SyntaxTree.Scope;
		BEGIN
			(*
			IF Trace & (dump # NIL) THEN dump.String("DeclarationVisitor:Procedure"); dump.Ln END;
			*)
			(* code section for this procedure *)
			prevScope := currentScope;
			scope := x.procedureScope;
			currentScope := scope;

			IF  (x.scope IS SyntaxTree.ModuleScope)
				&  (x= x.scope(SyntaxTree.ModuleScope).bodyProcedure)
				& (module.isCellNet)
				OR
				(x.scope IS SyntaxTree.CellScope)
				& (x= x.scope(SyntaxTree.CellScope).bodyProcedure)
				& (x.scope(SyntaxTree.CellScope).ownerCell.isCellNet)
			THEN
				IF scope.body # NIL THEN
					CellNetBody(scope.body);
				END;
			END;
			currentScope := prevScope;
		END Procedure;

		(** entry function to visit a complete module *)
		PROCEDURE Module*(x: SyntaxTree.Module);
		BEGIN
			ASSERT(x # NIL); module := x;
			currentActiveCellsScope := backend.activeCellsSpecification;
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
		currentCellScope: SyntaxTree.CellScope;
		currentActiveCellsScope: ActiveCells.Scope;

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
			currentCellScope := NIL;
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
				NEW(resultValue, system.booleanType); resultValue.boolean := b
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
			ELSIF x.left.type.resolved IS SyntaxTree.BooleanType THEN
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
				NEW(resultValue, system.booleanType); resultValue.boolean := b
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
			ELSIF x.left.type.resolved IS SyntaxTree.BooleanType THEN
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
			IF (type IS SyntaxTree.IntegerType) & (type.sizeInBits < 64)
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
		VAR p,p0,p1,p2: SyntaxTree.Expression;
			instanceType: ActiveCells.Type;
			port0,port1: ActiveCells.Port;
			channel: ActiveCells.Channel;
			type,t0,t1,t2: SyntaxTree.Type;
			instanceName, typeName, portName: SyntaxTree.String;
			len: LONGINT;
			instance,instance0,instance1: ActiveCells.Instance;
			symbol: ActiveCells.Symbol;
			i: LONGINT; value: Value; par: ActiveCells.Parameter;
			constructor: SyntaxTree.Procedure;
			parameter: SyntaxTree.Parameter;
			name: SyntaxTree.String;

			PROCEDURE Index(VAR e: SyntaxTree.Expression; VAR suffix: ARRAY OF CHAR);
			BEGIN
				IF (e # NIL)&  (e IS SyntaxTree.IndexDesignator) THEN
					IF e(SyntaxTree.IndexDesignator).parameters.Length() # 1 THEN Error(e.position,"unsupported array dimension") END;
					Expression(e(SyntaxTree.IndexDesignator).parameters.GetExpression(0));
					suffix := ""; AppendIndex(suffix,resultValue.integer);
					e := e(SyntaxTree.IndexDesignator).left;
				END;
			END Index;

			PROCEDURE GetInstanceName(e: SyntaxTree.Expression; VAR instanceName, typeName: ARRAY OF CHAR): BOOLEAN;
			VAR suffix: SyntaxTree.String; type: SyntaxTree.Type; name: SyntaxTree.String;
			BEGIN
				suffix := "";
				type := e.type.resolved;
				Index(e,suffix);
				IF ~(e IS SyntaxTree.SymbolDesignator) THEN Error(e.position,"unsupported designator"); RETURN FALSE
				END;

				WHILE (e # NIL) & (e IS SyntaxTree.SymbolDesignator) DO
					e(SyntaxTree.SymbolDesignator).symbol.GetName(name);
					IF instanceName # "" THEN
						Strings.Append(name,".");
						Strings.Append(name, instanceName);
					END;
					COPY(name,instanceName);
					e := e(SyntaxTree.SymbolDesignator).left
				END;
				Strings.Append(instanceName, suffix);
				IF (type.typeDeclaration # NIL) & (type.typeDeclaration.scope.ownerModule # moduleScope.ownerModule) THEN Global.GetSymbolName(type.typeDeclaration,typeName)
				ELSIF (type.typeDeclaration # NIL) THEN
					type.typeDeclaration.GetName(typeName);
				ELSE typeName := ""
				END;
				RETURN TRUE
			END GetInstanceName;

			PROCEDURE GetPort(p: SyntaxTree.Expression; VAR instance: ActiveCells.Instance; VAR port: ActiveCells.Port): BOOLEAN;
			VAR name, instanceName, typeName: SyntaxTree.String; suffix: SyntaxTree.String; type: SyntaxTree.Type;
			BEGIN
				type := p.type;
				Index(p, suffix);
				port := NIL;
				IF (type IS SyntaxTree.PortType) & GetInstanceName(p(SyntaxTree.SymbolDesignator).left, instanceName, typeName) THEN
					instance := currentActiveCellsScope.instances.ByName(instanceName);
					IF instance = NIL THEN Error(p.position,"not allocated"); RETURN FALSE END;
					instanceType := instance.type;
					p(SyntaxTree.SymbolDesignator).symbol.GetName(portName);
					IF instanceType = NIL THEN
						Error(p.position,"cell type could not be derived"); RETURN FALSE
					ELSE
						COPY(portName, name); Strings.Append(name,suffix);
						port := instanceType.ports.ByName(name);
						IF port = NIL THEN Error(p.position,"port not available"); Error(p.position,name); RETURN FALSE END;
					END;
					RETURN TRUE
				ELSE
					RETURN FALSE
				END;
			END GetPort;

			(*
			PROCEDURE GetChannel(p: SyntaxTree.Expression; VAR channel: ActiveCells.Channel): BOOLEAN;
			VAR name, instanceName: SyntaxTree.String; suffix: SyntaxTree.String;
			BEGIN
				Index(p,suffix);
				channel := NIL;
				IF (p.type.resolved IS SyntaxTree.ChannelType) & GetInstanceName(p, instanceName, typeName) THEN
					channel := currentActiveCellsScope.channels.ByName(instanceName);
				END;
				RETURN channel # NIL
			END GetChannel;
			*)

			PROCEDURE GetDelegatePort(p: SyntaxTree.Expression; VAR port: ActiveCells.Port): BOOLEAN;
			VAR portName, suffix: SyntaxTree.String;
			BEGIN
				Index(p,suffix);
				p(SyntaxTree.SymbolDesignator).symbol.GetName(portName);
				Strings.Append(portName,suffix);
				port := currentActiveCellsScope.ports.ByName(portName);
				IF port = NIL THEN Error(p.position,"port not available") END;
				RETURN port # NIL
			END GetDelegatePort;


		BEGIN
			p0 := NIL; p1 := NIL; p2 := NIL; len := x.parameters.Length();
			IF len > 0 THEN p0 := x.parameters.GetExpression(0); t0 := p0.type.resolved END;
			IF len > 1 THEN p1 := x.parameters.GetExpression(1); t1 := p1.type.resolved END;
			IF len > 2 THEN p2 := x.parameters.GetExpression(2); t2 := p2.type.resolved END;

			CASE x.id OF
			(* ----- NEW -----*)
			|Global.New:
				type := p0.type.resolved;
				IF type IS SyntaxTree.CellType THEN
					(* generate actor by calling method on activeCells specification *)
					IF GetInstanceName(p0,instanceName, typeName) THEN
						symbol := ActiveCells.GetSymbol(currentActiveCellsScope,typeName);
						IF (symbol = NIL) OR ~(symbol IS ActiveCells.Type) THEN
							Error(p0.position,"could not find type");
							Error(p0.position,typeName);
						ELSE
							instanceType := symbol(ActiveCells.Type);
						END;
						instance := currentActiveCellsScope.NewInstance(instanceName, instanceType);
					END;
					constructor := type(SyntaxTree.CellType).cellScope.constructor;
					IF constructor # NIL THEN
						parameter := constructor.type(SyntaxTree.ProcedureType).firstParameter;
						FOR i := 1 TO x.parameters.Length()-1 DO

							p := x.parameters.GetExpression(i);
							Global.GetSymbolName(parameter,name);
							Evaluate(p, value);
							ASSERT(value.type # NIL);
							IF value.type.resolved IS SyntaxTree.IntegerType THEN
								par := instance.AddParameter(name);
								par.SetInteger(value.integer);
							ELSIF value.type.resolved IS SyntaxTree.BooleanType THEN
								par := instance.AddParameter(name);
								par.SetBoolean(value.boolean);
							ELSE Error(x.position,NotYetImplemented)
							END;
							parameter := parameter.nextParameter
						END;
					END;
				ELSE
					Error(x.position,NotYetImplemented)
				END;
			(* ----- CONNECT ------*)
			|Global.Connect:
				IF GetPort(p0,instance0,port0) THEN
					IF GetPort(p1,instance1,port1) THEN
						ASSERT(instance0 # NIL); ASSERT(instance1 # NIL); ASSERT(port0 # NIL); ASSERT(port1 # NIL);
						channel := currentActiveCellsScope.NewChannel();
						channel.ConnectIn(instance0,port0);
						channel.ConnectOut(instance1,port1);
						IF (p2 # NIL) THEN
							Evaluate(p2,value);
							channel.SetFifoSize(value.integer);
						END;
						channel.SetWidth(port1.width);
					ELSE
						Error(p1.position,"unallocated");
					END;
				ELSE
					Error(p0.position,"unallocated");
				END;
			|Global.Delegate:
				IF GetDelegatePort(p0,port0) & GetPort(p1,instance1,port1) THEN
					port0.Delegate(instance1,port1)
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
				ELSIF expression.type.resolved IS SyntaxTree.BooleanType THEN
					Boolean(value.boolean);
				ELSIF expression.type.resolved IS SyntaxTree.StringType THEN
					String(value.string);
				ELSE Error(expression.position,NotYetImplemented);
				END;
				stringWriter.String("; ");
			END;
			stringWriter.Get(s);
			expression := x.GetExpression(0);
			IF backend.log # NIL THEN
				backend.log.String(moduleScope.ownerModule.sourceName);
				backend.log.String("@"); backend.log.Int(expression.position,1);
				backend.log.String(" "); backend.log.String(s); backend.log.Ln;
			END;
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
			IF (x.left.type.resolved IS SyntaxTree.IntegerType) OR (x.left.type.resolved IS SyntaxTree.BooleanType) THEN
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
			Expression(x); ASSERT(resultValue # NIL); ASSERT(resultValue.type.resolved IS SyntaxTree.BooleanType);
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

	ActiveCellsBackend*= OBJECT (Backend.Backend)
	VAR

		PROCEDURE &InitActiveCellsBackend*;
		BEGIN
			InitBackend;
		END InitActiveCellsBackend;

		(* Work on a module *)
		PROCEDURE ProcessSyntaxTreeModule(x: SyntaxTree.Module): Formats.GeneratedModule;
		VAR
			declarationVisitor: DeclarationVisitor;
			implementationVisitor: ImplementationVisitor;
			name, instructionSet: SyntaxTree.String;
		BEGIN
			ResetError;
			Global.GetSymbolName(x,name);
			GetDescription(instructionSet);
			ASSERT(activeCellsSpecification # NIL); (* must be set by compiler driver *)
			NEW(implementationVisitor,system,checker,SELF);
			NEW(declarationVisitor,system,implementationVisitor,SELF);
			declarationVisitor.Module(x);

			RETURN NIL
		END ProcessSyntaxTreeModule;

		PROCEDURE GetDescription*(VAR instructionSet: ARRAY OF CHAR);
		BEGIN instructionSet := "ActiveCells";
		END GetDescription;

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

	END ActiveCellsBackend;

	PROCEDURE AppendIndex(VAR name: ARRAY OF CHAR; index: LONGINT);
	BEGIN
		Strings.Append(name,"["); Basic.AppendNumber(name,index); Strings.Append(name,"]");
	END AppendIndex;

	PROCEDURE Direction(direction: LONGINT): LONGINT;
	BEGIN
		IF direction = SyntaxTree.OutPort THEN RETURN ActiveCells.Out
		ELSIF direction = SyntaxTree.InPort THEN RETURN ActiveCells.In
		ELSE HALT(100);
		END;
	END Direction;

	PROCEDURE AddModules(instanceType: ActiveCells.Type; scope: SyntaxTree.CellScope);
	VAR import: SyntaxTree.Import;
		local: BOOLEAN;

		PROCEDURE AddImport(x: SyntaxTree.Module);
		VAR module: ActiveCells.Module; VAR name: SyntaxTree.String; device: ActiveCells.Device;
		BEGIN
			IF ~Global.IsSystemModule(x) THEN
				x.GetName(name);
				IF local THEN
					device := instanceType.specification.supportedDevices.ByName(name);
					IF device # NIL THEN
						device := instanceType.NewDevice(device.name,device.adr)
					END;
				END;

				 IF instanceType.modules.ByName(name) = NIL THEN
					module := instanceType.NewModule(name,"");
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
			x.GetName(name);
			AddImport(x);
		END TraverseImports;

	BEGIN
		local := TRUE;
		import := scope.firstImport;
		WHILE import # NIL DO
			TraverseImports(import.module);
			import := import.nextImport
		END;
		local := FALSE;
		TraverseImports(scope.ownerModule);
	END AddModules;

	PROCEDURE Get*(): Backend.Backend;
	VAR backend: ActiveCellsBackend;
	BEGIN NEW(backend); RETURN backend
	END Get;

	PROCEDURE Init;
	BEGIN
	END Init;

BEGIN
	Init;
END FoxActiveCellsBackend.


