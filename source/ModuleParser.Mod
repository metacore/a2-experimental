MODULE ModuleParser;	(** AUTHOR "mb"; PURPOSE "Active Oberon parser for use with ModuleTrees **)
(**
 * Notes:
 *	- The Module node's parent is the module node itself
 *)

IMPORT
	Strings, Files, Diagnostics, OCScanner, KernelLog, Texts, TextUtilities;

CONST
	(* visibilities *)
	Public* = 1;
	PublicRO* = 2;
	Private* = 3;

	(* block modifiers *)
	Exclusive* = 1;
	Active* = 2;
	Safe* = 3;
	Priority* = 4;
	HasExclusiveBlock* = 5;
	(* procedure modifiers (in addition to block modifiers) *)
	Overwrite* = 6; (* procedure overwrites procedure in superclass *)
	Overwritten* = 7; (* procedure is overwritten in subclass *)

	ExclusiveStr = "EXCLUSIVE";
	ActiveStr = "ACTIVE";
	RealtimeStr = "REALTIME";
	SafeStr = "SAFE";
	PriorityStr = "PRIORITY";

VAR
	name: ARRAY 1024 OF CHAR;

TYPE
	InfoItem* = OBJECT
	VAR
		name*: Strings.String;
		pos*: LONGINT;
	END InfoItem;

	Node* = OBJECT
	VAR
		parent- : Node;

		PROCEDURE GetModule*() : Module;
		VAR node : Node; module : Module;
		BEGIN
			module := NIL;
			node := SELF;
			WHILE (node # NIL) & (node.parent # node) DO node := node.parent; END;
			IF (node # NIL) THEN
				module := node (Module);
			END;
			RETURN module;
		END GetModule;

		PROCEDURE &Init*(parent : Node);
		BEGIN
			SELF.parent := parent;
		END Init;

	END Node;

	NodeList* = OBJECT(Node);
	VAR
		next*: NodeList;

	END NodeList;

	Import* = OBJECT (NodeList)
	VAR
		ident*, alias*, context*: InfoItem;
	END Import;

	Definition* = OBJECT (NodeList)
	VAR
		ident*: InfoItem;
		refines*: Qualident;
		procs*: ProcHead;
	END Definition;

	Type* = OBJECT(Node)
	VAR
		qualident*: Qualident;
		array*: Array;
		record*: Record;
		pointer*: Pointer;
		object*: Object;
		procedure*: Procedure;
	END Type;

	Array* = OBJECT(Node)
	VAR
		open*: BOOLEAN;
		len*: InfoItem;
		base*: Type;
	END Array;

	Record* = OBJECT(Node)
	VAR
		super*: Qualident;
		superPtr* : Record;
		fieldList*: FieldDecl;
	END Record;

	FieldDecl* = OBJECT (NodeList)
	VAR
		identList*: IdentList;
		type*: Type;
	END FieldDecl;

	Pointer* = OBJECT(Node)
	VAR
		type*: Type;
	END Pointer;

	Object* = OBJECT(Node)
	VAR
		super*, implements*: Qualident;
		superPtr* : Object;
		modifiers* : SET;
		declSeq*: DeclSeq;
		bodyPos- : LONGINT;

		PROCEDURE FindProcDecl*(CONST name : ARRAY OF CHAR) : ProcDecl;
		VAR procDecl : ProcDecl;
		BEGIN
			IF (declSeq # NIL) THEN
				procDecl := declSeq.FindProcDecl(name);
			ELSE
				procDecl := NIL;
			END;
			RETURN procDecl;
		END FindProcDecl;

	END Object;

	Procedure* = OBJECT(Node)
	VAR
		delegate*: BOOLEAN;
		formalPars*: FormalPars;
	END Procedure;

	DeclSeq* = OBJECT (NodeList)
	VAR
		constDecl*: ConstDecl;
		typeDecl*: TypeDecl;
		varDecl*: VarDecl;
		procDecl*: ProcDecl;

		PROCEDURE FindProcDecl*(CONST name : ARRAY OF CHAR) : ProcDecl;
		VAR pd : ProcDecl;
		BEGIN
			pd := procDecl;
			WHILE (pd # NIL) & (pd.head.identDef.ident.name^ # name) DO
				IF (pd.next # NIL) THEN
					pd := pd.next (ProcDecl);
				ELSE
					pd := NIL;
				END;
			END;
			ASSERT((pd = NIL) OR (pd.head.identDef.ident.name^ = name));
			RETURN pd;
		END FindProcDecl;

		PROCEDURE FindTypeDecl*(CONST name : ARRAY OF CHAR) : TypeDecl;
		VAR td : TypeDecl;
		BEGIN
			td := typeDecl;
			WHILE (td # NIL) & (td.identDef.ident.name^ # name) DO
				IF (td.next # NIL) THEN
					td := td.next (TypeDecl);
				ELSE
					td := NIL;
				END;
			END;
			ASSERT((td = NIL) OR (td.identDef.ident.name^ = name));
			RETURN td;
		END FindTypeDecl;

	END DeclSeq;

	ConstDecl* = OBJECT (NodeList)
	VAR
		identDef*: IdentDef;
		constExpr*: Expr;
		expr*: InfoItem;
	END ConstDecl;

	TypeDecl* = OBJECT (NodeList)
	VAR
		identDef*: IdentDef;
		type*: Type;
	END TypeDecl;

	VarDecl* = OBJECT (NodeList)
	VAR
		identList*: IdentList;
		type*: Type;
	END VarDecl;

	ProcDecl* = OBJECT (NodeList)
	VAR
		head*: ProcHead;
		declSeq*: DeclSeq;
		bodyPos- : LONGINT;
	END ProcDecl;

	ProcHead* = OBJECT (NodeList)
	VAR
		sysFlag*: InfoItem;
		constructor*, inline*, operator*: BOOLEAN;
		modifiers* : SET;
		identDef*: IdentDef;
		formalPars*: FormalPars;
	END ProcHead;

	FormalPars* = OBJECT(Node)
	VAR
		fpSectionList*: FPSection;
		returnType*: Qualident;
		returnTypeAry*: Array;
		returnTypeObj*: InfoItem;
	END FormalPars;

	FPSection* = OBJECT (NodeList)
	VAR
		var*, const*: BOOLEAN;
		identList*: IdentList;
		type*: Type;
	END FPSection;

	Expr* = OBJECT (NodeList)
	VAR
		simpleExprL*, simpleExprR*: SimpleExpr;
		relation*: InfoItem;
	END Expr;

	SimpleExpr* = OBJECT (NodeList)
	VAR
		sign*: InfoItem;
		termL*, termR*: Term;
		addOp*: AddOp;
	END SimpleExpr;

	Term* = OBJECT (NodeList)
	VAR
		factorL*, factorR*: Factor;
		mulOp*: MulOp;
	END Term;

	Factor* = OBJECT (NodeList)
	VAR
		designator*: Designator;
		number*, string*, nil*, bool*: InfoItem;
		set*: Element;
		expr*: Expr;
		factor*: Factor;
	END Factor;

	Designator* = OBJECT (NodeList)
	VAR
		qualident*: Qualident;
		ident*, arrowUp*: InfoItem;
		exprList*: Expr;
	END Designator;

	Qualident* = OBJECT (NodeList)
	VAR
		ident*: InfoItem;
	END Qualident;

	Element* = OBJECT (NodeList)
	VAR
		expr*, upToExpr*: Expr;
	END Element;

	MulOp* = OBJECT (NodeList)
	VAR
		op*: InfoItem;
	END MulOp;

	AddOp* = OBJECT (NodeList)
	VAR
		op*: InfoItem;
	END AddOp;

	IdentDef* = OBJECT
	VAR
		ident*: InfoItem;
		vis*: SHORTINT;
	END IdentDef;

	IdentList* = OBJECT (NodeList)
	VAR
		identDef*: IdentDef;
	END IdentList;

	Module* = OBJECT(Node)
	VAR
		ident*, context*: InfoItem;
		importList*: Import;
		modifiers* : SET;
		definitions*: Definition;
		declSeq*: DeclSeq;
		bodyPos- : LONGINT;
		hasError-: BOOLEAN;
		resolved* : BOOLEAN;

		PROCEDURE FindTypeDecl*(CONST name : ARRAY OF CHAR) : TypeDecl;
		VAR typeDecl : TypeDecl;
		BEGIN
			IF (declSeq # NIL) THEN
				typeDecl := declSeq.FindTypeDecl(name);
			ELSE
				typeDecl := NIL;
			END;
			RETURN typeDecl;
		END FindTypeDecl;

		PROCEDURE FindImport*(CONST name : ARRAY OF CHAR) : Import;
		VAR import : Import;
		BEGIN
			import := importList;
			WHILE (import # NIL) & ((import.ident = NIL) OR (import.ident.name^ # name)) DO
				IF (import.next # NIL) THEN
					import := import.next (Import);
				ELSE
					import := NIL;
				END;
			END;
			RETURN import;
		END FindImport;

	END Module;

	Parser = OBJECT
	VAR
		symbol : OCScanner.Symbol;
		scanner: OCScanner.Scanner;
		hasError: BOOLEAN;

		PROCEDURE & Init*(scanner: OCScanner.Scanner);
		BEGIN
			ASSERT(scanner # NIL);
			SELF.scanner := scanner;
			hasError := FALSE;
		END Init;

		PROCEDURE NextSymbol;
		VAR ignore : BOOLEAN;
		BEGIN
			ignore := scanner.GetNextSymbol(symbol);
			WHILE (symbol.token = OCScanner.Comment) DO ignore := scanner.GetNextSymbol(symbol); END;
		END NextSymbol;

		PROCEDURE ModuleP(VAR module: Module);
		VAR
			modName: OCScanner.StringType;
			definition: Definition;
		BEGIN
			NextSymbol;
			IF symbol.token = OCScanner.Module THEN
				NEW(module, NIL); module.parent := module;
				NextSymbol;
				IF symbol.token = OCScanner.Identifier THEN
					NEW(module.ident);
					COPY(symbol.string, modName);
					module.ident.name := Strings.NewString(symbol.string);
					module.ident.pos := symbol.start;
				END;
				NextSymbol;
				IF symbol.token = OCScanner.In THEN
					NextSymbol;
					IF symbol.token = OCScanner.Identifier THEN
						NEW(module.context);
						module.context.name := Strings.NewString(symbol.string);
						module.context.pos := symbol.start;
					END;
					Check (OCScanner.Identifier);
				END;
				IF symbol.token = OCScanner.LeftBrace THEN
					WHILE (symbol.token # OCScanner.Semicolon) & (symbol.token # OCScanner.EndOfText) DO NextSymbol END;
				END;
				Check(OCScanner.Semicolon);
				IF symbol.token = OCScanner.Import THEN
					NEW(module.importList, module);
					ImportListP(module.importList);
				END;
				WHILE symbol.token = OCScanner.Definition DO
					NEW(definition, module);
					DefinitionP(definition);
					IF module.definitions = NIL THEN module.definitions := definition
					ELSE AppendLast(module.definitions, definition)
					END;
				END;
				IF 	(symbol.token = OCScanner.Const) OR (symbol.token = OCScanner.Type) OR
					(symbol.token = OCScanner.Var) OR (symbol.token = OCScanner.Procedure) OR (symbol.token = OCScanner.Operator) THEN
					NEW(module.declSeq, module);
					DeclSeqP(module.declSeq);
				END;
				IF (symbol.token = OCScanner.Begin) THEN
					module.bodyPos := symbol.start;
				ELSE
					module.bodyPos := 0;
				END;
				BodyP(FALSE, module.modifiers);
				IF (symbol.token = OCScanner.Identifier) & (symbol.string = modName) THEN
					(* correct *)
				ELSE
					(* maybe missing END or wrong module name *)
					hasError := TRUE;
					KernelLog.String("err3: "); KernelLog.Int(symbol.start, 0); KernelLog.Ln;
				END;
				module.hasError := hasError;
			END;
		END ModuleP;

		PROCEDURE ImportListP(import: Import);
		VAR newImport: Import;
		BEGIN
			NextSymbol;
			WHILE symbol.token = OCScanner.Identifier DO
				NEW(import.ident);
				import.ident.name := Strings.NewString(symbol.string);
				import.ident.pos := symbol.start;
				NextSymbol;	(* avoids endless loop *)
				IF symbol.token = OCScanner.Becomes THEN
					NextSymbol;
					IF symbol.token = OCScanner.Identifier THEN
						NEW(import.alias);
						import.alias.name := Strings.NewString(symbol.string);
						import.alias.pos := symbol.start;
						NextSymbol;
					ELSE
						(* Error *)
						hasError := TRUE;
						KernelLog.String("err2: "); KernelLog.Int(symbol.start, 0); KernelLog.Ln;
					END;
				END;
				IF symbol.token = OCScanner.In THEN
					NextSymbol;
					IF symbol.token = OCScanner.Identifier THEN
						NEW(import.context);
						import.context.name := Strings.NewString(symbol.string);
						import.context.pos := symbol.start;
					END;
					Check (OCScanner.Identifier);
				END;
				IF symbol.token = OCScanner.Comma THEN
					NextSymbol;
				END;
				NEW(newImport, import.parent);
				import.next := newImport;
				import := newImport;
			END;
			Check(OCScanner.Semicolon);
		END ImportListP;

		PROCEDURE DefinitionP(definition: Definition);
		VAR
			procHead: ProcHead;
		BEGIN
			IF symbol.token = OCScanner.Definition THEN
				NextSymbol;
				IF symbol.token = OCScanner.Identifier THEN
					NEW(definition.ident);
					definition.ident.name := Strings.NewString(symbol.string);
					definition.ident.pos := symbol.start;
					NextSymbol;
				END;
				WHILE symbol.token = OCScanner.Semicolon DO NextSymbol END;
		(*?		IF symbol.token = OCScanner.Refines THEN
					NextSymbol;
					NEW(definition.refines, definition);
					QualidentP(definition.refines);
				END; *)
				WHILE (symbol.token = OCScanner.Procedure) OR (symbol.token = OCScanner.Operator) DO
					NEW(procHead, definition);
					NextSymbol;
					ProcHeadP(procHead);
					IF definition.procs = NIL THEN definition.procs := procHead
					ELSE AppendLast(definition.procs, procHead)
					END;
					Check(OCScanner.Semicolon);
				END;
				Check(OCScanner.End);
				Check(OCScanner.Identifier);
				WHILE symbol.token = OCScanner.Semicolon DO NextSymbol END;
			END;
		END DefinitionP;

		PROCEDURE DeclSeqP(declSeq: DeclSeq);
		VAR
			constDecl: ConstDecl;
			typeDecl: TypeDecl;
			varDecl: VarDecl;
			procDecl: ProcDecl;

			PROCEDURE CheckEndOrSemicolon;
			BEGIN
				IF symbol.token # OCScanner.End THEN
					REPEAT Check(OCScanner.Semicolon) UNTIL symbol.token # OCScanner.Semicolon
				END;
			END CheckEndOrSemicolon;

		BEGIN
			LOOP
				CASE symbol.token OF
				| OCScanner.Const:
					NextSymbol;
					WHILE symbol.token = OCScanner.Identifier DO
						NEW(constDecl, declSeq);
						ConstDeclP(constDecl);
						IF declSeq.constDecl = NIL THEN declSeq.constDecl := constDecl;
						ELSE AppendLast(declSeq.constDecl, constDecl);
						END;
						CheckEndOrSemicolon;
						(*Check(OCScanner.Semicolon);*)
					END;
				| OCScanner.Type:
					NextSymbol;
					WHILE symbol.token = OCScanner.Identifier DO
						NEW(typeDecl, declSeq);
						TypeDeclP(typeDecl);
						IF declSeq.typeDecl = NIL THEN declSeq.typeDecl := typeDecl;
						ELSE AppendLast(declSeq.typeDecl, typeDecl);
						END;
						CheckEndOrSemicolon;
						(*Check(OCScanner.Semicolon);*)
					END;
				| OCScanner.Var:
					NextSymbol;
					WHILE symbol.token = OCScanner.Identifier DO
						NEW(varDecl, declSeq);
						VarDeclP(varDecl);
						IF declSeq.varDecl = NIL THEN declSeq.varDecl := varDecl;
						ELSE AppendLast(declSeq.varDecl, varDecl);
						END;
						CheckEndOrSemicolon;
						(*Check(OCScanner.Semicolon);*)
					END;
				| OCScanner.Procedure, OCScanner.Operator:
					WHILE (symbol.token = OCScanner.Procedure) OR (symbol.token = OCScanner.Operator) DO
						NextSymbol;
						NEW(procDecl, declSeq);
						ProcDeclP(procDecl);
						IF procDecl.head = NIL THEN
							procDecl := NIL
						ELSE
							IF declSeq.procDecl = NIL THEN declSeq.procDecl := procDecl;
							ELSE AppendLast(declSeq.procDecl, procDecl);
							END;
						END;
						CheckEndOrSemicolon;
						(*Check(OCScanner.Semicolon);*)
					END;
				ELSE
					EXIT;
				END;
			END;
		END DeclSeqP;

		PROCEDURE ConstDeclP(const: ConstDecl);
		BEGIN
			NEW(const.identDef);
			IdentDefP(const.identDef);
			Check(OCScanner.Equal);
			(* NEW(const.constExpr);
			ExprP(const.constExpr); *)
			NEW(const.expr);
			ConstExprP(OCScanner.Semicolon, -1, const.expr);
		END ConstDeclP;

		PROCEDURE TypeDeclP(type: TypeDecl);
		BEGIN
			NEW(type.identDef);
			IdentDefP(type.identDef);
			Check(OCScanner.Equal);
			NEW(type.type, type);
			TypeP(type.type);
		END TypeDeclP;

		PROCEDURE VarDeclP(var: VarDecl);
		VAR
			identDef: IdentDef;
			identList: IdentList;
		BEGIN
			(*SysFlag;*)
			NEW(var.identList, var);
			NEW(var.identList.identDef);
			IdentDefP(var.identList.identDef);
			SysFlag;
			WHILE symbol.token = OCScanner.Comma DO
				NextSymbol;	(* avoids endless loop *)
				NEW(identDef);
				IdentDefP(identDef);
				SysFlag;
				NEW(identList, var);
				identList.identDef := identDef;
				AppendLast(var.identList, identList);
			END;
			Check(OCScanner.Colon);
			NEW(var.type, var);
			TypeP(var.type);
		END VarDeclP;

		PROCEDURE ProcDeclP(proc: ProcDecl);
		VAR
			declSeq: DeclSeq;
		BEGIN
			NEW(proc.head, proc);
			ProcHeadP(proc.head);
			IF proc.head.identDef = NIL THEN proc.head := NIL; RETURN END;
			Check(OCScanner.Semicolon);
			IF 	(symbol.token = OCScanner.Const) OR (symbol.token = OCScanner.Var) OR
				(symbol.token = OCScanner.Type) OR (symbol.token = OCScanner.Procedure) OR (symbol.token = OCScanner.Operator) THEN
				NEW(declSeq, proc);
				DeclSeqP(declSeq);
				IF proc.declSeq = NIL THEN proc.declSeq := declSeq;
				ELSE AppendLast(proc.declSeq, declSeq);
				END;
			END;
			IF (symbol.token = OCScanner.Begin) THEN
				proc.bodyPos := symbol.start;
			ELSE
				proc.bodyPos := 0;
			END;
			BodyP(FALSE, proc.head.modifiers);
			NextSymbol;	(* skip ident *)
		END ProcDeclP;

		PROCEDURE ProcHeadP(head: ProcHead);
		VAR forward: BOOLEAN;
		BEGIN
			SysFlag;
			CASE symbol.token OF
			| OCScanner.Minus: head.inline := TRUE; NextSymbol;
			| OCScanner.And: head.constructor := TRUE; NextSymbol;
			| OCScanner.Times: (* ignore *) NextSymbol;
			| OCScanner.Arrow: (* ignore *) NextSymbol; forward := TRUE;
			| OCScanner.String: head.operator := TRUE;
			| OCScanner.Number: IF symbol.numberType = OCScanner.Character THEN head.operator := TRUE END;
			ELSE
			END;
			NEW(head.identDef);
			IdentDefP(head.identDef);
			OSAIrq;		(* tk: Compatibility to OSACompiler*)
			IF symbol.token = OCScanner.LeftParenthesis THEN
				NEW(head.formalPars, head);
				FormalParsP(head.formalPars);
			END;
			IF forward THEN
				head.identDef := NIL;
				head.formalPars := NIL;
			END;
		END ProcHeadP;

		PROCEDURE SysFlag;
		BEGIN
			IF symbol.token = OCScanner.LeftBrace THEN
				NextSymbol;
				Check(OCScanner.Identifier);
				IF symbol.token = OCScanner.Comma THEN
					NextSymbol;
					Check(OCScanner.Identifier)
				END;
				Check(OCScanner.RightBrace);
			END;
		END SysFlag;

		(* tk: For OSA Compatibility *)
		PROCEDURE OSAIrq;
		BEGIN
			IF symbol.token = OCScanner.LeftBracket THEN
				NextSymbol;
				Check(OCScanner.Number);
				Check(OCScanner.RightBracket);
			END;
		END OSAIrq;

		PROCEDURE FormalParsP(pars: FormalPars);
		VAR
			fpSection: FPSection;
		BEGIN
			NextSymbol;
			IF (symbol.token = OCScanner.Var) OR (symbol.token = OCScanner.Const) OR (symbol.token = OCScanner.Identifier) THEN
				NEW(pars.fpSectionList, pars);
				FPSectionP(pars.fpSectionList);
				WHILE symbol.token = OCScanner.Semicolon DO
					NextSymbol;	(* avoids endless loop *)
					NEW(fpSection, pars.fpSectionList);
					FPSectionP(fpSection);
					AppendLast(pars.fpSectionList, fpSection);
				END;
			END;
			Check(OCScanner.RightParenthesis);
			IF symbol.token = OCScanner.Colon THEN
				NextSymbol;
				IF symbol.token = OCScanner.Object THEN
					NEW(pars.returnTypeObj);
					pars.returnTypeObj.name := Strings.NewString("OBJECT");
					pars.returnTypeObj.pos := symbol.start;
					NextSymbol;
				ELSIF symbol.token = OCScanner.Array THEN
					NEW(pars.returnTypeAry, pars);
					NextSymbol;
					ArrayP(pars.returnTypeAry);

					(*
					NEW(pars.returnType.ident);
					pars.returnType.ident.name := Strings.NewString("ARRAY OF ???");
					pars.returnType.ident.pos := bol.start;
					SkipTo(OCScanner.Semicolon);
					*)
				ELSE
					NEW(pars.returnType, pars);
					QualidentP(pars.returnType)
				END;
			END;
		END FormalParsP;

		PROCEDURE FPSectionP(fpSection: FPSection);
		VAR identList: IdentList;
		BEGIN
			IF symbol.token = OCScanner.Var THEN
				fpSection.var := TRUE;
				NextSymbol;
			ELSIF symbol.token = OCScanner.Const THEN
				fpSection.const := TRUE;
				NextSymbol;
			END;
			IF symbol.token = OCScanner.Identifier THEN
				(*StringPool.GetString(scanner.name, name);*)
				NEW(fpSection.identList, fpSection);
				NEW(fpSection.identList.identDef);
				IdentDefP(fpSection.identList.identDef);
				(*
				fpSection.identList.ident.name := Strings.NewString(name);
				fpSection.identList.ident.pos := symbol.start;
				NextSymbol;
				*)
				WHILE symbol.token = OCScanner.Comma DO
					NEW(identList, fpSection.identList);
					NextSymbol;
					NEW(identList.identDef);
					IdentDefP(identList.identDef);
					AppendLast(fpSection.identList, identList);
					(*
					IF symbol.token = OCScanner.Identifier THEN
						StringPool.GetString(scanner.name, name);
						NEW(identDef);
						NEW(identDef.ident);
						identDef.ident.name := Strings.NewString(name);
						identDef.ident.pos := symbol.start;
						AppendLast(fpSection.identlist, identDef);
						NextSymbol;
					END;
					*)
				END;
				Check(OCScanner.Colon);
				NEW(fpSection.type, fpSection);
				TypeP(fpSection.type);
			END;
		END FPSectionP;

		PROCEDURE TypeP(type: Type);
		BEGIN
			CASE symbol.token OF
			| OCScanner.Array: NextSymbol; NEW(type.array, type); ArrayP(type.array);
			| OCScanner.Record: NextSymbol; NEW(type.record, type); RecordP(type.record);
			| OCScanner.Pointer: NextSymbol; NEW(type.pointer, type); PointerP(type.pointer);
			| OCScanner.Object: NextSymbol; NEW(type.object, type); ObjectP(type.object);
			| OCScanner.Procedure, OCScanner.Operator: NextSymbol; NEW(type.procedure, type); ProcedureP(type.procedure);
			| OCScanner.Identifier: NEW(type.qualident, type); QualidentP(type.qualident);
			ELSE
				(* Error *)
				hasError := TRUE; KernelLog.String("err4: "); KernelLog.Int(symbol.start, 0); KernelLog.Ln;
				NextSymbol;	(* ??? *)
			END;
		END TypeP;

		PROCEDURE ArrayP(array: Array);
		BEGIN
			SysFlag;
			IF symbol.token = OCScanner.Of THEN
				array.open := TRUE;
				NEW(array.base, array);
				NextSymbol;
				TypeP(array.base);
			ELSE
				NEW(array.len);
				ConstExprP(OCScanner.Of, OCScanner.Comma, array.len);
				(*
				SimpleExprP(array.len);
				*)
				IF symbol.token = OCScanner.Of THEN
					NEW(array.base, array);
					NextSymbol;
					TypeP(array.base);
				ELSIF symbol.token = OCScanner.Comma THEN
					NEW(array.base, array);
					NEW(array.base.array, array);
					NextSymbol;
					ArrayP(array.base.array)
				ELSE
					(* Error *)
					hasError := TRUE;
					KernelLog.String("err1: "); KernelLog.Int(symbol.start, 0); KernelLog.Ln;
				END;
			END;
		END ArrayP;

		PROCEDURE RecordP(record: Record);
		BEGIN
			SysFlag;
			IF symbol.token = OCScanner.LeftParenthesis THEN
				NextSymbol;
				NEW(record.super, record);
				QualidentP(record.super);
				Check(OCScanner.RightParenthesis);
			END;
			WHILE symbol.token = OCScanner.Semicolon DO NextSymbol END;
			IF symbol.token = OCScanner.Identifier THEN
				NEW(record.fieldList, record);
				FieldListP(record.fieldList);
			END;
			Check(OCScanner.End);
		END RecordP;

		PROCEDURE FieldListP(fieldList: FieldDecl);
		VAR fieldDecl: FieldDecl;
		BEGIN
			FieldDeclP(fieldList);
			WHILE symbol.token = OCScanner.Semicolon DO
				NextSymbol;
				NEW(fieldDecl, fieldList);
				FieldDeclP(fieldDecl);
				AppendLast(fieldList, fieldDecl);
			END;
		END FieldListP;

		PROCEDURE FieldDeclP(fieldDecl: FieldDecl);
		VAR
			identDef: IdentDef;
			identList: IdentList;
		BEGIN
			IF symbol.token = OCScanner.Identifier THEN
				NEW(fieldDecl.identList, fieldDecl);
				NEW(fieldDecl.identList.identDef);
				IdentDefP(fieldDecl.identList.identDef);
				SysFlag;
				WHILE symbol.token = OCScanner.Comma DO
					NextSymbol;
					NEW(identDef);
					IdentDefP(identDef);
					SysFlag;
					NEW(identList, identList);
					identList.identDef := identDef;
					AppendLast(fieldDecl.identList, identList);
				END;
				Check(OCScanner.Colon);
				NEW(fieldDecl.type, fieldDecl);
				TypeP(fieldDecl.type);
			END;
		END FieldDeclP;

		PROCEDURE PointerP(pointer: Pointer);
		BEGIN
			SysFlag;
			Check(OCScanner.To);
			NEW(pointer.type, pointer);
			TypeP(pointer.type);
		END PointerP;

		PROCEDURE ObjectP(object: Object);
		VAR declSeq: DeclSeq;
			pos: LONGINT;
		(*?	qualident: Qualident; *)
		BEGIN
			IF (symbol.token = OCScanner.Semicolon) OR (symbol.token = OCScanner.RightParenthesis) THEN RETURN END;
			SysFlag;
			IF symbol.token = OCScanner.LeftParenthesis THEN
				NEW(object.super, object);
				NextSymbol;
				QualidentP(object.super);
				Check(OCScanner.RightParenthesis);
			END;
		(*?	IF symbol.token = OCScanner.Implements THEN
				NEW(object.implements, object);
				NextSymbol;
				QualidentP(object.implements);
				WHILE symbol.token = OCScanner.Comma DO
					NEW(qualident, object.implements);
					NextSymbol;
					QualidentP(qualident);
					AppendLast(object.implements, qualident);
				END;
			END; *)
			pos := -1;
			WHILE (symbol.token # OCScanner.Begin) & (symbol.token # OCScanner.End) & (symbol.token # OCScanner.EndOfText) DO
					(* avoid endless-loop *)
				IF pos = symbol.start THEN NextSymbol END;
				pos := symbol.start;
				NEW(declSeq, object);
				DeclSeqP(declSeq);
				IF object.declSeq = NIL THEN object.declSeq := declSeq;
				ELSE AppendLast(object.declSeq, declSeq);
				END;
			END;
			IF (symbol.token = OCScanner.Begin) THEN
				object.bodyPos := symbol.start;
			ELSE
				object.bodyPos := 0;
			END;
			BodyP(TRUE, object.modifiers);
			IF symbol.token = OCScanner.Identifier THEN NextSymbol END;
		END ObjectP;

		PROCEDURE ProcedureP(proc: Procedure);
		BEGIN
			SysFlag;
			IF symbol.token = OCScanner.LeftBrace THEN
				NextSymbol;
				IF symbol.token # OCScanner.Identifier THEN
					(* Error *)
				ELSIF symbol.string = "DELEGATE" THEN
					proc.delegate := TRUE;
				END;
				NextSymbol;
				Check(OCScanner.RightBrace);
			END;
			IF symbol.token = OCScanner.LeftParenthesis THEN
				NEW(proc.formalPars, proc);
				FormalParsP(proc.formalPars);
			END;
		END ProcedureP;

		PROCEDURE ConstExprP(delimiter1, delimiter2: OCScanner.Token; expr: InfoItem);
		VAR
			exprStr, name: ARRAY 1024 OF CHAR;
			longExprStr : Strings.String; (* for exprStr content lengths > LEN(exprStr) *)
			paren, brace, brak: LONGINT;

			PROCEDURE Add(CONST str: ARRAY OF CHAR);
			VAR len1, len2 : LONGINT;
			BEGIN
				len1 := Strings.Length(exprStr);
				len2 := Strings.Length(str);
				IF (len1 + len2 + 1 > LEN(exprStr)) THEN
					IF (longExprStr = NIL) THEN
						longExprStr := Strings.ConcatToNew(exprStr, str);
					ELSE
						(* assume that this happens almost never *)
						longExprStr := Strings.ConcatToNew(longExprStr^, exprStr);
						longExprStr := Strings.ConcatToNew(longExprStr^, str);
					END;
					exprStr := "";
				ELSE
					Strings.Append(exprStr, str);
				END;
			END Add;

		BEGIN
			expr.pos := symbol.start;
			IF (symbol.token = delimiter1) OR (symbol.token = delimiter2) THEN RETURN END;
			REPEAT
				CASE symbol.token OF
				| OCScanner.LeftParenthesis: INC(paren); Add("(");
				| OCScanner.RightParenthesis: DEC(paren); Add(")");
				| OCScanner.LeftBrace: INC(brace); Add("{");
				| OCScanner.RightBrace: DEC(brace); Add("}");
				| OCScanner.LeftBracket: INC(brak); Add("[");
				| OCScanner.RightBracket: DEC(brak); Add("]");
				| OCScanner.Number: Add(symbol.string);
				| OCScanner.Nil: Add("NIL");
				| OCScanner.True: Add("TRUE");
				| OCScanner.False: Add("FALSE");
				| OCScanner.Not: Add("~");
				| OCScanner.Period: Add(".");
				| OCScanner.Identifier: Add(symbol.string);
				| OCScanner.Comma: Add(", ");
				| OCScanner.Plus: Add(" + ");
				| OCScanner.Minus: Add(" - ");
				| OCScanner.Times: Add(" * ");
				| OCScanner.Upto: Add(" .. ");
				| OCScanner.Equal: Add(" = ");
				| OCScanner.Unequal: Add(" # ");
				| OCScanner.Less: Add(" < ");
				| OCScanner.LessEqual: Add(" <= ");
				| OCScanner.Greater: Add(" > ");
				| OCScanner.GreaterEqual: Add(" >= ");
				| OCScanner.In: Add(" IN ");
				| OCScanner.Is: Add(" IS ");
				| OCScanner.Div: Add(" DIV ");
				| OCScanner.Mod: Add(" MOD ");
				| OCScanner.Slash: Add(" / ");
				| OCScanner.And: Add(" & ");
				| OCScanner.Or: Add(" OR ");
				| OCScanner.String: name[0] := '"'; name[1] := 0X; Add(name); Add(symbol.string); Add(name);
				| OCScanner.Arrow: Add("^");
				ELSE
					(* error *)
					hasError := TRUE;
				END;
				NextSymbol;
				(* urgh, what an ugly condition ... *)
			UNTIL (((symbol.token = delimiter1) OR (symbol.token = delimiter2)) & (paren = 0) & (brace = 0) & (brak = 0)) OR (symbol.token = OCScanner.EndOfText);
			IF (longExprStr = NIL) THEN
				expr.name := Strings.NewString(exprStr);
			ELSE
				expr.name := Strings.ConcatToNew(longExprStr^, exprStr);
			END;
		END ConstExprP;

		PROCEDURE BlockModifierP(allowBody : BOOLEAN; VAR modifiers : SET);
		VAR ignore : InfoItem;
		BEGIN
			modifiers := {};
			IF symbol.token = OCScanner.LeftBrace THEN
				NextSymbol;
				LOOP
					IF symbol.token = OCScanner.Identifier THEN
						IF symbol.string = ExclusiveStr  THEN
							modifiers := modifiers + {Exclusive};
							NextSymbol;
						ELSIF allowBody & (name = ActiveStr)  THEN
							modifiers := modifiers + {Active};
							NextSymbol
						ELSIF allowBody & (name = RealtimeStr) THEN
							NextSymbol;
						ELSIF allowBody & (name = SafeStr)  THEN
							modifiers := modifiers + {Safe};
							NextSymbol
						ELSIF allowBody & (name = PriorityStr)  THEN
							modifiers := modifiers + {Priority};
							NextSymbol;
							IF symbol.token = OCScanner.LeftParenthesis THEN
								NextSymbol;
								NEW(ignore);
								ConstExprP(OCScanner.RightParenthesis, -1, ignore);
								Check(OCScanner.RightParenthesis);
							END;
						ELSE
							Error(symbol.start); NextSymbol (* skip the ident, probably a typo *)
						END;
					END;
					IF symbol.token # OCScanner.Comma THEN EXIT END;
					NextSymbol
				END;
				Check(OCScanner.RightBrace);
			END;
		END BlockModifierP;

		PROCEDURE BodyP(allowBody : BOOLEAN; VAR modifiers : SET);
		VAR end, lastToken: LONGINT; m : SET; first : BOOLEAN;
		BEGIN
			IF symbol.token = OCScanner.Begin THEN
				end := 1;
				first := TRUE;
				REPEAT
					lastToken := symbol.token;
					NextSymbol;
					IF (lastToken = OCScanner.Begin) & (symbol.token = OCScanner.LeftBrace) THEN
						BlockModifierP(allowBody, m);
						IF first THEN
							allowBody := FALSE;
							modifiers := m;
						ELSE
							IF m * {Exclusive} # {} THEN
								modifiers := modifiers + {HasExclusiveBlock};
							END;
						END;
					END;
					first := FALSE;
					CASE symbol.token OF
					| OCScanner.Begin: INC(end);
					| OCScanner.If, OCScanner.Case, OCScanner.While, OCScanner.For, OCScanner.Loop, OCScanner.With: INC(end);
					| OCScanner.End: DEC(end);
					ELSE
					END;
				UNTIL (end = 0) OR (symbol.token = OCScanner.EndOfText);
			ELSIF symbol.token = OCScanner.Code THEN
				REPEAT NextSymbol UNTIL (symbol.token = OCScanner.End) OR (symbol.token = OCScanner.EndOfText);
			END;
			NextSymbol;
		END BodyP;

		PROCEDURE QualidentP(qualident: Qualident);
		VAR
			name : ARRAY 64 OF CHAR;
			pos: LONGINT;
		BEGIN
			IF symbol.token = OCScanner.Identifier THEN
				COPY(symbol.string, name);
				pos := symbol.start;
				NextSymbol;
				IF symbol.token = OCScanner.Period THEN
					NextSymbol;
					IF symbol.token = OCScanner.Identifier THEN
						Strings.Append(name, ".");
						Strings.Concat(name, symbol.string, name);
						NextSymbol;
					END;
				END;
				NEW(qualident.ident);
				qualident.ident.name := Strings.NewString(name);
				qualident.ident.pos := pos;
			END;
		END QualidentP;

		PROCEDURE IdentDefP(identDef: IdentDef);
		BEGIN
			IF symbol.token = OCScanner.Identifier THEN
				NEW(identDef.ident);
				identDef.ident.name := Strings.NewString(symbol.string);
				identDef.ident.pos := symbol.start;
			ELSIF (symbol.token = OCScanner.String) OR (symbol.token = OCScanner.Number) & (symbol.numberType = OCScanner.Character) THEN
				NEW(identDef.ident);
				identDef.ident.name := Strings.NewString(symbol.string);
				identDef.ident.pos := symbol.start;
			END;
			NextSymbol;
			IF symbol.token = OCScanner.Times THEN
				identDef.vis := Public;
				NextSymbol;
			ELSIF symbol.token = OCScanner.Minus THEN
				identDef.vis := PublicRO;
				NextSymbol;
			ELSE
				identDef.vis := Private;
			END;
		END IdentDefP;

		PROCEDURE Check(token: OCScanner.Token);
		BEGIN
			IF symbol.token = token THEN
				(* correct *)
			ELSE
				(* error *)

				KernelLog.String("******* Check error **********  ");
				KernelLog.Int(symbol.start, 0);
				KernelLog.Ln;

				hasError := TRUE;
				(*HALT(33);*)
			END;
			NextSymbol;
		END Check;

		PROCEDURE Error(pos : LONGINT);
		BEGIN
			KernelLog.String("ModuleParser: Error at pos "); KernelLog.Int(pos, 0); KernelLog.Ln;
		END Error;

	END Parser;

	ListEntry = POINTER TO RECORD
		module : Module;
		next : ListEntry;
	END;

	ModuleCache = OBJECT
	VAR
		head : ListEntry; (* private *)
		nofModules : LONGINT;

		PROCEDURE Add(module : Module);
		VAR entry : ListEntry;
		BEGIN {EXCLUSIVE}
			ASSERT((module # NIL) & (module.ident.name # NIL));
			entry := FindEntry(module.ident.name^);
			IF (entry = NIL) THEN
				NEW(entry);
				entry.next := head.next;
				head.next := entry;
				module.resolved := FALSE;
				INC(nofModules);
			END;
			entry.module := module;
		END Add;

		PROCEDURE Get(CONST moduleName : ARRAY OF CHAR) : Module;
		VAR module : Module; entry : ListEntry;
		BEGIN {EXCLUSIVE}
			entry := FindEntry(moduleName);
			IF (entry # NIL) THEN
				module := entry.module;
			ELSE
				module := NIL;
			END;
			RETURN module;
		END Get;

		PROCEDURE Enumerate(enumerator : EnumeratorProc);
		VAR entry : ListEntry;
		BEGIN
			ASSERT(enumerator # NIL);
			entry := head.next;
			WHILE (entry # NIL) DO
				enumerator(entry.module, SELF);
				entry := entry.next;
			END;
		END Enumerate;

		PROCEDURE FindEntry(CONST moduleName : ARRAY OF CHAR) : ListEntry; (* private *)
		VAR entry : ListEntry;
		BEGIN
			entry := head.next;
			WHILE (entry # NIL) & (entry.module.ident.name^ # moduleName) DO entry := entry.next; END;
			RETURN entry;
		END FindEntry;

		PROCEDURE &Init; (* private *)
		BEGIN
			NEW(head); head.module := NIL; head.next := NIL;
			nofModules := 0;
		END Init;

	END ModuleCache;

	EnumeratorProc = PROCEDURE {DELEGATE} (module : Module; cache : ModuleCache);

PROCEDURE AppendLast(head, node: NodeList);
VAR n: NodeList;
BEGIN
	IF head = NIL THEN RETURN END;
	n := head;
	WHILE n.next # NIL DO
		n := n.next;
	END;
	n.next := node;
END AppendLast;

PROCEDURE SplitName*(CONST name : ARRAY OF CHAR; VAR moduleName, typeName : ARRAY OF CHAR);
VAR i, j : LONGINT;
BEGIN
	IF Strings.ContainsChar(name, ".", FALSE) THEN
		i := 0;
		WHILE (i < LEN(name)) & (name[i] # ".") DO moduleName[i] := name[i]; INC(i); END;
		moduleName[i] := 0X;
		INC(i); (* skip "." *)
		j := 0;
		WHILE (i < LEN(name)) & (name[i] # 0X) DO typeName[j] := name[i]; INC(i); INC(j); END;
		typeName[j] := 0X;
	ELSE
		COPY("", moduleName);
		COPY(name, typeName);
	END;
END SplitName;

PROCEDURE FindType(CONST name : ARRAY OF CHAR; type : LONGINT; definitionModule : Module; cache : ModuleCache) : TypeDecl;
VAR
	module : Module; import : Import; typeDecl : TypeDecl;
	moduleName, importName, typeName : ARRAY 256 OF CHAR;
	context : ARRAY 32 OF CHAR;
	filename : Files.FileName;

	PROCEDURE FileExists(CONST filename : ARRAY OF CHAR) : BOOLEAN;
	VAR file : Files.File;
	BEGIN
		file := Files.Old(filename);
		RETURN (file # NIL);
	END FileExists;

	PROCEDURE GenerateFilename(CONST prefix, context, moduleName, fileExtension: ARRAY OF CHAR) : Files.FileName;
	VAR filename : Files.FileName;
	BEGIN
		COPY(prefix, filename);
		IF (context # "") THEN Strings.Append(filename, context); Strings.Append(filename, "."); END;
		Strings.Append(filename, moduleName); Strings.Append(filename, fileExtension);
		RETURN filename;
	END GenerateFilename;

	(* Simple heuristics that tries to find the filename of a given module name *)
	PROCEDURE FindCorrectFilename(CONST context, moduleName : ARRAY OF CHAR) : Files.FileName;
	VAR filename : Files.FileName;
	BEGIN
		filename := GenerateFilename("", context, moduleName, ".Mod");
		IF ~FileExists(filename) THEN
			filename := GenerateFilename("I386.", context, moduleName, ".Mod");
			IF ~FileExists(filename) THEN
				filename := GenerateFilename("Win32.", context, moduleName, ".Mod");
				IF ~FileExists(filename) THEN
					filename := GenerateFilename("Unix.", context, moduleName, ".Mod");
					IF ~FileExists(filename) THEN
						filename := GenerateFilename("Oberon.", context, moduleName, ".Mod");
						IF ~FileExists(filename) THEN
							filename := GenerateFilename("", context, moduleName, ".Mod");
						END;
					END;
				END;
			END;
		END;
		RETURN filename;
	END FindCorrectFilename;

BEGIN
	ASSERT((definitionModule # NIL) & (cache # NIL));
	SplitName(name, moduleName, typeName);
	import := definitionModule.FindImport(moduleName);
	importName := "";
	IF (import # NIL) THEN
		IF (import.context # NIL) THEN
			COPY(import.context.name^, context);
		ELSIF (definitionModule.context # NIL) THEN
			COPY(definitionModule.context.name^, context);
		ELSE
			COPY("", context);
		END;
		IF (import.alias # NIL) THEN
			Strings.Append(importName, import.alias.name^);
		ELSE
			Strings.Append(importName, import.ident.name^);
		END;
	END;
	IF (importName # "") THEN
		module := cache.Get(importName);
		IF (module = NIL) THEN
			filename := FindCorrectFilename(context, importName);
			module := ParseFile(filename, NIL);
			IF (module # NIL) THEN cache.Add(module); END;
		END;
	ELSE
		module := definitionModule;
	END;
	typeDecl := NIL;
	IF (module # NIL) THEN
		typeDecl := module.FindTypeDecl(typeName);
		IF (typeDecl # NIL) & (type # 3) &  (((typeDecl.type.record = NIL) & (type = 0)) OR ((typeDecl.type.object = NIL) & (type = 1)) OR
			(((typeDecl.type.pointer = NIL) OR (typeDecl.type.pointer.type.record = NIL)) & (type = 2))) THEN
			typeDecl := NIL; (* wrong type *)
		END;
	ELSE
		KernelLog.String("Module "); KernelLog.String(moduleName); KernelLog.String(" not found.");
		KernelLog.Ln;
	END;
	RETURN typeDecl;
END FindType;

PROCEDURE ResolveTypeHierarchy(module : Module; cache : ModuleCache);
VAR typeDecl, td : TypeDecl;
BEGIN
	ASSERT(module # NIL);
	IF ~module.resolved & (module.declSeq # NIL) & (module.declSeq.typeDecl # NIL) THEN
		typeDecl := module.declSeq.typeDecl;
		WHILE (typeDecl # NIL) DO
			IF (typeDecl.type.record # NIL) & (typeDecl.type.record.super # NIL) THEN
				td := FindType(typeDecl.type.record.super.ident.name^, 0, module, cache);
				IF (td # NIL) THEN
					typeDecl.type.record.superPtr := td.type.record;
				END;
			ELSIF (typeDecl.type.pointer # NIL) & (typeDecl.type.pointer.type.record # NIL) & (typeDecl.type.pointer.type.record.super # NIL) THEN
				td := FindType(typeDecl.type.pointer.type.record.super.ident.name^, 2, module, cache);
				IF (td # NIL) THEN
					typeDecl.type.pointer.type.record.superPtr := td.type.pointer.type.record;
				END;
			ELSIF (typeDecl.type.object # NIL) & (typeDecl.type.object.super # NIL) THEN
				td := FindType(typeDecl.type.object.super.ident.name^, 1, module, cache);
				IF (td # NIL) THEN
					typeDecl.type.object.superPtr := td.type.object;
				END;
			END;
			IF (typeDecl.next # NIL) THEN
				typeDecl := typeDecl.next (TypeDecl);
			ELSE
				typeDecl := NIL;
			END;
		END;
		module.resolved := TRUE;
	END;
END ResolveTypeHierarchy;

PROCEDURE ResolveMethodOverwrites(module : Module; cache : ModuleCache);
VAR typeDecl : TypeDecl; method, procDecl : ProcDecl; superClass : Object;
BEGIN
	IF module.resolved & (module.declSeq # NIL) & (module.declSeq.typeDecl # NIL) THEN
		typeDecl := module.declSeq.typeDecl;
		WHILE (typeDecl # NIL) DO
			IF (typeDecl.type.object # NIL) & (typeDecl.type.object.declSeq # NIL) THEN
				method := typeDecl.type.object.declSeq.procDecl;
				WHILE (method # NIL) DO
					superClass := typeDecl.type.object.superPtr;
					WHILE (superClass # NIL) DO
						procDecl := superClass.FindProcDecl(method.head.identDef.ident.name^);
						IF (procDecl # NIL) THEN
							INCL(procDecl.head.modifiers, Overwritten);
							INCL(method.head.modifiers, Overwrite)
						END;
						superClass := superClass.superPtr;
					END;
					IF (method.next # NIL) THEN
						method := method.next (ProcDecl);
					ELSE
						method := NIL;
					END;
				END;
			END;
			IF (typeDecl.next # NIL) THEN
				typeDecl := typeDecl.next (TypeDecl);
			ELSE
				typeDecl := NIL;
			END;
		END;
	END;
END ResolveMethodOverwrites;

PROCEDURE ParseFile*(CONST filename : ARRAY OF CHAR; diagnostics : Diagnostics.Diagnostics) : Module;
VAR
	module : Module;
	scanner : OCScanner.Scanner;
	text : Texts.Text; reader : TextUtilities.TextReader;
	format, res : LONGINT;
BEGIN
	ASSERT(diagnostics # NIL);
	NEW(text);
	TextUtilities.LoadAuto(text, filename, format, res);
	IF (res = 0) THEN
		NEW(reader, text);
		scanner := OCScanner.NewScanner(filename, reader, 0, diagnostics);
		Parse(scanner, module);
	ELSE
		diagnostics.Error("ModuleParser", Diagnostics.Invalid, Diagnostics.Invalid, "File not found");
	END;
	RETURN module
END ParseFile;

(** Parse all modules required to set the Record.superPtr and Object.superPtr fields and set these fields*)
PROCEDURE SetSuperTypes*(module: Module);
VAR cache : ModuleCache; nofModules : LONGINT;
BEGIN
	ASSERT(module # NIL);
	NEW(cache);
	cache.Add(module);
	ResolveTypeHierarchy(module, cache);
	nofModules := -1;
	WHILE (nofModules # cache.nofModules) DO
		nofModules := cache.nofModules;
		cache.Enumerate(ResolveTypeHierarchy);
	END;
	cache.Enumerate(ResolveMethodOverwrites);
END SetSuperTypes;

PROCEDURE Parse*(scanner: OCScanner.Scanner; VAR module: Module);
VAR parser: Parser;
BEGIN
	NEW(parser, scanner);
	parser.ModuleP(module);
END Parse;

END ModuleParser.

PC.Compile \s ModuleParser.Mod ~
Builder.Compile \s  ModuleParser.Mod ~
System.DeleteFiles ModuleParser.Obx ~
System.Free ModuleParser ~
Decoder.Decode ModuleParser ~
