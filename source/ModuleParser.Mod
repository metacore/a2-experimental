MODULE ModuleParser;	(** AUTHOR "mb"; PURPOSE "Active Oberon parser for use with ModuleTrees **)
(**
 * Notes:
 *	- The Module node's parent is the module node itself
 *)

IMPORT Streams, Strings, StringPool, Files, PCS, KernelLog, Texts, TextUtilities;

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
	delegate: StringPool.Index;
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
		sym: PCS.Token;
		scanner: PCS.Scanner;
		hasError: BOOLEAN;

		PROCEDURE & Init*(scanner: PCS.Scanner);
		BEGIN
			SELF.scanner := scanner;
			hasError := FALSE;
		END Init;

		PROCEDURE ModuleP(VAR module: Module);
		VAR
			name: ARRAY 64 OF CHAR;
			modName: PCS.Name;
			definition: Definition;
		BEGIN
			scanner.Get(sym);
			IF sym = PCS.module THEN
				NEW(module, NIL); module.parent := module;
				scanner.Get(sym);
				IF sym = PCS.ident THEN
					modName := scanner.name;
					StringPool.GetString(scanner.name, name);
					NEW(module.ident);
					module.ident.name := Strings.NewString(name);
					module.ident.pos := scanner.errpos;
				END;
				scanner.Get(sym);
				IF sym = PCS.in THEN
					scanner.Get(sym);
					IF sym = PCS.ident THEN
						StringPool.GetString(scanner.name, name);
						NEW(module.context);
						module.context.name := Strings.NewString(name);
						module.context.pos := scanner.errpos;
					END;
					Check (PCS.ident);
				END;
				IF sym = PCS.lbrace THEN
					WHILE (sym # PCS.semicolon) & (sym # PCS.eof) DO scanner.Get(sym) END;
				END;
				Check(PCS.semicolon);
				IF sym = PCS.import THEN
					NEW(module.importList, module);
					ImportListP(module.importList);
				END;
				WHILE sym = PCS.definition DO
					NEW(definition, module);
					DefinitionP(definition);
					IF module.definitions = NIL THEN module.definitions := definition
					ELSE AppendLast(module.definitions, definition)
					END;
				END;
				IF (sym = PCS.const) OR (sym = PCS.type) OR (sym = PCS.var) OR (sym = PCS.procedure) THEN
					NEW(module.declSeq, module);
					DeclSeqP(module.declSeq);
				END;
				IF (sym = PCS.begin) THEN
					module.bodyPos := scanner.errpos;
				ELSE
					module.bodyPos := 0;
				END;
				BodyP(FALSE, module.modifiers);
				IF (sym = PCS.ident) & (scanner.name = modName) THEN
					(* correct *)
				ELSE
					(* maybe missing END or wrong module name *)
					hasError := TRUE;
					KernelLog.String("err3: "); KernelLog.Int(scanner.errpos, 0); KernelLog.Ln;
				END;
				module.hasError := hasError;
			END;
		END ModuleP;

		PROCEDURE ImportListP(import: Import);
		VAR
			name: ARRAY 64 OF CHAR;
			newImport: Import;
		BEGIN
			scanner.Get(sym);
			WHILE sym = PCS.ident DO
				StringPool.GetString(scanner.name, name);
				NEW(import.ident);
				import.ident.name := Strings.NewString(name);
				import.ident.pos := scanner.errpos;
				scanner.Get(sym);	(* avoids endless loop *)
				IF sym = PCS.becomes THEN
					scanner.Get(sym);
					IF sym = PCS.ident THEN
						StringPool.GetString(scanner.name, name);
						NEW(import.alias);
						import.alias.name := Strings.NewString(name);
						import.alias.pos := scanner.errpos;
						scanner.Get(sym);
					ELSE
						(* Error *)
						hasError := TRUE;
						KernelLog.String("err2: "); KernelLog.Int(scanner.errpos, 0); KernelLog.Ln;
					END;
				END;
				IF sym = PCS.in THEN
					scanner.Get(sym);
					IF sym = PCS.ident THEN
						StringPool.GetString(scanner.name, name);
						NEW(import.context);
						import.context.name := Strings.NewString(name);
						import.context.pos := scanner.errpos;
					END;
					Check (PCS.ident);
				END;
				IF sym = PCS.comma THEN
					scanner.Get(sym);
				END;
				NEW(newImport, import.parent);
				import.next := newImport;
				import := newImport;
			END;
			Check(PCS.semicolon);
		END ImportListP;

		PROCEDURE DefinitionP(definition: Definition);
		VAR
			procHead: ProcHead;
		BEGIN
			IF sym = PCS.definition THEN
				scanner.Get(sym);
				IF sym = PCS.ident THEN
					StringPool.GetString(scanner.name, name);
					NEW(definition.ident);
					definition.ident.name := Strings.NewString(name);
					definition.ident.pos := scanner.errpos;
					scanner.Get(sym);
				END;
				WHILE sym = PCS.semicolon DO scanner.Get(sym) END;
				IF sym = PCS.refines THEN
					scanner.Get(sym);
					NEW(definition.refines, definition);
					QualidentP(definition.refines);
				END;
				WHILE sym = PCS.procedure DO
					NEW(procHead, definition);
					scanner.Get(sym);
					ProcHeadP(procHead);
					IF definition.procs = NIL THEN definition.procs := procHead
					ELSE AppendLast(definition.procs, procHead)
					END;
					Check(PCS.semicolon);
				END;
				Check(PCS.end);
				Check(PCS.ident);
				WHILE sym = PCS.semicolon DO scanner.Get(sym) END;
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
				IF sym # PCS.end THEN
					REPEAT Check(PCS.semicolon) UNTIL sym # PCS.semicolon
				END;
			END CheckEndOrSemicolon;

		BEGIN
			LOOP
				CASE sym OF
				| PCS.const:
					scanner.Get(sym);
					WHILE sym = PCS.ident DO
						NEW(constDecl, declSeq);
						ConstDeclP(constDecl);
						IF declSeq.constDecl = NIL THEN declSeq.constDecl := constDecl;
						ELSE AppendLast(declSeq.constDecl, constDecl);
						END;
						CheckEndOrSemicolon;
						(*Check(PCS.semicolon);*)
					END;
				| PCS.type:
					scanner.Get(sym);
					WHILE sym = PCS.ident DO
						NEW(typeDecl, declSeq);
						TypeDeclP(typeDecl);
						IF declSeq.typeDecl = NIL THEN declSeq.typeDecl := typeDecl;
						ELSE AppendLast(declSeq.typeDecl, typeDecl);
						END;
						CheckEndOrSemicolon;
						(*Check(PCS.semicolon);*)
					END;
				| PCS.var:
					scanner.Get(sym);
					WHILE sym = PCS.ident DO
						NEW(varDecl, declSeq);
						VarDeclP(varDecl);
						IF declSeq.varDecl = NIL THEN declSeq.varDecl := varDecl;
						ELSE AppendLast(declSeq.varDecl, varDecl);
						END;
						CheckEndOrSemicolon;
						(*Check(PCS.semicolon);*)
					END;
				| PCS.procedure:
					WHILE sym = PCS.procedure DO
						scanner.Get(sym);
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
						(*Check(PCS.semicolon);*)
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
			Check(PCS.eql);
			(* NEW(const.constExpr);
			ExprP(const.constExpr); *)
			NEW(const.expr);
			ConstExprP(PCS.semicolon, -1, const.expr);
		END ConstDeclP;

		PROCEDURE TypeDeclP(type: TypeDecl);
		BEGIN
			NEW(type.identDef);
			IdentDefP(type.identDef);
			Check(PCS.eql);
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
			WHILE sym = PCS.comma DO
				scanner.Get(sym);	(* avoids endless loop *)
				NEW(identDef);
				IdentDefP(identDef);
				SysFlag;
				NEW(identList, var);
				identList.identDef := identDef;
				AppendLast(var.identList, identList);
			END;
			Check(PCS.colon);
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
			Check(PCS.semicolon);
			IF (sym = PCS.const) OR (sym = PCS.var) OR (sym = PCS.type) OR (sym = PCS.procedure) THEN
				NEW(declSeq, proc);
				DeclSeqP(declSeq);
				IF proc.declSeq = NIL THEN proc.declSeq := declSeq;
				ELSE AppendLast(proc.declSeq, declSeq);
				END;
			END;
			IF (sym = PCS.begin) THEN
				proc.bodyPos := scanner.errpos;
			ELSE
				proc.bodyPos := 0;
			END;
			BodyP(FALSE, proc.head.modifiers);
			scanner.Get(sym);	(* skip ident *)
		END ProcDeclP;

		PROCEDURE ProcHeadP(head: ProcHead);
		VAR forward: BOOLEAN;
		BEGIN
			SysFlag;
			CASE sym OF
			| PCS.minus: head.inline := TRUE; scanner.Get(sym);
			| PCS.and: head.constructor := TRUE; scanner.Get(sym);
			| PCS.times: (* ignore *) scanner.Get(sym);
			| PCS.arrow: (* ignore *) scanner.Get(sym); forward := TRUE;
			| PCS.string: head.operator := TRUE;
			| PCS.number: IF scanner.numtyp = PCS.char THEN head.operator := TRUE END;
			ELSE
			END;
			NEW(head.identDef);
			IdentDefP(head.identDef);
			OSAIrq;		(* tk: Compatibility to OSACompiler*)
			IF sym = PCS. lparen THEN
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
			IF sym = PCS.lbrace THEN
				scanner.Get(sym);
				Check(PCS.ident);
				IF sym = PCS.comma THEN
					scanner.Get(sym);
					Check(PCS.ident)
				END;
				Check(PCS.rbrace);
			END;
		END SysFlag;

		(* tk: For OSA Compatibility *)
		PROCEDURE OSAIrq;
		BEGIN
			IF sym = PCS.lbrak THEN
				scanner.Get(sym);
				Check(PCS.number);
				Check(PCS.rbrak);
			END;
		END OSAIrq;

		PROCEDURE FormalParsP(pars: FormalPars);
		VAR
			fpSection: FPSection;
		BEGIN
			scanner.Get(sym);
			IF (sym = PCS.var) OR (sym = PCS.const) OR (sym = PCS.ident) THEN
				NEW(pars.fpSectionList, pars);
				FPSectionP(pars.fpSectionList);
				WHILE sym = PCS.semicolon DO
					scanner.Get(sym);	(* avoids endless loop *)
					NEW(fpSection, pars.fpSectionList);
					FPSectionP(fpSection);
					AppendLast(pars.fpSectionList, fpSection);
				END;
			END;
			Check(PCS.rparen);
			IF sym = PCS.colon THEN
				scanner.Get(sym);
				IF sym = PCS.object THEN
					NEW(pars.returnTypeObj);
					pars.returnTypeObj.name := Strings.NewString("OBJECT");
					pars.returnTypeObj.pos := scanner.errpos;
					scanner.Get(sym);
				ELSIF sym = PCS.array THEN
					NEW(pars.returnTypeAry, pars);
					scanner.Get(sym);
					ArrayP(pars.returnTypeAry);

					(*
					NEW(pars.returnType.ident);
					pars.returnType.ident.name := Strings.NewString("ARRAY OF ???");
					pars.returnType.ident.pos := scanner.errpos;
					SkipTo(PCS.semicolon);
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
			IF sym = PCS.var THEN
				fpSection.var := TRUE;
				scanner.Get(sym);
			ELSIF sym = PCS.const THEN
				fpSection.const := TRUE;
				scanner.Get(sym);
			END;
			IF sym = PCS.ident THEN
				(*StringPool.GetString(scanner.name, name);*)
				NEW(fpSection.identList, fpSection);
				NEW(fpSection.identList.identDef);
				IdentDefP(fpSection.identList.identDef);
				(*
				fpSection.identList.ident.name := Strings.NewString(name);
				fpSection.identList.ident.pos := scanner.errpos;
				scanner.Get(sym);
				*)
				WHILE sym = PCS.comma DO
					NEW(identList, fpSection.identList);
					scanner.Get(sym);
					NEW(identList.identDef);
					IdentDefP(identList.identDef);
					AppendLast(fpSection.identList, identList);
					(*
					IF sym = PCS.ident THEN
						StringPool.GetString(scanner.name, name);
						NEW(identDef);
						NEW(identDef.ident);
						identDef.ident.name := Strings.NewString(name);
						identDef.ident.pos := scanner.errpos;
						AppendLast(fpSection.identlist, identDef);
						scanner.Get(sym);
					END;
					*)
				END;
				Check(PCS.colon);
				NEW(fpSection.type, fpSection);
				TypeP(fpSection.type);
			END;
		END FPSectionP;

		PROCEDURE TypeP(type: Type);
		BEGIN
			CASE sym OF
			| PCS.array: scanner.Get(sym); NEW(type.array, type); ArrayP(type.array);
			| PCS.record: scanner.Get(sym); NEW(type.record, type); RecordP(type.record);
			| PCS.pointer: scanner.Get(sym); NEW(type.pointer, type); PointerP(type.pointer);
			| PCS.object: scanner.Get(sym); NEW(type.object, type); ObjectP(type.object);
			| PCS.procedure: scanner.Get(sym); NEW(type.procedure, type); ProcedureP(type.procedure);
			| PCS.ident: NEW(type.qualident, type); QualidentP(type.qualident);
			ELSE
				(* Error *)
				hasError := TRUE; KernelLog.String("err4: "); KernelLog.Int(scanner.errpos, 0); KernelLog.Ln;
				scanner.Get(sym);	(* ??? *)
			END;
		END TypeP;

		PROCEDURE ArrayP(array: Array);
		BEGIN
			SysFlag;
			IF sym = PCS.of THEN
				array.open := TRUE;
				NEW(array.base, array);
				scanner.Get(sym);
				TypeP(array.base);
			ELSE
				NEW(array.len);
				ConstExprP(PCS.of, PCS.comma, array.len);
				(*
				SimpleExprP(array.len);
				*)
				IF sym = PCS.of THEN
					NEW(array.base, array);
					scanner.Get(sym);
					TypeP(array.base);
				ELSIF sym = PCS.comma THEN
					NEW(array.base, array);
					NEW(array.base.array, array);
					scanner.Get(sym);
					ArrayP(array.base.array)
				ELSE
					(* Error *)
					hasError := TRUE;
					KernelLog.String("err1: "); KernelLog.Int(scanner.errpos, 0); KernelLog.Ln;
				END;
			END;
		END ArrayP;

		PROCEDURE RecordP(record: Record);
		BEGIN
			SysFlag;
			IF sym = PCS.lparen THEN
				scanner.Get(sym);
				NEW(record.super, record);
				QualidentP(record.super);
				Check(PCS.rparen);
			END;
			WHILE sym = PCS.semicolon DO scanner.Get(sym) END;
			IF sym = PCS.ident THEN
				NEW(record.fieldList, record);
				FieldListP(record.fieldList);
			END;
			Check(PCS.end);
		END RecordP;

		PROCEDURE FieldListP(fieldList: FieldDecl);
		VAR fieldDecl: FieldDecl;
		BEGIN
			FieldDeclP(fieldList);
			WHILE sym = PCS.semicolon DO
				scanner.Get(sym);
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
			IF sym = PCS.ident THEN
				NEW(fieldDecl.identList, fieldDecl);
				NEW(fieldDecl.identList.identDef);
				IdentDefP(fieldDecl.identList.identDef);
				SysFlag;
				WHILE sym = PCS.comma DO
					scanner.Get(sym);
					NEW(identDef);
					IdentDefP(identDef);
					SysFlag;
					NEW(identList, identList);
					identList.identDef := identDef;
					AppendLast(fieldDecl.identList, identList);
				END;
				Check(PCS.colon);
				NEW(fieldDecl.type, fieldDecl);
				TypeP(fieldDecl.type);
			END;
		END FieldDeclP;

		PROCEDURE PointerP(pointer: Pointer);
		BEGIN
			SysFlag;
			Check(PCS.to);
			NEW(pointer.type, pointer);
			TypeP(pointer.type);
		END PointerP;

		PROCEDURE ObjectP(object: Object);
		VAR declSeq: DeclSeq;
			pos: LONGINT;
			qualident: Qualident;
		BEGIN
			IF (sym = PCS.semicolon) OR (sym = PCS.rparen) THEN RETURN END;
			SysFlag;
			IF sym = PCS.lparen THEN
				NEW(object.super, object);
				scanner.Get(sym);
				QualidentP(object.super);
				Check(PCS.rparen);
			END;
			IF sym = PCS.implements THEN
				NEW(object.implements, object);
				scanner.Get(sym);
				QualidentP(object.implements);
				WHILE sym = PCS.comma DO
					NEW(qualident, object.implements);
					scanner.Get(sym);
					QualidentP(qualident);
					AppendLast(object.implements, qualident);
				END;
			END;
			pos := -1;
			WHILE (sym # PCS.begin) & (sym # PCS.end) & (sym # PCS.eof) DO
					(* avoid endless-loop *)
				IF pos = scanner.errpos THEN scanner.Get(sym) END;
				pos := scanner.errpos;
				NEW(declSeq, object);
				DeclSeqP(declSeq);
				IF object.declSeq = NIL THEN object.declSeq := declSeq;
				ELSE AppendLast(object.declSeq, declSeq);
				END;
			END;
			IF (sym = PCS.begin) THEN
				object.bodyPos := scanner.errpos;
			ELSE
				object.bodyPos := 0;
			END;
			BodyP(TRUE, object.modifiers);
			IF sym = PCS.ident THEN scanner.Get(sym) END;
		END ObjectP;

		PROCEDURE ProcedureP(proc: Procedure);
		BEGIN
			SysFlag;
			IF sym = PCS.lbrace THEN
				scanner.Get(sym);
				IF sym # PCS.ident THEN
					(* Error *)
				ELSIF scanner.name = delegate THEN
					proc.delegate := TRUE;
				END;
				scanner.Get(sym);
				Check(PCS.rbrace);
			END;
			IF sym = PCS.lparen THEN
				NEW(proc.formalPars, proc);
				FormalParsP(proc.formalPars);
			END;
		END ProcedureP;

		PROCEDURE ConstExprP(delimiter1, delimiter2: PCS.Token; expr: InfoItem);
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
			expr.pos := scanner.errpos;
			IF (sym = delimiter1) OR (sym = delimiter2) THEN RETURN END;
			REPEAT
				CASE sym OF
				| PCS.lparen: INC(paren); Add("(");
				| PCS.rparen: DEC(paren); Add(")");
				| PCS.lbrace: INC(brace); Add("{");
				| PCS.rbrace: DEC(brace); Add("}");
				| PCS.lbrak: INC(brak); Add("[");
				| PCS.rbrak: DEC(brak); Add("]");
				| PCS.number: scanner.GetNumAsString(name); Add(name);
				| PCS.nil: Add("NIL");
				| PCS.true: Add("TRUE");
				| PCS.false: Add("FALSE");
				| PCS.not: Add("~");
				| PCS.period: Add(".");
				| PCS.ident: StringPool.GetString(scanner.name, name); Add(name);
				| PCS.comma: Add(", ");
				| PCS.plus: Add(" + ");
				| PCS.minus: Add(" - ");
				| PCS.times: Add(" * ");
				| PCS.upto: Add(" .. ");
				| PCS.eql: Add(" = ");
				| PCS.neq: Add(" # ");
				| PCS.lss: Add(" < ");
				| PCS.leq: Add(" <= ");
				| PCS.gtr: Add(" > ");
				| PCS.geq: Add(" >= ");
				| PCS.in: Add(" IN ");
				| PCS.is: Add(" IS ");
				| PCS.div: Add(" DIV ");
				| PCS.mod: Add(" MOD ");
				| PCS.slash: Add(" / ");
				| PCS.and: Add(" & ");
				| PCS.or: Add(" OR ");
				| PCS.string: name[0] := '"'; name[1] := 0X; Add(name); Add(scanner.str); Add(name);
				| PCS.arrow: Add("^");
				ELSE
					(* error *)
					hasError := TRUE;
				END;
				scanner.Get(sym);
				(* urgh, what an ugly condition ... *)
			UNTIL (((sym = delimiter1) OR (sym = delimiter2)) & (paren = 0) & (brace = 0) & (brak = 0)) OR (sym = PCS.eof);
			IF (longExprStr = NIL) THEN
				expr.name := Strings.NewString(exprStr);
			ELSE
				expr.name := Strings.ConcatToNew(longExprStr^, exprStr);
			END;
		END ConstExprP;

		PROCEDURE BlockModifierP(allowBody : BOOLEAN; VAR modifiers : SET);
		VAR name : ARRAY 64 OF CHAR; ignore : InfoItem;
		BEGIN
			modifiers := {};
			IF sym = PCS.lbrace THEN
				scanner.Get(sym);
				LOOP
					IF sym = PCS.ident THEN
						StringPool.GetString(scanner.name, name);
						IF name = ExclusiveStr  THEN
							modifiers := modifiers + {Exclusive};
							scanner.Get(sym);
						ELSIF allowBody & (name = ActiveStr)  THEN
							modifiers := modifiers + {Active};
							scanner.Get(sym)
						ELSIF allowBody & (name = RealtimeStr) THEN
							scanner.Get(sym);
						ELSIF allowBody & (name = SafeStr)  THEN
							modifiers := modifiers + {Safe};
							scanner.Get(sym)
						ELSIF allowBody & (name = PriorityStr)  THEN
							modifiers := modifiers + {Priority};
							scanner.Get(sym);
							IF sym = PCS.lparen THEN
								scanner.Get(sym);
								NEW(ignore);
								ConstExprP(PCS.rparen, -1, ignore);
								Check(PCS.rparen);
							END;
						ELSE  Error(scanner.errpos); scanner.Get(sym) (* skip the ident, probably a typo *)
						END;
					END;
					IF sym # PCS.comma THEN EXIT END;
					scanner.Get(sym)
				END;
				Check(PCS.rbrace);
			END;
		END BlockModifierP;

		PROCEDURE BodyP(allowBody : BOOLEAN; VAR modifiers : SET);
		VAR end, lastSym: LONGINT; m : SET; first : BOOLEAN;
		BEGIN
			IF sym = PCS.begin THEN
				end := 1;
				first := TRUE;
				REPEAT
					lastSym := sym;
					scanner.Get(sym);
					IF (lastSym = PCS.begin) & (sym = PCS.lbrace) THEN
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
					CASE sym OF
					| PCS.begin: INC(end);
					| PCS.if, PCS.case, PCS.while, PCS.for, PCS.loop, PCS.with: INC(end);
					| PCS.end: DEC(end);
					ELSE
					END;
				UNTIL (end = 0) OR (sym = PCS.eof);
			ELSIF sym = PCS.code THEN
				REPEAT scanner.Get(sym) UNTIL (sym = PCS.end) OR (sym = PCS.eof);
			END;
			scanner.Get(sym);
		END BodyP;

		PROCEDURE QualidentP(qualident: Qualident);
		VAR
			name, name2: ARRAY 64 OF CHAR;
			pos: LONGINT;
		BEGIN
			IF sym = PCS.ident THEN
				StringPool.GetString(scanner.name, name);
				pos := scanner.errpos;
				scanner.Get(sym);
				IF sym = PCS.period THEN
					scanner.Get(sym);
					IF sym = PCS.ident THEN
						StringPool.GetString(scanner.name, name2);
						Strings.Append(name, ".");
						Strings.Concat(name, name2, name);
						scanner.Get(sym);
					END;
				END;
				NEW(qualident.ident);
				qualident.ident.name := Strings.NewString(name);
				qualident.ident.pos := pos;
			END;
		END QualidentP;

		PROCEDURE IdentDefP(identDef: IdentDef);
		VAR
			name: ARRAY 64 OF CHAR;
		BEGIN
			IF sym = PCS.ident THEN
				StringPool.GetString(scanner.name, name);
				NEW(identDef.ident);
				identDef.ident.name := Strings.NewString(name);
				identDef.ident.pos := scanner.errpos;
			ELSIF (sym = PCS.string) OR (sym = PCS.number) & (scanner.numtyp = PCS.char) THEN
				NEW(identDef.ident);
				identDef.ident.name := Strings.NewString(scanner.str);
				identDef.ident.pos := scanner.errpos;
			END;
			scanner.Get(sym);
			IF sym = PCS.times THEN
				identDef.vis := Public;
				scanner.Get(sym);
			ELSIF sym = PCS.minus THEN
				identDef.vis := PublicRO;
				scanner.Get(sym);
			ELSE
				identDef.vis := Private;
			END;
		END IdentDefP;

		PROCEDURE Check(token: PCS.Token);
		BEGIN
			IF sym = token THEN
				(* correct *)
			ELSE
				(* error *)

				KernelLog.String("******* Check error **********  ");
				KernelLog.Int(scanner.errpos, 0);
				KernelLog.Ln;

				hasError := TRUE;
				(*HALT(33);*)
			END;
			scanner.Get(sym);
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

PROCEDURE ParseFile*(CONST filename : ARRAY OF CHAR; out : Streams.Writer) : Module;
VAR
	module : Module; text : Texts.Text; scanner : PCS.Scanner;
	format, res : LONGINT;
BEGIN
	NEW(text);
	TextUtilities.LoadAuto(text, filename, format, res);
	IF (res = 0) THEN
		scanner := PCS.InitWithText(text, 0);
		Parse(scanner, module);
	ELSE
		IF out # NIL THEN out.String("Could not open file "); out.String(filename); out.String(", res: "); out.Int(res, 0); out.Ln; END
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

PROCEDURE Parse*(scanner: PCS.Scanner; VAR module: Module);
VAR parser: Parser;
BEGIN
	NEW(parser, scanner);
	parser.ModuleP(module);
END Parse;

PROCEDURE CreateString(VAR idx: StringPool.Index; CONST str: ARRAY OF CHAR);
BEGIN
	StringPool.GetIndex(str, idx);
END CreateString;

BEGIN
	CreateString(delegate, "DELEGATE");
END ModuleParser.

PC.Compile \s ModuleParser.Mod ~
Builder.Compile \s  ModuleParser.Mod ~
System.DeleteFiles ModuleParser.Obx ~
System.Free ModuleParser ~
Decoder.Decode ModuleParser ~
