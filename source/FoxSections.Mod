MODULE FoxSections; (** AUTHOR "fof"; PURPOSE "support for code sections and references"; *)

IMPORT SyntaxTree := FoxSyntaxTree,Streams,Global := FoxGlobal,Formats := FoxFormats, Basic := FoxBasic, Strings, ObjectFile, StringPool;

CONST
	(* section types *)
	CodeSection*=ObjectFile.Code;
	InitCodeSection*=ObjectFile.InitCode;
	InitCode2Section*=ObjectFile.InitCode2;
	BodyCodeSection*=ObjectFile.BodyCode;
	VarSection*=ObjectFile.Data;
	ConstSection*=ObjectFile.Const;
	InlineCodeSection*=10;

	LineCommentStart*="; ";



TYPE
	Identifier*=ObjectFile.Identifier;

	Section*=OBJECT
	VAR
		name-: SyntaxTree.String; (* name of this section (globally unique-name derived from symbol name) *)
		type-: SHORTINT; (* CodeSection, InlineCodeSection, VarSection or ConstSection *)
		symbol-: SyntaxTree.Symbol; (* corresponding symbol in AST *)
		offset-: LONGINT; (* mainly for compatibility with old object file format *)
		entryNumber-: LONGINT; (* needed for old object file format, will be removed *)
		referenced-: BOOLEAN;
		nextSection-: Section;
		fixed-: BOOLEAN; alignment-: LONGINT;

		PROCEDURE &InitSection*(type: SHORTINT; CONST n: ARRAY OF CHAR; symbol: SyntaxTree.Symbol);
		BEGIN
			COPY(n,name);
			SELF.symbol := symbol;
			SELF.type := type;
			entryNumber := 0;
			offset := 0;
			entryNumber := 0;
			referenced := TRUE;
			fixed := FALSE;
			alignment := 0;
		END InitSection;


		PROCEDURE SetReferenced*(ref: BOOLEAN);
		BEGIN referenced := ref;
		END SetReferenced;

		PROCEDURE SetOffset*(offset: LONGINT);
		BEGIN SELF.offset := offset;
		END SetOffset;

		PROCEDURE SetAlignment*(fix: BOOLEAN; value: LONGINT);
		BEGIN
			fixed := fix; alignment := value
		END SetAlignment;


		(* needed for old object file format, will be removed *)
		PROCEDURE SetEntryNumber*(nr: LONGINT);
		BEGIN entryNumber := nr;
		END SetEntryNumber;

		PROCEDURE Dump*(w: Streams.Writer);
		BEGIN
			CASE type OF
				|CodeSection:w.String("code ")
				|BodyCodeSection:w.String("bodycode ")
				|InlineCodeSection:w.String("inlinecode ")
				|VarSection:w.String("var ");
				|ConstSection:w.String("const ");
				|InitCodeSection: w.String("initcode ");
				|InitCode2Section: w.String("initcode2 ");
			END;
			DumpName(w);
			w.String(" offset="); w.Int(offset,1);
		END Dump;

		PROCEDURE DumpName*(w: Streams.Writer);
		BEGIN
			w.String(name);
		END DumpName;

	END Section;

	CommentStr* = POINTER TO ARRAY OF CHAR;
	Comment* = OBJECT
		VAR str-: CommentStr; strLen: LONGINT; pos-: LONGINT; nextComment-: Comment;

		PROCEDURE &Init*(pos: LONGINT);
		BEGIN
			SELF.pos := pos;
			NEW(str,32); strLen := 0;
			str[0] := 0X;
		END Init;

		PROCEDURE Append(CONST buf: ARRAY OF CHAR;  ofs, len: LONGINT);

			PROCEDURE Resize(newLen: LONGINT);
			VAR new: CommentStr; i: LONGINT;
			BEGIN
				NEW(new,newLen);
				FOR i := 0 TO strLen-1 DO
					new[i] := str[i]
				END;
				str := new
			END Resize;

		BEGIN
			INC(len,ofs);
			ASSERT(LEN(buf) >= len);
			WHILE (ofs < len) & (buf[ofs] # 0X) DO
				IF LEN(str) <= strLen THEN Resize(2*strLen) END;
				str[strLen] := buf[ofs];
				INC(ofs); INC(strLen);
			END;
			IF LEN(str) <= strLen THEN Resize(2*strLen) END;
			str[strLen] := 0X;
		END Append;

		PROCEDURE Dump*(w: Streams.Writer);
		VAR i: LONGINT;ch: CHAR; newln: BOOLEAN;
		BEGIN
			IF w IS Basic.Writer THEN w(Basic.Writer).BeginComment; w(Basic.Writer).IncIndent; END;
			w.String("; ");
			i := 0; ch := str[i]; newln := FALSE;
			WHILE(ch#0X) DO
				IF (ch = 0DX) OR (ch = 0AX) THEN newln := TRUE
				ELSE
					IF newln THEN w.Ln; w.String(LineCommentStart); newln := FALSE;  END;
				 	w.Char(ch);
				 END;
				INC(i); ch := str[i];
			END;
			IF w IS Basic.Writer THEN w(Basic.Writer).EndComment; w(Basic.Writer).DecIndent;END;
			w.Update;
		END Dump;

	END Comment;

	GetPCProcedure=PROCEDURE{DELEGATE}(): LONGINT;

	CommentWriter*= OBJECT (Streams.Writer)
	VAR
		firstComment-,lastComment-: Comment; comments-: LONGINT;
		getPC: GetPCProcedure;

		PROCEDURE AppendToLine*( CONST buf: ARRAY OF CHAR;  ofs, len: LONGINT;  propagate: BOOLEAN;  VAR res: LONGINT );
		VAR pos: LONGINT;
		BEGIN
			IF len = 0 THEN RETURN END;
			pos := getPC();
			IF lastComment = NIL THEN
				NEW(lastComment,pos); firstComment := lastComment;
			ELSIF (lastComment.pos # pos) THEN
				NEW(lastComment.nextComment,pos);
				lastComment := lastComment.nextComment;
			END;
			lastComment.Append(buf,ofs,len)
		END AppendToLine;

		PROCEDURE Ln;
		BEGIN
			Ln^;
			Update;
		END Ln;

		PROCEDURE Reset*;
		BEGIN
			firstComment := NIL; lastComment := NIL; comments := 0;
			Reset^;
		END Reset;


		PROCEDURE & InitCommentWriter*(getPC: GetPCProcedure);
		BEGIN
			SELF.getPC := getPC;
			InitWriter(AppendToLine,256);
			firstComment := NIL; lastComment := NIL; comments := 0;
		END InitCommentWriter;

	END CommentWriter;

	SectionLookup = OBJECT(Basic.HashTable); (* SyntaxTree.Symbol _> Symbol *)
	VAR

		PROCEDURE GetSection(symbol: SyntaxTree.Symbol):Section;
		VAR p: ANY;
		BEGIN
			p := Get(symbol);
			IF p # NIL THEN
				ASSERT(p(Section).symbol = symbol);
				RETURN p(Section);
			ELSE
				RETURN NIL
			END;
		END GetSection;

		PROCEDURE PutSection(symbol: SyntaxTree.Symbol; section: Section);
		BEGIN
			Put(symbol,section);
		END PutSection;

	END SectionLookup;

	SectionNameLookup = OBJECT(Basic.HashTableInt); (* SyntaxTree.Symbol _> Symbol *)

		PROCEDURE GetSection(CONST name: ARRAY OF CHAR):Section;
		VAR p: ANY; index: LONGINT;
		BEGIN
			index := StringPool.GetIndex1(name);
			p := Get(index);
			IF p # NIL THEN
				ASSERT(StringPool.GetIndex1(p(Section).name)=index);
				RETURN p(Section);
			ELSE
				RETURN NIL
			END;
		END GetSection;

		PROCEDURE PutSection(CONST name: ARRAY OF CHAR; section: Section);
		VAR index: LONGINT;
		BEGIN
			index := StringPool.GetIndex1(name);
			Put(index,section);
		END PutSection;

	END SectionNameLookup;


	SectionList*=OBJECT
	VAR first-,last-: Section; number-: LONGINT;
		lookup: SectionLookup;
		lookupName: SectionNameLookup;

		PROCEDURE & InitSectionList*;
		BEGIN first := NIL; last := NIL; number := 0; NEW(lookup,100); NEW(lookupName,100);
		END InitSectionList;

		PROCEDURE Add*(n: Section);
		BEGIN
			n.nextSection := NIL;
			IF first = NIL THEN first := n ELSE last.nextSection := n END; last := n; INC(number);
			IF n.symbol # NIL THEN (* special case, may not be added to lookup list *)
				lookup.PutSection(n.symbol,n)
			END;
			IF n.name # "" THEN
				lookupName.PutSection(n.name,n);
			END;
		END Add;

		PROCEDURE FindBySymbol*(symbol: SyntaxTree.Symbol): Section;
		BEGIN
			IF symbol = NIL THEN
				RETURN NIL
			ELSE
				RETURN lookup.GetSection(symbol)
			END
		END FindBySymbol;

		PROCEDURE FindByName*(CONST name: ARRAY OF CHAR): Section;
		BEGIN
			IF name = "" THEN
				RETURN NIL
			ELSE
				RETURN lookupName.GetSection(name)
			END
		END FindByName;


		PROCEDURE Dump*( w: Streams.Writer);
		VAR n: Section;
		BEGIN
			n := first;
			WHILE n # NIL DO
				n.Dump(w); w.Ln;
				n := n.nextSection;
			END;
		END Dump;

	END SectionList;

	Module* = OBJECT (Formats.GeneratedModule)
		VAR
			(* output of (intermediate) code generation *)
			sections-: SectionList;
			(*! separation of imported symbols, system calls and case tables for the old object file format,
				can be unified later on *)
			caseTables-: SectionList;
			importedSymbols-: SectionList;
			systemCalls-: SectionList;

		PROCEDURE & Init*(module: SyntaxTree.Module; system: Global.System);
		BEGIN
			Init^(module,system);
			NEW(sections);
			NEW(importedSymbols);
			NEW(systemCalls);
			NEW(caseTables);
		END Init;

		PROCEDURE Dump*(w: Streams.Writer);
		VAR name: SyntaxTree.String; import: SyntaxTree.Import; first: BOOLEAN;

		BEGIN
			w.String("module ");
			Global.ModuleFileName(module.name,module.context,name);
			w.String(name);
			w.Ln;
			w.Ln;

			import := module.moduleScope.firstImport;
			IF import # NIL THEN
				w.String("imports "); first := TRUE;
				WHILE import # NIL DO
					IF first THEN first := FALSE ELSE w.String(", ") END;
					IF import.module # NIL THEN
						Global.ModuleFileName(import.module.name,import.module.context,name);
					ELSE
						name := "<import failed>";
					END;
					w.String(name);
					import := import.nextImport;
				END;
				w.Ln; w.Ln;
			END;

			sections.Dump(w);
			w.Ln; w.String("; case tables"); w.Ln;
			caseTables.Dump(w);
			w.Ln; w.String("; imported symbols"); w.Ln;
			importedSymbols.Dump(w);
			w.Ln; w.String("; system calls"); w.Ln;
			systemCalls.Dump(w);
		END Dump;


	END Module;

	PROCEDURE DumpFiltered*(w: Streams.Writer; module: Module; CONST filter: ARRAY OF CHAR);
		PROCEDURE FilterSections(section: Section);
		BEGIN
			WHILE(section # NIL) DO
				IF Strings.Match(filter,section.name) THEN section.Dump(w); w.Ln; END;
				section := section.nextSection;
			END;
		END FilterSections;

	BEGIN
		FilterSections(module.sections.first);
		FilterSections(module.caseTables.first);
		FilterSections(module.importedSymbols.first);
		FilterSections(module.systemCalls.first);
	END DumpFiltered;

	PROCEDURE NewCommentWriter*(getPC: GetPCProcedure): CommentWriter;
	VAR c: CommentWriter;
	BEGIN
		NEW(c,getPC); RETURN c
	END NewCommentWriter;

END FoxSections.
