MODULE GenericLinker;	(* AUTHOR "negelef"; PURPOSE "Generic Object File Linker"; *)

IMPORT ObjectFile, Streams, Diagnostics;

TYPE Address* = ObjectFile.Unit;

CONST InvalidAddress* = MAX (Address);

TYPE Priority = LONGINT;

CONST InitCode = 0; Code = 1; Default = 2;

TYPE Arrangement* = OBJECT

	PROCEDURE Allocate* (CONST section: ObjectFile.Section): Address;
	END Allocate;

	PROCEDURE Patch* (pos, value: Address; offset, bits, unit: ObjectFile.Bits);
	END Patch;

END Arrangement;

TYPE Block = POINTER TO RECORD (ObjectFile.Section);
	next: Block;
	address: Address;
	referenced, used: BOOLEAN;
END;

TYPE Linker* = OBJECT
VAR
	diagnostics: Diagnostics.Diagnostics;
	verbose, error-: BOOLEAN;
	code, data: Arrangement;
	firstBlock, firstLinkedBlock: Block;

	PROCEDURE &InitLinker* (diagnostics: Diagnostics.Diagnostics; verbose: BOOLEAN; code, data: Arrangement);
	BEGIN SELF.diagnostics := diagnostics; SELF.verbose := verbose; error := FALSE; SELF.code := code; SELF.data := data; firstBlock := NIL; firstLinkedBlock := NIL;
	END InitLinker;

	PROCEDURE Error* (CONST source, message: ARRAY OF CHAR);
	BEGIN diagnostics.Error (source, Diagnostics.Invalid, Diagnostics.Invalid, message); error := TRUE;
	END Error;

	PROCEDURE Information* (CONST source, message: ARRAY OF CHAR);
	BEGIN IF verbose THEN diagnostics.Information (source, Diagnostics.Invalid, Diagnostics.Invalid, message); END;
	END Information;

	PROCEDURE FindBlock (CONST name: ObjectFile.SectionName): Block;
	VAR block: Block;
	BEGIN
		block := firstBlock;
		WHILE (block # NIL) & (block.name # name) DO block := block.next END;
		RETURN block;
	END FindBlock;

	PROCEDURE GetArrangement (block: Block): Arrangement;
	BEGIN  IF ObjectFile.IsCode (block.type) THEN RETURN code; ELSE RETURN data; END;
	END GetArrangement;

	PROCEDURE AddSection* (CONST section: ObjectFile.Section);
	VAR priority: Priority; block, current, previous: Block;
	BEGIN
		IF FindBlock (section.name) # NIL THEN Error (section.name, "duplicated section"); RETURN; END;
		NEW (block); ObjectFile.CopySection (section, block^); block.address := InvalidAddress; block.referenced := FALSE; block.used := FALSE;
		priority := GetPriority (block); current := firstBlock; previous := NIL;
		WHILE (current # NIL) & (GetPriority (current) < priority) DO previous := current; current := current.next; END;
		IF previous # NIL THEN previous.next := block; ELSE firstBlock := block; END; block.next := current;
	END AddSection;

	PROCEDURE Link*;
	VAR block: Block;
	BEGIN
		IF ~error THEN block := firstBlock; WHILE block # firstLinkedBlock DO Reference (block, GetPriority (block) = InitCode); block := block.next; END; END;
		IF ~error THEN block := firstBlock; WHILE block # firstLinkedBlock DO IF block.used THEN Arrange (block); END; block := block.next; END; END;
		IF ~error THEN block := firstBlock; WHILE block # firstLinkedBlock DO IF block.used THEN Patch (block); END; block := block.next; END; END;
		IF ~error THEN firstLinkedBlock := firstBlock; END;
		IF ~error & verbose THEN block := firstBlock; WHILE block # NIL DO Diagnose (block); block := block.next; END; END;
	END Link;

	PROCEDURE Reference (block: Block; used: BOOLEAN);
	VAR i: LONGINT; reference: Block;
	BEGIN
		IF used & ~block.used THEN block.used := TRUE;
		ELSIF block.referenced THEN RETURN; END; block.referenced := TRUE;
		FOR i := 0 TO block.fixups - 1 DO
			reference := FindBlock (block.fixup[i].section);
			IF reference # NIL THEN Reference (reference, block.used); ELSE Error (block.fixup[i].section, "unresolved"); END;
		END;
	END Reference;

	PROCEDURE Arrange (block: Block);
	VAR arrangement: Arrangement;
	BEGIN
		ASSERT (block.used);
		arrangement := GetArrangement (block);
		block.address := arrangement.Allocate (block^);
		IF block.address = InvalidAddress THEN Error (block.name, "failed to allocate"); RETURN; END;
		ASSERT ((block.alignment = 0) OR (block.address MOD block.alignment = 0));
	END Arrange;

	PROCEDURE Patch (block: Block);
	VAR arrangement: Arrangement; i: LONGINT;

		PROCEDURE PatchFixup (CONST fixup: ObjectFile.Fixup);
		VAR reference: Block; target, address: Address; i: LONGINT;

			PROCEDURE PatchPattern (CONST pattern: ObjectFile.FixupPattern);
			BEGIN arrangement.Patch (target, address, pattern.offset, pattern.bits, block.unit); address := ASH (address, -pattern.bits);
			END PatchPattern;

		BEGIN
			target := block.address + fixup.offset;
			reference := FindBlock (fixup.section); ASSERT (reference # NIL);
			address := reference.address + fixup.displacement;
			IF fixup.mode = ObjectFile.Relative THEN DEC (address, target); END;
			address := ASH (address, -fixup.scale);
			FOR i := 0 TO fixup.patterns - 1 DO PatchPattern (fixup.pattern[i]); END;
		END PatchFixup;

	BEGIN
		ASSERT (block.used);
		arrangement := GetArrangement (block);
		FOR i := 0 TO block.fixups - 1 DO PatchFixup (block.fixup[i]); END;
	END Patch;

	PROCEDURE Diagnose (block: Block);
	BEGIN
		IF block.used THEN Information (block.name, "arranged at");
		ELSE Information (block.name, "unused"); END;
	END Diagnose;

END Linker;

PROCEDURE GetPriority (block: Block): Priority;
BEGIN
	IF block.type = ObjectFile.InitCode THEN RETURN InitCode END;
	IF block.type = ObjectFile.Code THEN RETURN Code END;
	RETURN Default;
END GetPriority;

PROCEDURE Process* (reader: Streams.Reader; linker: Linker);
VAR section: ObjectFile.Section;
BEGIN
	WHILE reader.Peek () # 0X DO
		ObjectFile.ReadSection (reader, section);
		reader.SkipWhitespace;
		IF reader.res = Streams.Ok THEN linker.AddSection (section); END;
	END;
END Process;

END GenericLinker.
