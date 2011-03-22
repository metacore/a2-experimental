MODULE GenericLinker;	(* AUTHOR "negelef"; PURPOSE "Generic Object File Linker"; *)

IMPORT ObjectFile, Streams, Diagnostics, Strings;

TYPE Address* = ObjectFile.Unit;

CONST InvalidAddress* = MAX (Address);

TYPE Priority = LONGINT;

CONST Fixed = 0; InitCode = 1; InitCode2=2; BodyCode = 3; Code = 4; Default = 5; Empty = 6;

TYPE Arrangement* = OBJECT

	PROCEDURE Preallocate* (CONST section: ObjectFile.Section);
	END Preallocate;

	PROCEDURE Allocate* (CONST section: ObjectFile.Section): Address;
	END Allocate;

	PROCEDURE Patch* (pos, value: Address; offset, bits, unit: ObjectFile.Bits);
	END Patch;

END Arrangement;

TYPE Block* = POINTER TO RECORD (ObjectFile.Section)
	next: Block;
	address*: Address;
	referenced, used: BOOLEAN;
END;

TYPE Linker* = OBJECT
VAR
	diagnostics: Diagnostics.Diagnostics;
	verbose, useAll, stripInitCodes, error-: BOOLEAN;
	code, data: Arrangement;
	firstBlock, firstLinkedBlock: Block;
	linkRoot: ObjectFile.SectionName;

	PROCEDURE &InitLinker* (diagnostics: Diagnostics.Diagnostics; verbose, useAll, stripInitCodes: BOOLEAN; code, data: Arrangement);
	BEGIN
		SELF.diagnostics := diagnostics; SELF.verbose := verbose; SELF.useAll := useAll; SELF.stripInitCodes := stripInitCodes;
		error := FALSE; SELF.code := code; SELF.data := data; firstBlock := NIL; firstLinkedBlock := NIL;
		linkRoot := "";
	END InitLinker;

	PROCEDURE SetLinkRoot*(CONST root: ARRAY OF CHAR);
	BEGIN COPY(root, linkRoot)
	END SetLinkRoot;

	PROCEDURE Error* (CONST source, message: ARRAY OF CHAR);
	BEGIN diagnostics.Error (source, Diagnostics.Invalid, Diagnostics.Invalid, message); error := TRUE;
	END Error;

	PROCEDURE Information* (CONST source, message: ARRAY OF CHAR);
	BEGIN IF verbose THEN diagnostics.Information (source, Diagnostics.Invalid, Diagnostics.Invalid, message); END;
	END Information;

	PROCEDURE FindBlock* (CONST identifier: ObjectFile.Identifier): Block;
	VAR block: Block;
	BEGIN
		block := firstBlock;
		WHILE (block # NIL) & (block.identifier.name # identifier.name) DO block := block.next END;
		RETURN block;
	END FindBlock;

	PROCEDURE ImportBlock*(CONST identifier: ObjectFile.Identifier): Block;
	BEGIN
		RETURN NIL
	END ImportBlock;

	PROCEDURE ExportBlock*(block: Block);
	BEGIN
		(* can be overwritten by implementers, for example for hashing the block *)
	END ExportBlock;

	PROCEDURE GetArrangement (block: Block): Arrangement;
	BEGIN  IF ObjectFile.IsCode (block.type) THEN RETURN code; ELSE RETURN data; END;
	END GetArrangement;

	PROCEDURE AddSection* (CONST section: ObjectFile.Section);
	VAR priority: Priority; block, current, previous: Block;
	BEGIN
		IF FindBlock (section.identifier) # NIL THEN Error (section.identifier.name, "duplicated section"); RETURN; END;
		NEW (block); ObjectFile.CopySection (section, block^); block.address := InvalidAddress; block.referenced := FALSE; block.used := FALSE;
		priority := GetPriority (block); current := firstBlock; previous := NIL;
		WHILE (current # NIL) & (GetPriority (current) <= priority) DO previous := current; current := current.next; END;
		IF previous # NIL THEN previous.next := block; ELSE firstBlock := block; END; block.next := current;
		ExportBlock(block);
	END AddSection;

	PROCEDURE Resolve*;
	VAR block: Block; used: BOOLEAN; name: ARRAY 256 OF CHAR;
	BEGIN
		IF ~error THEN block := firstBlock;
			WHILE block # firstLinkedBlock DO
				used := (useAll OR (GetPriority (block) <= InitCode) OR (linkRoot # "") & Strings.StartsWith(linkRoot,0,block.identifier.name));
				COPY(block.identifier.name, name);
				IF stripInitCodes & (block.type = ObjectFile.InitCode) THEN used := FALSE END;
				Reference (block, used); block := block.next;
			END;
		END;
	END Resolve;

	PROCEDURE Link*;
	VAR block: Block;
	BEGIN
		Resolve;
		IF ~error THEN block := firstBlock; WHILE block # firstLinkedBlock DO IF block.used THEN Prearrange (block); END; block := block.next; END; END;
		IF ~error THEN block := firstBlock; WHILE block # firstLinkedBlock DO IF block.used THEN Arrange (block); END; block := block.next; END; END;
		IF ~error THEN block := firstBlock; WHILE block # firstLinkedBlock DO IF block.used THEN Patch (block); END; block := block.next; END; END;
		IF ~error THEN firstLinkedBlock := firstBlock; END;
		IF ~error & verbose THEN block := firstBlock; WHILE block # NIL DO Diagnose (block); block := block.next; END; END;
	END Link;

	PROCEDURE Reference (block: Block; used: BOOLEAN);
	VAR i: LONGINT;

		PROCEDURE ReferenceFixup (CONST fixup: ObjectFile.Fixup);
		VAR reference: Block;
		BEGIN
			reference := FindBlock (fixup.identifier);
			IF reference = NIL THEN reference := ImportBlock(fixup.identifier) END;

			IF reference = NIL THEN Error (fixup.identifier.name, "unresolved");
			ELSIF (reference.identifier.fingerprint # 0) & (block.fixup[i].identifier.fingerprint # 0) & (reference.identifier.fingerprint # block.fixup[i].identifier.fingerprint) THEN Error (fixup.identifier.name, "incompatible");
			ELSE Reference (reference, block.used); END;
		END ReferenceFixup;

	BEGIN
		IF used & ~block.used THEN block.used := TRUE;
		ELSIF block.referenced THEN RETURN; END; block.referenced := TRUE;
		IF ~used THEN RETURN END;
		FOR i := 0 TO block.fixups - 1 DO ReferenceFixup (block.fixup[i]); END;
	END Reference;

	PROCEDURE Prearrange (block: Block);
	VAR arrangement: Arrangement;
	BEGIN
		ASSERT (block.used);
		arrangement := GetArrangement (block);
		arrangement.Preallocate (block^);
	END Prearrange;

	PROCEDURE Arrange (block: Block);
	VAR arrangement: Arrangement;
	BEGIN
		ASSERT (block.used);
		arrangement := GetArrangement (block);
		block.address := arrangement.Allocate (block^);
		IF block.address = InvalidAddress THEN Error (block.identifier.name, "failed to allocate"); RETURN; END;
		IF block.fixed THEN ASSERT (block.address = block.alignment);
		ELSE ASSERT ((block.alignment = 0) OR (block.address MOD block.alignment = 0)); END;
	END Arrange;

	PROCEDURE Patch (block: Block);
	VAR arrangement: Arrangement; i: LONGINT;

		PROCEDURE PatchFixup (CONST fixup: ObjectFile.Fixup);
		VAR reference: Block; target, address: Address; i: LONGINT;

			PROCEDURE PatchPattern (CONST pattern: ObjectFile.FixupPattern);
			BEGIN arrangement.Patch (target, address, pattern.offset, pattern.bits, block.unit); address := ASH (address, -pattern.bits);
			END PatchPattern;

			PROCEDURE CheckBits(value: LONGINT; CONST patch: ObjectFile.Patch; offset: LONGINT);
			VAR i, nobits,remainder: LONGINT; minval, maxval: ObjectFile.Unit; name: ObjectFile.SectionName; number: ARRAY 32 OF CHAR;
			BEGIN
				nobits := 0;
				FOR i := 0 TO patch.patterns-1 DO
					INC(nobits,patch.pattern[i].bits);
				END;

				remainder := ASH(address,-nobits);

				IF  (nobits <32) & ((remainder > 0) OR (remainder < -1)) THEN
					IF patch.mode = ObjectFile.Relative THEN (* negative values allowed *)
						maxval := ASH(1,nobits-1)-1; minval := -maxval-1
					ELSE
						minval := 0; maxval := ASH(1,nobits);
					END;
					COPY(block.identifier.name,name);
					Strings.Append(name,":");
					Strings.IntToStr(offset,number);
					Strings.Append(name,number);
					Error(name,"fixup out of range");
				END;
			END CheckBits;

			PROCEDURE ApplyPatch(CONST patch: ObjectFile.Patch);
			VAR i,j: LONGINT;
			BEGIN
				FOR i := 0 TO patch.offsets-1 DO
					target := block.address + patch.offset[i];
					address := reference.address + patch.displacement;
					IF patch.mode = ObjectFile.Relative THEN
						DEC(address,target)
					END;
					address := ASH (address, patch.scale);
					CheckBits(address, patch, patch.offset[i]);
					FOR j := 0 TO patch.patterns-1 DO PatchPattern(patch.pattern[j]) END;
				END;
			END ApplyPatch;

		BEGIN
			reference := FindBlock (fixup.identifier);
			IF reference = NIL THEN reference := ImportBlock(fixup.identifier) END;
			ASSERT (reference # NIL);
			FOR i := 0 TO fixup.patches-1 DO
				ApplyPatch(fixup.patch[i]);
			END;
		END PatchFixup;

	BEGIN
		ASSERT (block.used);
		arrangement := GetArrangement (block);
		FOR i := 0 TO block.fixups - 1 DO PatchFixup (block.fixup[i]); END;
	END Patch;

	PROCEDURE Diagnose (block: Block);
	VAR msg,num: ARRAY 128 OF CHAR;
	BEGIN
		IF block.used THEN
			Strings.IntToHexStr(block.address, 8, num);
			msg := "arranged at ";
			Strings.Append(msg, num);
			IF block.bits # NIL THEN
				Strings.Append(msg, " to ");
				Strings.IntToHexStr(block.address+block.bits.GetSize() DIV block.unit, 8, num);
				Strings.Append(msg,num);
			END;
			Information (block.identifier.name, msg);
		ELSE Information (block.identifier.name, "unused"); END;
	END Diagnose;

END Linker;

PROCEDURE GetPriority (block: Block): Priority;
BEGIN
	IF block.fixed THEN RETURN Fixed END;
	IF block.type = ObjectFile.InitCode THEN RETURN InitCode END;
	IF block.type = ObjectFile.InitCode2 THEN RETURN InitCode2 END;
	IF block.type = ObjectFile.BodyCode THEN RETURN BodyCode END;
	IF block.bits.GetSize () = 0 THEN RETURN Empty END;
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
