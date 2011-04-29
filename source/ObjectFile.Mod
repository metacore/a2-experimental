MODULE ObjectFile;	(* AUTHOR "negelef"; PURPOSE "Generic Object File Representation"; *)

IMPORT Streams, BitSets, StringPool;

CONST
	(* Fixup modes *)
	Absolute* = 0;
	Relative* = 1;

	(* Section types *)
	Code* = 0;
	InitCode* = 1;
	InitCode2*= 2;
	BodyCode* = 3;
	Data* = 4;
	Const* = 5;

	Aligned=0;
	Fixed=1;

	DefaultExtension* = ".Gof";

TYPE
	Unit* = LONGINT;
	Bits* = LONGINT;

	SectionType = INTEGER;

	PooledName*= ARRAY 4 OF StringPool.Index;
	SectionName* = ARRAY 128 OF CHAR;

	(* FixupPattern = size (+|-) bits {size (+|-) bits}

		Example:
		fixupPattern = 0+8 -128+4 8-8 means
			store first 8 bits to offset 0
			leave out next 4 bits
			store next 8 bits to offset 8 in reverse order

		most frequently used are
			fixupPattern=0+8 : 8 bit fixup
			fixupPattern=0+16: 16 bit fixup
			fixupPattern=0+32: 32 bit fixup
	*)
	FixupPattern* = RECORD
		offset*, bits*: Bits;
	END;
	FixupPatterns*= POINTER TO ARRAY OF FixupPattern;

	Identifier*= RECORD
		name*: PooledName;
		fingerprint*: LONGINT;
	END;

	Offsets*= POINTER TO ARRAY OF Unit;

	Patch*= RECORD
		mode-: INTEGER; (* fixup mode: relative or absolute *)
		displacement-: Unit; (* displacement of the fixup ('source') *)
		scale-: Bits; (* exponent of scale factor (factor=2^scale) *)
		offsets-: LONGINT;
		offset-: Offsets;
		patterns-: LONGINT;
		pattern-: FixupPatterns; (* patterns describing the fixup format, cf. above *)
	END;
	Patches*= POINTER TO ARRAY OF Patch;

	Fixup* = RECORD
		identifier*: Identifier;
		patches-: LONGINT;
		patch-: Patches;
		filler1*: ARRAY 32 OF LONGINT; (* necessary for paco to work correctly. No idea why. *)
	END;

	Fixups*=POINTER TO ARRAY OF Fixup;

	Section* = RECORD
		type*: SectionType;
		identifier*: Identifier;
		unit*: Bits;
		fixed*: BOOLEAN;
		alignment*: Unit;
		fixups-: LONGINT;
		fixup-: Fixups;
		bits*: BitSets.BitSet;
	END;

	PoolMapItem= RECORD key, value: LONGINT END;
	PoolMapArray*=POINTER TO ARRAY OF PoolMapItem;

	PoolMap*=OBJECT
	VAR
		table: PoolMapArray;
		size: LONGINT;
		used-: LONGINT;
		maxLoadFactor: REAL;
		(* Interface *)

		PROCEDURE & Init* (initialSize: LONGINT);
		BEGIN
			ASSERT(initialSize > 2);
			NEW(table, initialSize);
			size := initialSize;
			used := 0;
			maxLoadFactor := 0.75;
			Clear;
		END Init;

		PROCEDURE Put*(key, value: LONGINT);
		VAR hash: LONGINT;
		BEGIN
			ASSERT(used < size);
			ASSERT(key >= 0);
			hash := HashValue(key);
			IF table[hash].key <0  THEN
				INC(used, 1);
			ELSE
				ASSERT(table[hash].key = key);
			END;
			table[hash].key := key;
			table[hash].value := value;

			IF (used / size) > maxLoadFactor THEN Grow END;
		END Put;

		PROCEDURE Get*(key: LONGINT):LONGINT;
		BEGIN
			IF key = -1 THEN
				RETURN -1
			ELSE
				RETURN table[HashValue(key)].value;
			END
		END Get;

		PROCEDURE Has*(key: LONGINT):BOOLEAN;
		BEGIN
			RETURN table[HashValue(key)].key = key;
		END Has;

		PROCEDURE Clear*;
		VAR i: LONGINT;
		BEGIN FOR i := 0 TO size - 1 DO table[i].key := -1; END; END Clear;

		(* Internals *)

		(* only correctly working, if NIL key cannot be entered *)
		PROCEDURE HashValue(key: LONGINT):LONGINT;
		VAR value, h, i: LONGINT;
		BEGIN
			value := key;
			i := 0;
			h := value MOD size;
			REPEAT
				value := (h + i) MOD size;
				INC(i);
			UNTIL((table[value].key  < 0) OR (table[value].key = key) OR (i > size));
			ASSERT((table[value].key <0)  OR (table[value].key = key));
			RETURN value;
		END HashValue;

		PROCEDURE Grow;
		VAR oldTable: PoolMapArray; oldSize, i: LONGINT; key: LONGINT;
		BEGIN
			oldSize := size;
			oldTable := table;
			Init(size*2);
			FOR i := 0 TO oldSize-1 DO
				key := oldTable[i].key;
				IF key >=0 THEN
					Put(key, oldTable[i].value);
				END;
			END;
		END Grow;

	END PoolMap;

VAR
	types: ARRAY 6 OF ARRAY 10 OF CHAR;
	modes: ARRAY 2 OF ARRAY 4 OF CHAR;
	relocatabilities: ARRAY 2 OF ARRAY 8 OF CHAR;


	PROCEDURE IsCode* (type: SectionType): BOOLEAN;
	BEGIN RETURN (type >= Code) & (type <=  BodyCode);
	END IsCode;

	PROCEDURE Matches*(CONST this, that: Identifier): BOOLEAN;
	BEGIN
		IF (this.fingerprint # 0) & (this.fingerprint = that.fingerprint) THEN RETURN TRUE
		ELSE RETURN (this.name = that.name)
		END;
	END Matches;

	PROCEDURE CopyPatch*(CONST source: Patch; VAR dest: Patch);
	VAR i: LONGINT;
		BEGIN
		dest.mode := source.mode;
		dest.displacement := source.displacement;
		dest.scale := source.scale;
		dest.patterns := source.patterns;
		dest.offsets := source.offsets;

		NEW(dest.offset, dest.offsets);
		FOR i := 0 TO source.offsets-1 DO
			dest.offset[i] := source.offset[i]
		END;

		NEW(dest.pattern, dest.patterns);
		FOR i := 0 TO source.patterns-1 DO
			dest.pattern[i] := source.pattern[i]
		END;
	END CopyPatch;

	PROCEDURE CopyFixup*(CONST source: Fixup; VAR dest: Fixup);
	VAR i: LONGINT;
	BEGIN
		dest.identifier.name := source.identifier.name;
		(*
		COPY(source.identifier.name, dest.identifier.name);
		*)
		dest.identifier.fingerprint := source.identifier.fingerprint;
		dest.patches := source.patches;
		NEW(dest.patch, dest.patches);
		FOR i := 0 TO source.patches-1 DO
			CopyPatch(source.patch[i], dest.patch[i]);
		END;
	END CopyFixup;

	PROCEDURE CopySection* (CONST source: Section; VAR dest: Section);
	VAR i: LONGINT;
	BEGIN
		dest.type := source.type;
		dest.identifier := source.identifier;
		dest.unit := source.unit;
		dest.fixed := source.fixed;
		dest.alignment := source.alignment;
		dest.fixups:= source.fixups;
		NEW (dest.fixup, dest.fixups);
		FOR i := 0 TO dest.fixups - 1 DO
			CopyFixup(source.fixup[i], dest.fixup[i]);
		END;
		NEW (dest.bits, source.bits.GetSize ());
		BitSets.CopyBits (source.bits, 0, dest.bits, 0, source.bits.GetSize ());
	END CopySection;

	PROCEDURE NibbleToCharacter* (value: LONGINT): CHAR;
	BEGIN
		IF value >= 10 THEN
			RETURN CHR ((ORD ('A') - 10) + value);
		ELSE
			RETURN CHR (ORD ('0') + value);
		END;
	END NibbleToCharacter;

	PROCEDURE CharacterToNibble* (char: CHAR): LONGINT;
	BEGIN
		IF ORD (char) >= ORD ('A') THEN
			RETURN ORD (char) - (ORD ('A') - 10);
		ELSE
			RETURN ORD (char) - ORD ('0');
		END;
	END CharacterToNibble;

	PROCEDURE WriteSectionTextual (writer: Streams.Writer; CONST section: Section);
	CONST Separator = ' '; Tab = 09X;
	VAR i: LONGINT; size: Bits; bits: LONGINT;

		PROCEDURE WriteValueIdentifier (value: INTEGER; CONST identifiers: ARRAY OF ARRAY OF CHAR);
		BEGIN
			writer.String (identifiers[value]);
		END WriteValueIdentifier;

		PROCEDURE WritePattern (CONST pattern: FixupPattern);
		BEGIN
			writer.Int (pattern.offset, 0);
			writer.Char (Separator);
			writer.Int (pattern.bits, 0);
			writer.Char (Separator);
		END WritePattern;

		PROCEDURE WriteIdentifier(CONST identifier: Identifier);
		VAR name: SectionName;
		BEGIN
			FromPooledName(identifier.name, name);
			writer.String (name);
			writer.Char (Separator);
			writer.Int (identifier.fingerprint, 0);
		END WriteIdentifier;

		PROCEDURE WritePatch(CONST patch: Patch);
		VAR i: LONGINT;
		BEGIN
			WriteValueIdentifier (patch.mode, modes);
			writer.Char (Separator);
			writer.Int (patch.displacement, 0);
			writer.Char (Separator);
			writer.Int (patch.scale, 0);
			writer.Char (Separator);
			writer.Int (patch.patterns, 0);
			writer.Char (Separator);
			FOR i := 0 TO patch.patterns - 1 DO
				WritePattern (patch.pattern[i]);
			END;
			writer.Int (patch.offsets, 0);
			writer.Char (Separator);
			FOR i := 0 TO patch.offsets - 1 DO
				writer.Int (patch.offset[i], 0);
				writer.Char (Separator);
			END;
		END WritePatch;

		PROCEDURE WriteFixup (CONST fixup: Fixup);
		VAR i: LONGINT;
		BEGIN
			WriteIdentifier(fixup.identifier);
			writer.Char (Separator);
			writer.Int(fixup.patches,1);
			writer.Char(Separator);
			FOR i := 0 TO fixup.patches-1 DO
				WritePatch(fixup.patch[i]);
			END;
		END WriteFixup;

	BEGIN
		IF section.type > Const THEN RETURN END; (* ignore exotic sections *)
		WriteValueIdentifier (section.type, types);
		writer.Char (Separator);
		WriteIdentifier(section.identifier);
		writer.Char (Separator);
		writer.Int (section.unit, 0);
		writer.Char (Separator);
		IF section.fixed THEN WriteValueIdentifier(Fixed,relocatabilities) ELSE WriteValueIdentifier(Aligned,relocatabilities) END;
		writer.Char (Separator);
		writer.Int (section.alignment, 0);
		writer.Char (Separator);
		writer.Int (section.fixups, 0);
		writer.Char (Separator);
		size := section.bits.GetSize ();
		writer.Int (size DIV section.unit, 0);
		ASSERT(size MOD section.unit = 0);
		FOR i := 0 TO section.fixups - 1 DO
			writer.Ln; writer.Char (Tab); WriteFixup (section.fixup[i]);
		END;
		i := 0; bits := 0;
		WHILE (i < size) & (bits = 0) DO
			bits := section.bits.GetBits(i, MIN(4, size-i));
			INC(i,4);
		END;
		IF (bits = 0) & (size > 0) THEN
			writer.Ln; writer.Char(Tab); writer.Char('N')
		ELSE
			FOR i := 0 TO size - 1 BY 4 DO
				IF i MOD (32 * 8) = 0 THEN writer.Ln; writer.Char (Tab); END;
				writer.Char (NibbleToCharacter (section.bits.GetBits (i, MIN (4, size - i))));
			END;
		END;
		writer.Ln;
	END WriteSectionTextual;

	PROCEDURE ReadSectionTextual (reader: Streams.Reader; VAR section: Section);
	VAR i, size: LONGINT; char: CHAR; relocatibility: INTEGER;

		PROCEDURE ReadValueIdentifier (VAR value: INTEGER; CONST identifiers: ARRAY OF ARRAY OF CHAR);
		VAR identifier: ARRAY 10 OF CHAR;
		BEGIN
			value := 0;
			reader.SkipWhitespace; reader.String (identifier);
			WHILE (value # LEN (identifiers)) & (identifier # identifiers[value]) DO INC (value); END;
			IF value = LEN (identifiers) THEN reader.res := Streams.FormatError; END;
		END ReadValueIdentifier;

		PROCEDURE ReadPattern (VAR pattern: FixupPattern);
		BEGIN
			reader.SkipWhitespace; reader.Int (pattern.offset, FALSE);
			reader.SkipWhitespace; reader.Int (pattern.bits, FALSE);
		END ReadPattern;

		PROCEDURE ReadIdentifier(VAR identifier: Identifier);
		VAR name: SectionName;
		BEGIN
			reader.SkipWhitespace;
			reader.String(name);
			ToPooledName(name,identifier.name);
			reader.SkipWhitespace; reader.Int (identifier.fingerprint,FALSE);
		END ReadIdentifier;

		PROCEDURE ReadPatch(VAR patch: Patch);
		VAR i: LONGINT;
		BEGIN
			reader.SkipWhitespace;
			ReadValueIdentifier (patch.mode, modes);
			reader.SkipWhitespace; reader.Int (patch.displacement, FALSE);
			reader.SkipWhitespace; reader.Int (patch.scale, FALSE);
			reader.SkipWhitespace; reader.Int (patch.patterns, FALSE);

			IF (patch.pattern = NIL) OR (LEN (patch.pattern) < patch.patterns) THEN
				NEW (patch.pattern, patch.patterns);
			END;
			FOR i := 0 TO patch.patterns - 1 DO
				ReadPattern (patch.pattern[i]);
			END;
			reader.SkipWhitespace; reader.Int(patch.offsets, FALSE);
			IF (patch.offset = NIL) OR (LEN(patch.offset) < patch.offsets) THEN
				NEW(patch.offset, patch.offsets);
			END;
			FOR i := 0 TO patch.offsets-1 DO
				reader.SkipWhitespace; reader.Int (patch.offset[i], FALSE);
			END;
		END ReadPatch;

		PROCEDURE ReadFixup (VAR fixup: Fixup);
		VAR i: LONGINT;
		BEGIN
			reader.SkipWhitespace; ReadIdentifier (fixup.identifier);
			reader.SkipWhitespace; reader.Int (fixup.patches, FALSE);
			IF (fixup.patch = NIL) OR (LEN (fixup.patch) < fixup.patches) THEN
				NEW (fixup.patch, fixup.patches);
			END;
			FOR i := 0 TO fixup.patches - 1 DO
				ReadPatch (fixup.patch[i]);
			END;
		END ReadFixup;

	BEGIN
		ReadValueIdentifier (section.type, types);
		ReadIdentifier (section.identifier);
		reader.SkipWhitespace; reader.Int (section.unit, FALSE);
		ReadValueIdentifier(relocatibility, relocatabilities);
		section.fixed := relocatibility = Fixed;
		reader.SkipWhitespace; reader.Int (section.alignment, FALSE);
		reader.SkipWhitespace; reader.Int (section.fixups, FALSE);
		reader.SkipWhitespace; reader.Int (size, FALSE); size := size * section.unit;
		IF (section.fixup = NIL) OR (LEN (section.fixup) < section.fixups) THEN
			NEW (section.fixup, section.fixups);
		END;
		FOR i := 0 TO section.fixups - 1 DO
			ReadFixup (section.fixup[i]);
		END;
		IF section.bits # NIL THEN
			section.bits.Resize (size);
		ELSE
			NEW (section.bits, size);
		END;
		FOR i := 0 TO size - 1 BY 4 DO
			reader.SkipWhitespace; reader.Char (char);
			IF char = 'N' THEN
				ASSERT(i=0);
				section.bits.Zero;
			(* skip rest of section *) RETURN
			END;
			section.bits.SetBits (i, MIN (4, size - i), CharacterToNibble (char));
		END;
	END ReadSectionTextual;

	PROCEDURE WriteSectionBinary (writer: Streams.Writer; CONST section: Section; poolMap: PoolMap);
	VAR i: LONGINT; size: Bits; bits: LONGINT;

		PROCEDURE WriteValueIdentifier (value: INTEGER; CONST identifiers: ARRAY OF ARRAY OF CHAR);
		BEGIN
			writer.RawNum(value);
			(*
			writer.RawString (identifiers[value]);
			*)
		END WriteValueIdentifier;

		PROCEDURE WritePattern (CONST pattern: FixupPattern);
		BEGIN
			writer.RawNum (pattern.offset);
			writer.RawNum (pattern.bits);
		END WritePattern;

		PROCEDURE WriteIdentifier(CONST identifier: Identifier);
		(*VAR name: SectionName;*)
		VAR i,num: LONGINT;
		BEGIN
			i := 0;
			REPEAT
				num := poolMap.Get(identifier.name[i])+1;
				writer.RawNum(num); (* avoid to write -1 *)
				INC(i);
			UNTIL (i = LEN(identifier.name)) OR (num = 0);
			writer.RawNum (identifier.fingerprint);
		END WriteIdentifier;

		PROCEDURE WritePatch(CONST patch: Patch);
		VAR i: LONGINT;
		BEGIN
			WriteValueIdentifier (patch.mode, modes);
			writer.RawNum (patch.displacement);
			writer.RawNum (patch.scale);
			writer.RawNum (patch.patterns);
			FOR i := 0 TO patch.patterns - 1 DO
				WritePattern (patch.pattern[i]);
			END;
			writer.RawNum (patch.offsets);
			FOR i := 0 TO patch.offsets - 1 DO
				writer.RawNum (patch.offset[i]);
			END;
		END WritePatch;

		PROCEDURE WriteFixup (CONST fixup: Fixup);
		VAR i: LONGINT;
		BEGIN
			WriteIdentifier(fixup.identifier);
			writer.RawNum(fixup.patches);
			FOR i := 0 TO fixup.patches-1 DO
				WritePatch(fixup.patch[i]);
			END;
		END WriteFixup;

	BEGIN
		IF section.type > Const THEN RETURN END; (* ignore exotic sections *)
		writer.Char(1X);
		WriteValueIdentifier (section.type, types);
		WriteIdentifier(section.identifier);
		writer.RawNum (section.unit);
		IF section.fixed THEN WriteValueIdentifier(Fixed,relocatabilities) ELSE WriteValueIdentifier(Aligned,relocatabilities) END;
		writer.RawNum (section.alignment);
		writer.RawNum (section.fixups);
		size := section.bits.GetSize ();
		writer.RawNum (size DIV section.unit);
		ASSERT(size MOD section.unit = 0);
		FOR i := 0 TO section.fixups - 1 DO
			WriteFixup (section.fixup[i]);
		END;
		i := 0; bits := 0;
		WHILE (i < size) & (bits = 0) DO
			bits := section.bits.GetBits(i, MIN(32, size-i));
			INC(i,32);
		END;
		IF (bits = 0) & (size > 0) THEN
			writer.Char('Z');
		ELSE
			writer.Char('N');
			FOR i := 0 TO size - 1 BY 32 DO
				writer.RawNum (section.bits.GetBits (i, MIN (32, size - i)));
			END;
		END;
		writer.Ln;
	END WriteSectionBinary;

	PROCEDURE ReadSectionBinary (reader: Streams.Reader; VAR section: Section; poolMap: PoolMap);
	VAR i, size: LONGINT; char: CHAR; relocatibility: INTEGER; num: LONGINT; ch: CHAR;

		PROCEDURE ReadValueIdentifier (VAR value: INTEGER; CONST identifiers: ARRAY OF ARRAY OF CHAR);
		(* VAR identifier: ARRAY 10 OF CHAR; *)
		VAR num: LONGINT;
		BEGIN
			reader.RawNum(num);
			value := SHORT(num);
			(*
			value := 0;
			reader.RawString (identifier);
			WHILE (value # LEN (identifiers)) & (identifier # identifiers[value]) DO INC (value); END;
			IF value = LEN (identifiers) THEN reader.res := Streams.FormatError; END;
			*)
		END ReadValueIdentifier;

		PROCEDURE ReadPattern (VAR pattern: FixupPattern);
		BEGIN
			reader.RawNum (pattern.offset);
			reader.RawNum (pattern.bits);
		END ReadPattern;

		PROCEDURE ReadIdentifier(VAR identifier: Identifier);
		(*VAR name: SectionName;*)
		VAR i,num: LONGINT;
		BEGIN
			i := 0;
			REPEAT
				reader.RawNum(num);
				identifier.name[i] := poolMap.Get(num-1);
				INC(i);
			UNTIL (i = LEN(identifier.name)) OR (num = 0);
			WHILE i < LEN(identifier.name) DO
				identifier.name[i] := -1; INC(i);
			END;
			 reader.RawNum (identifier.fingerprint);
		END ReadIdentifier;

		PROCEDURE ReadPatch(VAR patch: Patch);
		VAR i: LONGINT;
		BEGIN
			ReadValueIdentifier (patch.mode, modes);
			reader.RawNum (patch.displacement);
			reader.RawNum (patch.scale);
			reader.RawNum (patch.patterns);

			IF (patch.pattern = NIL) OR (LEN (patch.pattern) < patch.patterns) THEN
				NEW (patch.pattern, patch.patterns);
			END;
			FOR i := 0 TO patch.patterns - 1 DO
				ReadPattern (patch.pattern[i]);
			END;
			reader.RawNum(patch.offsets);
			IF (patch.offset = NIL) OR (LEN(patch.offset) < patch.offsets) THEN
				NEW(patch.offset, patch.offsets);
			END;
			FOR i := 0 TO patch.offsets-1 DO
				 reader.RawNum (patch.offset[i]);
			END;
		END ReadPatch;

		PROCEDURE ReadFixup (VAR fixup: Fixup);
		VAR i: LONGINT;
		BEGIN
			ReadIdentifier (fixup.identifier);
			reader.RawNum (fixup.patches);
			IF (fixup.patch = NIL) OR (LEN (fixup.patch) < fixup.patches) THEN
				NEW (fixup.patch, fixup.patches);
			END;
			FOR i := 0 TO fixup.patches - 1 DO
				ReadPatch (fixup.patch[i]);
			END;
		END ReadFixup;

	BEGIN
		reader.Char(ch); ASSERT(ch = 1X);
		ReadValueIdentifier (section.type, types);
		ReadIdentifier (section.identifier);
		reader.RawNum (section.unit);
		ReadValueIdentifier(relocatibility, relocatabilities);
		section.fixed := relocatibility = Fixed;
		reader.RawNum (section.alignment);
		reader.RawNum (section.fixups);
		reader.RawNum (size); size := size * section.unit;
		IF (section.fixup = NIL) OR (LEN (section.fixup) < section.fixups) THEN
			NEW (section.fixup, section.fixups);
		END;
		FOR i := 0 TO section.fixups - 1 DO
			ReadFixup (section.fixup[i]);
		END;
		IF section.bits # NIL THEN
			section.bits.Resize (size);
		ELSE
			NEW (section.bits, size);
		END;
		reader.Char (char);
		IF char = 'Z' THEN section.bits.Zero
		ELSE
			ASSERT(char ='N');
			FOR i := 0 TO size - 1 BY 32 DO
				reader.RawNum (num);
				section.bits.SetBits (i, MIN (32, size - i), num);
			END;
		END;
	END ReadSectionBinary;

	PROCEDURE ReadSection*(reader: Streams.Reader; VAR section: Section; binary: BOOLEAN; poolMap: PoolMap);
	BEGIN
		IF binary THEN
			ReadSectionBinary(reader,section,poolMap)
		ELSE
			ReadSectionTextual(reader,section);
		END
	END ReadSection;

	PROCEDURE WriteSection*(writer: Streams.Writer; CONST section: Section; binary: BOOLEAN; poolMap: PoolMap);
	BEGIN
		IF binary THEN
			WriteSectionBinary(writer,section, poolMap)
		ELSE
			WriteSectionTextual(writer,section)
		END
	END WriteSection;

	PROCEDURE SetFixups*(VAR section: Section; fixups: LONGINT; fixup: Fixups);
	BEGIN
		section.fixups := fixups;
		section.fixup := fixup;
	END SetFixups;

	PROCEDURE AddOffset(VAR offsets: LONGINT; VAR offset: Offsets; ofs: LONGINT);
	VAR newOffset: Offsets; newOffsets:LONGINT; i: LONGINT;
	BEGIN
		FOR i := 0 TO offsets-1 DO
			ASSERT(offset[i] # ofs);
		END;
		newOffsets := offsets+1;
		IF (offset = NIL) OR (LEN(offset) < newOffsets) THEN
			NEW(newOffset, 2*newOffsets);
			FOR i := 0 TO offsets-1 DO
				newOffset[i] := offset[i];
			END;
			offset := newOffset;
		END;
		offset[offsets] := ofs;
		offsets := newOffsets;
	END AddOffset;


	PROCEDURE SamePattern(patterns: LONGINT; left, right: FixupPatterns): BOOLEAN;
	VAR i: LONGINT;
	BEGIN
		FOR i := 0 TO patterns-1 DO
			IF (left[i].offset # right[i].offset) OR (left[i].bits # right[i].bits) THEN RETURN FALSE END;
		END;
		RETURN TRUE
	END SamePattern;


	PROCEDURE AddPatch(VAR patches: LONGINT; VAR patch: Patches; mode: INTEGER; displacement, scale: LONGINT; patterns: LONGINT; pattern: FixupPatterns; offset: LONGINT);
	VAR i: LONGINT; newPatches: LONGINT; newPatch: Patches; len: LONGINT;
	BEGIN
		FOR i := 0 TO patches-1 DO
			len := LEN(patch);
			ASSERT(patch # NIL,101);
			ASSERT(LEN(patch) > i,102);
			IF (patch[i].mode = mode) & (patch[i].displacement = displacement) & (patch[i].scale = scale) &  (patch[i].patterns = patterns) & SamePattern(patterns, patch[i].pattern, pattern) THEN
				AddOffset(patch[i].offsets, patch[i].offset, offset);
				RETURN
			END;
		END;
		newPatches := patches+1;
		IF (patch = NIL) OR (LEN(patch) < newPatches) THEN
			ASSERT(newPatches > 0);
			NEW(newPatch, 2*newPatches);
			FOR i := 0 TO patches-1 DO
				newPatch[i] := patch[i];
				(*
				CopyPatch(patch[i], newPatch[i]);
				*)
			END;
			patch := newPatch;
		END;
		ASSERT(LEN(patch) > patches);
		patch[patches].mode := mode;
		patch[patches].displacement := displacement;
		patch[patches].patterns := patterns;
		patch[patches].pattern := pattern;
		patch[patches].offsets := 0;
		patch[patches].offset := NIL;
		AddOffset(patch[patches].offsets, patch[patches].offset, offset);
		patches := newPatches;
		(* increase size and add *)
	END AddPatch;


	PROCEDURE AddFixup*(VAR fixups: LONGINT; VAR fixup: Fixups; CONST name: PooledName; fingerprint: LONGINT; mode: INTEGER; displacement, scale: LONGINT; patterns: LONGINT; pattern: FixupPatterns; offset: LONGINT);
	VAR i: LONGINT; newFixups: LONGINT; newFixup: Fixups;
	BEGIN
		FOR i := 0 TO fixups-1 DO
			IF (fixup[i].identifier.fingerprint = fingerprint) & (name =fixup[i].identifier.name) THEN
				AddPatch(fixup[i].patches, fixup[i].patch, mode, displacement, scale, patterns, pattern, offset);
				RETURN
			END;
		END;
		newFixups := fixups+1;
		IF (fixup = NIL) OR (LEN(fixup) < newFixups) THEN
			NEW(newFixup, MAX(2*newFixups,32));
			FOR i := 0 TO fixups-1 DO
				newFixup[i] := fixup[i];
				(*CopyFixup(fixup[i], newFixup[i]);*)
			END;
			fixup := newFixup;
		END;
		fixup[fixups].identifier.name := name;
		(*
		COPY(name, fixup[fixups].identifier.name);
		*)
		fixup[fixups].identifier.fingerprint := fingerprint;
		fixup[fixups].patches := 0;
		fixup[fixups].patch := NIL;
		AddPatch(fixup[fixups].patches, fixup[fixups].patch, mode, displacement, scale, patterns, pattern, offset);
		fixups := newFixups;
		(* increase size and add *)
	END AddFixup;

	PROCEDURE ToPooledName*(CONST name: ARRAY OF CHAR; VAR pooledName: PooledName);
	VAR i,j,index: LONGINT; n: SectionName;
	BEGIN
		(* convert a string of the form A.B.C.suffix to [S(A), S(B), S(C), S(suffix)] *)
		index := 0; i := 0;
		WHILE (index < LEN(pooledName)) DO
			j := 0;
			WHILE (name[i] # 0X) & (name[i] # ".") DO
				n[j] := name[i]; INC(i); INC(j);
			END;
			IF j > 0 THEN
				IF index = LEN(pooledName)-1 THEN
					WHILE (name[i] # 0X)  DO n[j] := name[i]; INC(i); INC(j); END;
				END;
				n[j] := 0X; StringPool.GetIndex(n,pooledName[index]);
			ELSE
				pooledName[index] := -1
			END;
			IF name[i] = "." THEN INC(i) END;
			INC(index);
		END;
	END ToPooledName;

	PROCEDURE FromPooledName*(CONST pooledName: PooledName; VAR name: ARRAY OF CHAR);
	VAR i,j, index: LONGINT; n: SectionName;
	BEGIN
		i := 0; index := 0;
		WHILE (index < LEN(pooledName)) DO
			IF pooledName[index] >= 0 THEN
				IF index > 0 THEN name[i] := "."; INC(i) END;
				StringPool.GetString(pooledName[index],n);
				j := 0;
				WHILE n[j] # 0X DO
					name[i] := n[j]; INC(i); INC(j);
				END;
			END;
			INC(index);
		END;
		name[i] := 0X;
	END FromPooledName;

	OPERATOR "="*(CONST l,r: PooledName): BOOLEAN;
	BEGIN
		RETURN (l[0]=r[0]) & (l[1]=r[1]) & (l[2]=r[2]) & (l[3]=r[3])
	END "=";

	OPERATOR "#"*(CONST l,r: PooledName): BOOLEAN;
	BEGIN
		RETURN (l[0]#r[0]) OR (l[1]#r[1]) OR (l[2]#r[2]) OR (l[3]#r[3])
	END "#";

BEGIN
	types[Code] := "code";
	types[InitCode] := "initcode";
	types[InitCode2] := "initcode2";
	types[BodyCode] := "bodycode";
	types[Data] := "data";
	types[Const] := "const";
	modes[Absolute] := "abs";
	modes[Relative] := "rel";
	relocatabilities[Fixed] := "fixed";
	relocatabilities[Aligned] := "aligned";
END ObjectFile.


ObjectFile.Test
