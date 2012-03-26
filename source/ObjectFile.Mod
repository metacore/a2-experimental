MODULE ObjectFile;	(* AUTHOR "negelef"; PURPOSE "Generic Object File Representation"; *)

IMPORT Streams, BitSets, StringPool;

CONST
	(* Fixup modes *)
	Absolute* = 0;
	Relative* = 1;


	(* Section categories *)
	(* code section categories, ordered by decreasing linking preference *)
	InitCode*=0; (* initcode sections provide the entry point for static linking. A static linker includes this sections, a dynamic linker wants to omit them *)
	BodyCode*=1; (* body code sections provide the entry point for dynamic linking. A dynamic linker needs to be able to distinguish them from normal code *)
	Code*=2; (* normal executable code *)
	(* data section categories *)
	Data* = 3; (* data sections provide space for (global) variables *)
	Const* = 4; (* const sections are data sections that are immutable *)

	(* alignment types *)
	Aligned=0;
	Fixed=1;

	DefaultExtension* = ".Gof";

	SegmentedNameLength=8;
TYPE

	Unit* = LONGINT;
	Bits* = LONGINT;

	SectionType = INTEGER;

	SegmentedName*= RECORD
		(*
			0X terminated string representation in the form
				{index char}.
			Empty string is represented as 0 0X.
			Implementers must guarantee that last separator is 0X.
		*)
		index*: ARRAY SegmentedNameLength OF StringPool.Index;
		sep*: ARRAY SegmentedNameLength OF CHAR;
	END;

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
		name*: SegmentedName;
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
		priority*: LONGINT;
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
	categories: ARRAY 6 OF ARRAY 10 OF CHAR;
	modes: ARRAY 2 OF ARRAY 4 OF CHAR;
	relocatabilities: ARRAY 2 OF ARRAY 8 OF CHAR;


	PROCEDURE IsCode* (type: SectionType): BOOLEAN;
	BEGIN RETURN (type IN {InitCode, BodyCode, Code})
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
		dest.priority := source.priority;
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
	VAR i,offset,start, len: LONGINT; size: Bits; bits: LONGINT;

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
			SegmentedNameToString(identifier.name, name);
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

		PROCEDURE Zeros(offset: LONGINT): LONGINT;
		VAR zeros: LONGINT;
		BEGIN
			zeros := 0;
			WHILE (offset < size) & (section.bits.GetBits(offset, MIN(4, size-offset)) = 0) DO
				INC(zeros);
				INC(offset,4);
			END;
			RETURN zeros
		END Zeros;

		PROCEDURE GetSegment(VAR offset, start, len: LONGINT): BOOLEAN;
		VAR zeros: LONGINT;
		BEGIN
			INC(offset, Zeros(offset)*4);
			start := offset;
			len := 0;
			WHILE (offset < size) DO
				zeros := Zeros(offset);
				INC(offset, zeros*4);
				IF (zeros > 8) OR (offset >= size) THEN
					RETURN TRUE;
				ELSE
					INC(len, zeros*4);
					INC(len, 4); INC(offset,4); (* non-zero element *)
				END;
			END;
			RETURN len > 0;
		END GetSegment;

		PROCEDURE WriteSegment(offset,len: LONGINT); (* offset in bits *)
		VAR bits: LONGINT; first: BOOLEAN;
		BEGIN
			writer.Int(len,1); writer.Char(Separator); writer.Int(offset,1); writer.Char(Separator);
			WHILE len > 0 DO
				bits := section.bits.GetBits(offset, MIN(4, size-offset));
				writer.Char(NibbleToCharacter(bits));
				INC(offset, 4);
				DEC(len, 4);
			END;
			writer.Ln;
		END WriteSegment;

	BEGIN
		IF section.type > Const THEN RETURN END; (* ignore exotic sections *)
		WriteValueIdentifier (section.type, categories);
		writer.Char (Separator);
		WriteIdentifier(section.identifier);
		writer.Char (Separator);
		writer.Int (section.unit, 0);
		writer.Char (Separator);
		IF section.fixed THEN WriteValueIdentifier(Fixed,relocatabilities) ELSE WriteValueIdentifier(Aligned,relocatabilities) END;
		writer.Char (Separator);
		writer.Int (section.alignment, 0);
		writer.Char (Separator);
		writer.Int(section.priority, 0);
		writer.Char (Separator);
		writer.Int (section.fixups, 0);
		writer.Char (Separator);
		size := section.bits.GetSize ();
		writer.Int (size DIV section.unit, 1);
		ASSERT(size MOD section.unit = 0);
		FOR i := 0 TO section.fixups - 1 DO
			writer.Ln; writer.Char (Tab); WriteFixup (section.fixup[i]);
		END;
		writer.Ln;
		offset := 0;
		WHILE GetSegment(offset, start, len) DO
			WriteSegment(start, len)
		END;
		writer.Int(0,1); writer.Ln;
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
			StringToSegmentedName(name,".",identifier.name);
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

		PROCEDURE ReadSegment(): BOOLEAN;
		VAR len,offset: LONGINT;
		BEGIN
			reader.Int(len,FALSE);
			reader.SkipWhitespace;
			IF len = 0 THEN RETURN FALSE END;
			reader.Int(offset,FALSE);
			reader.SkipWhitespace;
			WHILE len > 0 DO
				reader.Char (char);
				section.bits.SetBits (offset, MIN (4, size - offset), CharacterToNibble (char));
				DEC(len, 4); INC(offset,4);
			END;
			RETURN TRUE
		END ReadSegment;


	BEGIN
		ReadValueIdentifier (section.type, categories);
		ReadIdentifier (section.identifier);
		reader.SkipWhitespace; reader.Int (section.unit, FALSE);
		ReadValueIdentifier(relocatibility, relocatabilities);
		section.fixed := relocatibility = Fixed;
		reader.SkipWhitespace; reader.Int (section.alignment, FALSE);
		reader.SkipWhitespace; reader.Int (section.priority, FALSE);
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
			section.bits.Zero();
		ELSE
			NEW (section.bits, size);
		END;
		REPEAT
			reader.SkipWhitespace()
		UNTIL ~ReadSegment()
	END ReadSectionTextual;

	PROCEDURE WriteSectionBinary (writer: Streams.Writer; CONST section: Section; poolMap: PoolMap);
	VAR i, offset, start, len: LONGINT; size: Bits; bits: LONGINT;

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
		VAR segment, index: LONGINT; sep: CHAR;
		BEGIN
			segment := 0;
			REPEAT
				index := poolMap.Get(identifier.name.index[segment]);
				sep := identifier.name.sep[segment];
				writer.RawNum(index);
				writer.Char(sep);
				INC(segment);
			UNTIL sep = 0X;
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

		PROCEDURE Zeros(offset: LONGINT): LONGINT;
		VAR zeros: LONGINT;
		BEGIN
			WHILE (offset < size) & (section.bits.GetBits(offset, MIN(32, size-offset)) = 0) DO
				INC(zeros);
				INC(offset,32);
			END;
			RETURN zeros
		END Zeros;

		PROCEDURE GetSegment(VAR offset, start, len: LONGINT): BOOLEAN;
		VAR zeros: LONGINT;
		BEGIN
			INC(offset, Zeros(offset)*32);
			start := offset;
			len := 0;
			WHILE (offset < size) DO
				zeros := Zeros(offset);
				INC(offset, zeros*32);
				IF (zeros > 8) OR (offset >= size) THEN
					RETURN TRUE;
				ELSE
					ASSERT(offset < size);
					INC(len, zeros*32);
					INC(len, 32); INC(offset,32); (* non-zero element *)
				END;
			END;
			RETURN len > 0;
		END GetSegment;

		PROCEDURE WriteSegment(offset,len: LONGINT); (* offset in bits *)
		VAR bits: LONGINT; first: BOOLEAN;
		BEGIN
			ASSERT(len > 0);
			writer.RawNum(len); writer.RawNum(offset);
			WHILE len > 0 DO
				bits := section.bits.GetBits(offset, MIN(32, size-offset));
				INC(offset, 32);
				DEC(len, 32);
				writer.RawLInt(bits);
			END;
		END WriteSegment;


	BEGIN
		IF section.type > Const THEN RETURN END; (* ignore exotic sections *)
		writer.Char(1X);
		WriteValueIdentifier (section.type, categories);
		WriteIdentifier(section.identifier);
		writer.RawNum (section.unit);
		IF section.fixed THEN WriteValueIdentifier(Fixed,relocatabilities) ELSE WriteValueIdentifier(Aligned,relocatabilities) END;
		writer.RawNum (section.alignment);
		writer.RawNum (section.priority);
		writer.RawNum (section.fixups);
		size := section.bits.GetSize ();
		writer.RawNum (size DIV section.unit);
		ASSERT(size MOD section.unit = 0);
		FOR i := 0 TO section.fixups - 1 DO
			WriteFixup (section.fixup[i]);
		END;
		offset := 0;
		WHILE GetSegment(offset, start, len) DO
			WriteSegment(start, len);
		END;
		writer.RawNum(0);
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
		VAR i,index: LONGINT; sep: CHAR;
		BEGIN
			i := 0;
			REPEAT
				reader.RawNum(index);
				reader.Char(sep);
				identifier.name.index[i] := poolMap.Get(index);
				identifier.name.sep[i] := sep;
				INC(i);
			UNTIL (sep = 0X);
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

		PROCEDURE ReadSegment(): BOOLEAN;
		VAR len,offset,bits: LONGINT;
		BEGIN
			reader.RawNum(len);
			IF len = 0 THEN RETURN FALSE END;
			reader.RawNum(offset);
			WHILE len > 0 DO
				reader.RawLInt (bits);
				section.bits.SetBits (offset, MIN (32, size - offset), bits);
				DEC(len, 32); INC(offset,32);
			END;
			RETURN TRUE
		END ReadSegment;

	BEGIN
		reader.Char(ch); ASSERT(ch = 1X);
		ReadValueIdentifier (section.type, categories);
		ReadIdentifier (section.identifier);
		reader.RawNum (section.unit);
		ReadValueIdentifier(relocatibility, relocatabilities);
		section.fixed := relocatibility = Fixed;
		reader.RawNum (section.alignment);
		reader.RawNum (section.priority);
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
			section.bits.Zero();
		ELSE
			NEW (section.bits, size);
		END;

		WHILE ReadSegment() DO
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

	PROCEDURE AddFixup*(VAR fixups: LONGINT; VAR fixup: Fixups; CONST name: SegmentedName; fingerprint: LONGINT; mode: INTEGER; displacement, scale: LONGINT; patterns: LONGINT; pattern: FixupPatterns; offset: LONGINT);
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
		fixup[fixups].identifier.fingerprint := fingerprint;
		fixup[fixups].patches := 0;
		fixup[fixups].patch := NIL;
		AddPatch(fixup[fixups].patches, fixup[fixups].patch, mode, displacement, scale, patterns, pattern, offset);
		fixups := newFixups;
		(* increase size and add *)
	END AddFixup;

	PROCEDURE StringToSegmentedName*(CONST name: ARRAY OF CHAR; sep: CHAR; VAR segmentedName: SegmentedName);
	VAR i,j,segment: LONGINT; n: SectionName;
	BEGIN
		(* convert a string of the form A.B.C.suffix to [S(A), S(B), S(C), S(suffix)] *)
		segment := 0; i := 0;
		REPEAT
			j := 0;
			IF segment = LEN(segmentedName.index)-1 THEN
				WHILE (name[i] # 0X)  DO n[j] := name[i]; INC(i); INC(j); END;
			ELSE
				WHILE (name[i] # 0X) & (name[i] # sep) DO n[j] := name[i]; INC(i); INC(j) END;
			END;
			n[j] := 0X;
			StringPool.GetIndex(n,segmentedName.index[segment]);
			segmentedName.sep[segment] := name[i];
			IF name[i] = sep THEN INC(i) END;
			INC(segment);
		UNTIL name[i] = 0X;
	END StringToSegmentedName;

	PROCEDURE SegmentedNameToString*(CONST segmentedName: SegmentedName; VAR name: ARRAY OF CHAR);
	VAR i,j, segment: LONGINT; n: SectionName; sep: CHAR;
	BEGIN
		ASSERT(LEN(name) > 0);
		i := 0; segment:= 0;
		REPEAT
			StringPool.GetString(segmentedName.index[segment], n);
			j := 0;
			WHILE (n[j] # 0X) & (i< LEN(name)-1) DO
				name[i] := n[j]; INC(i); INC(j);
			END;
			sep := segmentedName.sep[segment];
			name[i] := sep;
			INC(segment); INC(i);
		UNTIL sep = 0X;
	END SegmentedNameToString;

	OPERATOR "="*(CONST l,r: SegmentedName): BOOLEAN;
	VAR i: LONGINT;
	BEGIN
		i := 0;
		WHILE (l.sep[i] # 0X) & (r.sep[i] # 0X) DO
			IF (l.index[i] # r.index[i]) OR (l.sep[i] # r.sep[i]) THEN RETURN FALSE END;
			INC(i);
		END;
		RETURN (l.sep[i] = r.sep[i]) & (l.index[i] = r.index[i]);
	END "=";

	OPERATOR ":="*(VAR l: SegmentedName; CONST rs: ARRAY OF CHAR);
	VAR r: SegmentedName;
	BEGIN
		StringToSegmentedName(rs,".", l);
	END ":=";

	OPERATOR "="*(CONST l: SegmentedName; CONST rs: ARRAY OF CHAR): BOOLEAN;
	VAR r: SegmentedName;
	BEGIN
		StringToSegmentedName(rs, ".", r);
		RETURN l=r
	END "=";

	OPERATOR "#"*(CONST l,r: SegmentedName): BOOLEAN;
	VAR i: LONGINT;
	BEGIN
		i := 0;
		WHILE (l.sep[i] # 0X) & (r.sep[i] # 0X) DO
			IF (l.index[i] # r.index[i]) OR (l.sep[i] # r.sep[i]) THEN RETURN TRUE END;
			INC(i);
		END;
		RETURN (l.sep[i] # r.sep[i]) OR (l.index[i] # r.index[i]);
	END "#";

BEGIN
	categories[Code] := "code";
	categories[InitCode] := "initcode";
	categories[BodyCode] := "bodycode";
	categories[Data] := "data";
	categories[Const] := "const";
	modes[Absolute] := "abs";
	modes[Relative] := "rel";
	relocatabilities[Fixed] := "fixed";
	relocatabilities[Aligned] := "aligned";
END ObjectFile.


ObjectFile.Test
