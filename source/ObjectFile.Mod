MODULE ObjectFile;	(* AUTHOR "negelef"; PURPOSE "Generic Object File Representation"; *)

IMPORT Streams;

CONST
	(* Fixup modes *)
	Absolute* = 0;
	Relative* = 1;

	(* Section types *)
	Code* = 0;
	InitCode* = 1;
	Data* = 2;
	Const* = 3;

	DefaultExtension* = "Gof";

TYPE
	SectionType = INTEGER;

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
		offset*, bits*: LONGINT;
	END;
	FixupPatterns*= POINTER TO ARRAY OF FixupPattern;

	Fixup* = RECORD
		mode*: INTEGER;
		offset*: LONGINT;
		section*: SectionName;
		fingerprint*, displacement*, scale*, patterns*: LONGINT;
		pattern*: FixupPatterns;
	END;

	DataArray*=POINTER TO ARRAY OF CHAR;
	Fixups*=POINTER TO ARRAY OF Fixup;

	Section* = RECORD
		type*: SectionType;
		name*: SectionName;
		fingerprint*, unit*, alignment*, size*, fixups*: LONGINT;
		fixup*: Fixups;
		data*: DataArray;
	END;

VAR
	types: ARRAY 4 OF ARRAY 10 OF CHAR;
	modes: ARRAY 2 OF ARRAY 4 OF CHAR;

PROCEDURE IsCode* (type: SectionType): BOOLEAN;
BEGIN RETURN (type = Code) OR (type = InitCode);
END IsCode;

PROCEDURE CopySection* (CONST source: Section; VAR dest: Section);
VAR i: LONGINT;
BEGIN
	dest.type := source.type;
	dest.name := source.name;
	dest.fingerprint := source.fingerprint;
	dest.unit := source.unit;
	dest.alignment := source.alignment;
	dest.size := source.size;
	dest.fixups:= source.fixups;
	NEW (dest.fixup, dest.fixups);
	NEW (dest.data, dest.size);
	FOR i := 0 TO dest.fixups - 1 DO dest.fixup[i] := source.fixup[i]; END;
	FOR i := 0 TO dest.size - 1 DO dest.data[i] := source.data[i]; END;
END CopySection;

PROCEDURE NibbleToCharacter* (value: INTEGER): CHAR;
BEGIN
	IF value >= 10 THEN
		RETURN CHR ((ORD ('A') - 10) + value);
	ELSE
		RETURN CHR (ORD ('0') + value);
	END;
END NibbleToCharacter;

PROCEDURE CharacterToNibble* (char: CHAR): INTEGER;
BEGIN
	IF ORD (char) >= ORD ('A') THEN
		RETURN ORD (char) - (ORD ('A') - 10);
	ELSE
		RETURN ORD (char) - ORD ('0');
	END;
END CharacterToNibble;

PROCEDURE WriteSection* (writer: Streams.Writer; CONST section: Section);
CONST
	Separator = ' '; Tab = 09X;

VAR
	i: LONGINT;

	PROCEDURE WriteIdentifier (value: INTEGER; CONST identifiers: ARRAY OF ARRAY OF CHAR);
	BEGIN
		writer.String (identifiers[value]);
	END WriteIdentifier;

	PROCEDURE WritePattern (CONST pattern: FixupPattern);
	BEGIN
		writer.Int (pattern.offset, 0);
		writer.Char (Separator);
		writer.Int (pattern.bits, 0);
		writer.Char (Separator);
	END WritePattern;

	PROCEDURE WriteFixup (CONST fixup: Fixup);
	VAR
		i: LONGINT;

	BEGIN
		WriteIdentifier (fixup.mode, modes);
		writer.Char (Separator);
		writer.Int (fixup.offset, 0);
		writer.Char (Separator);
		writer.String (fixup.section);
		writer.Char (Separator);
		writer.Int (fixup.fingerprint, 0);
		writer.Char (Separator);
		writer.Int (fixup.displacement, 0);
		writer.Char (Separator);
		writer.Int (fixup.scale, 0);
		writer.Char (Separator);
		writer.Int (fixup.patterns, 0);
		writer.Char (Separator);
		FOR i := 0 TO fixup.patterns - 1 DO
			WritePattern (fixup.pattern[i]);
		END;
	END WriteFixup;

	PROCEDURE WriteData (data: CHAR);
	BEGIN
		writer.Char (NibbleToCharacter (ORD (data) DIV 16));
		writer.Char (NibbleToCharacter (ORD (data) MOD 16));
	END WriteData;

BEGIN
	WriteIdentifier (section.type, types);
	writer.Char (Separator);
	writer.String (section.name);
	writer.Char (Separator);
	writer.Int (section.fingerprint, 0);
	writer.Char (Separator);
	writer.Int (section.unit, 0);
	writer.Char (Separator);
	writer.Int (section.alignment, 0);
	writer.Char (Separator);
	writer.Int (section.fixups, 0);
	writer.Char (Separator);
	writer.Int (section.size, 0);
	FOR i := 0 TO section.fixups - 1 DO
		writer.Ln; writer.Char (Tab); WriteFixup (section.fixup[i]);
	END;
	FOR i := 0 TO section.size - 1 DO
		IF i MOD 32 = 0 THEN writer.Ln; writer.Char (Tab); END;
		WriteData (section.data[i]);
	END;
	writer.Ln;
END WriteSection;

PROCEDURE ReadSection* (reader: Streams.Reader; VAR section: Section);
VAR
	i: LONGINT;

	PROCEDURE ReadIdentifier (VAR value: INTEGER; CONST identifiers: ARRAY OF ARRAY OF CHAR);
	VAR
		identifier: ARRAY 10 OF CHAR;

	BEGIN
		value := 0;
		reader.GetString (identifier);
		WHILE (value # LEN (identifiers)) & (identifier # identifiers[value]) DO INC (value); END;
		IF value = LEN (identifiers) THEN reader.res := Streams.FormatError; END;
	END ReadIdentifier;

	PROCEDURE ReadPattern (VAR pattern: FixupPattern);
	BEGIN
		reader.GetInteger (pattern.offset, FALSE);
		reader.GetInteger (pattern.bits, FALSE);
	END ReadPattern;

	PROCEDURE ReadFixup (VAR fixup: Fixup);
	VAR
		i: LONGINT;

	BEGIN
		ReadIdentifier (fixup.mode, modes);
		reader.GetInteger (fixup.offset, FALSE);
		reader.GetString (fixup.section);
		reader.GetInteger (fixup.fingerprint, FALSE);
		reader.GetInteger (fixup.displacement, FALSE);
		reader.GetInteger (fixup.scale, FALSE);
		reader.GetInteger (fixup.patterns, FALSE);
		IF (fixup.pattern = NIL) OR (LEN (fixup.pattern) < fixup.patterns) THEN
			NEW (fixup.pattern, fixup.patterns);
		END;
		FOR i := 0 TO fixup.patterns - 1 DO
			ReadPattern (fixup.pattern[i]);
		END;
	END ReadFixup;

	PROCEDURE ReadData (VAR data: CHAR);
	VAR low, high: CHAR;
	BEGIN
		reader.GetChar (high);
		reader.Char (low);
		data := CHR (CharacterToNibble (high) * 16 + CharacterToNibble (low));
	END ReadData;

BEGIN
	ReadIdentifier (section.type, types);
	reader.GetString (section.name);
	reader.GetInteger (section.fingerprint, FALSE);
	reader.GetInteger (section.unit, FALSE);
	reader.GetInteger (section.alignment, FALSE);
	reader.GetInteger (section.fixups, FALSE);
	reader.GetInteger (section.size, FALSE);
	IF (section.fixup = NIL) OR (LEN (section.fixup) < section.fixups) THEN
		NEW (section.fixup, section.fixups);
	END;
	FOR i := 0 TO section.fixups - 1 DO
		ReadFixup (section.fixup[i]);
	END;
	IF (section.data = NIL) OR (LEN (section.data) < section.size) THEN
		NEW (section.data, section.size);
	END;
	FOR i := 0 TO section.size - 1 DO
		ReadData (section.data[i]);
	END;
END ReadSection;

BEGIN
	types[0] := "code";
	types[1] := "initcode";
	types[2] := "data";
	types[3] := "const";
	modes[0] := "abs";
	modes[1] := "rel";
END ObjectFile.

