MODULE ObjectFile;	(* AUTHOR "negelef"; PURPOSE "Generic Object File Format"; *)

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

TYPE
	SectionName = ARRAY 128 OF CHAR;

	FixupPattern* = RECORD
		offset*, bits*: LONGINT;
	END;

	Fixup* = RECORD
		mode*: INTEGER;
		offset*: LONGINT;
		section*: SectionName;
		displacement*, scale*, patterns*: LONGINT;
		pattern*: POINTER TO ARRAY OF FixupPattern;
	END;

	DataArray*=POINTER TO ARRAY OF CHAR;
	Fixups*=POINTER TO ARRAY OF Fixup;

	Section* = RECORD
		type*: INTEGER;
		name*: SectionName;
		unit*, alignment*, size*, fixups*: LONGINT;
		fixup*: Fixups;
		data*: DataArray;
	END;

VAR
	types: ARRAY 4 OF ARRAY 10 OF CHAR;
	modes: ARRAY 2 OF ARRAY 4 OF CHAR;

PROCEDURE WriteSection* (writer: Streams.Writer; CONST section: Section);
CONST
	Separator = ' ';

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
		writer.Int (fixup.displacement, 0);
		writer.Char (Separator);
		writer.Int (fixup.scale, 0);
		writer.Char (Separator);
		writer.Int (fixup.patterns, 0);
		writer.Char (Separator);
		FOR i := 0 TO fixup.patterns DO
			WritePattern (fixup.pattern[i]);
		END;
		writer.Ln;
	END WriteFixup;

	PROCEDURE WriteData (data: CHAR);
	BEGIN
		writer.Hex ((ORD (data) DIV 16) MOD 16, 0);
		writer.Hex (ORD (data) MOD 16, 0);
	END WriteData;

BEGIN
	WriteIdentifier (section.type, types);
	writer.Char (Separator);
	writer.String (section.name);
	writer.Char (Separator);
	writer.Int (section.unit, 0);
	writer.Char (Separator);
	writer.Int (section.alignment, 0);
	writer.Char (Separator);
	writer.Int (section.size, 0);
	writer.Char (Separator);
	writer.Int (section.fixups, 0);
	writer.Char (Separator);
	FOR i := 0 TO section.fixups DO
		WriteFixup (section.fixup[i]);
	END;
	FOR i := 0 TO section.size DO
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
		WHILE (value # LEN (identifiers)) & (identifier # identifiers[value]) DO
			INC (value);
			reader.GetString (identifier);
		END;
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
		reader.GetInteger (fixup.displacement, FALSE);
		reader.GetInteger (fixup.scale, FALSE);
		reader.GetInteger (fixup.patterns, FALSE);
		IF (fixup.pattern = NIL) OR (LEN (fixup.pattern) < fixup.patterns) THEN
			NEW (fixup.pattern, fixup.patterns);
		END;
		FOR i := 0 TO fixup.patterns DO
			ReadPattern (fixup.pattern[i]);
		END;
	END ReadFixup;

	PROCEDURE ReadData (VAR data: CHAR);
	VAR
		low, high: CHAR;

		PROCEDURE GetNibble (char: CHAR): INTEGER;
		BEGIN
			reader.GetChar (char);
			IF ORD (char) >= ORD ('A') THEN
				RETURN ORD (char) - (ORD ('A') + 10);
			ELSE
				RETURN ORD (char);
			END;
		END GetNibble;

	BEGIN
		reader.GetChar (high);
		reader.Char (low);
		data := CHR (GetNibble (high) * 16 + GetNibble (low));
	END ReadData;

BEGIN
	ReadIdentifier (section.type, types);
	reader.GetString (section.name);
	reader.GetInteger (section.unit, FALSE);
	reader.GetInteger (section.alignment, FALSE);
	reader.GetInteger (section.size, FALSE);
	reader.GetInteger (section.fixups, FALSE);
	IF (section.fixup = NIL) OR (LEN (section.fixup) < section.fixups) THEN
		NEW (section.fixup, section.fixups);
	END;
	FOR i := 0 TO section.fixups DO
		ReadFixup (section.fixup[i]);
	END;
	IF (section.data = NIL) OR (LEN (section.data) < section.size DIV section.unit) THEN
		NEW (section.data, section.size DIV section.unit);
	END;
	FOR i := 0 TO section.size DO
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

