MODULE ObjectFile;	(* AUTHOR "negelef"; PURPOSE "Generic Object File Representation"; *)

IMPORT Streams, BitSets;

CONST
	(* Fixup modes *)
	Absolute* = 0;
	Relative* = 1;

	(* Section types *)
	Code* = 0;
	InitCode* = 1;
	BodyCode* = 2;
	Data* = 3;
	Const* = 4;

	Aligned=0;
	Fixed=1;

	DefaultExtension* = "Gof";

TYPE
	Unit* = LONGINT;
	Bits* = LONGINT;

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
		offset*, bits*: Bits;
	END;
	FixupPatterns*= POINTER TO ARRAY OF FixupPattern;

	Identifier*= RECORD
		name*: SectionName;
		fingerprint*: LONGINT;
	END;

	Fixup* = RECORD
		mode*: INTEGER; (* fixup mode: relative or absolute *)
		offset*: Unit; (* offset of address that has to be patched ('destination') *)
		identifier*: Identifier;
		displacement*: Unit; (* displacement of the fixup ('destination') *)
		scale*: Bits; (* exponent of scale factor (factor=2^scale) *)
		patterns*: LONGINT;
		pattern*: FixupPatterns; (* patterns describing the fixup format, cf. above *)
	END;

	Fixups*=POINTER TO ARRAY OF Fixup;

	Section* = RECORD
		type*: SectionType;
		identifier*: Identifier;
		unit*: Bits;
		fixed*: BOOLEAN;
		alignment*: Unit;
		fixups*: LONGINT;
		fixup*: Fixups;
		bits*: BitSets.BitSet;
	END;

VAR
	types: ARRAY 5 OF ARRAY 10 OF CHAR;
	modes: ARRAY 2 OF ARRAY 4 OF CHAR;
	relocatabilities: ARRAY 2 OF ARRAY 8 OF CHAR;

PROCEDURE IsCode* (type: SectionType): BOOLEAN;
BEGIN RETURN (type = Code) OR (type = InitCode) OR (type = BodyCode);
END IsCode;

PROCEDURE Matches*(CONST this, that: Identifier): BOOLEAN;
BEGIN
	IF (this.fingerprint # 0) & (this.fingerprint = that.fingerprint) THEN RETURN TRUE
	ELSE RETURN this.name = that.name
	END;
END Matches;

PROCEDURE CopySection* (CONST source: Section; VAR dest: Section);
VAR i,j: LONGINT;
BEGIN
	dest.type := source.type;
	dest.identifier := source.identifier;
	dest.unit := source.unit;
	dest.fixed := source.fixed;
	dest.alignment := source.alignment;
	dest.fixups:= source.fixups;
	NEW (dest.fixup, dest.fixups);
	NEW (dest.bits, source.bits.GetSize ());
	FOR i := 0 TO dest.fixups - 1 DO
		dest.fixup[i] := source.fixup[i];
		NEW(dest.fixup[i].pattern,source.fixup[i].patterns);
		FOR j := 0 TO source.fixup[i].patterns-1 DO
			dest.fixup[i].pattern[j] := source.fixup[i].pattern[j];
		END;
	END;
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

PROCEDURE WriteSection* (writer: Streams.Writer; CONST section: Section);
CONST Separator = ' '; Tab = 09X;
VAR i: LONGINT; size: Bits;

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
	BEGIN
		writer.String (identifier.name);
		writer.Char (Separator);
		writer.Int (identifier.fingerprint, 0);
	END WriteIdentifier;

	PROCEDURE WriteFixup (CONST fixup: Fixup);
	VAR i: LONGINT;
	BEGIN
		WriteValueIdentifier (fixup.mode, modes);
		writer.Char (Separator);
		writer.Int (fixup.offset, 0);
		writer.Char (Separator);
		WriteIdentifier(fixup.identifier);
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
	FOR i := 0 TO size - 1 BY 4 DO
		IF i MOD (32 * 8) = 0 THEN writer.Ln; writer.Char (Tab); END;
		writer.Char (NibbleToCharacter (section.bits.GetBits (i, MIN (4, size - i))));
	END;
	writer.Ln;
END WriteSection;

PROCEDURE ReadSection* (reader: Streams.Reader; VAR section: Section);
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
	BEGIN
		reader.SkipWhitespace; reader.String (identifier.name);
		reader.SkipWhitespace; reader.Int (identifier.fingerprint,FALSE);
	END ReadIdentifier;


	PROCEDURE ReadFixup (VAR fixup: Fixup);
	VAR i: LONGINT;
	BEGIN
		ReadValueIdentifier (fixup.mode, modes);
		reader.SkipWhitespace; reader.Int (fixup.offset, FALSE);
		ReadIdentifier(fixup.identifier);
		reader.SkipWhitespace; reader.Int (fixup.displacement, FALSE);
		reader.SkipWhitespace; reader.Int (fixup.scale, FALSE);
		reader.SkipWhitespace; reader.Int (fixup.patterns, FALSE);
		IF (fixup.pattern = NIL) OR (LEN (fixup.pattern) < fixup.patterns) THEN
			NEW (fixup.pattern, fixup.patterns);
		END;
		FOR i := 0 TO fixup.patterns - 1 DO
			ReadPattern (fixup.pattern[i]);
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
		section.bits.SetBits (i, MIN (4, size - i), CharacterToNibble (char));
	END;
END ReadSection;

BEGIN
	types[Code] := "code";
	types[InitCode] := "initcode";
	types[BodyCode] := "bodycode";
	types[Data] := "data";
	types[Const] := "const";
	modes[Absolute] := "abs";
	modes[Relative] := "rel";
	relocatabilities[Fixed] := "fixed";
	relocatabilities[Aligned] := "aligned";
END ObjectFile.

