MODULE BitSets;	(** AUTHOR "negelef"; PURPOSE "generic bit container"; *)

IMPORT SYSTEM;

CONST Elements = SYSTEM.SIZEOF (SET);

TYPE Data = POINTER TO ARRAY OF SET;

TYPE BitSet* = OBJECT

	VAR size: LONGINT;
	VAR data: Data;

	PROCEDURE & InitBitSet* (size: LONGINT);
	BEGIN SELF.size := size; Resize (size);
	END InitBitSet;

	PROCEDURE Resize* (size: LONGINT);
	VAR newData: Data; i: LONGINT;
	BEGIN
		ASSERT (size > 0);
		SELF.size := size;
		size := (size - 1) DIV Elements + 1;
		IF data # NIL THEN
			IF size <= LEN (data) THEN RETURN; END;
			size := MAX (size, LEN (data) * 2);
		END;
		NEW (newData, size);
		IF data # NIL THEN
			FOR i := 0 TO LEN (data) - 1 DO newData[i] := data[i]; END;
		END;
		data := newData;
	END Resize;

	PROCEDURE GetSize* (): LONGINT;
	BEGIN RETURN size;
	END GetSize;

	PROCEDURE SetBit* (pos: LONGINT; value: BOOLEAN);
	BEGIN
		ASSERT (pos >= 0); ASSERT (pos < size);
		IF value THEN
			INCL (data[pos DIV Elements], pos MOD Elements);
		ELSE
			EXCL (data[pos DIV Elements], pos MOD Elements);
		END;
	END SetBit;

	PROCEDURE GetBit* (pos: LONGINT): BOOLEAN;
	BEGIN
		ASSERT (pos >= 0); ASSERT (pos < size);
		RETURN pos MOD Elements IN data[pos DIV Elements];
	END GetBit;

	PROCEDURE SetBits* (startPos, bits, value: LONGINT);
	BEGIN
		WHILE bits # 0 DO
			ASSERT (startPos >= 0); ASSERT (startPos < size);
			SetBit (startPos, ODD (value)); value := value DIV 2;
			IF bits > 0 THEN INC (startPos); DEC (bits); ELSE DEC (startPos); INC (bits); END;
		END;
	END SetBits;

	PROCEDURE GetBits* (startPos, bits: LONGINT): LONGINT;
	VAR value: LONGINT;
	BEGIN
		value := 0;
		WHILE bits # 0 DO
			ASSERT (startPos >= 0); ASSERT (startPos < size);
			IF GetBit (startPos) THEN INC (value); END; value := value * 2;
			IF bits > 0 THEN INC (startPos); DEC (bits); ELSE DEC (startPos); INC (bits); END;
		END;
		RETURN value;
	END GetBits;

END BitSet;

PROCEDURE CopyBits* (source: BitSet; sourcePos: LONGINT; dest: BitSet; destPos, count: LONGINT);
VAR i: LONGINT;
BEGIN
	ASSERT (count > 0);
	FOR i := 0 TO count - 1 DO
		dest.SetBit (destPos + i, source.GetBit (sourcePos + i));
	END;
END CopyBits;

END BitSets.

