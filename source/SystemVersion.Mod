MODULE SystemVersion; (** AUTHOR ""; PURPOSE ""; *)

IMPORT
	SYSTEM, Kernel32,  Trace, Machine,  Heaps,  Modules, Objects, Kernel,
	KernelLog, Streams, Commands, Files, WinFS, Loader,	BootConsole;

(*! to do: move CRC Object to a more generic module, e.g. CRC.Mod*)
TYPE CRC= OBJECT
	VAR crc : LONGINT;

		PROCEDURE  &Init;
		BEGIN
			crc := LONGINT(0FFFFFFFFH);
		END Init;

		PROCEDURE Add(i: LONGINT);
		VAR idx: LONGINT;
		BEGIN
			idx := SYSTEM.VAL(LONGINT, SYSTEM.VAL(SET, crc) / SYSTEM.VAL(SET, i)) MOD 100H;
			crc := SYSTEM.VAL(LONGINT, SYSTEM.VAL(SET, CRC32Table[idx])/SYSTEM.VAL(SET, SYSTEM.LSH(crc, -8)));
		END Add;

		PROCEDURE Get():LONGINT;
		BEGIN
			RETURN SYSTEM.VAL(LONGINT, SYSTEM.VAL(SET, crc)/{0..31})
		END Get;
	
	END CRC;

	VAR CRC32Table: ARRAY 256 OF SET;
		(* CRC of those Kernel Modules that were already loaded when this module was first loaded *)
		BootCRC-: LONGINT;

	PROCEDURE InitTable32;
	CONST poly = SHORT(0EDB88320H);
	VAR n, c, k: LONGINT;
	BEGIN
		FOR n := 0 TO 255 DO
			c := n;
			FOR k := 0 TO 7 DO
				IF ODD(c) THEN c := SYSTEM.VAL(LONGINT, SYSTEM.VAL(SET, poly) / SYSTEM.VAL(SET, SYSTEM.LSH(c, -1)))
				ELSE c := SYSTEM.LSH(c, -1)
				END
			END;
			CRC32Table[n] := SYSTEM.VAL(SET, c)
		END
	END InitTable32;

	(* combined CRC of those Kernel Modules that loaded at this point in time *)
	PROCEDURE GetKernelCRC*():LONGINT;
	VAR m:Modules.Module; crc: CRC;
	BEGIN
		NEW(crc);
		m:=Modules.ModuleByName("Kernel32"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("Trace"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("Machine"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("Heaps"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("Modules"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("Objects"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("Kernel"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("KernelLog"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("Streams"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("Commands"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("Files"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("WinFS"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("Loader"); IF m#NIL THEN crc.Add(m.crc) END;
		m:=Modules.ModuleByName("BootConsole"); IF m#NIL THEN crc.Add(m.crc) END;
		RETURN crc.Get()
	END GetKernelCRC;
	
	PROCEDURE GetKernelDate*(CONST name: ARRAY OF CHAR; VAR d,t: LONGINT): BOOLEAN;
	VAR f: Files.File;
	BEGIN
		(*! TBD*)
		d:=0; t:=0; RETURN FALSE;
	END GetKernelDate;
	
	
	PROCEDURE Test*;
	BEGIN
		KernelLog.String("Kernel CRC at boot time: "); KernelLog.Hex(BootCRC,8); KernelLog.Ln;
		KernelLog.String("Kernel CRC now: "); KernelLog.Hex(GetKernelCRC(),8); KernelLog.Ln;
	END Test;
	

BEGIN 
	InitTable32;
	BootCRC:=GetKernelCRC();
END SystemVersion.

SystemVersion.Test
SystemTools.FreeDownTo SystemVersion ~

