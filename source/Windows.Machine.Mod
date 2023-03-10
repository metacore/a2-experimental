MODULE Machine;
(** AUTHOR "pjm,fof"; PURPOSE "Bootstrapping, configuration and machine interface, adaption to windows fof"; *)
(* red marked parts are WinAos specific *)

IMPORT SYSTEM, Trace, Kernel32;

CONST
#IF AMD64 THEN
	Version = "WinA2 (64bit) ";
#ELSIF I386 THEN
	Version = "WinAos (32bit) ";
#ELSE
	-- UNDEFINED
#END

	DefaultConfigFile = "aos.ini";
	DefaultGenericConfigFile = "aosg.ini";
	UserConfigFile = "myaos.ini";

	MaxCPU* = 8;	(* dummy definition to make GC for both Win32 and I386 work *)

#IF AMD64 THEN
	DefaultObjectFileExtension* = ".GofWw";
#ELSIF I386 THEN
	DefaultObjectFileExtension* = ".Obw";
#ELSE
	-- UNDEFINED
#END

	(** bits in features variable *)
	MTTR* = 12;  MMX* = 23;

	debug* = FALSE;   (** display more debug output during booting *)

CONST
	StaticBlockSize = 8*SIZEOF(ADDRESS);		(* static heap block size *)

(** standard lock levels (in order) *)  (* also refer to Traps.Show *)
	TraceOutput* = 0;   (* Trace output *)
	Memory* = 1;   (* Virtual memory management, stack and page allocation *)
	Heaps* = 2;   (* Storage allocation and Garbage collection *)
	Interrupts* = 3;   (* Interrupt handling. *)
	Modules* = 4;   (* Module list *)
	Objects* = 5;   (* Ready queue *)
	Processors* = 6;   (* Interprocessor interrupts *)
	KernelLog* = 7;   (* Atomic output *)
	GC* = 8;
	MaxLocks = 9;   (* { <= 32 } *)

	StrongChecks = TRUE;


	MemBlockSize = 32*1024*1024; (* must be multiple of StaticBlockSize *)

	NilVal = 0;

	Second* = 1000; (* frequency of ticks increments in Hz *)


CONST
		(* error codes *)
		Ok* = 0;
		NilAdr* = -1;	(* nil value for addresses (not same as pointer NIL value) *)

TYPE
	Vendor* = ARRAY 13 OF CHAR;
	IDMap* = ARRAY 16 OF SIGNED8;

	Range* = RECORD
		adr*, size*: SIGNED32
	END;

	MemoryBlock* = POINTER {UNSAFE, UNTRACED} TO MemoryBlockDesc;
	MemoryBlockDesc* = RECORD
		next- : MemoryBlock;
		startAdr-: ADDRESS; 		(* sort key in linked list of memory blocks *)
		size-: SIZE;
		beginBlockAdr-, endBlockAdr-: ADDRESS
	END;

	(* dummy definition to make GC work for both I386 and Win32 - copied from BIOS.I386.Machine.Mod, but not really used *)
	Stack* = RECORD	(** values are read-only *)
		low: ADDRESS;		(* lowest virtual address that may be allocated for stack *)
		adr*: ADDRESS;		(* lowest address on allocated stack *)	(* exported for Objects only *)
		high*: ADDRESS;	(* next virtual address after stack *)	(* exported for Objects only *)
	END;

VAR

	LastAddress: RECORD END;
	stackBottom-: ADDRESS;

	MMXSupport*: BOOLEAN;
	SSESupport*: BOOLEAN;
	SSE2Support*: BOOLEAN;
	SSE3Support-: BOOLEAN; (* PH 04/11*)
	SSSE3Support-: BOOLEAN;
	SSE41Support-: BOOLEAN;
	SSE42Support-: BOOLEAN;
	SSE5Support-: BOOLEAN;
	AVXSupport-: BOOLEAN;

	version*: ARRAY 64 OF CHAR;   (** Aos version *)
	features*,features2*: SET;   (** processor features *)
	fcr*: SET;   (** default floating-point control register value (default rounding mode is towards -infinity, for ENTIER) *)
	mhz*: SIGNED64;   (** clock rate of GetTimer() in MHz, or 0 if not known *)
	boottime-: SIGNED64; (** in timer units *)

	commandLine-: ARRAY 256 OF CHAR;
	hin, hout: Kernel32.HANDLE;

VAR
	lock-: ARRAY MaxLocks OF CHAR;  (* not implemented as SET because of shared access *)
	cs: ARRAY MaxLocks OF Kernel32.CriticalSection;
	taken: ARRAY MaxLocks OF SIGNED32;
	defaultConfigFile, userConfigFile, traceName: ARRAY Kernel32.MaxPath OF CHAR;

	gcThreshold-: SIZE;
	memBlockHead-{UNTRACED}, memBlockTail-{UNTRACED}: MemoryBlock; (* head and tail of sorted list of memory blocks *)


	(** Convert a string to an integer.  Parameter i specifies where in the string scanning should begin (usually 0 in the first call).  Scanning stops at the first non-valid character, and i returns the updated position.  Parameter s is the string to be scanned.  The value is returned as result, or 0 if not valid.  Syntax: number = ["-"] digit {digit} ["H" | "h"] .  digit = "0" | ... "9" | "A" .. "F" | "a" .. "f" .  If the number contains any hexdecimal letter, or if it ends in "H" or "h", it is interpreted as hexadecimal. *)

	PROCEDURE StrToInt*( VAR i: SIZE;  CONST s: ARRAY OF CHAR ): SIGNED32;
	VAR vd, vh, sgn, d: SIGNED32;  hex: BOOLEAN;
	BEGIN
		vd := 0;  vh := 0;  hex := FALSE;
		IF s[i] = "-" THEN sgn := -1;  INC( i ) ELSE sgn := 1 END;
		LOOP
			IF (s[i] >= "0") & (s[i] <= "9") THEN d := ORD( s[i] ) - ORD( "0" )
			ELSIF (CAP( s[i] ) >= "A") & (CAP( s[i] ) <= "F") THEN d := ORD( CAP( s[i] ) ) - ORD( "A" ) + 10;  hex := TRUE
			ELSE EXIT
			END;
			vd := 10 * vd + d;  vh := 16 * vh + d;  INC( i )
		END;
		IF CAP( s[i] ) = "H" THEN hex := TRUE;  INC( i ) END;   (* optional H *)
		IF hex THEN vd := vh END;
		RETURN sgn * vd
	END StrToInt;

	(** -- Atomic operations -- *)

	(** Atomic INC(x). *)
	PROCEDURE -AtomicInc*(VAR x: SIGNED32);
	CODE
#IF AMD64 THEN
		POP RAX
		LOCK
		INC DWORD [RAX]
#ELSIF I386 THEN
		POP	EAX
		LOCK
		INC	DWORD[EAX]
#ELSE
	UNIMPLEMENTED
#END
	END AtomicInc;

	(** Atomic DEC(x). *)
	PROCEDURE -AtomicDec*(VAR x: SIGNED32);
	CODE
#IF AMD64 THEN
		POP RAX
		LOCK
		DEC DWORD [RAX]
#ELSIF I386 THEN
		POP	EAX
		LOCK
		DEC	DWORD[EAX]
#ELSE
	UNIMPLEMENTED
#END
	END AtomicDec;

	(** Atomic EXCL. *)
	PROCEDURE AtomicExcl* (VAR s: SET; bit: SIGNED32);
	CODE
#IF AMD64 THEN
		MOV EAX, [RBP + bit]
		MOV RBX, [RBP + s]
		LOCK
		BTR [RBX], EAX
#ELSIF I386 THEN
		MOV EAX, [EBP + bit]
		MOV EBX, [EBP + s]
		LOCK
		BTR [EBX], EAX
#ELSE
	UNIMPLEMENTED
#END
	END AtomicExcl;

	(** Atomic INC(x, y). *)
	PROCEDURE -AtomicAdd*(VAR x: SIGNED32; y: SIGNED32);
	CODE
#IF AMD64 THEN
		POP RBX
		POP RAX
		LOCK
		ADD DWORD [RAX], EBX
#ELSIF I386 THEN
		POP	EBX
		POP	EAX
		LOCK
		ADD	DWORD[EAX], EBX
#ELSE
	UNIMPLEMENTED
#END
	END AtomicAdd;

	(** Atomic test-and-set. Set x = TRUE and return old value of x. *)
	PROCEDURE -AtomicTestSet*(VAR x: BOOLEAN): BOOLEAN;
	CODE
#IF AMD64 THEN
		POP RBX
		MOV AL, 1
		XCHG [RBX], AL
#ELSIF I386 THEN
		POP	EBX
		MOV	AL, 1
		XCHG	[EBX], AL
#ELSE
	UNIMPLEMENTED
#END
	END AtomicTestSet;

	(* Atomic compare-and-swap. Set x = new if x = old and return old value of x *)
	PROCEDURE -AtomicCAS* (VAR x: SIGNED32; old, new: SIGNED32): SIGNED32;
	CODE
#IF AMD64 THEN
		POP RBX		; new
		POP RAX		; old
		POP RCX		; address of x
		LOCK CMPXCHG [RCX], EBX	; atomicly compare x with old and set it to new if equal
#ELSIF I386 THEN
		POP EBX		; new
		POP EAX		; old
		POP ECX		; address of x
		DB 0F0X, 00FX, 0B1X, 019X	; LOCK CMPXCHG [ECX], EBX; atomicly compare x with old and set it to new if equal

#ELSE
	UNIMPLEMENTED
#END
	END AtomicCAS;


	(** This procedure should be called in all spin loops as a hint to the processor (e.g. Pentium 4). *)
	PROCEDURE -SpinHint*;
	CODE
		PAUSE
	END SpinHint;

	(** -- Miscellaneous -- *)

	(* Return current instruction pointer *)
	PROCEDURE CurrentPC* (): ADDRESS;
	CODE
#IF AMD64 THEN
		MOV RAX, [RBP + 8]
#ELSIF I386 THEN
		MOV EAX, [EBP+4]
#ELSE
	UNIMPLEMENTED
#END
	END CurrentPC;

	(** Fill "size" bytes at "destAdr" with "filler". "size" must be multiple of 4. *)
	PROCEDURE Fill32* (destAdr: ADDRESS; size: SIZE; filler: SIGNED32);
	CODE
#IF AMD64 THEN
		MOV RDI, [RBP + destAdr]
		MOV RCX, [RBP + size]
		MOV EAX, [RBP + filler]
		TEST RCX, 3
		JZ ok
		PUSH 8	; ASSERT failure
		INT 3
	ok:
		SHR RCX, 2
		CLD
		REP STOSD
#ELSIF I386 THEN
		MOV	EDI, [EBP+destAdr]
		MOV	ECX, [EBP+size]
		MOV	EAX, [EBP+filler]
		TEST	ECX, 3
		JZ	ok
		PUSH	8	;  ASSERT failure
		INT	3
	ok:
		SHR	ECX, 2
		CLD
		REP	STOSD
#ELSE
	UNIMPLEMENTED
#END
	END Fill32;
	(** -- Processor initialization -- *)

	PROCEDURE -SetFCR( s: SET );
	CODE
#IF AMD64 THEN
		FLDCW	[RSP]	;  parameter s
		POP	RAX
#ELSIF I386 THEN
		FLDCW	[ESP]	;  parameter s
		POP	EAX
#ELSE
	UNIMPLEMENTED
#END
	END SetFCR;

	PROCEDURE -FCR( ): SET;
	CODE
#IF AMD64 THEN
		PUSH	0
		FNSTCW	[RSP]
		FWAIT
		POP	RAX
#ELSIF I386 THEN
		PUSH	0
		FNSTCW	[ESP]
		FWAIT
		POP	EAX
#ELSE
	UNIMPLEMENTED
#END
	END FCR;

	PROCEDURE -InitFPU;
	CODE
		FNINIT
	END InitFPU;

(** Setup FPU control word of current processor. *)

	PROCEDURE SetupFPU*;
	BEGIN
		InitFPU;  SetFCR( fcr )
	END SetupFPU;

(** CPU identification. *)

	PROCEDURE CPUID*( VAR vendor: Vendor;  VAR version: SIGNED32;  VAR features1,features2: SET );
	CODE
#IF AMD64 THEN
		MOV	EAX, 0
		CPUID
		CMP	EAX, 0
		JNE	ok
		MOV	RSI, [RBP+vendor]
		MOV	[RSI], AL	;  AL = 0
		MOV	RSI, [RBP+version]
		MOV	[RSI], EAX	;  EAX = 0
		MOV	RSI, [RBP+features1]
		MOV	[RSI], EAX
		MOV	RSI, [RBP+features2]
		MOV	[RSI], EAX
		JMP	end
		ok:
		MOV	RSI, [RBP+vendor]
		MOV	[RSI], EBX
		MOV	[RSI+4], EDX
		MOV	[RSI+8], ECX
		MOV	BYTE [RSI+12], 0
		MOV	EAX, 1
		CPUID
		MOV	RSI, [RBP+version]
		MOV	[RSI], EAX
		MOV	RSI, [RBP+features1]
		MOV	[RSI], EDX
		MOV	RSI, [RBP+features2]
		MOV	[RSI], ECX
		end:
#ELSIF I386 THEN
		MOV	EAX, 0
		CPUID
		CMP	EAX, 0
		JNE	ok
		MOV	ESI, [EBP+vendor]
		MOV	[ESI], AL	;  AL = 0
		MOV	ESI, [EBP+version]
		MOV	[ESI], EAX	;  EAX = 0
		MOV	ESI, [EBP+features1]
		MOV	[ESI], EAX
		MOV	ESI, [EBP+features2]
		MOV	[ESI], EAX
		JMP	end
		ok:
		MOV	ESI, [EBP+vendor]
		MOV	[ESI], EBX
		MOV	[ESI+4], EDX
		MOV	[ESI+8], ECX
		MOV	BYTE [ESI+12], 0
		MOV	EAX, 1
		CPUID
		MOV	ESI, [EBP+version]
		MOV	[ESI], EAX
		MOV	ESI, [EBP+features1]
		MOV	[ESI], EDX
		MOV	ESI, [EBP+features2]
		MOV	[ESI], ECX
		end:
#ELSE
	UNIMPLEMENTED
#END
	END CPUID;

	PROCEDURE GetConfig*( CONST name: ARRAY OF CHAR;  VAR val: ARRAY OF CHAR );
	CONST ConfigKey = "Configuration";
	BEGIN
		COPY ("", val);

		IF Kernel32.GetPrivateProfileString (ConfigKey, name, "", val, LEN (val)(Kernel32.DWORD), userConfigFile) # 0 THEN
		ELSIF Kernel32.GetPrivateProfileString (ConfigKey, name, "", val, LEN (val)(Kernel32.DWORD), defaultConfigFile) # 0 THEN
		END;

		IF (name = "ObjectFileExtension") & (val = "") THEN
#IF AMD64 THEN
			IF Kernel32.Generic THEN
				val := ".GofWw";
			ELSE
				val := ".Obww"
			END;
#ELSIF I386 THEN
			IF Kernel32.Generic THEN
				val := ".GofW";
			ELSE
				val := ".Obw"
			END;
#ELSE
	UNIMPLEMENTED
#END
		END;
	END GetConfig;

	PROCEDURE Shutdown*( restart: BOOLEAN );
	BEGIN
		RemoveTraceFile;
		Kernel32.Shutdown( 0 );   (* calls the finalizer of Heaps *)
	END Shutdown;

(* Dan: from new Machine *)
PROCEDURE -GetTimer*(): SIGNED64;
CODE {SYSTEM.Pentium}
	RDTSC	; set EDX:EAX
END GetTimer;

(* Dan:  mono CPU PCs *)
PROCEDURE ID*(): SIGNED32;
BEGIN
	RETURN 0
END ID;


(**
 * Flush Data Cache for the specified virtual address range. If len is negative, flushes the whole cache.
 * This is used on some architecture to interact with DMA hardware (e.g. Ethernet and USB. It can be
 * left empty on Intel architecture.
 *)
PROCEDURE FlushDCacheRange * (adr: ADDRESS; len: SIZE);
END FlushDCacheRange;

(**
 * Invalidate Data Cache for the specified virtual address range. If len is negative, flushes the whole cache.
 * This is used on some architecture to interact with DMA hardware (e.g. Ethernet and USB. It can be
 * left empty on Intel architecture.
 *)
PROCEDURE InvalidateDCacheRange * (adr: ADDRESS; len: SIZE);
END InvalidateDCacheRange;

(**
 * Invalidate Instruction Cache for the specified virtual address range. If len is negative, flushes the whole cache.
 * This is used on some architecture to interact with DMA hardware (e.g. Ethernet and USB. It can be
 * left empty on Intel architecture.
 *)
PROCEDURE InvalidateICacheRange * (adr: ADDRESS; len: SIZE);
END InvalidateICacheRange;


(* setup MMX, SSE and SSE2..SSE5 and AVX extension *)

PROCEDURE SetupSSE2Ext;
CONST
	MMXFlag=23;(*IN features from EBX*)
	FXSRFlag = 24;
	SSEFlag = 25;
	SSE2Flag = 26;
	SSE3Flag = 0; (*IN features2 from ECX*) (*PH 04/11*)
	SSSE3Flag =9;
	SSE41Flag =19;
	SSE42Flag =20;
	SSE5Flag = 11;
	AVXFlag = 28;
BEGIN
	MMXSupport := MMXFlag IN features;
	SSESupport := SSEFlag IN features;
	SSE2Support := SSESupport & (SSE2Flag IN features);
	SSE3Support := SSE2Support & (SSE3Flag IN features2);
	SSSE3Support := SSE3Support & (SSSE3Flag IN features2); (* PH 04/11*)
	SSE41Support := SSE3Support & (SSE41Flag IN features2);
	SSE42Support := SSE3Support & (SSE42Flag IN features2);
	SSE5Support := SSE3Support & (SSE5Flag IN features2);
	AVXSupport := SSE3Support & (AVXFlag IN features2);

	IF SSESupport & (FXSRFlag IN features) THEN
		(* InitSSE(); *) (*! not privileged mode in Windows not allowed *)
	END;
END SetupSSE2Ext;

PROCEDURE ReadCommandLine(VAR commandLine: ARRAY OF CHAR);
VAR adr: ADDRESS; i: SIGNED32; ch: CHAR;
BEGIN
	adr := Kernel32.GetCommandLine();
	SYSTEM.GET(adr,ch);
	i := 0;
	WHILE (i<LEN(commandLine)-1) & (ch # 0X) DO
		commandLine[i] := ch;
		INC(adr); INC(i);
		SYSTEM.GET(adr,ch);
	END;
END ReadCommandLine;

PROCEDURE ParseLine(VAR c: ARRAY OF CHAR; VAR iniFile: ARRAY OF CHAR);
VAR i: SIGNED32;

	PROCEDURE SkipSpaces;
	BEGIN
		WHILE (c[i] <= " ") & (c[i] # 0X) DO INC(i) END;
	END SkipSpaces;

	PROCEDURE SkipName;
	BEGIN
		WHILE (c[i] > " ") DO INC(i) END;
	END SkipName;

	PROCEDURE CheckName(CONST name: ARRAY OF CHAR): BOOLEAN;
	VAR j: SIGNED32;
	BEGIN
		j := 0;
		WHILE (c[i] = name[j]) & (c[i] # 0X) & (name[j] # 0X) DO
			INC(i); INC(j);
		END;
		RETURN (name[j] = 0X);
	END CheckName;

	PROCEDURE ReadName(VAR name: ARRAY OF CHAR);
	VAR j: SIGNED32;
	BEGIN
		SkipSpaces;
		j := 0;
		WHILE (c[i] > " ") & (j < LEN(name)-1) DO
			name[j] := c[i];
			INC(i); INC(j);
		END;
		name[j] := 0X;
	END ReadName;

BEGIN
	c[LEN(c)-1] := 0X;
	i := 0;
	SkipSpaces;
	SkipName;
	SkipSpaces;
	IF c[i] = "-" THEN (* option *)
		INC(i);
		IF CheckName("ini") THEN SkipSpaces; ReadName(iniFile) END;
	END;
END ParseLine;


PROCEDURE TraceChar(c: CHAR);
VAR len: SIGNED32; b: Kernel32.BOOL;
BEGIN
	len := 1;
	b := Kernel32.WriteFile(hout,c,len,len,NIL);
END TraceChar;

PROCEDURE SetTraceFile*;
BEGIN
	traceName := "SystemTrace.txt";
	SetupTraceName(traceName);
	Trace.String("trace -> file "); Trace.String(traceName); Trace.Ln;
	hout := Kernel32.CreateFile(traceName, {Kernel32.GenericWrite}, {Kernel32.FileShareRead}, NIL, Kernel32.CreateAlways, {Kernel32.FileAttributeNormal}, Kernel32.NULL);
	IGNORE Kernel32.GetFullPathName(traceName, LEN(traceName),traceName, NIL);
	Trace.Char := TraceChar;
	Trace.String(version); Trace.Ln;
END SetTraceFile;

PROCEDURE SetTraceConsole*;
VAR res: INTEGER;
BEGIN
	Trace.String("trace -> console"); Trace.Ln;
	res := Kernel32.AllocConsole ();
	hin := Kernel32.GetStdHandle (Kernel32.STDInput);
	hout := Kernel32.GetStdHandle (Kernel32.STDOutput);
	Trace.Char := TraceChar;
	Trace.String(version); Trace.Ln;
END SetTraceConsole;

PROCEDURE SetupTraceName(VAR traceName: ARRAY OF CHAR);
VAR
	ext: ARRAY 256 OF CHAR;
	extPos,i,j: SIGNED32;
	systemTime: Kernel32.SystemTime;
	ch: CHAR;

	PROCEDURE AppendDecimals(int: SIGNED32; from, to: SIGNED32);
	BEGIN
		WHILE to >= from DO
			traceName[i] := CHR(ORD("0")+ int DIV to MOD 10); INC(i);
			to := to DIV 10;
		END;
	END AppendDecimals;

BEGIN
	Kernel32.GetLocalTime(systemTime);

	extPos := 0;
	REPEAT
		ch := traceName[i];

		IF ch = "." THEN j := 0; extPos := i END;

		ext[j] := ch;
		INC(j); INC(i);
	UNTIL ch = 0X;

	IF extPos > 0 THEN i := extPos END;
	ext[j] := 0X;

	AppendDecimals(systemTime.wYear,1,1000);
	AppendDecimals(systemTime.wMonth,1,10);
	AppendDecimals(systemTime.wDay,1,10);
	traceName[i] := "_"; INC(i);
	AppendDecimals(systemTime.wHour,1,10);
	AppendDecimals(systemTime.wMinute,1,10);
	AppendDecimals(systemTime.wSecond,1,10);
	traceName[i] := "_"; INC(i);
	AppendDecimals(systemTime.wMilliseconds,10,100);
	j := 0;
	REPEAT
		ch := ext[j];
		traceName[i] := ch;
		INC(i); INC(j);
	UNTIL ch = 0X;

END SetupTraceName;

PROCEDURE RemoveTraceFile;
VAR res: INTEGER;
BEGIN
	IF (traceName # "") & (traceName # "Console") THEN
		Trace.String("removing "); Trace.String(traceName); Trace.Ln;
		(*Trace.Char := LogChar;*)
		res := Kernel32.CloseHandle(hout);
		IF res = 0 THEN
			res := Kernel32.GetLastError();
			Trace.String("could not close "); Trace.String("; res = "); Trace.Int(res,1); Trace.Ln;
		END;
		res := Kernel32.DeleteFile(traceName);
		IF res = 0 THEN
			res := Kernel32.GetLastError();
			Trace.String("could not delete "); Trace.String(traceName); Trace.String("; res = "); Trace.Int(res,1); Trace.Ln;
		END;
	END;
END RemoveTraceFile;

PROCEDURE ToExecutablePath(CONST name: ARRAY OF CHAR; VAR fullName: ARRAY OF CHAR);
VAR i,j: SIGNED32;
BEGIN
	IGNORE Kernel32.GetModuleFileName(Kernel32.hInstance, fullName, LEN( fullName )(Kernel32.DWORD) );
	j := -1; i := 0;
	WHILE fullName[i] # 0X DO
		IF fullName[i] = '\' THEN j := i END;
		INC( i )
	END;
	i := 0; INC(j);
	WHILE name[i] # 0X DO
		fullName[j] := name[i]; INC(i); INC(j);
	END;
	fullName[j] := 0X;
END ToExecutablePath;

PROCEDURE Append(VAR s: ARRAY OF CHAR; CONST t: ARRAY OF CHAR);
VAR i,j: SIGNED32;
BEGIN
	i := 0;
	WHILE(s[i] # 0X) DO INC(i) END;
	j := 0;
	WHILE (t[j] # 0X) DO
		s[i] := t[j];
		INC(i); INC(j);
	END;
	s[i] := 0X;
END Append;

PROCEDURE Init*;
VAR vendor: Vendor; ver: SIGNED32; hfile: Kernel32.HANDLE;
BEGIN
	Kernel32.Init;
	(*	trace[1] := 0X; Trace.Char := LogChar; Trace.Color := TraceColor; *)
	InitLocks();
	boottime:=GetTimer();

	COPY( Version, version );
	Append(version, SYSTEM.Date);
	CPUID(vendor, ver, features,features2);	 SetupSSE2Ext;
	fcr := (FCR() - {0,2,3,10,11}) + {0..5,8,9};	(* default FCR RC=00B *)

	ReadCommandLine(commandLine);

	IF Kernel32.Generic THEN
		ToExecutablePath(DefaultGenericConfigFile, defaultConfigFile);
	ELSE
		ToExecutablePath(DefaultConfigFile, defaultConfigFile);
	END;
	COPY(UserConfigFile, userConfigFile);
	hfile := Kernel32.CreateFile( userConfigFile, {Kernel32.GenericRead}, {Kernel32.FileShareRead}, NIL , Kernel32.OpenExisting, {Kernel32.FileAttributeNormal}, 0 );
	IF hfile = Kernel32.InvalidHandleValue THEN
		ToExecutablePath(UserConfigFile, userConfigFile);
	ELSE
		IGNORE Kernel32.CloseHandle(hfile)
	END;

	(*
	(* ever used ? *)
	ParseLine(commandLine, userConfigFile);
	userConfigFile[Kernel32.GetFullPathName (userConfigFile, Kernel32.MaxPath, userConfigFile, 0)] := 0X;

	traceName[0] := 0X;
	GetConfig("Trace",traceName);
	Trace.String("traceName "); Trace.String(traceName); Trace.Ln;
	IF traceName = "File" THEN SetTraceFile;
	ELSIF traceName = "Console" THEN SetTraceConsole
	(* else trace is on kernel log *)
	END;
	Trace.String("Machine init done"); Trace.Ln;
	*)
END Init;

	PROCEDURE {OPENING} Start*;
	BEGIN
		stackBottom := SYSTEM.GetStackPointer();
		Init; (* cannot allocate variables in here *)
	END Start;

	(* Initialize locks. *)
	PROCEDURE InitLocks;
	VAR i: SIGNED32;
	BEGIN
		i := 0;
		WHILE i < MaxLocks DO Kernel32.InitializeCriticalSection( cs[i] ); lock[i] := "N"; taken[i] := 0; INC( i ) END;
	END InitLocks;

	PROCEDURE CleanupLocks*;
	VAR i: SIGNED32;
	BEGIN
		i := 0;
		WHILE i < MaxLocks DO Kernel32.DeleteCriticalSection( cs[i] ); taken[i] := 0; lock[i] := "N"; INC( i ) END;
	END CleanupLocks;

(** Acquire a spin-lock. *)
	PROCEDURE Acquire*( level: SIGNED32 );   (* non reentrant lock  (non reentrance "ensured" by ASSERT statement ), CriticalSections are reentrant *)
	VAR i: INTEGER;
	BEGIN
		Kernel32.EnterCriticalSection( cs[level] );
		taken[level] := Kernel32.GetCurrentThreadId();
		IF StrongChecks THEN
			ASSERT ( lock[level] = "N", 1001 );
			FOR i := 0 TO level-1 DO
				ASSERT(taken[i] # taken[level]);
			END
		ELSIF lock[level] # "N" THEN
			Trace.String("warning: reentered non-reentrant lock"); Trace.Ln;
		END;
		lock[level] := "Y";
	END Acquire;

(** Release a spin-lock. *)
	PROCEDURE Release*( level: SIGNED32 );   (* release lock *)
	BEGIN
		IF StrongChecks THEN
			ASSERT ( lock[level] ="Y", 1002 );
			ASSERT( taken[level] = Kernel32.GetCurrentThreadId());
		ELSIF lock[level] # "Y" THEN
			Trace.String("warning: reentered non-reentrant lock"); Trace.Ln;
		END;
		lock[level] := "N";
		taken[level] := 0;
		Kernel32.LeaveCriticalSection( cs[level] )
	END Release;


	(* added by Alexey *)
	PROCEDURE GetMemStatus(VAR stat: Kernel32.MemoryStatusEx): BOOLEAN;
	BEGIN
		stat.dwLength := 64;
		IF Kernel32.GlobalMemoryStatusEx(stat) = 1 THEN
			RETURN TRUE;
		ELSE
			RETURN FALSE;
		END;
	END GetMemStatus;

(** dummy procedure to make GC work for both I386 and Win32 *)
PROCEDURE GetKernelStacks*(VAR stack: ARRAY OF Stack);
VAR i: SIGNED32;
BEGIN
	FOR i := 0 TO MaxCPU-1 DO
		stack[i].adr := NilVal;
		stack[i].high := NilVal
	END
END GetKernelStacks;

(* Set machine-dependent parameter gcThreshold *)
PROCEDURE SetGCParams*;
BEGIN
	gcThreshold := 10*1024*1024; (* 10 MB *)
END SetGCParams;

(** Get first memory block and first free address, the first free address is identical to memBlockHead.endBlockAdr *)
PROCEDURE GetStaticHeap*(VAR beginBlockAdr, endBlockAdr, freeBlockAdr: ADDRESS);
BEGIN
	beginBlockAdr := NIL; endBlockAdr := NIL; freeBlockAdr := NIL;
END GetStaticHeap;

(* returns if an address is a currently allocated heap address *)
PROCEDURE ValidHeapAddress*(p: ADDRESS): BOOLEAN;
VAR mb: MemoryBlock;
BEGIN
	IF (p>=ADDRESS OF Kernel32.EntryPoint) & (p<=ADDRESSOF(LastAddress)) THEN RETURN TRUE END;
	IF (p < memBlockHead.beginBlockAdr) OR (p>memBlockTail.endBlockAdr) THEN RETURN FALSE END;
	mb := memBlockHead;
	WHILE mb # NIL DO
		IF (p >= mb.beginBlockAdr) & (p <= mb.endBlockAdr) THEN  RETURN TRUE  END;
		mb := mb.next;
	END;
	RETURN FALSE;
END ValidHeapAddress;

PROCEDURE GetFreeK* (VAR total, lowFree, highFree: SIZE);
VAR
	stat: Kernel32.MemoryStatusEx;
BEGIN
	total := MAX(SIZE); lowFree := 0; highFree := total;
	(*<< added by Alexey *)
	IF GetMemStatus(stat) THEN
		total := SIZE(stat.ullTotalVirtual DIV 1024);
		lowFree := 0;
		highFree := SIZE(stat.ullAvailVirtual DIV 1024);
	END;
	(* added by Alexey >>*)
END GetFreeK;

(* ug *)
PROCEDURE TraceMemBlocks*;
VAR memBlock {UNTRACED}: MemoryBlock; i : SIGNED32;
BEGIN
	memBlock := memBlockHead;
	i := 0;
	WHILE memBlock # NIL DO
		Trace.String("block "); Trace.Int(i, 0); Trace.String(": startAdr = "); Trace.Hex(memBlock.startAdr, 0);
		Trace.String(" size = "); Trace.Hex(memBlock.size, 0);
		Trace.String(" beginBlockAdr = "); Trace.Hex(memBlock.beginBlockAdr, 0);
		Trace.String(" endBlockAdr = "); Trace.Hex(memBlock.endBlockAdr, 0); Trace.Ln;
		memBlock := memBlock.next;
		INC(i)
	END
END TraceMemBlocks;

(* insert given memory block in sorted list of memory blocks, sort key is startAdr field - called during GC *)
PROCEDURE InsertMemoryBlock(memBlock: MemoryBlock);
VAR cur {UNTRACED}, prev {UNTRACED}: MemoryBlock;
BEGIN
	cur := memBlockHead;
	prev := NIL;
	WHILE (cur # NIL) & (cur.startAdr < memBlock.startAdr) DO
		prev := cur;
		cur := cur.next
	END;
	IF prev = NIL THEN (* insert at head of list *)
		memBlock.next := memBlockHead;
		memBlockHead := memBlock
	ELSE (* insert in middle or at end of list *)
		memBlock.next := cur;
		prev.next := memBlock;
	END;
		IF cur = NIL THEN
			memBlockTail := memBlock
		END
END InsertMemoryBlock;

	(* expand heap by allocating a new memory block *)
	PROCEDURE ExpandHeap*( dummy: SIGNED32; size: SIZE; VAR memoryBlock: MemoryBlock; VAR beginBlockAdr, endBlockAdr: ADDRESS );
	VAR mBlock: MemoryBlock;  alloc: SIZE;  adr,initVal: ADDRESS; continue: BOOLEAN;
	BEGIN
		ASSERT(SIZEOF(MemoryBlockDesc) <= StaticBlockSize); (* make sure MemoryBlock contents fits into one StaticBlock *)
		alloc := size + StaticBlockSize;
		IF alloc < MemBlockSize THEN alloc := MemBlockSize END;
		INC( alloc, (-alloc) MOD StaticBlockSize );

		IF memBlockTail # NIL THEN
			initVal := memBlockTail.startAdr + memBlockTail.size;
		ELSE
			initVal := NIL
		END;
		adr := Kernel32.VirtualAlloc(initVal, alloc, {Kernel32.MEMCommit, Kernel32.MEMReserve}, {Kernel32.PageExecuteReadWrite});
		IF adr = NilVal THEN (* allocation failed *)
			adr := Kernel32.VirtualAlloc(NilVal, alloc, {Kernel32.MEMCommit}, {Kernel32.PageExecuteReadWrite});
		END;
		continue := adr = initVal;
		ASSERT(adr MOD StaticBlockSize = 0); (* is fulfilled because VirtualAlloc is on page granularity *)

	IF adr # 0 THEN

		IF continue THEN
			memoryBlock := memBlockTail;
			memoryBlock.size := memoryBlock.size + alloc;

			beginBlockAdr := memBlockTail.endBlockAdr;
			endBlockAdr := beginBlockAdr;
			INC(endBlockAdr, alloc);
		ELSE
			mBlock := adr;
			mBlock.next := NIL;
			mBlock.startAdr := adr;
			mBlock.size := alloc;

			beginBlockAdr := adr + StaticBlockSize;
			endBlockAdr := beginBlockAdr + alloc - StaticBlockSize;

			mBlock.beginBlockAdr := beginBlockAdr;
			mBlock.endBlockAdr := beginBlockAdr; (* block is still empty -- Heaps module will set the upper bound *)

			InsertMemoryBlock( mBlock );

			memoryBlock := mBlock;
		END;
	ELSE
		beginBlockAdr := 0; endBlockAdr := 0; memoryBlock := NIL;
	END;
END ExpandHeap;


(* Set memory block end address *)
PROCEDURE SetMemoryBlockEndAddress*(memBlock: MemoryBlock; endBlockAdr: ADDRESS);
BEGIN
	ASSERT(endBlockAdr >= memBlock.beginBlockAdr);
	memBlock.endBlockAdr := endBlockAdr
END SetMemoryBlockEndAddress;

(* Free unused memory block - called during GC *)
PROCEDURE FreeMemBlock*(memBlock: MemoryBlock);
VAR cur {UNTRACED}, prev {UNTRACED}: MemoryBlock;
	startAdr: ADDRESS;
BEGIN
	cur := memBlockHead;
	prev := NIL;
	WHILE (cur # NIL) & (cur # memBlock) DO
		prev := cur;
		cur := cur.next
	END;
	IF cur = memBlock THEN
		IF prev = NIL THEN
			memBlockHead := cur.next;
		ELSE
			prev.next := cur.next;
			IF prev.next = NIL THEN
				memBlockTail := prev
			END
		END;
		memBlock.next := NIL;
		startAdr := memBlock.startAdr; (* this value must be cached for the second call of Kernel32.VirtualFree *)
		IGNORE Kernel32.VirtualFree(memBlock.startAdr, memBlock.size, {Kernel32.MEMDecommit});
		IGNORE Kernel32.VirtualFree(startAdr , 0, {Kernel32.MEMRelease});
	ELSE
		HALT(535)	(* error in memory block management *)
	END;
END FreeMemBlock;

PROCEDURE PhysicalAdr*(adr: ADDRESS; size: SIZE): ADDRESS;
END PhysicalAdr;

(* function returning the number of processors that are available to Aos *)
PROCEDURE NumberOfProcessors*( ): SIGNED32;
VAR info: Kernel32.SystemInfo;
BEGIN
	Kernel32.GetSystemInfo( info );
	RETURN info.dwNumberOfProcessors
END NumberOfProcessors;

(* function for changing byte order *)
PROCEDURE ChangeByteOrder* (n: SIGNED32): SIGNED32;
CODE
#IF AMD64 THEN
	MOV EAX, [RBP+n]				; load n in eax
	BSWAP EAX						; swap byte order
#ELSIF I386 THEN
	MOV EAX, [EBP+n]				; load n in eax
	BSWAP EAX
#ELSE
	UNIMPLEMENTED
#END
END ChangeByteOrder;

	PROCEDURE  Portin8*(port: SIGNED32; VAR val: CHAR);
	END Portin8;

	PROCEDURE  Portin16*(port: SIGNED32; VAR val: SIGNED16);
	END Portin16;

	PROCEDURE  Portin32*(port: SIGNED32; VAR val: SIGNED32);
	END Portin32;

	PROCEDURE  Portout8*(port: SIGNED32; val: CHAR);
	END Portout8;

	PROCEDURE  Portout16*(port: SIGNED32; val: SIGNED16);
	END Portout16;

	PROCEDURE  Portout32*(port: SIGNED32; val: SIGNED32);
	END Portout32;

BEGIN
	IF ~Kernel32.Generic THEN
		Init
	END;
	Trace.String(version); Trace.Ln;
END Machine.
