(* ETH Oberon, Copyright 2000 ETH Zuerich Institut fuer Computersysteme, ETH Zentrum, CH-8092 Zuerich.
Refer to the "General ETH Oberon System Source License" contract available at: http://www.oberon.ethz.ch/ *)

MODULE Modules;   (* Oberon for Windows Module Loader; RC/MH 10.12.93 / 3.2.94 / 25.5.94 / tk 4.1.96*)

(*	1999.11.12	g.f.	Linux/Solaris x86 version	*)
(*	2001.01.05	g.f.	adapted to new Compiler	*)
(*	2006.06.20	g.f.	Unix-Aos version *)
(*	2007.04.30	g.f.	adapted to the new extended Module structure *)


IMPORT S := SYSTEM, Glue, Aos := Basetypes, Heaps, Machine, Trace, Unix;

TYPE
	Address = S.ADDRESS;
	Size = S.SIZE;

	Name* = Aos.Name;  Module* = Aos.Module;  Command* = Aos.Command;
	CommandProc* = Aos.CommandProc;  CommandParProc* = Aos.CommandParProc;
	TypeDesc* = Aos.TypeDesc;  ExportPtr* = Aos.ExportPtr;  ExportDesc* = Aos.ExportDesc;
	ExceptionTable* = Aos.ExceptionTable;  ExceptionTableEntry* = Aos.ExceptionTableEntry;
	ProcTable* = Aos.ProcTable;  ProcTableEntry* = Aos.ProcTableEntry;

	Bytes* = Aos.Bytes;  TerminationHandler* = Aos.TermHandler;

	ProcOffsetEntry* = RECORD
				data*: ProcTableEntry;   (* code offsets of procedures *)
				startIndex*: LONGINT;   (* index into global ptrOffsets table *)
			END;

	ProcOffsetTable* = POINTER TO ARRAY OF ProcOffsetEntry;
	PtrTable* = Aos.PtrTable;

	Suffix* = ARRAY 8 OF CHAR;

	LoaderProc* = PROCEDURE ( name, fileName: ARRAY OF CHAR;  VAR res: LONGINT;  VAR msg: ARRAY OF CHAR ): Module;

CONST
	Ok* = 0;

	MaxTags* = 16;   (* in type descriptor *)

	(** type descriptor field offsets relative to root (middle) *)
	Tag0Ofs* = -8;   (** first tag *)
	Mth0Ofs* = Tag0Ofs - 4*MaxTags;   (** first method *)
	Ptr0Ofs* = 4;   (** first pointer offset *)


	MaxObjFormats = 5;   (* maximum number of object file formats installed *)
	ClearCode = TRUE;
	ModOfs = 16;   (* moduleAdr offset in TypeDesc *)

	None* = 0;  PowerDown* = 1;  Reboot* = 2;   (* shutdown codes *)

	InitTableLen = 1024;  InitPtrTableLen = 2048;

	DefaultContext* = "A2";


VAR
	extension-: ARRAY MaxObjFormats OF Suffix;
	loader: ARRAY MaxObjFormats OF LoaderProc;
	numLoaders: LONGINT;
	kernelProc*: ARRAY 11 OF Address;	(** kernel call addresses for loader *)

	procOffsets-: ProcOffsetTable;   (* global table containing procedure code offsets and pointer offsets,
										sorted in ascending order of procedure code offsets *)
	numProcs: LONGINT;   (* number of entries in procOffsets *)
	ptrOffsets-: PtrTable;  numPtrs: LONGINT;

	root*: Module;
	shutdown*: LONGINT;   (** None, Reboot, PowerDown *)

	freeRoot*: Module;   (** list of freed modules (temporary) *)

	debug: SET;  llev: INTEGER;

	traceGC: BOOLEAN;
	traceLoad: BOOLEAN;

	PROCEDURE trace( CONST m, s: ARRAY OF CHAR );
	VAR i: INTEGER;
	BEGIN
		Machine.Acquire( Machine.Modules );
		i := 0;  
		WHILE i < llev DO  Trace.String( "    " );  INC( i )  END;
		Trace.String( m );
		IF s = "" THEN Trace.Ln  ELSE  Trace.String( s ) END;
		Machine.Release( Machine.Modules );
	END trace;

	PROCEDURE AddLoader*( CONST ext: ARRAY OF CHAR;  proc: LoaderProc );
	BEGIN
		Machine.Acquire( Machine.Modules );
		ASSERT( numLoaders < MaxObjFormats );  loader[numLoaders] := proc;
		COPY( ext, extension[numLoaders] );
		ASSERT( ext = extension[numLoaders] );   (* no overflow *)
		INC( numLoaders );
		Machine.Release( Machine.Modules );
	END AddLoader;

	PROCEDURE AddTopLoader*( CONST ext: ARRAY OF CHAR;  proc: LoaderProc );
	VAR i: LONGINT;
	BEGIN
		Machine.Acquire( Machine.Modules );
		ASSERT( numLoaders < MaxObjFormats );  i := numLoaders;
		WHILE i > 0 DO  extension[i] := extension[i - 1];  loader[i] := loader[i - 1];  DEC( i )  END;
		loader[0] := proc;  COPY( ext, extension[0] );
		ASSERT( ext = extension[0] );   (* no overflow *)
		INC( numLoaders );
		Machine.Release( Machine.Modules );
	END AddTopLoader;

	PROCEDURE RemoveLoader*( CONST ext: ARRAY OF CHAR;  proc: LoaderProc );
	VAR i, j: LONGINT;
	BEGIN
		Machine.Acquire( Machine.Modules );
		i := 0;
		WHILE (i # numLoaders) & ((loader[i] # proc) OR (extension[i] # ext)) DO  INC( i )  END;
		IF i # numLoaders THEN
			FOR j := i TO numLoaders - 2 DO  loader[j] := loader[j + 1];  extension[j] := extension[j + 1]  END;
			loader[numLoaders - 1] := NIL;  extension[numLoaders - 1] := "";  DEC( numLoaders )
		END;
		Machine.Release( Machine.Modules )
	END RemoveLoader;

	(*	Retrieve a procedure given a module name, the procedure name and some type information (kernel call) *)
	PROCEDURE GetProcedure( CONST moduleName, procedureName: ARRAY OF CHAR;  argTdAdr, retTdAdr: Address;
											  VAR entryAdr: Address );
	VAR m: Module;  i, res: LONGINT;
		msg: ARRAY 32 OF CHAR;
	BEGIN
		m := ThisModule( moduleName, res, msg );
		IF res = 0 THEN
			ASSERT( m.initialized );   (* module body must have been called (see note at end of module) *)
			Machine.Acquire( Machine.Modules );
			i := 0;  entryAdr := 0;
			WHILE (entryAdr = 0) & (i # LEN( m.command^ )) DO
				IF (m.command[i].name = procedureName) &
				    (m.command[i].argTdAdr = argTdAdr) &
				    (m.command[i].retTdAdr = retTdAdr) THEN  entryAdr := m.command[i].entryAdr;
				END;
				INC( i )
			END;
			Machine.Release( Machine.Modules );
		END;
	END GetProcedure;

	PROCEDURE FindPos( key: Address;  VAR pos: LONGINT ): BOOLEAN;
	VAR l, r, x: LONGINT;  isHit: BOOLEAN;
	BEGIN
		l := 0;  r := numProcs - 1;
		REPEAT
			x := (l + r) DIV 2;
			IF key < procOffsets[x].data.pcFrom THEN  r := x - 1  ELSE  l := x + 1  END;
			isHit := ((procOffsets[x].data.pcFrom <= key) & (key < procOffsets[x].data.pcLimit));
		UNTIL isHit OR (l > r);
		IF isHit THEN  pos := x;  RETURN TRUE   ELSE  RETURN FALSE   END
	END FindPos;

	(** searches for the given pc in the global ProcKeyTable, if found it returns the corresponding data element *)
	PROCEDURE FindProc*( pc: Address;  VAR data: ProcTableEntry;  VAR index: LONGINT;  VAR success: BOOLEAN );
	VAR x: LONGINT;
	BEGIN
		success := FindPos( pc, x );
		IF success THEN  data := procOffsets[x].data;  index := procOffsets[x].startIndex  END
	END FindProc;

	PROCEDURE FindInsertionPos( VAR entry: ProcTableEntry;  VAR pos: LONGINT ): BOOLEAN;
	VAR l, r, x: LONGINT;  success, isHit: BOOLEAN;
	BEGIN
		pos := -1;  success := FALSE;
		IF numProcs = 0 THEN  (* empty table *)
		 pos := 0;  success := TRUE
		ELSE
			l := 0;  r := numProcs - 1;
			REPEAT
				x := (l + r) DIV 2;
				IF entry.pcLimit < procOffsets[x].data.pcFrom THEN  r := x - 1  ELSE  l := x + 1  END;
				isHit := ((x = 0) OR (procOffsets[x - 1].data.pcLimit < entry.pcFrom)) &
						(entry.pcLimit < procOffsets[x].data.pcFrom);
			UNTIL isHit OR (l > r);
			IF isHit THEN  pos := x;  success := TRUE   ELSE
				IF (x = numProcs - 1) & (procOffsets[x].data.pcLimit < entry.pcFrom) THEN  pos := x + 1;  success := TRUE   END
			END
		END;
		RETURN success
	END FindInsertionPos;

	PROCEDURE NumTotalPtrs( procTable: ProcTable ): LONGINT;
	VAR i, num: LONGINT;
	BEGIN
		num := 0;
		FOR i := 0 TO LEN( procTable ) - 1 DO  num := num + procTable[i].noPtr  END;
		RETURN num
	END NumTotalPtrs;

	(* insert the procedure code offsets and pointer offsets of a single module into the global table *)
	PROCEDURE InsertProcOffsets( procTable: ProcTable;  ptrTable: PtrTable;  maxPtr: LONGINT );
	VAR success: BOOLEAN;  i, j, pos, poslast, newLen, num: LONGINT;  newProcOffsets: ProcOffsetTable;
		newPtrOffsets: PtrTable;
	BEGIN
		(* this procedure is called by procedure Publish only and is protected by the Machine.Modules lock *)
		IF LEN( procTable ) > 0 THEN
			IF numProcs + LEN( procTable ) > LEN( procOffsets ) THEN
				newLen := LEN( procOffsets ) + InitTableLen;
				WHILE numProcs + LEN( procTable ) > newLen DO  newLen := newLen + InitTableLen  END;
				NEW( newProcOffsets, newLen );
				FOR i := 0 TO numProcs - 1 DO  newProcOffsets[i] := procOffsets[i]  END;
				procOffsets := newProcOffsets
			END;
			num := NumTotalPtrs( procTable );
			IF numPtrs + num > LEN( ptrOffsets ) THEN
				newLen := LEN( ptrOffsets ) + InitPtrTableLen;
				WHILE numPtrs + num > newLen DO  newLen := newLen + InitPtrTableLen  END;
				NEW( newPtrOffsets, newLen );
				FOR i := 0 TO numPtrs - 1 DO  newPtrOffsets[i] := ptrOffsets[i]  END;
				ptrOffsets := newPtrOffsets
			END;
			success := FindInsertionPos( procTable[0], pos );
			success := success & FindInsertionPos( procTable[LEN( procTable ) - 1], poslast );
			IF ~success THEN  Machine.Release( Machine.Modules )  END;
			ASSERT( success & (pos = poslast) );

			FOR i := numProcs - 1 TO pos BY -1 DO  procOffsets[i + LEN( procTable )] := procOffsets[i]  END;
			FOR i := 0 TO LEN( procTable ) - 1 DO
				procOffsets[pos + i].data := procTable[i];
				procOffsets[pos + i].startIndex := numPtrs;  (* this field is never accessed in case of procTable[i].noPtr = 0, so we may as well put numPtrs in there *)
				FOR j := 0 TO procTable[i].noPtr - 1 DO  ptrOffsets[numPtrs + j] := ptrTable[i*maxPtr + j]  END;
				numPtrs := numPtrs + procTable[i].noPtr;
			END;
			numProcs := numProcs + LEN( procTable );
		END
	END InsertProcOffsets;


	(** deletes a sequence of entries given in procTable from the global procOffsets table - the table remains sorted,
		this procedure is called within AosLocks.AosModules, so no lock is taken here. *)
	PROCEDURE DeleteProcOffsets( firstProcPC: Address;  noProcsInMod: LONGINT );
	VAR pos, i, noPtrsInMod, oldIndex: LONGINT;  success: BOOLEAN;
	BEGIN
		IF noProcsInMod > 0 THEN
			success := FindPos( firstProcPC, pos );
			IF success THEN
				(* delete entries in ptrOffsets first *)
				noPtrsInMod := 0;
				FOR i := pos TO pos + noProcsInMod - 1 DO  noPtrsInMod := noPtrsInMod + procOffsets[i].data.noPtr  END;
				oldIndex := procOffsets[pos].startIndex;
				FOR i := procOffsets[pos].startIndex + noPtrsInMod TO numPtrs - 1 DO
					ptrOffsets[i - noPtrsInMod] := ptrOffsets[i]
				END;
				numPtrs := numPtrs - noPtrsInMod;
				(* delete entries in procOffsets *)
				FOR i := pos + noProcsInMod TO numProcs - 1 DO  procOffsets[i - noProcsInMod] := procOffsets[i]  END;
				numProcs := numProcs - noProcsInMod;
				(* adjust startIndex of procOffsets entries greater than those that have been deleted *)
				FOR i := 0 TO numProcs - 1 DO
					IF procOffsets[i].startIndex > oldIndex THEN
						procOffsets[i].startIndex := procOffsets[i].startIndex - noPtrsInMod
					END
				END;
			ELSE  Trace.StringLn( "corrupt global procOffsets table" );  HALT( 2000 )
			END
		END
	END DeleteProcOffsets;

	PROCEDURE DeAllocCodeBlock( p: Address );
	BEGIN
		Unix.free( p - 24 )
	END DeAllocCodeBlock;


	(* Generate a module file name. *)
	PROCEDURE GetFileName( CONST name, extension: ARRAY OF CHAR;  VAR fileName: ARRAY OF CHAR );
	VAR i, j: LONGINT;
	BEGIN
		i := 0;
		WHILE name[i] # 0X DO  fileName[i] := name[i];  INC( i )  END;
		j := 0;
		WHILE extension[j] # 0X DO  fileName[i] := extension[j];  INC( i );  INC( j )  END;
		fileName[i] := 0X
	END GetFileName;

	(** Append string from to to, truncating on overflow. *)
	PROCEDURE Append*( CONST src: ARRAY OF CHAR;  VAR dest: ARRAY OF CHAR );
	VAR i, j, m: LONGINT;
	BEGIN
		j := 0;
		WHILE dest[j] # 0X DO  INC( j )  END;
		m := LEN( dest ) - 1;  i := 0;
		WHILE (src[i] # 0X) & (j # m) DO  dest[j] := src[i];  INC( i );  INC( j )  END;
		dest[j] := 0X
	END Append;

	(** Add a module to the pool of accessible modules, or return named module. *)
	PROCEDURE Publish*( VAR m: Module;  VAR new: BOOLEAN );
	VAR n: Module;  i: LONGINT;
	BEGIN
		ASSERT( (m.code # NIL ) & (LEN( m.code^ ) > 0) );
		Machine.Acquire( Machine.Modules );
		n := root;
		WHILE (n # NIL ) & (n.name # m.name) DO  n := n.next  END;
		IF n # NIL THEN  (* module with same name exists, return it and ignore new m *)
		 m := n;  new := FALSE
		ELSE
			m.published := TRUE;
			m.next := root;  root := m;
			m.refcnt := 0;
			InsertProcOffsets(m.procTable, m.ptrTable, m.maxPtrs);
			m.procTable := NIL; m.ptrTable := NIL; (* not used any more as entered in global variable *)
			FOR i := 0 TO m.modules - 1 DO  INC( m.module[i].refcnt )  END;
			new := TRUE
		END;
		Machine.Release( Machine.Modules );
	END Publish;

	PROCEDURE CheckModuleName( CONST name: ARRAY OF CHAR ): BOOLEAN;
	VAR i: LONGINT;  ch: CHAR;
	BEGIN
		i := 0;
		WHILE name[i] # 0X DO
			ch := name[i];
			IF ~(((CAP( ch ) >= "A") & (CAP( ch ) <= "Z")) OR ((i > 0) & (ch >= '0') & (ch <= '9')) OR (ch = "-")) THEN  RETURN FALSE   END;
			INC( i )
		END;
		RETURN TRUE
	END CheckModuleName;

	(** Load the module if it is not already loaded. *)  (* Algorithm J. Templ, ETHZ, 1994 *)

	PROCEDURE ThisModule*( CONST name: ARRAY OF CHAR;  VAR res: LONGINT;  VAR msg: ARRAY OF CHAR ): Module;
	TYPE Body = PROCEDURE;
	VAR m, p: Module;
		fileName: ARRAY 64 OF CHAR;
		body: Body;  new: BOOLEAN;  i: LONGINT;
	BEGIN
		res := 0;  msg[0] := 0X;
		IF ~CheckModuleName( name ) THEN
			res := 6;   (* module not found *)
			COPY( "module '", msg );  Append( name, msg );  Append( "' not found", msg );  RETURN NIL
		END;
		m := ModuleByName( name );
		IF m = NIL THEN
			i := 0;  INC( llev );
			IF 0 IN debug THEN  trace( name, "" )  END;
			REPEAT
				GetFileName( name, extension[i], fileName );
				m := loader[i]( name, fileName, res, msg );  INC( i );
			UNTIL (i = numLoaders) OR (m # NIL );
			IF (m = NIL ) & (0 IN debug) THEN
				Trace.String( name );  Trace.String( ": loading failed: " );  Trace.StringLn( msg )
			END;
			IF (m # NIL ) & ~m.published THEN  (* no race on m.published, as update is done below in Publish *)
				p := m;  Publish( m, new );
				IF new THEN  (* m was successfully published *)
					IF 0 IN debug THEN
						trace( name, ".body " );  Trace.Ln
					END;
					body := S.VAL( Body, S.ADR( m.code[0] ) );
					body;
					res := 0;  msg[0] := 0X;
					m.initialized := TRUE;   (* allow ThisCommand *)
				ELSE
					(* m was part of cycle, replaced by existing module *)
				END
			END;
			DEC( llev );
		END;
		RETURN m
	END ThisModule;

	(** Return the module that contains code address pc or NIL if not found.  Can also return freed modules. *)

	PROCEDURE ThisModuleByAdr*( pc: LONGINT ): Module;
	VAR m: Module;  cbase, dbase, i: LONGINT;  found: BOOLEAN;
	BEGIN
		Machine.Acquire( Machine.Modules );
		i := 0;  found := FALSE;
		REPEAT
			CASE i OF
			| 0:       m := root
			| 1:       m := freeRoot
			END;
			WHILE (m # NIL ) & ~found DO
				cbase := S.ADR( m.code[0] );  dbase := S.ADR( m.data[0] );
				(* include 1 byte after module in module, therefore <= below *)
				IF (cbase <= pc) & (pc <= cbase + LEN( m.code^ )) THEN  found := TRUE
				ELSIF (dbase <= pc) & (pc <= dbase + LEN( m.data^ )) THEN  found := TRUE
				ELSE  m := m.next
				END
			END;
			INC( i )
		UNTIL found OR (i = 1 (*2*)); (*	don't use freeRoot in Unix ports,
										deref m.code causes segm. violation! *)
		Machine.Release( Machine.Modules );
		RETURN m
	END ThisModuleByAdr;

	PROCEDURE FindCommand( m: Module;  CONST name: ARRAY OF CHAR;  VAR cmd: Command );
	VAR i: LONGINT;  found: BOOLEAN;
	BEGIN
		ASSERT( m.initialized );   (* module body must have been called (see note at end of module) *)
		Machine.Acquire( Machine.Modules );
		i := 0;  found := FALSE;
		WHILE ~found & (i # LEN( m.command^ )) DO
			IF m.command[i].name = name THEN  found := TRUE;  cmd := m.command[i]  ELSE  INC( i )  END
		END;
		IF ~found THEN  cmd.argTdAdr := 0;  cmd.retTdAdr := 0;  cmd.entryAdr := 0  END;
		Machine.Release( Machine.Modules )
	END FindCommand;


	(** Return the named module or NIL if it is not loaded yet. *)

	PROCEDURE ModuleByName*( CONST name: ARRAY OF CHAR ): Module;
	VAR m: Module;
	BEGIN
		Machine.Acquire( Machine.Modules );
		m := root;
		WHILE (m # NIL ) & (m.name # name) DO  m := m.next  END;
		Machine.Release( Machine.Modules );
		RETURN m
	END ModuleByName;

	(** Return the named command. *)
	PROCEDURE ThisCommand*( m: Module;  CONST name: ARRAY OF CHAR ): CommandProc;
	VAR cmd: Command;
	BEGIN
		FindCommand( m, name, cmd );
		IF (cmd.entryAdr # 0) & (cmd.argTdAdr = 0) & (cmd.retTdAdr = 0) THEN
			RETURN S.VAL( CommandProc, cmd.entryAdr )
		ELSE  RETURN NIL
		END
	END ThisCommand;

	(** Return the named parameterized command. *)
	PROCEDURE ThisCommandPar*( m: Module;  CONST name: ARRAY OF CHAR ): CommandParProc;
	VAR cmd: Command;
	BEGIN
		FindCommand( m, name, cmd );  RETURN S.VAL( CommandParProc, cmd.entryAdr )
	END ThisCommandPar;

	(** Return the CommandParProc of a command given by a string in the format <module>.<command>
		returns NIL if either the Module or the CommandParProc is not found *)
	PROCEDURE GetCommandByString*( cmd: ARRAY OF CHAR ): CommandParProc;
	VAR i, n, res: LONGINT;
		msg: ARRAY 64 OF CHAR;
		m: Module;
	BEGIN
		i := 0;
		WHILE (cmd[i] # 0X) & (cmd[i] # ".") DO  INC( i )  END;
		IF cmd[i] = "." THEN
			cmd[i] := 0X;  m := ThisModule( cmd, res, msg );
			IF m # NIL THEN
				INC( i );  n := i;
				WHILE cmd[i] # 0X DO  cmd[i - n] := cmd[i];  INC( i )  END;
				cmd[i - n] := 0X;  RETURN ThisCommandPar( m, cmd )
			END
		END;
		RETURN NIL
	END GetCommandByString;

	PROCEDURE Shutdown*( scode: LONGINT );
	VAR m: Module;  term: TerminationHandler;
	BEGIN
		IF scode # None THEN
			LOOP
				Machine.Acquire( Machine.Modules );
				m := root;
				WHILE (m # NIL ) & (m.term = NIL ) DO  m := m.next  END;
				IF m # NIL THEN  term := m.term;  m.term := NIL   END;
				Machine.Release( Machine.Modules );
				IF m = NIL THEN  EXIT   END;
				term() (* if this causes exception or hangs, another shutdown call will retry *)
			END;
			(* clean up finalizers *)
			m := root;
			WHILE m # NIL DO
				Heaps.CleanupModuleFinalizers( S.ADR( m.code[0] ), LEN( m.code ), m.name );  m := m.next
			END;
			Machine.Shutdown( FALSE )
		END
	END Shutdown;


	(** Free a module.  The module's termination handler, if any, is called first.
		Then all objects that have finalizers in this module are finalized (even if they are still reachable).
		Then the module's data and code are invalidated. *)

	PROCEDURE FreeModule*( CONST name: ARRAY OF CHAR;  VAR res: LONGINT;  VAR msg: ARRAY OF CHAR );
	VAR p, m, im: Module;  term: Aos.TermHandler;  i: LONGINT;
	BEGIN
		m := ModuleByName( name );
		IF (m # NIL ) & (m.refcnt = 0) THEN  (* will be freed below *)
			IF m.term # NIL THEN  (* call termination handler *)
				term := m.term;  m.term := NIL;  term (* may trap *)
			END;
			Heaps.CleanupModuleFinalizers( S.ADR( m.code[0] ), LEN( m.code^ ), m.name )
		END;
		res := 0;  msg[0] := 0X;
		Machine.Acquire( Machine.Modules );
		p := NIL;  m := root;
		WHILE (m # NIL ) & (m.name # name) DO  p := m;  m := m.next  END;
		IF m # NIL THEN
			IF m.refcnt = 0 THEN  (* free the module *)
				FOR i := 0 TO LEN( m.module ) - 1 DO  im := m.module[i];  DEC( im.refcnt )  END;
				m.initialized := FALSE;   (* disallow ThisCommand *)
				Append( "?", m.name );
				(* move module to free list *)
				IF p = NIL THEN  root := root.next  ELSE  p.next := m.next  END;
				m.next := freeRoot;  freeRoot := m;
				(* clear global pointers and code *)
				FOR i := 0 TO LEN( m.ptrAdr ) - 1 DO  S.PUT( m.ptrAdr[i], NIL )  END;
				(*==== Code resides outside Aos heap =============
				IF ClearCode THEN
					FOR i := 0 TO LEN( m.code^ ) - 1 DO  m.code[i] := 0CCX  END
				END;
				===============*)
				(* remove references to module data *)
				m.published := FALSE;  m.entry := NIL;  m.command := NIL;  m.ptrAdr := NIL;
				(* do not clear m.type or m.module, as old heap block tags might reference type descs indirectly. *)
				(* do not clear m.data or m.code, as they are used in ThisModuleByAdr (for debugging). *)
				(* do not clear m.refs, as they are used in AosTrap (for debugging). *)
				m.module := NIL;  m.export.dsc := NIL;  m.exTable := NIL;
				DeleteProcOffsets( m.firstProc, m.noProcs ) ;
				(*  DeAllocCodeBlock( S.VAL( Address, m.code ) )  *)
			ELSE
				res := 1901;   (* can not free module in use *)
				COPY( name, msg );  Append( " reference count not zero", msg )
			END
		ELSE
			res := 1902;   (* module not found *)
			COPY( name, msg );  Append( " not found", msg )
		END;
		Machine.Release( Machine.Modules )
	END FreeModule;


	(** Install a procedure to be called before a module is freed from memory,
		or before the Oberon system terminates.
		The termination handler  is associated with the module where it is located *)

	PROCEDURE InstallTermHandler*( h: TerminationHandler );
	VAR m: Module;
	BEGIN
		m := ThisModuleByAdr( S.VAL( Address, h ) );
		IF m # NIL THEN
			 m.term := h (* overwrite existing handler, if any *)
		END
	END InstallTermHandler;


(** Return the named type. *)
	PROCEDURE ThisType*( m: Module;  CONST name: ARRAY OF CHAR ): TypeDesc;
	VAR i: LONGINT;  type: TypeDesc;
	BEGIN
		Machine.Acquire( Machine.Modules );
		i := 0;
		WHILE (i < LEN( m.typeInfo ))& (m.typeInfo[i].name # name)  DO INC( i )  END;
		IF i = LEN( m.typeInfo ) THEN  type := NIL
		ELSE type := m.typeInfo[i]
		END;
		Machine.Release( Machine.Modules );
		RETURN type
	END ThisType;


	(** Return the type with the specified tag address. (UNSAFE) *)
	PROCEDURE ThisTypeByAdr*( adr: LONGINT;  VAR m: Module;  VAR t: TypeDesc );
	BEGIN
		IF (adr # 0) & (adr MOD 16 = 8) THEN
			Machine.Acquire( Machine.Modules );
			S.GET( adr - 4, adr );  t := S.VAL( TypeDesc, adr );
			S.GET( adr + ModOfs, m );   (* this is only correct if we never free modules *)
			Machine.Release( Machine.Modules )
		ELSE  m := NIL;  t := NIL
		END
	END ThisTypeByAdr;

	(** create a new object given its type descriptor *)
	PROCEDURE NewObj*( t: TypeDesc ): ANY;
	VAR x: ANY;
	BEGIN
		Heaps.NewRec( x, t.tag, FALSE );  RETURN x;
	END NewObj;

	(** return the type descriptor of an object *)
	PROCEDURE TypeOf*( obj: ANY ): TypeDesc;
	VAR m: Module;  t: TypeDesc;  adr: LONGINT;
	BEGIN
		S.GET( S.VAL( LONGINT, obj ) - 4, adr );  ThisTypeByAdr( adr, m, t );  RETURN t;
	END TypeOf;


	(* Is this PC handled in the corresponding module. deep = scan the whole stack. *)
	PROCEDURE IsExceptionHandled*( VAR pc, fp: LONGINT;  deep: BOOLEAN ): BOOLEAN;
	VAR handler: LONGINT;
	BEGIN
		IF deep THEN
			handler := GetExceptionHandler( pc );
			IF handler # -1 THEN  (* Handler in the current PAF *)
			 RETURN TRUE
			ELSE
				WHILE (fp # 0) & (handler = -1) DO
					S.GET( fp + 4, pc );
					pc := pc - 1;   (*  CALL instruction, machine dependant!!! *)
					handler := GetExceptionHandler( pc );
					S.GET( fp, fp ) (* Unwind PAF *)
				END;
				IF handler = -1 THEN  RETURN FALSE   ELSE  pc := handler;  RETURN TRUE   END
			END
		ELSE  RETURN GetExceptionHandler( pc ) # -1
		END
	END IsExceptionHandled;


	(* Is this PC handled in the corresponding module. If the PC is handled the PC of the
		handler is return else -1 is returned. There is no problem concurrently accessing this
		procedure, there is only reading work. *)
	PROCEDURE GetExceptionHandler*( pc: LONGINT ): LONGINT;
	VAR m: Module;

		PROCEDURE BinSearch( exTable: Aos.ExceptionTable;  key: LONGINT ): LONGINT;
		VAR x, l, r: LONGINT;
		BEGIN
			l := 0;  r := LEN( exTable ) - 1;
			REPEAT
				x := (l + r) DIV 2;
				IF key < exTable[x].pcFrom THEN  r := x - 1  ELSE  l := x + 1  END;
			UNTIL ((key >= exTable[x].pcFrom) & (key < exTable[x].pcTo)) OR (l > r);
			IF (key >= exTable[x].pcFrom) & (key < exTable[x].pcTo) THEN  RETURN exTable[x].pcHandler;   ELSE  RETURN -1;   END
		END BinSearch;

	BEGIN
		m := ThisModuleByAdr( pc );
		IF (m # NIL ) & (m.exTable # NIL ) & (m.exTableLen > 0) THEN  RETURN BinSearch( m.exTable, pc )  END;
		RETURN -1;
	END GetExceptionHandler;

	PROCEDURE GetKernelProc*( num: LONGINT ): Address;
	VAR adr: Address;
	BEGIN
		adr := kernelProc[253 - num];
		ASSERT( adr # 0 );
		RETURN adr
	END GetKernelProc;


	PROCEDURE MarkModules;
	VAR m: Module;  i: LONGINT;  ptr: Address;
	BEGIN
		IF traceGC  THEN  Trace.String( "mark modules: " )  END;
		m := root;
		WHILE m # NIL DO
			IF m.published THEN
				IF traceGC  THEN  Trace.Char( '.' )   END;
				FOR i := 0 TO m.pointers -1 DO
					S.GET( m.ptrAdr[i], ptr );
					IF ptr # 0 THEN  Heaps.Mark( ptr )  END
				END
			END;

			Heaps.Mark( S.VAL( Address, m ) );
			m := m.next;
		END;
		IF traceGC  THEN  Trace.Ln  END
	END MarkModules;


	PROCEDURE Init;
	VAR
		newRec: PROCEDURE ( VAR p: ANY;  tag: Address;  isRealtime: BOOLEAN );
		newSys: PROCEDURE ( VAR p: ANY;  size: Size;  isRealTimr: BOOLEAN );
		newArr: PROCEDURE ( VAR p: ANY;  eltag: Address;  nofelem, nofdim: Size;  isRealtime: BOOLEAN );
		getProcedure: PROCEDURE ( CONST m, p: ARRAY OF CHAR;  argTdAdr, retTdAdr: Address;  VAR entryAdr: Address );
	BEGIN
		newArr := Heaps.NewArr;
		newSys := Heaps.NewSys;
		newRec := Heaps.NewRec;
		getProcedure := GetProcedure;
		kernelProc[0] := S.VAL (Address, newRec);	(* 253 *)
		kernelProc[1] := S.VAL (Address, newSys);	(* 252 *)
		kernelProc[2] := S.VAL (Address, newArr);	(* 251 *)
		kernelProc[3] := 0;	(* 250 *)
		kernelProc[4] := 0;	(* 249 *)
		kernelProc[5] := 0;	(* 248 *)
		kernelProc[6] := 0;	(* 247 *)
		kernelProc[7] := 0;	(* 246 *)
		kernelProc[8] := 0;	(* 245 *)
		kernelProc[9] := 0;	(* 244 *)
		kernelProc[10] := S.VAL(Address, getProcedure);	(* 243 *)
		(* Kernel0.SetKernelProc( 10, S.VAL( Address, getProcedure ) );   (* 243 *)===*)

		root := Glue.modules;

		traceLoad := 0 IN Glue.debug;
		traceGC := 1 IN Glue.debug;
		debug := Glue.debug;  llev := 1;
		numLoaders := 0;

		Heaps.findRootsInModules := MarkModules;
		NEW( procOffsets, InitTableLen );
		NEW( ptrOffsets, InitPtrTableLen );
	END Init;

BEGIN
	Init;
END Modules.