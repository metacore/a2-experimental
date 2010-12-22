MODULE BootConsole;

IMPORT S := SYSTEM, Trace, Glue, Unix, Machine, Modules, Loader, Commands;

TYPE
	Module = Modules.Module;
	CommandProc = PROCEDURE;

	CommandThread = OBJECT
		BEGIN {ACTIVE}
			Execute( modName, cmdName );
			Modules.Shutdown( Modules.Reboot )
		END CommandThread;

VAR
	modName, cmdName: ARRAY 32 OF CHAR;
	appl{UNTRACED}: CommandThread;


	PROCEDURE LoadModule( CONST name: ARRAY OF CHAR );
	VAR
		m: Module;  res: LONGINT;  msg: ARRAY 256 OF CHAR;
	BEGIN
		m := Modules.ThisModule( name, res, msg );
		IF m = NIL THEN
			Trace.String( "could not load module " );  Trace.String( name );  Trace.Ln
		END
	END LoadModule;



	PROCEDURE Command( CONST cmd: ARRAY OF CHAR );
	VAR
		res: LONGINT;
		s: ARRAY 256 OF CHAR;
	BEGIN
		Commands.Call( cmd, {}, res, s );
		IF res # 0 THEN  Trace.String( s ); Trace.Ln  END
	END Command;


	(** Return the named command. *)
	PROCEDURE ThisCommand( m: Module;  CONST name: ARRAY OF CHAR ): CommandProc;
	VAR cmd: Modules.Command; i: LONGINT;  found: BOOLEAN;
	BEGIN		
		i := 0;  found := FALSE;
		WHILE ~found & (i # LEN( m.command^ )) DO
			IF m.command[i].name = name THEN  found := TRUE;  cmd := m.command[i]  ELSE  INC( i )  END
		END;
		IF (cmd.entryAdr # 0) & (cmd.argTdAdr = 0) & (cmd.retTdAdr = 0) THEN
			RETURN S.VAL( CommandProc, cmd.entryAdr )
		ELSE  
			RETURN NIL
		END
	END ThisCommand;

	PROCEDURE Execute( CONST modName, procName: ARRAY OF CHAR );
	VAR m: Module;  cmd: CommandProc;  res: LONGINT;
		msg: ARRAY 256 OF CHAR;
	BEGIN
		m := Modules.ThisModule( modName, res, msg );
		IF m # NIL THEN
			cmd := ThisCommand( m, procName );
			IF cmd # NIL THEN  cmd
			ELSE
				Trace.String( "Starter.Execute:  module " );  Trace.String( modName );
				Trace.String( " has no command named " );  Trace.String( procName );  Trace.Ln;
			END
		ELSE  Trace.String( "Starter.Execute:  could not load module " );  Trace.String( modName );  Trace.Ln
		END
	END Execute;


	PROCEDURE getCmd( ): BOOLEAN;
	VAR cmd: ARRAY 64 OF CHAR;
		i, j, k: INTEGER;  c: CHAR;
	BEGIN
		Unix.GetArgval( "-x", cmd );
		IF cmd = "" THEN  RETURN FALSE
		ELSE
			i := 0;
			REPEAT  c := cmd[i];  modName[i] := c;  INC( i )
			UNTIL ~(("a" <= c) & (c <= "z") OR ("A" <= c) & (c <= "Z"));
			IF (c = '.') & (i > 1) THEN
				modName[i - 1] := 0X;  j := i;  k := 0;
				REPEAT  c := cmd[j];  cmdName[k] := c;  INC( j );  INC( k )
				UNTIL ~(("a" <= c) & (c <= "z") OR ("A" <= c) & (c <= "Z"));
				cmdName[k - 1] := 0X;
				IF k > 1 THEN  RETURN TRUE  END
			END  ;
			Trace.String( "bad command line parameter: -x " );  Trace.String( cmd );  Trace.Ln;
			RETURN FALSE
		END;
	END getCmd;
	
	PROCEDURE InitPrelinkedModules;
	TYPE Body = PROCEDURE;
	VAR m: Modules.Module;  body: Body; traceEnabled: BOOLEAN;
	BEGIN
		m := Modules.root;  traceEnabled := FALSE;
		LOOP
			IF m.name = "BootConsole" THEN  EXIT   END;   (* initialize modules belonging to bootfile only *)
			IF (Glue.debug # {}) & traceEnabled THEN
				Trace.String( "Initializing " );  Trace.StringLn( m.name )
			END;
			body := S.VAL( Body, S.ADR( m.code[0] ) );
			body;	
			IF m.name = "Glue" THEN  traceEnabled := TRUE  END;
			m := m.next
		END
	END InitPrelinkedModules;


	PROCEDURE StartSystem;
	BEGIN
		IF getCmd()  THEN
			(* start the procedure specified in the command line (aos  -x M.P) *)
			IF Glue.debug # {} THEN
				Trace.String( "Starting " );
				Trace.String( modName );  Trace.Char( "." );  Trace.String( cmdName );
				Trace.Ln
			END;
			NEW( appl )
		ELSE
			(* normal system start *)
			LoadModule( "Clock" );
			Execute( "XDisplay",  "Install" );
			Execute( "KbdMouse",  "Init" );


			Command( "WindowManager.Install" );
			Command( "DisplayRefresher.Install" );

			Command( "Autostart.Run" );
		END
	END StartSystem;



BEGIN
	InitPrelinkedModules;
	Modules.AddLoader( Machine.DefaultObjectFileExtension, Loader.LoadObj );
	Execute( "UnixFiles",  "Install" );
	StartSystem;
	Machine.AwaitShutdown;
END BootConsole.


