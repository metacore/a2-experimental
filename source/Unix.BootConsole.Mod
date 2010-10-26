MODULE BootConsole;

IMPORT Trace, Glue, Unix, Machine, Modules, Objects, Loader, Commands;

TYPE
	Module = Modules.Module;
	CommandProc = Modules.CommandProc;

	CommandThread = OBJECT
		BEGIN {ACTIVE}
			Execute( modName, cmdName );
			Modules.Shutdown( Modules.Reboot )
		END CommandThread;

VAR
	modName, cmdName: ARRAY 32 OF CHAR;
	appl: CommandThread;


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


	PROCEDURE Execute( CONST modName, procName: ARRAY OF CHAR );
	VAR m: Module;  cmd: CommandProc;  res: LONGINT;
		msg: ARRAY 256 OF CHAR;
	BEGIN
		m := Modules.ThisModule( modName, res, msg );
		IF m # NIL THEN
			cmd := Modules.ThisCommand( m, procName );
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

			Glue.systemIsUp := TRUE;

			Command( "Autostart.Run" );
		END
	END StartSystem;



BEGIN
	Modules.AddLoader( Machine.DefaultObjectFileExtension, Loader.LoadObj );
	Execute( "UnixFiles",  "Install" );
	StartSystem;
	LOOP (* idle *)
		Objects.Sleep( 100 );
		IF Glue.systemTerminating THEN  EXIT  END;
	END
END BootConsole.


