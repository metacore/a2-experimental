(* ETH Oberon, Copyright 2000 ETH Zuerich Institut fuer Computersysteme, ETH Zentrum, CH-8092 Zuerich.
Refer to the "General ETH Oberon System Source License" contract available at: http://www.oberon.ethz.ch/ *)

MODULE Glue;   (* g.f.  25.2.98 *)	(** non portable *)

(** Interface to the dynamic linker of Unix *)


IMPORT S := SYSTEM, Aos := Basetypes, Trace;

TYPE
	Address = S.ADDRESS;
	Module = Aos.Module;

CONST
	AdrSize = S.SIZEOF( S.ADDRESS );

	B = 32;   (* must be a mutiple of 32 *)
	ProtOfs = B + 16;

VAR
	(* the first variable ("AA...") gets initialized by the bootfile loader *)
	AAgetadr-	: PROCEDURE {C} ( handle: LONGINT;  symbol,  adr: LONGINT );

	dlsym-		: PROCEDURE {C} ( handle: Address;  name: Address; adr: Address );
	dlopen-		: PROCEDURE {C} ( pathname: Address;  mode: LONGINT ): Address;
	dlclose-		: PROCEDURE {C} ( handle: Address );
	cout		: PROCEDURE {C} ( c: CHAR );

	debug-		: SET;	(* value of environment variable  OBERON_DEBUG  *)

	modules-	: Module;   (** prelinked modules *)

	stackBottom-	: Address;


	PROCEDURE Char (c: CHAR );
	BEGIN
		cout( c )
	END Char;


	PROCEDURE GetStackBottom;
	VAR i: LONGINT;
	BEGIN
		stackBottom := S.ADR( i ) + 2*AdrSize;
	END GetStackBottom;


	PROCEDURE CallBodies;
		(* initialize prelinked modules *)
		(* the last one (Starter) will startup the system *)
	TYPE Body = PROCEDURE;
	VAR m, last: Module;  body: Body;  consoleReady: BOOLEAN;
	BEGIN
		last := modules;  consoleReady := FALSE;
		WHILE last.next # NIL DO  last := last.next;   END;

		m := modules;
		LOOP
			IF m.name # "Glue" THEN
				IF debug # {} THEN
					Trace.String( "Glue: Initializing " );  Trace.StringLn( m.name )
				END;
				body := S.VAL( Body, S.ADR( m.code[0] ) );
				body;
				IF m.name = "Trace" THEN  Trace.Char := Char  END;
			END;
			IF m = last THEN  EXIT   END;   (* initialize modules belonging to bootfile only *)
			m := m.next
		END
	END CallBodies;


	PROCEDURE GetPrelinkedModules;
	VAR heapAdr, firstBlock: Address;
	BEGIN
		dlsym( 0, S.ADR( "heapAdr" ), S.ADR( heapAdr ) );
		firstBlock := heapAdr + ((-heapAdr - 4) MOD B);
		modules := S.VAL( Module, firstBlock + 4 + ProtOfs );
	END GetPrelinkedModules;




	PROCEDURE Init;
	BEGIN
		S.MOVE( S.ADR( AAgetadr ), S.ADR( dlsym ), AdrSize );
		dlsym( 0, S.ADR( "dlopen" ), S.ADR( dlopen ) );
		dlsym( 0, S.ADR( "dlclose" ), S.ADR( dlclose ) );
		dlsym( 0, S.ADR( "debug" ), S.ADR( debug ) );
		dlsym( 0, S.ADR( "cout" ), S.ADR( cout ) );
		Trace.Char := Char;
	END Init;

BEGIN
	Init;
	GetStackBottom;
	GetPrelinkedModules;
	CallBodies;
END Glue.
