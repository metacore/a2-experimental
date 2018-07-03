(* Runtime environment for Unix *)
(* Copyright (C) Florian Negele *)

MODULE Environment;

IMPORT SYSTEM, Activities, Counters, Unix, Processors, Queues, Trace;

CONST IsNative* = FALSE;

CONST Running* = 0; ShuttingDown* = 1; Rebooting* = 2;

VAR status* := 0: WORD;

PROCEDURE {NORETURN} Abort-;
BEGIN {UNCOOPERATIVE, UNCHECKED}
	IF Activities.GetCurrentActivity () # NIL THEN Activities.TerminateCurrentActivity END;
	Exit (1);
END Abort;

PROCEDURE Shutdown*;
BEGIN {UNCOOPERATIVE, UNCHECKED}
	Trace.StringLn ("system: shutting down...");
	Trace.StringLn ("system: shutting down...");
END Shutdown;

PROCEDURE Reboot*;
BEGIN {UNCOOPERATIVE, UNCHECKED}
	Shutdown;
	ASSERT (CAS (status, ShuttingDown, Rebooting) = ShuttingDown);
END Reboot;

PROCEDURE {NORETURN} Exit- (status: WORD);
BEGIN {UNCOOPERATIVE, UNCHECKED}
	Unix.exit (status);
END Exit;

PROCEDURE GetInit- (n: SIZE; VAR val: LONGINT);
BEGIN val := 0;
END GetInit;

END Environment.
