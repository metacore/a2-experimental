MODULE ProcessInfo0; (** AUTHOR "staubesv"; PURPOSE "Platform-dependent process interface"; *)

IMPORT
	Threads, Objects;

TYPE

	ProcessArray* = ARRAY OF Objects.Process;

PROCEDURE GetProcesses*(VAR array : ProcessArray; VAR nofProcesses : LONGINT);
VAR thread : Threads.Thread; length : LONGINT;
BEGIN
	nofProcesses := 0;
	length := LEN(array);
	thread := Threads.threads;
	WHILE (thread # NIL) & (nofProcesses < length) DO
		IF (thread(Objects.Process).mode # Objects.Terminated) THEN
			array[nofProcesses] := thread(Objects.Process);
			INC(nofProcesses);
		END;
		thread := thread.next;
	END;
END GetProcesses;

PROCEDURE GetProcess*(id : LONGINT) : Objects.Process;
VAR process : Objects.Process; thread : Threads.Thread;
BEGIN
	process := NIL;
	thread := Threads.threads;
	WHILE (thread # NIL) & (process = NIL) DO
		IF thread(Objects.Process).id = id THEN process := thread(Objects.Process); END;
		thread := thread.next;
	END;
	RETURN process;
END GetProcess;

END ProcessInfo0.
