MODULE HierarchicalProfiler0; (** AUTHOR "staubesv"; PURPOSE "WinAos platform-specific part of the hierarchical profiler"; *)

IMPORT
	SYSTEM, Kernel32, Objects, Modules, ProcessInfo;

CONST
	Initialized = 0;
	Running = 1;
	Terminating = 2;
	Terminated = 3;

	Intervall = 1; (* milliseconds *)

TYPE

	Callback = PROCEDURE (id : LONGINT; process : Objects.Process; pc, bp : SYSTEM.ADDRESS);

	Poller = OBJECT
	VAR
		processes : ARRAY ProcessInfo.MaxNofProcesses OF Objects.Process;
		nofProcesses : LONGINT;
		me : Objects.Process;
		state : LONGINT;

		PROCEDURE &Init;
		BEGIN
			state := Running;
		END Init;

		PROCEDURE Terminate;
		BEGIN {EXCLUSIVE}
			IF (state # Terminated) THEN state := Terminating; END;
			AWAIT(state = Terminated);
		END Terminate;

		PROCEDURE Process;
		VAR i : LONGINT;
		BEGIN
			ProcessInfo.GetProcesses(processes, nofProcesses);
			FOR i := 0 TO nofProcesses - 1 DO
				IF (processes[i] # me) THEN
					HandleProcess(processes[i]);
				END;
			END;
			ProcessInfo.Clear(processes);
		END Process;

	BEGIN {ACTIVE, PRIORITY(Objects.Realtime)}
		me := Objects.CurrentProcess();
		LOOP
			WHILE (state = Running) DO
				Process;
				Kernel32.Sleep(Intervall);
			END;
			IF (state = Terminating) THEN EXIT; END;
		END;
		BEGIN {EXCLUSIVE} state := Terminated; END;
	END Poller;

VAR
	poller : Poller;
	callback : Callback;
	state : LONGINT;

PROCEDURE HandleProcess(process : Objects.Process);
VAR context : Kernel32.Context; id : LONGINT; res : Kernel32.BOOL;
BEGIN
	ASSERT(process # NIL);
	ASSERT(process.handle # Kernel32.InvalidHandleValue);
	res := Kernel32.SuspendThread(process.handle);
	IF (res # -1) THEN
		context.ContextFlags := Kernel32.ContextControl;
		res := Kernel32.GetThreadContext(process.handle, context);
		IF (res = Kernel32.True) THEN
			id := 1;
			IF (context.PC # 0) THEN
				callback(id, process, context.PC, context.BP);
			END;
		END;
		res := Kernel32.ResumeThread(process.handle);
	END;
END HandleProcess;

PROCEDURE Enable*(proc : Callback);
BEGIN {EXCLUSIVE}
	ASSERT(proc # NIL);
	ASSERT((state = Initialized) & (poller = NIL));
	callback := proc;
	NEW(poller);
	state := Running;
END Enable;

PROCEDURE Disable*;
BEGIN {EXCLUSIVE}
	ASSERT((state = Running) & (poller # NIL));
	poller.Terminate;
	poller := NIL;
	state := Initialized;
END Disable;

PROCEDURE Cleanup;
BEGIN
	IF (poller # NIL) THEN poller.Terminate; poller := NIL; END;
END Cleanup;

BEGIN
	state := Initialized;
	Modules.InstallTermHandler(Cleanup);
END HierarchicalProfiler0.
