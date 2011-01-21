MODULE OCProfiler; (** AUTHOR "fof"; PURPOSE "minimal implementation of a compiler supported profiler"; *)

IMPORT KernelLog,Objects,Machine,SYSTEM,Streams,Kernel,Commands;

CONST
	Trace=FALSE;
	MaxModules=256;
	MaxProcedures=256;
	MaxProcesses=256;
	MaxStackSize=256;

TYPE
	Name = ARRAY 64 OF CHAR;
	Procedures = POINTER TO ARRAY OF Name;
	Modules= ARRAY MaxModules OF Procedures;

	ProcedureTime= RECORD
		calls:LONGINT;
		time: HUGEINT
	END;
	ProcedureTimes= ARRAY MaxProcedures OF ProcedureTime;

	Process= OBJECT
	VAR
		stackPosition: LONGINT;
		time, correcture: ARRAY MaxStackSize OF HUGEINT;
		modules: ARRAY MaxModules OF ProcedureTimes;

		PROCEDURE &Init;
		VAR i,j: LONGINT;
		BEGIN
			stackPosition := 0;
			FOR i := 0 TO LEN(modules)-1 DO
				FOR j := 0 TO LEN(modules[i])-1 DO
					modules[i,j].calls := 0;
				END;
			END;
		END Init;

		PROCEDURE Enter(moduleId, procedureId: LONGINT; enterTime: HUGEINT);
		BEGIN
			IF stackPosition < MaxStackSize THEN
				time[stackPosition] := enterTime;
				correcture[stackPosition] := Machine.GetTimer()-enterTime;
			END;
			IF (moduleId < MaxModules) & (procedureId < MaxProcedures) THEN
				INC(modules[moduleId,procedureId].calls);
			END;
			INC(stackPosition);
		END Enter;

		PROCEDURE Exit(moduleId, procedureId: LONGINT; enterTime: HUGEINT);
		BEGIN
			DEC(stackPosition);
			IF stackPosition < MaxStackSize THEN
				INC(correcture[stackPosition], Machine.GetTimer()-enterTime);
				IF (moduleId < MaxModules) & (procedureId < MaxProcedures) THEN
					INC(modules[moduleId,procedureId].time,Machine.GetTimer()-time[stackPosition]-correcture[stackPosition]);
				END;
				IF stackPosition > 0 THEN
					INC(correcture[stackPosition-1], correcture[stackPosition]);
				END;
			END;
		END Exit;

	END Process;

	HashEntryInt = RECORD
		used: BOOLEAN; key, value: LONGINT;
	END;
	HashIntArray = ARRAY 2*MaxProcesses OF HashEntryInt


VAR
	(* modules *)
	modules:Modules;
	numberModules: LONGINT;
	(* process hash table *)
	table: HashIntArray;
	numberProcesses: LONGINT;
	processes: ARRAY MaxProcesses OF Process;
	(* logging *)
	log: Streams.Writer;
	(* timing *)
	frequency: LONGREAL; n: LONGINT;

	PROCEDURE Put*(key, value: LONGINT);
	VAR hash: LONGINT;
	BEGIN
		ASSERT(numberProcesses < LEN(table),5000);
		hash := HashValue(key);
		IF ~table[hash].used THEN
			INC(numberProcesses, 1);
		ELSE
			ASSERT(table[hash].key = key,5001);
		END;
		table[hash].key := key;
		table[hash].value := value;
	END Put;

	PROCEDURE Get*(key: LONGINT):LONGINT;
	BEGIN
		RETURN table[HashValue(key)].value;
	END Get;

	PROCEDURE Has*(key: LONGINT):BOOLEAN;
	BEGIN
		RETURN table[HashValue(key)].key = key;
	END Has;

	PROCEDURE HashValue(key: LONGINT):LONGINT;
	VAR value, h1, h2, i: LONGINT;
	BEGIN
		value :=key;
		i := 0;
		h1 := value MOD LEN(table);
		h2 := 1; (* Linear probing *)
		REPEAT
			value := (h1 + i*h2) MOD LEN(table);
			INC(i);
		UNTIL((~table[value].used) OR (table[value].key = key) OR (i >= LEN(table)));
		ASSERT(i<LEN(table),5002);
		RETURN value;
	END HashValue;

	PROCEDURE GetProcess(): Process;
	VAR process: ANY; value: LONGINT; key: SYSTEM.ADDRESS;
	BEGIN
		process := Objects.CurrentProcess();
		key := SYSTEM.VAL(SYSTEM.ADDRESS,process) DIV SYSTEM.SIZEOF(SYSTEM.ADDRESS);
		IF Has(key) THEN
			value := Get(key)
		ELSE
			BEGIN{EXCLUSIVE}
				value := numberProcesses;
				NEW(processes[value]);
				Put(key,value);
			END;
		END;
		RETURN processes[value]
	END GetProcess;

	PROCEDURE AddModule*(VAR moduleId: LONGINT; procedures: LONGINT; CONST name: ARRAY OF CHAR);
	BEGIN
		IF Trace THEN
			log.String("Add Module: "); log.String(name); log.String(", #procs: "); log.Int(procedures,1);
			log.String(", id: "); log.Int(numberModules,1); log.Ln; log.Update;
		END;
		moduleId := numberModules; NEW(modules[moduleId],procedures);
		INC(numberModules);
	END AddModule;

	PROCEDURE AddProcedure*(moduleId, procedureId: LONGINT; CONST name: ARRAY OF CHAR);
	BEGIN
		IF Trace THEN
			log.String("Add procedure: "); log.String(name); log.String(": "); log.Int(moduleId,1); log.String(","); log.Int(procedureId,1); log.Ln; log.Update;
		END;
		COPY(name,modules[moduleId,procedureId]);
	END AddProcedure;

	PROCEDURE EnterProcedure*(moduleId, procedureId: LONGINT);
	VAR time: HUGEINT; p: Process;
	BEGIN
		time:= Machine.GetTimer();
		IF Trace THEN log.String("Enter procedure: "); log.Int(moduleId,1); log.String(", "); log.Int(procedureId,1); log.Ln; log.Update 	END;
		p := GetProcess();
		p.Enter(moduleId,procedureId,time);
	END EnterProcedure;

	PROCEDURE ExitProcedure*(moduleId, procedureId: LONGINT);
	VAR time: HUGEINT; p: Process;
	BEGIN
		time:= Machine.GetTimer();
		IF Trace THEN log.String("Exit procedure: "); log.Int(moduleId,1); log.String(", "); log.Int(procedureId,1); log.Ln; log.Update END;
		p := GetProcess();
		p.Exit(moduleId, procedureId, time);
	END ExitProcedure;

	PROCEDURE Init*;
	VAR i: LONGINT;
	BEGIN
		FOR i := 0 TO LEN(modules)-1 DO	modules[i] := NIL	END;
		FOR i := 0 TO LEN(table)-1 DO table[i].used := FALSE END;
		numberModules := 0;
		numberProcesses := 0;
	END Init;

	PROCEDURE Calibrate;
	VAR timer: Kernel.MilliTimer;  t: HUGEINT;
	BEGIN
		INC( n );  Kernel.SetTimer( timer, 1000 );  t := Machine.GetTimer();
		WHILE ~Kernel.Expired( timer ) DO END;
		t := Machine.GetTimer() - t;
		log.Ln;  log.String( "Timing reported MHz : " ); log.FloatFix( t / 1000 / 1000, 5, 1,0 );
		log.Ln;  frequency := (frequency * (n - 1) + t) / n;  log.String( "Updated value: " );  log.FloatFix( frequency / 1000 / 1000, 5, 1,0 );
		log.Ln;  log.Update;
	END Calibrate;

	PROCEDURE Report*(context: Commands.Context);
	TYPE
		Record=RECORD
			name: ARRAY 64 OF CHAR;
			calls:LONGINT; time: HUGEINT
		END;
		Records=POINTER TO ARRAY OF Record;
	VAR
		i,j,k: LONGINT; records: Records; time: HUGEINT; calls: LONGINT; recordNumber: LONGINT;
		option: ARRAY 32 OF CHAR;

		PROCEDURE Sort(id: LONGINT);
		(* stupid bubblesort *)
			PROCEDURE Swap;
			VAR temp: Record;
			BEGIN
				temp := records[i]; records[i] := records[j]; records[j] := temp
			END Swap;

		BEGIN
			FOR i := 0 TO LEN(records)-1 DO
				FOR j := i TO LEN(records)-1 DO
					IF (id=0) & (records[j].name < records[i].name) THEN Swap
					ELSIF (id=1) & (records[j].calls < records[i].calls) THEN Swap
					ELSIF (id=2) & (records[j].time < records[i].time) THEN Swap
					END;
				END;
			END;
		END Sort;

	BEGIN
		recordNumber := 0;
		FOR i := 0 TO numberModules-1 DO
			INC(recordNumber, LEN(modules[i]));
		END;
		NEW(records,recordNumber);
		recordNumber := 0;
		FOR i := 0 TO numberModules-1 DO
			FOR j := 0 TO LEN(modules[i])-1 DO
				time := 0; calls := 0;
				FOR k := 0 TO numberProcesses-1 DO
					INC(time, processes[k].modules[i,j].time);
					INC(calls, processes[k].modules[i,j].calls);
				END;
				records[recordNumber].calls := calls;
				records[recordNumber].time := time;
				COPY(modules[i,j],records[recordNumber].name);
				INC(recordNumber)
			END;
		END;

		IF context.arg.GetString(option) THEN
			IF option = "name" THEN Sort(0)
			ELSIF option = "calls" THEN Sort(1)
			ELSIF option = "time" THEN Sort(2)
			END;
		END;

		log.String("---  OCProfiler timing report ----"); log.Ln;
		FOR i := 0 TO LEN(records)-1 DO
			log.String(records[i].name);
			log.String(" calls="); log.Int(records[i].calls,1);
			log.String(", time(s)="); log.Float(records[i].time / frequency,20);
			log.Ln;
		END;
		log.String("---------------------------"); log.Ln;
		log.Update;
	END Report;

BEGIN Streams.OpenWriter( log, KernelLog.Send ); Calibrate;  Init;
END OCProfiler.

OCProfiler.Report ~
OCProfiler.Report time ~
OCProfiler.Report calls ~
OCProfiler.Report name ~


