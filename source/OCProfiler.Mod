MODULE OCProfiler; (** AUTHOR "fof"; PURPOSE "minimal implementation of a compiler supported profiler"; *)

IMPORT KernelLog,Objects,Machine,SYSTEM,Streams,Kernel;

CONST
	Trace=FALSE;

	MaxModules=256;
	MaxProcesses=256;
	MaxStackSize=4096;

TYPE
	Procedure= RECORD
		name: ARRAY 64 OF CHAR;
		calls: LONGINT;
		time: HUGEINT;
	END;
	Procedures= POINTER TO ARRAY OF Procedure;
	Modules= ARRAY MaxModules OF Procedures;

	HashEntryInt = RECORD
		used: BOOLEAN; key, value: LONGINT;
	END;
	HashIntArray = ARRAY 2*MaxProcesses OF HashEntryInt;

	Process=POINTER TO RECORD
		position: LONGINT;
		time: ARRAY MaxStackSize OF HUGEINT;
		correcture : ARRAY MaxStackSize OF HUGEINT;
	END;


VAR
	(* modules *)
	module:Modules;
	numberModules: LONGINT;
	(* process hash table *)
	table: HashIntArray;
	used: LONGINT;
	processes: ARRAY MaxProcesses OF Process;
	(* logging *)
	log: Streams.Writer;
	(* timing *)
	frequency: LONGREAL; n: LONGINT;
	stackOverflow, maxStackSize: LONGINT;

	PROCEDURE Put*(key, value: LONGINT);
	VAR hash: LONGINT;
	BEGIN
		ASSERT(used < LEN(table),5000);
		hash := HashValue(key);
		IF ~table[hash].used THEN
			INC(used, 1);
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

	PROCEDURE GetProcess(): LONGINT;
	VAR process: ANY; value: LONGINT; key: SYSTEM.ADDRESS;
	BEGIN
		process := Objects.CurrentProcess();
		key := SYSTEM.VAL(SYSTEM.ADDRESS,process) DIV SYSTEM.SIZEOF(SYSTEM.ADDRESS);
		IF Has(key) THEN
			value := Get(key)
		ELSE
			BEGIN{EXCLUSIVE}
				value := used;
				NEW(processes[value]);
				Put(key,value);
			END;
		END;
		RETURN value
	END GetProcess;

	PROCEDURE AddModule*(VAR moduleId: LONGINT; procedures: LONGINT; CONST name: ARRAY OF CHAR);
	BEGIN
		IF Trace THEN
			log.String("Add Module: "); log.String(name); log.String(", #procs: "); log.Int(procedures,1);
			log.String(", id: "); log.Int(numberModules,1); log.Ln; log.Update;
		END;
		moduleId := numberModules; NEW(module[moduleId],procedures);
		INC(numberModules);
	END AddModule;

	PROCEDURE AddProcedure*(moduleId, procedureId: LONGINT; CONST name: ARRAY OF CHAR);
	BEGIN
		IF Trace THEN
			log.String("Add procedure: "); log.String(name); log.String(": "); log.Int(moduleId,1); log.String(","); log.Int(procedureId,1); log.Ln; log.Update;
		END;
		COPY(name,module[moduleId,procedureId].name);
		module[moduleId,procedureId].calls := 0;
	END AddProcedure;

	PROCEDURE EnterProcedure*(moduleId, procedureId: LONGINT);
	VAR position,p: LONGINT; localTime: HUGEINT;
	BEGIN
		localTime:= Machine.GetTimer();
		IF Trace THEN
			log.String("Enter procedure: "); log.Int(moduleId,1); log.String(", "); log.Int(procedureId,1); log.Ln; log.Update;
		END;
		INC(module[moduleId,procedureId].calls);
		p := GetProcess();
		position := processes[p].position;
		IF position < MaxStackSize THEN
			processes[p].time[position] := localTime;
			processes[p].correcture[position] := Machine.GetTimer()-localTime;
		ELSE INC(stackOverflow); IF position > maxStackSize THEN maxStackSize := position END;
		END;
		INC(processes[p].position);
	END EnterProcedure;

	PROCEDURE ExitProcedure*(moduleId, procedureId: LONGINT);
	VAR time: HUGEINT; position,p: LONGINT; localTime: HUGEINT;
	BEGIN
		localTime:= Machine.GetTimer();
		IF Trace THEN
			log.String("Exit procedure: "); log.Int(moduleId,1); log.String(", "); log.Int(procedureId,1); log.Ln;
		END;
		p := GetProcess();
		DEC(processes[p].position);
		position := processes[p].position;
		IF position < MaxStackSize THEN
			time := Machine.GetTimer()-processes[p].time[position];
			INC(module[moduleId,procedureId].time,time);
			INC(processes[p].correcture[position], Machine.GetTimer()-localTime);
			DEC(module[moduleId,procedureId].time,processes[p].correcture[position]);
			IF position > 0 THEN
				INC(processes[p].correcture[position-1], processes[p].correcture[position]);
			END;
		END;
	END ExitProcedure;

	PROCEDURE Init*;
	VAR i: LONGINT;
	BEGIN
		FOR i := 0 TO LEN(module)-1 DO	module[i] := NIL	END;
		FOR i := 0 TO LEN(table)-1 DO table[i].used := FALSE END;
		numberModules := 0;
		used := 0;
		stackOverflow := 0;
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

	PROCEDURE Report*;
	VAR i,j: LONGINT;
	BEGIN
		FOR i := 0 TO numberModules-1 DO
			FOR j := 0 TO LEN(module[i])-1 DO
				log.String(module[i,j].name); log.String(":"); log.Int(module[i,j].calls,1);
				log.String(", time (s): "); log.Float(SHORT(module[i,j].time / frequency ),20);
				log.Ln;log.Update;
			END;
		END;
		log.String("overflows: "); log.Int(stackOverflow,1); log.Ln;
		log.String("maxStackSize: "); log.Int(maxStackSize,1); log.Ln;

		log.Update
	END Report;

BEGIN Streams.OpenWriter( log, KernelLog.Send ); Calibrate;  Init;
END OCProfiler.


