(* Aos, Copyright 2001, Pieter Muller, ETH Zurich *)

MODULE Objects;   (** AUTHOR "pjm, G.F."; PURPOSE "Active object runtime support"; *)


IMPORT SYSTEM, Trace, Glue, Unix, Machine, Heaps, Modules;

CONST
	ConcurrentGC = TRUE; (* if TRUE then release needs to be compiled with --writeBarriers *)

	(*! Process flags, meaningless in Unix ports !!! *)
	PleaseHalt* = 10;		(* Process requested to Halt itself soon *)
	Unbreakable*= 11;		(* FINALLY shall not catch HALT exception (PleaseHalt is also set) *)
	SelfTermination*=12;	(* Indicates the process has requested to terminate ifself (PleaseHalt is also set) *)
	Preempted* = 27;		(* Has been preempted. *)
	Resistant* = 28;		(* Can only be destroyed by itself *)


	MinPriority*	= Unix.ThreadLow;
	Low*			= Unix.ThreadLow + 1;
	Normal*		= Unix.ThreadNormal;
	High*			= Unix.ThreadHigh - 2;
	GCPriority*	= Unix.ThreadHigh - 1;
	Realtime*	= Unix.ThreadHigh;

	(* Process flag defined by compiler in OPC.CallRecBody *)
	Restart* = 0;	(* Restart/Destroy process on exception *)

	(* Process modes (in UnixAos Running means Running or Ready!) *)
	Unknown* = 0;  Ready* = 1;  Running* = 2;  AwaitingLock* = 3;
	AwaitingCond* = 4;  AwaitingEvent* = 5;  Terminated* = 6;

	Second* = 1000;	(* frequency of ticks increments in Hz *)

	DefaultStacksize = 128*1024;


VAR
	(* timer *)
	timerActivity		: TimerActivity;
	clock				: Clock;
	timers				: Timer;
	timerListMutex	: Unix.Mutex_t;

	timerStopped: BOOLEAN;

	(* processes *)
	root-	: Process;	(*!  Anchor of all instantiated threads in system *)
	stacksize: SIZE;		(* stack size of active objects, adjustable via boot parameter *)

	processList		: Unix.Mutex_t;
	createProcess	: Unix.Mutex_t;
	startProcess		: Unix.Mutex_t;
	startEventLock	: Unix.Mutex_t;
	lockMutex		: Unix.Mutex_t;
	childrunning		: Unix.Condition_t;

	processPointer	: Unix.Key_t;

	newProcess: Process;
	nextPID: INTEGER;

	finalizerCaller	: FinalizerCaller;
	mainthread: Unix.Thread_t;

	startedMainProcess := FALSE: BOOLEAN;

TYPE

	LockT= POINTER TO RECORD
		mtx, enter: ADDRESS;
	END;

	CpuCyclesArray* = ARRAY Machine.MaxCPU OF SIGNED64;

	ProtectedObject = POINTER TO RECORD END;

	ObjectHeader = Heaps.ProtRecBlock;

	ProcessQueue = Heaps.ProcessQueue;

	EventHandler* = PROCEDURE  {DELEGATE};



	Timer* =  OBJECT
	VAR
		next: Timer;
		trigger: SIGNED32;
		handler: EventHandler
	END Timer;

	TimerActivity = OBJECT
	VAR
		t, r: Timer;  h: EventHandler;  restart: BOOLEAN;

		PROCEDURE UpdateTicks;
		BEGIN {EXCLUSIVE}
			Machine.UpdateTicks
		END UpdateTicks;

		PROCEDURE Restart;
		BEGIN {EXCLUSIVE}
			restart := TRUE
		END Restart;

	BEGIN {ACTIVE, SAFE, PRIORITY(High)}
		restart := FALSE;
		LOOP
			t := timers;
			IF t # NIL THEN
				h := NIL;  r := NIL;
				BEGIN {EXCLUSIVE}
					AWAIT( (Machine.ticks >= t.trigger) OR restart );  restart := FALSE;
					IF Machine.ticks >= t.trigger THEN
						h := t.handler;  r := t
					END
				END;
				IF r # NIL THEN  Remove( r )  END;
				IF h # NIL THEN  (* not canceled *) h END
			ELSE
				BEGIN{EXCLUSIVE}
					AWAIT( restart );  restart := FALSE;
				END
			END
		END
	END TimerActivity;

	Clock* = OBJECT
	BEGIN {ACTIVE}
		LOOP
			Unix.ThrSleep( 10 );
			IF ~timerStopped THEN  timerActivity.UpdateTicks  END
		END;
	END Clock;

	FinalizerCaller = OBJECT	(* separate active object that calls finalizers *)
	VAR
		n: Heaps.FinalizerNode;  start: BOOLEAN;

		PROCEDURE Activate;
		BEGIN {EXCLUSIVE}
			start := TRUE
		END Activate;

	BEGIN {ACTIVE, SAFE, PRIORITY(High)}
		start := FALSE;
		LOOP
			BEGIN {EXCLUSIVE} AWAIT( start ) END;
			start := FALSE;
			LOOP
				n := Heaps.GetFinalizer();
				IF n = NIL THEN EXIT END;
				IF n.collection # NIL THEN
					n.collection.RemoveAll(n.objStrong)	(* remove it if it is not removed yet *)
				END;
				IF n.finalizer # NIL THEN
					n.finalizer(n.objStrong)	(* may acquire locks *)
				END;
			END;
		END
	END FinalizerCaller;



	Body = PROCEDURE ( self: ProtectedObject );
	Condition = PROCEDURE ( slink: ADDRESS ): BOOLEAN;

	GCContext = RECORD
		p: Process; (* correspondig process *)
		nextPos: SIZE; (* 0 to start with *)
		last: ARRAY 32 OF RECORD bp, pc, sp: ADDRESS END;
		
		PROCEDURE AddContext(bp, pc, sp: ADDRESS);
		BEGIN
			last[nextPos].bp := bp;
			last[nextPos].pc := pc;
			last[nextPos].sp := sp;
			IF nextPos = 0 THEN
				(* needed by Object Tracker in Solaris and Darwin ports *)
				p.state.PC := pc;
				p.state.SP := sp;
				p.state.BP := bp
			END;
			INC(nextPos);
		END AddContext;

		PROCEDURE GetNextContext(VAR pos: SIZE; VAR bp, pc, sp: ADDRESS): BOOLEAN;
		BEGIN
			IF pos < 1 THEN RETURN FALSE END;
			DEC(pos);
			bp := last[pos].bp;
			pc := last[pos].pc;
			sp := last[pos].sp;
			RETURN TRUE;
		END GetNextContext;

		PROCEDURE RemoveContext();
		BEGIN
			IF nextPos > 0 THEN
				DEC(nextPos);
				last[nextPos].bp := NIL;
				last[nextPos].pc := NIL;
				last[nextPos].sp := NIL;
			END;
		END RemoveContext;
	END;

	Process* = OBJECT (Heaps.ProcessLink)
	VAR
		threadId-			: Unix.Thread_t;
		nextProcess-	: Process;	(* next in list of all processes *)
		stackBottom	-	: ADDRESS;
		id-				: INTEGER;
		body			: Body;
		mode-		: INTEGER;
		flags-			: SET;
		priority-		: INTEGER;	(* only effective if Aos is running SUID root *)
		succ			: Process;   		  	(* in ProcessQueue *)
		obj-			: ProtectedObject;	(* associated active object *)
		condition-	: Condition;   			(* awaited process' condition *)
		condFP-		: ADDRESS;			(* awaited process' condition's context *)
		continue		: Unix.Condition_t;	(* gets signaled when condition yields true *)
		waitingOn-	: ProtectedObject;
		procID-		: SIGNED32;				(*! processor ID where running, not used in UnixAos *)
		state-			: Machine.State;
		state0	: ARRAY 2048 OF CHAR;		(* thread state at body start, used for restart after trap *)
		context: ANY; (* commands context *)
		lastThreadTimes: SIGNED64;
		gcContext: GCContext;

		PROCEDURE SetMode (mode: INTEGER);
		BEGIN
				Machine.Acquire(Machine.Heaps);(* process does not silently stop or run when GC is active *)
				SELF.mode := mode;
				Machine.Release(Machine.Heaps);
		END SetMode;

		PROCEDURE FindRoots;
		VAR sp, bp, sb, n, a0, a1, adr, pc: ADDRESS; desc {UNTRACED}: Modules.ProcedureDescPointer; i: SIZE; p {UNTRACED}: ANY;
			contextPos: SIZE; suspended: BOOLEAN;
		BEGIN {UNTRACKED}
			IF (mode < Running) OR (mode = Terminated) THEN  RETURN  END;
			suspended := FALSE;
			IF SELF = CurrentProcess() THEN
				state.SP := SYSTEM.GetStackPointer( );
				state.BP := SYSTEM.GetFramePointer( );
				state.PC := Machine.CurrentPC();
			ELSIF ConcurrentGC THEN
				suspended := TRUE;
				Suspend(SELF);
			END;
			sb := stackBottom;
			contextPos := CAS(gcContext.nextPos,0,0);
			sp := state.SP; bp := state.BP; pc := state.PC;  (* <---- might all be invalid, when A2 was left ! *)

			IF TraceProcessHook # NIL THEN (* stack trace *)
				TraceProcessHook(SELF, pc, bp, sp, sb);
			END;

			IF contextPos >= 0 THEN (* this thread is currently active in A2 *)
				IF Heaps.GCType = Heaps.HeuristicStackInspectionGC THEN
					(* debugging info*)
					IF (stackBottom # 0) & (bp <= stackBottom) & (bp >= sp - SIZE OF ADDRESS) THEN
						SYSTEM.GET( bp, n );
						IF ODD( n ) THEN (* procedure descriptor at bp *)
							IF n > 1024 THEN
							desc := SYSTEM.VAL( Modules.ProcedureDescPointer, n-1 ); (* tracing !*)
							END;
						END;
					END;
					IF (stackBottom # 0) & (sp # 0) & (sp <= stackBottom) THEN
						Heaps.RegisterCandidates( sp, stackBottom - sp );
					END;
				ELSIF Heaps.GCType = Heaps.MetaDataForStackGC THEN
					LOOP
						IF (bp <= stackBottom) & (bp >= sp) THEN
						ELSIF Machine.ValidHeapAddress(pc) & (bp # NIL) THEN (* bp = NIL can happen when code has no procedure activation frame *)
							(* ok, valid stack frame from A2, we can trace this *)
						ELSIF gcContext.GetNextContext(contextPos, bp, pc, sp) THEN
							IF TraceProcessHook # NIL THEN (* stack trace *)
								TraceProcessHook(SELF, pc, bp, sp-128, sb);
							END;
						ELSE
							EXIT
						END;
						IF Machine.ValidHeapAddress(pc) & (bp > sp) THEN (* in A2 *)
							SYSTEM.GET( bp-SIZEOF(ADDRESS), desc );
							IF desc # NIL THEN
								a0 := ADDRESSOF( desc.offsets );
								a1 :=  SYSTEM.VAL( ADDRESS, desc.offsets );
								ASSERT( a0+SIZEOF( ADDRESS ) = a1, 54321 );
								FOR i := 0 TO LEN( desc.offsets ) - 1 DO
									adr := bp + desc.offsets[i]; (* pointer at offset *)
									SYSTEM.GET( adr, p ); (* load pointer *)
									IF p # NIL THEN
										Heaps.Mark( p );
									END
								END
							END;
						END;
						SYSTEM.GET(bp + SIZEOF(ADDRESS), pc);
						SYSTEM.GET(bp, bp);
					END; (* LOOP *)
				END; (* gctype *)
			END; (* contextpos *)
			IF ConcurrentGC THEN
				IF suspended THEN
					Resume(SELF);
				END;
			END;
		END FindRoots;

		PROCEDURE Cancel;
		VAR pt, t: Process;  kt: Unix.Thread_t;
		BEGIN
			IF SELF = CurrentProcess() THEN  Exit
			ELSE
				Machine.Acquire( Machine.X11 );  (* let the thread to be killed first finish its last I/O, if any *)
				Unix.MtxLock( processList );
					pt := NIL; t := root;  kt := 0;
					WHILE (t # NIL ) & (t # SELF) DO  pt := t;  t := t.nextProcess  END;
					IF t = SELF THEN
						kt := threadId;
						IF pt = NIL THEN  root := t.nextProcess  ELSE  pt.nextProcess := t.nextProcess  END;
					END;
				Unix.MtxUnlock( processList );
				IF kt # 0 THEN  Unix.ThrKill( kt )  END;
				Machine.Release( Machine.X11 );
			END
		END Cancel;

		PROCEDURE GetPriority( ): INTEGER;
		BEGIN
			RETURN Unix.ThrGetPriority( threadId )
		END GetPriority;

		PROCEDURE SetPriority( prio: INTEGER );
		VAR pr: INTEGER;
		BEGIN
		(*
			Linux/Solaris11: works only with SUID root and FIFO threads
			Solaris10: woks only with SUID root
			Darwin: works allways
		*)
			pr := MAX( Machine.prioLow, MIN( prio, Machine.prioHigh ) );
			Unix.ThrSetPriority( threadId, pr );
			priority := GetPriority( )
		END SetPriority;


		PROCEDURE & Initialize( obj: ProtectedObject;  bodyProc: Body;  prio: INTEGER; fl: SET; stacksize: SIZE);
		BEGIN
			SELF.obj := obj;  condition := NIL;  continue := Unix.NewCond( );
			flags := fl;
			priority := prio;
			nextProcess := NIL;
			context := CurrentContext();
			(* must happen here before body is created! *)
			gcContext.nextPos := 0;
			gcContext.p := SELF;
			IF CAS(root,NIL,SELF) = NIL THEN
				(* first process *)
				stackBottom := Glue.stackBottom;
				threadId := Unix.ThrThis( );
				id := 0;  nextPID := 1;
				mode := Running;
				Unix.WriteKey( processPointer, SELF );
				ASSERT(~CAS(startedMainProcess, FALSE, TRUE));
			ELSE
				newProcess := SELF;
				ASSERT( bodyProc # NIL );
				body := bodyProc;
				Unix.MtxLock( startProcess );
				Unix.MtxLock( startEventLock ); (* the cond wait below opens this lock again! *)
				threadId := Unix.ThrStart( BodyStarter, stacksize );
				Unix.CondWait( childrunning, startEventLock );
				Unix.MtxUnlock( startEventLock );
				Unix.MtxUnlock( startProcess );
				RegisterFinalizer( SELF, FinalizeProcess );
			END;
		END Initialize;

	END Process;

TYPE	GCStatusExt = OBJECT (Heaps.GCStatus)

		(*	called from Heaps.InvokeGC, i.e. this is a hidden upcall. However, it is necessary to take the Machine.Objects
			lock here since writing the set of variables here must not be interrupted, i.e. atomic writing of the set of variables
			is absolutely necessary.  They system may hang if the lock is not taken. *)
		PROCEDURE SetgcOngoing( value: BOOLEAN );
		BEGIN
			IF value THEN
				Machine.Acquire( Machine.Heaps );
				IF ConcurrentGC THEN
					Heaps.CollectGarbage( Modules.root );
				ELSE
					SuspendActivities;
					Heaps.CollectGarbage( Modules.root );
					ResumeActivities;
				END;
				Machine.Release( Machine.Heaps );
				finalizerCaller.Activate;
			END;
		END SetgcOngoing;

	END GCStatusExt;



	PROCEDURE BodyStarter;
	VAR p: Process;  res: INTEGER; sp: ADDRESS;
	BEGIN
		(* make sure the process cannot be GCed in an intermediate unsafe state *)
		Machine.Acquire(Machine.Heaps);
		Unix.MtxLock( startEventLock );
		p := newProcess;  newProcess := NIL;
		Unix.WriteKey( processPointer, p );
		p.id := nextPID;  INC( nextPID );
		p.stackBottom := SYSTEM.GetFramePointer( );
		Machine.Release(Machine.Heaps);

		Unix.MtxLock( processList );
		p.nextProcess := root;  root := p;
		Unix.MtxUnlock( processList );
		Unix.CondSignal( childrunning );
		Unix.MtxUnlock( startEventLock );

		p.SetPriority( p.priority );

		IF Restart IN p.flags THEN
			(* store and restore stack pointer because it is saved on the stack during SYSVABI calls to ensure stack alignment *)
			sp := SYSTEM.GetStackPointer ();
			res := Unix.sigsetjmp( ADDRESSOF( p.state0[0] ), 1 );
			SYSTEM.SetStackPointer (sp);
		END;
		p.SetMode(Running);
		p.body( p.obj );
		Exit
	END BodyStarter;




	(*---------------------   create,  lock,  await,  unlock   -------------------------*)


	(* initialize the ObjectHeader, requires lockMutex temporarily *)
	PROCEDURE InitProtHeader( hdr {UNTRACED}: ObjectHeader);
	VAR lock: LockT;
	BEGIN
		(* we cannot hold the lockMute here because allocation can trigger the GC that requires the lock when activating the finalizers *)
		NEW(lock);
		Unix.MtxLock(lockMutex);
		IF hdr.lock = NIL THEN
			lock.mtx := Unix.NewMtx( );  lock.enter := Unix.NewCond( );  hdr.lockedBy := NIL;
			hdr.lock := lock;
		END;
		Unix.MtxUnlock(lockMutex);
	END InitProtHeader;


	PROCEDURE CreateProcess*( body: Body;  priority: INTEGER;  flags: SET;  obj: ProtectedObject );
	VAR p: Process;  hdr{UNTRACED}: ObjectHeader;
	BEGIN
		Unix.MtxLock( createProcess );
		SYSTEM.GET( SYSTEM.VAL( ADDRESS, obj ) + Heaps.HeapBlockOffset, hdr );
		InitProtHeader( hdr );
		IF priority = 0 THEN  priority := Normal  END;
		NEW( p, obj, body, priority, flags, stacksize ) ;	(* execute BodyStarter as new (posix or solaris) thread *)
		Unix.MtxUnlock( createProcess );
		RegisterFinalizer( obj, FinalizeActiveObj )
	END CreateProcess;

	PROCEDURE Lock*( obj: ProtectedObject;  exclusive: BOOLEAN );
	VAR hdr {UNTRACED}: ObjectHeader;  p : Process; lock: LockT;
	BEGIN
		ASSERT( exclusive );   (* shared not implemented yet *)
		SYSTEM.GET( SYSTEM.VAL( ADDRESS, obj ) + Heaps.HeapBlockOffset, hdr );
		p := CurrentProcess();

		(*! we might want to replace the lock mutex by a lock free construct *)
		IF hdr.lock = NIL THEN  InitProtHeader( hdr )  END;
		lock := SYSTEM.VAL(LockT, hdr.lock);

		p.mode := AwaitingLock;
		Unix.MtxLock( lock.mtx );
		WHILE hdr.lockedBy # NIL DO
			(* wait until threads with complied AWAIT conditions have left the monitor *)
			Unix.CondWait( lock.enter, lock.mtx );
		END;
		p.mode := Running;  hdr.lockedBy := p;  p.waitingOn := NIL
	END Lock;

	PROCEDURE Await*( cond: Condition;  slink: ADDRESS;  obj: ProtectedObject;  flags: SET );
	VAR hdr {UNTRACED}: ObjectHeader;  p, c: Process; lock: LockT;
	BEGIN
		IF 1 IN flags THEN  (* compiler did not generate IF *)
			IF cond( slink ) THEN  (* condition already true *)  RETURN  END
		END;
		SYSTEM.GET( SYSTEM.VAL( ADDRESS, obj ) + Heaps.HeapBlockOffset, hdr );  c := NIL;
		lock := SYSTEM.VAL(LockT, hdr.lock);
		IF hdr.awaitingCond.head # NIL THEN  c := FindCondition( hdr.awaitingCond )  END;

		p := CurrentProcess();
		ASSERT( hdr.lockedBy = p, 2204 );
		p.succ := NIL;  p.condition := cond;  p.condFP := slink;  p.waitingOn := obj;

		Put( hdr.awaitingCond, p );
		hdr.lockedBy := c;
		IF c # NIL THEN  Unix.CondSignal( c.continue )  ELSE  Unix.CondSignal( lock.enter )  END;

		p.mode := AwaitingCond;
		Unix.CondWait( p.continue, lock.mtx );
		p.mode := Running;  hdr.lockedBy := p;  p.waitingOn := NIL
	END Await;

	PROCEDURE Unlock*( obj: ProtectedObject;  dummy: BOOLEAN );
	VAR hdr{UNTRACED}: ObjectHeader;  c: Process; lock: LockT;
	BEGIN
		SYSTEM.GET( SYSTEM.VAL( ADDRESS, obj ) + Heaps.HeapBlockOffset, hdr );  c := NIL;
		lock := SYSTEM.VAL(LockT,hdr.lock);
		IF hdr.awaitingCond.head # NIL THEN  c := FindCondition( hdr.awaitingCond )  END;

		hdr.lockedBy := c;
		IF c # NIL THEN  Unix.CondSignal( c.continue )  ELSE  Unix.CondSignal( lock.enter )  END;
		Unix.MtxUnlock( lock.mtx );
	END Unlock;

	PROCEDURE FindCondition( VAR q: ProcessQueue ): Process;
	VAR first, cand: Process;
	BEGIN
		Get( q, first );
		IF first.condition( first.condFP ) THEN  RETURN first  ELSE  Put( q, first )  END;
		WHILE q.head # first DO
			Get( q, cand );
			IF cand.condition( cand.condFP ) THEN  RETURN cand  ELSE  Put( q, cand )  END;
		END;
		RETURN NIL
	END FindCondition;

	PROCEDURE Get( VAR queue: ProcessQueue;  VAR new: Process );
	VAR t: Process;
	BEGIN
		t := queue.head(Process);
		IF t # NIL THEN
			IF t = queue.tail THEN  queue.head := NIL;  queue.tail := NIL
			ELSE  queue.head := t.succ;  t.succ := NIL
			END
		END;
		new := t
	END Get;

	PROCEDURE Put( VAR queue: ProcessQueue;  t: Process );
	BEGIN
		IF queue.head = NIL THEN  queue.head := t  ELSE  queue.tail(Process).succ := t  END;
		queue.tail := t
	END Put;

	(*-------------------------------------------------------------------------*)

	PROCEDURE Terminate-;
	BEGIN
		Exit
	END Terminate;

	PROCEDURE TerminateThis*( p: Process; unbreakable: BOOLEAN );
	BEGIN
		p.SetMode(Terminated);
		p.Cancel
	END TerminateThis;

	PROCEDURE SetPriority*( pri: INTEGER );		(* Set the current process' priority. *)
	VAR me: Process;
	BEGIN
		me := CurrentProcess();
		me.SetPriority( pri )
	END SetPriority;

	PROCEDURE Sleep*( ms: SIGNED32 );
	BEGIN
		Unix.ThrSleep( ms );
	END Sleep;

	PROCEDURE Yield-;	(* Relinquish control. *)
	BEGIN
		Unix.ThrYield( );
	END Yield;

	(* Return current process. (DEPRECATED, use ActiveObject) *)
	PROCEDURE CurrentProcess*( ):  {UNTRACED}Process;
	BEGIN
		RETURN SYSTEM.VAL( Process , Unix.ReadKey( processPointer ) )
	END CurrentProcess;

	PROCEDURE CurrentContext*(): ANY;
	VAR p : Process;
	BEGIN
		p := CurrentProcess();
		IF p # NIL THEN RETURN p.context
		ELSE RETURN NIL
		END;
	END CurrentContext;

	PROCEDURE SetContext*(context: ANY);
	VAR p: Process;
	BEGIN
		p := CurrentProcess();
		IF p # NIL THEN p.context := context END;
	END SetContext;


	(* Return the active object currently executing. *)
	PROCEDURE ActiveObject*( ): ANY;
	VAR p: Process;
	BEGIN
		p := CurrentProcess();
		RETURN p.obj
	END ActiveObject;


	(* Return stack bottom of process. For compatibility WinAos/UnixAos/NativeAos  *)
	PROCEDURE GetStackBottom*(p: Process): ADDRESS;
	BEGIN
		RETURN p.stackBottom
	END GetStackBottom;

	PROCEDURE GetStack*(p: Process; VAR pc, bp, sp, sb: ADDRESS; VAR contextPos: SIZE);
	BEGIN
		UpdateProcessState(p);
		bp := p.state.BP;
		pc := p.state.PC;
		sp := p.state.SP;
		sb := p.stackBottom;
		contextPos := p.gcContext.nextPos;

		IF CurrentProcess() = p THEN
			sp := SYSTEM.GetStackPointer();
			bp := SYSTEM.GetFramePointer();
			SYSTEM.GET(bp, bp);
			SYSTEM.GET(bp+SIZEOF(ADDRESS), pc);
		ELSE
			IF Machine.ValidHeapAddress(pc) THEN
			ELSE
				IGNORE NextValidStackSegment(p, bp, pc, sp, contextPos);
			END;
		END;
	END GetStack;

	PROCEDURE NextValidStackSegment*(p: Process; VAR bp, pc, sp: ADDRESS; VAR contextPos: SIZE): BOOLEAN;
	BEGIN
		bp := NIL;
		WHILE p.gcContext.GetNextContext(contextPos, bp, pc, sp) & (bp = NIL) DO
		END;
		RETURN bp  # NIL;
	END NextValidStackSegment;

	PROCEDURE GetProcessID*( ): INTEGER;
	VAR p: Process;
	BEGIN
		p := CurrentProcess();
		RETURN p.id;
	END GetProcessID;
	
	PROCEDURE NumReady*( ): SIGNED32;
	VAR n: SIGNED32; p: Process;
	BEGIN
		n := 0;
		Unix.MtxLock( processList );
		p := root;
		WHILE p # NIL DO
			IF p.mode = Running THEN INC( n ) END;  
			p := p.nextProcess
		END;
		Unix.MtxUnlock( processList );
		RETURN n
	END NumReady;


	PROCEDURE GetCpuCycles*( process : Process; VAR cpuCycles: CpuCyclesArray; all: BOOLEAN );
	VAR temp : SIGNED64;
	BEGIN
		ASSERT(process # NIL);
		cpuCycles[0] := Machine.GetTimer();

		IF ~all THEN
			temp := process.lastThreadTimes;
			process.lastThreadTimes := cpuCycles[0];
			cpuCycles[0] := cpuCycles[0] - temp;
		END;
	END GetCpuCycles;



	(*-----------------------------------------------------------------------*)

	PROCEDURE RegisterFinalizer( obj: ANY;  fin: Heaps.Finalizer );
	VAR n: Heaps.FinalizerNode;
	BEGIN
		NEW( n ); n.finalizer := fin;  Heaps.AddFinalizer( obj, n );
	END RegisterFinalizer;

	PROCEDURE FinalizeActiveObj( obj: ANY );
	VAR p: Process;
	BEGIN
		Unix.MtxLock( processList );
			p := root;
			WHILE (p # NIL) & (p.obj # obj) DO p := p.nextProcess  END;
		Unix.MtxUnlock( processList );
		IF (p # NIL) & (p.obj = obj) THEN
			p.SetMode(Terminated);
			Unix.CondDestroy( p.continue );  p.continue := 0;
			FinalizeProtObject( obj );
			p.Cancel
		END;
	END FinalizeActiveObj;

	PROCEDURE FinalizeProtObject( obj: ANY );
	VAR hdr{UNTRACED}: ObjectHeader; lock: LockT;
	BEGIN
		SYSTEM.GET( SYSTEM.VAL( ADDRESS, obj ) + Heaps.HeapBlockOffset, hdr );
		IF hdr.lock # NIL THEN
			lock := SYSTEM.VAL(LockT, hdr.lock);
			Unix.MtxDestroy( lock.mtx );  lock.mtx := 0
		END
	END FinalizeProtObject;


	PROCEDURE FinalizeProcess( obj: ANY );
	VAR p: Process;
	BEGIN
		p := obj(Process);
		IF p.continue # 0 THEN
			Unix.CondDestroy( p.continue );  p.continue := 0
		END
	END FinalizeProcess;

	(* Terminate calling thread. *)
	PROCEDURE Exit;
	VAR prev, p, me: Process;
	BEGIN
		me := CurrentProcess();
		me.SetMode(Terminated);
		Unix.MtxLock( processList );
		prev := NIL;  p := root;
		WHILE (p # NIL ) & (p # me) DO  prev := p;  p := p.nextProcess  END;
		IF p = me THEN
			IF prev = NIL THEN  root := p.nextProcess  ELSE  prev.nextProcess := p.nextProcess  END;
		END;
		Unix.MtxUnlock( processList );
		Unix.ThrExit( );
	END Exit;

	PROCEDURE ExitTrap-;
	VAR p: Process;
	BEGIN
		p := CurrentProcess();
		IF p.id = 0 THEN
			(* main thread *)
			Unix.exit( 1 )
		END;
		(* restart the object body if it was given the SAFE flag *)
		IF Restart IN p.flags THEN
			Unix.siglongjmp( ADDRESSOF( p.state0[0] ), 1 )
		END;
		Exit
	END ExitTrap;




	(*---------------------------- Timer --------------------------------*)


	PROCEDURE Remove( t: Timer );  (* remove timer from list of active timers *)
	VAR p, x: Timer;
	BEGIN
		Unix.MtxLock( timerListMutex );
		t.trigger := 0;  t.handler := NIL;
		IF timers # NIL THEN
			IF t = timers THEN
				timers := t.next
			ELSE
				p := timers;  x := p.next;
				WHILE (x # NIL) & (x # t)  DO  p := x;  x := p.next  END;
				IF x = t THEN  p.next := t.next  END
			END;
			t.next := NIL
		END;
		Unix.MtxUnlock( timerListMutex )
	END Remove;

	PROCEDURE Insert( t: Timer );
	VAR  p, x: Timer;
	BEGIN
		Unix.MtxLock( timerListMutex );
		p := NIL;  x := timers;
		WHILE (x # NIL) & (x.trigger < t.trigger)  DO  p := x;  x := p.next  END;
		t.next := x;
		IF p = NIL THEN  timers := t  ELSE   p.next := t  END;
		Unix.MtxUnlock( timerListMutex )
	END Insert;

	PROCEDURE SetTimeout*( t: Timer;  h: EventHandler;  ms: SIGNED32 );
	BEGIN
		ASSERT( ( t # NIL) & ( h # NIL) );
		Remove( t );
		IF ms < 1 THEN ms := 1 END;
		t.trigger := Machine.ticks + ms;  t.handler := h;
		Insert( t );
		timerActivity.Restart
	END SetTimeout;

	PROCEDURE SetTimeoutAt*( t: Timer;  h: EventHandler;  ms: SIGNED32 );
	BEGIN
		ASSERT( (t # NIL) & (h # NIL) );
		Remove( t );
		t.trigger := ms;  t.handler := h;
		Insert( t );
		timerActivity.Restart
	END SetTimeoutAt;

	PROCEDURE CancelTimeout*( t: Timer );
	BEGIN
		Remove( t )
	END CancelTimeout;

	(*--------------------  Garbage Collection  ------------------------------------*)


	PROCEDURE GetContext( ctxt: Unix.Ucontext );
	VAR p: Process; context: Unix.McontextDesc;
	BEGIN
		p := CurrentProcess( );
		IF p.gcContext.nextPos = 0 THEN  (* in A2 *)
			Unix.CopyContext( ctxt.mc, context );
			p.state.PC := context.r_pc;
			p.state.BP := context.r_bp;
			p.state.SP := context.r_sp
		ELSE
			VAR contextPos := p.gcContext.nextPos;
			IF p.gcContext.GetNextContext(contextPos, p.state.BP, p.state.PC, p.state.SP) THEN END;
		END
	END GetContext;

	(* called by WMProcessInfo to obtain the current state of a process *)
	PROCEDURE UpdateProcessState*( p: Process );
	BEGIN
		Machine.Acquire(Machine.Heaps);  (* must not run concurrently with GC *)
		IF p = CurrentProcess() THEN
			p.state.PC := Machine.CurrentPC( );
			p.state.BP := SYSTEM.GetFramePointer( );
			p.state.SP := SYSTEM.GetStackPointer( )
		ELSE
			IF p.mode = Running THEN
				timerStopped := TRUE;
				Suspend(p);
				Resume(p);
				timerStopped := FALSE
			END
		END;
		Machine.Release(Machine.Heaps);
	END UpdateProcessState;

	(* suspend and store state *)
	PROCEDURE Suspend(p: Process);
	BEGIN
		Machine.Acquire(Machine.X11);
		Unix.ThrSuspend( p.threadId, p.mode = Running ); (*	the second parameter is ignored in the Linux port
																		but important for the other Unix ports. cf. Solaris.Unix.ThrSuspend *)
		Machine.Release(Machine.X11);
	END Suspend;

	PROCEDURE Resume(p: Process);
	BEGIN
		Unix.ThrResume( p.threadId );
	END Resume;

	PROCEDURE SuspendActivities;
	VAR t, me: Process;
	BEGIN
		Unix.MtxLock( processList ); (* no process should silently quit during global thread suspension *)
		me := CurrentProcess();
		t := root;
		WHILE t # NIL DO
			IF t # me THEN
				Suspend(t)
			END;
			t := t.nextProcess
		END;
		Unix.MtxUnlock( processList );
		Machine.Release(Machine.X11);
	END SuspendActivities;

	PROCEDURE ResumeActivities;
	VAR t, me: Process;
	BEGIN
		Unix.MtxLock( processList ); (* no process should silently quit during global thread suspension *)
		me := CurrentProcess();
		t := root;
		WHILE t # NIL DO
			IF (t # me) THEN
				Resume(t);
			END;
			t := t.nextProcess
		END;
		Unix.MtxUnlock( processList );
	END ResumeActivities;


	PROCEDURE CurrentProcessTime*(): SIGNED64;
	BEGIN
		RETURN  Machine.GetTimer()
	END CurrentProcessTime;

	PROCEDURE TimerFrequency*(): SIGNED64;
	BEGIN
		RETURN Machine.timerFrequency;
	END TimerFrequency;

	(* Leave A2 is called when a process leaves A2 by a call to the underlying OS API *)
	PROCEDURE LeaveA2*;
	VAR cur {UNTRACED}: Process; ebp, pc, sp: ADDRESS;
	BEGIN{UNTRACKED}
		IF CAS(startedMainProcess,FALSE,FALSE) THEN
			cur := CurrentProcess();
			IF cur # NIL THEN
				ebp := SYSTEM.GetFramePointer();
				sp := SYSTEM.GetStackPointer();
				SYSTEM.GET(ebp+SIZEOF(ADDRESS), pc);
				SYSTEM.GET(ebp, ebp);
				cur.gcContext.AddContext(ebp, pc, sp);				
			END;
		END;
	END LeaveA2;

	(* reenter is called when a process returns from a call to the underlying OS API *)
	PROCEDURE ReenterA2*;
	VAR cur{UNTRACED}: Process;
	BEGIN{UNTRACKED}
		IF CAS(startedMainProcess,FALSE,FALSE) THEN
			cur := CurrentProcess();
			IF cur # NIL THEN
				cur.gcContext.RemoveContext();
			END;
		END;
	END ReenterA2;

	(*----------------------------- initialization ----------------------------------*)

	PROCEDURE StartTimerActivity;
	BEGIN
		timerListMutex := Unix.NewMtx( );  timers := NIL;
		NEW( timerActivity );
	END StartTimerActivity;


	PROCEDURE GetStacksize;
	VAR str: ARRAY  32 OF  CHAR;  i: SIZE;
	BEGIN
		Machine.GetConfig( "StackSize", str );
		IF str = "" THEN  stacksize := DefaultStacksize
		ELSE
			i := 0;  stacksize := Machine.StrToInt( i, str );
			stacksize := stacksize * 1024;
		END;
		IF Glue.debug # {} THEN
			Trace.String( "Stacksize of active objects = " );
			Trace.Int( stacksize DIV 1024, 0 );  Trace.StringLn( "K"  )
		END;
	END GetStacksize;


	PROCEDURE Convert;
	VAR p: Process; o: ProtectedObject;
	BEGIN
		(* make current thread the first active object  *)
		mainthread := Unix.ThrThis();
		NEW( o ); (* alibi object, e.g. for Locks *)
		NEW( p, o, NIL, 0, {}, 0 );
	END Convert;

	PROCEDURE Init;
	BEGIN
		Unix.suspendHandler := GetContext;

		createProcess := Unix.NewMtx( );  processList := Unix.NewMtx( );
		startEventLock := Unix.NewMtx( );  childrunning := Unix.NewCond( );
		lockMutex := Unix.NewMtx( );
		startProcess := Unix.NewMtx( );

		processPointer := Unix.NewKey( );

		GetStacksize;
		Convert;
		StartTimerActivity;  timerStopped := FALSE;
		NEW( clock );
		NEW( finalizerCaller );

		Heaps.gcStatus := GCStatusFactory()
	END Init;

TYPE
	MainThread = OBJECT
	VAR exit: BOOLEAN;

		PROCEDURE & Init;
		BEGIN
			exit := FALSE;
		END Init;

		PROCEDURE Await();
		BEGIN {EXCLUSIVE}
			AWAIT( exit );
		END Await;

	END MainThread;

VAR main: MainThread;

	PROCEDURE MainThreadSleep;
	BEGIN
		NEW( main );
		main.Await( );
		Unix.exit( 0 );
	END MainThreadSleep;

	PROCEDURE {CLOSING} Final;
	BEGIN
		MainThreadSleep;
	END Final;

	PROCEDURE GCStatusFactory(): Heaps.GCStatus;
	VAR gcStatusExt : GCStatusExt;
	BEGIN
		ASSERT( Heaps.gcStatus = NIL );
		NEW( gcStatusExt );
		RETURN gcStatusExt
	END GCStatusFactory;

VAR
	(* for compatibility and later extension *)
	TraceProcessHook*: PROCEDURE (prcoess: Process; pc, bp: ADDRESS; stacklow, stackhigh: ADDRESS);

BEGIN
	TraceProcessHook := NIL;
	Init;
END Objects.

