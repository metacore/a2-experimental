(* Aos, Copyright 2001, Pieter Muller, ETH Zurich *)

MODULE Objects;   (** AUTHOR "pjm"; PURPOSE "Active object runtime support"; *)

(*	2006.06.20	g.f.	Unix port  *)
(*	2007.04.13	g.f.	Timer added *)
(*	2007.09.21	g.f.	Lock, Unlock fixed *)

IMPORT S := SYSTEM, Trace, Glue, Unix, Machine, Heaps, Modules;

CONST

	(* Process flags, meaningless in Unix ports !!! *)
	PleaseHalt* = 10;		(* Process requested to Halt itself soon *)
	Unbreakable*= 11;		(* FINALLY shall not catch HALT exception (PleaseHalt is also set) *)
	SelfTermination*=12;	(* Indicates the process has requested to terminate ifself (PleaseHalt is also set) *)
	Preempted* = 27;		(* Has been preempted. *)
	Resistant* = 28;			(* Can only be destroyed by itself *)


	MinPriority* = Unix.ThreadLow;
	Low* = Unix.ThreadLow + 1;
	Normal* = Unix.ThreadNormal;
	High* = Unix.ThreadHigh - 2;
	GCPriority* = Unix.ThreadHigh - 1;
	Realtime* = Unix.ThreadHigh;

	(* Process flag defined by compiler in OPC.CallRecBody *)
	Restart* = 0;	(* Restart/Destroy process on exception *)

	(* Process modes (in UnixAos Running means Running or Ready!) *)
	Unknown* = 0;  Ready* = 1;  Running* = 2;  AwaitingLock* = 3;
	AwaitingCond* = 4;  AwaitingEvent* = 5;  Terminated* = 6;

	Second* = 1000;	(* frequency of ticks increments in Hz *)

	DefaultStacksize = 256*1024;
	
	AdrSize = S.SIZEOF( S.ADDRESS );

TYPE
	cThread = LONGINT;
	cMutex = LONGINT;
	cCond = LONGINT;

	Address = S.ADDRESS;
	Size = S.SIZE;

	CpuCyclesArray* = ARRAY Machine.MaxCPU OF HUGEINT;

	ProtectedObject = POINTER TO RECORD END;

	ObjectHeader = POINTER TO RECORD  (* header of a protected object *)
				(* should not be used as global variable or record field, because of Heaps.Mark *)
				size: Size;
				sentinel: Address;
				count: SHORTINT;   (* -1 => exclusive lock, 0 => unlocked, (later: > 0 => number of shared locks) *)
				locked: BOOLEAN;
				filler: INTEGER;		(* set to -1 for Info.Objects *)
				mtx: cMutex;		(* processes blocked awaiting lock *)
				awaitingCond: ProcessQueue;   (* processes blocked awaiting condition *)
			END;

	Body = PROCEDURE ( typetag: Address;  self: ProtectedObject );
	Condition = PROCEDURE ( slink: Address ): BOOLEAN;
	
	Process* = OBJECT (Heaps.RootObject)
			VAR
				processLink-	: Process;
				stackBottom-	: Address;
				SP-				: Address;
				id-				: LONGINT;
				proc			: Body;
				mode-			: LONGINT;
				flags-			: SET;
				priority-		: LONGINT;	(* only used if Aos is running SUID root *)
				
				succ: Process;   		  		(* in ProcessQueue *)
				obj-: ProtectedObject;		(* associated active object *)
				condition-: Condition;   		(* awaited process' condition *)
				condFP-: Address;			(* awaited process' condition's context *)
				cond: cCond;				(* gets signaled when condition yields true *)
				waitingOn-	: ProtectedObject;
				procID-		: LONGINT;			(* processor ID where running, not used in UnixAos *)
				state-		: Machine.State;		(* not used in UnixAos *)
				state0: ARRAY  2048 OF CHAR;		(* thread state at starting, used for restart after trap *)
				
				
				PROCEDURE & Initialize( obj: ProtectedObject;  bodyProc: Body;  prio: LONGINT; fl: SET; stacksize: LONGINT );
				BEGIN
					SELF.obj := obj;  condition := NIL;  cond := conInit(0);
					flags := fl;
					priority := prio;
					processLink := NIL;
					IF processes # NIL THEN
						Machine.Acquire( Machine.Objects );
						newProcess := SELF;
						ASSERT( bodyProc # NIL );
						proc := bodyProc;  
						mtxLock( start1 );
							nid := thrStart( BodyStarter, stacksize );
							conWait( childrunning, start1 );
						mtxUnlock( start1 );
						ASSERT( id = nid );					
						RegisterFinalizer( SELF, FinalizeProcess );
						Machine.Release( Machine.Objects);
						Sleep( 5 ) (* give the child time to do get a llttle further, needed for paco *) 
					ELSE 
						stackBottom := Glue.stackBottom;  
						SP := Machine.CurrentSP( );
						id := thrThis(0);
						processes := SELF;
						mode := Running;
						noThreads := 1;
					END;
				END Initialize;
				
				PROCEDURE FindRoots*;
				VAR sp, ptr: Address;
				BEGIN
					IF mode # Terminated THEN
						sp := SP;
						WHILE sp < stackBottom DO  
							S.GET( sp, ptr );  
							Heaps.AddCandidate( ptr );  
							INC( sp, AdrSize )  
						END;
					END;
					Heaps.Mark( processLink ) 
				END FindRoots;
				
				PROCEDURE Cancel*;
				VAR pt, t: Process;  kt: cThread;
				BEGIN
					IF SELF = This() THEN  Exit
					ELSE
						Machine.Acquire( Machine.X11 );  (* let the thread to be killed first finish its last I/O, if any *)
						Machine.Acquire( Machine.Heaps );
						pt := NIL; t := processes;  kt := 0;
						WHILE (t # NIL ) & (t # SELF) DO  pt := t;  t := t.processLink  END;
						IF t = SELF THEN
							kt := id;
							IF pt = NIL THEN  processes := t.processLink  ELSE  pt.processLink := t.processLink  END;
							DEC( noThreads )
						END;
						Machine.Release( Machine.Heaps );
						IF traceThreads & (noThreads < 100) THEN
							Trace.Ln;  Trace.String( "cancel thread " ); 
							Trace.String( ", threads left: " );  Trace.Int( noThreads, 1 );  Trace.Ln
						END;
						IF kt # 0 THEN  thrKill( kt )  END;
						Machine.Release( Machine.X11 );
					END
				END Cancel;

				PROCEDURE GetPriority*( ): LONGINT;
				BEGIN
					RETURN thrGetPriority( id ) 
				END GetPriority;

				PROCEDURE SetPriority*( prio: LONGINT );
				VAR pr: LONGINT;
				BEGIN
					pr := max( Machine.prioLow, min( prio, Machine.prioHigh ) );
					thrSetPriority( id, pr );	(* works only if SUID root *)
					priority := GetPriority( )
				END SetPriority;
				
			END Process;

	ProcessQueue = RECORD
				head, tail: Process
			END;


	EventHandler* = PROCEDURE  {DELEGATE};

	Timer* =  OBJECT
			VAR
				next: Timer;
				trigger: LONGINT;
				handler: EventHandler
			END Timer;
			
CONST
	TimerInterval = 10; (* ms *)

TYPE			
	TimerActivity = OBJECT		
	VAR sleeptime: LONGINT;  t: Timer; 
	
	PROCEDURE tSleep( ms: LONGINT );
		BEGIN
			mtxUnlock( tmtx );  Sleep( ms );  mtxLock( tmtx )
		END tSleep;
		
	BEGIN{ACTIVE, SAFE, PRIORITY(High)}
		mtxLock( tmtx );  
		LOOP
			t := timers;
			IF t # NIL THEN
				sleeptime := t.trigger - Machine.Ticks();  
				IF sleeptime > TimerInterval THEN  
					tSleep( TimerInterval );  DEC( sleeptime, TimerInterval )
				ELSIF sleeptime > 0 THEN  
					tSleep( sleeptime );  sleeptime := 0
				END;
				IF (sleeptime <= 0) & (t.handler # NIL) THEN  (* expired, not canceled *)
					t.handler;
					Remove( t );
				END;
			ELSE
				tSleep( TimerInterval )
			END
		END
	END TimerActivity;


CONST
	(* host system values *)
	Solaris = 1;  Linux = 2;  Darwin = 3;

VAR
	timers: Timer;  
	timerActivity: TimerActivity;
	tmtx: cMutex;
	
	processes-: Process;	(*  Anchor of all instantiated threads in system *)
	noThreads-: LONGINT;
	
	start1: cMutex;
	childrunning: cCond;
	newProcess{UNTRACED}: Process;
	nid: cThread;	
	
	createmtx: cMutex;

	hostSystem: LONGINT;
	stacksize: LONGINT;
	
	traceGC, traceThreads: BOOLEAN;

	(* the dummy parameters assure proper stack alignment when compiled with option \A *)
	mtxInit: 		PROCEDURE {REALTIME, C}  ( dummy: LONGINT ): cMutex;
	mtxDestroy: 	PROCEDURE {REALTIME, C}  ( mtx: cMutex );
	mtxLock: 		PROCEDURE {REALTIME, C}  ( mtx: cMutex );
	mtxUnlock:	 	PROCEDURE {REALTIME, C}  ( mtx: cMutex );

	conInit: 			PROCEDURE {REALTIME, C}  ( dummy: LONGINT ): cCond;
	conDestroy: 	PROCEDURE {REALTIME, C}  ( cond: cCond );
	conWait: 		PROCEDURE {REALTIME, C}  ( cond: cCond;  mtx: cMutex );
	conSignal: 		PROCEDURE {REALTIME, C}  ( cond: cCond );
	
	thrStart: 		PROCEDURE {REALTIME, C} ( p: PROCEDURE;  stackLen: LONGINT ): cThread;
	thrThis: 			PROCEDURE {REALTIME, C} ( dummy: LONGINT ): cThread;
	thrSleep: 		PROCEDURE {REALTIME, C} ( ms: LONGINT );
	thrPass: 		PROCEDURE {REALTIME, C} ( dummy: LONGINT );
	thrExit: 			PROCEDURE {REALTIME, C} ( dummy: LONGINT );
	thrSuspend: 	PROCEDURE {REALTIME, C} ( t: cThread );
	thrResume: 		PROCEDURE {REALTIME, C} ( t: cThread );
	thrSetPriority: 	PROCEDURE {REALTIME, C} ( t: cThread;  prio: LONGINT );
	thrGetPriority: 	PROCEDURE {REALTIME, C} ( t: cThread ): LONGINT;
	thrKill: 			PROCEDURE {REALTIME, C} ( t: cThread );
	
	
	PROCEDURE min( a, b: LONGINT ): LONGINT;
	BEGIN
		IF a <= b THEN  RETURN a  ELSE  RETURN b  END
	END min;

	PROCEDURE max( a, b: LONGINT ): LONGINT;
	BEGIN
		IF a >= b THEN  RETURN a  ELSE  RETURN b  END
	END max;
	
	
	PROCEDURE Lock( obj: ProtectedObject;  exclusive: BOOLEAN );
	VAR hdr: ObjectHeader;  p: Process;
	BEGIN
		ASSERT( exclusive );   (* shared not implemented yet *)
		hdr := S.VAL( ObjectHeader, S.VAL( Address, obj ) - Heaps.ProtOfs );
		p:= This( );
		p.mode := AwaitingLock;
		IF hdr.mtx = 0 THEN
			(* module object *)
			hdr.mtx := mtxInit( 0 );  hdr.locked := FALSE;
			RegisterFinalizer( obj, FinalizeProtObject )
		END;
		mtxLock( hdr.mtx );
		WHILE hdr.locked DO
			(* wait until thread with satisfied AWAIT condition has left the monitor *)
			mtxUnlock( hdr.mtx );
			IF hostSystem = Darwin THEN  Yield  END;
			mtxLock( hdr.mtx )
		END;
		p.mode := Running;
	END Lock;

	PROCEDURE Await( cond: Condition;  slink: Address;  obj: ProtectedObject;  flags: SET );
	VAR hdr: ObjectHeader;  p: Process;
	BEGIN
		IF 1 IN flags THEN  (* compiler did not generate IF *)
			IF cond( slink ) THEN  (* condition already true *)  RETURN  END
		END;
		hdr := S.VAL( ObjectHeader, S.VAL( Address, obj ) - Heaps.ProtOfs );
		p := This( );
		p.condition := cond;  p.condFP := slink;  p.succ := NIL;
		Put( hdr.awaitingCond, p );
		p.mode := AwaitingCond;
		
		conWait( p.cond, hdr.mtx );  
		
		hdr.locked := FALSE;
		p.mode := Running;
	END Await;

	PROCEDURE Unlock( obj: ProtectedObject;  dummy: BOOLEAN );
	VAR hdr: ObjectHeader;  c: Process;
	BEGIN
		hdr := S.VAL( ObjectHeader, S.VAL( Address, obj ) - Heaps.ProtOfs );
		c := NIL;
		IF hdr.awaitingCond.head # NIL THEN
			c := FindCondition( hdr.awaitingCond );
			IF c # NIL THEN  hdr.locked := TRUE  END;
		END;
		mtxUnlock( hdr.mtx );
		IF c # NIL THEN  conSignal( c.cond )  END;
	END Unlock;

	PROCEDURE RegisterFinalizer( obj: ANY;  fin: Heaps.Finalizer );
	VAR n: Heaps.FinalizerNode;
	BEGIN
		NEW( n ); n.finalizer := fin;  Heaps.AddFinalizer( obj, n );
	END RegisterFinalizer;


	PROCEDURE BodyStarter;
	VAR p{UNTRACED}: Process;  proc: Body;  id: cThread; res: LONGINT; prevBP, type: Address;
	BEGIN
		mtxLock( start1 );
			id := thrThis(0);  
			newProcess.id := id;
			newProcess.SP := Machine.CurrentSP(  );  
			newProcess.stackBottom := Machine.CurrentBP( );
			S.GET( newProcess.stackBottom, prevBP );
			S.PUT( prevBP, S.VAL( Address, 0 ) );	(* for terminating Reflection.StackTraceBack *)
			proc := newProcess.proc; 
			Machine.Acquire( Machine.Heaps );
			(* processes # NIL *)
			newProcess.processLink := processes;  processes := newProcess;
			p := newProcess;  
			INC( noThreads );
			Machine.Release( Machine.Heaps );
			IF traceThreads  THEN
				Trace.Ln;  Trace.String( "starting thread " ); Trace.Int( noThreads, 1 ); Trace.Ln
			END;
		mtxUnlock( start1 );
		conSignal( childrunning );
		SetPriority( p.priority );
		IF Restart IN p.flags THEN
			res := Unix.sigsetjmp( S.ADR( p.state0[0] ), 1 );
		END;
		IF p.obj # NIL THEN  S.GET( S.VAL( Address, p.obj ) - AdrSize, type )  ELSE  type := 0  END;
		p.mode := Running;
		proc( type, p.obj );
		p.mode := Terminated;
		Exit
	END BodyStarter;


	PROCEDURE CreateProcess( body: Body;  priority: LONGINT;  flags: SET;  obj: ProtectedObject );
	VAR p: Process;  hdr: ObjectHeader;
	BEGIN
		mtxLock( createmtx );
		hdr := S.VAL( ObjectHeader, S.VAL( Address, obj ) - Heaps.ProtOfs );
		hdr.mtx := mtxInit( 0 );  hdr.locked := FALSE;
		IF priority = 0 THEN  priority := Normal  END;
		NEW( p, obj, body, priority, flags, stacksize ) ;	(* execute ObjBodyStarter as new (posix or solaris) thread *)
		mtxUnlock( createmtx );
		RegisterFinalizer( obj, FinalizeActiveObj )
	END CreateProcess;

	PROCEDURE FinalizeActiveObj( obj: ANY );
	VAR p: Process;
	BEGIN
		Machine.Acquire( Machine.Heaps );
		p := processes;
		WHILE (p # NIL) & (p.obj # obj) DO p := p.processLink  END;
		IF (p # NIL) & (p.obj = obj) THEN
			p.mode := Terminated;
			Machine.Release( Machine.Heaps );
			conDestroy( p.cond );
			p.cond := 0;
			FinalizeProtObject( obj );
			p.Cancel
		ELSE
			Machine.Release( Machine.Heaps )
		END;
	END FinalizeActiveObj;

	PROCEDURE FinalizeProtObject( obj: ANY );
	VAR hdr: ObjectHeader;
	BEGIN
		hdr := S.VAL( ObjectHeader, S.VAL( Address, obj ) - Heaps.ProtOfs );
		IF hdr.mtx # 0 THEN
			mtxDestroy( hdr.mtx );
			hdr.mtx := 0
		END
	END FinalizeProtObject;


	PROCEDURE FinalizeProcess( obj: ANY );
	VAR p: Process;
	BEGIN
		p := obj(Process);
		IF p.cond # 0 THEN
			conDestroy( p.cond );  p.cond := 0
		END
	END FinalizeProcess;
	
	(** Terminate calling thread. *)
	PROCEDURE Exit;
	VAR prev, p, me: Process;
	BEGIN
		me := This();
		me.mode := Terminated;
		Machine.Acquire( Machine.Heaps );
		prev := NIL;  p := processes;
		WHILE (p # NIL ) & (p # me) DO  prev := p;  p := p.processLink  END;
		IF p = me THEN
			IF prev = NIL THEN  processes := p.processLink  ELSE  prev.processLink := p.processLink  END;
			DEC( noThreads )
		END ;
		Machine.Release( Machine.Heaps );
		IF traceThreads & (noThreads < 100) THEN
			Trace.Ln;
			Trace.String( "termiating thread" ); 
			Trace.String( ", threads left: " );  Trace.Int( noThreads, 1 );  Trace.Ln
		END;
		thrExit(0)
	END Exit;

	PROCEDURE ExitTrap*;
	VAR p: Process;
	BEGIN
		p := This();
		(* restart the object body if it was given the SAFE flag *)
		IF Restart IN p.flags THEN
			Trace.String( "restarting thread" ); 
			Unix.siglongjmp( S.ADR( p.state0[0] ), 1 )
		END;
		Exit
	END ExitTrap;
	

	PROCEDURE SetPriority*( pri: LONGINT );		(* Set the current process' priority. *)
	VAR me: Process;
	BEGIN
		IF Machine.prioHigh > Machine.prioLow THEN
			me := This();
			me.SetPriority( pri )
		END
	END SetPriority;
	
	(** Get the current thread beeing processed. *)
	PROCEDURE This( ): Process;
	VAR me: cThread;  p: Process;
	BEGIN
		me := thrThis(0);
		p := processes;
		WHILE (p # NIL ) & (p.id # me) DO  p := p.processLink  END;
		RETURN p
	END This;

	PROCEDURE CurrentProcess*( ): Process;		(* Return current process. (DEPRECATED, use ActiveObject) *)
	BEGIN
		RETURN This();
	END CurrentProcess;

	PROCEDURE GetProcessID*( ): LONGINT;
	VAR p: Process;
	BEGIN
		p := This();
		RETURN p.id;
	END GetProcessID;



	PROCEDURE ActiveObject*( ): ANY;		(* Return the active object currently executing. *)
	VAR p: Process;
	BEGIN
		p := This();
		RETURN S.VAL( ANY, p.obj )
	END ActiveObject;
	
	
	(** Set the calling thread to sleep for the specified amount of milliseconds. *)
	PROCEDURE Sleep*( ms: LONGINT );
	BEGIN
		thrSleep( ms )
	END Sleep;

	PROCEDURE Yield*;	(* Relinquish control. *)
	BEGIN
		thrPass(0);
	END Yield;


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
		t := queue.head;
		IF t # NIL THEN
			IF t = queue.tail THEN  queue.head := NIL;  queue.tail := NIL
			ELSE  queue.head := t.succ;  t.succ := NIL
			END
		END;
		new := t
	END Get;

	PROCEDURE Put( VAR queue: ProcessQueue;  t: Process );
	BEGIN
		IF queue.head = NIL THEN  queue.head := t  ELSE  queue.tail.succ := t  END;
		queue.tail := t
	END Put;

	(*---------------------------- Timer --------------------------------*)


	PROCEDURE Remove( t: Timer );  (* remove timer from list of active timers *)
	VAR p, x: Timer;
	BEGIN
		t.trigger := 0;  t.handler := NIL;
		IF timers # NIL THEN
			IF t = timers THEN  
				timers := t.next
			ELSE
				p := timers;  x := p.next;
				WHILE (x # NIL) &(x # t)  DO  p := x;  x := p.next  END;
				IF x = t THEN  p.next := t.next  END
			END;
			t.next := NIL
		END;
	END Remove;
	
	PROCEDURE Insert( t: Timer );
	VAR  p, x: Timer;
	BEGIN
		p := NIL;  x := timers;
		WHILE (x # NIL) &(x.trigger < t.trigger)  DO  p := x;  x := p.next  END;
		t.next := x;
		IF p = NIL THEN  timers := t  ELSE   p.next := t  END;
	END Insert;

	PROCEDURE SetTimeout*( t: Timer;  h: EventHandler;  ms: LONGINT );
	BEGIN
		ASSERT(( t # NIL ) & ( h # NIL ));
		mtxLock( tmtx ); 
			Remove( t );  
			IF ms < 1 THEN ms := 1 END;
			t.trigger := Machine.Ticks() + ms;  t.handler := h;
			Insert( t );
		mtxUnlock( tmtx );
	END SetTimeout;

	PROCEDURE SetTimeoutAt*( t: Timer;  h: EventHandler;  ms: LONGINT );
	BEGIN
		ASSERT(( t # NIL ) & ( h # NIL ));
		mtxLock( tmtx );
			Remove( t );
			t.trigger := ms;  t.handler := h;
			Insert( t );
		mtxUnlock( tmtx )
	END SetTimeoutAt;

	PROCEDURE CancelTimeout*( t: Timer );
	BEGIN
		mtxLock( tmtx );  Remove( t );  mtxUnlock( tmtx )
	END CancelTimeout;

	PROCEDURE StartTimer;
	BEGIN
		tmtx := mtxInit(0);  timers := NIL;  
		NEW( timerActivity )
	END StartTimer;

	(*------------------------------------------------------------------*)


	PROCEDURE Terminate*;
	BEGIN
		Exit
	END Terminate;

	PROCEDURE TerminateThis*( p: Process; unbreakable: BOOLEAN );
	BEGIN
		p.mode := Terminated;
		p.Cancel
	END TerminateThis;



	(*------------------------------------------------------------------*)
	
	
	PROCEDURE SuspendActivities*;
	VAR t: Process;  me: cThread;
	BEGIN
		IF traceGC THEN  Trace.String( "Suspending threads " )  END;
		me := thrThis(0);
		t := processes;
		WHILE t # NIL DO
			IF t.id # me THEN
				IF traceGC THEN  Trace.Char( "." )  END;
				thrSuspend( t.id )
			END;
			t := t.processLink
		END;
		IF traceGC THEN  Trace.Ln  END;
	END SuspendActivities;

	PROCEDURE ResumeActivities*;
	VAR t: Process;  me: cThread;
	BEGIN
		IF traceGC THEN  Trace.String( "Resuming threads " )  END;
		me := thrThis(0);
		t := processes;
		WHILE t # NIL DO
			IF t.id # me THEN
				IF traceGC THEN  Trace.Char( "." )  END;
				thrResume( t.id )
			END;
			t := t.processLink
		END;
		IF traceGC THEN  Trace.Ln  END;
	END ResumeActivities;
	
	PROCEDURE FindRootsInStacks;
	VAR p: Process;  
	BEGIN
		IF traceGC  THEN  Trace.String( "mark stacks:  " )  END;
		p := processes;  
		WHILE p # NIL DO 
			p.FindRoots;
			p := p.processLink
		END;
		IF traceGC  THEN  Trace.String( " done" );  Trace.Ln  END;
	END FindRootsInStacks;

	PROCEDURE SaveSP;   (* save current SP for usage by the GC *)
	VAR me: cThread;  t: Process;
	BEGIN
		me := thrThis(0);  t := processes;
		WHILE (t # NIL ) & (t.id # me) DO  t := t.processLink  END;
		IF t # NIL THEN  t.SP := Machine.CurrentSP( )  END
	END SaveSP;
	
	PROCEDURE GetCpuCycles*( process : Process; VAR cpuCycles: CpuCyclesArray; all: BOOLEAN );
	VAR i : LONGINT;
	BEGIN
		ASSERT( process # NIL );
		FOR i := 0 TO Machine.MaxCPU-1 DO  cpuCycles[i] := 0  END;
		(*
		IF ~all THEN
			FOR i := 0 TO Machine.MaxCPU-1 DO
				cpuCycles[i] := cpuCycles[i] - process.lastCpuCycles[i];
				process.lastCpuCycles[i] := process.cpuCycles[i]; (* actually could have changed meanwhile *)
			END;
		END;
		*)
	END GetCpuCycles;


	PROCEDURE GetStacksize;
	VAR str: ARRAY  32 OF  CHAR;  i: LONGINT;
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

	PROCEDURE GetHostSystem;
	BEGIN
		IF Unix.version = "Solaris" THEN  hostSystem := Solaris
		ELSIF Unix.version = "Linux" THEN  hostSystem := Linux
		ELSIF Unix.version = "Darwin"  THEN  hostSystem := Darwin
		ELSE  hostSystem := Unknown
		END
	END GetHostSystem;

	
	PROCEDURE Convert;
	VAR p: Process;
	BEGIN
		(* make current thread the first active object  *)
		NEW( p, NIL, NIL, 0, {}, 0 );
	END Convert;

	PROCEDURE Init;
	VAR
		lock: PROCEDURE ( obj: ProtectedObject;  exclusive: BOOLEAN );
		unlock: PROCEDURE ( obj: ProtectedObject;  dummy: BOOLEAN );
		await: PROCEDURE ( cond: Condition;  slink: Address;  obj: ProtectedObject;  flags: SET );
		create: PROCEDURE ( body: Body;  priority: LONGINT;  flags: SET;  obj: ProtectedObject );
	BEGIN
		lock := Lock;  unlock := Unlock;  await := Await;  create := CreateProcess;

		Modules.kernelProc[3] := S.VAL( Address, create);	(* 250 *)
		Modules.kernelProc[4] := S.VAL( Address, await);	(* 249 *)
		Modules.kernelProc[6] := S.VAL( Address, lock);		(* 247 *)
		Modules.kernelProc[7] := S.VAL( Address, unlock);	(* 246 *)

		Unix.Dlsym( 0, "mtxInit",		S.VAL( Address, mtxInit ) );
		Unix.Dlsym( 0, "mtxDestroy",	S.VAL( Address, mtxDestroy ) );
		Unix.Dlsym( 0, "mtxLock",	S.VAL( Address, mtxLock ) );
		Unix.Dlsym( 0, "mtxUnlock",	S.VAL( Address, mtxUnlock ) );
		Unix.Dlsym( 0, "conInit",		S.VAL( Address, conInit ) );
		Unix.Dlsym( 0, "conDestroy",	S.VAL( Address, conDestroy ) );
		Unix.Dlsym( 0, "conWait",	S.VAL( Address, conWait ) );
		Unix.Dlsym( 0, "conSignal",	S.VAL( Address, conSignal ) );
		
		Unix.Dlsym( 0, "thrStart",	S.VAL( Address, thrStart ) );
		Unix.Dlsym( 0, "thrThis",		S.VAL( Address, thrThis ) );
		Unix.Dlsym( 0, "thrSleep",	S.VAL( Address, thrSleep ) );
		Unix.Dlsym( 0, "thrPass",		S.VAL( Address, thrPass ) );
		Unix.Dlsym( 0, "thrExit",		S.VAL( Address, thrExit ) );
		Unix.Dlsym( 0, "thrSuspend",	S.VAL( Address, thrSuspend ) );
		Unix.Dlsym( 0, "thrResume",	S.VAL( Address, thrResume ) );
		Unix.Dlsym( 0, "thrGetPriority",	S.VAL( Address, thrGetPriority ) );
		Unix.Dlsym( 0, "thrSetPriority",	S.VAL( Address, thrSetPriority ) );
		Unix.Dlsym( 0, "thrKill",		S.VAL( Address, thrKill ) );
		
		createmtx := mtxInit( 0 );
		start1 := mtxInit(0);  childrunning := conInit(0); 
		
		
		Machine.saveSP := SaveSP;
					
		traceGC := 1 IN Glue.debug;
		traceThreads := 2 IN Glue.debug;
		
		GetHostSystem;  GetStacksize;  
		
		Convert;
		StartTimer;
	END Init;

BEGIN
	Init;
END Objects.

