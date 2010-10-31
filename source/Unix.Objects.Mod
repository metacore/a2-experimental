(* Aos, Copyright 2001, Pieter Muller, ETH Zurich *)

MODULE Objects;   (** AUTHOR "pjm"; PURPOSE "Active object runtime support"; *)

(*	2006.06.20	g.f.	Unix port  *)
(*	2007.04.13	g.f.	Timer added *)
(*	2007.09.21	g.f.	Lock, Unlock fixed *)

IMPORT S := SYSTEM, Trace, Aos := Basetypes, Glue, Unix, Machine, Heaps, Modules;

CONST

	(* Process flags, meaningless in Unix ports !!! *)
	PleaseHalt* = 10;		(* Process requested to Halt itself soon *)
	Unbreakable*= 11;		(* FINALLY shall not catch HALT exception (PleaseHalt is also set) *)
	SelfTermination*=12;	(* Indicates the process has requested to terminate ifself (PleaseHalt is also set) *)
	Preempted* = 27;		(* Has been preempted. *)
	Resistant* = 28;			(* Can only be destroyed by itself *)


	MinPriority* = Unix.ThreadLow;
	Low* = Unix.ThreadLow;
	Normal* = Unix.ThreadNormal;
	High* = Unix.ThreadHigh;
	GCPriority* = Unix.ThreadHigh;
	Realtime* = Unix.ThreadHigh;

	(* Process flag defined by compiler in OPC.CallRecBody *)
	Restart* = 0;	(* Restart/Destroy process on exception *)

	(* Process modes (in UnixAos Running means Running or Ready!) *)
	Unknown* = 0;  Ready* = 1;  Running* = 2;  AwaitingLock* = 3;
	AwaitingCond* = 4;  AwaitingEvent* = 5;  Terminated* = 6;

	Second* = 1000;	(* frequency of ticks increments in Hz *)

	DefaultStacksize = 128*1024;
	
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
	
	Process* = OBJECT 
			VAR
				processLink-		: Process;
				stackBottom-, SP-	: Address;
				id-		: LONGINT;
				name-	: ARRAY 64 OF CHAR;
				proc	: Body;
				
				succ: Process;   		  		(* in ProcessQueue *)
				obj-: ProtectedObject;		(* associated active object *)
				condition-: Condition;   		(* awaited process' condition *)
				condFP-: Address;			(* awaited process' condition's context *)
				cond: cCond;				(* gets signaled when condition yields true *)
				state0: POINTER TO ARRAY  2048 OF CHAR;
				mode-: LONGINT;
				procID-: LONGINT;
				flags-: SET;
				priority-: LONGINT;
				waitingOn-: ProtectedObject;
				state-: Machine.State;

				PROCEDURE & Initialize( obj: ProtectedObject;  bodyProc: Body;  prio: LONGINT; fl: SET; stacksize: LONGINT );
				VAR ttag: Address;  
				BEGIN
					mtxLock( start );
					SELF.obj := obj;  condition := NIL;  cond := conInit( );
					flags := fl;
					priority := prio;
					processLink := NIL;
					IF processes # NIL THEN
						IF obj # NIL THEN 
							S.GET( S.VAL( Address, obj ) - 4, ttag );
							GetTypeName( ttag, name );
						ELSE
							name := ""
						END;
						newProcess := SELF;
						ASSERT( bodyProc # NIL );
						proc := bodyProc;  
						mtxLock( start1 );
							nid := thrStart( BodyStarter, stacksize );
							conWait( childrunning, start1 );
						mtxUnlock( start1 );
						ASSERT( id = nid );					
						RegisterFinalizer( SELF, FinalizeProcess );
					ELSE 
						name := "Main Thread";
						stackBottom := Glue.stackBottom;  
						SP  := Machine.CurrentSP( );
						id := thrThis();
						processes := SELF;
						noThreads := 1;
					END;
					mode := Ready;
					mtxUnlock( start );
				Sleep( 5 ) (* give the child time to do get a llttle further, needed for paco *) 
				END Initialize;
				
				PROCEDURE Cancel*;
				VAR pt, t: Process;  kt: cThread;
				BEGIN
					IF SELF = This() THEN  Exit
					ELSE
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
							Trace.Ln;  Trace.String( "cancel thread " ); Trace.String( name );
							Trace.String( ", threads left: " );  Trace.Int( noThreads, 1 );  Trace.Ln
						END;
						Machine.Acquire( Machine.X11IO );  (* let the thread to be killed first finish its last I/O, if any *)
						IF kt # 0 THEN  thrKill( kt )  END;
						Machine.Release( Machine.X11IO );
					END
				END Cancel;

				PROCEDURE GetPriority*( ): LONGINT;
				BEGIN
					RETURN thrGetPriority( id ) 
				END GetPriority;

				PROCEDURE SetPriority*( prio: LONGINT );
				BEGIN
					priority := max( plow, min( prio, phigh ) );
					thrSetPriority( id, priority )
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
	(* host system values *)
	Solaris = 1;  Linux = 2;  Darwin = 3;

VAR
	timers: Timer;  
	tmtx: cMutex;
	
	processes-: Process;	(*  Anchor of all instantiated threads in system *)
	noThreads-: LONGINT;
	plow, phigh: LONGINT;   (* permitted thread priorities, both are the same if not running suid root *)
	
	start, start1: cMutex;
	childrunning: cCond;
	newProcess: Process;
	nid: cThread;
	
	
	createmtx: cMutex;

	hostSystem: LONGINT;
	stacksize: LONGINT;
	
	traceGC, traceThreads: BOOLEAN;

	mtxInit-: 		PROCEDURE {REALTIME, C} ( ): cMutex;
	mtxDestroy-: 	PROCEDURE {REALTIME, C}  ( mtx: cMutex );
	mtxLock-: 		PROCEDURE {REALTIME, C}  ( mtx: cMutex );
	mtxUnlock-: 	PROCEDURE {REALTIME, C}  ( mtx: cMutex );

	conInit: 			PROCEDURE {REALTIME, C}  ( ): cCond;
	conDestroy: 	PROCEDURE {REALTIME, C}  ( cond: cCond );
	conWait: 		PROCEDURE {REALTIME, C}  ( cond: cCond;  mtx: cMutex );
	conSignal: 		PROCEDURE {REALTIME, C}  ( cond: cCond );

	thrInitialize: 	PROCEDURE {REALTIME, C} ( VAR low, high: LONGINT ): BOOLEAN;
	
	thrStart: 		PROCEDURE {REALTIME, C} ( p: PROCEDURE;  stackLen: LONGINT ): cThread;
	thrThis: 			PROCEDURE {REALTIME, C} ( ): cThread;
	thrSleep: 		PROCEDURE {REALTIME, C} ( ms: LONGINT );
	thrPass: 		PROCEDURE {REALTIME, C};
	thrExit: 			PROCEDURE {REALTIME, C};
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
			hdr.mtx := mtxInit( );  hdr.locked := FALSE;
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
	VAR t, p: Process;  proc: Body;  id: cThread; res: LONGINT; type: Address;
	BEGIN
		mtxLock( start1 );
			id := thrThis();  
			newProcess.id := id;
			newProcess.SP := Machine.CurrentSP(  );  
			newProcess.stackBottom := Machine.CurrentBP( );
			proc := newProcess.proc; 
			Machine.Acquire( Machine.Heaps );
			t := processes;
			WHILE t.processLink # NIL DO  t := t.processLink  END;
			t.processLink := newProcess;
			INC( noThreads );
			Machine.Release( Machine.Heaps );
			IF traceThreads  THEN
				Trace.Ln;  Trace.String( "starting thread " ); Trace.Int( noThreads, 1 ); Trace.String( "  " );  Trace.String( newProcess.name );  Trace.Ln
			END;
		mtxUnlock( start1 );
		conSignal( childrunning );
		p := newProcess;
		SetPriority( p.priority );
		IF Restart IN p.flags THEN
			NEW( p.state0 );
			res := Unix.sigsetjmp( S.ADR( p.state0[0] ), 1 );
		ELSE  
			p.state0 := NIL
		END;
		IF p.obj # NIL THEN  S.GET( S.VAL( Address, p.obj ) - AdrSize, type )  ELSE type := 0  END;
		proc( type, p.obj );
		Exit
	END BodyStarter;


	PROCEDURE CreateProcess( body: Body;  priority: LONGINT;  flags: SET;  obj: ProtectedObject );
	VAR p: Process;  hdr: ObjectHeader;
	BEGIN
		mtxLock( createmtx );
		hdr := S.VAL( ObjectHeader, S.VAL( Address, obj ) - Heaps.ProtOfs );
		hdr.mtx := mtxInit ();  hdr.locked := FALSE;
		NEW( p, obj, body, priority, flags, stacksize ) ;	(* execute ObjBodyStarter as new (posix or solaris) thread *)
		mtxUnlock( createmtx );
		RegisterFinalizer( obj, FinalizeActiveObj )
	END CreateProcess;

	PROCEDURE FinalizeActiveObj( obj: ANY );
	VAR t: Process;
	BEGIN
		t := processes;
		WHILE (t # NIL) & (t.obj # obj) DO t := t.processLink  END;
		IF (t # NIL) & (t.obj = obj) THEN
			conDestroy( t.cond );
			t.cond := 0;
			FinalizeProtObject( obj );
			t.Cancel
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
	VAR pt, t, me: Process;
	BEGIN
		me := This();
		Machine.Acquire( Machine.Heaps );
		pt := NIL;  t := processes;
		WHILE (t # NIL ) & (t # me) DO  pt := t;  t := t.processLink  END;
		IF t = me THEN
			IF pt = NIL THEN  processes := t.processLink  ELSE  pt.processLink := t.processLink  END;
			DEC( noThreads )
		END ;
		Machine.Release( Machine.Heaps );
		IF traceThreads & (noThreads < 100) THEN
			Trace.Ln;
			Trace.String( "termiating " ); Trace.String( t.name );
			Trace.String( ", threads left: " );  Trace.Int( noThreads, 1 );  Trace.Ln
		END;
		thrExit
	END Exit;

	PROCEDURE ExitTrap*;
	VAR p: Process;
	BEGIN
		p := This();
		IF ~Glue.systemTerminating  THEN
			(* restart the object body if it was given the SAFE flag *)
			IF p.state0 # NIL THEN
				Trace.String( "restarting " ); Trace.StringLn( p.name );
				Unix.siglongjmp( S.ADR( p.state0[0] ), 1 )
			END
		END;
		Exit
	END ExitTrap;
	

	PROCEDURE SetPriority*( pri: LONGINT );		(* Set the current process' priority. *)
	VAR me: Process;
	BEGIN
		IF phigh > plow THEN
			me := This();
			me.SetPriority( pri )
		END
	END SetPriority;
	
	(** Get the current thread beeing processed. *)
	PROCEDURE This( ): Process;
	VAR me: cThread;  p: Process;
	BEGIN
		me := thrThis();
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
		thrPass;
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

	PROCEDURE tSleep( ms: LONGINT );
	BEGIN
		mtxUnlock( tmtx );  Sleep( ms );  mtxLock( tmtx )
	END tSleep;

	
	PROCEDURE timer( type: Address; obj: ProtectedObject );
	CONST Interval = 10;
	VAR sleeptime: LONGINT;  t: Timer; 
	BEGIN
		mtxLock( tmtx );  
		LOOP
			t := timers;
			IF t # NIL THEN
				sleeptime := t.trigger - Machine.Ticks();  
				IF sleeptime > Interval THEN  tSleep( Interval );  DEC( sleeptime, Interval )
				ELSIF sleeptime > 0 THEN  tSleep( sleeptime );  sleeptime := 0
				END;
				IF (sleeptime <= 0) & (t.handler # NIL) THEN  (* expired, not canceled *)
					t.handler;
					Remove( t );
				END;
			ELSE
				tSleep( Interval )
			END
		END
	END timer;

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
	VAR p: Process;
	BEGIN
		tmtx := mtxInit();  timers := NIL;  
		NEW( p, NIL, timer, phigh, {Restart}, 10000 ); 
	END StartTimer;

	(*------------------------------------------------------------------*)


	PROCEDURE Terminate*;
	BEGIN
		Exit
	END Terminate;

	PROCEDURE TerminateThis*( t: Process; unbreakable: BOOLEAN );
	BEGIN
		t.Cancel
	END TerminateThis;



	(*------------------------------------------------------------------*)
	
	
	PROCEDURE SuspendActivities;
	VAR t: Process;  me: cThread;
	BEGIN
		IF traceGC THEN  Trace.String( "Suspending threads " )  END;
		me := thrThis();
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

	PROCEDURE ResumeActivities;
	VAR t: Process;  me: cThread;
	BEGIN
		IF traceGC THEN  Trace.String( "Resuming threads " )  END;
		me := thrThis();
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
	VAR p: Process;  sp, ptr: Address;
	BEGIN
		IF traceGC  THEN  Trace.String( "mark stacks:  " )  END;
		p := processes;  
		WHILE p # NIL DO
			IF traceGC  THEN  Trace.Char( '.' )  END;
			sp := p.SP - 32;
			WHILE sp < p.stackBottom DO  
				S.GET( sp, ptr );  Heaps.AddCandidate( ptr );  INC( sp, AdrSize )  
			END;
			p := p.processLink
		END;
		IF traceGC  THEN  Trace.String( " done" );  Trace.Ln  END;
	END FindRootsInStacks;
	


	PROCEDURE {REALTIME} SaveSP;   (* save current SP for usage by the GC *)
	VAR me: cThread;  t: Process;
	BEGIN
		me := thrThis();  t := processes;
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

	PROCEDURE Append( VAR ar: ARRAY OF CHAR;  CONST this: ARRAY OF CHAR );
	VAR i, j: LONGINT;
	BEGIN
		i := 0;  j := 0;
		WHILE ar[i] # 0X DO  INC( i )  END;
		WHILE (i < LEN( ar ) - 1) & (this[j] # 0X) DO  ar[i] := this[j];  INC( i );  INC( j )  END;
		ar[i] := 0X
	END Append;

	PROCEDURE GetTypeName( tag: Address;  VAR name: ARRAY OF CHAR );
	VAR  typ: Aos.TypeDesc;
	BEGIN
		S.GET( tag - 4, typ );  name[0] := 0X;
		IF typ.mod # NIL THEN  Append( name, typ.mod.name );  Append( name,  "." )  END;
		Append( name, typ.name )
	END GetTypeName;

	PROCEDURE GetStacksize;
	VAR str: ARRAY  32 OF  CHAR;  i: LONGINT;
	BEGIN
		Machine.GetConfig( "Stacksize", str );
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

	PROCEDURE InitThreads;
	VAR res: BOOLEAN; 
	BEGIN
		res := thrInitialize( plow, phigh );
		IF res THEN
			start := mtxInit();  start1 := mtxInit();  childrunning := conInit( ); 
			createmtx := mtxInit( );
			processes := NIL; 
		ELSE
			Trace.StringLn( "Objects.InitThreads: no threads support in boot environment.  teminating" ); 
			Unix.exit( 1 )
		END;
	END InitThreads;

	
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
		Unix.Dlsym( 0, "thrInitialize",	S.VAL( Address, thrInitialize ) );
		
		InitThreads;
		
		Machine.saveSP := SaveSP;
		Heaps.findRootsInStacks := FindRootsInStacks;
		Heaps.suspendActivities := SuspendActivities;
		Heaps.resumeActivities := ResumeActivities;
		
		traceGC := 1 IN Glue.debug;
		traceThreads := 2 IN Glue.debug;
		
		GetHostSystem;  GetStacksize;  
		
		Convert;
		StartTimer;
	END Init;

BEGIN
	Init;
END Objects.

