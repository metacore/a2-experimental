(* ETH Oberon, Copyright 2002 ETH Zuerich Institut fuer Computersysteme, ETH Zentrum, CH-8092 Zuerich.
Refer to the "General ETH Oberon System Source License" contract available at: http://www.oberon.ethz.ch/ *)

MODULE Heaps;

IMPORT S := SYSTEM, Glue, Trace, Machine;

TYPE
	Address = S.ADDRESS;
	Size = S.SIZE;


CONST
	Stats* = TRUE; (* maintain statistical counters *)

	
	AdrSize = S.SIZEOF( S.ADDRESS );
	SizeSize = S.SIZEOF( S.SIZE );

	TypeDescOffset* = -AdrSize;

	FlagsOfs = AdrSize * 3;			(* flags offset in TypeDesc *)
	ModOfs* = AdrSize * 4;			(* moduleAdr offset in TypeDesc *)
(*	TypeNameOfs = AdrSize * 5;		(* type name offset in TypeDesc *)
	ModNameOfs = AdrSize * 2;		(* module name offset in ModuleDesc *)
*)	
	
	NilVal* = 0;

	MaxHeapBlockSize = 512*1024*1024;

	MinPtrOfs = -40000000H;	(* sentinel offset for ptrOfs *)
	MethodEndMarker* = MinPtrOfs;   (* marks the end of the method addresses, used in Info.ModuleDetails *)

	ArrayAlignment = 8;
	
	MaxMarkDepth = 10000;

VAR

	debug: SET;

	(* ----------------- object finalization ------------------------------*)

TYPE
	Finalizer* = PROCEDURE {DELEGATE}( obj: ANY );

	FinalizerNode* = POINTER TO RECORD
				objWeak*{UNTRACED}: ANY;	(* weak reference to checked object *)
				markAdr: Address;   				(* address of type tag of object *)
				nextFin: FinalizerNode;   		(* in finalization list *)
				objStrong*: ANY;   				(* strong reference to object to be finalized *)
				finalizer*{UNTRACED}: Finalizer;	(* finalizer, if any *)
				finalizerStrong: Finalizer			(* strong ref. to the obj that is referenced by the finalyzer, if any *)
			END;

VAR
	checkRoot: FinalizerNode;   (* list of checked objects (contains weak references to the checked objects) *)
	finalizeRoot: FinalizerNode;   (* objects scheduled for finalization (contains references to scheduled objects) *)

	(* ------------------------- Heap ------------------------------- *)
CONST
	BlockSize = 32;
	N = 32;  
	ProtOfs* = BlockSize + 16;
	ProtTypeBit* = 31;   (** flags in TypeDesc, low bits reserved for extLevel *)

	MarkBit* = 0;  ArrayBit* = 1;  FreeBit* = 2;  SubObjBit* = 3;  ProtObjBit* = 4;
	FlagBits* = {MarkBit, ArrayBit, FreeBit, SubObjBit, ProtObjBit};

TYPE
	FreeBlk = POINTER TO RECORD
				tag: Address;  (* = S.ADR( size ) *)
				size: Size;
				next{UNTRACED}: FreeBlk;
			END;

	RootObject* = OBJECT 
		PROCEDURE FindRoots*;	(** abstract *)
		BEGIN HALT( 301 ) END FindRoots;
	END RootObject;

	StaticTypeBlock*= POINTER TO StaticTypeDesc;
	StaticTypeDesc = RECORD
		recSize: Size;
		pointerOffsets* {UNTRACED}: PointerOffsets;
	END;

	PointerOffsets = POINTER TO ARRAY OF Size;
	
VAR
	A: ARRAY N + 1 OF  (*FreeBlk*) Address;
	lastA: ARRAY N + 1 OF Address;
	candidates: ARRAY 1024 OF  Address;
	nofcand: LONGINT;
	
	deferred: ARRAY 1000 OF Address;
	noDeferred: LONGINT;
	
	fastNEW: BOOLEAN;	(* TRUE:  faster NEW is preferred over smaller heap *)

	heapSize, heapAvailable: Size;

	throuput:  Size;
	NgetBlock: LONGINT;
	getBlockFinished: LONGINT;
	GCEnabled: BOOLEAN;
	GC*: PROCEDURE;
	collecting-: BOOLEAN;
	markDepth: LONGINT;

	traceGC, traceNEW: BOOLEAN;
	
	(** Statistics. Will only be maintained if Stats = TRUE *)

	(** Memory allocation statistics *)
	Nnew- : LONGINT;			(** Number of times NewBlock has been called since system startup *)
	NnewBytes- : HUGEINT;		(** Number of bytes allocated by NewBlock since system startup *)

	(** Garbage collection statistics *)
	Ngc- : LONGINT;  (** Number of GC cycles since system startup *)

	(** Statistics considering the last GC cyle *)
	Nmark-, Nmarked-, NfinalizeAlive-, NfinalizeDead-: LONGINT;
	NgcCyclesMark-, NgcCyclesLastRun-, NgcCyclesMax-, NgcCyclesAllRuns- : HUGEINT;

	PROCEDURE EmptyProc;
	END EmptyProc;

	(* ----------------- object finalization ---------------------------*)


	PROCEDURE AddFinalizer*( obj: ANY;  n: FinalizerNode );
	VAR adr: Address;
	BEGIN
		n.objWeak := obj;  n.objStrong := NIL;  n.finalizerStrong := NIL;
		adr := S.VAL( Address, obj );
		IF SubObjBit IN S.VAL( SET, obj ) THEN  (* indirect tag *)
			n.markAdr := S.GET32( adr - AdrSize ) - AdrSize
		ELSIF ProtObjBit IN S.VAL( SET, obj ) THEN  (* protected object *)
			n.markAdr := adr - ProtOfs - AdrSize
		ELSE  n.markAdr := adr - AdrSize
		END;
		Machine.Acquire( Machine.Heaps );
		n.nextFin := checkRoot;  checkRoot := n;
		Machine.Release( Machine.Heaps )
	END AddFinalizer;

	(* Check reachability of finalized objects. *)
	PROCEDURE CheckFinalizedObjects;
	VAR n, p, t: FinalizerNode;  n1, n2: LONGINT;

		PROCEDURE MarkDelegate( p: Finalizer );
		VAR pointer: ANY;
		BEGIN
			S.GET( S.ADR( p ) + AdrSize, pointer );
			IF pointer # NIL THEN  Mark( pointer )  END
		END MarkDelegate;

	BEGIN
		IF traceGC  THEN  n1 := 0;  n2 := 0;  Trace.String( "CheckFinalizedObjects: " )  END;
		n := checkRoot;
		WHILE n # NIL DO  (* move unmarked checked objects to finalize list *)
			INC( n1 );
			IF ~(MarkBit IN S.VAL( SET, S.GET32( n.markAdr ) )) THEN
				INC( n2 );
				IF n = checkRoot THEN  checkRoot := n.nextFin  ELSE  p.nextFin := n.nextFin  END;
				n.objStrong := n.objWeak;		(* anchor the object for finalization *)
				n.finalizerStrong := n.finalizer;	(* anchor the finalizer for finalization *)
				t := n.nextFin;  n.nextFin := finalizeRoot;  finalizeRoot := n;  n := t;
				IF Stats THEN DEC(NfinalizeAlive); INC(NfinalizeDead) END
			ELSE  p := n;  n := n.nextFin
			END
		END;

		(* now trace the weak references to keep finalized objects alive during this collection *)
		n := finalizeRoot;
		WHILE n # NIL DO
			MarkDelegate( n.finalizerStrong );
			Mark( n.objStrong );  n := n.nextFin
		END;

		n := checkRoot;
		WHILE n # NIL DO (* list of objects that had been marked before entering CheckFinalizedObjects *)
			(* we still have to mark the weak finalizers, as they might have not been marked before  *)
			MarkDelegate( n.finalizer );  n := n.nextFin
		END;
		IF traceGC  THEN
			Trace.String( "objects: " );  Trace.Int( n1, 1 );
			Trace.String( ", objects to finalize: " );  Trace.Int( n2, 1 );  Trace.Ln
		 END
	END CheckFinalizedObjects;

	(** Return the next scheduled finalizer or NIL if none available.  Called by finalizer object in AosKernel. *)
	PROCEDURE GetFinalizer*( ): FinalizerNode;
	VAR n: FinalizerNode;
	BEGIN
		n := NIL;
		IF finalizeRoot # NIL THEN
			Machine.Acquire( Machine.Heaps );
			n := finalizeRoot;   (* take one finalizer *)
			IF n # NIL THEN
				finalizeRoot := n.nextFin;   n.nextFin := NIL;
				IF Stats THEN DEC(NfinalizeDead) END;
			END;
			Machine.Release( Machine.Heaps );
		END;
		RETURN n
	END GetFinalizer;

	(** Check finalizers registered in the specified module, which is about to be freed or shut down.
			Remove all finalizer procedures in this module from the finalizer lists so they won't be called any more. *)
	PROCEDURE CleanupModuleFinalizers*( codeAdr: Address; codeLen: Size;  CONST name: ARRAY OF CHAR );
	VAR n, p, t: FinalizerNode;  codeEnd: Address;  N1, N2: LONGINT;
	BEGIN
		codeEnd := codeAdr + codeLen;  N1 := 0; N2 := 0;
		Machine.Acquire( Machine.Heaps );
		n := checkRoot;
		WHILE n # NIL DO  (* iterate over checked list *)
			t := n;  n := n.nextFin;
			IF Machine.LessOrEqual( codeAdr, S.VAL( Address, t.finalizer ) ) & 
			    Machine.LessOrEqual( S.VAL( Address, t.finalizer ), codeEnd ) THEN
				IF t = checkRoot THEN  checkRoot := t.nextFin  ELSE  p.nextFin := t.nextFin  END;
				IF Stats THEN DEC(NfinalizeAlive) END;
				INC( N1 )
			ELSE  
				p := t
			END
		END;
		(* also remove finalizers from list, so they won't be called *)
		n := finalizeRoot;
		WHILE n # NIL DO  (* iterate over finalized list *)
			t := n;  n := n.nextFin;
			IF Machine.LessOrEqual( codeAdr, S.VAL( Address, t.finalizer ) ) & 
			    Machine.LessOrEqual( S.VAL( Address, t.finalizer ), codeEnd ) THEN
				IF t = finalizeRoot THEN  finalizeRoot := t.nextFin  ELSE  p.nextFin := t.nextFin  END;
				IF Stats THEN DEC(NfinalizeDead) END;
				INC( N2 )
			ELSE  
				p := t
			END
		END;
		Machine.Release( Machine.Heaps );
		IF (N1 # 0) OR (N2 # 0) THEN
			Machine.Acquire ( Machine.TraceOutput );
			Trace.String( name );  Trace.Char( " " );
			Trace.Int( N1, 1 );  Trace.String( " discarded finalizers, " );
			Trace.Int( N2, 1 );  Trace.StringLn( " pending finalizers" );
			Machine.Release ( Machine.TraceOutput );
		END
	END CleanupModuleFinalizers;
	
	
	
	(* Add a root object to the set of traversable objects. If in allocated heap then mark and traverse, if in Module Heap (Bootfile) then only traverse. *)
	PROCEDURE AddRootObject*( rootObject: RootObject );
	BEGIN
		IF rootObject = NIL THEN (* nothing *)
		(*
		ELSIF CheckPointer(SYSTEM.VAL(SYSTEM.ADDRESS,rootObject)) THEN
			(* object in heap, must be fully marked and traversed *)
			Mark(rootObject)
		ELSE
			(* object in bootfile, traverse as root object only *)
			rootObject.nextRoot := rootList; rootList := rootObject;	(* link root list *)
		*)
		ELSE
			Mark( rootObject )
		END;
	END AddRootObject;



	(* ------------------------- garbage collector ----------------------- *)


	PROCEDURE UnmarkedObject( ptr: ANY ): BOOLEAN; (* FALSE: alredy marked or sysblock or subobj *)
	VAR taddr, haddr, block: Address;  hval, tag: SET;  sysblock: BOOLEAN;
	BEGIN
		IF ptr = NIL THEN  RETURN FALSE  END;
		block := S.VAL( Address, ptr );
		IF ~ValidPointer( block ) THEN  RETURN FALSE  END;	
		sysblock := FALSE;  taddr := block - AdrSize;
		IF SubObjBit IN S.VAL( SET, block ) THEN
			(* Subobject or sysblock *)
			S.GET( taddr, tag );
			haddr := S.VAL( Address, tag - {ArrayBit, MarkBit} ) - AdrSize;
			IF taddr - haddr # 24 THEN
				(* subobject! don't mark it *)  RETURN FALSE
			END;
			sysblock := TRUE
		ELSIF ProtObjBit IN S.VAL( SET, block ) THEN  haddr := taddr - ProtOfs;
		ELSE  haddr := taddr;
		END;

		S.GET( haddr, hval );
		IF ~(MarkBit IN hval) THEN
			S.PUT( haddr, hval + {MarkBit} );   (* mark this block *)  INC( Nmarked );
			IF ~sysblock THEN  
				IF ptr IS RootObject THEN  ptr(RootObject).FindRoots  END;	
				RETURN TRUE  
			END
		END;
		RETURN FALSE
	END UnmarkedObject;

	PROCEDURE MarkRecordFields( rec: Address; sTB: StaticTypeBlock );
	VAR ptr: ANY; i, n: Size;  
	BEGIN
		n := LEN( sTB.pointerOffsets ); i := 0;
		WHILE i < n DO
			S.GET( rec + sTB.pointerOffsets[i], ptr );
			IF ptr # NIL THEN  Mark( ptr )  END;
			INC( i )
		END
	END MarkRecordFields;
	
	PROCEDURE Mark*( ptr: ANY );
	VAR 
		block, cur, lastElem: Address;  
		tag: SET;  sTB{UNTRACED}: StaticTypeBlock;
		depth: LONGINT;
	BEGIN
		IF Stats THEN  INC(Nmark)  END;
		INC( markDepth );  depth := markDepth;
		
		IF UnmarkedObject( ptr ) THEN
			block := S.VAL( Address, ptr );
			S.GET( block - AdrSize, tag );
			sTB := S.VAL( StaticTypeBlock, tag - {ArrayBit, MarkBit} );
			IF ArrayBit IN tag THEN
				IF markDepth <= MaxMarkDepth - 10 THEN
					 S.GET( block, lastElem );
					 S.GET( block + 2*AdrSize, cur );   
					 REPEAT
						MarkRecordFields( cur, sTB );						
						INC( cur, sTB.recSize );
					UNTIL Machine.GreaterThan( cur, lastElem )
				ELSE
					deferred[noDeferred] := block;  INC( noDeferred );
				END;
			ELSE  
				IF markDepth <= MaxMarkDepth THEN
					MarkRecordFields( block, sTB )
				ELSE
					deferred[noDeferred] := block;  INC( noDeferred );
				END;	
			END;			
		END;
		DEC( markDepth );
		IF (markDepth <= 0) & (noDeferred > 0) THEN  MarkDeferred  END
	END Mark;

	PROCEDURE MarkDeferred;
	VAR 
		block, cur, lastElem: Address;  
		tag: SET;  sTB{UNTRACED}: StaticTypeBlock;
	BEGIN
		markDepth := 1;
		WHILE noDeferred > 0 DO
			DEC( noDeferred );  
			block := deferred[noDeferred];  
			S.GET( block - AdrSize, tag );
			sTB := S.VAL( StaticTypeBlock, tag - {ArrayBit, MarkBit} );
			IF ArrayBit IN tag THEN
				 S.GET( block, lastElem );
				 S.GET( block + 2*AdrSize, cur );   
				 REPEAT
					MarkRecordFields( cur, sTB );						
					INC( cur, sTB.recSize );
				UNTIL Machine.GreaterThan( cur, lastElem )
			ELSE  
				MarkRecordFields( block, sTB )
			END;			
		END;
	END MarkDeferred;


	
	PROCEDURE Recycle( blkAdr: Address; blkSize: Size; atEnd: BOOLEAN );
	VAR i: LONGINT;  block, x: FreeBlk;
	BEGIN
		i := blkSize DIV BlockSize;
		IF i > N THEN  i := N  END;
		block := S.VAL( FreeBlk, blkAdr );
		
		block.tag := blkAdr + AdrSize;
		block.size := blkSize - AdrSize;
		
		IF (i < N) OR fastNEW THEN	
			IF atEnd THEN
				(* append to end of list *)
				block.next := NIL;
				S.PUT( lastA[i], blkAdr );  
				lastA[i] := S.ADR( block.next )
			ELSE
				(* prepend to list *)
				block.next := S.VAL( FreeBlk, A[i] );
				A[i] := blkAdr
			END;	
		ELSE
			(* keep them ordered to avoid unnecessary splits *)
			(* this optimization has positive impact on heap utilization
			    130 MB vs. 240 MB heap for compiling and linking a new system
			    but it slows down heap allocation speed. 	*)
			x := S.VAL( FreeBlk, A[N] );
			IF (x = NIL) OR (x.size > blkSize - AdrSize) THEN 
				block.next := x;
				A[N] := blkAdr
			ELSE
				WHILE ( x.next # NIL) & (x.next.size < blkSize - AdrSize) DO  x := x.next  END;
				block.next := x.next;
				x.next := block 
			END	
		END;	
		
		INC( heapAvailable, blkSize );
	END Recycle;
	
	PROCEDURE InitFreeLists;
	VAR i: LONGINT;
	BEGIN
		FOR i := 0 TO N DO
			A[i] := NilVal;  lastA[i] := S.ADR( A[i] );
		END
	END InitFreeLists;

	PROCEDURE Sweep;
	VAR
		block, freeBlock, endBlockAdr: Address;  tag: SET;  
		size, freeSize: Size;
		memBlock, nextMemBlock: Machine.MemoryBlock;
	BEGIN
		IF traceGC  THEN  Trace.String( "Sweep" );  Trace.Ln  END;
		InitFreeLists;
		heapAvailable := 0; 

		memBlock := Machine.memBlockHead;  
		WHILE memBlock # NIL DO
			block := memBlock.beginBlockAdr;  endBlockAdr := memBlock.endBlockAdr;

			freeSize := 0;
			WHILE Machine.LessThan( block, endBlockAdr ) DO
				size := SizeOf( block );
				S.GET( block, tag );
				IF ~(MarkBit IN tag) THEN
					(* collect *)
					IF freeSize = 0 THEN  freeBlock := block  END;
					INC( freeSize, size );
				ELSE
					S.PUT( block, tag - {MarkBit} );	(* remove mark bit *)
					IF freeSize > 0 THEN
						Recycle( freeBlock, freeSize, TRUE );
						freeSize := 0
					END
				END;
				INC( block, size );
			END;

			(* last collected block: *)
			nextMemBlock := memBlock.next;
			IF (freeSize = endBlockAdr - memBlock.beginBlockAdr)  THEN
				(* whole block is free, unlink it*)
				Machine.FreeMemBlock( S.VAL( Machine.MemoryBlock, memBlock ) );
				heapSize := GetHeapSize();
			ELSIF freeSize > 0 THEN
				Recycle( freeBlock, freeSize, TRUE ); (* last collected block: *)
			END;
			
			memBlock := nextMemBlock;
		END
	END Sweep;


	PROCEDURE SizeOf( block: Address ): Size;
	VAR tag: SET;  lastElem: Address;  recSize, blockSize: Size;
	BEGIN
		S.GET( block, tag );
		S.GET( S.VAL( Address, tag - {ArrayBit, MarkBit} ), recSize );
		IF ArrayBit IN tag THEN
			S.GET( block + AdrSize, lastElem );
			blockSize := lastElem + recSize - block
		ELSE
			blockSize := recSize + AdrSize
		END;
		INC( blockSize, (-blockSize) MOD BlockSize );
		RETURN blockSize
	END SizeOf;
	
	PROCEDURE SortCandidates;
	VAR i, j, h: LONGINT;  p: Address;
	BEGIN
		(* sort them in increasing order using shellsort *)
		h := 1;
		REPEAT  h := h*3 + 1  UNTIL h > nofcand;
		REPEAT
			h := h DIV 3;  i := h;
			WHILE i < nofcand DO
				p := candidates[i];  j := i;
				WHILE (j >= h) & Machine.GreaterThan(candidates[j - h], p) DO  
					candidates[j] := candidates[j - h];  j := j - h  
				END;
				candidates[j] := p;  INC( i )
			END
		UNTIL h = 1;
	END SortCandidates;

	PROCEDURE CheckCandidates;  
	VAR
		i: LONGINT; sb: Machine.MemoryBlock;
		p, tag1, tag2, block, endBlockAdr: Address;
		blkSize: Size;
	BEGIN
		IF nofcand = 0 THEN  RETURN  END;
		
		SortCandidates;

		(* sweep phase *)
		i := 0;  p := candidates[i];

		sb := Machine.memBlockHead;
		LOOP
			IF sb = NIL THEN  EXIT   END;

			block := sb.beginBlockAdr;  endBlockAdr := sb.endBlockAdr;
			blkSize := SizeOf( block );

			LOOP
				IF Machine.LessOrEqual( p, block + AdrSize ) THEN
					IF p = block + AdrSize THEN
						S.GET( block, tag1 );
						IF tag1 # p THEN  (* not a free block *) Mark( S.VAL( ANY, p ) )  END
					END;
					INC( i );
					IF i = nofcand THEN  EXIT   END;
					p := candidates[i]
				ELSIF p = block + AdrSize + 24 THEN  (* system block ? *)
					S.GET( block, tag1 );
					S.GET( p - AdrSize, tag2 );
					IF (tag2 = p - 24) & (tag2 = tag1)  THEN
						(* really a sysblock *)  Mark( S.VAL( ANY, p ) );
					END;
					INC( i );
					IF i = nofcand THEN  EXIT   END;
					p := candidates[i]
				ELSIF (blkSize > AdrSize + ProtOfs) & (p = block + AdrSize + ProtOfs)  THEN  (* prot. obj. ? *)
					S.GET( block, tag1 );
					IF tag1 = block + AdrSize THEN  Mark( S.VAL( ANY, p ) )  END;
					INC( i );
					IF i = nofcand THEN  EXIT   END;
					p := candidates[i]
				ELSE
					block := block + blkSize;
					IF Machine.GreaterOrEqual( block, endBlockAdr ) THEN  EXIT   END;
					blkSize := SizeOf( block );
				END;
			END;

			IF i = nofcand THEN  EXIT   END;
			sb := sb.next;
		END;
		nofcand := 0
	END CheckCandidates;


	PROCEDURE AddCandidate*( p: Address );
	VAR tag0Addr, tag0: Address;  tag: SET;
	BEGIN
		IF p MOD 32 = 0 THEN
			tag0Addr := p - AdrSize (* RecBlk, ArrBlk *)
		ELSIF p MOD 32 = 16 THEN
			tag0Addr := p - ProtOfs - AdrSize (* ProtObj *)
		ELSIF p MOD 16 = 8 THEN
			tag0Addr := p - 24 - AdrSize (* SysBlk *)
		ELSE  RETURN
		END;
		IF ValidAddress( tag0Addr ) THEN
			S.GET( tag0Addr, tag0 );
			IF ODD( tag0 ) THEN  RETURN  END;  (* already marked *)
			S.GET ( p - AdrSize, tag );
			IF ValidAddress( S.VAL( Address, tag - {ArrayBit, MarkBit} ) ) THEN
				candidates[nofcand] := p;  INC( nofcand );
				IF nofcand = LEN( candidates ) THEN  CheckCandidates  END
			END;
		END
	END AddCandidate;



	PROCEDURE CollectGarbage*( root: RootObject );
	VAR time1, time2 : HUGEINT; 
	BEGIN
		IF traceGC  THEN  Trace.String( "Heaps.Collect ... " );  Trace.Ln  END;
		IF Stats THEN
			Nmark := 0; Nmarked := 0;
			INC(Ngc);
			time1 := Machine.GetTimer ();
		END;
		collecting := TRUE;  markDepth := 0; noDeferred := 0;
		
		Mark( root );
		CheckCandidates;  CheckFinalizedObjects;
		Sweep;

		collecting := FALSE;  throuput := 0;
		IF traceGC  THEN  Trace.String( "Heaps.Collect done " );  Trace.Ln;  Trace.Ln  END;
		IF Stats THEN
			time2 := Machine.GetTimer ();
			NgcCyclesLastRun := time2 - time1;
			IF NgcCyclesLastRun > NgcCyclesMax THEN NgcCyclesMax := NgcCyclesLastRun; END;
			INC(NgcCyclesAllRuns, NgcCyclesLastRun);
			NgcCyclesMark := NgcCyclesLastRun
		END;
	END CollectGarbage;
	


	(* -------------------------- memory allocation ----------------------- *)



	PROCEDURE GetBlock( size: Size ): Address;   (* size MOD B = 0 *)
	VAR 
		i: LONGINT;  adr2: Address;
		block, prevBlock, newBlock: FreeBlk;  blkSize, restSize: Size;  blkAdr: Address;
	BEGIN
		IF (size < 0) OR (size > MaxHeapBlockSize)  THEN
			Machine.Release( Machine.Heaps );
			HALT( 99 )
		END;
		
		IF NgetBlock > 0 THEN 
			(* got here while "Heaps" was released for GC *)
			Machine.conWait( getBlockFinished, Machine.mtx[Machine.Heaps] )
		END;
		INC( NgetBlock );
		
		IF GCEnabled &  (throuput  > Machine.MemBlockSize) & (Machine.lock[Machine.GC] = 'N') THEN  
			Machine.InvokeGC;
			throuput := 0;
		END;

		REPEAT
			i := size DIV BlockSize;
			IF i > N THEN  i := N  END;

			LOOP
				block := S.VAL( FreeBlk, A[i] );  prevBlock := NIL;
				IF i = N  THEN
					LOOP
						IF block = NIL THEN
							IF GCEnabled & (throuput > 0) & (Machine.lock[Machine.GC] = 'N') THEN
								Machine.InvokeGC;
								throuput := 0;
							ELSE
								Machine.ExpandHeap( 0, size, S.VAL( Address, newBlock ), adr2 );
								IF newBlock # NIL  THEN
									newBlock.next := S.VAL( FreeBlk, A[N] );  
									A[N] := S.VAL( Address, newBlock );
									heapSize := GetHeapSize();
									heapAvailable := Available()
								ELSE
									Trace.Ln;  
									Trace.String( "Heapspace exhaustet" ); Trace.Ln;  
									Machine.Release( Machine.Heaps );
									HALT( 99 )
								END
							END;
							DEC( i );  (* try again *)
							EXIT
						END;
						
						IF block.size >= size - AdrSize THEN  (* found *) EXIT   END;
						prevBlock := block;
						block := block.next
					END  (* loop *)
				END;
				IF block # NIL THEN  EXIT   END;
				INC( i )
			END;  (* loop *)
		UNTIL block # NIL;

		blkSize := block.size + AdrSize;
		blkAdr := S.VAL( Address, block );
		
		(*	unlink found block	*)
		IF (i < N) OR (prevBlock = NIL) THEN  A[i] := S.VAL( Address, block.next )
		ELSE  prevBlock.next := block.next
		END;
		DEC( heapAvailable, blkSize );
		
		restSize := blkSize - size;
		IF restSize > 0 THEN  Recycle( blkAdr + size, restSize, FALSE )  END;
		
		INC( throuput, size );
		IF Stats THEN  INC(Nnew); INC(NnewBytes, size)  END;
		IF NgetBlock > 0 THEN 
			DEC( NgetBlock );  
			Machine.conSignal( getBlockFinished )
		END;
		RETURN blkAdr
	END GetBlock;

	PROCEDURE ClearMem*( a: Address; len: LONGINT );
	BEGIN
		Machine.Fill32( a, len, 0 )
	END ClearMem;


	(** Private compiler interface. Do not use. *)
	PROCEDURE NewRec*( VAR p: ANY;  tag: Address; isRealtime: BOOLEAN );   (* implementation of NEW( ptr ) *)
	VAR size, recSize: Size;  ptr: Address;  typeInfoAdr: Address;  flags: SET;
	BEGIN
		IF traceNEW  THEN  Trace.Char( 'r' ); Trace.Hex( tag, -8 )  END;
		S.GET( tag - AdrSize, typeInfoAdr );   
		S.GET( typeInfoAdr + FlagsOfs, flags );
		IF ProtTypeBit IN flags THEN  (* protected record *)
			NewProtRec( p, tag, isRealtime );  RETURN
		END;
		S.GET( tag, recSize );
		size := recSize + AdrSize;  INC( size, (-size) MOD BlockSize );
		Machine.Acquire( Machine.Heaps );
		ptr := GetBlock( size ) + AdrSize;
		S.PUT( ptr - AdrSize, tag );
		ClearMem( ptr, size - AdrSize );
		p := S.VAL( ANY, ptr );
		Machine.Release( Machine.Heaps )
	END NewRec;

	PROCEDURE NewProtRec*( VAR p: ANY;  tag: Address; isRealtime: BOOLEAN );
	VAR recSize, size: Size;  ptr: Address;
	BEGIN
		IF traceNEW  THEN  Trace.Char( 'p' )  END;
		S.GET( tag, recSize );
		(* add space for tag and header and round up to BlockSize *)
		size := recSize + ProtOfs + AdrSize;  INC( size, (-size) MOD BlockSize );
		Machine.Acquire( Machine.Heaps );
		ptr := GetBlock( size ) + AdrSize;
		S.PUT( ptr - AdrSize, ptr );   (* set the main tag *)
		S.PUT( ptr, size - AdrSize );   (* size *)
		S.PUT( ptr + AdrSize, S.VAL( Address, - AdrSize ) );
		ClearMem( ptr + 8, ProtOfs - 12 );   (* clear header *)
		S.PUT16( ptr + 10, -1 );   (* flag = -1 *)
		S.PUT( ptr + (ProtOfs - AdrSize), tag );   (* set the tag *)
		INC( ptr, ProtOfs );
		(* clear must be done inside lock to ensure all traced pointer fields are initialized to NIL *)
		ClearMem( ptr, size - (AdrSize + ProtOfs) );   (* clear everything except tag & header *)
		p := S.VAL( ANY, ptr );
		Machine.Release( Machine.Heaps );
	END NewProtRec;


	(** Private compiler interface. Do not use. *)
	PROCEDURE NewSys*( VAR p: ANY;  size: Size; isRealtime: BOOLEAN );   (* implementation of S.NEW(ptr, size) *)
	VAR ptr: Address;
	BEGIN
		IF traceNEW  THEN  Trace.String( '[s' ); Trace.Int( size, 1)  END;
		size := size + AdrSize + 24;  INC( size, (-size) MOD BlockSize );
		Machine.Acquire( Machine.Heaps );
		ptr := GetBlock( size ) + AdrSize;  ClearMem( ptr, size - AdrSize );
		S.PUT( ptr - AdrSize, ptr );  S.PUT( ptr, size - AdrSize );
		S.PUT( ptr + AdrSize, S.VAL( Address, -AdrSize ) );
		S.PUT( ptr + 20, ptr );
		p := S.VAL( ANY, ptr + 24 );
		IF traceNEW  THEN  Trace.Char( ']' )  END;
		Machine.Release( Machine.Heaps )
	END NewSys;

	(** Private compiler interface. Do not use. *)
	PROCEDURE NewArr*( VAR p: ANY;  eltag: Address;  nofelem, nofdim: Size; isRealtime: BOOLEAN );
	VAR size, elSize, arrSize, dataOffset, ptrOfs0: Size;  ptr, firstElem: Address;
	BEGIN
		S.GET( eltag, elSize );
		arrSize := nofelem*elSize;
		IF arrSize = 0 THEN
			NewSys( p, nofdim*4 + 3*AdrSize, isRealtime );
		ELSE
			dataOffset := 3*AdrSize + nofdim*AdrSize;
			INC( dataOffset, (-dataOffset) MOD ArrayAlignment );
			S.GET( eltag + AdrSize, ptrOfs0 );
			IF ptrOfs0 = -AdrSize THEN
				(* no pointers in element type *)
				NewSys( p, dataOffset + arrSize, isRealtime );
			ELSE
				size := dataOffset + arrSize + AdrSize; INC( size, (-size) MOD BlockSize );
				Machine.Acquire( Machine.Heaps );
				ptr := GetBlock( size ) + AdrSize;
				S.PUT( ptr - AdrSize, S.VAL( SET, eltag ) + {ArrayBit} );
				ClearMem( ptr, size - AdrSize );
				firstElem := ptr + dataOffset;
				S.PUT( ptr, firstElem + arrSize - elSize );  (* last elem *)
				(* ptr + 4 is reserved for mark phase *)
				S.PUT( ptr + 2*AdrSize, firstElem );
				p := S.VAL( ANY, ptr );
				Machine.Release( Machine.Heaps )
			END
		END;
	END NewArr;

	PROCEDURE FillStaticType* ( VAR staticTypeAddr: Address;
								   startAddr, typeInfoAdr: Address;
								   size, recSize: Size;
								   numPtrs, numSlots: LONGINT );
	VAR 
		p, offset: Address;  sTB {UNTRACED}: StaticTypeBlock;
	BEGIN
		Machine.Acquire( Machine.Heaps );
		
		Machine.Fill32( startAddr, size, 0 );	(* clear whole static type, size MOD AdrSize = 0 implicitly, see WriteType in PCOF.Mod *)
		S.PUT( startAddr, S.VAL( Address, -AdrSize ) );	(* sentinel *)

		(* methods and tags filled in later *)

		offset := AdrSize*(numSlots + 1 + 1);  (* #methods, max. no. of tags, method end marker (sentinel), pointer to type information*)
		p := startAddr + offset;
		S.PUT( p - AdrSize, typeInfoAdr ); 	(* pointer to typeInfo *)
		sTB := S.VAL( StaticTypeBlock, p );
		sTB.recSize := recSize;
		staticTypeAddr := p;
		
		(* create the pointer for the dynamic array of pointer offsets, the dynamic array of pointer offsets 
		    is stored in the static type descriptor, it has no header part *)
		INC( p, S.SIZEOF(StaticTypeDesc) );
		IF p MOD (2 * AdrSize) # 0 THEN  INC( p, AdrSize )  END;
		S.PUT( p + 3 * AdrSize, numPtrs ); (* internal structure of dynamic array without pointers: the first 3 fields are unused *)
		sTB.pointerOffsets := S.VAL( PointerOffsets, p ); (* the fourth field contains the dimension of the array *)

		(* ptrOfs filled in later *)

		Machine.Release( Machine.Heaps )
	END FillStaticType;



	(*------------------------------  misc  ----------------------------------------*)

	(** WriteType - Write a type name (for tracing only). *)
	PROCEDURE WriteType*( t: Address );		(* t is static type descriptor *)
	VAR m: Address; i: LONGINT;  ch: CHAR;  name: ARRAY 32 OF CHAR;
	BEGIN
		name := "";
		S.GET( t - AdrSize, t );
		S.GET( t + 4*AdrSize, m );
		IF m # 0 THEN
			i := 0;  S.GET( m + 4*AdrSize + i, ch );
			WHILE (ch >= '0') & (ch <= 'z') & (i < 32) DO
				Trace.Char( ch );
				INC( i );  S.GET( m + 4* AdrSize + i, ch )
			END
		ELSE  Trace.String( "NIL" )
		END;
		Trace.Char( '.' );
		S.MOVE( t + 5*AdrSize, S.ADR( name[0] ), 32 );
		IF name[0] = 0X THEN  Trace.String( "-" )  ELSE  Trace.String( name )  END;
	END WriteType;


	PROCEDURE ValidAddress*( p: Address ): BOOLEAN;
	VAR sb: Machine.MemoryBlock;
	BEGIN
		IF (p # 0 ) & (p MOD 4 = 0) THEN
			sb := Machine.memBlockHead;
			WHILE sb # NIL DO
				IF Machine.LessOrEqual( sb.beginBlockAdr, p ) & 
				    Machine.LessOrEqual( p, sb.endBlockAdr ) THEN  RETURN TRUE  END;
				sb := sb.next;
			END
		END;
		RETURN FALSE
	END ValidAddress;

	PROCEDURE ValidPointer( p: Address ): BOOLEAN;   (* check if p is a valid pointer into the Heap *)
	VAR tag: SET;  ok: BOOLEAN;
	BEGIN
		ok := FALSE;  tag := {};
		IF ValidAddress( p ) THEN
			IF p MOD 16 = 8 THEN  ok := TRUE (* subobject or sysblock *)
			ELSE
				S.GET( p - AdrSize, tag );
				ok := ValidAddress( S.VAL( Address, tag - {ArrayBit, MarkBit} ) )
			END
		END;
		IF ~ok THEN
			Trace.String( "illegal pointer value: " ); Trace.Hex( p, -8 );
			IF tag # {} THEN  
				Trace.String( " (bad tag: " );  Trace.Hex( S.VAL( Address, tag ), -8 );  Trace.Char( ')' )  
			END;
			Trace.Ln
		END;
		RETURN ok
	END ValidPointer;
	

	(* Returns the size in bytes of the remaining free heap *)
	PROCEDURE Available( ): Size;
	VAR i: LONGINT;  avail: Size;  block: FreeBlk;
	BEGIN
		avail := 0;  i := 0;
		WHILE i <= N DO
			block := S.VAL( FreeBlk, A[i] );
			WHILE block # NIL  DO
				INC( avail, block.size + AdrSize );  block := block.next
			END;
			INC( i )
		END;
		RETURN avail
	END Available;
	

	(** Returns the total heap size of the Oberon system. *)
	PROCEDURE HeapSize*( ): LONGINT;
	BEGIN
		RETURN heapSize;
	END HeapSize;
	
	
	PROCEDURE GetHeapInfo*( VAR total, free, largest: Size );
	VAR i: LONGINT;  block: FreeBlk;
	BEGIN
		free := 0;  largest := 0;  i := 0;
		Machine.Acquire( Machine.Heaps );
		total := heapSize;
		WHILE i <= N DO
			block := S.VAL( FreeBlk, A[i] );
			WHILE block # NIL DO
				INC( free, block.size + AdrSize );  block := block.next;
				IF block.size > largest THEN  largest := block.size  END;
			END;
			INC( i )
		END;
		Machine.Release( Machine.Heaps );
	END GetHeapInfo;

	PROCEDURE Used*( ): LONGINT;
	BEGIN
		RETURN heapSize - heapAvailable
	END Used;

	PROCEDURE GetHeapSize( ): Size;
	VAR heap: Size;  sb: Machine.MemoryBlock;
	BEGIN
		sb := Machine.memBlockHead;  heap := 0;
		WHILE sb # NIL DO  heap := heap + sb.size;  sb := sb.next  END;
		RETURN heap;
	END GetHeapSize;



	(*------------------ Initialization --------------------------------------------------*)

	PROCEDURE InitHeap;
	VAR i: LONGINT; adr1, adr2: Address;
		recSize, blkSize: Size;
		tag: SET;
		block, lastElem, a: Address;
	BEGIN
		block := Machine.memBlockHead.beginBlockAdr;
		S.GET( block, tag );
		WHILE tag # {} DO
			S.GET( S.VAL( Address, tag - {ArrayBit, MarkBit} ), recSize );
			IF ArrayBit IN tag THEN
				S.GET( block + AdrSize, lastElem );
				blkSize := lastElem + recSize - block
			ELSE
				blkSize := recSize + AdrSize
			END;
			INC( blkSize, (-blkSize) MOD BlockSize );

			INC( block, blkSize );
			S.GET( block, tag );
		END;
		S.PUT( block, block + AdrSize );
		S.PUT( block + AdrSize,  Machine.memBlockHead.endBlockAdr - block - AdrSize );
		S.PUT( block + AdrSize + SizeSize, S.VAL( Address, 0 ) );
		
		a := Machine.memBlockHead.endBlockAdr;
		S.PUT( a, a + AdrSize );
		S.PUT( a + AdrSize, S.VAL( Address, 0 ) );
		
		i := 0;
		WHILE i < N DO  A[i] := NilVal;  INC( i )  END;
		A[N] := block;
		
		Machine.ExpandHeap( 0, 2*Machine.MemBlockSize - 2*BlockSize, adr1, adr2 );
		IF adr1 # 0  THEN
			S.PUT( adr1 + AdrSize + SizeSize, A[N] );  A[N] := adr1;
			heapSize := GetHeapSize();
			heapAvailable := Available()
		END;
	END InitHeap;


	PROCEDURE Init;
	VAR s: ARRAY 8 OF CHAR;
	BEGIN
		IF Stats THEN
			Ngc := 0;
			Nmark := 0; Nmarked := 0; NfinalizeAlive := 0; NfinalizeDead := 0;
			NgcCyclesMark := 0; NgcCyclesLastRun := 0; NgcCyclesMax := 0; NgcCyclesAllRuns := 0;
		END;

		GC := EmptyProc;	(* no GC until EmptyProc gets replaced (in module Kernel) *)
		nofcand := 0; 

		debug := Glue.debug;
		GCEnabled :=  ~(6 IN debug);
		traceGC := 1 IN debug;
		traceNEW := 4 IN debug;

		InitHeap;
		NgetBlock := 0;
		getBlockFinished := Machine.conInit( 0 );
		
		Machine.GetConfig( "FastNEW", s );
		fastNEW := ( s[0] = "1" )
	END Init;


BEGIN
	Init;
END Heaps.