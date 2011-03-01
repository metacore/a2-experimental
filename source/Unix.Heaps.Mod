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
	TypeNameOfs = AdrSize * 5;		(* type name offset in TypeDesc *)
	ModNameOfs = AdrSize * 2;		(* module name offset in ModuleDesc *)
	
	
	NilVal* = 0;

	MaxHeapBlockSize = 512*1024*1024;

	MinPtrOfs = -40000000H;	(* sentinel offset for ptrOfs *)
	MethodEndMarker* = MinPtrOfs;   (* marks the end of the method addresses, used in Info.ModuleDetails *)

	ArrayAlignment = 8;

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
	N = 9;  
	ProtOfs* = BlockSize + 16;
	ProtTypeBit* = 31;   (** flags in TypeDesc, low bits reserved for extLevel *)

	MarkBit* = 0;  ArrayBit* = 1;  FreeBit* = 2;  SubObjBit* = 3;  ProtObjBit* = 4;
	FlagBits* = {MarkBit, ArrayBit, FreeBit, SubObjBit, ProtObjBit};

TYPE
	FreeBlk = POINTER TO RECORD
				tag: Address;  (* = S.ADR( size ) *)
				size: Size;
				next: Address;
			END;

	RootObject* = OBJECT 
		PROCEDURE FindRoots*;	(** abstract *)
		BEGIN HALT( 301 ) END FindRoots;
	END RootObject;


VAR
	A: ARRAY N + 1 OF  (*FreeBlk*) Address;
	candidates: ARRAY 1024 OF  Address;
	nofcand, marks: LONGINT;

	heapSize: Size;

	throuput:  Size;
	GCEnabled: BOOLEAN;
	GC*: PROCEDURE;
	collecting-: BOOLEAN;
	getBlockActive: BOOLEAN;

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
	VAR n, p, t: FinalizerNode;  codeEnd: Address;
	BEGIN
		codeEnd := codeAdr + codeLen;
		Machine.Acquire( Machine.Heaps );
		n := checkRoot;
		WHILE n # NIL DO  (* iterate over checked list *)
			t := n;  n := n.nextFin;
			IF Machine.LessOrEqual( codeAdr, S.VAL( Address, t.finalizer ) ) & 
			    Machine.LessOrEqual( S.VAL( Address, t.finalizer ), codeEnd ) THEN
				IF t = checkRoot THEN  checkRoot := t.nextFin  ELSE  p.nextFin := t.nextFin  END;
				IF Stats THEN DEC(NfinalizeAlive) END;
			ELSE  p := t
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
			ELSE  p := t
			END
		END;
		Machine.Release( Machine.Heaps );
	END CleanupModuleFinalizers;



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
			S.PUT( haddr, hval + {MarkBit} );   (* mark this block *)  INC( marks );
			IF ~sysblock THEN  
				IF ptr IS RootObject THEN  ptr(RootObject).FindRoots  END;	
				RETURN TRUE  
			END
		END;
		RETURN FALSE
	END UnmarkedObject;

	PROCEDURE InitMarkState( blk: Address; VAR curr, tag: Address; VAR arr: BOOLEAN );
	VAR stag: SET;
	BEGIN
		S.GET( blk - AdrSize, stag );
		arr := ArrayBit IN stag;
		tag := S.VAL( Address, stag - {ArrayBit, MarkBit} );
		IF arr THEN  S.GET( blk + 2*AdrSize, curr )  ELSE  curr := blk  END
	END InitMarkState;

	PROCEDURE RestoreMarkState( blk: Address; VAR curr, tag: Address; VAR arr: BOOLEAN );
	VAR stag: SET;
	BEGIN
		S.GET( blk - AdrSize, stag );
		arr := ArrayBit IN stag;
		tag := S.VAL( Address, stag - {ArrayBit, MarkBit} );
		IF arr THEN  S.GET( blk + AdrSize, curr )  ELSE  curr := blk  END
	END RestoreMarkState;

	PROCEDURE SaveMarkState( blk: Address; curr, tag: Address; arr: BOOLEAN );
	VAR stag: SET;
	BEGIN
		stag := S.VAL( SET, tag ) + {MarkBit};
		IF arr THEN  INCL( stag, ArrayBit )  END;
		S.PUT( blk - AdrSize, stag );
		IF arr THEN  S.PUT( blk + AdrSize, curr ) END
	END SaveMarkState;



	PROCEDURE Mark*( ptr: ANY );
	VAR 
		block: Address;
		field, father, tmp: Address; cur, lastElem: Address;
		offset, elsize: LONGINT;  tag: Address;  arr: BOOLEAN;  stag: SET;
	BEGIN
		IF Stats THEN INC(Nmark); END;
		IF UnmarkedObject( ptr ) THEN
			block := S.VAL( Address, ptr );
			InitMarkState( block, cur, tag, arr );
			father := 0;

			LOOP
				INC( tag, AdrSize );
				S.GET( tag, offset );   (* array: 0 or -8, record: ptr offset or -AdrSize(n+1) *)
				IF offset >= 0 THEN
					S.GET( cur + offset, field );
					IF UnmarkedObject( S.VAL( ANY, field ) ) THEN
						(* down *)
						SaveMarkState( block, cur, tag, arr );
						S.PUT( cur + offset, father );
						father := block;
						block := field;
						InitMarkState( block, cur, tag, arr );
					END
				ELSE  (* offset < 0 *)
					INC( tag, offset );	(* back to starting point *)
					S.GET( block, lastElem );
					IF arr & (cur < lastElem) THEN
						S.GET( tag, elsize );
						INC( cur, elsize );
					ELSE
						(* up *)
						stag := S.VAL( SET, tag ) + {MarkBit};
						IF arr THEN  INCL( stag, ArrayBit )  END;
						IF ProtObjBit IN S.VAL( SET, block )  THEN  EXCL( stag, MarkBit )  END;
						S.PUT( block - AdrSize, stag );

						IF father = 0 THEN  EXIT  END;

						RestoreMarkState( father, cur, tag, arr );
						S.GET( tag, offset );
						S.GET( cur + offset, tmp );
						S.PUT( cur + offset, block );
						block := father;
						father := tmp;
					END
				END
			END  (* loop *)

		END
	END Mark;



	PROCEDURE Sweep;
	VAR
		block, endBlock, lastElem: Address;  tag: SET;  recSize: Size;
		lastp: FreeBlk;  size, lastsize: Size;
		lastA: ARRAY N + 1 OF Address;
		sb, nextSuper: Machine.MemoryBlock;
		i: LONGINT;
	BEGIN
		IF traceGC  THEN  Trace.String( "Sweep" );  Trace.Ln  END;
		i := 0;
		WHILE i <= N DO  A[i] := NilVal;  lastA[i] := S.ADR( A[i] );  INC( i )  END;

		sb := Machine.memBlockHead;
		WHILE sb # NIL DO
			block := sb.beginBlockAdr;  endBlock := sb.endBlockAdr;
			nextSuper := sb.next;

			lastsize := 0;
			WHILE block # endBlock DO
				S.GET( block, tag );
				S.GET( S.VAL( Address,  tag - {ArrayBit, MarkBit} ), recSize );
				IF ArrayBit IN tag  THEN  (* array block *)
					S.GET( block + AdrSize, lastElem );
					size := lastElem + recSize - block
				ELSE
					size := recSize + AdrSize
				END;
				INC( size, (-size) MOD BlockSize );

				IF ~(MarkBit IN tag) THEN
					(* collect *)
					IF lastsize = 0 THEN  lastp := S.VAL( FreeBlk, block )  END;
					S.PUT( block, S.VAL( Address, 0 ) );  (* remove type tag *)
					INC( lastsize, size );
				ELSE
					S.PUT( block, tag - {MarkBit} );	(* remove mark bit *)
					IF lastsize > 0 THEN
						lastp.size := lastsize - AdrSize;  lastp.tag := S.ADR( lastp.size );
						i := lastsize DIV BlockSize;
						IF i > N THEN  i := N  END;
						lastp.next := NilVal;  S.PUT( lastA[i], lastp );  lastA[i] := S.ADR( lastp.next );
						lastsize := 0
					END
				END;
				INC( block, size );
			END;

			(* last collected block: *)
			IF (lastsize = sb.endBlockAdr - sb.beginBlockAdr)  THEN
				(* whole block is free, unlink it*)
				Machine.FreeMemBlock( S.VAL( Machine.MemoryBlock, sb ) );
				heapSize := GetHeapSize();
			ELSIF lastsize > 0 THEN
				(* last collected block: *)
				lastp.size := lastsize - AdrSize;  lastp.tag := S.ADR( lastp.size );
				i := lastsize DIV BlockSize;
				IF i > N THEN  i := N  END;
				lastp.next := NilVal;  S.PUT( lastA[i], lastp );  lastA[i] := S.ADR( lastp.next )
			END;
			sb := nextSuper;
		END
	END Sweep;


	PROCEDURE CheckCandidates;  
	VAR
		i, j, h: LONGINT; tag: SET;  sb: Machine.MemoryBlock;
		p, tag1, tag2, block, lastElem, sbEnd: Address;
		recSize, blockSize: Size;
	BEGIN
		IF nofcand = 0 THEN  RETURN  END;
		(* first sort them in increasing order using shellsort *)
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

		(* sweep phase *)
		i := 0;  p := candidates[i];

		sb := Machine.memBlockHead;
		LOOP
			IF sb = NIL THEN  EXIT   END;

			block := sb.beginBlockAdr;  sbEnd := sb.endBlockAdr;

			LOOP
				IF Machine.LessOrEqual( p, block + AdrSize ) THEN
					IF p = block + AdrSize THEN
						S.GET( block, tag1 );
						IF tag1 # p THEN  Mark( S.VAL( ANY, p ) )  END
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
				ELSIF p = block + AdrSize + ProtOfs  THEN  (* prot. obj. ? *)
					S.GET( block, tag1 );
					IF tag1 = block + AdrSize THEN  Mark( S.VAL( ANY, p ) )  END;
					INC( i );
					IF i = nofcand THEN  EXIT   END;
					p := candidates[i]
				ELSE
					(* next block calc *)
					S.GET( block, tag );
					S.GET( S.VAL( Address, tag - {ArrayBit, MarkBit} ), recSize );
					IF ArrayBit IN tag THEN
						S.GET( block + AdrSize, lastElem );
						blockSize := lastElem + recSize - block
					ELSE
						blockSize := recSize + AdrSize
					END;
					INC( blockSize, (-blockSize) MOD BlockSize );
					INC( block, blockSize );
					(* end of next block calc *)

					IF Machine.GreaterOrEqual( block, sbEnd ) THEN  EXIT   END;
				END
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



	PROCEDURE Collect*( root: RootObject );
	VAR time1, time2 : HUGEINT; 
	BEGIN
		IF traceGC  THEN  Trace.String( "Heaps.Collect ... " );  Trace.Ln  END;
		IF Stats THEN
			Nmark := 0; Nmarked := 0;
			INC(Ngc);
			time1 := Machine.GetTimer ();
		END;
		collecting := TRUE;
		
		Mark( root );
		CheckCandidates;  CheckFinalizedObjects;
		Sweep;

		marks := 0;
		collecting := FALSE;  throuput := 0;

		IF traceGC  THEN  Trace.String( "Heaps.Collect done " );  Trace.Ln;  Trace.Ln  END;
		IF Stats THEN
			time2 := Machine.GetTimer ();
			NgcCyclesLastRun := time2 - time1;
			IF NgcCyclesLastRun > NgcCyclesMax THEN NgcCyclesMax := NgcCyclesLastRun; END;
			INC(NgcCyclesAllRuns, NgcCyclesLastRun);
			NgcCyclesMark := NgcCyclesLastRun
		END;
		throuput := 0;
	END Collect;



	(* -------------------------- memory allocation ----------------------- *)


	PROCEDURE AwaitGetBlockFinish;
	BEGIN
		REPEAT
			Machine.Release( Machine.Heaps );
			Machine.thrSleep( 1 );
			Machine.Acquire( Machine.Heaps )
		UNTIL ~getBlockActive
	END AwaitGetBlockFinish;
	
	PROCEDURE GetBlock( size: Size ): Address;   (* size MOD B = 0 *)
	VAR i: LONGINT;  restSize, fbsize: Size;  adr1, adr2, ptr, restPtr: Address;
		freeSize: Size;
	BEGIN
		IF (size < 0) OR (size > MaxHeapBlockSize)  THEN
			Machine.Release( Machine.Heaps );
			HALT( 99 )
		END;
		
		IF getBlockActive THEN  AwaitGetBlockFinish  END;
		getBlockActive := TRUE;

		IF GCEnabled &  (throuput  > 64*1024*1024) THEN
			Machine.Release( Machine.Heaps );
			GC;
			Machine.Acquire( Machine.Heaps )
		 END;


		REPEAT
			i := size DIV BlockSize;
			IF i > N THEN  i := N  END;

			LOOP
				ptr := A[i];
				IF i = N  THEN
					LOOP
						IF ptr = NilVal THEN
							IF GCEnabled & (throuput > 0) THEN
								Machine.Release( Machine.Heaps );
								GC;
								Machine.Acquire( Machine.Heaps )
							ELSE
								Machine.ExpandHeap( 0, size, adr1, adr2 );
								IF adr1 # 0  THEN
									S.PUT( adr1 + 2*AdrSize, A[N] );  A[N] := adr1;
									heapSize := GetHeapSize()
								ELSE
									Trace.Ln;  
									Trace.String( "Heapspace exhaustet" ); Trace.Ln;  
									HALT( 99 )
								END
							END;
							EXIT
						END;
						S.GET( ptr + AdrSize, fbsize );
						IF fbsize + AdrSize >= size THEN  EXIT   END;
						S.GET( ptr + AdrSize + SizeSize, ptr )
					END  (* loop *)

				END;
				IF (ptr # NilVal) OR (i = N)  THEN  EXIT   END;
				INC( i )
			END;  (* loop *)
		UNTIL ptr # NilVal;

		S.GET( ptr + AdrSize, fbsize );
		S.GET( ptr + AdrSize + 4, A[i] );
		restSize := fbsize + AdrSize - size;
		IF restSize > 0 THEN  (* >= B >= 16 *)
			i := restSize DIV BlockSize;
			IF i > N THEN  i := N  END;
			restPtr := ptr + size;
			S.PUT( restPtr, restPtr + AdrSize );			(* tag *)
			S.PUT( restPtr + AdrSize, restSize - AdrSize );	(* size *)
			S.PUT( restPtr + AdrSize + SizeSize, A[i] );		(* next free block *)
			A[i] := restPtr
		END;
		INC( throuput, size );
		IF Stats THEN INC(Nnew); INC(NnewBytes, size) END;
		getBlockActive := FALSE;
		RETURN ptr
	END GetBlock;

	PROCEDURE ClearMem*( a: Address; len: LONGINT );
	BEGIN
		Machine.Fill32( a, len, 0 )
	END ClearMem;


	(** Private compiler interface. Do not use. *)
	PROCEDURE NewRec*( VAR p: ANY;  tag: Address; isRealtime: BOOLEAN );   (* implementation of NEW( ptr ) *)
	VAR size, recSize: Size;  ptr: Address;  typeInfoAdr: Address;  flags: SET;
	BEGIN
		IF traceNEW  THEN  Trace.Char( 'r' )  END;
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

	PROCEDURE FillStaticType* ( VAR p: Address;
								   startAddr, typeInfoAdr: Address;
								   size, recSize: Size;
								   numPtrs, numSlots: LONGINT );
	VAR staticTypeAdr, offset: Address;
	BEGIN
		Machine.Acquire( Machine.Heaps );
		Machine.Fill32( startAddr, size, 0 );	(* clear whole static type, size MOD AdrSize = 0 implicitly, see WriteType in PCOF.Mod *)
		S.PUT( startAddr, S.VAL( Address, -AdrSize ) );	(* sentinel *)

		(* methods and tags filled in later *)

		offset := AdrSize*(numSlots + 1 + 1);  (* #methods, max. no. of tags, method end marker (sentinel), pointer to type information*)
		staticTypeAdr := startAddr + offset;
		S.PUT( staticTypeAdr - AdrSize, typeInfoAdr ); 	(* pointer to typeInfo *)
		S.PUT( staticTypeAdr, recSize );					(* recSize *)


		(* ptrOfs filled in later *)

		S.PUT( staticTypeAdr + (numPtrs + 1)*AdrSize,  -(numPtrs + 1)*AdrSize );	(* sentinel *)
		p := staticTypeAdr;
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
	VAR i: LONGINT;  avail: Size;  ptr: FreeBlk;
	BEGIN
		avail := 0;  i := 0;
		WHILE i <= N DO
			ptr := S.VAL( FreeBlk, A[i] );
			WHILE ptr # NIL  DO
				INC( avail, ptr.size );  ptr := S.VAL( FreeBlk, ptr.next )
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
	VAR i: LONGINT;  ptr: FreeBlk;
	BEGIN
		free := 0;  largest := 0;  i := 0;
		Machine.Acquire( Machine.Heaps );
		total := heapSize;
		WHILE i <= N DO
			ptr := S.VAL( FreeBlk, A[i] );
			WHILE ptr # NIL DO
				INC( free, ptr.size );  ptr := S.VAL( FreeBlk, ptr.next );
				IF ptr.size > largest THEN  largest := ptr.size  END;
			END;
			INC( i )
		END;
		Machine.Release( Machine.Heaps );
	END GetHeapInfo;



	PROCEDURE GetHeapSize( ): Size;
	VAR heap: Size;  sb: Machine.MemoryBlock;
	BEGIN
		sb := Machine.memBlockHead;  heap := 0;
		WHILE sb # NIL DO  heap := heap + sb.size;  sb := sb.next  END;
		RETURN heap;
	END GetHeapSize;

	PROCEDURE Used*( ): LONGINT;
	BEGIN
		RETURN heapSize - Available()
	END Used;

	(** Returns the size in bytes of the largest free available memory block. Allocating objects with a size
		  greater than this size will cause the memory allocation to fail. *)
	PROCEDURE LargestAvailable*( ): LONGINT;
	BEGIN
		RETURN MAX( LONGINT );
	END LargestAvailable;



	(*------------------ Initialization --------------------------------------------------*)

	PROCEDURE InitHeap;
	VAR i: LONGINT; adr1, adr2: Address;
		recSize, size: Size;
		tag: SET;
		block, lastElem: Address;
	BEGIN
		block := Machine.memBlockHead.beginBlockAdr;
		S.GET( block, tag );
		WHILE tag # {} DO
			S.GET( S.VAL( Address, tag - {ArrayBit, MarkBit} ), recSize );
			IF ArrayBit IN tag THEN
				S.GET( block + AdrSize, lastElem );
				size := lastElem + recSize - block
			ELSE
				size := recSize + AdrSize
			END;
			INC( size, (-size) MOD BlockSize );

			INC( block, size );
			S.GET( block, tag );
		END;

		S.PUT( block, block + AdrSize );
		S.PUT( block + AdrSize,  Machine.memBlockHead.endBlockAdr - block - AdrSize );
		S.PUT( block + 2*AdrSize, 0 );

		i := 0;
		WHILE i < N DO  A[i] := NilVal;  INC( i )  END;
		A[N] := block;
		Machine.ExpandHeap( 0, 128*1024*1024, adr1, adr2 );
		IF adr1 # 0  THEN
			S.PUT( adr1 + 2*AdrSize, A[N] );  A[N] := adr1;
			heapSize := GetHeapSize();
		END;
	END InitHeap;


	PROCEDURE Init;
	BEGIN
		IF Stats THEN
			Ngc := 0;
			Nmark := 0; Nmarked := 0; NfinalizeAlive := 0; NfinalizeDead := 0;
			NgcCyclesMark := 0; NgcCyclesLastRun := 0; NgcCyclesMax := 0; NgcCyclesAllRuns := 0;
		END;

		GC := EmptyProc;	(* no GC until EmptyProc gets replaced (in module Kernel) *)
		nofcand := 0; marks := 0;

		debug := Glue.debug;
		GCEnabled :=  ~(6 IN debug);
		traceGC := 1 IN debug;
		traceNEW := 4 IN debug;

		InitHeap;
	END Init;


BEGIN
	Init;
END Heaps.