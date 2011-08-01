MODULE SortDemo;	(** AUTHOR "g.f."; PURPOSE sort demo *)

(* this is an A2-port of the SortDemo done by W.Weck in 1993 for Oberon V4 *)

IMPORT
	Raster, Random, Objects, WMRectangles, Strings,
	WM := WMWindowManager, WMComponents, WMStandardComponents,
	Out := KernelLog, Clock, Kernel;
	
CONST
	N = 100;  ElemSize = 4;

	
TYPE
	SDW* =  OBJECT (WM.BufferWindow)
	CONST
		WindowWidth = N*ElemSize;  WindowHeight = N*ElemSize;
		MaxY = WindowHeight - 1;
	VAR
		white, grey, red, yellow: Raster.Pixel;
		data: ARRAY N OF LONGINT;
		random: Random.Generator;
		t: Kernel.Timer;
		
		nofcomps, nofswaps: LONGINT; running:BOOLEAN;
		
		
		PROCEDURE &New*;
		VAR d, t: LONGINT;
		BEGIN
			Init( WindowWidth, WindowHeight, FALSE );
			manager := WM.GetDefaultManager();
			manager.Add( 300, 300, SELF, {WM.FlagFrame, WM.FlagClose, WM.FlagNoResizing} );
			SetTitle( Strings.NewString( "SortArray" ) );
			Raster.SetRGB( white, 255, 255, 255 );
			Raster.SetRGB( red, 255, 0, 0 );
			Raster.SetRGB( yellow, 255, 255, 0 );
			Raster.SetRGB( grey, 127, 127, 127 );
			
			NEW( random );  Clock.Get( t, d );  random.InitSeed( t );
			
			Order;
			running := FALSE
		END New;
		
		PROCEDURE Start;
		BEGIN
			nofcomps := 0;  nofswaps := 0;  running := TRUE
		END Start;
		
		PROCEDURE Finish( CONST name: ARRAY OF CHAR );
		BEGIN
			Out.String( name ); Out.String( ": " ); 
			Out.Int( nofcomps, 1 ); Out.String( " compares, " );
			Out.Int( nofswaps, 1 ); Out.String( " swaps, " );
			Out.Ln;
			running := FALSE
		END Finish;
		
		PROCEDURE DrawElement( n: LONGINT );
		VAR mode: Raster.Mode;
			x, y, len: LONGINT;
		BEGIN
			len := data[n];
			x := ElemSize*n;  y := MaxY - (ElemSize*len);
			Raster.InitMode( mode, Raster.srcCopy );
			IF len < N THEN  Raster.Fill( img, x, 0, x+ElemSize, y, white, mode )  END;
			Raster.Fill( img, x, y+1, x+ElemSize, y+ElemSize+1, red, mode );
			IF len > 1 THEN  Raster.Fill( img, x, y+ElemSize+1, x+ElemSize, MaxY, grey, mode )  END;
		END DrawElement;
		
		
		PROCEDURE Highlight( n: LONGINT );
		VAR mode: Raster.Mode;
			x, y, len: LONGINT;
		BEGIN
			len := data[n];
			x := ElemSize*n;  y := MaxY - (ElemSize*len);
			Raster.InitMode( mode, Raster.srcCopy );
			IF len > 1 THEN  Raster.Fill( img, x, y+ElemSize+1, x+ElemSize, MaxY, yellow, mode )  END;
		END Highlight;
		
		PROCEDURE Clear( n: LONGINT );
		VAR mode: Raster.Mode;
			x, y, len: LONGINT;
		BEGIN
			len := data[n];
			x := ElemSize*n;  y := MaxY - (ElemSize*len);
			Raster.InitMode( mode, Raster.srcCopy );
			IF len > 1 THEN  Raster.Fill( img, x, y+ElemSize+1, x+ElemSize, MaxY, grey, mode )  END;
		END Clear;
		
		
		PROCEDURE Update;
		BEGIN
			Invalidate( WMRectangles.MakeRect( 0, 0, GetWidth(), GetHeight() ) );
		END Update;
		
		PROCEDURE Randomize( n: LONGINT );
		VAR i, j, k: LONGINT;
		BEGIN
			FOR i := 1 TO n DO
				j := random.Dice( N );  k := random.Dice( N );
				Swap( j, k );
				IF i MOD 16 = 0 THEN  NEW(t); t.Sleep(10) (*! Unix: Objects.Sleep( 10 ) *) END;
			END
		END Randomize;
		
		
		PROCEDURE Order;
		VAR i: LONGINT;
		BEGIN
			FOR i := 0 TO N-1 DO  data[i] := i + 1;  DrawElement( i )  END;
			Update
		END Order;
		
		PROCEDURE RevOrder;
		VAR i: LONGINT;
		BEGIN
			FOR i := 0 TO N-1 DO  data[i] := N - i;  DrawElement( i )  END;
			Update
		END RevOrder;
		
		PROCEDURE BadOrder;
		VAR i, m: LONGINT;
		BEGIN
			m := (N - 1) DIV 2;
			FOR i := 0 TO m-1 DO  data[i] := i + 1  END;
			data[m] := N;
			FOR i := m+1 TO N-1 DO  data[i] := i   END;
			
			FOR i := 0 TO N-1 DO  DrawElement( i )  END;
			Update
		END BadOrder;
		
		
		PROCEDURE Swap( i, j: LONGINT );
		VAR t: LONGINT;
		BEGIN
			t := data[i];  data[i] := data[j];  data[j] := t;
			DrawElement( i );
			DrawElement( j );
			Update;
			INC( nofswaps )
		END Swap;
		
		PROCEDURE Less( i, j: LONGINT ): BOOLEAN;
		BEGIN
			Highlight( i );  Highlight( j );  Update;  NEW(t); t.Sleep(10); (*! Unix: Objects.Sleep( 10 ); *)
			Clear( i ); Clear( j );  Update;
			INC( nofcomps );
			RETURN data[i] < data[j];
		END Less;
		
		
		PROCEDURE BubbleSort;
		VAR i, n, swaps: LONGINT; 
		BEGIN
			n := N - 2;
			REPEAT
				swaps := 0;  
				FOR i := 0 TO n DO
					IF Less( i + 1, i )  THEN  Swap( i, i + 1 );  INC( swaps )  END
				END;
				DEC( n )
			UNTIL swaps = 0;
		END BubbleSort;
		
		
		
		PROCEDURE SelectSort;
		VAR i, j, min: LONGINT;
		BEGIN
			FOR i := 0 TO N-1 DO
				min := i;  j := i + 1;
				FOR j := i+1 TO N-1 DO
					IF Less( j, min ) THEN  min := j  END
				END;
				IF i # min THEN  Swap( i, min )  END
			END
		END SelectSort;
		
		
		
		PROCEDURE ShellSort;
		VAR i, j, h: LONGINT;
		BEGIN
			i := 4;  h := 1;
			WHILE i < N DO  i := i*2;  h := h*2 + 1  END;
			WHILE h # 0 DO
				i := h;
				WHILE i < N DO
					j := i - h;
					WHILE (j >= 0) & Less( j + h, j ) DO  Swap( j, j + h );  j := j - h  END;
					INC( i )
				END;
				h := (h - 1) DIV 2
			END;
		END ShellSort;
		
		
		
		PROCEDURE QuickSort;
		
			PROCEDURE Sort( lo, hi: LONGINT );
			VAR i, j, m: LONGINT;
			BEGIN
				IF lo < hi THEN
					i := lo;  j := hi;  m := (lo + hi) DIV 2;
					REPEAT
						WHILE Less( i, m ) DO  INC( i )  END;
						WHILE Less( m, j ) DO  DEC( j )  END;
						IF i <= j THEN
							IF m = i THEN  m := j
							ELSIF m = j THEN  m := i
							END;
							Swap( i, j );  INC( i );  DEC( j )
						END
					UNTIL i > j;
					Sort( lo, j );  Sort( i, hi )
				END
			END Sort;
		
		BEGIN
			Sort( 0, N-1 );
		END QuickSort;
		
		
		
		PROCEDURE HeapSort;
		VAR l, r: LONGINT;
		
			PROCEDURE Sift( l, r: LONGINT );
			VAR i, j: LONGINT;
			BEGIN
				i := l;  j := 2*l + 1;
				IF (j + 1 < r) & Less( j, j + 1 ) THEN  INC( j )  END;
				WHILE (j < r) & ~Less( j, i ) DO
					Swap( i, j );
					i := j;  j := 2*j + 1;
					IF (j + 1 < r) & Less( j, j + 1 ) THEN  INC( j )  END
				END
			END Sift;
			
		BEGIN
			r := N;  l := N DIV 2;
			WHILE l > 0 DO  DEC( l );  Sift( l, r )  END;
			WHILE r > 0 DO  DEC( r );  Swap( 0, r );  Sift( 0, r )  END;
		END HeapSort;
		
		
		
		PROCEDURE SmoothSort;  	(* W.Weck 21 Jan 93, SmoothSort due to E.W.Dijkstra, J.Gutknecht *)
		VAR q, r, p, b, c: LONGINT;  

			PROCEDURE up( VAR b, c: LONGINT );  
			VAR b1: LONGINT;  
			BEGIN  b1 := b;  b := b + c + 1;  c := b1 
			END up;  

			PROCEDURE down( VAR b, c: LONGINT );  
			VAR c1: LONGINT;  
			BEGIN  c1 := c;  c := b - c - 1;  b := c1 
			END down;  

			PROCEDURE sift( r, b, c: LONGINT );  
			VAR r1: LONGINT;  
			BEGIN 
				WHILE b >= 3 DO  r1 := r - b + c;  
					IF Less( r1, r - 1 ) THEN  r1 := r - 1;  down( b, c )  END;  
					IF Less( r, r1 ) THEN  Swap( r, r1 );  r := r1;  down( b, c )  ELSE  b := 1  END  
				END  
			END sift;  

			PROCEDURE trinkle( r, p, b, c: LONGINT );  
			VAR r1, r2: LONGINT;  
			BEGIN 
				WHILE p > 0 DO  
					WHILE ~ODD( p ) DO  p := p DIV 2;  up( b, c )  END;  
					r2 := r - b;  
					IF (p = 1) OR ~Less( r, r2 ) THEN  p := 0  
					ELSE  p := p - 1;  
						IF b = 1 THEN  Swap( r, r2 );  r := r2  
						ELSE  r1 := r - b + c;  
							IF Less( r1, r - 1 ) THEN  r1 := r - 1;  down( b, c );  p := p*2  END;  
							IF ~Less( r2, r1 ) THEN  Swap( r, r2 );  r := r2  ELSE  Swap( r, r1 );  r := r1;  down( b, c );  p := 0  END  
						END  
					END  
				END;  
				sift( r, b, c ) 
			END trinkle;  

			PROCEDURE semiTrinkle( r, p, b, c: LONGINT );  
			VAR r1: LONGINT;  
			BEGIN  r1 := r - c;  
				IF Less( r, r1 ) THEN  Swap( r, r1 );  trinkle( r1, p, b, c )  END  
			END semiTrinkle;  

		BEGIN 
			q := 1;  r := 0;  p := 1;  b := 1;  c := 1;  
			WHILE q # N DO  
				IF p MOD 8 = 3 (* p = ... 011 *) THEN  
					sift( r, b, c );  p := (p + 1) DIV 4;  up( b, c );  up( b, c ) (* b >= 3 *)
				ELSE  (* p = ... 01 *)
					IF (q + c) < N THEN  sift( r, b, c )  ELSE  trinkle( r, p, b, c )  END;  
					down( b, c );  p := p*2;  
					WHILE b # 1 DO  down( b, c );  p := p*2  END;  
					p := p + 1 
				END;  
				q := q + 1;  r := r + 1 
			END;  
			trinkle( r, p, b, c );  
			WHILE q # 1 DO  q := q - 1;  p := p - 1;  
				IF b = 1 THEN  r := r - 1;  
					WHILE ~ODD( p ) DO  p := p DIV 2;  up( b, c )  END  
				ELSE  (* b >= 3 *)  r := r - b + c;  
					IF p > 0 THEN  semiTrinkle( r, p, b, c )  END;  
					down( b, c );  p := p*2 + 1;  r := r + c;  semiTrinkle( r, p, b, c );  down( b, c );  p := p*2 + 1 
				END  
			END;  
		END SmoothSort;  
		
		
	END SDW;
	
	
	
	Window = OBJECT( WMComponents.FormWindow )
		VAR
			toolbar: WMStandardComponents.Panel;
			button : WMStandardComponents.Button;

			sdw: SDW;

			PROCEDURE &New;
			VAR vc: WMComponents.VisualComponent;
			BEGIN
				vc := CreateForm();
				Init( vc.bounds.GetWidth(), vc.bounds.GetHeight(), FALSE );
				SetContent( vc );
				SetTitle( WM.NewString( "Sort Demo" ) );
				WM.DefaultAddWindow( SELF );
				NEW( sdw )
			END New;


			PROCEDURE CreateForm( ): WMComponents.VisualComponent;
			VAR
				panel: WMStandardComponents.Panel;
				label : WMStandardComponents.Label;
			BEGIN
				NEW( panel );
					panel.bounds.SetWidth( 560 );
					panel.bounds.SetHeight( 40 );
					panel.fillColor.Set( SHORT( 0FFFFFFFFH ) );
				
				
				NEW( toolbar );
					toolbar.bounds.SetHeight( 20 );
					toolbar.alignment.Set( WMComponents.AlignTop );
					toolbar.fillColor.Set( SHORT( 0CCCCCCFFH ) );

				NEW( label );
					label.bounds.SetWidth( 80 );
					label.alignment.Set( WMComponents.AlignLeft );
					label.caption.SetAOC( " Array init: " );
					label.textColor.Set( 0000000FFH );
				toolbar.AddContent(label);


				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " order " );
					button.onClick.Add( Order );
				toolbar.AddContent( button );
				
				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " rev. order " );
					button.onClick.Add( RevOrder );
				toolbar.AddContent( button );
				
				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " bad order " );
					button.onClick.Add( BadOrder );
				toolbar.AddContent( button );

				
				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " rand 10 " );
					button.onClick.Add( Rand10 );
				toolbar.AddContent( button );
				
				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " rand 100 " );
					button.onClick.Add( Rand100 );
				toolbar.AddContent( button );
				
				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " rand 500 " );
					button.onClick.Add( Rand500 );
				toolbar.AddContent( button );
				
				panel.AddContent( toolbar );	

				NEW( toolbar );
					toolbar.bounds.SetHeight( 20 );
					toolbar.alignment.Set( WMComponents.AlignTop );
					toolbar.fillColor.Set( SHORT( 0CCCCCCFFH ) );

				NEW( label );
					label.bounds.SetWidth( 80 );
					label.alignment.Set( WMComponents.AlignLeft );
					label.caption.SetAOC( " Sorter: " );
					label.textColor.Set( 0000000FFH );
				toolbar.AddContent(label);


				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " Bubble " );
					button.onClick.Add( StartBubbleSort );
				toolbar.AddContent( button );
				
				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " Select " );
					button.onClick.Add( StartSelectSort );
				toolbar.AddContent( button );
				
				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " Shell " );
					button.onClick.Add( StartShellSort );
				toolbar.AddContent( button );

				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " Quick " );
					button.onClick.Add( StartQuickSort );
				toolbar.AddContent( button );
				
				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " Heap " );
					button.onClick.Add( StartHeapSort );
				toolbar.AddContent( button );
				
				NEW( button );
					button.bounds.SetWidth( 80 );
					button.alignment.Set( WMComponents.AlignLeft );
					button.caption.SetAOC( " Smooth " );
					button.onClick.Add( StartSmoothSort );
				toolbar.AddContent( button );
				
				panel.AddContent( toolbar );

				RETURN panel
			END CreateForm;
			
			PROCEDURE Order( sender, data: ANY );
			BEGIN
				sdw.Order
			END Order;
			
			PROCEDURE RevOrder( sender, data: ANY );
			BEGIN
				sdw.RevOrder
			END RevOrder;
			
			PROCEDURE BadOrder( sender, data: ANY );
			BEGIN
				sdw.BadOrder
			END BadOrder;
			
			
			PROCEDURE Rand10( sender, data: ANY );
			BEGIN
				sdw.Randomize( 10 )
			END Rand10;
			
			PROCEDURE Rand100( sender, data: ANY );
			BEGIN
				sdw.Randomize( 100 )
			END Rand100;
			
			PROCEDURE Rand500( sender, data: ANY );
			BEGIN
				sdw.Randomize( 500 )
			END Rand500;
			
			PROCEDURE StartBubbleSort( sender, data: ANY );
			BEGIN
				IF ~ sdw.running THEN
					sdw.Start;
					sdw.BubbleSort;
					sdw.Finish( "BubbleSort" )
				END
			END StartBubbleSort;
				
			
			PROCEDURE StartSelectSort( sender, data: ANY );
			BEGIN
				IF ~ sdw.running THEN
					sdw.Start;
					sdw.SelectSort;
					sdw.Finish( "SelectSort" )
				END
			END StartSelectSort;
				
			
			PROCEDURE StartShellSort( sender, data: ANY );
			BEGIN
				IF ~ sdw.running THEN
					sdw.Start;
					sdw.ShellSort;
					sdw.Finish( "ShellSort" )
				END
			END StartShellSort;
				
					
			PROCEDURE StartQuickSort( sender, data: ANY );
			BEGIN
				IF ~ sdw.running THEN
					sdw.Start;
					sdw.QuickSort;
					sdw.Finish( "QuickSort" )
				END
			END StartQuickSort;
			
			
			PROCEDURE StartHeapSort( sender, data: ANY );
			BEGIN
				IF ~ sdw.running THEN
					sdw.Start;
					sdw.HeapSort;
					sdw.Finish( "HeapSort" )
				END
			END StartHeapSort;
				
			
			PROCEDURE StartSmoothSort( sender, data: ANY );
			BEGIN
				IF ~ sdw.running THEN
					sdw.Start;
					sdw.SmoothSort;
					sdw.Finish( "SmoothSort" )
				END
			END StartSmoothSort;
				
				
	END Window;
	
	
	PROCEDURE Open*;
	VAR w: Window
	BEGIN
		NEW( w )
	END Open;


END SortDemo.





SortDemo.Open

SystemTools.Free SortDemo ~

