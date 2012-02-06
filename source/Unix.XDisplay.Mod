(* ETH Oberon, Copyright 2000 ETH Zürich Institut für Computersysteme, ETH Zentrum, CH-8092 Zürich.
Refer to the general ETH Oberon System license contract available at: http://www.oberon.ethz.ch/ *)

MODULE XDisplay;   (** X Windows display driver *)

(*! uses XEvents from X11Api *)

IMPORT S := SYSTEM, Trace, Unix, Machine, Files, UnixFiles, X11, Api:=X11Api, Displays, Strings;

CONST
	IconNameStr = "UnixAos";

	BG = 0;  FG = 15;   (* Background, foreground colors.*)
	

CONST
	(* formats for Transfer.  value DIV 8 = bytes per pixel. *)
	unknown* = 0;
	index8 = 8;  color555 = 16;  color565 = 17;  color664 = 18;
	color888 = 24;  color8888* = 32;

	(* Drawing operation modes. *)
	replace = 0;   (* destcolor := sourcecolor. *)
	paint = 1;   (* destcolor := destcolor OR sourcecolor. *)
	invert = 2;   (* destcolor := destcolor XOR sourcecolor. *)

VAR
	winName, iconName: ARRAY 128 OF CHAR;


	X:	RECORD
			display:				X11.DisplayPtr;
			screen,
			screenw, screenh:	LONGINT;
			cells, planes:		LONGINT;
			defcmap:			X11.Colormap;
			depth:				INTEGER;
		END;

TYPE
	Address = S.ADDRESS;
	
	RGB =	RECORD
				r, g, b: INTEGER
			END;

	Painter* = PROCEDURE ( x, y: INTEGER );

	Marker* = RECORD
				Fade*, Draw*: Painter (** Remove and draw marker. *)
			END;

	Cursor* = RECORD
				marker*: Marker;   (** Cursor marker. *)
				on*: BOOLEAN;   (** Is cursor shown? *)
				X*, Y*: INTEGER (** Absolute cursor position. *)
			END;


	Clip* = OBJECT
		VAR
			d: Display;  lx, ly, lw, lh: LONGINT;

			PROCEDURE & Init( disp: Display );
			BEGIN
				d := disp;  lx := 0; ly := 0; lw := 0; lh := 0;
				Reset
			END Init;

			PROCEDURE Set*( x, y, w, h: LONGINT );
			VAR rect: X11.Rectangle;
			BEGIN
				IF w < 0 THEN  w := 0  END;
				IF h < 0 THEN  h := 0  END;
				IF (x # lx) OR (y # ly) OR (w # lw) OR (h # lh) THEN
					lx := x;  ly := y;  lw := w;  lh := h;
					IF y  < d.height THEN  d.currwin := d.primary  ELSE  d.currwin := d.secondary;  DEC( y, d.height )  END;
					rect.x := SHORT( x );  rect.y := SHORT( y );
					rect.w := SHORT( w );  rect.h := SHORT( h );
					Machine.Acquire( Machine.X11 );
					IF (rect.x <= 0) & (rect.y <= 0) & (rect.w >= d.width) & (rect.h >= d.height) THEN
						X11.SetClipMask( d.xdisp, d.gc, X11.None ) (* no clipping *)
					ELSE
						X11.SetClipRectangles( d.xdisp, d.gc, 0, 0, S.ADR( rect ), 1, X11.YXBanded )
					END;
					Machine.Release( Machine.X11 )
				END;
			END Set;

			PROCEDURE Get*( VAR x, y, w, h: LONGINT );
			BEGIN
				x := lx;  y := ly;  w := lw;  h := lh
			END Get;

			PROCEDURE InClip*( x, y, w, h: LONGINT ): BOOLEAN;
			BEGIN
				RETURN  (x >= lx) & (x + w <= lx + lw) & (y >= ly) & (y + h <= ly + lh)
			END InClip;


			PROCEDURE Reset*;
			BEGIN
				Set( 0, 0, d.width, d.height );
			END Reset;

			(** Intersect with current clip rectangle resulting in a new clip rectangle. *)
			PROCEDURE Adjust*( x, y, w, h: LONGINT );   (* intersection *)
			VAR x0, y0, x1, y1: LONGINT;
			BEGIN
				IF x > lx THEN  x0 := x  ELSE  x0 := lx  END;
				IF y > ly THEN  y0 := y  ELSE  y0 := ly  END;
				IF x + w < lx + lw THEN  x1 := x + w  ELSE  x1 := lx + lw  END;
				IF y + h < ly + lh THEN  y1 := y + h  ELSE  y1 := ly + lh  END;
				Set( x0, y0, x1 - x0, y1 - y0 );
			END Adjust;

		END Clip;



	Display* = OBJECT   (Displays.Display)
			VAR
				xdisp-				: X11.DisplayPtr;
				screen				: LONGINT;
				visual-{UNTRACED}	: X11.VisualPtr;
				depth-				: INTEGER;
				nofcol-				: LONGINT;
				cmap-				: X11.Colormap;
				planesMask-		: LONGINT;
				primary-,
				secondary-,
				currwin*			: X11.Window;
				basePixel-,
				foreground-,
				background-		: LONGINT;
				gc-					: X11.GC;
				clip-				: Clip;

				bigEndian			: BOOLEAN;
				rgb-, defPal-		: ARRAY 256 OF RGB;
				pixel-				: ARRAY 256 OF LONGINT;   (* pixel values for Oberon colors *)

				xformat				: LONGINT;
				currcol, currmode	: LONGINT;
				xfunc				: ARRAY 3 OF LONGINT;
				
				wmDelete- : X11.Atom;

				PROCEDURE SetMode( col: LONGINT );
				VAR mode: LONGINT;
				BEGIN
					mode :=  replace;
					IF (col # -1) & (30 IN S.VAL( SET, col )) THEN  mode := invert;  EXCL( S.VAL( SET, col ), 30 )  END;
					IF mode # currmode THEN  X11.SetFunction( xdisp, gc, xfunc[mode] );  currmode := mode  END;
					IF col # currcol THEN  X11.SetForeground( xdisp, gc, ColorToPixel( col ) );  currcol := col  END;
				END SetMode;



				PROCEDURE Dot*( col, x, y: LONGINT );
				BEGIN
					IF currwin = secondary THEN  DEC( y, height )  END;
					Machine.Acquire( Machine.X11 );
					SetMode( col );
					X11.DrawPoint( xdisp, currwin, gc, x, y );
					Machine.Release( Machine.X11 )
				END Dot;

				PROCEDURE Fill*( col, x, y, w, h: LONGINT );
				BEGIN
					IF (h > 0) & (w > 0) THEN
						IF currwin = secondary THEN  DEC( y, height )  END;
						Machine.Acquire( Machine.X11 );
						SetMode( col );
						X11.FillRectangle( xdisp, currwin, gc, x, y, w, h );
						Machine.Release( Machine.X11 )
					END
				END Fill;

				(** Transfer a block of pixels in "raw" display format to (op = set) or from (op = get) the display.
					Pixels in the rectangular area are transferred from left to right and top to bottom.  The pixels
					are transferred to or from "buf", starting at "ofs".  The line byte increment is "stride", which may
					be positive, negative or zero. *)

				PROCEDURE Transfer*( VAR buf: ARRAY OF CHAR;  ofs, stride, x, y, w, h, op: LONGINT );
				CONST  Get = 0;  Set = 1;
				VAR image: X11.Image;
					imp: X11.ImagePtr;
					bp, bp0, ip: Address; 
					line, ll: LONGINT;
				BEGIN
					ll := w*(xformat DIV 8);
					IF (ofs + (h - 1)*stride + ll > LEN( buf )) OR (ofs + (h - 1)*stride < 0) THEN  HALT( 99 )  END;
		
					IF LEN( imgBuffer ) < 4*w*h THEN
						NEW( imgBuffer, 4*w*h );	(* create buffer outside lock to avoid deadlock *)
					END;

					Machine.Acquire( Machine.X11 );
					image := X11.CreateImage( xdisp, visual, depth, X11.ZPixmap, 0, 0, w, h, 32, 0 );
					imp := S.VAL( X11.ImagePtr, image );
					imp.data := S.ADR( imgBuffer[0] );
					bp0 := S.ADR( buf[ofs] );
					IF op = Set THEN
						FOR line := 0 TO h - 1  DO
							bp := bp0;  ip := imp.data + line*imp.bytesPerLine;
							IF imp.byteOrder = 0 THEN  PutLine( xformat, w, ip, bp )
							ELSE  PutLineBE( xformat, w, ip, bp )
							END;
							bp0 := bp0 + stride;
						END;
						IF currmode # replace THEN  
							X11.SetFunction( xdisp, gc, xfunc[replace] );  currmode := replace  
						END;
						X11.PutImage( xdisp, primary, gc, image, 0, 0, x, y, w, h );
					ELSIF op = Get THEN
						image := X11.GetImage( xdisp, primary, x, y, w, h, planesMask, X11.ZPixmap );
						imp := S.VAL( X11.ImagePtr, image );
						FOR line := 0 TO h - 1 DO
							bp := bp0;  ip := imp.data + line*imp.bytesPerLine;
							IF imp.byteOrder = 0 THEN  GetLine( xformat, w, ip, bp )
							ELSE  GetLineBE( xformat, w, ip, bp )
							END;
							bp0 := bp0 + stride
						END;
						X11.Free( imp.data )
					END;
					X11.Free( image );  imp := NIL;
					Machine.Release( Machine.X11 )
				END Transfer;


				(** Transfer a block of pixels from a 1-bit mask to the display.  Pixels in the rectangular area are
					transferred from left to right and top to bottom.  The pixels are transferred from "buf", starting
					at bit offset "bitofs".  The line byte increment is "stride", which may be positive, negative or zero.
					"fg" and "bg" specify the colors for value 1 and 0 pixels respectively. *)
				PROCEDURE Mask*( VAR buf: ARRAY OF CHAR;  bitofs, stride, fg, bg, x, y, w, h: LONGINT );
				VAR p, i: LONGINT;  s: SET;
					image: X11.Image;
					fgpixel, bgpixel, xret: LONGINT;
					ix, iy, ih: LONGINT;
					imp: X11.ImagePtr;
				BEGIN
					IF (w > 0) & (h > 0) THEN
						IF fg >= 0 THEN  fgpixel := pixel[fg MOD 256]  ELSE  fgpixel := ColorToPixel( fg )  END;
						IF bg >= 0 THEN  bgpixel := pixel[bg MOD 256]  ELSE  bgpixel := ColorToPixel( bg )  END;

						IF LEN( imgBuffer ) < 4*w*h THEN
							NEW( imgBuffer, 4*w*h );	(* create buffer outside lock to avoid deadlock *)
						END;

						Machine.Acquire( Machine.X11 );
						image := X11.CreateImage( xdisp, visual, depth, X11.ZPixmap, 0, 0, w, h, 32, 0 );
						imp := S.VAL( X11.ImagePtr, image );
						imp.data := S.ADR( imgBuffer[0] );
						i := S.ADR( buf[0] ) MOD 4;  INC( bitofs, i*8 );
						p := S.ADR( buf[0] ) - i + bitofs DIV 32*4;   (* p always aligned to 32-bit boundary *)
						bitofs := bitofs MOD 32;  stride := stride*8;
						ix := 0; iy := 0; ih := h;
						LOOP
							S.GET( p, s );  i := bitofs;
							LOOP
								IF (i MOD 32) IN s THEN  xret := X11.PutPixel( image, ix, iy, fgpixel );
								ELSE  xret := X11.PutPixel( image, ix, iy, bgpixel );
								END;
								INC( i );  INC( ix );
								IF i - bitofs = w THEN  EXIT   END;
								IF i MOD 32 = 0 THEN  S.GET( p + i DIV 8, s )  END
							END;
							DEC( ih );
							IF ih = 0 THEN  EXIT   END;
							INC( iy );  ix := 0;  INC( bitofs, stride );
							IF (bitofs >= 32) OR (bitofs < 0) THEN  (* moved outside s *)
								INC( p, bitofs DIV 32*4 );  bitofs := bitofs MOD 32
							END
						END;  (* loop *)
						IF currmode # replace THEN  X11.SetFunction( xdisp, gc, xfunc[replace] )  END;
						X11.PutImage( xdisp, primary, gc, image, 0, 0, x, y, w, h );
						IF currmode # replace THEN  X11.SetFunction( xdisp, gc, xfunc[currmode] )  END;
						X11.Free( image );
						Machine.Release( Machine.X11 );
					END
				END Mask;

				(** Copy source block sx, sy, w, h to destination dx, dy.  Overlap is allowed. *)
				PROCEDURE Copy*( sx, sy, w, h, dx, dy: LONGINT );
				VAR src: X11.DisplayPtr;
				BEGIN
					IF (w > 0) & (h > 0) THEN
						IF sy  < height THEN  src := primary  ELSE  src := secondary;  DEC( sy, height )  END;
						IF currwin = secondary THEN  DEC( sy, height )  END;
						Machine.Acquire( Machine.X11 );
						SetMode( currcol );
						X11.CopyArea( xdisp, src, currwin, gc, sx, sy, w, h, dx, dy  );
						Machine.Release( Machine.X11 )
					END;
				END Copy;


				(** Update the visible display (if caching is used). *)
				PROCEDURE Update*;
				BEGIN
					Machine.Acquire( Machine.X11 );
					X11.Sync( xdisp, X11.False );
					Machine.Release( Machine.X11 )
				END Update;

				(** Map a color value to an 8-bit CLUT index.  Only used if xformat = index8. *)
				PROCEDURE ColorToIndex*( col: LONGINT ): LONGINT;
				BEGIN
					RETURN ColorToIndex0( SELF, col )
				END ColorToIndex;

				(** Map an 8-bit CLUT index to a color value.  Only used if xformat = index8. *)
				PROCEDURE IndexToColor*( n: LONGINT ): LONGINT;
				VAR r, g, b: LONGINT;
				BEGIN
					IF n >= 0 THEN
						IF n > 255 THEN  n := BG  END;
						r := rgb[n].r;  g := rgb[n].g;  b := rgb[n].b;
						RETURN MIN( LONGINT ) + (r*100H + g)*100H + b
					ELSE  RETURN n
					END;
				END IndexToColor;

				PROCEDURE SetColor*( col, red, green, blue: INTEGER );   (* 0 <= col, red, green, blue < 256 *)
				VAR xcol: X11.Color;  res: LONGINT;
				BEGIN
					IF (col < 0) OR (col > 255) THEN  RETURN   END;
					rgb[col].r := red;  rgb[col].g := green;  rgb[col].b := blue;
					xcol.red := 256*red;  xcol.green := 256*green;  xcol.blue := 256*blue;
					Machine.Acquire( Machine.X11 );
					IF depth > 8 THEN
						res := X11.AllocColor( xdisp, cmap, S.ADR( xcol ) );
						IF res # 0 THEN  pixel[col] := xcol.pixel  END
					ELSE
						xcol.flags := CHR( X11.DoAll );  xcol.pixel := pixel[col];
						IF col < nofcol THEN  X11.StoreColor( xdisp, cmap, S.ADR( xcol ) )  END;
					END;
					Machine.Release( Machine.X11 )
				END SetColor;

				PROCEDURE GetColor*( col: INTEGER;  VAR red, green, blue: INTEGER );
				BEGIN
					IF (0 <= col) & (col <= 255) THEN
						red := rgb[col].r;  green := rgb[col].g;  blue := rgb[col].b
					ELSE
						red := rgb[BG].r;  green := rgb[BG].g;  blue := rgb[BG].b
					END
				END GetColor;

				PROCEDURE ColorToPixel*( col: LONGINT ): LONGINT;
				VAR r, g, b, i, ii, x, y, z, m, min: LONGINT;  rc: RGB;
				BEGIN
					r := S.LSH( col, -16 ) MOD 256;  g := S.LSH( col, -8 ) MOD 256;  b := col MOD 256;
					CASE xformat OF
					color8888, color888:
								IF bigEndian THEN  RETURN ASH( b, 16 ) + ASH( g, 8 ) + r
								ELSE  RETURN ASH( r, 16 ) + ASH( g, 8 ) + b
								END
					| color555:
								r := 32*r DIV 256;  g := 32*g DIV 256;  b := 32*b DIV 256;
								IF bigEndian THEN  RETURN ASH( b, 10 ) + ASH( g, 5 ) + r
								ELSE  RETURN ASH( r, 10 ) + ASH( g, 5 ) + b
								END
					| color565:
								r := 32*r DIV 256;  g := 64*g DIV 256;  b := 32*b DIV 256;
								IF bigEndian THEN  RETURN ASH( b, 11 ) + ASH( g, 5 ) + r
								ELSE  RETURN ASH( r, 11 ) + ASH( g, 5 ) + b
								END
					| color664:
								r := 64*r DIV 256;  g := 64*g DIV 256;  b := 16*b DIV 256;
								IF bigEndian THEN  RETURN ASH( b, 12 ) + ASH( g, 6 ) + r
								ELSE  RETURN ASH( r, 10 ) + ASH( g, 4 ) + b
								END
					ELSE  (* index8 *)
						i := 0;  ii := 0;  min := MAX( LONGINT );
						WHILE (i < 256) & (min > 0) DO
							rc := rgb[i];  x := ABS( r - rc.r );  y := ABS( g - rc.g );  z := ABS( b - rc.b );  m := x;
							IF y > m THEN  m := y  END;
							IF z > m THEN  m := z  END;
							m := m*m + (x*x + y*y + z*z);
							IF m < min THEN  min := m;  ii := i  END;
							INC( i )
						END;
						RETURN pixel[ii]
					END
				END ColorToPixel;



				PROCEDURE  & Initialize( absWidth, absHeight, relWidth, relHeight: LONGINT );
				VAR event: Api.XEvent;  root: X11.Window;  gRoot, gX, gY, gW, gH, gBW, gD: LONGINT;
					
					res: LONGINT;
				BEGIN
					xdisp := X.display;  depth := X.depth;  cmap := X.defcmap;  screen := X.screen;
					foreground := X11.BlackPixel( X.display, X.screen );
					background := X11.WhitePixel( X.display, X.screen );
					Machine.Acquire( Machine.X11 );
					root := X11.DefaultRootWindow( X.display );
					primary := X11.CreateSimpleWindow( X.display, root, 0, 0,
											     			X.screenw - 16, X.screenh - 32, 0,
														foreground, background );
					X11.StoreName( xdisp, primary, S.ADR( winName ) );
					X11.SetIconName( xdisp, primary, S.ADR( iconName ) );
					X11.SetCommand( xdisp, primary, Unix.argv, Unix.argc );
					X11.SelectInput( xdisp, primary, X11.ExposureMask );
					
					
					(* set wm_delete_events if in windowed mode *)
					wmDelete := Api.InternAtom(xdisp, "WM_DELETE_WINDOW", Api.True);   
					res := Api.SetWMProtocols(xdisp, primary, S.ADR(wmDelete), 1);
							
					X11.MapRaised( xdisp, primary );
					REPEAT  Api.NextEvent( xdisp, event )
					UNTIL (event.typ = Api.Expose) & (event.window = primary);
					(* adjust to physical window size *)
					X11.GetGeometry( xdisp, primary, gRoot, gX, gY, gW, gH, gBW, gD );
					IF relWidth # -1 THEN
						gW := relWidth * gW DIV 100;
					ELSE
						gW := absWidth;
					END;
					IF relHeight # -1 THEN
						gH := relHeight * gH DIV 100;
					ELSE
						gH := absHeight;
					END;
					IF gW MOD 8 # 0 THEN  DEC( gW, gW MOD 8 )  END;
					X11.ResizeWindow( xdisp, primary, gW, gH );
					width := gW;  height := gH;
					offscreen := height;

					(* pixmap may not be larger than screen: *)
					IF gW > X.screenw THEN  gW := X.screenw  END;
					IF gH > X.screenh THEN  gH := X.screenh  END;
					secondary := X11.CreatePixmap( xdisp, primary, gW, gH, depth );
					Machine.Release( Machine.X11 );

					CreateColors( SELF );  InitPalette( SELF );  SuppressX11Cursors( SELF ); 
					InitFormat( SELF );  CreateGC( SELF );  InitFunctions( SELF );

					NEW( clip, SELF )
				END Initialize;


				(** Finalize the display.  Further calls to display methods are not allowed, and may cause exceptions. *)
				PROCEDURE Finalize*;
				(*
				BEGIN  (* should really be exclusive with Transfer, but we assume the caller keeps to the rules above *)
					fbadr := 0;  fbsize := 0
				*)
				END Finalize;


			END Display;

VAR
	dispname: ARRAY 64 OF CHAR;
	
	imgBuffer: POINTER TO ARRAY OF CHAR;


	PROCEDURE ColorToIndex0( disp: Display; col: LONGINT ): INTEGER;
	VAR idx, i: INTEGER;  r, g, b, min, x, y, z, d: LONGINT;  rc: RGB;
	BEGIN
		r := ASH( col, -16 ) MOD 100H;  g := ASH( col, -8 ) MOD 100H;  b := col MOD 100H;
		i := 0;  idx := 0;  min := MAX( LONGINT );
		WHILE (i < 256) & (min > 0) DO
			rc := disp.defPal[i];  x := ABS( r - rc.r );  y := ABS( g - rc.g );  z := ABS( b - rc.b );  d := x;
			IF y > d THEN  d := y  END;
			IF z > d THEN  d := z  END;
			d := d*d + (x*x + y*y + z*z);
			IF d < min THEN  min := d;  idx := i  END;
			INC( i )
		END;
		RETURN idx
	END ColorToIndex0;


	PROCEDURE PutLine( xformat, width: LONGINT;  VAR ip, bp: Address );
	VAR colum: LONGINT;  byte: CHAR;
	BEGIN
		FOR colum := 0 TO width - 1 DO
			CASE xformat OF
			| index8:
						S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );
			| color565, color555, color664:
						S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );
						S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );
			| color888:
						S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );   (* B *)
						S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );   (* G *)
						S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );   (* R *)
						byte := 0X;  S.PUT( ip, byte );  INC( ip );
			ELSE  (* color8888 *)
				S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );   (* B *)
				S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );   (* G *)
				S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );   (* R *)
				S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );   (* X *)
			END
		END;
	END PutLine;



	PROCEDURE GetLine( xformat, width: LONGINT;  VAR ip, bp: Address );
	VAR colum: LONGINT;  byte: CHAR;
	BEGIN
		FOR colum := 0 TO width - 1 DO
			CASE xformat OF
			| index8:
						S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );
			| color565, color555, color664:
						S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );
						S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );
			| color888:
						S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );   (* B *)
						S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );   (* G *)
						S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );   (* R *)
						INC( ip )
			ELSE  (* color8888 *)
				S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );   (* B *)
				S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );   (* G *)
				S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );   (* R *)
				S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );   (* X *)
			END
		END;
	END GetLine;


	PROCEDURE PutLineBE( xformat, width: LONGINT;  VAR ip, bp: Address );
	VAR colum: LONGINT;  byte: CHAR;
	BEGIN
		FOR colum := 0 TO width - 1 DO
			CASE xformat OF
			index8:
						S.GET( bp, byte );  S.PUT( ip, byte );  INC( bp );  INC( ip );
			| color565, color555, color664:
						S.GET( bp + 1, byte );  S.PUT( ip, byte );  INC( ip );
						S.GET( bp + 0, byte );  S.PUT( ip, byte );  INC( ip );
						INC( bp, 2 )
			| color888:
						byte := 0X;  S.PUT( ip, byte );  INC( ip );
						S.GET( bp + 2, byte );  S.PUT( ip, byte );  INC( ip );   (* B *)
						S.GET( bp + 1, byte );  S.PUT( ip, byte );  INC( ip );   (* G *)
						S.GET( bp + 0, byte );  S.PUT( ip, byte );  INC( ip );   (* R *)
						INC( bp, 3 );
			ELSE  (* color8888 *)
				S.GET( bp + 3, byte );  S.PUT( ip, byte );  INC( ip );   (* X *)
				S.GET( bp + 2, byte );  S.PUT( ip, byte );  INC( ip );   (* B *)
				S.GET( bp + 1, byte );  S.PUT( ip, byte );  INC( ip );   (* G *)
				S.GET( bp + 0, byte );  S.PUT( ip, byte );  INC( ip );   (* R *)
				INC( bp, 4 );
			END;
		END;
	END PutLineBE;

	PROCEDURE GetLineBE( xformat, width: LONGINT;  VAR ip, bp: Address );
	VAR colum: LONGINT;  byte: CHAR;
	BEGIN
		FOR colum := 0 TO width - 1 DO
			CASE xformat OF
			| index8:
						S.GET( ip, byte );  S.PUT( bp, byte );  INC( ip );  INC( bp );
			| color565, color555, color664:
						S.GET( ip, byte );  S.PUT( bp + 1, byte );  INC( ip );
						S.GET( ip, byte );  S.PUT( bp + 0, byte );  INC( ip );
						INC( bp, 2 )
			| color888:
						INC( ip );
						S.GET( ip, byte );  S.PUT( bp + 2, byte );  INC( ip );   (* B *)
						S.GET( ip, byte );  S.PUT( bp + 1, byte );  INC( ip );   (* G *)
						S.GET( ip, byte );  S.PUT( bp + 0, byte );  INC( ip );   (* R *)
						INC( bp, 3 );
			ELSE  (* color8888 *)
				S.GET( ip, byte );  S.PUT( bp + 3, byte );  INC( ip );   (* X *)
				S.GET( ip, byte );  S.PUT( bp + 2, byte );  INC( ip );   (* B *)
				S.GET( ip, byte );  S.PUT( bp + 1, byte );  INC( ip );   (* G *)
				S.GET( ip, byte );  S.PUT( bp + 0, byte );  INC( ip );   (* R *)
				INC( bp, 4 );
			END
		END;
	END GetLineBE;



	PROCEDURE NewPattern( d: Display;
							CONST image: ARRAY OF SET;  
							width, height: INTEGER ): X11.Pattern;
	VAR
		pixmap: X11.Pixmap;  pat: X11.PatternPtr;
		w, h, i, j, b, dest, srcw, destb, srci, desti: LONGINT;
		data: ARRAY 256*32 OF CHAR;   (* 256*256 bits *)
	BEGIN
		i := 0;
		WHILE i < LEN( data ) DO  data[i] := 0X;  INC( i )  END;
		w := width;  h := height;
		srcw := (width + 31) DIV 32;   (* number of words in source line *)
		destb := (w + 7) DIV 8;   (* number of bytes in dest line *)
		srci := (height - 1)*srcw;  desti := 0;
		WHILE srci >= 0 DO
			i := 0;  j := 0;  b := 0;  dest := 0;
			LOOP
				dest := dest DIV 2;
				IF b IN image[srci + j + 1] THEN  INC( dest, 80H )  END;
				INC( b );
				IF b MOD 8 = 0 THEN
					data[desti + i] := CHR( dest );  INC( i );  dest := 0;
					IF i >= destb THEN  EXIT   END
				END;
				IF b = 32 THEN
					b := 0;  INC( j );
					IF j >= srcw THEN
						WHILE i < destb DO  data[desti + i] := 0X;  INC( i )  END;
						EXIT
					END
				END
			END;
			INC( desti, destb );  DEC( srci, srcw )
		END;
		Machine.Acquire( Machine.X11 );
		pixmap := X11.CreateBitmapFromData( d.xdisp, d.primary, S.ADR( data[0] ), w, h );
		Machine.Release( Machine.X11 );
		IF pixmap = 0 THEN  HALT( 99 )  END;
		pat := S.VAL( X11.PatternPtr, Unix.malloc( S.SIZEOF( X11.PatternDesc ) ) );
		pat.x := 0;  pat.y := 0;  pat.w := width;  pat.h := height;  pat.pixmap := pixmap;
		RETURN S.VAL( LONGINT, pat )
	END NewPattern;

	PROCEDURE InitNames;
	VAR cwd: ARRAY 128 OF CHAR;
	BEGIN
		UnixFiles.GetWorkingDirectory( cwd );
		COPY( Machine.version, winName );  
		Strings.Append( winName, ",  Work: " );  Strings.Append( winName, cwd );
		iconName := IconNameStr;
	END InitNames;

	PROCEDURE getDisplayName;
	VAR adr: LONGINT;  i: INTEGER;  ch: CHAR;
	BEGIN
		Unix.GetArgval( "-display", dispname );
		IF dispname = "" THEN
			adr := Unix.getenv( S.ADR( "DISPLAY" ) );
			IF adr # 0 THEN
				i := 0;
				REPEAT  S.GET( adr, ch );  INC( adr );  dispname[i] := ch;  INC( i )   UNTIL ch = 0X;
			ELSE  dispname := ":0"
			END
		END
	END getDisplayName;

	PROCEDURE OpenX11Display;
	VAR fd: LONGINT;
	BEGIN
		getDisplayName;
		X.display := Api.OpenDisplay( dispname );
		IF X.display = 0 THEN
			Trace.String( "Cannot open X11 display " );  Trace.StringLn( dispname );  Unix.exit( 1 )
		END;
		S.GET( X.display + 8, fd );
		X.screen := X11.DefaultScreen( X.display );
		X.screenw := X11.DisplayWidth( X.display, X.screen );
		X.screenh := X11.DisplayHeight( X.display, X.screen );
		X.depth := SHORT( X11.DefaultDepth( X.display, X.screen ) );
		IF X.depth < 8 THEN  ColorError  END;
		X.defcmap := X11.DefaultColormap( X.display, X.screen );
		X.cells := X11.DisplayCells( X.display, X.screen );
		X.planes := X11.DisplayPlanes( X.display, X.screen );
	END OpenX11Display;

	PROCEDURE ColorError;
	BEGIN
		Trace.StringLn( "UnixAos needs a color display. sorry." );  Unix.exit( 1 )
	END ColorError;

	PROCEDURE CreateColors( d: Display );
	VAR col: INTEGER;
		visualInfo: X11.VisualInfo;  visual{UNTRACED}: X11.VisualPtr;
	BEGIN
		Machine.Acquire( Machine.X11 );
		col := 0;
		WHILE col < 256 DO  d.pixel[col] := col;  INC( col )  END;
		IF (d.depth > 8) & (X11.MatchVisualInfo( d.xdisp, d.screen, d.depth, X11.TrueColor, visualInfo ) = 1) THEN
			visual := visualInfo.visual;
		ELSIF X11.MatchVisualInfo( d.xdisp, d.screen, d.depth, X11.PseudoColor, visualInfo ) = 1 THEN
			visual := visualInfo.visual
		ELSE  ColorError
		END;
		d.nofcol := visual.mapEntries;
		d.bigEndian := FALSE;
		IF d.depth > 8 THEN  d.bigEndian := visual.blueMask > visual.redMask  END;
		IF d.depth <= 8 THEN
			d.nofcol := visual.mapEntries;
			d.cmap := X11.CreateColormap( d.xdisp, d.primary, visual, X11.AllocAll );
			X11.SetWindowColormap( d.xdisp, d.primary, d.cmap );
			d.foreground := d.pixel[FG];
			d.background := d.pixel[BG];
			X11.SetWindowBackground( d.xdisp, d.primary, d.background );
			X11.ClearWindow( d.xdisp, d.primary )
		END;
		Machine.Release( Machine.X11 );
		d.visual := visual;  d.basePixel := 0;  d.planesMask := ASH( 1, d.depth ) - 1
	END CreateColors;


	PROCEDURE InitPalette( d: Display );
	VAR f: Files.File;  r: Files.Reader;  red, green, blue: CHAR;  i, cols: INTEGER;
	BEGIN
		IF d.depth >= 8 THEN cols := 256 ELSE cols := 16 END;
		f := Files.Old( "Default.Pal" );
		IF f # NIL THEN
			Files.OpenReader( r, f, 0 );
			FOR i := 0 TO cols - 1 DO
				r.Char( red );  r.Char( green );  r.Char( blue );
				d.SetColor( i, ORD( red ), ORD( green ), ORD( blue ) )
			END
		END;
		d.defPal := d.rgb
	END InitPalette;


	PROCEDURE SuppressX11Cursors( d: Display );
	VAR 
		fg, bg: X11.Color;  src, msk: X11.PatternPtr;
		image: ARRAY 17 OF SET;  i: INTEGER;
		noCursor: X11.Cursor;
	BEGIN
		fg.red := 256*d.rgb[FG].r;  fg.green := 256*d.rgb[FG].g;  fg.blue := 256*d.rgb[FG].b;
		bg.red := 256*d.rgb[BG].r;  bg.green := 256*d.rgb[BG].g;  bg.blue := 256*d.rgb[BG].b;

		FOR i := 1 TO 16 DO  image[i] := {}  END;
		src := S.VAL( X11.PatternPtr, NewPattern( d, image, 16, 16 ) );  
		msk := S.VAL( X11.PatternPtr, NewPattern( d, image, 16, 16 ) );
		
		Machine.Acquire( Machine.X11 );
		noCursor := X11.CreatePixmapCursor( d.xdisp, src.pixmap, msk.pixmap, S.ADR( fg ), S.ADR( bg ), 1, 1 );
		X11.DefineCursor( d.xdisp, d.primary, noCursor );
		Machine.Release( Machine.X11 )
	END SuppressX11Cursors;
	

	PROCEDURE InitFormat( d: Display );
	VAR visual: X11.VisualPtr;
	BEGIN
		visual := S.VAL( X11.VisualPtr, d.visual );
		IF d.depth = 8 THEN  
			d.format := Displays.index8;
			d.xformat := index8
		ELSIF d.depth = 15 THEN  
			d.format := Displays.color565;
			d.xformat := color555
		ELSIF d.depth = 16 THEN
			d.format := Displays.color565;
			IF visual.blueMask = 0FH THEN  
				d.xformat := color664
			ELSE  
				d.xformat := color565
			END
		ELSIF d.depth = 24 THEN  
			d.format := Displays.color888;
			d.xformat := color888
		ELSIF d.depth = 32 THEN  
			d.format := Displays.color8888;
			d.xformat := color8888
		ELSE  
			d.format := unknown
		END;
		Trace.String( "X11 Display depth = " ); Trace.Int( d.depth, 1 ); Trace.Ln
	END InitFormat;

	PROCEDURE CreateGC( d: Display );
	BEGIN
		Machine.Acquire( Machine.X11 );
		d.gc := X11.CreateGC( d.xdisp, d.primary, 0, 0 );
		IF d.gc = 0 THEN  Machine.Release( Machine.X11 );  HALT( 45 )  END;
		X11.SetPlaneMask( d.xdisp, d.gc, d.planesMask );
		X11.SetGraphicsExposures( d.xdisp, d.gc, X11.True );
		X11.SetBackground( d.xdisp, d.gc, d.background );
		Machine.Release( Machine.X11 );
	END CreateGC;

	PROCEDURE InitFunctions( d: Display );
	BEGIN
		d.xfunc[replace] := X11.GXcopy;
		d.xfunc[paint] := X11.GXor;   (* not used *)
		(* drawing in invert mode with BackgroundCol on BackgroundCol is a no-op: *)
		IF S.VAL( SET, d.background )*S.VAL( SET, d.planesMask ) # {} THEN
			d.xfunc[invert] := X11.GXequiv
		ELSE
			d.xfunc[invert] := X11.GXxor
		END;
		d.currcol := -1;  d.currmode := -1;
	END InitFunctions;


	(* PB - 2010-04-20
		Return:
			-1: absolute width and height according to DisplaySize config string.
			else: value from 50 to 100 as scaling factor, argument variables width and height are unspecified.

		Lower limit is either 50% as scaling factor or 640x480 as absolute size.
	*)
	PROCEDURE GetDisplaySize(VAR width, height: LONGINT): LONGINT;  (* % of Screen [50% ... 100%] *)
	VAR buf: ARRAY 64 OF CHAR; size, i: LONGINT; c: CHAR; absolute: BOOLEAN;
	BEGIN
		Machine.GetConfig( "DisplaySize", buf );
		IF buf = "" THEN size := 100
		ELSE
			size := 0; c := buf[0];  i := 0;
			WHILE (c >= '0') & (c <= '9') DO
				size := 10*size + ORD( c ) - ORD( '0' );
				INC( i ); c := buf[i]
			END;
			IF c = 'x' THEN
				width := size;
				size := 0;
				INC( i ); c := buf[i];
			END;
			WHILE (c >= '0') & (c <= '9') DO
				size := 10*size + ORD( c ) - ORD( '0' );
				INC( i ); c := buf[i]
			END;
			IF (width # 0) & (size # 0) THEN
				height := size;
				absolute := TRUE;
			ELSIF (width # 0) THEN (* failed to read two numbers -> fall back to scaling *)
				size := width;
				width := 0
			END;
			IF absolute THEN
				size := -1;
				IF width < 640 THEN width := 640; END;
				IF height < 480 THEN height := 480; END;
			ELSE
				IF size < 50 THEN  size := 50  END;
				IF size > 100 THEN  size := 100  END
			END;
		END;
		RETURN size
	END GetDisplaySize;

	PROCEDURE Install*;
	VAR disp: Display; res: LONGINT; s, w, h: LONGINT;
	BEGIN
		InitNames; OpenX11Display;
		s := GetDisplaySize( w, h );
		NEW( disp, w, h, s, s );
		disp.SetName( "XDisplay" );
		disp.desc := "X11 display driver";
		Displays.registry.Add( disp, res );
	END Install;

BEGIN
	NEW( imgBuffer, 10000 )
END XDisplay.