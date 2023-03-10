(* ETH Oberon, Copyright 2001 ETH Zuerich Institut fuer Computersysteme, ETH Zentrum, CH-8092 Zuerich.
Refer to the "General ETH Oberon System Source License" contract available at: http://www.oberon.ethz.ch/ *)

MODULE Bitmaps IN Oberon;	(** non-portable *)

(* as 20.02.99, ported to Shark Oberon *)

(* to do:
o get rid of buffer
o ASSERT bounds everywhere
*)

IMPORT SYSTEM, Display;

CONST
	BufSize = 10000H;
	Assembler = TRUE;

TYPE
	Bitmap* = POINTER TO BitmapDesc;
	BitmapDesc* = RECORD	(* cf. Display.DisplayBlock  *)
		width*, height*, depth*: SIGNED16;	(* offset 0, 2, 4 *)
		wth*, size: SIGNED32;	(* offset 8, 12 *)
		address*: ADDRESS;	(* offset 16 *)
	END;

	Buffer = RECORD bytes: ARRAY BufSize OF CHAR END;

VAR
	buffer: POINTER TO Buffer;

PROCEDURE Define*(B: Bitmap; width, height, depth: SIGNED16; address: ADDRESS);
BEGIN
	B.width := width;
	B.wth := width;
	B.height := height;
	B.depth := depth;
	B.address := address;
	B.size := LONG(width)*height
END Define;

PROCEDURE Get*(B: Bitmap; X, Y: SIGNED16): SIGNED16;
VAR ofs: SIGNED32; ch: CHAR;
BEGIN
	ofs := Y*B.wth + X;  ASSERT((ofs >= 0) & (ofs < B.size));
	SYSTEM.GET(B.address + ofs, ch);
	RETURN ORD(ch)
END Get;

PROCEDURE Clear*(B: Bitmap);
VAR adr: ADDRESS; size: SIGNED32;
BEGIN
	size := B.size;  adr := B.address;
	WHILE size >= 4 DO
		SYSTEM.PUT(adr, SIGNED32(0));
		INC(adr, 4);  DEC(size, 4)
	END;
	WHILE size > 0 DO SYSTEM.PUT(adr, 0X);  INC(adr);  DEC(size) END
END Clear;

PROCEDURE Dot*(B: Bitmap; col, X, Y, mode: SIGNED16);
VAR adr: ADDRESS;  ch: CHAR;
BEGIN
	adr := Y*B.wth + X;  ASSERT((adr >= 0) & (adr < B.size));
	INC(adr, B.address);
	IF mode = Display.invert THEN
		SYSTEM.GET(adr, ch);
		SYSTEM.PUT(adr, CHR(SIGNED32(
				SET(ORD(ch)) / SET(col))))
	ELSE
		SYSTEM.PUT(adr, CHR(col))
	END
END Dot;

PROCEDURE CopyBlock0(n, w: SIGNED32; adr: ADDRESS; buf: ADDRESS; width: SIGNED32;  from: BOOLEAN);
BEGIN
	IF from THEN
		REPEAT SYSTEM.MOVE(adr, buf, w); DEC(n);  INC(adr, width);  INC(buf, w) UNTIL n = 0
	ELSE
		REPEAT SYSTEM.MOVE(buf, adr, w); DEC(n);  INC(adr, width);  INC(buf, w) UNTIL n = 0
	END
END CopyBlock0;

PROCEDURE CopyBlock*(sB, dB: Bitmap; SX, SY, W, H, DX, DY, mode: SIGNED16);
VAR SourceWth, DestWth, sx, sy, w, h, dx, dy, w0, h0, dx0, dy0, src, dst, n, bufLines: SIGNED32;
BEGIN	(* only the destination block is clipped *)
	SourceWth := sB.wth; DestWth := dB.wth;
	sx := SX;  sy := SY;  w := W;  h := H;  dx := DX;  dy := DY;
	w0 := w;  h0 := h;  dx0 := dx;  dy0 := dy;
	IF dx < 0 THEN dx := 0;  DEC(w, dx-dx0) END;
	IF dy < 0 THEN dy := 0;  DEC(h, dy-dy0) END;
	IF (w > 0) & (h > 0) & (w <= w0) & (h <= h0) THEN
		IF dx+w-1 > dB.width-1 THEN DEC(w, dx+w-1 - (dB.width-1)) END;
		IF dy+h-1 > dB.height-1 THEN DEC(h, dy+h-1 - (dB.height-1)) END;
		IF (w > 0) & (h > 0) & (w <= w0) & (h <= h0) THEN
			src := sy*SourceWth + sx;  ASSERT((src >= 0) & (src < sB.size));
			dst := dy*DestWth + dx;  ASSERT((dst >= 0) & (dst < dB.size));
			bufLines := BufSize DIV w;	(* lines to copy at a time *)
			IF bufLines > h THEN bufLines := h END;
				(* adjust direction for overlap *)
			IF (dy-h+1 < sy) & (sy < dy) THEN	(* start at bottom *)
				n := h-bufLines;
				INC(src, SourceWth*n);  INC(dst, DestWth*n);
				REPEAT
					CopyBlock0(bufLines, w, sB.address+src, ADDRESSOF(buffer.bytes[0]), SourceWth, TRUE);
					CopyBlock0(bufLines, w, dB.address+dst, ADDRESSOF(buffer.bytes[0]), DestWth, FALSE);
					DEC(h, bufLines);
					IF bufLines > h THEN bufLines := h END;
					DEC(src, bufLines * SourceWth);  DEC(dst, bufLines * DestWth)
				UNTIL h = 0
			ELSE	(* start at top *)
				REPEAT
					CopyBlock0(bufLines, w, sB.address+src, ADDRESSOF(buffer.bytes[0]), SourceWth, TRUE);
					CopyBlock0(bufLines, w, dB.address+dst, ADDRESSOF(buffer.bytes[0]), DestWth, FALSE);
					INC(src, bufLines * SourceWth);  INC(dst, bufLines * DestWth);
					DEC(h, bufLines);
					IF bufLines > h THEN bufLines := h END
				UNTIL h = 0
			END
		END
	END
END CopyBlock;

PROCEDURE CopyPattern0(ofs: SIGNED32; src, dst: ADDRESS; w, col, mode: SIGNED32);
VAR ch: CHAR;  m, i: SIGNED32;  s: SET;
BEGIN
	IF mode = Display.invert THEN
		REPEAT	(* loop over w pixels *)
			SYSTEM.GET(src, ch);
			i := ofs;	(* start bit *)
			m := 8;	(* stop bit *)
			IF m > ofs+w THEN m := ofs+w END;
			REPEAT	(* loop over bits *)
				IF ODD(ASH(ORD(ch), -i)) THEN	(* pixel on *)
					SYSTEM.GET(dst, ch);
					s := SET(ORD(ch));
					SYSTEM.PUT(dst, CHR(SIGNED32(SET(col) / s)))
				END;
				INC(dst);  INC(i)
			UNTIL i = m;
			INC(src);  DEC(w, m-ofs);  ofs := 0
		UNTIL w = 0
	ELSE (* paint, replace *)
		REPEAT	(* loop over w pixels *)
			SYSTEM.GET(src, ch);
			i := ofs;	(* start bit *)
			m := 8;	(* stop bit *)
			IF m > ofs+w THEN m := ofs+w END;
			REPEAT	(* loop over bits *)
				IF ODD(ASH(ORD(ch), -i)) THEN	(* pixel on *)
					(* paint & replace *)
					SYSTEM.PUT(dst, CHR(col))
				ELSIF mode = Display.replace THEN	(* pixel off *)
					SYSTEM.PUT(dst, CHR(Display.BG))
				ELSE (* skip *)
				END;
				INC(dst);  INC(i)
			UNTIL i = m;
			INC(src);  DEC(w, m-ofs);  ofs := 0
		UNTIL w = 0
	END;
END CopyPattern0;

PROCEDURE CopyPattern1(B: Bitmap; src: ADDRESS; x, y, w, col, mode: SIGNED32);
VAR ch: CHAR;  m, i: SIGNED32;
BEGIN
	IF (y < 0) OR (y > B.height-1) THEN RETURN END;
	REPEAT	(* loop over w pixels *)
		SYSTEM.GET(src, ch);
		i := 0;	(* start bit *)
		m := 8;	(* stop bit *)
		IF m > w THEN m := w END;
		REPEAT	(* loop over bits *)
			IF ODD(ASH(ORD(ch), -i)) THEN	(* pixel on *)
				Dot(B,SHORT(col), SHORT(x), SHORT(y), SHORT(mode))
			ELSIF mode = Display.replace THEN	(* pixel off *)
				Dot(B,Display.BG, SHORT(x), SHORT(y), Display.replace)
			ELSE (* skip *)
			END;
			INC(x);  INC(i)
		UNTIL i = m;
		INC(src);  DEC(w, m)
	UNTIL w = 0
END CopyPattern1;

PROCEDURE CopyPattern*(B: Bitmap; col: SIGNED16; pat: Display.Pattern; X, Y, mode: SIGNED16);
VAR x, y, x2, y2, w, w0, h: SIGNED32; src, dst: ADDRESS;  ch: CHAR;
BEGIN
	SYSTEM.GET(pat, ch);  w := ORD(ch);
	SYSTEM.GET(pat+1, ch);  h := ORD(ch);
	IF (w > 0) & (h > 0) THEN
		x := X;  y := Y;  x2 := x+w-1;  y2 := y+h-1;	(* (x,y) bottom left & (x2,y2) top right *)
		src := pat+2;	(* first line of pattern *)
		w0 := (w+7) DIV 8;	(* bytes in pattern line *)
		IF (x >= 0) & (y >= 0) & (x2 < B.width) & (y2 < B.height) THEN	(* fully visible - common case *)
			dst := y * B.wth + x + B.address;
			REPEAT	(* loop over h lines *)
				CopyPattern0(0, src, dst, w, col, mode);
				DEC(h);  INC(dst, B.wth);  INC(src, w0)
			UNTIL h = 0
		ELSIF (x2 >= 0) & (y2 >= 0) & (x < B.width) & (y < B.height) THEN	(* partially visible *)
			REPEAT	(* loop over h lines *)
				CopyPattern1(B, src, x, y, w, col, mode);
				INC(y);  INC(src, w0);  DEC(h)
			UNTIL h = 0
		ELSE (* invisible *)
		END
	END
END CopyPattern;

PROCEDURE ReplConst*(B: Bitmap; col, X, Y, W, H, mode: SIGNED16);
VAR addr, addr0: ADDRESS; pat, w: SIGNED32; s: SET; c: CHAR;
BEGIN
	addr := B.address + B.wth*Y + X;
	pat := col + ASH(col, 8) + ASH(col, 16) + ASH(col, 24);
	IF mode = Display.invert THEN
		WHILE H > 0 DO w := W; addr0 := addr;
			WHILE w # 0 DO
				SYSTEM.GET(addr0, c);
				s := SET(ORD(c));
				SYSTEM.PUT(addr0, CHR(SIGNED32(s/SET(col))));
				DEC(w); INC(addr0)
			END;
			INC(addr, B.wth); DEC(H)
		END
	ELSE
		WHILE H > 0 DO w := W; addr0 := addr;
			WHILE w # 0 DO SYSTEM.PUT(addr0, CHR(col)); DEC(w); INC(addr0) END;
			INC(addr, B.wth); DEC(H)
		END
	END;
END ReplConst;

PROCEDURE FillPattern0(ofs: SIGNED32; src, dst: ADDRESS; w, pw, col, mode: SIGNED32);
VAR ch: CHAR;  m, i: SIGNED32; src0: ADDRESS; left: SIGNED32;  s: SET; c: CHAR;
BEGIN
	left := pw-ofs;	(* pixels left to do in pattern *)
	src0 := src;  INC(src, ofs DIV 8);  ofs := ofs MOD 8;	(* start position *)
	IF mode = Display.invert THEN
		REPEAT	(* loop over w pixels *)
			SYSTEM.GET(src, ch);
			i := ofs;	(* start bit *)
			m := 8;	(* stop bit *)
			IF m > ofs+left THEN m := ofs+left END;	(* max left times *)
			IF m > ofs+w THEN m := ofs+w END;	(* max w times *)
			REPEAT	(* loop over bits *)
				IF ODD(ASH(ORD(ch), -i)) THEN	(* pixel on *)
					SYSTEM.GET(dst, c);
					s := SET(ORD(c));
					SYSTEM.PUT(dst, CHR(SIGNED32(SET(col) / s)))
				END;
				INC(dst);  INC(i)
			UNTIL i = m;
			INC(src);  DEC(left, m-ofs);  DEC(w, m-ofs);  ofs := 0;
			IF left = 0 THEN src := src0;  left := pw END	(* wrap to start of pattern *)
		UNTIL w = 0
	ELSIF mode = Display.paint THEN
		REPEAT	(* loop over w pixels *)
			SYSTEM.GET(src, ch);
			i := ofs;	(* start bit *)
			m := 8;	(* stop bit *)
			IF m > ofs+left THEN m := ofs+left END;	(* max left times *)
			IF m > ofs+w THEN m := ofs+w END;	(* max w times *)
			REPEAT	(* loop over bits *)
				IF ODD(ASH(ORD(ch), -i)) THEN	(* pixel on *)
					SYSTEM.PUT(dst, CHR(col))
				END;
				INC(dst);  INC(i)
			UNTIL i = m;
			INC(src);  DEC(left, m-ofs);  DEC(w, m-ofs);  ofs := 0;
			IF left = 0 THEN src := src0;  left := pw END	(* wrap to start of pattern *)
		UNTIL w = 0
	ELSE (* replace *)
		REPEAT	(* loop over w pixels *)
			SYSTEM.GET(src, ch);
			i := ofs;	(* start bit *)
			m := 8;	(* stop bit *)
			IF m > ofs+left THEN m := ofs+left END;	(* max left times *)
			IF m > ofs+w THEN m := ofs+w END;	(* max w times *)
			REPEAT	(* loop over bits *)
				IF ODD(ASH(ORD(ch), -i)) THEN	(* pixel on *)
					SYSTEM.PUT(dst, CHR(col))
				ELSE (* pixel off *)
					SYSTEM.PUT(dst, CHR(Display.BG))
				END;
				INC(dst);  INC(i)
			UNTIL i = m;
			INC(src);  DEC(left, m-ofs);  DEC(w, m-ofs);  ofs := 0;
			IF left = 0 THEN src := src0;  left := pw END	(* wrap to start of pattern *)
		UNTIL w = 0
	END
END FillPattern0;

PROCEDURE ReplPattern*(B: Bitmap; col: SIGNED16; pat: SIGNED32; X, Y, W, H, mode: SIGNED16);
VAR px, pw, ph, x, y, x2, y2, w, w0, h: SIGNED32; src0, src, dst: ADDRESS;  ch: CHAR;
BEGIN
	x := X;  y := Y;  w := W;  h := H;
	x2 := x+w-1;  y2 := y+h-1;	(* (x,y) bottom left & (x2,y2) top right *)
	IF (w > 0) & (h > 0) THEN
		SYSTEM.GET(pat, ch);  pw := ORD(ch);
		SYSTEM.GET(pat+1, ch);  ph := ORD(ch);
		IF (pw > 0) & (ph > 0) THEN
			INC(pat, 2);	(* adr of bitmap *)
			w0 := (pw+7) DIV 8;	(* bytes in pattern line *)
			src0 := pat + (ph-1)*w0;	(* last line of pattern *)
			src := pat;	(* start line of pattern *)
			px := x MOD pw;	(* start pixel offset *)
			dst := y * B.wth + x + B.address;
			REPEAT	(* loop over h lines *)
				FillPattern0(px, src, dst, w, pw, col, mode);
				DEC(h);  INC(dst, B.wth);
				IF src = src0 THEN src := pat ELSE INC(src, w0) END
			UNTIL h = 0
		END
	END
END ReplPattern;

PROCEDURE DisplayBlock*(B: Bitmap; SX, SY, W, H, DX, DY, mode: SIGNED16; VAR colortable: ARRAY OF SIGNED32 (* fof *));
BEGIN
	Display.DisplayBlock(B, SX, SY, W, H, DX, DY, mode,colortable);
END DisplayBlock;

PROCEDURE GetPix*(VAR addr: ADDRESS; VAR buf: SYSTEM.BYTE; depth: SIGNED16);
VAR s1, s2, s3: SIGNED8;
BEGIN
	IF depth = 8 THEN SYSTEM.GET(addr, buf); INC(addr)
	ELSIF depth = 4 THEN
		SYSTEM.GET(addr, s1); INC(addr); SYSTEM.GET(addr, s2); INC(addr); buf := s2*16 + (s1 MOD 16)
	ELSE (* depth = 1 *)
		s1 := 0; s2 := 0;
		WHILE s1 < 8 DO SYSTEM.GET(addr, s3); INC(addr); INC(s1); s2 := s2*2 + s3 MOD 2 END; buf := s2
	END;
END GetPix;

PROCEDURE PutPix*(VAR addr: ADDRESS; border: ADDRESS; buf: SYSTEM.BYTE; depth: SIGNED16);
VAR s1: SIGNED8;
BEGIN
	IF (depth = 8) & (addr < border) THEN SYSTEM.PUT(addr, buf); INC(addr)
	ELSIF depth = 4 THEN
		IF addr < border THEN SYSTEM.PUT(addr, SYSTEM.VAL(SIGNED8, buf) MOD 16); INC(addr) END;
		IF addr < border THEN SYSTEM.PUT(addr, SYSTEM.VAL(SIGNED8, buf) DIV 16 MOD 16); INC(addr) END;
	ELSE (* depth = 1 *)
		s1 := 0;
		WHILE s1 < 8 DO
			IF addr < border THEN
				IF ODD(SYSTEM.VAL(SIGNED8, buf)) THEN SYSTEM.PUT(addr, 15) ELSE SYSTEM.PUT(addr, 0) END
			END;
			INC(s1); INC(addr); buf := SYSTEM.VAL(SIGNED8, buf) DIV 2;
		END
	END;
END PutPix;

PROCEDURE -Copy0(src, dst: ADDRESS; hx, sw2, dw2: SIGNED32);
CODE {SYSTEM.AMD64}
	POP RDX	; dw2
	POP RCX	; sw2
	POP RBX	; hx
	POP RDI	; dst
	POP RSI	; src
	MOV EAX, EDX
	SHR EAX, 1
	PUSH RAX	; count
for:
	MOV AL, [RSI]
	MOV [RDI], AL
	JMP while1
while0:
	INC RSI
	SUB EBX, EDX
while1:
	CMP EBX, 0
	JG while0
	INC RDI
	ADD EBX, ECX
	DEC DWORD [RSP]
	JNZ for
	POP RAX
END Copy0;

PROCEDURE Copy*(sB, dB: Bitmap; SX, SY, SW, SH, DX, DY, DW, DH, mode: SIGNED16);
VAR hx, hy, DW2, SW2: SIGNED32; src, dst: ADDRESS; i: SIGNED32; dy: SIGNED16; ch: CHAR;
BEGIN
	IF (SX >= 0) & (SY >= 0) & (SX+SW <= sB.width) & (SY+SH <= sB.height) &
			(DX >= 0) & (DY >= 0) & (DX+DW <= dB.width) & (DY+DH <= dB.height) &
			(SW > 0) & (SH > 0) & (DW > 0) & (DH > 0) THEN
		dy := DY + DH; DW2 := 2 * DW; SW2 := 2 * SW;
		hy := 2*SH - DH;
		WHILE DY < dy DO
			IF Assembler THEN
				Copy0(sB.address + SY*sB.wth + SX, dB.address + DY*dB.wth + DX, 2*SW - DW, SW2, DW2)
			ELSE
				hx := 2*SW - DW;
				src := sB.address + SY*sB.wth + SX;
				dst := dB.address + DY*dB.wth + DX;
				FOR i := 1 TO DW DO
					SYSTEM.GET(src, ch); SYSTEM.PUT(dst, ch);
					WHILE hx > 0 DO INC(src); DEC(hx, DW2) END;
					INC(dst); INC(hx, SW2)
				END
			END;
			WHILE hy > 0 DO INC(SY); hy := hy - 2 * DH END;
			INC(DY); hy := hy + 2*SH
		END
	ELSE
		HALT(99)
	END
END Copy;

PROCEDURE PutLine*(B: Bitmap; VAR data: ARRAY OF SIGNED16; X, Y, W: SIGNED16);
VAR dst, src: ADDRESS; i: SIGNED32; ch: CHAR;
BEGIN
	IF (X >= 0) & (X+W <= B.width) & (Y >= 0) & (Y < B.height) & (W <= LEN(data)) THEN
		src := ADDRESSOF(data[0]); dst := B.address + Y*B.wth + X; i := W;
		WHILE i > 0 DO
			SYSTEM.GET(src, ch); SYSTEM.PUT(dst, ch);
			INC(src, 2); INC(dst);
			DEC(i)
		END
	ELSE
		HALT(99)
	END
END PutLine;

PROCEDURE GetLine*(B: Bitmap; VAR data: ARRAY OF SIGNED16; X, Y, W: SIGNED16);
VAR dst, src: ADDRESS; i: SIGNED32; ch: CHAR;
BEGIN
	IF (X >= 0) & (X+W <= B.width) & (Y >= 0) & (Y < B.height) & (W <= LEN(data)) THEN
		dst := ADDRESSOF(data[0]); src := B.address + Y*B.wth + X; i := W;
		WHILE i > 0 DO
			SYSTEM.GET(src, ch); SYSTEM.PUT(dst, ORD(ch));
			INC(src); INC(dst, 2);
			DEC(i)
		END
	ELSE
		HALT(99)
	END
END GetLine;

BEGIN
	NEW(buffer)
END Bitmaps.
