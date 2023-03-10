MODULE WMOTFonts;	(** AUTHO "PL"; PURPOSE "OpenType Support" *)

IMPORT
	KernelLog, WMGraphics, Raster, WMFontManager, Strings, WMRectangles,
	Files, OpenType, OpenTypeInt, OpenTypeScan;

CONST
	ScreenDPI = 71;
	Debug = FALSE;

TYPE
	Char32 = WMGraphics.Char32;
	Glyph*  = RECORD
		img- : WMGraphics.Image;
		code- : Char32; 										(* import only *)
		dx, x, y, w, h : SIGNED32;
	END;
	GlyphArray* = POINTER TO ARRAY OF Glyph;

	GlyphRange* = RECORD
		firstCode-, lastCode- : Char32;							 (* inclusive *)
		glyphs- : GlyphArray;
		loaded- : BOOLEAN;
	END;
	GlyphRangeArray* = POINTER TO ARRAY OF GlyphRange;


TYPE
	RasterData = RECORD (OpenType.RasterData)
		cache-: POINTER TO ARRAY OF ARRAY OF CHAR;
	END;

	PROCEDURE FillRect*(llx, lly, urx, ury, opacity: SIGNED16; VAR data: OpenType.RasterData0);
	VAR x,y: SIGNED32;
	BEGIN
		WITH data: RasterData DO
			FOR y := lly TO ury-1 DO
				FOR x := llx TO urx-1 DO
					IF (y < LEN(data.cache)) & (x < LEN(data.cache[0])) THEN
						IF CHR(opacity) > data.cache[y,x] THEN
							data.cache[y,x] := CHR(opacity);
						END;
					END;
				END;
			END;
		END;
	END FillRect;

TYPE
	Font*  = OBJECT(WMGraphics.Font)
	VAR nofGlyphs- : SIGNED32;
		nofGlyphRanges- : SIGNED32;
		glyphRanges : GlyphRangeArray;
		placeholderimg : WMGraphics.Image;
		fontFile : Files.File;
		empty : WMRectangles.Rectangle;
		fname-, subfam- : ARRAY 256 OF CHAR;
		ofont : OpenType.Font;
		inst: OpenType.Instance;
		glyph : OpenType.Glyph;

		cache-: POINTER TO ARRAY OF ARRAY OF CHAR;

		ras: OpenTypeScan.Rasterizer;

		PROCEDURE &Init*;
		VAR mode : Raster.Mode; pix : Raster.Pixel;
		BEGIN
			Init^;
			isScalable := TRUE;
			nofGlyphRanges := 0;
			empty := WMRectangles.MakeRect(0, 0, 0, 0);		(* save the proc call *)
			NEW(placeholderimg); Raster.Create(placeholderimg, 16, 16, Raster.A1);
			Raster.InitMode(mode, Raster.srcCopy);
			Raster.SetRGBA(pix, 255, 0, 0, 0);
			Raster.Fill(placeholderimg, 0, 0, 15, 15, pix, mode);
			ascent := 16; descent := 5;
		END Init;

		(* support the oberon encoding scheme *)
		PROCEDURE MapCode(VAR code : Char32);
		BEGIN
			IF (code >= 126) & (code <= 155) THEN code := OpenType.CharToUnicode[code] END;
		END MapCode;

		PROCEDURE GetGlyphMap*(code : Char32; VAR map : WMGraphics.Image);
		VAR g : Glyph; range : SIZE;
		BEGIN
			IF FindGlyphRange(code, range) THEN
				IF FindGlyph(code, g) THEN
					map := g.img
				ELSE map := placeholderimg
				END
			ELSE map := placeholderimg
			END
		END GetGlyphMap;

		PROCEDURE HasChar*(code : Char32) : BOOLEAN;
		VAR dummy : SIZE;
		BEGIN
			RETURN FindGlyphRange(code, dummy)
		END HasChar;

		PROCEDURE GetGlyphSpacings*(code : Char32; VAR glyphSpacings : WMGraphics.GlyphSpacings);
		VAR g : Glyph; range : SIZE;
		BEGIN
			IF FindGlyphRange(code, range) THEN
				IF FindGlyph(code, g) THEN
					glyphSpacings.width := g.w;
					glyphSpacings.ascent := ascent; glyphSpacings.descent := descent;
					glyphSpacings.bearing.l := g.x;
					glyphSpacings.bearing.r := g.dx - (g.w + g.x);

					glyphSpacings.height := g.h;
					glyphSpacings.dy := ascent - g.h - g.y
				ELSE glyphSpacings.width := 5; glyphSpacings.height := 15; glyphSpacings.ascent := 16;
				END
			ELSE
				KernelLog.String("code= "); KernelLog.Int(code, 0); KernelLog.String("out of range"); KernelLog.Ln;
			glyphSpacings.width := 5; glyphSpacings.height := 15; glyphSpacings.ascent := 16;
			END
		END GetGlyphSpacings;


		PROCEDURE LoadGlyphRange(gri : SIZE);
		VAR i: Char32;
		BEGIN
			IF glyphRanges[gri].glyphs = NIL THEN
				NEW(glyphRanges[gri].glyphs, glyphRanges[gri].lastCode - glyphRanges[gri].firstCode + 1);
				FOR i := glyphRanges[gri].firstCode TO glyphRanges[gri].lastCode DO
					glyphRanges[gri].glyphs[i - glyphRanges[gri].firstCode].code := -1;
				END;
			END;

			(* epxeriment *)
			glyphRanges[gri].loaded := TRUE;
			RETURN;


				FOR i := glyphRanges[gri].firstCode TO glyphRanges[gri].lastCode DO
					ReadGlyph(i, glyphRanges[gri].glyphs[i - glyphRanges[gri].firstCode])
				END;
				glyphRanges[gri].loaded := TRUE;
		END LoadGlyphRange;

		PROCEDURE FindGlyphRange(code : Char32; VAR gri : SIZE) : BOOLEAN;
		VAR a, b, m : SIZE;
		BEGIN
			gri := 0;
			a := 0; b := LEN(glyphRanges)- 1;
			WHILE (a < b) DO m := (a + b) DIV 2;
				IF glyphRanges[m].lastCode < code THEN a := m + 1
				ELSE b := m
				END
			END;
			IF (glyphRanges[a].firstCode <= code) & (glyphRanges[a].lastCode >= code) THEN
				IF ~glyphRanges[a].loaded THEN LoadGlyphRange(a) END;
				gri := a; RETURN TRUE
			ELSE RETURN FALSE
			END
		END FindGlyphRange;

		PROCEDURE FindGlyph(code : Char32; VAR glyph : Glyph) : BOOLEAN;
		VAR gri : SIZE;
		BEGIN
			IF FindGlyphRange(code, gri) THEN
				IF glyphRanges[gri].glyphs[code - glyphRanges[gri].firstCode].code # code THEN
					ReadGlyph(code, glyphRanges[gri].glyphs[code - glyphRanges[gri].firstCode])
				END;
				glyph := glyphRanges[gri].glyphs[code - glyphRanges[gri].firstCode];
				RETURN TRUE
			ELSE RETURN FALSE
			END
		END FindGlyph;

		PROCEDURE CountGlyphes():SIGNED32;
		VAR i : SIGNED32; c : Char32;
		BEGIN
			FOR i := 0 TO nofGlyphRanges - 1 DO
				c := c + glyphRanges[i].lastCode - glyphRanges[i].firstCode + 1;
			END;
			RETURN c(SIGNED32)
		END CountGlyphes;

		PROCEDURE ReadGlyph(code : Char32; VAR g : Glyph);
		VAR no, dw, dh, y, x: SIGNED32; mode: Raster.Mode; data: RasterData;
		BEGIN{EXCLUSIVE}
			Raster.InitMode(mode, Raster.srcCopy);

			no := OpenType.UnicodeToGlyph(ofont, code);
			IF Debug THEN KernelLog.String("Reading Glyph Nr: "); KernelLog.Int(no, 0); KernelLog.String(" Code: u"); KernelLog.Hex(code, 4); KernelLog.Ln END;

			OpenType.LoadGlyph(inst, glyph, ras, no,  {OpenType.Hinted, OpenType.Width , OpenType.Raster, OpenType.Grey});

			g.dx := glyph.awx;													(* advance *)
			g.x := glyph.hbx;													(* horizontal bearing x *)
			g.y := glyph.hby;													(* horizontal bearing y *)
			g.w := glyph.rw;													(* image width *)
			g.h := glyph.rh;													(* image height *)
			g.code := code;

			dh := glyph.rh;
			dw := glyph.rw;

			IF dw*dh # 0 THEN
				IF (cache = NIL) OR (LEN(cache,0) < dh) OR (LEN(cache,1) < dw) THEN
					NEW(cache,dh,dw);
				END;
				data.cache := cache;
				data.rect := FillRect;
				FOR y := 0 TO dh-1 DO
					FOR x := 0 TO dw-1 DO
						cache[y,x] := 0X;
					END;
				END;
				OpenType.EnumRaster(ras, data);
				NEW(g.img);
				Raster.Create(g.img, dw, dh, Raster.A8);

				FOR y := 0 TO dh-1 DO
					Raster.PutPixels(g.img, 0, dh - y -1, dw, Raster.A8, cache[y], 0, mode);
				END;

				OpenTypeScan.DisposeRasterizer(ras);
			END;
		END ReadGlyph;

		PROCEDURE Load(filename : ARRAY OF CHAR; size : SIZE) : BOOLEAN;
		VAR i, j, k, ngri, splitCount : SIGNED32; res : SIGNED16;
			ascent, descent : SIGNED32;
		BEGIN

			fontFile := Files.Old(filename);															(* open file *)
			IF fontFile = NIL THEN RETURN FALSE END;
			ofont := OpenType.Open(filename);														(* read file *)
			IF ofont = NIL THEN KernelLog.String("OT: Could not open Font: "); KernelLog.String(filename); KernelLog.Ln; RETURN FALSE END;

			NEW(glyph);
			OpenType.InitGlyph(glyph, ofont);
			res := ScreenDPI;
			OpenType.GetInstance(ofont, (40H*size)(OpenType.F26D6), res, res, OpenType.Identity, inst);					(* get instance *)
			IF inst = NIL THEN KernelLog.String("OT: Could not get Instance: "); KernelLog.String(filename);  KernelLog.Ln; RETURN FALSE END;

			OpenType.GetName(ofont, 1, fname);													(* get Name *)
			OpenType.GetName(ofont, 2, subfam);													(* get SubFamily *)

			nofGlyphs := glyph.font.maxp.numGlyphs;													(* number of glyphs *)
			nofGlyphRanges := 0; (*ofont.cmap.segCount;*)											(* number of ranges *)

			(* split into ranges of max size 256 *)
			ngri := ofont.cmap.segCount;
			FOR i := 0 TO ngri - 1 DO
				IF (ofont.cmap.seg[i].end # 0) THEN
					INC(nofGlyphRanges, 1 + ((ofont.cmap.seg[i].end - ofont.cmap.seg[i].start) MOD 10000H) DIV 100H)
				END
			END;

			NEW(glyphRanges, nofGlyphRanges); i := 0; k := 0;
			IF Debug  THEN KernelLog.String("-- Building Ranges: "); KernelLog.Int(nofGlyphRanges, 0); KernelLog.Ln END;
			WHILE k < ngri DO
				IF ofont.cmap.seg[k].end # 0 THEN
					splitCount := ((ofont.cmap.seg[k].end - ofont.cmap.seg[k].start) MOD 10000H) DIV 100H; j := 0;
					WHILE j < splitCount DO
						glyphRanges[i+j].firstCode := (ofont.cmap.seg[k].start MOD 10000H) + 100H*j; glyphRanges[i+j].lastCode := (ofont.cmap.seg[k].start MOD 10000H) + 100H*(j+1) - 1;
						IF Debug THEN KernelLog.String("  SRange: "); KernelLog.Int(i+j, 0); KernelLog.String("  Start: "); KernelLog.Int(glyphRanges[i+j].firstCode, 0); KernelLog.String("  End: "); KernelLog.Int(glyphRanges[i+j].lastCode, 0); KernelLog.Ln END;
						INC(j);
					END;
					glyphRanges[i+j].firstCode := (ofont.cmap.seg[k].start MOD 10000H) + 100H*splitCount ; glyphRanges[i+j].lastCode := ofont.cmap.seg[k].end MOD 10000H;
					IF Debug THEN KernelLog.String("  Range: "); KernelLog.Int(i+j, 0); KernelLog.String("  Start: "); KernelLog.Int(glyphRanges[i+j].firstCode, 0); KernelLog.String("  End: "); KernelLog.Int(glyphRanges[i+j].lastCode, 0); KernelLog.Ln END;
					INC(i, splitCount+1);
				END;
				INC(k)
			END;

(*			height := inst.font.hhea.ascender + inst.font.hhea.descender + inst.font.hhea.lineGap;
			SELF.height := SHORT(OpenTypeInt.MulDiv(height, inst.yppm, 40H*LONG(inst.font.head.unitsPerEm)));		(* height *)
*)
			ascent := inst.font.hhea.ascender;
			SELF.ascent := SHORT(OpenTypeInt.MulDiv(ascent, inst.yppm, 40H*LONG(inst.font.head.unitsPerEm)));		(* ascent *)
			descent := inst.font.hhea.descender;
			SELF.descent := -SHORT(OpenTypeInt.MulDiv(descent, inst.yppm, 40H*LONG(inst.font.head.unitsPerEm)));	(* descent *)

			RETURN TRUE
		END Load;

	END Font;

(* ------------------------------------------------- *)

VAR bit: ARRAY 100H, 8 OF BOOLEAN;					(* Bit[b, i] means bit i in byte b is set *)

PROCEDURE InitBitTable;
VAR b, i: SIGNED32;
BEGIN
	FOR b := 0 TO 0FFH DO
		FOR i := 0 TO 7 DO
			bit[b, i] := ODD(ASH(b, -i))
		END
	END
END InitBitTable;

PROCEDURE LoadFont(name : ARRAY OF CHAR; size : SIZE) : Font;
VAR font: Font;
BEGIN
	IF Debug THEN KernelLog.String("Loading Font: "); KernelLog.String(name); KernelLog.Ln END;
	NEW(font); IF ~font.Load(name, size) THEN RETURN NIL END;
	RETURN font
END LoadFont;

PROCEDURE LoadExactFont*(fi : WMFontManager.FontInfo) : WMGraphics.Font;
VAR exactName : ARRAY 256 OF CHAR; f : WMGraphics.Font; try: SIGNED32;
BEGIN
	try := 0;
	LOOP
		COPY(fi.name^, exactName);

		(* possible suffixes
			bold:  b, B, bd, Bd, _bd, -Bold
			italic: i, I, _i, -Italic
			bold+italic: bi, BI, _bi, -BoldItalic
		*)
		IF WMGraphics.FontBold IN fi.style THEN
			IF WMGraphics.FontItalic IN fi.style THEN
				CASE try OF
				|0: Strings.Append(exactName, "bi");
				|1: Strings.Append(exactName, "-BoldItalic");
				|2: Strings.Append(exactName, "_bi");
				|3: Strings.Append(exactName, "BI");
				|4: Strings.Append(exactName, "-BoldOblique");
				ELSE EXIT
				END
			ELSE
				CASE try OF
				|0: Strings.Append(exactName, "b");
				|1: Strings.Append(exactName, "-Bold");
				|2: Strings.Append(exactName, "bd");
				|3: Strings.Append(exactName, "_bd");
				|4: Strings.Append(exactName, "B");
				|5: Strings.Append(exactName, "Bd");
				ELSE EXIT
				END
			END;
		ELSIF WMGraphics.FontItalic IN fi.style THEN
				CASE try OF
				|0: Strings.Append(exactName, "i");
				|1: Strings.Append(exactName, "-Italic");
				|2: Strings.Append(exactName, "_i");
				|3: Strings.Append(exactName, "I");
				|4: Strings.Append(exactName, "-Oblique");
				ELSE
					EXIT
				END;
		ELSE
			CASE try OF
				0:;
				|1: Strings.Append(exactName, "-Regular");
			ELSE
				EXIT;
			END;
		END;

		Strings.Append(exactName, ".ttf");
		f := LoadFont(exactName, fi.size);
		IF f # NIL THEN EXIT END;

		INC( try )
	END;
	IF f # NIL THEN
		COPY(fi.name^, f.name);
		f.size := fi.size;
		f.style := fi.style;
	END;
	RETURN f
END LoadExactFont;


PROCEDURE LoadApproximateFont*(fi : WMFontManager.FontInfo) : WMGraphics.Font;
VAR exactName : ARRAY 256 OF CHAR; f : WMGraphics.Font;
BEGIN
	COPY(fi.name^, exactName);
	Strings.Append(exactName, ".ttf");
	f := LoadFont(exactName, fi.size);
	IF f # NIL THEN
		COPY(fi.name^, f.name);
		f.size := fi.size;
		f.style := fi.style
	END;
	RETURN f
END LoadApproximateFont;

PROCEDURE MultiTest*;
VAR name : ARRAY 256 OF CHAR; flags : SET; time, date : SIGNED32;
	size: Files.Size;
	enumerator : Files.Enumerator;
	f : WMGraphics.Font;
BEGIN
	NEW(enumerator);
	enumerator.Open("*.ttf", {});
	KernelLog.String("*** TrueType MultiTester v0.1 ***"); KernelLog.Ln;
	WHILE enumerator.HasMoreEntries() DO
		IF enumerator.GetEntry(name, flags, time, date, size) THEN
			KernelLog.String("    Testing File: "); KernelLog.String(name);
			f := LoadFont(name, 40);
			IF f # NIL THEN
				KernelLog.String("            all ok")
			ELSE
				KernelLog.String("            failed")
			END;
			KernelLog.Ln
		END
	END;
	KernelLog.String("*** all done ***"); KernelLog.Ln;
	enumerator.Close;
END MultiTest;

BEGIN
	InitBitTable
END WMOTFonts.


--------------------------------------------

System.Free WMOTFonts~
WMOTFonts.MultiTest~
