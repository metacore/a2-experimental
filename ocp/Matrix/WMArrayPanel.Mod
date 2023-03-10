MODULE WMArrayPanel; (** AUTHOR ""; PURPOSE "Display of 3D and 4D tensors as image"; *)

IMPORT Inputs, XML, MatrixRaster, MatrixUtilities, Files, Streams, WMMessages, Modules, Kernel, 
	WM:=WMWindowManager, WMComponents, WMProperties, WMStandardComponents, WMRectangles, Strings, Models, WMGraphics, Commands, GZip;
CONST
	unsigned=0;
	signed=1;
	lut=2;
	rgb=3;
	heat=4;
	(*display modes*)
	Default*=0;
	SumIntensity*=1;
	MaxIntensity*=2;

(*! to do: improve current limitation to subtensor[0,?] display. Generalize to 1D, 2D and 5D+ data. implement lookup table display*)

TYPE
	Tensor= ARRAY [?] OF FLOAT64;

TYPE Data*= OBJECT (Models.Model)
		VAR m*, r*,g*,b*: Tensor;
		PROCEDURE &Init*;
		BEGIN
			Init^;
			SetGenerator("WMArrayPanel.GenData");
			SetNameAsString(Strings.NewString("TensorData"));
		END Init;
	END Data;
	
TYPE Animator=OBJECT
		VAR p:Panel;
			dead:BOOLEAN;
			timer:Kernel.Timer;
			interval: SIGNED32;
		PROCEDURE &Init(p:Panel; interval: SIGNED32);
		BEGIN
			SELF.p:=p;
			SELF.interval:=interval;
			NEW(timer);
		END Init;
		
		PROCEDURE Die;
		BEGIN{EXCLUSIVE} 
			dead:=TRUE;
			timer.Wakeup;
		END Die;
		
		BEGIN{ACTIVE}
			WHILE ~dead DO 
				p.current:=(p.current+1) MOD LEN(p.data.m, p.orientation.Get());
				p.Render;
				p.Invalidate;
				timer.Sleep(interval);
			END;
		END Animator;
		

TYPE Panel*= OBJECT (WMStandardComponents.ImagePanel) (*! tbd: convert some local variables to properties. move some local variables to model .  tbd: serialization*)
		VAR data*:Data; (*is also in model property*)
		orientation-: WMProperties.Int32Property;
		displayMode-:WMProperties.Int32Property;
		transparency-:WMProperties.BooleanProperty;
		type, cur3:SIGNED32;
		mx0,my0,mx1,my1:SIZE;
		current*,offset*:SIZE;
		max,min, gain*:FLOAT64;
		baseTitle, title: ARRAY 256 OF CHAR;
		img0 : WMGraphics.Image;
		showIndex*:BOOLEAN;
		win*:WM.Window;
		animator: Animator;
		dataStoreSuffix*:ARRAY 7 OF CHAR; (* "MtA" for array storage, "MtZ" or "MtA.gz" for gzipped array storage*)

	PROCEDURE &Init*();
	BEGIN
		Init^;
		SetGenerator("WMArrayPanels.GenPanel");
		NEW(SELF.orientation, NIL, Strings.NewString("orientation"), Strings.NewString("")); properties.Add(SELF.orientation);
		NEW(displayMode, NIL, Strings.NewString("displayMode"), Strings.NewString("default, sum, max")); properties.Add(displayMode);
		SELF.orientation.Set(0);
		NEW(transparency, NIL, Strings.NewString("transparency"), Strings.NewString("transparency")); properties.Add(transparency);
		transparency.Set(FALSE);
		NEW(img0);
		NEW(data);
	 	model.Set(data); model.Changed;
		COPY(title,baseTitle);
		(*dataStoreSuffix:="MtA";*)
		dataStoreSuffix:="MtZ";
		id.Set(Strings.NewString(title));
		current:=0;
		RecacheProperties;
	END Init;

	PROCEDURE HandleInternal*(VAR x : WMMessages.Message);
		VAR filename: Files.FileName; f:Files.File; w:Streams.Writer; fw:Files.Writer; dw:GZip.DeflateWriter;
		BEGIN
			IF (x.msgType = WMMessages.MsgSerialize) & (x.msgSubType = WMMessages.MsgSubSerializeData) THEN
				IF title#"" THEN GenerateName(title, filename)
				ELSE GenerateName(id.Get()^, filename);
				END;
				IF dataStoreSuffix="MtA" THEN
					Strings.Append(filename, ".MtA"); (* file type "MathArray" *)
					w:=fw;
				ELSIF (dataStoreSuffix="MtZ") OR (dataStoreSuffix="MtA.gz") THEN
					Strings.Append(filename,"."); Strings.Append(filename,dataStoreSuffix);
					f:=Files.New(filename);
					Files.OpenWriter(fw,f,0);
					NEW(dw,fw); 
					w:=dw;
				END;
				MatrixUtilities.StoreLR(w, data.m);
				w.Update;
				Files.Register(f);
			ELSE HandleInternal^(x);
			END;
	END HandleInternal;

	PROCEDURE PointerDown*(x, y : SIZE; keys : SET);
		BEGIN
			mx0:=x; my0:=y;
			PointerDown^(x,y,keys);
		END PointerDown;

	PROCEDURE PointerUp*(x, y : SIZE; keys : SET);
		BEGIN
			mx1:=x; my1:=y;
		END PointerUp;

	PROCEDURE PointerMove*(x, y : SIZE; keys : SET);
		BEGIN
			IF keys={2} THEN
				mx1:=x; my1:=y;
				gain:=gain*(1 + (mx1-mx0)/100);
				offset:=offset+(my0-my1);
				mx0:=mx1; my0:=my1;
				model.Set(data);
				model.Changed;
			ELSE
				PointerMove^(x,y,keys)
			END;
		END PointerMove;

	PROCEDURE WheelMove*(dz : SIZE);
	VAR s: ARRAY 16 OF CHAR;
		BEGIN
			IF DIM(data.m)=3 THEN current:=(current - dz) MOD LEN(data.m, orientation.Get()); (*! to do: fix for 3D, 2D, nD*)
			ELSIF DIM(data.m)=4 THEN current:=(current - dz) MOD LEN(data.m, orientation.Get()(*+1*));
			END;
			COPY(baseTitle,title); Strings.Append(title,"-");
			IF DIM(data.m)=4 THEN Strings.IntToStr(cur3 MOD LEN(data.m,0), s); Strings.Append(title, s); Strings.Append(title,"_") END;
			Strings.IntToStr(current,s);
			Strings.Append(title,s);
			id.Set(Strings.NewString(title));
			IF win#NIL THEN win.SetTitle(Strings.NewString(title)) END;
			model.Set(data);
			model.Changed;
		END WheelMove;

	(*The window can determine wether the key was pressed or released by examining the
			Inputs.Release flag in flags. ucs contains the unicode equivalent of the key. Special input editors
			send the generated unicode characters via KeyEvent.  *)
	PROCEDURE KeyEvent*(ucs : SIZE; flags : SET; VAR keysym : SIZE);
		VAR dz: SIGNED32; s: ARRAY 32 OF CHAR; dim:SIZE;
		BEGIN
			IF ~(Inputs.Release IN flags )THEN
				dim:=MAX(DIM(data.m),DIM(data.r));
				IF keysym = Inputs.KsUp THEN
					IF dim=3 THEN dz:=1; current:=(current + dz) MOD LEN(data.m, orientation.Get());
					ELSE INC(cur3)
					END;
				ELSIF keysym = Inputs.KsDown THEN
					IF dim=3 THEN dz:=-1; current:=(current + dz) MOD LEN(data.m, orientation.Get());
					ELSE DEC(cur3);
					END;
				ELSIF keysym = Inputs.KsRight THEN
					orientation.Set((orientation.Get()+1) MOD dim(SIGNED32)); current:=0;
				ELSIF keysym = Inputs.KsLeft THEN
					orientation.Set((orientation.Get()-1) MOD dim(SIGNED32)); current:=0;
				ELSE
					KeyEvent^(ucs,flags,keysym); RETURN
				END;
				COPY(baseTitle,title); Strings.Append(title,"-");
				IF dim=4 THEN Strings.IntToStr(cur3 MOD LEN(data.m,0), s); Strings.Append(title, s); Strings.Append(title,"_") END;
				Strings.IntToStr(current,s);
				Strings.Append(title,s);
				id.Set(Strings.NewString(title));

				model.Set(data);
				model.Changed;
			ELSE
				KeyEvent^(ucs,flags,keysym);
			END;
		END KeyEvent;

	PROCEDURE SetOrientation*(orientation:SIGNED32 );
	BEGIN
		ASSERT(orientation<DIM(data.m),201);
		SELF.orientation.Set(orientation);
	END SetOrientation;

	PROCEDURE SetArray*(CONST m: Tensor; deepCopy:=FALSE:BOOLEAN);
	BEGIN
		ASSERT(DIM(m) IN {2,3,4}, 200);
		IF LEN(m)>0 THEN
			IF deepCopy THEN data.m:=m;
			ELSE data.m:=ALIAS OF m;
			END;
			max:=MAX(m); min:=MIN(m); IF min<0 THEN type:=signed ELSE type:=unsigned END;
			offset:=0;
			IF max#min THEN gain:= 255/MAX( ABS(max),ABS(min));
			ELSE gain:=1;
			END;
			model.Set(data); (*? why are both calls needed to assure correct display ? maybe because the former only sends message if object has changed*)
			model.Changed;
		ELSE type:=unsigned;
		END;
	END SetArray;

	PROCEDURE SetSubArray*(CONST a: Tensor; CONST ranges:ARRAY [*] OF RANGE);
	BEGIN
		ASSERT(DIM(a) IN {2,3,4}, 200);
		IF LEN(a)>0 THEN
			CASE LEN(ranges,0) OF
				 1: data.m[ranges[0]]:=a;
				|2: data.m[ranges[0],ranges[1]]:=a;
				|3: data.m[ranges[0],ranges[1],ranges[2]]:=a;
				|4: data.m[ranges[0],ranges[1],ranges[2],ranges[3]]:=a;
			ELSE HALT(201);
			END;
			max:=MAX(data.m); min:=MIN(data.m); IF min<0 THEN type:=signed ELSE type:=unsigned END;
			offset:=0;
			IF max#min THEN gain:= 255/MAX( ABS(max),ABS(min));
			ELSE gain:=1;
			END;
			model.Set(data); (*? why are both calls needed to assure correct display ? maybe because the former only sends message if object has changed*)
			model.Changed;
		ELSE type:=unsigned;
		END;
	END SetSubArray;


	PROCEDURE SetArrayCustom*(CONST m: Tensor; offset:SIGNED32;gain: FLOAT64);
	BEGIN
		IF LEN(m)>0 THEN
			data.m:=ALIAS OF m;
			max:=MAX(m); min:=MIN(m); IF min<0 THEN type:=signed ELSE type:=unsigned END;
			SELF.offset:=offset; SELF.gain:=gain;
			model.Set(data);
			model.Changed;
		END;
	END SetArrayCustom;

	PROCEDURE SetArrayHeat*(CONST m: Tensor);
	BEGIN
		IF LEN(m)>0 THEN
			data.m:=ALIAS OF m;(* no-copy version *)
			max:=MAX(m); min:=MIN(m);
			type:=heat;
			IF max#min THEN gain:= 511/(max-min);
			ELSE gain:=1;
			END;
			offset:=ENTIER(-255-gain*min);
			model.Set(data);
			model.Changed;
		END;
	END SetArrayHeat;

	PROCEDURE SetArrayRGB*(CONST r,g,b: Tensor); (*? need to assign data.m ?*)
	BEGIN
		IF LEN(r)>0 THEN
			offset:=0; gain:=255/MAX(MAX(ABS(r)), MAX(MAX(ABS(g)), MAX(ABS(b))));
			data.r:=ALIAS OF r; data.g:=ALIAS OF g; data.b:=ALIAS OF b;
			type:=rgb;
			model.Set(data);
			model.Changed;
		END;
	END SetArrayRGB;

	PROCEDURE Render*;
	VAR m,r,g,b: Tensor; orient, w, h: SIZE;
		len: ARRAY [*] OF SIZE;
	BEGIN
		orient:=orientation.Get();

		IF DIM(data.m)=2 THEN
			w:=LEN(data.m,1); h:=LEN(data.m,0);
		ELSIF DIM(data.m)=3 THEN
			IF orient=0 THEN w:=LEN(data.m,2); h:= LEN(data.m,1);
			ELSIF orient=1 THEN w:=LEN(data.m,2); h:= LEN(data.m,0);
			ELSE w:=LEN(data.m,1); h:= LEN(data.m,0);
			END;
		ELSIF DIM(data.m)=4 THEN
			IF orient=0 THEN w:=LEN(data.m,3); h:= LEN(data.m,2);
			ELSIF orient=1 THEN w:=LEN(data.m,3); h:= LEN(data.m,1);
			ELSE w:=LEN(data.m,2); h:= LEN(data.m,1);
			END;
		ELSE RETURN
		END;

		(* implicit call of Raster.Create in MatrixRaster calls*)
		len:=LEN(data.m);
		IF type=signed THEN
			IF DIM(data.m)=4 THEN m:=ALIAS OF data.m[cur3 MOD LEN(data.m,0),?]
			ELSE m:=ALIAS OF data.m (*only effective in DIM=3*)
			END;
			IF transparency.Get() THEN
				IF DIM(data.m)=2 THEN MatrixRaster.LRealToImageBRA(data.m[*,*], offset, gain, img0);
				ELSIF orient=0 THEN MatrixRaster.LRealToImageBRA(m[current MOD len[0],*,*], offset, gain, img0);
				ELSIF orient=1 THEN MatrixRaster.LRealToImageBRA(m[.., current MOD len[1], ..], offset, gain, img0);
				ELSE MatrixRaster.LRealToImageBRA(m[..,..,current MOD len[2]], offset, gain, img0);
				END;
			ELSE
				IF DIM(data.m)=2 THEN MatrixRaster.LRealToImageBR(data.m[*,*], offset, gain, img0);
				ELSIF orient=0 THEN MatrixRaster.LRealToImageBR(m[current MOD len[0],*,*], offset, gain, img0);
				ELSIF orient=1 THEN MatrixRaster.LRealToImageBR(m[.., current MOD len[1], ..], offset, gain, img0);
				ELSE MatrixRaster.LRealToImageBR(m[..,..,current MOD len[2]], offset, gain, img0);
				END;
			END;
		ELSIF type=heat THEN
			IF DIM(data.m)=4 THEN m:=ALIAS OF data.m[cur3 MOD LEN(data.m,0),?] ELSE m:=ALIAS OF data.m END;
			IF DIM(data.m)=2 THEN MatrixRaster.LRealToImageHeat(data.m[*,*], offset, gain, img0);
			ELSIF orient=0 THEN MatrixRaster.LRealToImageHeat(m[current MOD len[0],*,*], offset, gain, img0);
			ELSIF orient=1 THEN MatrixRaster.LRealToImageHeat(m[.., current MOD len[1], ..], offset, gain, img0);
			ELSE MatrixRaster.LRealToImageHeat(m[..,..,current MOD len[2]], offset, gain, img0);
			END;
		ELSIF type=rgb THEN
			IF DIM(data.r)=4 THEN
				r:=ALIAS OF data.r[cur3 MOD LEN(data.r,0),?];
				g:=ALIAS OF data.g[cur3 MOD LEN(data.g,0),?];
				b:=ALIAS OF data.b[cur3 MOD LEN(data.b,0),?]
			ELSE r:=ALIAS OF data.r; g:=ALIAS OF data.g; b:=ALIAS OF data.b; (*only effective in DIM=3*)
			END;
			IF DIM(data.r)=2 THEN MatrixRaster.LRealRGBToImageB( data.r[*,*], data.g[*,*], data.b[*,*], offset, gain, img0);
			ELSIF orient=0 THEN MatrixRaster.LRealRGBToImageB( r[current MOD len[0],*,*], g[current MOD len[0],*,*], b[current MOD len[0],*,*], offset, gain, img0);
			ELSIF orient=1 THEN MatrixRaster.LRealRGBToImageB( r[..,current MOD len[1],..], g[..,current MOD len[1],..], b[..,current MOD len[1],..], offset, gain, img0);
			ELSE MatrixRaster.LRealRGBToImageB( r[..,..,current MOD len[2]], g[..,..,current MOD len[2]], b[..,..,current MOD len[2]], offset, gain, img0);
			END;
		ELSIF LEN(data.m,0)>0 THEN
			IF DIM(data.m)=4 THEN m:=ALIAS OF data.m[cur3 MOD LEN(data.m,0),?] ELSE m:=ALIAS OF data.m END;
			IF DIM(data.m)=2 THEN MatrixRaster.LRealToImage(data.m[*,*], offset, gain, img0);
			ELSE
				IF displayMode.Get()=Default THEN
					IF orient=0 THEN MatrixRaster.LRealToImage(m[current MOD LEN(m)[0],*,*], offset, gain, img0);
					ELSIF orient=1 THEN MatrixRaster.LRealToImage(m[..,current MOD LEN(m)[1],..], offset, gain, img0);
					ELSE 					MatrixRaster.LRealToImage(m[..,..,current MOD LEN(m)[2]], offset, gain, img0);
					END;
				ELSIF displayMode.Get()=SumIntensity THEN
					IF orient=0 THEN MatrixRaster.LRealToImage(SUM(m,0), offset, gain/LEN(m,0), img0);
					ELSIF orient=1 THEN MatrixRaster.LRealToImage(SUM(m,1) , offset, gain/LEN(m,1), img0);
					ELSE 					MatrixRaster.LRealToImage(SUM(m,2), offset, gain/LEN(m,2), img0);
					END;
				ELSIF displayMode.Get()=MaxIntensity THEN
					IF orient=0 THEN MatrixRaster.LRealToImage(MAX(m,0), offset, gain, img0);
					ELSIF orient=1 THEN MatrixRaster.LRealToImage(MAX(m,1) , offset, gain, img0);
					ELSE 					MatrixRaster.LRealToImage(MAX(m,2), offset, gain, img0);
					END;
				END;
			END;
		ELSE
		END;
	END Render;

	PROCEDURE PropertyChanged*(sender, property : ANY);
		BEGIN
			IF property = model THEN RecacheProperties; (*implicit invalidate in RecacheProperties*)
			ELSIF property=orientation THEN RecacheProperties;
			ELSIF property=displayMode THEN RecacheProperties
			ELSIF property=transparency THEN RecacheProperties
			ELSE	PropertyChanged^(sender, property)
			END
		END PropertyChanged;

		PROCEDURE LinkChanged*(sender, link : ANY); (*TBD: there is reduncancy. ideally, only a LinkChanged message should be n*)
		BEGIN
			IF link = data THEN RecacheProperties;
			ELSE	LinkChanged^(sender, link)
			END
		END LinkChanged;

		PROCEDURE RecacheProperties*;
		BEGIN
			RecacheProperties^;
			Render;
			bounds.SetWidth(img0.width);
			bounds.SetHeight(img0.height);
			SetImage(SELF, img0) (*Implicit invalidate*)
		END RecacheProperties;
		
		PROCEDURE GetImage*():WMGraphics.Image;
		BEGIN
			RETURN img0
		END GetImage;

		PROCEDURE Animate*(interval:SIGNED32);
		BEGIN
			NEW(animator,SELF,interval);
		END Animate;
		
		PROCEDURE StopAnimation*;
		BEGIN
			IF animator#NIL THEN animator.Die; animator:=NIL END;
		END StopAnimation;

	END Panel;

PROCEDURE GenerateName(prefix: ARRAY OF CHAR; VAR str: ARRAY OF CHAR);
VAR  i,j:SIZE; title: Files.FileName; c:CHAR; s:ARRAY 8 OF CHAR;
BEGIN
	i:=0; j:=0;
	WHILE (i<LEN(prefix)) & (j<LEN(title)-1) DO
		c:=prefix[i];
		IF (c>="A")&(c<="Z") OR (c>="a")&(c<="z") OR(c>="0")&(c<="9") OR (c="_") OR (c=" ")THEN
			IF c=" " THEN c:="_" END;
			title[j]:=c; INC(i); INC(j);
		ELSE
			INC(i);
		END;
	END;
	title[j]:=0X;
	IF title="" THEN title:="Matrix" END;
	COPY(title, str);
END GenerateName;

(*OPERATOR "SUM"*(CONST t:Tensor; dim: SIGNED32):Tensor; (*implementation limitation: 3D*)
VAR res: Tensor;i:SIZE;
BEGIN
	IF DIM(t)=2 THEN
		HALT(200);
	ELSIF DIM(t)=3 THEN
		IF dim=0 THEN
			NEW(res, LEN(t)[1..]); FOR i:=0 TO LEN(t,0)-1 DO res:=res+t[i,*,*] END;
		ELSIF dim=1 THEN
			NEW(res, LEN(t,0), LEN(t,2)); FOR i:=0 TO LEN(t,1)-1 DO res:=res+t[*,i,*] END;
		ELSE
			NEW(res, LEN(t)[..1]); FOR i:=0 TO LEN(t,2)-1 DO res:=res+t[*,*,i] END;
		END;
	END;
	RETURN res;
END "SUM";*)

OPERATOR "SUM"*(CONST m:Tensor; dimension:SIGNED8):Tensor; (*! TBD: eliminate allocation of "len"k and of tensor descriptor*)
VAR len:ARRAY[*]OF SIZE; dims,i:SIZE;
BEGIN
	dims:=DIM(m);
	ASSERT(dimension<DIM(m));
	NEW(len, DIM(m)-1);
	FOR i:=0 TO dimension-1 DO			len[i]:=LEN(m,i); 		END;
	FOR i:=dimension TO LEN(len,0)-1 DO	len[i]:=LEN(m,i+1);	END;
	IF LEN(RESULT)#len THEN NEW(RESULT,len) ELSE RESULT:=0 END;
	CASE dimension OF
		|0:IF dims=3 THEN
				FOR i:=0 TO LEN(m,0)-1 DO RESULT:=RESULT+m[i,..,..] 		END;(*?does this allocate descriptor ?*)
			ELSE
				FOR i:=0 TO LEN(m,0)-1 DO RESULT:=RESULT+m[i,?] 		END;(*?does this allocate descriptor ?*)
			END;
		|1:IF dims=3 THEN
				FOR i:=0 TO LEN(m,1)-1 DO RESULT:=RESULT+m[..,i,..] 		END;
			ELSE
				FOR i:=0 TO LEN(m,1)-1 DO RESULT:=RESULT+m[..,i,?] 		END;
			END;
		|2:IF dims=3 THEN
				FOR i:=0 TO LEN(m,2)-1 DO RESULT:=RESULT+m[..,..,i] 	END;
			ELSE 
				FOR i:=0 TO LEN(m,2)-1 DO RESULT:=RESULT+m[..,..,i,?] 	END;
			END;
		|3:FOR i:=0 TO LEN(m,3)-1 DO RESULT:=RESULT+m[..,..,..,i,?] 	END;
		ELSE HALT(200);
	END;
	RETURN RESULT
END "SUM";

OPERATOR "MAX"*(CONST t:Tensor; dim: SIGNED8):Tensor; (*implementation limitation: 3D*)
VAR res: Tensor;a,b: SIZE;
BEGIN
	IF dim=0 THEN
		NEW(res, LEN(t)[1..]);
		FOR a:=0 TO LEN(t,1)-1 DO
			FOR b:=0 TO LEN(t,2)-1 DO
				res[a,b]:=MAX(t[*,a,b])
			END;
		END;
	ELSIF dim=1 THEN
		NEW(res, LEN(t,0), LEN(t,2));
		FOR a:=0 TO LEN(t,0)-1 DO
			FOR b:=0 TO LEN(t,2)-1 DO
				res[a,b]:=MAX(t[a,*,b])
			END;
		END;
	ELSE
		NEW(res, LEN(t)[..1]);
		FOR a:=0 TO LEN(t,0)-1 DO
			FOR b:=0 TO LEN(t,1)-1 DO
				res[a,b]:=MAX(t[a,b,*])
			END;
		END;
	END;
	RETURN res;
END "MAX";

PROCEDURE GenPanel*() : XML.Element;
VAR
	p : Panel;
BEGIN
	NEW(p);
	RETURN p
END GenPanel;

PROCEDURE GenData*() : XML.Element;
VAR d : Data;
BEGIN NEW(d); RETURN d
END GenData;

PROCEDURE GetPanel*(CONST tensor: ARRAY [?] OF FLOAT64; deepCopy:=FALSE:BOOLEAN): Panel;
VAR	panel:Panel; 
BEGIN
	NEW(panel);
	panel.SetArray(tensor, deepCopy);
	panel.SetOrientation(0);
	IF (DIM(tensor)>1) & (LEN(tensor)>0) THEN 
		panel.bounds.Set(WMRectangles.MakeRect(0,0,LEN(tensor)[DIM(tensor)-1],LEN(tensor)[DIM(tensor)-2]))
	ELSE
		 panel.bounds.Set(WMRectangles.MakeRect(0,0,400,400));
	END;
	RETURN panel
END GetPanel;

(*

PROCEDURE AddWindow*(CONST tensor: ARRAY [?] OF FLOAT64; CONST title: ARRAY OF CHAR);
VAR window:WMComponents.FormWindow; w,h:SIGNED32;
	panel:Panel;
BEGIN
	NEW(panel);
	panel.SetArray(tensor);
	panel.SetOrientation(0);
	IF DIM(tensor)>1 THEN w:=LEN(tensor)[DIM(tensor)-1]; h:=LEN(tensor)[DIM(tensor)-2];
	ELSE w:=400; h:=400;
	END;
	NEW(window, w, h, FALSE);
	window.SetTitle(Strings.NewString(title));
	INCL(window.flags, WM.FlagStorable); (* allow storing of data interactively, through right-click on navigator icon*)
	WM.DefaultAddWindow(window);
	window.SetContent(panel);
	window.form.fillColor.Set(008888FFH);(*background*)
END AddWindow;
*)

PROCEDURE CreateWindow*(panel:Panel; CONST title: ARRAY OF CHAR): WMComponents.FormWindow;
(*PROCEDURE CreateWindow*(panel:WMStandardComponents.Panel; CONST title: ARRAY OF CHAR): WMComponents.FormWindow;*)
VAR window:WMComponents.FormWindow;bounds: WMRectangles.Rectangle;
	w,h:SIZE;
BEGIN
	bounds:=panel.bounds.Get();
	w:=bounds.r-bounds.l; h:=bounds.b-bounds.t; ASSERT(h>0);
	NEW(window, SIGNED32(w), SIGNED32(h), TRUE);
	IF panel IS Panel THEN panel(Panel).win:=window END;
	window.SetTitle(Strings.NewString(title));
	INCL(window.flags, WM.FlagStorable); (* allow storing of data interactively, through right-click on navigator icon*)
	panel.alignment.Set(WMComponents.AlignClient);
	IF panel IS Panel THEN COPY(title, panel(Panel).title); COPY(title, panel(Panel).baseTitle) END;
	window.SetContent(panel);
	(*window.form.fillColor.Set(008888FFH);*)(*background*)
	window.form.fillColor.Set(0);(*background*)
	RETURN window;
END CreateWindow;

PROCEDURE AddWindow*(CONST tensor: ARRAY [?] OF FLOAT64; CONST title: ARRAY OF CHAR; deepCopy:=FALSE:BOOLEAN);
VAR window:WMComponents.FormWindow;
	w,h:SIZE;
	panel:Panel;
BEGIN
	IF DIM(tensor)>1 THEN w:=LEN(tensor)[DIM(tensor)-1]; h:=LEN(tensor)[DIM(tensor)-2];
	ELSE w:=400; h:=400;
	END;
	panel:=GetPanel(tensor, deepCopy);
	window:=CreateWindow(panel,title);
	WM.DefaultAddWindow(window);
END AddWindow;

PROCEDURE Cleanup;
VAR manager:WM.WindowManager; w,remove:WM.Window;
BEGIN {EXCLUSIVE}
	manager:=WM.GetDefaultManager();
	manager.lock.AcquireWrite;
	w:=manager.GetFirst();
	WHILE (w#NIL) DO
		remove:=w;
		w:=manager.GetNext(w);
		IF (remove#NIL)&(remove IS WMComponents.FormWindow)&(remove(WMComponents.FormWindow).form.GetFirst() IS Panel) THEN
			IF remove(WMComponents.FormWindow).form.GetFirst()(Panel).animator#NIL THEN 
				remove(WMComponents.FormWindow).form.GetFirst()(Panel).animator.Die;
			END;
		END;
	END;
	w:=manager.GetFirst();
	WHILE (w#NIL) DO
		remove:=w;
		w:=manager.GetNext(w);
		IF (remove#NIL)&(remove IS WMComponents.FormWindow)&(remove(WMComponents.FormWindow).form.GetFirst() IS Panel) THEN
			manager.Remove(remove); 
		END;
	END;
	manager.lock.ReleaseWrite;
END Cleanup;


PROCEDURE  Test*(context:Commands.Context); (*deprecated -  will be eliminated from source*)
VAR window:WMComponents.FormWindow;
	panel:Panel;
	tensor: ARRAY [?] OF FLOAT64; (* or FLOAT64 or other..*)
BEGIN
	log:=context.out;
	(*have some data in a 3D array ready*)
	NEW(tensor,50,100,120);
	tensor[.. ,10..80 BY 2,..]:=1;
	tensor[10..25 BY 2,..,..]:=2;
	tensor[..,..,10..30 BY 2]:=3;
	tensor[..,..,60..100 BY 4]:=4;

	(*show data as mouse or arrow key scrollable window*)
	NEW(panel);
	panel.SetArray(tensor);
	panel.SetOrientation(0);
	NEW(window, 400,400, TRUE);
	window.SetTitle(Strings.NewString("tensor window"));
	INCL(window.flags, WM.FlagStorable); (* allow storing of data interactively, through right-click on navigator icon*)
	panel.alignment.Set(WMComponents.AlignClient);
	window.SetContent(panel);
	window.form.fillColor.Set(0);(*background*)
	(*window.form.fillColor.Set(008888FFH);*)(*background*)
	WM.DefaultAddWindow(window);
	panel.Animate(200);
	(*LOOP
		panel.SetSubArray(MatrixUtilities.Random([6,100,120],MatrixUtilities.Uniform), [10..15,..,..]);
	END;*)
END Test;

VAR log:Streams.Writer;

BEGIN
	Modules.InstallTermHandler(Cleanup);
END WMArrayPanel.

WMArrayPanel.Test~

System.FreeDownTo WMArrayPanel~

System.FreeDownTo MatrixUtilities ~

