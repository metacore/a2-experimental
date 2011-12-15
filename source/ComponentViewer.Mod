MODULE ComponentViewer;	(** AUTHOR "TF"; PURPOSE "Testbed for the component system"; *)

IMPORT
	Modules, Commands, Options, XML, Repositories, WMMessages, WMGraphics, WMWindowManager, WMComponents, WMRestorable, D:= Debugging, Files;

CONST
	DefaultWidth = 320;
	DefaultHeight = 240;

TYPE

	KillerMsg = OBJECT
	END KillerMsg;

	Window = OBJECT(WMComponents.FormWindow)

		PROCEDURE RestoreWindow*(c : WMRestorable.Context);
		VAR vc : WMComponents.VisualComponent;
		BEGIN
			ReInit(c.r-c.l, c.b-c.t);
			(*
			Init(c.r - c.l, c.b - c.t, FALSE);
			*)
			IF c.appData # NIL THEN
				DisableUpdate;
				LoadComponents(c.appData(XML.Element));
				EnableUpdate;
			END;
			WMRestorable.AddByContext(SELF, c);
			Resized(c.r-c.l,c.b-c.t);
		END RestoreWindow;

		PROCEDURE &InitWindow(width, height : LONGINT; alpha : BOOLEAN);
		BEGIN
			IncCount;
			Init(width, height, alpha);
		END InitWindow;

		PROCEDURE Close;
		BEGIN
			Close^;
			DecCount
		END Close;

		PROCEDURE Handle(VAR m : WMMessages.Message);
		VAR data: XML.Element;
		BEGIN
			IF (m.msgType = WMMessages.MsgExt) & (m.ext # NIL) THEN
				IF  (m.ext IS KillerMsg) THEN Close
				ELSIF (m.ext IS WMRestorable.Storage) THEN
					data := StoreComponents();
					m.ext(WMRestorable.Storage).Add("ComponentViewer", "ComponentViewer.Restore", SELF, data)
				ELSE Handle^(m);
				END;
			ELSE Handle^(m);
			END;
		END Handle;

	END Window;

VAR
	nofWindows : LONGINT;

PROCEDURE Open*(context : Commands.Context); (** [Options] <RepositoryName:ComponentName:ID> | <ModuleName.ProcedureName> | <Filename> ~ *)
VAR
	options : Options.Options;
	filename, repositoryName, componentName : ARRAY 128 OF CHAR;
	window : Window;
	moduleName, procedureName : Modules.Name;
	ignoreMsg : ARRAY 1 OF CHAR;
	generatorProc : XML.GeneratorProcedure;
	c : XML.Content; component : Repositories.Component; string : XML.String;
	vc : WMComponents.VisualComponent;
	width, height, id, res : LONGINT;
	fx,fy,fw,fh,x,y: LONGINT;
	viewPort: WMWindowManager.ViewPort;
	manager: WMWindowManager.WindowManager;
BEGIN
	NEW(options);
	options.Add("h", "height", Options.Integer);
	options.Add("w", "width", Options.Integer);
	options.Add("c", "client", Options.Flag);
	options.Add("a","alpha", Options.Flag);
	options.Add("f","fullscreen", Options.Flag);
	IF options.Parse(context.arg, context.error) & context.arg.GetString(filename) THEN
		IF Repositories.SplitName(filename, repositoryName, componentName, id) & (repositoryName # "") THEN
			(* Retrieve component from repository *)
			Repositories.GetComponentByString(filename, component, res);
			IF (res = Repositories.Ok) THEN
				c := component;
			ELSE
				context.error.String("Could not load "); context.error.String(filename);
				context.error.String(" from repository, res: "); context.error.Int(res, 0); context.error.Ln;
			END;
		ELSE
			Commands.Split(filename, moduleName, procedureName, res, ignoreMsg);
			IF (res = Commands.Ok) THEN
				(* Assume argument is a generator procedure *)
				GETPROCEDURE(moduleName, procedureName, generatorProc);
				IF (generatorProc # NIL) THEN
					c := generatorProc();
				ELSE
					(* Maybe argument is a filename *)
					c := WMComponents.Load(filename);
				END;
			ELSE
				(* Load component from XML file *)
				c := WMComponents.Load(filename);
			END;
		END;
		IF (c # NIL) & (c IS WMComponents.VisualComponent) THEN
			vc := c (WMComponents.VisualComponent);
			IF options.GetInteger("width", width) THEN
				vc.bounds.SetWidth(width);
			ELSE
				width := vc.bounds.GetWidth();
				IF (width <= 0) THEN width := DefaultWidth; END;
			END;
			IF options.GetInteger("height", height) THEN
				vc.bounds.SetHeight(height);
			ELSE
				height := vc.bounds.GetHeight();
				IF (height <= 0) THEN height := DefaultHeight; END;
			END;
			IF options.GetFlag("client") THEN
				vc.alignment.Set(WMComponents.AlignClient);
			END;
			IF options.GetFlag("fullscreen") THEN
				viewPort := WMWindowManager.GetDefaultView();
				fx := -1; fy := 0; fw := 1; fh := 1; (* full screen on screen number 4 *)
				x := fx * viewPort.width0;
				y := fy * viewPort.height0;
				width := fw* viewPort.width0;
				height := fh * viewPort.height0;
			END;
			NEW(window, width, height, options.GetFlag("alpha"));
			window.SetTitle(vc.GetName());
			window.SetContent(c);
			IF options.GetFlag("fullscreen") THEN
				manager := WMWindowManager.GetDefaultManager();
				manager.Add(x, y, window, {WMWindowManager.FlagStayOnTop});
			ELSE
				WMWindowManager.DefaultAddWindow(window);
			END;
		ELSE
			IF (c = NIL) THEN context.error.String("Could not load/generate component "); context.error.String(filename);
			ELSE context.error.String(filename); context.error.String(" is not a VisualComponent.");
			END;
			context.error.Ln;
		END;
	ELSE
		context.error.String("Usage: ComponentViewer.Open [Options] <string> ~"); context.error.Ln;
	END;
END Open;

PROCEDURE Store*(context: Commands.Context);
VAR
	filename, name, ext, formName : ARRAY 256 OF CHAR;
	form: WMComponents.Component;
	id,res: LONGINT;
	originator: WMComponents.Component;
	parent: XML.Element;
BEGIN{EXCLUSIVE}
	context.arg.SkipWhitespace; context.arg.String(filename); D.String(filename); D.Ln;

	IF (context # NIL) & (context IS WMComponents.EventContext) THEN
		originator := context(WMComponents.EventContext).originator;
		parent := originator.GetParent();
		WHILE (parent # NIL) & (parent IS WMComponents.Component) & ~(parent IS WMComponents.Form) DO
			originator := parent(WMComponents.Component);
			parent := originator.GetParent();
		END;
	END;
	form := originator;
	(*form := GetForm(current);*)
	IF (form # NIL) & (filename # "") THEN
		Repositories.CreateRepository(filename,res);
		ASSERT(res = Repositories.Ok);
		Files.SplitExtension(filename, name, ext);
		id:= 1;
		COPY(form.GetName()^,formName);
		Repositories.PutComponent(form,name,form.GetName()^,id,res);
		ASSERT(res = Repositories.Ok);
		Repositories.StoreRepository(name,res);
		ASSERT(res = Repositories.Ok);
		Repositories.UnloadRepository(name,res);
		ASSERT(res = Repositories.Ok);
		context.out.String("stored component in repository "); context.out.String(filename); context.out.Ln;
	END;
FINALLY
END Store;


PROCEDURE Restore*(context : WMRestorable.Context);
VAR w : Window;
BEGIN
	IF context # NIL THEN
		NEW(w, 100,100,FALSE);
		w.RestoreWindow(context);
	END;
END Restore;

PROCEDURE IncCount;
BEGIN {EXCLUSIVE}
	INC(nofWindows)
END IncCount;

PROCEDURE DecCount;
BEGIN {EXCLUSIVE}
	DEC(nofWindows)
END DecCount;

PROCEDURE Cleanup;
VAR
	die : KillerMsg;
	msg : WMMessages.Message;
	m : WMWindowManager.WindowManager;
BEGIN {EXCLUSIVE}
	NEW(die);
	msg.ext := die;
	msg.msgType := WMMessages.MsgExt;
	m := WMWindowManager.GetDefaultManager();
	m.Broadcast(msg);
	(*AWAIT(nofWindows = 0)*)
END Cleanup;

BEGIN
	nofWindows := 0;
	Modules.InstallTermHandler(Cleanup)
END ComponentViewer.

SystemTools.Free ComponentViewer ~
ComponentViewer.Open FractalDemo.XML ~

ComponentViewer.Open --width=128 --height=64 --client WMStandardComponents.GenButton ~