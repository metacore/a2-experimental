MODULE WMBackdropLoader;	(** AUTHOR "ug"; December 1, 2005 *)

IMPORT
	WMComponents, WMStandardComponents, Strings,
	Commands, Modules, KernelLog, Looks, Files,
	WM := WMWindowManager;

CONST
	Toleft = 300;
	Fromtop = 400;
	PanelWidth = 100;
	ButtonHeight = 20;

TYPE
	Window=OBJECT (WMComponents.FormWindow);
	VAR
		nofLooks : SIGNED32;
		nextINchain : Window;
		buttonArr : POINTER TO ARRAY OF WMStandardComponents.Button;
		lookList : Looks.LookList;

		PROCEDURE &New *(lookList : Looks.LookList);
		VAR
			panel : WMStandardComponents.Panel;
			i : SIGNED32;
			look : Looks.Look;
		BEGIN
			ASSERT((lookList # NIL) & (lookList.GetCount() > 0));
			SELF.lookList := lookList;
			nofLooks := lookList.GetCount ();
			NEW (panel);
			panel.bounds.SetWidth (PanelWidth);
			panel.bounds.SetHeight (nofLooks * ButtonHeight);

			NEW(buttonArr, nofLooks);
			FOR i := 0 TO nofLooks-1 DO
				NEW(buttonArr[i]);
				look := lookList.GetItem (i);
				buttonArr[i].caption.SetAOC(look.name); buttonArr[i].alignment.Set(WMComponents.AlignTop);
				buttonArr[i].bounds.SetWidth(PanelWidth); buttonArr[i].bounds.SetHeight(ButtonHeight);
				buttonArr[i].onClick.Add(LoadSkin);
				panel.AddContent(buttonArr[i]);
			END;

			Init (panel.bounds.GetWidth (), panel.bounds.GetHeight (), TRUE);
			SetContent (panel);

			WM.AddWindow (SELF, Toleft, Fromtop);
			manager := WM.GetDefaultManager();
			manager.SetFocus(SELF);
			SetTitle (Strings.NewString ("Backdrops"));

			nextINchain := windows;
			windows := SELF
		END New;

		PROCEDURE FindSender(sender : WMStandardComponents.Button; VAR index : SIGNED32);
		VAR i : SIGNED32;
		BEGIN
			i := 0;
			WHILE (i < nofLooks) & (buttonArr[i] # sender) DO INC(i) END;
			IF i < nofLooks THEN index := i ELSE index := -1 END
		END FindSender;

		PROCEDURE LoadSkin(sender, data : ANY);
		VAR look : Looks.Look;
			cmd, s, msg : ARRAY 128 OF CHAR;
			index : SIGNED32; res : INTEGER;
		BEGIN
			IF sender IS WMStandardComponents.Button THEN
				FindSender(sender(WMStandardComponents.Button), index);
				IF index >= 0 THEN
					look := lookList.GetItem(index);
					Strings.Concat("WMBackdrop.AddBackdropImage ", look.file, s);
					Strings.Concat(s, " ? ? ? ?", cmd);
					Commands.Call(cmd, {}, res, msg);
					IF res # 0 THEN KernelLog.Enter; KernelLog.String(msg); KernelLog.Exit END
				END
			END
		END LoadSkin;

		PROCEDURE Close*;
		BEGIN
			Close^;
			FreeWindow (SELF)
		END Close;

	END Window;

VAR
	windows : Window;

PROCEDURE FreeWindow(free : Window);
VAR
	winstance : Window;
BEGIN
	IF free = windows THEN
		windows := windows.nextINchain
	ELSE
		winstance := windows;
		WHILE (winstance # NIL) & (winstance.next # free) DO
			winstance := winstance.nextINchain
		END;
		IF winstance # NIL THEN
			winstance.nextINchain := free.nextINchain
		END
	END
END FreeWindow;

PROCEDURE Open* (context : Commands.Context);
VAR winstance : Window; filename : Files.FileName; lookList : Looks.LookList;
BEGIN
	context.arg.SkipWhitespace; context.arg.String(filename);
	Looks.LoadLooks(filename, lookList);
	IF (lookList.GetCount() > 0) THEN
		NEW (winstance, lookList);
	ELSE
		context.out.String("WMBackdropLoader: No backdrops found in file '");
		context.out.String(filename); context.out.String("'");
		context.out.Ln;
	END;
END Open;

PROCEDURE Cleanup;
BEGIN
	WHILE windows # NIL DO
		windows.Close ();
	END
END Cleanup;

BEGIN
	Modules.InstallTermHandler (Cleanup)
END WMBackdropLoader.

System.Free WMBackdropLoader Looks ~
WMBackdropLoader.Open BackdropList.XML ~


