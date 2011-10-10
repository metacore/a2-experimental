MODULE WMInspector; (** AUTHOR "staubesv"; PURPOSE "Component inspection"; *)

IMPORT
	Modules, Strings, XMLObjects, Texts,
	WMRectangles, WMGraphics, WMMessages, WMRestorable, WMWindowManager,
	WMComponents, WMStandardComponents, WMTrees, WMTabComponents, WMInspectionComponents, XML, Raster;

CONST
	WindowWidth = 800; WindowHeight = 500;

	(* Maximum number of windows that can be managed by components inside this module *)
	MaxNofWindows = 100;

	Bearing = 2;

TYPE
	Windows = ARRAY MaxNofWindows OF WMWindowManager.Window;

	(** Tree component that displays all window instances and their component hierarchies *)
	InspectionTree* = OBJECT(WMComponents.VisualComponent)
	VAR
		treeView- : WMTrees.TreeView;
		tree- : WMTrees.Tree;

		PROCEDURE &Init;
		BEGIN
			Init^;
			NEW(treeView); treeView.alignment.Set(WMComponents.AlignClient);
			tree := treeView.GetTree();
			(* add treeView in subclass *)
		END Init;

		PROCEDURE AddComponents(component : WMComponents.Component; parent : WMTrees.TreeNode);
		VAR
			node : WMTrees.TreeNode;
			name, string : Strings.String;
			caption : ARRAY 128 OF CHAR;
			enum : XMLObjects.Enumerator;
			p : ANY; i, len : LONGINT;
		BEGIN
			name := component.GetName();
			IF (name # NIL) THEN
				COPY(name^, caption);
			ELSE
				caption := "NoName";
			END;

			IF (component IS WMStandardComponents.Button) THEN
				string := component(WMStandardComponents.Button).caption.Get();
				IF (string # NIL) THEN
					Strings.Append(caption, " (");
					Strings.Append(caption, string^);
					Strings.Append(caption, ")");
				END;
			ELSIF (component IS WMStandardComponents.Label) THEN
				string := component(WMStandardComponents.Label).caption.Get();
				IF (string # NIL) THEN
					Strings.Append(caption, " (");
					IF (Strings.Length(caption) <= 10) THEN
						Strings.Append(caption, string^);
					ELSE
						len := Strings.Length(caption);
						i := 0;
						WHILE (i < 10) & (string[i] # 0X) & (len + i < LEN(caption) - 1) DO
							caption[len + i] := string[i]; INC(i);
						END;
						caption[i] := 0X;
						Strings.Append(caption, "...");
					END;
					Strings.Append(caption, ")");
				END;
			END;

			IF component.internal THEN
				Strings.Append(caption, " [internal]");
			END;

			NEW(node);
			tree.SetNodeCaption(node, Strings.NewString(caption));
			tree.SetNodeData(node, component);
			tree.AddChildNode(parent, node);

			enum := component.GetContents();
			WHILE enum.HasMoreElements() DO
				p := enum.GetNext();
				IF (p IS WMComponents.Component) THEN
					AddComponents(p(WMComponents.Component), node);
				END;
			END;
		END AddComponents;

		PROCEDURE Refresh(sender, data : ANY);
		END Refresh;

	END InspectionTree;

TYPE

	(** Tree component that displays all window instances and their component hierarchies *)
	FormComponentsTree* = OBJECT(InspectionTree)
	VAR
		windows : Windows;
		refreshBtn : WMStandardComponents.Button;
		dragger: DragCommand;

		PROCEDURE &Init;
		BEGIN
			Init^;
			Clear(windows);

			NEW(refreshBtn); refreshBtn.alignment.Set(WMComponents.AlignBottom);
			refreshBtn.bounds.SetHeight(20);
			refreshBtn.caption.SetAOC("Refresh");
			refreshBtn.onClick.Add(Refresh);
			AddContent(refreshBtn);
			NEW(dragger); dragger.alignment.Set(WMComponents.AlignBottom);
			dragger.bounds.SetHeight(20);
			AddContent(dragger);
			AddContent(treeView);
		END Init;

		PROCEDURE AddFormWindow(window : WMComponents.FormWindow; parent : WMTrees.TreeNode);
		VAR node : WMTrees.TreeNode; caption : ARRAY 64 OF CHAR; string : Strings.String;
		BEGIN
			ASSERT((window # NIL) & (parent # NIL));
			string := window.GetTitle();
			IF (string # NIL) THEN
				COPY(string^, caption);
			ELSE
				caption := "NoTitle";
			END;

			NEW(node);
			tree.SetNodeCaption(node, Strings.NewString(caption));
			tree.AddChildNode(parent, node);
			tree.InclNodeState(node, WMTrees.NodeExpanded);
			tree.ExpandToRoot(node);
			IF (window.form # NIL) THEN
				AddComponents(window.form, node);
			END;
		END AddFormWindow;

		PROCEDURE Refresh(sender, data : ANY);
		VAR root : WMTrees.TreeNode; nofWindows, i : LONGINT;
		BEGIN
			ASSERT(tree # NIL);
			GetWindows(windows, nofWindows);
			tree.Acquire;
			NEW(root);
			tree.SetRoot(root);
			tree.SetNodeCaption(root, Strings.NewString("Windows"));
			tree.InclNodeState(root, WMTrees.NodeExpanded);
			IF (nofWindows > 0) THEN
				FOR i := 0 TO nofWindows - 1 DO
					IF (windows[i] # NIL) & (windows[i] IS WMComponents.FormWindow) THEN
						AddFormWindow(windows[i](WMComponents.FormWindow), root);
					END;
				END;
			END;
			tree.Release;
		END Refresh;

	END FormComponentsTree;

TYPE

	TextComponentsTree = OBJECT(InspectionTree)

		PROCEDURE &Init;
		BEGIN
			Init^;
			AddContent(treeView);
			Texts.onLastTextChanged.Add(Refresh);
		END Init;

		PROCEDURE Refresh(sender, data : ANY);
		VAR
			root : WMTrees.TreeNode;
			text : Texts.Text; reader : Texts.TextReader;
			ignoreCh : Texts.Char32;
		BEGIN
			ASSERT(tree # NIL);
			text := Texts.GetLastText();
			IF (text # NIL) THEN
				text.AcquireRead;
				NEW(reader, text); reader.SetPosition(0);
				tree.Acquire;
				NEW(root);
				tree.SetRoot(root);
				tree.SetNodeCaption(root, Strings.NewString("Text"));
				tree.InclNodeState(root, WMTrees.NodeExpanded);
				WHILE ~reader.eot DO
					reader.ReadCh(ignoreCh);
					IF (reader.object # NIL) & (reader.object IS WMComponents.Component) THEN
						AddComponents(reader.object (WMComponents.Component), root);
					END;
				END;
				tree.Release;
				text.ReleaseRead;
			ELSE
				tree.Acquire;
				NEW(root);
				tree.SetRoot(root);
				tree.SetNodeCaption(root, Strings.NewString("No text selection"));
				tree.InclNodeState(root, WMTrees.NodeExpanded);
				tree.Release;
			END;
		END Refresh;

		PROCEDURE Finalize;
		BEGIN
			Finalize^;
			Texts.onLastTextChanged.Remove(Refresh);
		END Finalize;

	END TextComponentsTree;

TYPE

	SelectedTextTree = OBJECT(InspectionTree)

		PROCEDURE &Init;
		BEGIN
			Init^;
			AddContent(treeView);
			Texts.onLastSelectionChanged.Add(Refresh);
		END Init;

		PROCEDURE Refresh(sender, data : ANY);
		VAR
			root : WMTrees.TreeNode;
			text : Texts.Text; from, to : Texts.TextPosition; reader : Texts.TextReader;
			ignoreCh : Texts.Char32;
		BEGIN
			ASSERT(tree # NIL);
			IF Texts.GetLastSelection(text, from, to) THEN
				text.AcquireRead;
				NEW(reader, text); reader.SetPosition(from.GetPosition());
				tree.Acquire;
				NEW(root);
				tree.SetRoot(root);
				tree.SetNodeCaption(root, Strings.NewString("Text"));
				tree.InclNodeState(root, WMTrees.NodeExpanded);
				WHILE ~reader.eot & (reader.GetPosition() < to.GetPosition()) DO
					reader.ReadCh(ignoreCh);
					IF (reader.object # NIL) & (reader.object IS WMComponents.Component) THEN
						AddComponents(reader.object (WMComponents.Component), root);
					END;
				END;
				tree.Release;
				text.ReleaseRead;
			ELSE
				tree.Acquire;
				NEW(root);
				tree.SetRoot(root);
				tree.SetNodeCaption(root, Strings.NewString("No text selection"));
				tree.InclNodeState(root, WMTrees.NodeExpanded);
				tree.Release;
			END;
		END Refresh;

		PROCEDURE Finalize;
		BEGIN
			Finalize^;
			Texts.onLastSelectionChanged.Remove(Refresh);
		END Finalize;

	END SelectedTextTree;

TYPE

	KillerMsg = OBJECT
	END KillerMsg;

	Window* = OBJECT(WMComponents.FormWindow)
	VAR
		formTree- : FormComponentsTree;
		textTree : TextComponentsTree;
		selectedTextTree : SelectedTextTree;
		currentTree : InspectionTree;
		propertyPanel : WMInspectionComponents.PropertyPanel;
		libraryPanel : WMInspectionComponents.RepositoryPanel;
		xmlPanel : WMInspectionComponents.XMLPanel;

		PROCEDURE &New*(context : WMRestorable.Context);
		BEGIN
			Init(WindowWidth, WindowHeight, FALSE);
			IncCount;
			SetContent(CreateForm());
			SetTitle(Strings.NewString("Inspector"));
			SetIcon(WMGraphics.LoadImage("WMInspector.tar://WMInspector.png", TRUE));
			currentTree := formTree;
			formTree.treeView.onClickNode.Add(NodeClicked);
			formTree.Refresh(NIL, NIL);
			textTree.treeView.onClickNode.Add(NodeClicked);
			textTree.Refresh(NIL, NIL);
			selectedTextTree.treeView.onClickNode.Add(NodeClicked);
			selectedTextTree.Refresh(NIL, NIL);
		END New;

		PROCEDURE CreateForm() : WMComponents.VisualComponent;
		VAR
			panel, rightPanel, treePanel, libPanel : WMStandardComponents.Panel; resizer : WMStandardComponents.Resizer;
			tabPanel : WMTabComponents.TabPanel; tabControl : WMTabComponents.Tabs; tabEntry : WMTabComponents.TabEntry;
		BEGIN
			NEW(panel); panel.alignment.Set(WMComponents.AlignClient);
			panel.fillColor.Set(WMGraphics.White);

			NEW(treePanel); treePanel.alignment.Set(WMComponents.AlignLeft);
			treePanel.bounds.SetWidth(200);
			panel.AddContent(treePanel);

			NEW(resizer); resizer.alignment.Set(WMComponents.AlignRight);
			resizer.bounds.SetWidth(5);
			treePanel.AddContent(resizer);

			NEW(tabPanel); tabPanel.alignment.Set(WMComponents.AlignClient);
			treePanel.AddContent(tabPanel);

			NEW(tabControl); tabControl.alignment.Set(WMComponents.AlignTop);
			tabControl.bounds.SetHeight(20);
			tabControl.onSelectTab.Add(TabSelected);
			tabPanel.AddContent(tabControl);

			NEW(tabEntry); tabEntry.alignment.Set(WMComponents.AlignClient);
			tabEntry.caption.SetAOC("Windows");
			tabPanel.AddContent(tabEntry);

			NEW(formTree); formTree.alignment.Set(WMComponents.AlignClient);
			tabEntry.AddContent(formTree);
			formTree.dragger.window := SELF;

			NEW(tabEntry); tabEntry.alignment.Set(WMComponents.AlignClient);
			tabEntry.caption.SetAOC("Text");
			tabPanel.AddContent(tabEntry);

			NEW(textTree); textTree.alignment.Set(WMComponents.AlignClient);
			tabEntry.AddContent(textTree);

			NEW(tabEntry); tabEntry.alignment.Set(WMComponents.AlignClient);
			tabEntry.caption.SetAOC("Selection");
			tabPanel.AddContent(tabEntry);

			NEW(selectedTextTree); selectedTextTree.alignment.Set(WMComponents.AlignClient);
			tabEntry.AddContent(selectedTextTree);

			NEW(rightPanel); rightPanel.alignment.Set(WMComponents.AlignClient);
			panel.AddContent(rightPanel);

			NEW(libPanel); libPanel.alignment.Set(WMComponents.AlignBottom);
			libPanel.bounds.SetHeight(60);
			libPanel.fillColor.Set(0C0C0C0FFH);
			rightPanel.AddContent(libPanel);

			NEW(resizer); resizer.alignment.Set(WMComponents.AlignTop);
			resizer.bounds.SetHeight(5);
			libPanel.AddContent(resizer);

			NEW(libraryPanel); libraryPanel.alignment.Set(WMComponents.AlignTop);
			libraryPanel.bounds.SetHeight(50);
			libraryPanel.bearing.Set(WMRectangles.MakeRect(Bearing, Bearing, Bearing, Bearing));
			libPanel.AddContent(libraryPanel);

			NEW(xmlPanel); xmlPanel.alignment.Set(WMComponents.AlignTop);
			xmlPanel.bounds.SetHeight(20);
			xmlPanel.bearing.Set(WMRectangles.MakeRect(2*Bearing, Bearing, Bearing, Bearing));
			libPanel.AddContent(xmlPanel);

			NEW(propertyPanel); propertyPanel.alignment.Set(WMComponents.AlignClient);
			rightPanel.AddContent(propertyPanel);

			RETURN panel;
		END CreateForm;

		PROCEDURE TabSelected(sender, data : ANY);
		VAR caption : Strings.String;
		BEGIN
			IF (data # NIL) & (data IS WMTabComponents.Tab)  THEN
				caption := data(WMTabComponents.Tab).caption;
				IF (caption # NIL) THEN
					IF (caption^ = "Windows") THEN currentTree := formTree;
					ELSIF (caption^ = "Text") THEN currentTree := textTree;
					ELSIF (caption^ = "Selection") THEN currentTree := selectedTextTree;
					END;
				END;
			END;
		END TabSelected;

		PROCEDURE NodeClicked(sender, data : ANY);
		VAR ptr : ANY;
		BEGIN
			IF (data # NIL) & (data IS WMTrees.TreeNode) THEN
				currentTree.tree.Acquire;
				ptr := currentTree.tree.GetNodeData(data(WMTrees.TreeNode));
				currentTree.tree.Release;
				IF (ptr # NIL) & (ptr IS WMComponents.Component) THEN
					propertyPanel.SetComponent(SELF, ptr(WMComponents.Component));
					libraryPanel.SetComponent(ptr(WMComponents.Component));
					xmlPanel.SetComponent(ptr(WMComponents.Component));
				ELSE
					propertyPanel.SetComponent(SELF, NIL);
					libraryPanel.SetComponent(NIL);
					xmlPanel.SetComponent(NIL);
				END;
			END;
		END NodeClicked;

		PROCEDURE Handle(VAR x : WMMessages.Message);
		BEGIN
			IF (x.msgType = WMMessages.MsgExt) & (x.ext # NIL) THEN
				IF (x.ext IS KillerMsg) THEN Close
				ELSIF (x.ext IS WMRestorable.Storage) THEN
					x.ext(WMRestorable.Storage).Add("WMInspector", "WMInspector.Restore", SELF, NIL);
				ELSE Handle^(x)
				END
			ELSE Handle^(x)
			END
		END Handle;

		PROCEDURE Close;
		BEGIN
			Close^;
			DecCount;
		END Close;

	END Window;

	(* quick and dirty, preliminary for testing purposes, fof *)
	DragCommand*= OBJECT(WMStandardComponents.Label)
	VAR caption: XML.Attribute; window: Window;

		PROCEDURE &Init*;
		BEGIN
			Init^; SELF.window := NIL;
			NEW(caption); caption.SetName("Caption"); caption.SetValue("Drag to Inspect"); AddAttribute(caption);
			SetGenerator("IngaComponents.NewCommandDragger");
		END Init;

		PROCEDURE DrawBackground(canvas: WMGraphics.Canvas);
		VAR r: WMRectangles.Rectangle; name: XML.String;
		BEGIN
			r := GetClientRect();
			canvas.Fill(r,LONGINT(0FF00FFFFH),WMGraphics.ModeSrcOverDst);
			name := caption.GetValue();
			IF name # NIL THEN
				r := GetClientRect();
				canvas.SetColor(0FFH);
				WMGraphics.DrawStringInRect(canvas, r, FALSE, 1, 1, name^)
			END;
		END DrawBackground;

		PROCEDURE Accept(sender, par: ANY);
		VAR window: Window;
			treeView : WMTrees.TreeView;
			tree : WMTrees.Tree;
			root: WMTrees.TreeNode;
		(*window: WMInspectionComponents.Window; propertyPanel: WMInspectionComponents.PropertyPanel;*)

			PROCEDURE FindComponent(node: WMTrees.TreeNode): BOOLEAN;
			BEGIN
				IF node = NIL THEN RETURN FALSE
				ELSIF tree.GetNodeData(node)=sender THEN
					tree.InclNodeState(node, WMTrees.NodeExpanded);
					treeView.SelectNode(node);
					treeView.onClickNode.Call(node);
					RETURN TRUE
				ELSE
					IF FindComponent(tree.GetChildren(node)) THEN
						tree.InclNodeState(node, WMTrees.NodeExpanded);
						RETURN TRUE
						(* open drag *)
					ELSE
						tree.ExclNodeState(node, WMTrees.NodeExpanded);
						RETURN FindComponent(tree.GetNextSibling(node))
					END;
				END;
			END FindComponent;

		BEGIN
			IF (sender # NIL) & (sender IS WMComponents.Component) THEN
				IF SELF.window = NIL THEN
					NEW(window,NIL);
					WMWindowManager.AddWindow(window,100,100);
				ELSE window := SELF.window
				END;

				treeView := window.formTree.treeView;
				tree := window.formTree.tree;
				window.formTree.Refresh(SELF,NIL);
				tree.Acquire;
				root := tree.GetRoot();
				IF FindComponent(root) THEN END;
				tree.Release;
				(*
				NEW(propertyPanel);
				propertyPanel.bounds.SetExtents(300,300);
				propertyPanel.fillColor.Set(WMGraphics.Yellow);
				NEW(window, propertyPanel);
				propertyPanel.SetComponent(SELF,sender);
				*)
			END;
		END Accept;

		PROCEDURE PointerDown(x, y : LONGINT; keys : SET);
		VAR
			img,icon: WMGraphics.Image; canvas, iconCanvas: WMGraphics.BufferCanvas; color: LONGINT;
			r: WMRectangles.Rectangle;
		BEGIN
			IF 0 IN keys THEN
				r := GetClientRect();
				color := LONGINT(0AAFF00FFH);
				NEW(img);
				Raster.Create(img, 30,30, Raster.BGRA8888);
				NEW(canvas,img);
				canvas.Fill(WMRectangles.MakeRect(0, 0, 30,30), color , WMGraphics.ModeSrcOverDst);

				IF StartDrag(NIL, img, 0,0,Accept,Accept) THEN
				END;
			END
		END PointerDown;

	END DragCommand;

VAR
	nofWindows : LONGINT;
	manager : WMWindowManager.WindowManager;

PROCEDURE Open*;
VAR window : Window;
BEGIN
	NEW(window, NIL);
	WMWindowManager.AddWindow(window, 100, 100);
END Open;

PROCEDURE Restore*(context : WMRestorable.Context);
VAR window : Window;
BEGIN
	NEW(window, context);
	WMRestorable.AddByContext(window, context);
END Restore;

PROCEDURE Clear(VAR windows : Windows);
VAR i : LONGINT;
BEGIN
	FOR i := 0 TO LEN(windows)-1 DO
		windows[i] := NIL;
	END;
END Clear;

(** Postcondition: {(windows # NIL) & (0 <= nofWindows < MaxNofWindows) & (windows[i < nofWindows] # NIL)} *)
PROCEDURE GetWindows(VAR windows : Windows; VAR nofWindows : LONGINT);
VAR
	window : WMWindowManager.Window;

	PROCEDURE IsUserWindow(window : WMWindowManager.Window) : BOOLEAN;
	BEGIN
		ASSERT(window # NIL);
		RETURN {WMWindowManager.FlagDecorWindow} * window.flags = {};
	END IsUserWindow;

	PROCEDURE SortWindowsById(VAR windows : Windows);
	VAR temp : WMWindowManager.Window; i, j : LONGINT;
	BEGIN
		(* for now bubble sort is sufficient *)
		FOR i := 0 TO nofWindows-1 DO
			FOR j := 0 TO nofWindows-2 DO
				IF (windows[j].id > windows[j+1].id) THEN
					temp := windows[j+1];
					windows[j+1] := windows[j];
					windows[j] := temp;
				END;
			END;
		END;
	END SortWindowsById;

BEGIN
	ASSERT((manager # NIL));
	(* clear all references *)
	Clear(windows);
	manager.lock.AcquireWrite;
	nofWindows := 0;
	window := manager.GetFirst();
	WHILE (window # NIL) & (nofWindows < MaxNofWindows) DO
		IF IsUserWindow(window) THEN
			windows[nofWindows] := window;
			INC(nofWindows);
		END;
		window := manager.GetNext(window);
	END;
	manager.lock.ReleaseWrite;
	IF (nofWindows > 1) THEN SortWindowsById(windows); END;
END GetWindows;

PROCEDURE IncCount;
BEGIN {EXCLUSIVE}
	INC(nofWindows)
END IncCount;

PROCEDURE DecCount;
BEGIN {EXCLUSIVE}
	DEC(nofWindows)
END DecCount;

PROCEDURE Cleanup;
VAR die : KillerMsg;
	 msg : WMMessages.Message;
	 m : WMWindowManager.WindowManager;
BEGIN {EXCLUSIVE}
	NEW(die);
	msg.ext := die;
	msg.msgType := WMMessages.MsgExt;
	m := WMWindowManager.GetDefaultManager();
	m.Broadcast(msg);
	AWAIT(nofWindows = 0)
END Cleanup;

PROCEDURE NewCommandDragger*(): XML.Element;
VAR label : DragCommand;
BEGIN NEW(label); RETURN label
END NewCommandDragger;

BEGIN
	nofWindows := 0;
	manager := WMWindowManager.GetDefaultManager();
	Modules.InstallTermHandler(Cleanup);
END WMInspector.

SystemTools.Free WMInspector ~

SystemTools.FreeDownTo WMInspectionComponents ~

WMInspector.Open ~

ComponentViewer.Open --client WMInspector.NewCommandDragger ~
