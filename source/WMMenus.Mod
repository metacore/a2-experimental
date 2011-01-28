MODULE WMMenus;	(** AUTHOR "TF"; PURPOSE "Menu support"; *)

IMPORT
	Strings, Raster, WMRectangles, WMGraphics, WMGraphicUtilities, WMComponents,
	WMWindowManager, WMProperties, WMEvents, WMTrees, KernelLog;

CONST
	OpenDefault* = 0;
	OpenUpLeft* = 1;
	OpenUpRight* = 2;
	OpenDownLeft* = 3;
	OpenDownRight* = 4;

	(* ShadowWindow.type *)
	Right = 0;
	Bottom = 1;

	ShadowWidth = 5;
	ShadowHeight = 5;
	ShadowOffsetVertical = 5;
	ShadowOffsetHorizontal = 5;

	HMenuDistance = 10;
	VMenuDistance = 4;

	SeparatorCaption = "---";
	SeparatorWidth = 9;
	SeparatorHeight = 9;

TYPE

	Separator* = OBJECT(WMTrees.TreeNode)
	END Separator;

TYPE

	MenuPanel*= OBJECT(WMComponents.VisualComponent)
	VAR
		horizontal- : WMProperties.BooleanProperty;
		openDirection- : WMProperties.Int32Property;

		borders- : WMProperties.RectangleProperty;
		bordersI : WMRectangles.Rectangle;

		onSelect- : WMEvents.EventSource;

		menu : WMTrees.Tree;
		root, selection, hover : WMTrees.TreeNode;

		subMenuIndicatorImg : WMGraphics.Image;

		subMenu : MenuWindow;

		parentMenuPanel : MenuPanel;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			SetNameAsString(StrMenuPanel);
			NEW(horizontal, NIL, NIL, NIL); properties.Add(horizontal);
			NEW(openDirection, NIL, NIL, NIL); properties.Add(openDirection);
			NEW(borders, NIL, NIL, NIL); properties.Add(borders);
			NEW(onSelect, SELF, NIL, NIL, NIL);
			bordersI := WMRectangles.MakeRect(15, 5, 5, 5);
			borders.Set(bordersI);
			menu := NIL;
			root := NIL; selection := NIL; hover := NIL;
			subMenuIndicatorImg := NIL;
			subMenu := NIL;
			parentMenuPanel := NIL;
			takesFocus.Set(TRUE);
		END Init;

		PROCEDURE PropertyChanged(sender, property : ANY);
		BEGIN
			IF (property = borders) THEN
				bordersI := borders.Get(); Invalidate;
			ELSE
				PropertyChanged^(sender, property);
			END;
		END PropertyChanged;

		PROCEDURE RecacheProperties;
		BEGIN
			RecacheProperties^;
			bordersI := borders.Get();
			Invalidate;
		END RecacheProperties;

		PROCEDURE SetParent(parentMenuPanel : MenuPanel);
		BEGIN
			SELF.parentMenuPanel := parentMenuPanel;
		END SetParent;

		PROCEDURE SetMenu*(menu : WMTrees.Tree; root : WMTrees.TreeNode);
		BEGIN
			ASSERT((menu # NIL) & (root # NIL));
			Acquire;
			SELF.menu := menu; SELF.root := root; selection := NIL; hover := NIL;
			Invalidate;
			Release
		END SetMenu;

		PROCEDURE Measure(VAR width, height : LONGINT);
		VAR child : WMTrees.TreeNode;
		BEGIN
			ASSERT((menu # NIL) & (root # NIL));
			width := bordersI.l + bordersI.r;
			height := bordersI.t + bordersI.b;
			IF horizontal.Get() THEN
				menu.Acquire;
				child := menu.GetChildren(root);
				WHILE (child # NIL) DO
					width := width + ItemWidth(child);
					child := menu.GetNextSibling(child);
				END;
				menu.Release;
			ELSE
				menu.Acquire;
				child := menu.GetChildren(root);
				WHILE (child # NIL) DO
					height := height + ItemHeight(child);
					width := Strings.Max(width, ItemWidth(child) + bordersI.l + bordersI.r);
					child := menu.GetNextSibling(child);
				END;
				menu.Release;
			END;
		END Measure;

		PROCEDURE DrawBackground(canvas : WMGraphics.Canvas);
		VAR
			child : WMTrees.TreeNode;
			x, y, dx, dy, t : LONGINT;
			font : WMGraphics.Font;
			caption : Strings.String;
			image : Raster.Image;
		BEGIN
			DrawBackground^(canvas);
			IF (menu = NIL) OR (root = NIL) THEN RETURN; END;
			font := GetFont();
			canvas.SetFont(font);
			canvas.SetColor(WMGraphics.Black);
			x := bordersI.l; y := bordersI.t;
			IF horizontal.Get() THEN
				menu.Acquire;
				child := menu.GetChildren(root);
				WHILE (child # NIL) DO
					IF ~(child IS Separator) THEN
						IF (child = hover) THEN
							canvas.Fill(WMRectangles.MakeRect(x, 0, x + ItemWidth(child), bounds.GetHeight()), SHORT(0FFFF00FFH), WMGraphics.ModeCopy);
						END;
						image := menu.GetNodeImage(child);
						IF (image # NIL) THEN
							canvas.DrawImage(HMenuDistance DIV 2 + x, 0, image, WMGraphics.ModeSrcOverDst);
							x := x + image.width;
						END;

						caption := menu.GetNodeCaption(child);
						IF (caption # NIL) THEN
							font.GetStringSize(caption^, dx, dy); canvas.DrawString(HMenuDistance DIV 2 + x, dy, caption^);
							x := x + dx;
						END;
						INC(x, HMenuDistance);
					ELSE
						canvas.Line(x + (SeparatorWidth DIV 2) + 1, 2, x + (SeparatorWidth DIV 2) + 1, bounds.GetHeight() - 2, WMGraphics.Black, WMGraphics.ModeCopy);
						x := x + SeparatorWidth;
					END;
					child := menu.GetNextSibling(child)
				END;
				menu.Release;
			ELSE
				menu.Acquire;
				child := menu.GetChildren(root);
				WHILE (child # NIL) DO
					IF ~(child IS Separator) THEN
						IF (child = hover) THEN
							canvas.Fill(WMRectangles.MakeRect(0, y, bounds.GetWidth(), y + ItemHeight(child)), SHORT(0FFFF00FFH), WMGraphics.ModeCopy);
						END;

						dy := 0;
						image := menu.GetNodeImage(child);
						IF (image # NIL) THEN
							canvas.DrawImage(0, y, image, WMGraphics.ModeSrcOverDst);
							dy := image.width + VMenuDistance;
						END;

						caption := menu.GetNodeCaption(child);
						IF (caption # NIL) THEN
							font.GetStringSize(caption^, dx, t); canvas.DrawString(x, y + font.ascent + VMenuDistance DIV 2, caption^);
							INC(t, VMenuDistance);
							IF t > dy THEN dy := t END
						END;

						IF menu.GetChildren(child) # NIL THEN
							IF subMenuIndicatorImg # NIL THEN
								canvas.DrawImage(bounds.GetWidth() - subMenuIndicatorImg.width, 0, subMenuIndicatorImg, WMGraphics.ModeSrcOverDst)
							ELSE
								canvas.DrawString(bounds.GetWidth() - 10, y + font.ascent, "...")
							END
						END;
						y := y + dy;
					ELSE
						canvas.Line(x + 2, y + (SeparatorHeight DIV 2) + 1, bounds.GetWidth(), y + (SeparatorHeight DIV 2) + 1, WMGraphics.Black, WMGraphics.ModeCopy);
						y := y + SeparatorHeight;
					END;
					child := menu.GetNextSibling(child)
				END;
				menu.Release;
			END;
		END DrawBackground;

		(* caller must hold tree lock *)
		PROCEDURE ItemWidth(item : WMTrees.TreeNode) : LONGINT;
		VAR
			width, dx, dy : LONGINT;
			font : WMGraphics.Font;
			caption : Strings.String;
			image : Raster.Image;
		BEGIN
			IF ~(item IS Separator) THEN
				width := HMenuDistance;

				caption := menu.GetNodeCaption(item);
				IF (caption # NIL) THEN
					font := GetFont(); font.GetStringSize(caption^, dx, dy);
					width := width + dx;
				END;

				image := menu.GetNodeImage(item);
				IF (image # NIL) THEN width := width + image.width; END;
			ELSE
				width := SeparatorWidth;
			END;
			RETURN width;
		END ItemWidth;

		(* caller must hold tree lock *)
		PROCEDURE ItemHeight(item : WMTrees.TreeNode) : LONGINT;
		VAR
			height, dx, dy : LONGINT;
			font : WMGraphics.Font;
			caption : Strings.String;
			image : Raster.Image;
		BEGIN
			IF ~(item IS Separator) THEN
				height := VMenuDistance;

				caption := menu.GetNodeCaption(item);
				IF (caption # NIL) THEN
					font := GetFont(); font.GetStringSize(caption^, dx, dy);
					height := height + dy;
				END;

				image := menu.GetNodeImage(item);
				IF (image # NIL) THEN
					IF (image.height + VMenuDistance > height) THEN
						height := image.height + VMenuDistance;
					END;
				END;
			ELSE
				height := SeparatorHeight;
			END;
			RETURN height
		END ItemHeight;

		PROCEDURE IsSelectable(node : WMTrees.TreeNode) : BOOLEAN;
		BEGIN
			ASSERT(node # NIL);
			RETURN ~(node IS Separator);
		END IsSelectable;

		PROCEDURE FindHorizontal(x : LONGINT) : WMTrees.TreeNode;
		VAR p : LONGINT; child : WMTrees.TreeNode;
		BEGIN
			p := bordersI.l;
			menu.Acquire;
			child := menu.GetChildren(root);
			IF (child # NIL) THEN
				REPEAT
					p := p + ItemWidth(child);
					IF p < x THEN child := menu.GetNextSibling(child); END;
				UNTIL (child = NIL) OR (p >= x);
			END;
			menu.Release;
			RETURN child;
		END FindHorizontal;

		PROCEDURE FindVertical(y : LONGINT) : WMTrees.TreeNode;
		VAR p : LONGINT; child : WMTrees.TreeNode;
		BEGIN
			p := bordersI.t;
			menu.Acquire;
			child := menu.GetChildren(root);
			IF (child # NIL) THEN
				REPEAT
					p := p + ItemHeight(child);
					IF p < y THEN child := menu.GetNextSibling(child); END;
				UNTIL (child = NIL) OR (p >= y);
			END;
			menu.Release;
			RETURN child;
		END FindVertical;

		PROCEDURE GetItemRect(i : WMTrees.TreeNode; VAR r : WMRectangles.Rectangle);
		VAR child : WMTrees.TreeNode;
		BEGIN
			r.l := 0; r.t := 0;
			menu.Acquire;
			child := menu.GetChildren(root);
			WHILE (child # NIL) & (child # i) DO
				IF horizontal.Get() THEN
					INC(r.l, ItemWidth(child))
				ELSE
					INC(r.t, ItemHeight(child))
				END;
				child := menu.GetNextSibling(child);
			END;
			IF (child # NIL) THEN r.r := r.l + ItemWidth(child); r.b := r.t + ItemHeight(child) END;
			menu.Release
		END GetItemRect;

		PROCEDURE PointerMove(x, y : LONGINT; keys : SET);
		VAR node : WMTrees.TreeNode;
		BEGIN
			IF horizontal.Get() THEN
				node := FindHorizontal(x);
			ELSE
				node := FindVertical(y);
			END;
			IF (node # NIL) & ~IsSelectable(node) THEN node := NIL; END;
			IF (node # hover) THEN hover := node; Invalidate; END;
		END PointerMove;

		PROCEDURE LeafSelect(item : WMTrees.TreeNode);
		BEGIN
			IF parentMenuPanel = NIL THEN
				IF subMenu # NIL THEN subMenu.CloseMenu(SELF, NIL); subMenu := NIL; END;
				onSelect.Call(item);
			ELSE
				parentMenuPanel.LeafSelect(item);
			END
		END LeafSelect;

		PROCEDURE PointerDown(x, y : LONGINT; keys : SET);
		VAR node, child : WMTrees.TreeNode; r : WMRectangles.Rectangle;
		BEGIN
			IF horizontal.Get() THEN
				node := FindHorizontal(x);
			ELSE
				node := FindVertical(y);
			END;
			IF (node # NIL) & IsSelectable(node) THEN
				menu.Acquire;
				child := menu.GetChildren(node);
				IF (child # NIL) THEN
					GetItemRect(node, r);
					IF horizontal.Get() THEN
						IF openDirection.Get() IN {OpenUpLeft, OpenUpRight} THEN ToWMCoordinates(r.l, r.t, x, y);
						ELSE ToWMCoordinates(r.l, r.b, x, y);
						END
					ELSE
						CASE openDirection.Get() OF
							|OpenUpLeft : ToWMCoordinates(r.l, r.b, x, y);
							|OpenUpRight : ToWMCoordinates(r.r, r.b, x, y);
							|OpenDownLeft : ToWMCoordinates(r.l, r.t, x, y);
							|OpenDownRight : ToWMCoordinates(r.r, r.t, x, y);
						ELSE
							ToWMCoordinates(r.r, r.t, x, y);
						END;
					END;
					IF subMenu # NIL THEN subMenu.CloseMenu(SELF, NIL); subMenu := NIL; END;
					NEW(subMenu, x, y, openDirection.Get(), menu, node, SELF);
					PointerLeave;
				ELSE
					LeafSelect(node)
				END;
				menu.Release;
			END;
		END PointerDown;

		PROCEDURE PointerLeave;
		BEGIN
			IF hover # NIL THEN hover := NIL; Invalidate; END;
		END PointerLeave;

		PROCEDURE Finalize;
		BEGIN
			Finalize^;
			IF subMenu # NIL THEN subMenu.Close; subMenu := NIL; END;
		END Finalize;

		PROCEDURE FocusLost;
		BEGIN
			IF subMenu # NIL THEN subMenu.Close; subMenu := NIL; END;
		END FocusLost;

	END MenuPanel;

TYPE

	ShadowWindow = OBJECT(WMWindowManager.Window)
	VAR
		type, color : LONGINT;

		PROCEDURE &New(type : LONGINT);
		BEGIN
			ASSERT((type = Right) OR (type = Bottom));
			SELF.type := type;
			Init(0, 0, TRUE);
			color := 04FH;
		END New;

		PROCEDURE Draw*(canvas : WMGraphics.Canvas; w, h, q : LONGINT);
		BEGIN
			canvas.Fill(WMRectangles.MakeRect(0, 0, w, h), color, WMGraphics.ModeSrcOverDst);
		END Draw;

	END ShadowWindow;

TYPE

	MenuWindow= OBJECT(WMComponents.FormWindow)
	VAR
		menuPanel : MenuPanel;

		PROCEDURE &Open*(x, y : LONGINT; openDirection : LONGINT; menu : WMTrees.Tree; root : WMTrees.TreeNode; parent : MenuPanel);
		VAR width, height, dx, dy : LONGINT;
		BEGIN
			NEW(menuPanel);
			menuPanel.SetMenu(menu, root);
			menuPanel.SetParent(parent);

			menuPanel.Measure(width, height);
			IF (height < 5) THEN height := 5; END;
			IF (width < 5) THEN width := 5; END;

			CASE openDirection OF
				|OpenUpLeft : dx := -width; dy := -height;
				|OpenUpRight : dy := -height;
				|OpenDownLeft : dx := -width;
			ELSE
				dx := 0; dy := 0;
			END;
			menuPanel.openDirection.Set(openDirection);
			menuPanel.bounds.SetExtents(width, height);
			menuPanel.fillColor.Set(WMGraphics.White);

			Init(menuPanel.bounds.GetWidth(), menuPanel.bounds.GetHeight(), FALSE);
			SetContent(menuPanel);
			AddWindow(SELF, x + dx, y + dy, {WMWindowManager.FlagNoFocus, WMWindowManager.FlagFrame, WMWindowManager.FlagHidden});
			IF manager.TransferPointer(SELF) THEN KernelLog.String("Pointer transferred "); KernelLog.Ln;  END;
		END Open;

		PROCEDURE CloseMenu(sender, data : ANY);
		BEGIN
			IF ~sequencer.IsCallFromSequencer() THEN
				sequencer.ScheduleEvent(SELF.CloseMenu, NIL, NIL);
			ELSE
				Close;
			END
		END CloseMenu;

		PROCEDURE Draw(canvas : WMGraphics.Canvas; w, h, q : LONGINT); (** override *)
		BEGIN
			Draw^(canvas, w, h, q);
			WMGraphicUtilities.DrawRect(canvas, WMRectangles.MakeRect(0, 0, w, h), WMGraphics.Black, WMGraphics.ModeCopy);
		END Draw;

	END MenuWindow;

VAR
	StrMenuPanel : Strings.String;

PROCEDURE AddWindow(window : WMWindowManager.Window; x, y : LONGINT; flags : SET);
VAR
	manager : WMWindowManager.WindowManager;
	view : WMWindowManager.ViewPort;
	oldDecorator : WMWindowManager.Decorator;
BEGIN
	ASSERT(window # NIL);
	manager := WMWindowManager.GetDefaultManager();
	view := WMWindowManager.GetDefaultView();
	ASSERT((manager # NIL) & (view # NIL));
	manager.lock.AcquireWrite;
	oldDecorator := manager.decorate;
	manager.decorate := ShadowDecorator;
	manager.Add(ENTIER(view.range.l) + x, ENTIER(view.range.t) + y, window, flags);
	manager.decorate := oldDecorator;
	manager.lock.ReleaseWrite;
END AddWindow;

PROCEDURE ShadowDecorator(window : WMWindowManager.Window);
VAR shadow : ShadowWindow; l, r, t, b : LONGINT;

	PROCEDURE InsertAfter(old, new : WMWindowManager.Window);
	BEGIN
		new.next := old.next;
		new.prev := old;
		old.next := new;
		new.next.prev := new
	END InsertAfter;

	PROCEDURE InitShadow(shadow : ShadowWindow);
	BEGIN
		shadow.manager := window.manager;
		shadow.flags := {WMWindowManager.FlagNoFocus, WMWindowManager.FlagHidden};
		IF WMWindowManager.FlagStayOnBottom IN window.flags THEN INCL(shadow.flags, WMWindowManager.FlagStayOnBottom); END;
		IF WMWindowManager.FlagNoResizing IN window.flags THEN INCL(shadow.flags, WMWindowManager.FlagNoResizing); END;
		IF WMWindowManager.FlagNavigation IN window.flags THEN
			shadow.view := window.view;
			INCL(shadow.flags, WMWindowManager.FlagNavigation);
		END;
		InsertAfter(window, shadow);

		shadow.manager.AddDecorWindow(window, shadow);
		shadow.manager.AddVisibleDirty(shadow, shadow.bounds);
	END InitShadow;

BEGIN
	ASSERT((window.manager # NIL) & (window.manager.lock.HasWriteLock()));
	l := window.bounds.l; r := window.bounds.r; t := window.bounds.t; b := window.bounds.b;

	NEW(shadow, Right); window.rightW := shadow;
	shadow.bounds := WMRectangles.MakeRect(r, t + ShadowOffsetVertical, r + ShadowWidth, b + ShadowHeight);
	InitShadow(shadow);

	NEW(shadow, Bottom); window.bottomW := shadow;
	shadow.bounds := WMRectangles.MakeRect(l + ShadowOffsetHorizontal, b, r, b + ShadowHeight);
	InitShadow(shadow);
END ShadowDecorator;

PROCEDURE GetCaption*(data : ANY; menu : WMTrees.Tree) : Strings.String;
VAR caption : Strings.String;
BEGIN
	ASSERT(menu # NIL);
	IF (data # NIL) & (data IS WMTrees.TreeNode) THEN
		menu.Acquire;
		caption := menu.GetNodeCaption(data(WMTrees.TreeNode));
		menu.Release;
	ELSE
		caption := NIL;
	END;
	RETURN caption;
END GetCaption;

PROCEDURE FindChild(CONST caption : ARRAY OF CHAR; parent : WMTrees.TreeNode; tree : WMTrees.Tree) : WMTrees.TreeNode;
VAR child : WMTrees.TreeNode; string : Strings.String; found : BOOLEAN;
BEGIN
	ASSERT((parent # NIL) & (tree # NIL) & (tree.HasLock()));
	found := FALSE;
	child := tree.GetChildren(parent);
	WHILE (child # NIL) & ~found DO
		string := tree.GetNodeCaption(child);
		found := (string # NIL) & (string^ = caption);
		IF ~found THEN
			child := tree.GetNextSibling(child);
		END;
	END;
	RETURN child;
END FindChild;

PROCEDURE AddChild*(CONST caption : ARRAY OF CHAR; parent : WMTrees.TreeNode; tree : WMTrees.Tree) : WMTrees.TreeNode;
VAR node : WMTrees.TreeNode; separator : Separator;
BEGIN
	ASSERT((parent # NIL) & (tree # NIL) & (tree.HasLock()));
	IF (caption # SeparatorCaption) THEN
		NEW(node);
		tree.SetNodeCaption(node, Strings.NewString(caption));
	ELSE
		NEW(separator);
		node := separator;
	END;
	tree.AddChildNode(parent, node);
	RETURN node;
END AddChild;

PROCEDURE Find*(CONST path : ARRAY OF CHAR; menu : WMTrees.Tree) : WMTrees.TreeNode;
VAR caption : ARRAY 256 OF CHAR; child, node, parent : WMTrees.TreeNode; i, j : LONGINT;
BEGIN
	ASSERT(menu # NIL);
	node := NIL;
	menu.Acquire;
	parent := menu.GetRoot();
	IF (parent # NIL) THEN
		caption := "";
		i := 0; j := 0;
		LOOP
			IF (i >= LEN(path)) THEN
				EXIT;
			ELSIF (path[i] = ".") OR (path[i] = 0X) THEN
				caption[j] := 0X;
				child := FindChild(caption, parent, menu);
				IF (child = NIL) THEN
					EXIT;
				END;
				parent := child;
				IF (path[i] = 0X) THEN
					node := child;
					EXIT;
				ELSE
					caption := ""; j := 0;
				END;
			ELSIF (j < LEN(caption) - 1) THEN
				caption[j] := path[i];
				INC(j);
			END;
			INC(i);
		END;
	END;
	menu.Release;
	RETURN node;
END Find;

PROCEDURE AddItem*(CONST path : ARRAY OF CHAR; menu : WMTrees.Tree);
VAR caption : ARRAY 256 OF CHAR; node, parent : WMTrees.TreeNode; i, j : LONGINT;
BEGIN
	ASSERT(menu # NIL);
	menu.Acquire;
	IF (menu.GetRoot() = NIL) THEN
		NEW(node); menu.SetRoot(node)
	END;
	i := 0; j := 0;
	caption := ""; parent := menu.GetRoot();
	LOOP
		IF (i >= LEN(path)) THEN
			EXIT;
		ELSIF (path[i] = ".") OR (path[i] = 0X) THEN
			caption[j] := 0X;
			node := FindChild(caption, parent, menu);
			IF (node = NIL) THEN
				node := AddChild(caption, parent, menu);
			END;
			parent := node;
			caption := ""; j := 0;
			IF (path[i] = 0X) THEN EXIT; END;
		ELSIF (j < LEN(caption) - 1) THEN
			caption[j] := path[i];
			INC(j);
		END;
		INC(i);
	END;
	menu.Release;
END AddItem;

PROCEDURE Show*(menu : WMTrees.Tree; x, y : LONGINT; handler : WMEvents.EventListener);
VAR window : MenuWindow; root : WMTrees.TreeNode;
BEGIN
	ASSERT((menu # NIL) & (handler # NIL));
	menu.Acquire;
	root := menu.GetRoot();
	menu.Release;
	IF (root # NIL) THEN
		NEW(window, x, y, OpenDefault, menu, root, NIL);
		window.menuPanel.onSelect.Add(handler);
	END;
END Show;

BEGIN
	StrMenuPanel := Strings.NewString("MenuPanel");
END WMMenus.

