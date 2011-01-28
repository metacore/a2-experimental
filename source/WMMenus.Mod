MODULE WMMenus;	(** AUTHOR "TF"; PURPOSE "Menu support"; *)

IMPORT
	Strings, Raster, WMRectangles, WMGraphics, WMGraphicUtilities, WMComponents,
	WMWindowManager, WMProperties, WMEvents, WMTrees, KernelLog;

CONST
	HMenuDistance = 10;
	VMenuDistance = 4;
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

TYPE

	MenuPanel*= OBJECT(WMComponents.VisualComponent)
	VAR
		menu : WMTrees.Tree;
		root : WMTrees.TreeNode;
		selection, hover : WMTrees.TreeNode;
		horizontal- : WMProperties.BooleanProperty;
		menuSelectEvent- : WMEvents.EventSource;
		openDirection- : WMProperties.Int32Property;

		subMenuIndicatorImg : WMGraphics.Image;

		subMenu : MenuWindow;

		parentMenuPanel : MenuPanel;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			NEW(horizontal, NIL, NIL, NIL); properties.Add(horizontal);
			NEW(openDirection, NIL, NIL, NIL); properties.Add(openDirection);
			NEW(menuSelectEvent, SELF, NIL, NIL, NIL);
			takesFocus.Set(TRUE);
			SetNameAsString(StrMenuPanel);
		END Init;

		PROCEDURE SetParent(parentMenuPanel : MenuPanel);
		BEGIN
			SELF.parentMenuPanel := parentMenuPanel
		END SetParent;

		PROCEDURE SetMenu*(menu : WMTrees.Tree; root : WMTrees.TreeNode);
		BEGIN
			Acquire;
			SELF.menu := menu; SELF.root := root; selection := NIL;
			Invalidate;
			Release
		END SetMenu;

		PROCEDURE Measure(VAR w, h : LONGINT);
		VAR a : WMTrees.TreeNode;
		BEGIN
			w := 0;
			ASSERT((menu # NIL) & (root # NIL));
			IF horizontal.Get() THEN
				menu.Acquire;
				a := menu.GetChildren(root);
				WHILE a # NIL DO
					w := w + ItemWidth(a);
					a := menu.GetNextSibling(a)
				END;
				menu.Release;
			ELSE
				menu.Acquire;
				h := 0; w := 10;
				a := menu.GetChildren(root);
				WHILE a # NIL DO
					h := h + ItemHeight(a);
					w := Strings.Max(w, ItemWidth(a));
					a := menu.GetNextSibling(a)
				END;
				menu.Release;
			END;
		END Measure;

		PROCEDURE DrawBackground(canvas : WMGraphics.Canvas);
		VAR
			a : WMTrees.TreeNode;
			h, w, dx, dy, t : LONGINT;
			f : WMGraphics.Font;
			s : Strings.String;
			img : Raster.Image;
		BEGIN
			ASSERT((menu # NIL) & (root # NIL));
			DrawBackground^(canvas);
			f := GetFont();
			canvas.SetFont(f);
			canvas.SetColor(0FFH);
			w := 0; h := 0;
			IF horizontal.Get() THEN
				menu.Acquire;
				a :=menu.GetChildren(root);
				WHILE a # NIL DO
					IF a = hover THEN
						canvas.Fill(WMRectangles.MakeRect(w, 0, w + ItemWidth(a), bounds.GetHeight()), SHORT(0FFFF00FFH), WMGraphics.ModeCopy);
					END;
					s := menu.GetNodeCaption(a);
					img := menu.GetNodeImage(a);
					IF img # NIL THEN
						canvas.DrawImage(HMenuDistance DIV 2 + w, 0, img, WMGraphics.ModeSrcOverDst);
						w := w + img.width
					END;
					IF s # NIL THEN
						f.GetStringSize(s^, dx, dy); canvas.DrawString(HMenuDistance DIV 2 + w, dy, s^);
						w := w + dx
					END;
					INC(w, HMenuDistance);
					a := menu.GetNextSibling(a)
				END;
				menu.Release;
			ELSE
				menu.Acquire;
				a :=menu.GetChildren(root);
				WHILE a # NIL DO
					IF a = hover THEN
						canvas.Fill(WMRectangles.MakeRect(0, h, bounds.GetWidth(), h + ItemHeight(a)), SHORT(0FFFF00FFH), WMGraphics.ModeCopy);
					END;
					s := menu.GetNodeCaption(a);
					img := menu.GetNodeImage(a);
					dy := 0;
					IF img # NIL THEN
						canvas.DrawImage(0, h, img, WMGraphics.ModeSrcOverDst);
						dy := img.width
					END;
					IF s # NIL THEN
						f.GetStringSize(s^, dx, t); canvas.DrawString(0, h + f.ascent + VMenuDistance DIV 2, s^);
						INC(t, VMenuDistance);
						IF t > dy THEN dy := t END
					END;
					IF menu.GetChildren(a) # NIL THEN
						IF subMenuIndicatorImg # NIL THEN
							canvas.DrawImage(bounds.GetWidth() - subMenuIndicatorImg.width, 0, subMenuIndicatorImg, WMGraphics.ModeSrcOverDst)
						ELSE
							canvas.DrawString(bounds.GetWidth() - 10, h + f.ascent, "...")
						END
					END;
					h := h + dy;
					INC(w, HMenuDistance);
					a := menu.GetNextSibling(a)
				END;
				menu.Release;
			END;
			WMGraphicUtilities.DrawRect(canvas, bounds.Get(), WMGraphics.Black, WMGraphics.ModeCopy);
		END DrawBackground;

		(* caller must hold tree lock *)
		PROCEDURE ItemWidth(item : WMTrees.TreeNode) : LONGINT;
		VAR w, dx, dy : LONGINT;
			f : WMGraphics.Font;
			s : Strings.String;
			img : Raster.Image;
		BEGIN
			f := GetFont();
			w := 0;
			s := menu.GetNodeCaption(item);
			img := menu.GetNodeImage(item);
			IF s # NIL THEN f.GetStringSize(s^, dx, dy); w := w + dx END;
			IF img # NIL THEN w := w + img.width END;
			INC(w, HMenuDistance);
			RETURN w
		END ItemWidth;

		(* caller must hold tree lock *)
		PROCEDURE ItemHeight(item : WMTrees.TreeNode) : LONGINT;
		VAR t, dx, dy : LONGINT;
			f : WMGraphics.Font;
			s : Strings.String;
			img : Raster.Image;
		BEGIN
			f := GetFont();
			s := menu.GetNodeCaption(item);
			img := menu.GetNodeImage(item);
			dy := 0;
			IF img # NIL THEN dy := img.width END;
			IF s # NIL THEN f.GetStringSize(s^, dx, t); INC(t, VMenuDistance); IF t > dy THEN dy := t END END;
			RETURN dy
		END ItemHeight;

		PROCEDURE FindHorizontal(x : LONGINT) : WMTrees.TreeNode;
		VAR p : LONGINT;
			a : WMTrees.TreeNode;
		BEGIN
			p := 0;
			menu.Acquire;
			a :=menu.GetChildren(root);
			IF a # NIL THEN
				REPEAT
					p := p + ItemWidth(a);
					IF p < x THEN a := menu.GetNextSibling(a) END;
				UNTIL (a = NIL) OR (p >= x);
			END;
			menu.Release;
			RETURN a
		END FindHorizontal;

		PROCEDURE FindVertical(y : LONGINT) : WMTrees.TreeNode;
		VAR p : LONGINT;
			a : WMTrees.TreeNode;
		BEGIN
			p := 0;
			menu.Acquire;
			a :=menu.GetChildren(root);
			IF a # NIL THEN
				REPEAT
					p := p + ItemHeight(a);
					IF p < y THEN a := menu.GetNextSibling(a) END;
				UNTIL (a = NIL) OR (p >= y);
			END;
			menu.Release;
			RETURN a
		END FindVertical;

		PROCEDURE GetItemRect(i : WMTrees.TreeNode; VAR r : WMRectangles.Rectangle);
		VAR a : WMTrees.TreeNode;
		BEGIN
			menu.Acquire;
			a :=menu.GetChildren(root);
			r.l := 0; r.t := 0;
			WHILE (a # NIL) & (a # i) DO
				IF horizontal.Get() THEN	INC(r.l, ItemWidth(a))
				ELSE INC(r.t, ItemHeight(a))
				END;
				a := menu.GetNextSibling(a);
			END;
			IF a # NIL THEN r.r := r.l + ItemWidth(a); r.b := r.t + ItemHeight(a) END;
			menu.Release
		END GetItemRect;

		PROCEDURE PointerMove(x, y : LONGINT; keys : SET);
		VAR m : WMTrees.TreeNode;
		BEGIN
			IF horizontal.Get() THEN m := FindHorizontal(x)
			ELSE m := FindVertical(y)
			END;
			IF m # hover  THEN hover := m; Invalidate END;
		END PointerMove;

		PROCEDURE LeafSelect(item : WMTrees.TreeNode);
		BEGIN
			IF parentMenuPanel = NIL THEN
				IF subMenu # NIL THEN subMenu.CloseMenu(SELF, NIL); subMenu := NIL END;
				menuSelectEvent.Call(item)
			ELSE
				parentMenuPanel.LeafSelect(item);
			END
		END LeafSelect;

		PROCEDURE PointerDown(x, y : LONGINT; keys : SET);
		VAR m, s : WMTrees.TreeNode;
			r : WMRectangles.Rectangle;
		BEGIN
			IF horizontal.Get() THEN m := FindHorizontal(x)
			ELSE m := FindVertical(y)
			END;
			IF m # NIL THEN
				menu.Acquire;
				s := menu.GetChildren(m);
				IF s # NIL THEN
					GetItemRect(m, r);
					IF horizontal.Get() THEN
						IF openDirection.Get() IN {OpenUpLeft, OpenUpRight} THEN ToWMCoordinates(r.l, r.t, x, y)
						ELSE ToWMCoordinates(r.l, r.b, x, y)
						END
					ELSE
						CASE openDirection.Get() OF
							|OpenUpLeft : ToWMCoordinates(r.l, r.b, x, y)
							|OpenUpRight : ToWMCoordinates(r.r, r.b, x, y)
							|OpenDownLeft : ToWMCoordinates(r.l, r.t, x, y)
							|OpenDownRight : ToWMCoordinates(r.r, r.t, x, y)
						ELSE ToWMCoordinates(r.r, r.t, x, y)
						END;
					END;
					IF subMenu # NIL THEN subMenu.CloseMenu(SELF, NIL); subMenu := NIL END;
					NEW(subMenu, x, y, openDirection.Get(), menu, m, SELF);
					PointerLeave;
				ELSE
					LeafSelect(m)
				END;
				menu.Release;
			END;
		END PointerDown;

		PROCEDURE PointerLeave;
		BEGIN
			IF hover # NIL THEN hover := NIL; Invalidate END;
		END PointerLeave;

		PROCEDURE Finalize;
		BEGIN
			Finalize^;
			IF subMenu # NIL THEN subMenu.Close; subMenu := NIL END;
		END Finalize;

		PROCEDURE FocusLost;
		BEGIN
			IF subMenu # NIL THEN subMenu.Close; subMenu := NIL END;
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
	VAR menuPanel : MenuPanel;

		PROCEDURE &Open*(x, y : LONGINT; openDirection : LONGINT;  menu : WMTrees.Tree; root : WMTrees.TreeNode; parent : MenuPanel);
		VAR w, h, dx, dy : LONGINT;
		BEGIN
			NEW(menuPanel);
			menuPanel.SetParent(parent);
			menuPanel.fillColor.Set(WMGraphics.White);
			menuPanel.SetMenu(menu, root);
			menuPanel.Measure(w, h);
			IF h < 5 THEN h := 5 END; IF w < 5 THEN w := 5 END;
			menuPanel.bounds.SetExtents(w, h);
			CASE openDirection OF
				|OpenUpLeft : dx := -w; dy := -h
				|OpenUpRight : dy := -h
				|OpenDownLeft : dx := -w
			ELSE dx := 0; dy :=0
			END;
			menuPanel.openDirection.Set(openDirection);
			Init(menuPanel.bounds.GetWidth(), menuPanel.bounds.GetHeight(), FALSE);
			SetContent(menuPanel);
			AddWindow(SELF, x + dx, y + dy, {WMWindowManager.FlagNoFocus, WMWindowManager.FlagFrame, WMWindowManager.FlagHidden});
			IF manager.TransferPointer(SELF) THEN KernelLog.String("Pointer transferred "); KernelLog.Ln;  END;
		END Open;

		PROCEDURE CloseMenu(sender, data : ANY);
		BEGIN
			IF ~sequencer.IsCallFromSequencer() THEN
				sequencer.ScheduleEvent(SELF.CloseMenu, NIL, NIL)
			ELSE Close
			END
		END CloseMenu;

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
	KernelLog.String("Decorate");
	ASSERT((window.manager # NIL) & (window.manager.lock.HasWriteLock()));
	l := window.bounds.l; r := window.bounds.r; t := window.bounds.t; b := window.bounds.b;

	NEW(shadow, Right); window.rightW := shadow;
	shadow.bounds := WMRectangles.MakeRect(r, t + ShadowOffsetVertical, r + ShadowWidth, b + ShadowHeight);
	InitShadow(shadow);

	NEW(shadow, Bottom); window.bottomW := shadow;
	shadow.bounds := WMRectangles.MakeRect(l + ShadowOffsetHorizontal, b, r, b + ShadowHeight);
	InitShadow(shadow);
END ShadowDecorator;

BEGIN
	StrMenuPanel := Strings.NewString("MenuPanel");
END WMMenus.

