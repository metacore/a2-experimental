MODULE Models; (** AUTHOR "staubesv"; PURPOSE "Models"; *)

IMPORT
	Types, Strings, XML, Texts, TextUtilities, WMProperties, WMEvents, WMComponents;

CONST
	Ok* = Types.Ok;

	InitialStringSize = 128;

TYPE

	Model* = OBJECT(WMComponents.Component)
	VAR
		onChanged- : WMEvents.EventSource;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			NEW(onChanged, NIL, NIL, NIL, NIL); events.Add(onChanged);
		END Init;

		PROCEDURE SetGeneric*(CONST wrapper : Types.Wrapper; VAR res : LONGINT);
		BEGIN
			res := Types.CannotConvert;
		END SetGeneric;

		PROCEDURE GetGeneric*(VAR wrapper : Types.Wrapper; VAR res : LONGINT);
		BEGIN
			res := Types.CannotConvert;
		END GetGeneric;

		PROCEDURE Changed*; (** protected *)
		BEGIN
			onChanged.Call(SELF);
		END Changed;

	END Model;

TYPE

	Boolean* = OBJECT(Model)
	VAR
		value : BOOLEAN;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			SetNameAsString(StrBoolean);
			value := FALSE;
		END Init;

		PROCEDURE Set*(value : BOOLEAN);
		VAR changed : BOOLEAN;
		BEGIN
			BEGIN {EXCLUSIVE}
				changed := SELF.value # value;
				SELF.value := value;
			END;
			IF changed THEN Changed; END;
		END Set;

		PROCEDURE Get*() : BOOLEAN;
		BEGIN {EXCLUSIVE}
			RETURN value;
		END Get;

		PROCEDURE SetGeneric*(CONST wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : BOOLEAN;
		BEGIN
			Types.GetBoolean(wrapper, value, res);
			IF (res = Types.Ok) THEN Set(value); END;
		END SetGeneric;

		PROCEDURE GetGeneric*(VAR wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : BOOLEAN;
		BEGIN
			value := Get();
			Types.SetBoolean(wrapper, value, res);
		END GetGeneric;

	END Boolean;

TYPE

	Integer* = OBJECT(Model)
	VAR
		value : LONGINT;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			SetNameAsString(StrInteger);
			value := 0;
		END Init;

		PROCEDURE Set*(value : LONGINT);
		VAR changed : BOOLEAN;
		BEGIN
			BEGIN {EXCLUSIVE}
				changed := SELF.value # value;
				SELF.value := value;
			END;
			IF changed THEN Changed; END;
		END Set;

		PROCEDURE Get*() : LONGINT;
		BEGIN {EXCLUSIVE}
			RETURN value;
		END Get;

		PROCEDURE Add*(value : LONGINT);
		BEGIN
			IF (value # 0) THEN
				BEGIN {EXCLUSIVE}
					SELF.value := SELF.value + value;
				END;
				Changed;
			END;
		END Add;

		PROCEDURE SetGeneric*(CONST wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : LONGINT;
		BEGIN
			Types.GetInteger(wrapper, value, res);
			IF (res = Types.Ok) THEN Set(value); END;
		END SetGeneric;

		PROCEDURE GetGeneric*(VAR wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : LONGINT;
		BEGIN
			value := Get();
			Types.SetInteger(wrapper, value, res);
		END GetGeneric;

	END Integer;

TYPE

	BoundedInteger* = OBJECT(Integer)
	VAR
		min, max : WMProperties.Int32Property;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			SetNameAsString(StrBoundedInteger);
			NEW(min, PrototypeBiMin, NIL, NIL); properties.Add(min);
			NEW(max, PrototypeBiMax, NIL, NIL); properties.Add(max);
		END Init;

		PROCEDURE Set*(value : LONGINT);
		BEGIN {EXCLUSIVE}
			SELF.value := value;
		END Set;

	END BoundedInteger;

TYPE

	Real* = OBJECT(Model)
	VAR
		value : REAL;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			SetNameAsString(StrReal);
			value := 0.0;
		END Init;

		PROCEDURE Set*(value : REAL);
		VAR changed : BOOLEAN;
		BEGIN
			BEGIN {EXCLUSIVE}
				changed := SELF.value # value;
				SELF.value := value;
			END;
			IF changed THEN Changed; END;
		END Set;

		PROCEDURE Get*() : REAL;
		BEGIN {EXCLUSIVE}
			RETURN value;
		END Get;

		PROCEDURE SetGeneric*(CONST wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : REAL;
		BEGIN
			Types.GetReal(wrapper, value, res);
			IF (res = Types.Ok) THEN Set(value); END;
		END SetGeneric;

		PROCEDURE GetGeneric*(VAR wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : REAL;
		BEGIN
			value := Get();
			Types.SetReal(wrapper, value, res);
		END GetGeneric;

	END Real;

TYPE

	Longreal* = OBJECT(Model)
	VAR
		value : LONGREAL;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			SetNameAsString(StrLongreal);
			value := 0.0;
		END Init;

		PROCEDURE Set*(value : LONGREAL);
		VAR changed : BOOLEAN;
		BEGIN
			BEGIN {EXCLUSIVE}
				changed := SELF.value # value;
				SELF.value := value;
			END;
			IF changed THEN Changed; END;
		END Set;

		PROCEDURE Get*() : LONGREAL;
		BEGIN {EXCLUSIVE}
			RETURN value;
		END Get;

		PROCEDURE SetGeneric*(CONST wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : LONGREAL;
		BEGIN
			Types.GetLongreal(wrapper, value, res);
			IF (res = Types.Ok) THEN Set(value); END;
		END SetGeneric;

		PROCEDURE GetGeneric*(VAR wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : LONGREAL;
		BEGIN
			value := Get();
			Types.SetLongreal(wrapper, value, res);
		END GetGeneric;

	END Longreal;

TYPE

	Char* = OBJECT(Model)
	VAR
		value : CHAR;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			SetNameAsString(StrChar);
			value := 0X;
		END Init;

		PROCEDURE Set*(value : CHAR);
		VAR changed : BOOLEAN;
		BEGIN
			BEGIN {EXCLUSIVE}
				changed := SELF.value # value;
				SELF.value := value;
			END;
			IF changed THEN Changed; END;
		END Set;

		PROCEDURE Get*() : CHAR;
		BEGIN {EXCLUSIVE}
			RETURN value;
		END Get;

		PROCEDURE SetGeneric*(CONST wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : CHAR;
		BEGIN
			Types.GetChar(wrapper, value, res);
			IF (res = Types.Ok) THEN Set(value); END;
		END SetGeneric;

		PROCEDURE GetGeneric*(VAR wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : CHAR;
		BEGIN
			value := Get();
			Types.SetChar(wrapper, value, res);
		END GetGeneric;

	END Char;

TYPE

	(** 0X-terminated string (no Unicode support here! *)
	String* = OBJECT(Model)
	VAR
		value : Strings.String; (* {value # NIL} *)

		PROCEDURE &Init*;
		BEGIN
			Init^;
			NEW(value, InitialStringSize);
			SetNameAsString(StrString);
		END Init;

		PROCEDURE Set*(CONST value : ARRAY OF CHAR);
		VAR changed : BOOLEAN; length : LONGINT;
		BEGIN
			length := 0;
			WHILE (length < LEN(value)) & (value[length] # 0X) DO INC(length); END;
			BEGIN {EXCLUSIVE}
				IF (length > LEN(value)) THEN
					SELF.value := Strings.NewString(value);
					changed := TRUE;
				ELSE
					changed := SELF.value^ # value;
					IF changed THEN COPY(value, SELF.value^); END;
				END;
			END;
			ASSERT(SELF.value # NIL);
			IF changed THEN Changed; END;
		END Set;

		PROCEDURE Get*() : Strings.String;
		BEGIN {EXCLUSIVE}
			ASSERT(SELF.value # NIL);
			RETURN value;
		END Get;

		PROCEDURE GetAOC*(VAR value : ARRAY OF CHAR);
		BEGIN {EXCLUSIVE}
			COPY(SELF.value^, value);
		END GetAOC;

		PROCEDURE SetGeneric*(CONST wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : ARRAY 256 OF CHAR;
		BEGIN
			Types.GetString(wrapper, value, res);
			IF (res = Types.Ok) THEN Set(value); END;
		END SetGeneric;

		PROCEDURE GetGeneric*(VAR wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : Strings.String;
		BEGIN
			value := Get();
			Types.SetString(wrapper, value, res);
		END GetGeneric;

	END String;

TYPE

	Set* = OBJECT(Model)
	VAR
		value : SET;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			SetNameAsString(StrSet);
			value := {};
		END Init;

		PROCEDURE Set*(value : SET);
		VAR changed : BOOLEAN;
		BEGIN
			BEGIN {EXCLUSIVE}
				changed := SELF.value # value;
				SELF.value := value;
			END;
			IF changed THEN Changed; END;
		END Set;

		PROCEDURE Get*() : SET;
		BEGIN {EXCLUSIVE}
			RETURN value;
		END Get;

		PROCEDURE Include*(element : LONGINT);
		VAR changed : BOOLEAN;
		BEGIN
			BEGIN {EXCLUSIVE}
				changed := ~(element IN SELF.value);
				IF changed THEN INCL(SELF.value, element); END;
			END;
			IF changed THEN Changed(); END;
		END Include;

		PROCEDURE Exclude*(element : LONGINT);
		VAR changed : BOOLEAN;
		BEGIN
			BEGIN {EXCLUSIVE}
				changed := (element IN SELF.value);
				IF changed THEN EXCL(SELF.value, element); END;
			END;
			IF changed THEN Changed(); END;
		END Exclude;

		PROCEDURE IsInSet*(element : LONGINT) : BOOLEAN;
		BEGIN {EXCLUSIVE}
			RETURN element IN SELF.value;
		END IsInSet;

	END Set;

TYPE

	TextModel* = OBJECT(Model)
	VAR
		text : Texts.Text; (* {value # NIL} *)

		PROCEDURE &Init;
		BEGIN
			Init^;
			SetNameAsString(StrText);
			NEW(text);
		END Init;

		PROCEDURE Set*(text : Texts.Text);
		BEGIN {EXCLUSIVE}
			IF (text = NIL) THEN
				SELF.text.AcquireWrite;
				SELF.text.Delete(0, SELF.text.GetLength());
				SELF.text.ReleaseWrite;
			ELSE
				SELF.text.onTextChanged.Remove(OnTextChanged);
				SELF.text := text;
				SELF.text.onTextChanged.Add(OnTextChanged);
			END;
			ASSERT(text # NIL);
			Changed;
		END Set;

		PROCEDURE Get*() : Texts.Text;
		VAR text : Texts.Text;
		BEGIN {EXCLUSIVE}
			text := SELF.text;
			ASSERT(text # NIL);
			RETURN text;
		END Get;

		PROCEDURE OnTextChanged(sender, data : ANY);
		BEGIN
			Changed;
		END OnTextChanged;

		PROCEDURE SetAsString*(CONST string : ARRAY OF CHAR);
		BEGIN {EXCLUSIVE}
			SELF.text.AcquireWrite;
			SELF.text.Delete(0, SELF.text.GetLength());
			TextUtilities.StrToText(SELF.text, 0, string);
			SELF.text.ReleaseWrite;
		END SetAsString;

		PROCEDURE GetAsString*(VAR string : ARRAY OF CHAR);
		BEGIN {EXCLUSIVE}
			SELF.text.AcquireRead;
			TextUtilities.TextToStr(SELF.text, string);
			SELF.text.ReleaseRead;
		END GetAsString;

		PROCEDURE SetGeneric*(CONST wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR text : Texts.Text;
		BEGIN
			Types.GetText(wrapper, text, res);
			IF (res = Types.Ok) THEN Set(text); END;
		END SetGeneric;

		PROCEDURE GetGeneric*(VAR wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR text : Texts.Text;
		BEGIN
			text := Get();
			Types.SetText(wrapper, text, res);
		END GetGeneric;

	END TextModel;

(*
TYPE

	Container* = OBJECT(Model)
	VAR
		models : Model;

		PROCEDURE &Init;
		BEGIN
			Init^;
			SetNameAsString(StrContainer);
			models := NIL;
		END Init;

		PROCEDURE AddContent(content : XML.Content);
		VAR model : Model; oldLock : Locks.RWLock;
		BEGIN
			AddContent^(content);
			IF (content # NIL) & (content IS Model) THEN
				model := content(Model);
				IF (model.GetAttributeValue(AttributeName) # NIL) THEN
					ASSERT((model.parent = NIL) & (model.next = NIL) & (model.lock # NIL));
					model.lock.AcquireWrite;
					oldLock := model.lock;
					model.lock := SELF.lock;
					oldLock.ReleaseWrite;
					model.next := models;
					models := model;
				ELSE
					KernelLog.String("Warning: WMModels.Container.AddContent: Tried to add unnamed model to container");
					KernelLog.Ln;
				END;
			END;
		END AddContent;

		PROCEDURE AddAttribute(attribute : XML.Attribute);
		BEGIN
			AddAttribute^(attribute);
		END AddAttribute;

		PROCEDURE RemoveContent(content : XML.Content);
		VAR model, m : Model;
		BEGIN
			RemoveContent^(content);
			IF (content # NIL) & (content IS Model) THEN
				model := content(Model);
				IF (models = model) THEN
					models := model.next;
				ELSE
					m := models;
					WHILE (m # NIL) & (m.next # NIL) & (m.next # model) DO m := m.next; END;
					IF (m # NIL) THEN
						m.next := m.next.next;
					END;
				END;
				(* TODO: Exchange lock *)
				model.next := NIL;
				model.parent := NIL;
			END;
		END RemoveContent;

		PROCEDURE FindModel(CONST name : ARRAY OF CHAR) : Model;
		VAR model, result : Model; string : Strings.String;
		BEGIN
			KernelLog.String("FindModel: "); KernelLog.String(name); KernelLog.Ln;
			result := NIL;
			model := models;
			WHILE (result = NIL) & (model # NIL) DO
				string := model.GetAttributeValue(AttributeName);
				KernelLog.String("CompareTo : ");
				IF (string = NIL) THEN KernelLog.String("NIL");
				ELSE KernelLog.String(string^);
				END;
				KernelLog.Ln;
				IF (string # NIL) & (string^ =  name) THEN result := model; END;
				model := model.next;
			END;
			RETURN result;
		END FindModel;

		PROCEDURE FindModelByName(CONST fullname : ARRAY OF CHAR) : Model;
		VAR curModel : Model; name : ARRAY 32 OF CHAR; i, j : LONGINT; done : BOOLEAN;
		BEGIN
			curModel := SELF;
			done := FALSE;
			i := 0; j := 0;
			WHILE ~done & (curModel # NIL)  & (i < LEN(fullname)) & (j < LEN(name)) DO
				IF (fullname[i] = ".") OR (fullname[i] = 0X) THEN
					name[j] := 0X;
					IF (curModel IS Container) THEN
						curModel := curModel(Container).FindModel(name);
					ELSE
						curModel := NIL;
					END;
					done := (fullname[i] = 0X);
					j := 0;
				ELSE
					name[j] := fullname[i];
					INC(j);
				END;
				INC(i);
			END;
			RETURN curModel;
		END FindModelByName;

		PROCEDURE SetField*(CONST name : ARRAY OF CHAR; CONST wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR model : Model;
		BEGIN
			model := FindModelByName(name);
			IF (model # NIL) & ~(model IS Container) THEN
				IF (model IS IntegerModel) THEN KernelLog.String("INTEGER"); KernelLog.Ln; END;
				IF (wrapper IS String256) THEN KernelLog.String("String256"); KernelLog.Ln;ELSE KernelLog.String("OOPSS"); KernelLog.Ln; END;
				model.SetGeneric(wrapper, res);
			ELSE
				res := 192;
			END;
		END SetField;

		PROCEDURE GetField*(CONST name : ARRAY OF CHAR; VAR wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR model : Model;
		BEGIN
			model := FindModelByName(name);
			IF (model # NIL) & ~(model IS Container) THEN
				model.GetGeneric(wrapper, res);
			ELSE
				res := 192;
			END;
		END GetField;

	END Container;
*)

VAR
	PrototypeBiMin, PrototypeBiMax : WMProperties.Int32Property;
	StrBoolean, StrInteger, StrBoundedInteger, StrReal, StrLongreal, StrChar, StrString, StrSet, StrText, StrContainer : Strings.String;

PROCEDURE GenBoolean*() : XML.Element;
VAR boolean : Boolean;
BEGIN
	NEW(boolean); RETURN boolean;
END GenBoolean;

PROCEDURE GenInteger*() : XML.Element;
VAR integer : Integer;
BEGIN
	NEW(integer); RETURN integer;
END GenInteger;

PROCEDURE GenBoundedInteger*() : XML.Element;
VAR bi : BoundedInteger;
BEGIN
	NEW(bi); RETURN bi;
END GenBoundedInteger;

PROCEDURE GenReal*() : XML.Element;
VAR real : Real;
BEGIN
	NEW(real); RETURN real;
END GenReal;

PROCEDURE GenLongreal*() : XML.Element;
VAR longReal : Longreal;
BEGIN
	NEW(longReal); RETURN longReal;
END GenLongreal;

PROCEDURE GenChar*() : XML.Element;
VAR char : Char;
BEGIN
	NEW(char); RETURN char;
END GenChar;

PROCEDURE GenString*() : XML.Element;
VAR string : String;
BEGIN
	NEW(string); RETURN string;
END GenString;

PROCEDURE GenSet*() : XML.Element;
VAR set : Set;
BEGIN
	NEW(set); RETURN set;
END GenSet;

(*
PROCEDURE GenText*() : XML.Element;
VAR text : TextModel;
BEGIN
	NEW(text); RETURN text;
END GenText;

PROCEDURE GenContainer*() : XML.Element;
VAR container : Container;
BEGIN
	NEW(container); RETURN container;
END GenContainer;
*)

PROCEDURE InitPrototypes;
BEGIN
	NEW(PrototypeBiMin, NIL, Strings.NewString("Min"), Strings.NewString("Lower bound"));
	PrototypeBiMin.Set(MIN(LONGINT));
	NEW(PrototypeBiMax, NIL, Strings.NewString("Max"), Strings.NewString("Upper bounds"));
	PrototypeBiMax.Set(MAX(LONGINT));
END InitPrototypes;

PROCEDURE InitStrings;
BEGIN
	StrBoolean := Strings.NewString("Boolean");
	StrInteger := Strings.NewString("Integer");
	StrBoundedInteger := Strings.NewString("BoundedInteger");
	StrReal := Strings.NewString("Real");
	StrLongreal := Strings.NewString("Longreal");
	StrChar := Strings.NewString("Char");
	StrString := Strings.NewString("String");
	StrSet := Strings.NewString("Set");
	StrText := Strings.NewString("Text");
	StrContainer := Strings.NewString("Container");
END InitStrings;

BEGIN
	InitStrings;
	InitPrototypes;
END Models.
