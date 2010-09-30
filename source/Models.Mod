MODULE Models; (** AUTHOR "staubesv"; PURPOSE "Models"; *)

IMPORT
	Locks, Types, Strings, XML, Texts, TextUtilities, Repositories, WMProperties, WMEvents;

CONST
	Ok* = Types.Ok;

	InitialStringSize = 128;

	AttributeName = "name";

TYPE

	Model* = OBJECT(Repositories.Component)
	VAR
		onChanged- : WMEvents.EventSource;
		changed : BOOLEAN;
		lock : Locks.RWLock;

		PROCEDURE &Init*; (** protected *)
		BEGIN
			Init^;
			NEW(onChanged, NIL, NIL, NIL, NIL);
			changed := FALSE;
			NEW(lock);
		END Init;

		PROCEDURE SetGeneric*(CONST wrapper : Types.Wrapper; VAR res : LONGINT); (** abstract *)
		END SetGeneric;

		PROCEDURE GetGeneric*(VAR wrapper : Types.Wrapper; VAR res : LONGINT); (** abstract *)
		END GetGeneric;

		PROCEDURE AcquireRead*;
		BEGIN
			lock.AcquireRead;
		END AcquireRead;

		PROCEDURE ReleaseRead*;
		BEGIN
			lock.ReleaseRead;
		END ReleaseRead;

		PROCEDURE HasReadLock*() : BOOLEAN;
		BEGIN
			RETURN lock.HasReadLock();
		END HasReadLock;

		PROCEDURE AcquireWrite*;
		BEGIN
			lock.AcquireWrite;
		END AcquireWrite;

		PROCEDURE ReleaseWrite*;
		VAR notifyListeners : BOOLEAN;
		BEGIN
			(* If the last writer releases the lock and the model data has changed, we have to notify interested listeners *)
			notifyListeners := (lock.GetWLockLevel() = 1) & changed;
			lock.ReleaseWrite;
			IF notifyListeners THEN
				onChanged.Call(SELF);
			END;
		END ReleaseWrite;

		PROCEDURE HasWriteLock*() : BOOLEAN;
		BEGIN
			RETURN lock.HasWriteLock();
		END HasWriteLock;

		(** 	Indicate that the value of the model has changed. Listeners will be notified when the writer lock
			is released *)
		PROCEDURE Changed*; (** protected *)
		BEGIN
			ASSERT(HasWriteLock());
			changed := TRUE;
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
		BEGIN
			AcquireWrite;
			IF (SELF.value # value) THEN Changed; END;
			SELF.value := value;
			ReleaseWrite;
		END Set;

		PROCEDURE Get*() : BOOLEAN;
		VAR value : BOOLEAN;
		BEGIN
			AcquireRead;
			value := SELF.value;
			ReleaseRead;
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
		BEGIN
			AcquireWrite;
			IF (SELF.value # value) THEN Changed; END;
			SELF.value := value;
			ReleaseWrite;
		END Set;

		PROCEDURE Get*() : LONGINT;
		VAR value : LONGINT;
		BEGIN
			AcquireRead;
			value := SELF.value;
			ReleaseRead;
			RETURN value;
		END Get;

		PROCEDURE Add*(value : LONGINT);
		BEGIN
			IF (value # 0) THEN
				AcquireWrite;
				SELF.value := SELF.value + value;
				Changed;
				ReleaseWrite;
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
		min, max : LONGINT;

		PROCEDURE &Init*;
		BEGIN
			Init^;
			SetNameAsString(StrBoundedInteger);
		END Init;

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
		BEGIN
			AcquireWrite;
			IF (SELF.value # value) THEN Changed; END;
			SELF.value := value;
			ReleaseWrite;
		END Set;

		PROCEDURE Get*() : REAL;
		VAR value : REAL;
		BEGIN
			AcquireRead;
			value := SELF.value;
			ReleaseRead;
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
		BEGIN
			AcquireWrite;
			IF (SELF.value # value) THEN Changed; END;
			SELF.value := value;
			ReleaseWrite;
		END Set;

		PROCEDURE Get*() : LONGREAL;
		VAR value : LONGREAL;
		BEGIN
			AcquireRead;
			value := SELF.value;
			ReleaseRead;
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
		BEGIN
			AcquireWrite;
			IF (SELF.value # value) THEN Changed; END;
			SELF.value := value;
			ReleaseWrite;
		END Set;

		PROCEDURE Get*() : CHAR;
		VAR value : CHAR;
		BEGIN
			AcquireRead;
			value := SELF.value;
			ReleaseRead;
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

		PROCEDURE Set*(value : Strings.String);
		BEGIN
			ASSERT(value # NIL); (*? CHECK *)
			AcquireWrite;
			IF (value # SELF.value) THEN Changed; END;
			SELF.value := value;
			ReleaseWrite;
		END Set;

		PROCEDURE Get*() : Strings.String;
		VAR value : Strings.String;
		BEGIN
			AcquireRead;
			value := SELF.value;
			ReleaseRead;
			ASSERT(value # NIL);
			RETURN value;
		END Get;

		PROCEDURE SetAOC*(CONST value : ARRAY OF CHAR);
		VAR length : LONGINT;
		BEGIN
			length := 0;
			WHILE (length < LEN(value)) & (value[length] # 0X) DO INC(length); END;
			AcquireWrite;
			IF (length > LEN(value)) THEN
				SELF.value := Strings.NewString(value);
				Changed;
			ELSIF (SELF.value^ # value) THEN
				COPY(value, SELF.value^);
				Changed;
			END;
			ASSERT(SELF.value # NIL);
			ReleaseWrite;
		END SetAOC;

		PROCEDURE GetAOC*(VAR value : ARRAY OF CHAR);
		BEGIN
			AcquireRead;
			COPY(SELF.value^, value);
			ReleaseRead;
		END GetAOC;

		PROCEDURE SetGeneric*(CONST wrapper : Types.Wrapper; VAR res : LONGINT);
		VAR value : Strings.String;
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
		BEGIN
			AcquireWrite;
			IF (SELF.value # value) THEN Changed; END;
			SELF.value := value;
			ReleaseWrite;
		END Set;

		PROCEDURE Get*() : SET;
		VAR value : SET;
		BEGIN
			AcquireRead;
			value := SELF.value;
			ReleaseRead;
			RETURN value;
		END Get;

		PROCEDURE Include*(element : LONGINT);
		BEGIN
			AcquireWrite;
			IF ~(element IN SELF.value) THEN
				INCL(SELF.value, element);
				Changed;
			END;
			ReleaseWrite;
		END Include;

		PROCEDURE Exclude*(element : LONGINT);
		BEGIN
			AcquireWrite;
			IF (element IN SELF.value) THEN
				EXCL(SELF.value, element);
				Changed;
			END;
			ReleaseWrite;
		END Exclude;

		PROCEDURE Contains*(element : LONGINT) : BOOLEAN;
		VAR result : BOOLEAN;
		BEGIN
			AcquireRead;
			result := element IN SELF.value;
			ReleaseRead;
			RETURN result;
		END Contains;

	END Set;

TYPE

	Text* = OBJECT(Model)
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

	END Text;

TYPE

	Container* = OBJECT(Model)

		PROCEDURE &Init;
		BEGIN
			Init^;
			SetNameAsString(StrContainer);
		END Init;

		PROCEDURE FindModel(CONST name : ARRAY OF CHAR) : Model;
		VAR result : Model; string : Strings.String; content : XML.Content;
		BEGIN
			result := NIL;
			(*? locking!!! *)
			content := GetFirst();
			WHILE (result = NIL) & (content # NIL) DO
				IF (content IS Model) THEN
					string := content(Model).GetAttributeValue(AttributeName);
					IF (string # NIL) & (string^ = name) THEN result := content(Model); END;
				END;
				content := GetNext(content);
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

PROCEDURE GenText*() : XML.Element;
VAR text : Text;
BEGIN
	NEW(text); RETURN text;
END GenText;

PROCEDURE GenContainer*() : XML.Element;
VAR container : Container;
BEGIN
	NEW(container); RETURN container;
END GenContainer;

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
