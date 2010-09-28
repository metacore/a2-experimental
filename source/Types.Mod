MODULE Types; (** AUTHOR "staubesv"; PURPOSE "Generic types and type conversion"; *)

IMPORT
	Strings, Texts, TextUtilities, Repositories;

CONST

	(*
		res > Ok: Could convert but maybe lost precision / truncated string
		res = Ok; Conversion succeeded with no loss of precision
		res < Ok; Conversion errors
	*)
	Ok* = 0;

	Truncated* = 1;
	CannotConvert* = -10;
	ConversionError* = -11;
	TruncatedError* = -12; (* string truncation leads to error *)
	CannotRead* = -20;
	CannotWrite* = -21;
	TargetIsNIL* = -30;

TYPE

	Wrapper* = RECORD END;

	(** Basic types *)

	Boolean* = RECORD(Wrapper)
		value* : BOOLEAN;
	END;

	Integer* = RECORD(Wrapper)
		value* : LONGINT;
	END;

	Real* = RECORD(Wrapper)
		value* : REAL;
	END;

	Longreal* = RECORD(Wrapper)
		value* : LONGREAL;
	END;

	Char* = RECORD(Wrapper)
		value* : CHAR;
	END;

	String32* = RECORD(Wrapper)
		value* : ARRAY 32 OF CHAR;
	END;

	String256* = RECORD(Wrapper)
		value* : ARRAY 256 OF CHAR;
	END;

	String* = RECORD(Wrapper)
		value* : Strings.String; (* {value # NIL} ??? *)
	END;

	Set* = RECORD(Wrapper)
		value* : SET;
	END;

	Text* = RECORD(Wrapper)
		value* : Texts.Text;
	END;

	Object* = RECORD(Wrapper)
		value* : Repositories.Component;
	END;

TYPE

	(** Generic types *)

	GenericWrapper* = RECORD(Wrapper)
		Get* : Getter;
		Set* : Setter;
	END;

	(** Read value into wrapper *)
	Getter* = PROCEDURE {DELEGATE} (CONST self : GenericWrapper; VAR wrapper : Wrapper; VAR res : LONGINT);

	(** Store value into wrapper *)
	Setter* = PROCEDURE {DELEGATE} (CONST self : GenericWrapper; CONST wrapper : Wrapper; VAR res : LONGINT);

PROCEDURE GetBoolean*(CONST wrapper : Wrapper; VAR value : BOOLEAN; VAR res : LONGINT);
VAR temp : ARRAY 2 OF CHAR; boolean : Boolean;
BEGIN
	res := Ok;
	IF (wrapper IS Boolean) THEN
		value := wrapper(Boolean).value;
	ELSIF (wrapper IS Char) THEN
		temp[0] := wrapper(Char).value;
		temp[1] := 0X;
		Strings.StrToBool(temp, value);
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			Strings.StrToBool(wrapper(String).value^, value);
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		Strings.StrToBool(wrapper(String32).value, value);
	ELSIF (wrapper IS String256) THEN
		Strings.StrToBool(wrapper(String256).value, value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Get # NIL) THEN
			wrapper(GenericWrapper).Get(wrapper(GenericWrapper), boolean, res);
			IF (res = Ok) THEN
				value := boolean.value;
			END;
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetBoolean;

PROCEDURE SetBoolean*(VAR wrapper : Wrapper; value : BOOLEAN; VAR res : LONGINT);
VAR temp : ARRAY 2 OF CHAR; boolean : Boolean;
BEGIN
	res := Ok;
	IF (wrapper IS Boolean) THEN
		wrapper(Boolean).value := value;
	ELSIF (wrapper IS Char) THEN
		Strings.BoolToStr(value, temp);
		wrapper(Char).value := temp[0];
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			Strings.BoolToStr(value, wrapper(String).value^);
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		Strings.BoolToStr(value, wrapper(String32).value);
	ELSIF (wrapper IS String256) THEN
		Strings.BoolToStr(value, wrapper(String256).value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Set # NIL) THEN
			boolean.value := value;
			wrapper(GenericWrapper).Set(wrapper(GenericWrapper), boolean, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetBoolean;

PROCEDURE GetInteger*(CONST wrapper : Wrapper; VAR value : LONGINT; VAR res : LONGINT);
VAR integer : Integer;
BEGIN
	res := Ok;
	IF (wrapper IS Integer) THEN
		value := wrapper(Integer).value;
	ELSIF (wrapper IS Real) THEN
		value := ENTIER(wrapper(Real).value);
	ELSIF (wrapper IS Longreal) THEN
		value := ENTIER(wrapper(Longreal).value);
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			Strings.StrToInt(wrapper(String).value^, value);
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		Strings.StrToInt(wrapper(String32).value, value);
	ELSIF (wrapper IS String256) THEN
		Strings.StrToInt(wrapper(String256).value, value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Get # NIL) THEN
			wrapper(GenericWrapper).Get(wrapper(GenericWrapper), integer, res);
			IF (res = Ok) THEN
				value := integer.value;
			END;
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetInteger;

PROCEDURE SetInteger*(VAR wrapper : Wrapper; value : LONGINT;  VAR res : LONGINT);
VAR integer : Integer;
BEGIN
	res := Ok;
	IF (wrapper IS Integer) THEN
		wrapper(Integer).value := value;
	ELSIF (wrapper IS Real) THEN
		wrapper(Real).value := value;
	ELSIF (wrapper IS Longreal) THEN
		wrapper(Longreal).value := value;
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			Strings.IntToStr(value, wrapper(String).value^);
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		Strings.IntToStr(value, wrapper(String32).value);
	ELSIF (wrapper IS String256) THEN
		Strings.IntToStr(value, wrapper(String256).value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Set # NIL) THEN
			integer.value := value;
			wrapper(GenericWrapper).Set(wrapper(GenericWrapper), integer, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetInteger;

PROCEDURE GetReal*(CONST wrapper : Wrapper; VAR value : REAL; VAR res : LONGINT);
VAR longreal : LONGREAL; real : Real;
BEGIN
	res := Ok;
	IF (wrapper IS Real) THEN
		value := wrapper(Real).value;
	ELSIF (wrapper IS Longreal) THEN
		value := SHORT(wrapper(Longreal).value);
	ELSIF (wrapper IS Integer) THEN
		value := wrapper(Integer).value;
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			Strings.StrToFloat(wrapper(String).value^, longreal);
			value := SHORT(longreal);
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		Strings.StrToFloat(wrapper(String32).value, longreal);
		value := SHORT(longreal);
	ELSIF (wrapper IS String256) THEN
		Strings.StrToFloat(wrapper(String256).value, longreal);
		value := SHORT(longreal);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Get # NIL) THEN
			wrapper(GenericWrapper).Get(wrapper(GenericWrapper), real, res);
			IF (res = Ok) THEN
				value := real.value;
			END;
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetReal;

PROCEDURE SetReal*(VAR wrapper : Wrapper; value : REAL; VAR res : LONGINT);
VAR real : Real;
BEGIN
	res := Ok;
	IF (wrapper IS Real) THEN
		wrapper(Real).value := value;
	ELSIF (wrapper IS Longreal) THEN
		wrapper(Longreal).value := value;
	ELSIF (wrapper IS Integer) THEN
		wrapper(Integer).value := ENTIER(value);
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			Strings.FloatToStr(value, 0, 1, 0, wrapper(String).value^);
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		Strings.FloatToStr(value, 0, 1, 0, wrapper(String32).value);
	ELSIF (wrapper IS String256) THEN
		Strings.FloatToStr(value, 0, 1, 0, wrapper(String256).value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Set # NIL) THEN
			real.value := value;
			wrapper(GenericWrapper).Set(wrapper(GenericWrapper), real, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetReal;

PROCEDURE GetLongreal*(CONST wrapper : Wrapper; VAR value : LONGREAL; VAR res : LONGINT);
VAR longreal : Longreal;
BEGIN
	res := Ok;
	IF (wrapper IS Longreal) THEN
		value := wrapper(Longreal).value;
	ELSIF (wrapper IS Real) THEN
		value := wrapper(Real).value;
	ELSIF (wrapper IS Integer) THEN
		value := wrapper(Integer).value;
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			Strings.StrToFloat(wrapper(String).value^, value);
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		Strings.StrToFloat(wrapper(String32).value, value);
	ELSIF (wrapper IS String256) THEN
		Strings.StrToFloat(wrapper(String256).value, value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Get # NIL) THEN
			wrapper(GenericWrapper).Get(wrapper(GenericWrapper), longreal, res);
			IF (res = Ok) THEN
				value := longreal.value;
			END;
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetLongreal;

PROCEDURE SetLongreal*(VAR wrapper : Wrapper; value : LONGREAL; VAR res : LONGINT);
VAR longreal : Longreal;
BEGIN
	res := Ok;
	IF (wrapper IS Longreal) THEN
		wrapper(Longreal).value := value;
	ELSIF (wrapper IS Real) THEN
		wrapper(Real).value := SHORT(value);
	ELSIF (wrapper IS Integer) THEN
		wrapper(Integer).value := ENTIER(value);
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			Strings.FloatToStr(value, 0, 0, 0, wrapper(String).value^);
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		Strings.FloatToStr(value, 0, 0, 0, wrapper(String32).value);
	ELSIF (wrapper IS String256) THEN
		Strings.FloatToStr(value, 0, 0, 0, wrapper(String256).value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Set # NIL) THEN
			longreal.value := value;
			wrapper(GenericWrapper).Set(wrapper(GenericWrapper), longreal, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetLongreal;

PROCEDURE GetChar*(CONST wrapper : Wrapper; VAR value : CHAR; VAR res : LONGINT);
VAR string : ARRAY 8 OF CHAR; char : Char;
BEGIN
	res := Ok;
	IF (wrapper IS Char) THEN
		value := wrapper(Char).value;
	ELSIF (wrapper IS Boolean) THEN
		Strings.BoolToStr(wrapper(Boolean).value, string);
		value := string[0];
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			value := wrapper(String).value[0];
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		value := wrapper(String32).value[0];
	ELSIF (wrapper IS String256) THEN
		value := wrapper(String256).value[0];
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Get # NIL) THEN
			wrapper(GenericWrapper).Get(wrapper(GenericWrapper), char, res);
			IF (res = Ok) THEN
				value := char.value;
			END;
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetChar;

PROCEDURE SetChar*(VAR wrapper : Wrapper; value : CHAR; VAR res : LONGINT);
VAR temp : ARRAY 2 OF CHAR; char : Char;
BEGIN
	res := Ok;
	IF (wrapper IS Char) THEN
		wrapper(Char).value := value;
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) & (LEN(wrapper(String).value) >= 2) THEN
			wrapper(String).value[0] := value;
			wrapper(String).value[1] := 0X;
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		wrapper(String32).value[0] := value;
		wrapper(String32).value[1] := 0X;
	ELSIF (wrapper IS String256) THEN
		wrapper(String256).value[0] := value;
		wrapper(String256).value[1] := 0X;
	ELSIF (wrapper IS Boolean) THEN
		temp[0] := value;
		temp[1] := 0X;
		Strings.StrToBool(temp, wrapper(Boolean).value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Set # NIL) THEN
			char.value := value;
			wrapper(GenericWrapper).Set(wrapper(GenericWrapper), char, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetChar;

PROCEDURE GetAOC*(CONST wrapper : Wrapper; VAR value : ARRAY OF CHAR; VAR res : LONGINT);
BEGIN
	res := Ok;
	IF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			COPY(wrapper(String).value^, value);
			IF (Strings.Length(wrapper(String).value^) >= LEN(value)) THEN
				res := Truncated;
			END;
		ELSE
			value := "";
		END;
	ELSIF (wrapper IS String32) THEN
		COPY(wrapper(String32).value, value);
	ELSIF (wrapper IS String256) THEN
		COPY(wrapper(String256).value, value);
	ELSIF (wrapper IS Boolean) THEN
		Strings.BoolToStr(wrapper(Boolean).value, value);
	ELSIF (wrapper IS Integer) THEN
		Strings.IntToStr(wrapper(Integer).value, value);
	ELSIF (wrapper IS Real) THEN
		(* TODO *)
	ELSIF (wrapper IS Longreal) THEN
		(* TODO *)
	ELSIF (wrapper IS Char) THEN
		value[0] := wrapper(Char).value;
		value[1] := 0X;
	ELSIF (wrapper IS Object) THEN
		ComponentToString(wrapper(Object).value, value, res);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Get # NIL) THEN
			(* TBD *)
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetAOC;

PROCEDURE SetAOC*(VAR wrapper : Wrapper; CONST value : ARRAY OF CHAR; VAR res : LONGINT);
VAR temp : LONGREAL; string : String;
BEGIN
	res := Ok;
	IF (wrapper IS String) THEN
		wrapper(String).value := Strings.NewString(value); (*? most likely not what we want *)
	ELSIF (wrapper IS String32) THEN
		COPY(value, wrapper(String32).value);
	ELSIF (wrapper IS String256) THEN
		COPY(value, wrapper(String256).value);
	ELSIF (wrapper IS Boolean) THEN
		Strings.StrToBool(value, wrapper(Boolean).value);
	ELSIF (wrapper IS Integer) THEN
		Strings.StrToInt(value, wrapper(Integer).value);
	ELSIF (wrapper IS Real) THEN
		Strings.StrToFloat(value, temp);
		wrapper(Real).value := SHORT(temp);
	ELSIF (wrapper IS Char) THEN
		wrapper(Char).value := value[0];
	ELSIF (wrapper IS Object) THEN
		StringToComponent(value, wrapper(Object).value, res);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Set # NIL) THEN
			string.value := Strings.NewString(value); (*? !!! *)
			wrapper(GenericWrapper).Set(wrapper(GenericWrapper), string, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetAOC;

PROCEDURE GetString*(CONST wrapper : Wrapper; VAR string : Strings.String; VAR res : LONGINT);
VAR value : ARRAY 64 OF CHAR; (*? !!! *)
BEGIN
	res := Ok;
	IF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			COPY(wrapper(String).value^, value);
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		COPY(wrapper(String32).value, value);
	ELSIF (wrapper IS String256) THEN
		COPY(wrapper(String256).value, value);
	ELSIF (wrapper IS Boolean) THEN
		Strings.BoolToStr(wrapper(Boolean).value, value);
	ELSIF (wrapper IS Integer) THEN
		Strings.IntToStr(wrapper(Integer).value, value);
	ELSIF (wrapper IS Real) THEN
		(* TODO *)
	ELSIF (wrapper IS Longreal) THEN
		(* TODO *)
	ELSIF (wrapper IS Char) THEN
		value[0] := wrapper(Char).value;
		value[1] := 0X;
	ELSIF (wrapper IS Object) THEN
		ComponentToString(wrapper(Object).value, value, res);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Get # NIL) THEN
			(* TBD *)
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetString;

PROCEDURE SetString*(VAR wrapper : Wrapper; value : Strings.String; VAR res : LONGINT);
BEGIN
	IF (value # NIL) THEN
		SetAOC(wrapper, value^, res);
	ELSIF (wrapper IS String) THEN
		wrapper(String).value := value;
		res := Ok;
	ELSE (*? semantics *)
		res := CannotConvert;
	END;
END SetString;

PROCEDURE GetSet*(CONST wrapper : Wrapper; VAR value : SET; VAR res : LONGINT);
VAR set : Set;
BEGIN
	res := Ok;
	IF (wrapper IS Set) THEN
		value := wrapper(Set).value;
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			Strings.StrToSet(wrapper(String).value^, value);
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		Strings.StrToSet(wrapper(String32).value, value);
	ELSIF (wrapper IS String256) THEN
		Strings.StrToSet(wrapper(String256).value, value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Get # NIL) THEN
			wrapper(GenericWrapper).Get(wrapper(GenericWrapper), set, res);
			IF (res = Ok) THEN
				value := set.value;
			END;
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetSet;

PROCEDURE SetSet*(VAR wrapper : Wrapper; value : SET; VAR res : LONGINT);
VAR temp : ARRAY 32 OF CHAR; set : Set;
BEGIN
	res := Ok;
	IF (wrapper IS Set) THEN
		wrapper(Set).value := value;
	ELSIF (wrapper IS String) THEN
		Strings.SetToStr(value, temp);
		wrapper(String).value := Strings.NewString(temp);
	ELSIF (wrapper IS String32) THEN
		Strings.SetToStr(value, wrapper(String32).value);
	ELSIF (wrapper IS String256) THEN
		Strings.SetToStr(value, wrapper(String256).value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Set # NIL) THEN
			set.value := value;
			wrapper(GenericWrapper).Set(wrapper(GenericWrapper), set, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetSet;

PROCEDURE GetText*(CONST wrapper : Wrapper; VAR value : Texts.Text; VAR res : LONGINT);
VAR
	temp : ARRAY 64 OF CHAR;
	text : Text;

	PROCEDURE SetAsString(CONST string : ARRAY OF CHAR);
	BEGIN
		IF (value = NIL) THEN
			NEW(value);
			value.AcquireWrite;
		ELSE
			value.AcquireWrite;
			value.Delete(0, value.GetLength());
		END;
		value.InsertUTF8(0, string);
		value.ReleaseWrite;
	END SetAsString;

BEGIN
	res := Ok;
	IF (wrapper IS Text) THEN
		value := wrapper(Text).value;
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			SetAsString(wrapper(String).value^);
		ELSE
			SetAsString(""); (*? semantics? *)
		END;
	ELSIF (wrapper IS String32) THEN
		SetAsString(wrapper(String32).value);
	ELSIF (wrapper IS String256) THEN
		SetAsString(wrapper(String256).value);
	ELSIF (wrapper IS Integer) THEN
		Strings.IntToStr(wrapper(Integer).value, temp);
		SetAsString(temp);
	ELSIF (wrapper IS Boolean) THEN
		Strings.BoolToStr(wrapper(Boolean).value, temp);
		SetAsString(temp);
	ELSIF (wrapper IS Set) THEN
		Strings.SetToStr(wrapper(Set).value, temp);
		SetAsString(temp);
	ELSIF (wrapper IS Char) THEN
		temp[0] := wrapper(Char).value;
		temp[1] := 0X;
		SetAsString(temp);
	ELSIF (wrapper IS Real) THEN
		Strings.FloatToStr(wrapper(Real).value, 20, 8, 10, temp);
		SetAsString(temp);
	ELSIF (wrapper IS Longreal) THEN
		Strings.FloatToStr(wrapper(Longreal).value, 20, 8, 10, temp);
		SetAsString(temp);
	ELSIF (wrapper IS Object) THEN
		ComponentToString(wrapper(Object).value, temp, res);
		IF (res = Ok) THEN
			SetAsString(temp);
		END;
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Get # NIL) THEN
			wrapper(GenericWrapper).Get(wrapper(GenericWrapper), text, res);
			IF (res = Ok) THEN
				value := text.value;
			END;
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetText;

PROCEDURE SetText*(VAR wrapper : Wrapper; CONST value : Texts.Text; VAR res : LONGINT);
VAR text : Text; temp : ARRAY 64 OF CHAR; lr : LONGREAL;
BEGIN
	res := Ok;
	IF (wrapper IS Text) THEN
		wrapper(Text).value := value;
	ELSIF (wrapper IS String) THEN
		IF (wrapper(String).value # NIL) THEN
			TextUtilities.TextToStr(value, wrapper(String).value^); (*? no valid result code, e.g. truncation *)
		ELSE
			res := ConversionError;
		END;
	ELSIF (wrapper IS String32) THEN
		TextUtilities.TextToStr(value, wrapper(String32).value); (*? no valid result code, e.g. truncation *)
	ELSIF (wrapper IS String256) THEN
		TextUtilities.TextToStr(value, wrapper(String256).value); (*? no valid result code, e.g. truncation *)
	ELSIF (wrapper IS Integer) THEN
		TextUtilities.TextToStr(value, temp);
		Strings.StrToInt(temp, wrapper(Integer).value);
	ELSIF (wrapper IS Boolean) THEN
		TextUtilities.TextToStr(value, temp);
		Strings.StrToBool(temp, wrapper(Boolean).value);
	ELSIF (wrapper IS Set) THEN
		TextUtilities.TextToStr(value, temp);
		Strings.StrToSet(temp, wrapper(Set).value);
	ELSIF (wrapper IS Real) THEN
		TextUtilities.TextToStr(value, temp);
		Strings.StrToFloat(temp, lr);
		wrapper(Real).value := SHORT(lr);
	ELSIF (wrapper IS Longreal) THEN
		TextUtilities.TextToStr(value, temp);
		Strings.StrToFloat(temp, wrapper(Longreal).value);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Set # NIL) THEN
			text.value := value;
			wrapper(GenericWrapper).Set(wrapper(GenericWrapper), text, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetText;

PROCEDURE GetObject*(CONST wrapper : Wrapper; VAR value : Repositories.Component; VAR res : LONGINT);
VAR object : Object;
BEGIN
	res := Ok;
	IF (wrapper IS Object) THEN
		value := wrapper(Object).value;
	ELSIF (wrapper IS String32) THEN
		StringToComponent(wrapper(String32).value, value, res);
	ELSIF (wrapper IS String256) THEN
		StringToComponent(wrapper(String256).value, value, res);
	ELSIF (wrapper IS String) THEN
		(*? TBD Check for NIL *)
		StringToComponent(wrapper(String).value^, value, res);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Get # NIL) THEN
			wrapper(GenericWrapper).Get(wrapper(GenericWrapper), object, res);
			IF (res = Ok) THEN
				value := object.value;
			END;
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetObject;

(*? TBD Check for NIL *)
PROCEDURE SetObject*(VAR wrapper : Wrapper; CONST value : Repositories.Component; VAR res : LONGINT);
VAR object : Object;
BEGIN
	res := Ok;
	IF (wrapper IS Object) THEN
		wrapper(Object).value := value;
	ELSIF (wrapper IS String32) THEN
		ComponentToString(value, wrapper(String32).value, res);
	ELSIF (wrapper IS String256) THEN
		ComponentToString(value, wrapper(String256).value, res);
	ELSIF (wrapper IS String) THEN
		ComponentToString(value, wrapper(String).value^, res);
	ELSIF (wrapper IS GenericWrapper) THEN
		IF (wrapper(GenericWrapper).Set # NIL) THEN
			object.value := value;
			wrapper(GenericWrapper).Set(wrapper(GenericWrapper), object, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetObject;

(* Helper procedures *)

PROCEDURE StringToComponent(CONST string : ARRAY OF CHAR; VAR component : Repositories.Component; VAR res : LONGINT);
VAR repositoryName, componentName : ARRAY 64 OF CHAR; componentID : LONGINT;
BEGIN
	component := NIL;
	IF Repositories.SplitName(string, repositoryName, componentName, componentID) THEN
		Repositories.GetComponent(repositoryName, componentName, componentID, component, res);
	ELSE
		res := 99; (*? TBD *)
	END;
END StringToComponent;

PROCEDURE ComponentToString(CONST component : Repositories.Component; VAR string : ARRAY OF CHAR; VAR res : LONGINT);
VAR repository : Repositories.Repository; componentName : Repositories.Name; nbr : ARRAY 16 OF CHAR; componentID : LONGINT;
BEGIN
	string := "";
	IF (component # NIL) THEN
		component.GetRepository(repository, componentName, componentID);
		IF (repository # NIL) THEN
			Strings.IntToStr(componentID, nbr);
			IF (Strings.Length(repository.name) + 1 + Strings.Length(componentName) + 1 + Strings.Length(nbr) + 1 <= LEN(string)) THEN
				COPY(repository.name, string);
				Strings.Append(string, Repositories.Delimiter);
				Strings.Append(string, componentName);
				Strings.Append(string, Repositories.Delimiter);
				Strings.Append(string, nbr);
				res := Ok;
			ELSE
				res := TruncatedError;
			END;
		ELSE
			res := 99; (*? TBD *)
		END;
	ELSE
		res := 99; (*? TBD *)
	END;
END ComponentToString;

END Types.
