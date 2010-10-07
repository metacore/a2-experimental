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

	Any* = RECORD END;

	(** Basic types *)

	Boolean* = RECORD(Any)
		value* : BOOLEAN;
	END;

	Integer* = RECORD(Any)
		value* : LONGINT;
	END;

	Real* = RECORD(Any)
		value* : REAL;
	END;

	Longreal* = RECORD(Any)
		value* : LONGREAL;
	END;

	Char* = RECORD(Any)
		value* : CHAR;
	END;

	String32* = RECORD(Any)
		value* : ARRAY 32 OF CHAR;
	END;

	String256* = RECORD(Any)
		value* : ARRAY 256 OF CHAR;
	END;

	String* = RECORD(Any)
		value* : Strings.String; (* {value # NIL} ??? *)
	END;

	Set* = RECORD(Any)
		value* : SET;
	END;

	Text* = RECORD(Any)
		value* : Texts.Text;
	END;

	Object* = RECORD(Any)
		value* : Repositories.Component;
	END;

TYPE

	(** Generic types *)

	Generic* = RECORD(Any)
		Get* : Getter;
		Set* : Setter;
	END;

	(** Read value into source *)
	Getter* = PROCEDURE {DELEGATE} (CONST self : Generic; VAR value : Any; VAR res : LONGINT);

	(** Store value into source *)
	Setter* = PROCEDURE {DELEGATE} (CONST self : Generic; CONST value : Any; VAR res : LONGINT);

PROCEDURE GetBoolean*(CONST source : Any; VAR value : BOOLEAN; VAR res : LONGINT);
VAR temp : ARRAY 2 OF CHAR; boolean : Boolean;
BEGIN
	res := Ok;
	IF (source IS Boolean) THEN
		value := source(Boolean).value;
	ELSIF (source IS Char) THEN
		temp[0] := source(Char).value;
		temp[1] := 0X;
		Strings.StrToBool(temp, value);
	ELSIF (source IS String) THEN
		IF (source(String).value # NIL) THEN
			Strings.StrToBool(source(String).value^, value);
		ELSE
			res := ConversionError;
		END;
	ELSIF (source IS String32) THEN
		Strings.StrToBool(source(String32).value, value);
	ELSIF (source IS String256) THEN
		Strings.StrToBool(source(String256).value, value);
	ELSIF (source IS Generic) THEN
		IF (source(Generic).Get # NIL) THEN
			source(Generic).Get(source(Generic), boolean, res);
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

PROCEDURE SetBoolean*(VAR target : Any; value : BOOLEAN; VAR res : LONGINT);
VAR temp : ARRAY 2 OF CHAR; boolean : Boolean;
BEGIN
	res := Ok;
	IF (target IS Boolean) THEN
		target(Boolean).value := value;
	ELSIF (target IS Char) THEN
		Strings.BoolToStr(value, temp);
		target(Char).value := temp[0];
	ELSIF (target IS String) THEN
		IF (target(String).value # NIL) THEN
			Strings.BoolToStr(value, target(String).value^);
		ELSE
			res := ConversionError;
		END;
	ELSIF (target IS String32) THEN
		Strings.BoolToStr(value, target(String32).value);
	ELSIF (target IS String256) THEN
		Strings.BoolToStr(value, target(String256).value);
	ELSIF (target IS Generic) THEN
		IF (target(Generic).Set # NIL) THEN
			boolean.value := value;
			target(Generic).Set(target(Generic), boolean, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetBoolean;

PROCEDURE GetInteger*(CONST source : Any; VAR value : LONGINT; VAR res : LONGINT);
VAR integer : Integer;
BEGIN
	res := Ok;
	IF (source IS Integer) THEN
		value := source(Integer).value;
	ELSIF (source IS Real) THEN
		value := ENTIER(source(Real).value);
	ELSIF (source IS Longreal) THEN
		value := ENTIER(source(Longreal).value);
	ELSIF (source IS String) THEN
		IF (source(String).value # NIL) THEN
			Strings.StrToInt(source(String).value^, value);
		ELSE
			res := ConversionError;
		END;
	ELSIF (source IS String32) THEN
		Strings.StrToInt(source(String32).value, value);
	ELSIF (source IS String256) THEN
		Strings.StrToInt(source(String256).value, value);
	ELSIF (source IS Generic) THEN
		IF (source(Generic).Get # NIL) THEN
			source(Generic).Get(source(Generic), integer, res);
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

PROCEDURE SetInteger*(VAR target : Any; value : LONGINT;  VAR res : LONGINT);
VAR integer : Integer;
BEGIN
	res := Ok;
	IF (target IS Integer) THEN
		target(Integer).value := value;
	ELSIF (target IS Real) THEN
		target(Real).value := value;
	ELSIF (target IS Longreal) THEN
		target(Longreal).value := value;
	ELSIF (target IS String) THEN
		IF (target(String).value # NIL) THEN
			Strings.IntToStr(value, target(String).value^);
		ELSE
			res := ConversionError;
		END;
	ELSIF (target IS String32) THEN
		Strings.IntToStr(value, target(String32).value);
	ELSIF (target IS String256) THEN
		Strings.IntToStr(value, target(String256).value);
	ELSIF (target IS Generic) THEN
		IF (target(Generic).Set # NIL) THEN
			integer.value := value;
			target(Generic).Set(target(Generic), integer, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetInteger;

PROCEDURE GetReal*(CONST source : Any; VAR value : REAL; VAR res : LONGINT);
VAR longreal : LONGREAL; real : Real;
BEGIN
	res := Ok;
	IF (source IS Real) THEN
		value := source(Real).value;
	ELSIF (source IS Longreal) THEN
		value := SHORT(source(Longreal).value);
	ELSIF (source IS Integer) THEN
		value := source(Integer).value;
	ELSIF (source IS String) THEN
		IF (source(String).value # NIL) THEN
			Strings.StrToFloat(source(String).value^, longreal);
			value := SHORT(longreal);
		ELSE
			res := ConversionError;
		END;
	ELSIF (source IS String32) THEN
		Strings.StrToFloat(source(String32).value, longreal);
		value := SHORT(longreal);
	ELSIF (source IS String256) THEN
		Strings.StrToFloat(source(String256).value, longreal);
		value := SHORT(longreal);
	ELSIF (source IS Generic) THEN
		IF (source(Generic).Get # NIL) THEN
			source(Generic).Get(source(Generic), real, res);
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

PROCEDURE SetReal*(VAR target : Any; value : REAL; VAR res : LONGINT);
VAR real : Real;
BEGIN
	res := Ok;
	IF (target IS Real) THEN
		target(Real).value := value;
	ELSIF (target IS Longreal) THEN
		target(Longreal).value := value;
	ELSIF (target IS Integer) THEN
		target(Integer).value := ENTIER(value);
	ELSIF (target IS String) THEN
		IF (target(String).value # NIL) THEN
			Strings.FloatToStr(value, 0, 1, 0, target(String).value^);
		ELSE
			res := ConversionError;
		END;
	ELSIF (target IS String32) THEN
		Strings.FloatToStr(value, 0, 1, 0, target(String32).value);
	ELSIF (target IS String256) THEN
		Strings.FloatToStr(value, 0, 1, 0, target(String256).value);
	ELSIF (target IS Generic) THEN
		IF (target(Generic).Set # NIL) THEN
			real.value := value;
			target(Generic).Set(target(Generic), real, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetReal;

PROCEDURE GetLongreal*(CONST source : Any; VAR value : LONGREAL; VAR res : LONGINT);
VAR longreal : Longreal;
BEGIN
	res := Ok;
	IF (source IS Longreal) THEN
		value := source(Longreal).value;
	ELSIF (source IS Real) THEN
		value := source(Real).value;
	ELSIF (source IS Integer) THEN
		value := source(Integer).value;
	ELSIF (source IS String) THEN
		IF (source(String).value # NIL) THEN
			Strings.StrToFloat(source(String).value^, value);
		ELSE
			res := ConversionError;
		END;
	ELSIF (source IS String32) THEN
		Strings.StrToFloat(source(String32).value, value);
	ELSIF (source IS String256) THEN
		Strings.StrToFloat(source(String256).value, value);
	ELSIF (source IS Generic) THEN
		IF (source(Generic).Get # NIL) THEN
			source(Generic).Get(source(Generic), longreal, res);
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

PROCEDURE SetLongreal*(VAR target : Any; value : LONGREAL; VAR res : LONGINT);
VAR longreal : Longreal;
BEGIN
	res := Ok;
	IF (target IS Longreal) THEN
		target(Longreal).value := value;
	ELSIF (target IS Real) THEN
		target(Real).value := SHORT(value);
	ELSIF (target IS Integer) THEN
		target(Integer).value := ENTIER(value);
	ELSIF (target IS String) THEN
		IF (target(String).value # NIL) THEN
			Strings.FloatToStr(value, 0, 0, 0, target(String).value^);
		ELSE
			res := ConversionError;
		END;
	ELSIF (target IS String32) THEN
		Strings.FloatToStr(value, 0, 0, 0, target(String32).value);
	ELSIF (target IS String256) THEN
		Strings.FloatToStr(value, 0, 0, 0, target(String256).value);
	ELSIF (target IS Generic) THEN
		IF (target(Generic).Set # NIL) THEN
			longreal.value := value;
			target(Generic).Set(target(Generic), longreal, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetLongreal;

PROCEDURE GetChar*(CONST source : Any; VAR value : CHAR; VAR res : LONGINT);
VAR string : ARRAY 8 OF CHAR; char : Char;
BEGIN
	res := Ok;
	IF (source IS Char) THEN
		value := source(Char).value;
	ELSIF (source IS Boolean) THEN
		Strings.BoolToStr(source(Boolean).value, string);
		value := string[0];
	ELSIF (source IS String) THEN
		IF (source(String).value # NIL) THEN
			value := source(String).value[0];
		ELSE
			res := ConversionError;
		END;
	ELSIF (source IS String32) THEN
		value := source(String32).value[0];
	ELSIF (source IS String256) THEN
		value := source(String256).value[0];
	ELSIF (source IS Generic) THEN
		IF (source(Generic).Get # NIL) THEN
			source(Generic).Get(source(Generic), char, res);
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

PROCEDURE SetChar*(VAR target : Any; value : CHAR; VAR res : LONGINT);
VAR temp : ARRAY 2 OF CHAR; char : Char;
BEGIN
	res := Ok;
	IF (target IS Char) THEN
		target(Char).value := value;
	ELSIF (target IS String) THEN
		IF (target(String).value # NIL) & (LEN(target(String).value) >= 2) THEN
			target(String).value[0] := value;
			target(String).value[1] := 0X;
		ELSE
			res := ConversionError;
		END;
	ELSIF (target IS String32) THEN
		target(String32).value[0] := value;
		target(String32).value[1] := 0X;
	ELSIF (target IS String256) THEN
		target(String256).value[0] := value;
		target(String256).value[1] := 0X;
	ELSIF (target IS Boolean) THEN
		temp[0] := value;
		temp[1] := 0X;
		Strings.StrToBool(temp, target(Boolean).value);
	ELSIF (target IS Generic) THEN
		IF (target(Generic).Set # NIL) THEN
			char.value := value;
			target(Generic).Set(target(Generic), char, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetChar;

PROCEDURE GetAOC*(CONST source : Any; VAR value : ARRAY OF CHAR; VAR res : LONGINT);
BEGIN
	res := Ok;
	IF (source IS String) THEN
		IF (source(String).value # NIL) THEN
			COPY(source(String).value^, value);
			IF (Strings.Length(source(String).value^) >= LEN(value)) THEN
				res := Truncated;
			END;
		ELSE
			value := "";
		END;
	ELSIF (source IS String32) THEN
		COPY(source(String32).value, value);
	ELSIF (source IS String256) THEN
		COPY(source(String256).value, value);
	ELSIF (source IS Boolean) THEN
		Strings.BoolToStr(source(Boolean).value, value);
	ELSIF (source IS Integer) THEN
		Strings.IntToStr(source(Integer).value, value);
	ELSIF (source IS Real) THEN
		(* TODO *)
	ELSIF (source IS Longreal) THEN
		(* TODO *)
	ELSIF (source IS Char) THEN
		value[0] := source(Char).value;
		value[1] := 0X;
	ELSIF (source IS Object) THEN
		ComponentToString(source(Object).value, value, res);
	ELSIF (source IS Generic) THEN
		IF (source(Generic).Get # NIL) THEN
			(* TBD *)
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetAOC;

PROCEDURE SetAOC*(VAR target : Any; CONST value : ARRAY OF CHAR; VAR res : LONGINT);
VAR temp : LONGREAL; string : String;
BEGIN
	res := Ok;
	IF (target IS String) THEN
		target(String).value := Strings.NewString(value); (*? most likely not what we want *)
	ELSIF (target IS String32) THEN
		COPY(value, target(String32).value);
	ELSIF (target IS String256) THEN
		COPY(value, target(String256).value);
	ELSIF (target IS Boolean) THEN
		Strings.StrToBool(value, target(Boolean).value);
	ELSIF (target IS Integer) THEN
		Strings.StrToInt(value, target(Integer).value);
	ELSIF (target IS Real) THEN
		Strings.StrToFloat(value, temp);
		target(Real).value := SHORT(temp);
	ELSIF (target IS Char) THEN
		target(Char).value := value[0];
	ELSIF (target IS Object) THEN
		StringToComponent(value, target(Object).value, res);
	ELSIF (target IS Generic) THEN
		IF (target(Generic).Set # NIL) THEN
			string.value := Strings.NewString(value); (*? !!! *)
			target(Generic).Set(target(Generic), string, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetAOC;

PROCEDURE GetString*(CONST source : Any; VAR string : Strings.String; VAR res : LONGINT);
VAR value : ARRAY 64 OF CHAR; (*? !!! *)
BEGIN
	res := Ok;
	IF (source IS String) THEN
		IF (source(String).value # NIL) THEN
			COPY(source(String).value^, value);
		ELSE
			res := ConversionError;
		END;
	ELSIF (source IS String32) THEN
		COPY(source(String32).value, value);
	ELSIF (source IS String256) THEN
		COPY(source(String256).value, value);
	ELSIF (source IS Boolean) THEN
		Strings.BoolToStr(source(Boolean).value, value);
	ELSIF (source IS Integer) THEN
		Strings.IntToStr(source(Integer).value, value);
	ELSIF (source IS Real) THEN
		(* TODO *)
	ELSIF (source IS Longreal) THEN
		(* TODO *)
	ELSIF (source IS Char) THEN
		value[0] := source(Char).value;
		value[1] := 0X;
	ELSIF (source IS Object) THEN
		ComponentToString(source(Object).value, value, res);
	ELSIF (source IS Generic) THEN
		IF (source(Generic).Get # NIL) THEN
			(* TBD *)
		ELSE
			res := CannotRead;
		END;
	ELSE
		res := CannotConvert;
	END;
END GetString;

PROCEDURE SetString*(VAR target : Any; value : Strings.String; VAR res : LONGINT);
BEGIN
	IF (value # NIL) THEN
		SetAOC(target, value^, res);
	ELSIF (target IS String) THEN
		target(String).value := value;
		res := Ok;
	ELSE (*? semantics *)
		res := CannotConvert;
	END;
END SetString;

PROCEDURE GetSet*(CONST source : Any; VAR value : SET; VAR res : LONGINT);
VAR set : Set;
BEGIN
	res := Ok;
	IF (source IS Set) THEN
		value := source(Set).value;
	ELSIF (source IS String) THEN
		IF (source(String).value # NIL) THEN
			Strings.StrToSet(source(String).value^, value);
		ELSE
			res := ConversionError;
		END;
	ELSIF (source IS String32) THEN
		Strings.StrToSet(source(String32).value, value);
	ELSIF (source IS String256) THEN
		Strings.StrToSet(source(String256).value, value);
	ELSIF (source IS Generic) THEN
		IF (source(Generic).Get # NIL) THEN
			source(Generic).Get(source(Generic), set, res);
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

PROCEDURE SetSet*(VAR target : Any; value : SET; VAR res : LONGINT);
VAR temp : ARRAY 32 OF CHAR; set : Set;
BEGIN
	res := Ok;
	IF (target IS Set) THEN
		target(Set).value := value;
	ELSIF (target IS String) THEN
		Strings.SetToStr(value, temp);
		target(String).value := Strings.NewString(temp);
	ELSIF (target IS String32) THEN
		Strings.SetToStr(value, target(String32).value);
	ELSIF (target IS String256) THEN
		Strings.SetToStr(value, target(String256).value);
	ELSIF (target IS Generic) THEN
		IF (target(Generic).Set # NIL) THEN
			set.value := value;
			target(Generic).Set(target(Generic), set, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetSet;

PROCEDURE GetText*(CONST source : Any; VAR value : Texts.Text; VAR res : LONGINT);
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
	IF (source IS Text) THEN
		value := source(Text).value;
	ELSIF (source IS String) THEN
		IF (source(String).value # NIL) THEN
			SetAsString(source(String).value^);
		ELSE
			SetAsString(""); (*? semantics? *)
		END;
	ELSIF (source IS String32) THEN
		SetAsString(source(String32).value);
	ELSIF (source IS String256) THEN
		SetAsString(source(String256).value);
	ELSIF (source IS Integer) THEN
		Strings.IntToStr(source(Integer).value, temp);
		SetAsString(temp);
	ELSIF (source IS Boolean) THEN
		Strings.BoolToStr(source(Boolean).value, temp);
		SetAsString(temp);
	ELSIF (source IS Set) THEN
		Strings.SetToStr(source(Set).value, temp);
		SetAsString(temp);
	ELSIF (source IS Char) THEN
		temp[0] := source(Char).value;
		temp[1] := 0X;
		SetAsString(temp);
	ELSIF (source IS Real) THEN
		Strings.FloatToStr(source(Real).value, 20, 8, 10, temp);
		SetAsString(temp);
	ELSIF (source IS Longreal) THEN
		Strings.FloatToStr(source(Longreal).value, 20, 8, 10, temp);
		SetAsString(temp);
	ELSIF (source IS Object) THEN
		ComponentToString(source(Object).value, temp, res);
		IF (res = Ok) THEN
			SetAsString(temp);
		END;
	ELSIF (source IS Generic) THEN
		IF (source(Generic).Get # NIL) THEN
			source(Generic).Get(source(Generic), text, res);
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

PROCEDURE SetText*(VAR target : Any; CONST value : Texts.Text; VAR res : LONGINT);
VAR text : Text; temp : ARRAY 64 OF CHAR; lr : LONGREAL;
BEGIN
	res := Ok;
	IF (target IS Text) THEN
		target(Text).value := value;
	ELSIF (target IS String) THEN
		IF (target(String).value # NIL) THEN
			TextUtilities.TextToStr(value, target(String).value^); (*? no valid result code, e.g. truncation *)
		ELSE
			res := ConversionError;
		END;
	ELSIF (target IS String32) THEN
		TextUtilities.TextToStr(value, target(String32).value); (*? no valid result code, e.g. truncation *)
	ELSIF (target IS String256) THEN
		TextUtilities.TextToStr(value, target(String256).value); (*? no valid result code, e.g. truncation *)
	ELSIF (target IS Integer) THEN
		TextUtilities.TextToStr(value, temp);
		Strings.StrToInt(temp, target(Integer).value);
	ELSIF (target IS Boolean) THEN
		TextUtilities.TextToStr(value, temp);
		Strings.StrToBool(temp, target(Boolean).value);
	ELSIF (target IS Set) THEN
		TextUtilities.TextToStr(value, temp);
		Strings.StrToSet(temp, target(Set).value);
	ELSIF (target IS Real) THEN
		TextUtilities.TextToStr(value, temp);
		Strings.StrToFloat(temp, lr);
		target(Real).value := SHORT(lr);
	ELSIF (target IS Longreal) THEN
		TextUtilities.TextToStr(value, temp);
		Strings.StrToFloat(temp, target(Longreal).value);
	ELSIF (target IS Generic) THEN
		IF (target(Generic).Set # NIL) THEN
			text.value := value;
			target(Generic).Set(target(Generic), text, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetText;

PROCEDURE GetObject*(CONST source : Any; VAR value : Repositories.Component; VAR res : LONGINT);
VAR object : Object;
BEGIN
	res := Ok;
	IF (source IS Object) THEN
		value := source(Object).value;
	ELSIF (source IS String32) THEN
		StringToComponent(source(String32).value, value, res);
	ELSIF (source IS String256) THEN
		StringToComponent(source(String256).value, value, res);
	ELSIF (source IS String) THEN
		(*? TBD Check for NIL *)
		StringToComponent(source(String).value^, value, res);
	ELSIF (source IS Generic) THEN
		IF (source(Generic).Get # NIL) THEN
			source(Generic).Get(source(Generic), object, res);
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
PROCEDURE SetObject*(VAR target : Any; CONST value : Repositories.Component; VAR res : LONGINT);
VAR object : Object;
BEGIN
	res := Ok;
	IF (target IS Object) THEN
		target(Object).value := value;
	ELSIF (target IS String32) THEN
		ComponentToString(value, target(String32).value, res);
	ELSIF (target IS String256) THEN
		ComponentToString(value, target(String256).value, res);
	ELSIF (target IS String) THEN
		ComponentToString(value, target(String).value^, res);
	ELSIF (target IS Generic) THEN
		IF (target(Generic).Set # NIL) THEN
			object.value := value;
			target(Generic).Set(target(Generic), object, res);
		ELSE
			res := CannotWrite;
		END;
	ELSE
		res := CannotConvert;
	END;
END SetObject;

PROCEDURE Assign*(VAR to : Any; CONST from : Any; VAR res : LONGINT);
VAR string : String;
BEGIN
	IF (from IS Boolean) THEN
		SetBoolean(to, from(Boolean).value, res);
	ELSIF (from IS Integer) THEN
		SetInteger(to, from(Integer).value, res);
	ELSIF (from IS Real) THEN
		SetReal(to, from(Real).value, res);
	ELSIF (from IS Longreal) THEN
		SetLongreal(to, from(Longreal).value, res);
	ELSIF (from IS Char) THEN
		SetChar(to, from(Char).value, res);
	ELSIF (from IS String32) THEN
		SetAOC(to, from(String32).value, res);
	ELSIF (from IS String256) THEN
		SetAOC(to, from(String256).value, res);
	ELSIF (from IS String) THEN
		SetString(to, from(String).value, res);
	ELSIF (from IS Set) THEN
		SetSet(to, from(Set).value, res);
	ELSIF (from IS Text )THEN
		SetText(to, from(Text).value, res);
	ELSIF (from IS Object) THEN
		SetObject(to, from(Object).value, res);
	ELSIF (from IS Generic) THEN
		IF (from(Generic).Get # NIL) THEN
			from(Generic).Get(from(Generic), string, res);
			IF ( res = Ok) THEN
				SetString(to, string.value, res);
			END;
		ELSE
			res := CannotRead;
		END;
	END;
END Assign;

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
