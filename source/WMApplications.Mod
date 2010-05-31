MODULE WMApplications; (** AUTHOR "staubesv"; PURPOSE "Application Launcher"; *)

IMPORT
	KernelLog,
	Streams, Commands, Strings, XML, XMLObjects, Repositories,
	WMGraphics, WMComponents, WMMessages, WMRestorable, WMWindowManager;

CONST
	Ok = 0;
	RepositoryNotFound = 1;
	ApplicationNotFound = 2;
	ParseError = 3;

TYPE

	WindowInfo = RECORD
		title : Strings.String;
		icon : Strings.String;
		width, height : LONGINT;
		alpha : BOOLEAN;
	END;

	ApplicationInfo = RECORD
		repository : Repositories.Repository; (* {repository # NIL} *)
		name : Repositories.Name;
		content : WMComponents.VisualComponent;
		window : WindowInfo;
	END;

TYPE

	Window* = OBJECT (WMComponents.FormWindow)
	VAR
		name : Repositories.Name;
		repository : Repositories.Repository;

		PROCEDURE &New*(CONST info : ApplicationInfo; context : WMRestorable.Context);
		BEGIN
			ASSERT(info.repository # NIL);
			repository := info.repository;
			COPY(info.name, name);

			IF (context = NIL) THEN
				Init(info.window.width, info.window.height, info.window.alpha);
			ELSE
				Init(context.r - context.l, context.b - context.t, info.window.alpha);
			END;

			IF (info.content # NIL) THEN
				SetContent(info.content);
			END;

			IF (info.window.title # NIL) THEN
				SetTitle(info.window.title);
			END;

			IF (info.window.icon # NIL) THEN
				SetIcon(WMGraphics.LoadImage(info.window.icon^, TRUE));
			END;

			IF (context # NIL) THEN
				WMRestorable.AddByContext(SELF, context);
			ELSE
				WMWindowManager.DefaultAddWindow(SELF)
			END;
		END New;

		PROCEDURE Close;
		BEGIN
			Close^;
		END Close;

		PROCEDURE Handle(VAR x : WMMessages.Message);
		VAR data : XML.Element;
		BEGIN
			IF (x.msgType = WMMessages.MsgExt) & (x.ext # NIL) THEN
				IF (x.ext IS WMRestorable.Storage) THEN
					NEW(data); data.SetName("Data");
					data.SetAttributeValue("repository", repository.name);
					data.SetAttributeValue("name", repository.name);
					x.ext(WMRestorable.Storage).Add(name, "WMApplications.Restore", SELF, data);
				ELSE
					Handle^(x)
				END
			ELSE
				Handle^(x)
			END
		END Handle;

	END Window;

PROCEDURE Open*(context : Commands.Context);
VAR
	fullName, repositoryName, applicationName : ARRAY 128 OF CHAR;
	refNum, res : LONGINT;
	info : ApplicationInfo;
	window : Window;
BEGIN
	fullName := "";
	context.arg.GetString(fullName);
	IF Repositories.SplitName(fullName, repositoryName, applicationName, refNum) THEN
		res := GetApplicationInfo(repositoryName, applicationName, info);
		IF (res = Ok) THEN
			NEW(window, info, NIL);
		ELSIF (res = RepositoryNotFound) THEN
			context.error.String("Repository "); context.error.String(repositoryName);
			context.error.String(" not found."); context.error.Ln;
		ELSIF (res = ApplicationNotFound) THEN
			context.error.String("Application "); context.error.String(applicationName);
			context.error.String(" not found in repository "); context.error.String(repositoryName);
			context.error.Ln;
		ELSIF (res = ParseError) THEN
			context.error.String("Application parse error."); context.error.Ln;
		ELSE
			context.error.String("res = "); context.error.Int(res, 0); context.error.Ln;
		END;
	ELSE
		context.error.String(fullName); context.error.String(" not valid."); context.error.Ln;
	END;
END Open;

PROCEDURE Restore*(context : WMRestorable.Context);
VAR
	repositoryName, applicationName : Repositories.Name; string : Strings.String;
	window : Window;
	info : ApplicationInfo;
	writer : Streams.Writer;
	res : LONGINT;
BEGIN
	ASSERT((context # NIL) & (context.appData # NIL));
	string := context.appData.GetAttributeValue("repository");
	IF (string # NIL) THEN
		COPY(string^, repositoryName);
		string := context.appData.GetAttributeValue("name");
		IF (string # NIL) THEN
			COPY(string^, applicationName);
			res := GetApplicationInfo(repositoryName, applicationName, info);
			IF (res = Ok) THEN
				NEW(window, info, context);
			ELSE
				NEW(writer, KernelLog.Send, 128);
				ShowRes(res, repositoryName, applicationName, writer);
			END;
		ELSE
			KernelLog.String("WMApplications.Restore failed"); KernelLog.Ln;
		END;
	ELSE
		KernelLog.String("WMApplications.Restore failed"); KernelLog.Ln;
	END;
END Restore;

PROCEDURE ShowRes(res : LONGINT; CONST repositoryName, applicationName : ARRAY OF CHAR; out : Streams.Writer);
BEGIN
	ASSERT(out # NIL);
	CASE res OF
		| Ok:
			out.String("Ok");
		| RepositoryNotFound:
			out.String("Repository "); out.String(repositoryName); out.String(" not found."); out.Ln;
		| ApplicationNotFound:
			out.String("Application "); out.String(applicationName);
			out.String(" not found in repository "); out.String(repositoryName); out.Ln;
		| ParseError:
			out.String("Application parse error."); out.Ln;
	ELSE
		out.String("res = "); out.Int(res, 0); out.Ln;
	END;
	out.Update;
END ShowRes;

PROCEDURE GetApplicationInfo(CONST repositoryName, applicationName : ARRAY OF CHAR; VAR info : ApplicationInfo) : LONGINT;
VAR repository : Repositories.Repository; application : XML.Element; res : LONGINT;
BEGIN
	repository := Repositories.ThisRepository(repositoryName);
	IF (repository # NIL) THEN
		application := GetApplication(repository, applicationName);
		IF (application # NIL) THEN
			IF ParseApplication(applicationName, application, info) THEN info.repository := repository; res := Ok;
			ELSE res := ParseError;
			END;
		ELSE res := ApplicationNotFound;
		END;
	ELSE res := RepositoryNotFound;
	END;
	RETURN res;
END GetApplicationInfo;

PROCEDURE ParseApplication(CONST applicationName : ARRAY OF CHAR; CONST application : XML.Element; VAR applicationInfo : ApplicationInfo) : BOOLEAN;
VAR enumerator : XMLObjects.Enumerator; ptr : ANY; string : Strings.String; component : Repositories.Component; res : LONGINT;
BEGIN
	ASSERT(application # NIL);
	COPY(applicationName, applicationInfo.name);
	enumerator := application.GetContents();
	WHILE enumerator.HasMoreElements() DO
		ptr := enumerator.GetNext();
		IF (ptr # NIL) THEN
			IF (ptr IS XML.Element) THEN
				string := ptr(XML.Element).GetName();
				IF (string # NIL) & (string^ = "Window") THEN
					applicationInfo.window.title := ptr(XML.Element).GetAttributeValue("title");
					applicationInfo.window.icon := ptr(XML.Element).GetAttributeValue("icon");
					IF GetInteger(ptr(XML.Element), "width", applicationInfo.window.width) THEN END;
					IF GetInteger(ptr(XML.Element), "height", applicationInfo.window.height) THEN END;
					IF GetBoolean(ptr(XML.Element), "alpha", applicationInfo.window.alpha) THEN END;
				ELSE
					KernelLog.String("He2_??"); KernelLog.Ln;
				END;
			ELSIF (ptr IS XML.Chars) THEN
				KernelLog.String("Chars"); KernelLog.Ln;
				string := ptr(XML.Chars).GetStr();
				IF (string # NIL) THEN
					Repositories.GetComponentByString(string^, component, res);
					IF (res = Repositories.Ok) THEN
						IF (component IS WMComponents.VisualComponent) THEN
							applicationInfo.content := component(WMComponents.VisualComponent);
						ELSE
							KernelLog.String("Component is not a visual components."); KernelLog.Ln;
						END;
					ELSE
						KernelLog.String("Component not found"); KernelLog.Ln;
					END;
				END;
			ELSE
				KernelLog.String("HEEE??"); KernelLog.Ln;
			END;
		END;
	END;
	RETURN applicationInfo.content # NIL;
END ParseApplication;

PROCEDURE GetApplication(repository : Repositories.Repository; CONST applicationName : ARRAY OF CHAR) : XML.Element;
VAR result : XML.Element; enumerator : XMLObjects.Enumerator; ptr : ANY; string : Strings.String;
BEGIN
	ASSERT(repository # NIL);
	result := NIL;
	enumerator := repository.GetApplicationEnumerator();
	IF (enumerator # NIL) THEN
		WHILE (result = NIL) & enumerator.HasMoreElements() DO
			ptr := enumerator.GetNext();
			IF (ptr # NIL) & (ptr IS XML.Element) THEN
				string := ptr(XML.Element).GetName();
				IF (string # NIL) & (string^ = "Application") THEN
					string := ptr(XML.Element).GetAttributeValue("name");
					IF (string # NIL) & (string^ = applicationName) THEN
						result := ptr(XML.Element);
					END;
				END;
			END;
		END;
	END;
	RETURN result;
END GetApplication;

PROCEDURE GetInteger(element : XML.Element; CONST attributeName : ARRAY OF CHAR; VAR value : LONGINT) : BOOLEAN;
VAR string : Strings.String;
BEGIN
	ASSERT(element # NIL);
	string := element.GetAttributeValue(attributeName);
	IF (string # NIL) THEN
		Strings.StrToInt(string^, value);
	END;
	RETURN (string # NIL);
END GetInteger;

PROCEDURE GetBoolean(element : XML.Element; CONST attributeName : ARRAY OF CHAR; VAR value : BOOLEAN) : BOOLEAN;
VAR string : Strings.String;
BEGIN
	ASSERT(element # NIL);
	string := element.GetAttributeValue(attributeName);
	IF (string # NIL) THEN
		Strings.StrToBool(string^, value);
	END;
	RETURN (string # NIL);
END GetBoolean;

END WMApplications.

WMApplications.Open RepositoryName::ApplicationName ~

WMApplications.Open Test:Test:0 ~

SystemTools.Free WMApplications ~
