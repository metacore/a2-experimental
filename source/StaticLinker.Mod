MODULE StaticLinker;	(* AUTHOR "negelef"; PURPOSE "Static Object File Linker"; *)

IMPORT Commands, Options, Diagnostics, Files, GenericLinker, ObjectFile;

TYPE Data = POINTER TO ARRAY OF CHAR;

TYPE Arrangement* = OBJECT (GenericLinker.Arrangement);
	VAR
		size, displacement: LONGINT;
		data: Data;

	PROCEDURE & InitArrangement (displacement: LONGINT);
	BEGIN size := 0; SELF.displacement := displacement; NEW (data, 1024);
	END InitArrangement;

	PROCEDURE Allocate* (CONST section: ObjectFile.Section): GenericLinker.Address;
	VAR address: GenericLinker.Address; new: Data; i: LONGINT;
	BEGIN
		address := size;
		IF section.alignment # 0 THEN INC (address, (section.alignment - address MOD section.alignment) MOD section.alignment); END;
		size := address + section.size;
		IF size > LEN (data) THEN
			NEW (new, size * 2);
			FOR i := 0 TO LEN (data) - 1 DO new[i] := data[i]; END;
			data := new;
		END;
		FOR i := 0 TO section.size - 1 DO data[address + i] := section.data[i]; END;
		RETURN address;
	END Allocate;

END Arrangement;

TYPE FileFormat = PROCEDURE (arrangement: Arrangement; writer: Files.Writer);

PROCEDURE ReadObjectFile (CONST moduleName, path, extension: Files.FileName; linker: GenericLinker.Linker);
VAR fileName: Files.FileName; file: Files.File; reader: Files.Reader;
BEGIN
	IF path # "" THEN Files.JoinPath (path, moduleName, fileName); ELSE fileName := moduleName; END;
	Files.JoinExtension (fileName, extension, fileName);
	file := Files.Old (fileName);
	IF file = NIL THEN linker.Error (fileName, "failed to open file"); RETURN; END;
	Files.OpenReader (reader, file, 0);
	GenericLinker.Process (reader, linker);
	IF reader.res # Files.Ok THEN linker.Error (fileName, "failed to parse"); ELSIF ~linker.error THEN linker.Information (fileName, "processed"); END;
END ReadObjectFile;

PROCEDURE WriteOutputFile (arrangement: Arrangement; CONST fileName: Files.FileName; linker: GenericLinker.Linker; fileFormat: FileFormat);
VAR file: Files.File; writer: Files.Writer;
BEGIN
	file := Files.New (fileName);
	Files.OpenWriter (writer, file, 0);
	fileFormat (arrangement, writer);
	writer.Update; Files.Register (file);
	linker.Information (fileName, "written");
END WriteOutputFile;

PROCEDURE WriteBinaryFile (arrangement: Arrangement; writer: Files.Writer);
VAR i: LONGINT;
BEGIN FOR i := 0 TO arrangement.size - 1 DO writer.Char (arrangement.data[i]); END;
END WriteBinaryFile;

PROCEDURE WriteTRMFile (arrangement: Arrangement; writer: Files.Writer; nibbles: LONGINT);
VAR i: LONGINT; nibble: INTEGER;
BEGIN
	FOR i := 0 TO arrangement.size * 2 - 1 DO
		IF (i # 0) & (i MOD nibbles = 0) THEN writer.Ln; END;
		IF ODD (i) THEN nibble := ORD (arrangement.data[i DIV 2]) MOD 16; ELSE nibble := ORD (arrangement.data[i DIV 2]) DIV 16; END;
		writer.Char (ObjectFile.NibbleToCharacter (nibble));
	END;
	writer.Ln;
END WriteTRMFile;

PROCEDURE WriteTRMCodeFile (arrangement: Arrangement; writer: Files.Writer);
BEGIN WriteTRMFile (arrangement, writer, 9);
END WriteTRMCodeFile;

PROCEDURE WriteTRMDataFile (arrangement: Arrangement; writer: Files.Writer);
BEGIN WriteTRMFile (arrangement, writer, 8);
END WriteTRMDataFile;

PROCEDURE GetFileFormat (options: Options.Options; CONST name: Options.Name; default: FileFormat): FileFormat;
VAR format: ARRAY 10 OF CHAR;
BEGIN
	IF ~options.GetString (name, format) THEN RETURN default;
	ELSIF format = "TRMCode" THEN RETURN WriteTRMCodeFile;
	ELSIF format = "TRMData" THEN RETURN WriteTRMDataFile;
	ELSE RETURN default; END;
END GetFileFormat;

PROCEDURE Link* (context: Commands.Context);
VAR options: Options.Options;
	verbose: BOOLEAN;
	codeFileFormat, dataFileFormat: FileFormat;
	codeDisplacement, dataDisplacement: LONGINT;
	path, extension, codeFileName, dataFileName, moduleName: Files.FileName;
	diagnostics: Diagnostics.StreamDiagnostics; code, data: Arrangement; linker: GenericLinker.Linker;
BEGIN
	NEW (options);
	options.Add ('v', "verbose", Options.Flag);
	options.Add (0X, "path", Options.String); options.Add (0X, "extension", Options.String);
	options.Add (0X, "fileName", Options.String); options.Add (0X, "dataFileName", Options.String);
	options.Add (0X, "displacement", Options.Integer); options.Add (0X, "dataDisplacement", Options.Integer);
	options.Add (0X, "fileFormat", Options.String); options.Add (0X, "dataFileFormat", Options.String);
	IF ~options.Parse (context.arg, context.error) THEN context.result := Commands.CommandParseError; RETURN; END;
	verbose := options.GetFlag ("verbose");
	IF ~options.GetString ("path", path) THEN path := ""; END;
	IF ~options.GetString ("extension", extension) THEN extension := ObjectFile.DefaultExtension; END;
	IF ~options.GetString ("fileName", codeFileName) THEN codeFileName := "linker.bin"; END;
	IF ~options.GetString ("dataFileName", dataFileName) THEN dataFileName := codeFileName; END;
	IF ~options.GetInteger ("displacement", codeDisplacement) THEN codeDisplacement := 0; END;
	IF ~options.GetInteger ("dataDisplacement", codeDisplacement) THEN dataDisplacement := codeDisplacement; END;
	codeFileFormat := GetFileFormat (options, "fileFormat", WriteBinaryFile);
	dataFileFormat := GetFileFormat (options, "dataFileFormat", codeFileFormat);

	NEW (code, codeDisplacement);
	IF codeFileName # dataFileName THEN NEW (data, dataDisplacement); ELSE data := code; END;
	NEW (diagnostics, context.error); NEW (linker, diagnostics, verbose, code, data);

	context.arg.GetString (moduleName);
	WHILE ~linker.error & (context.arg.res = Files.Ok) DO
		ReadObjectFile (moduleName, path, extension, linker); context.arg.GetString (moduleName);
	END;

	IF linker.Link () THEN
		WriteOutputFile (code, codeFileName, linker, codeFileFormat);
		IF data # code THEN WriteOutputFile (data, dataFileName, linker, dataFileFormat); END;
	END;

	IF linker.error THEN context.result := Commands.CommandError; END;
END Link;

END StaticLinker.;

Compiler.Compile --objectFile=Generic Test.Mod ~

SystemTools.Free StaticLinker GenericLinker ObjectFile ~
StaticLinker.Link --verbose --fileName=test.bin --fileFormat=TRMCode Test ~

