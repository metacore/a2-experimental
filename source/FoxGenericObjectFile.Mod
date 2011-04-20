MODULE FoxGenericObjectFile; (** AUTHOR "negelef"; PURPOSE "Generic Object File Writer"; *)

IMPORT
	Streams, Commands, Basic := FoxBasic, Formats := FoxFormats, Sections := FoxSections, IntermediateCode := FoxIntermediateCode,
	SyntaxTree := FoxSyntaxTree, BinaryCode := FoxBinaryCode,
	FingerPrinter := FoxFingerPrinter, Files, Options, ObjectFile, Diagnostics, SymbolFileFormat := FoxTextualSymbolFile, KernelLog, D := Debugging;

CONST
	version = 0;
	Trace = FALSE;

TYPE ObjectFileFormat* = OBJECT (Formats.ObjectFileFormat)
	VAR prefix, extension: Files.FileName; binary: BOOLEAN;

		PROCEDURE Export* (module: Formats.GeneratedModule; symbolFileFormat: Formats.SymbolFileFormat): BOOLEAN;
		VAR fileName: Files.FileName; file: Files.File; writer: Files.Writer; fingerPrinter: FingerPrinter.FingerPrinter;

			PROCEDURE ExportSection (section: IntermediateCode.Section): BOOLEAN;
			VAR name: ARRAY 128 OF CHAR; (* debugging *)
			BEGIN
				COPY(section.name,name);
				IF section.resolved = NIL THEN
					D.String('"section.resolved = NIL" for '); D.String(section.name); D.Ln;
					RETURN FALSE
				ELSE
					IF (section.symbol # NIL) & (section.symbol.scope # NIL) & (section.symbol.scope.ownerModule # module(Sections.Module).module) THEN
						(* nothing to do *)
					ELSE
						section.resolved.identifier.fingerprint := GetFingerPrint (section, fingerPrinter);
						UpdateFixups (section.resolved, fingerPrinter);
						ObjectFile.WriteSection(writer,section.resolved^,binary)
					END
				END;
				RETURN TRUE
			END ExportSection;

			PROCEDURE ExportSections (sections: Sections.SectionList): BOOLEAN;
			VAR
				section, test: Sections.Section;
				i, j: LONGINT;
			BEGIN
				FOR i := 0 TO sections.Length() - 1 DO
					section := sections.GetSection(i);
					IF ~ExportSection(section(IntermediateCode.Section)) THEN RETURN FALSE END;
					IF section(IntermediateCode.Section).resolved.identifier.fingerprint # 0 THEN
						FOR j := 0 TO i - 1 DO
							test := sections.GetSection(j);
							IF test(IntermediateCode.Section).resolved.identifier.fingerprint = section(IntermediateCode.Section).resolved.identifier.fingerprint THEN
								diagnostics.Warning(module.moduleName,Diagnostics.Invalid,Diagnostics.Invalid,"duplicate fingerPrints");
								KernelLog.String(section(IntermediateCode.Section).resolved.identifier.name); KernelLog.String(",");
								KernelLog.String(test(IntermediateCode.Section).resolved.identifier.name); KernelLog.Ln;
							END
						END
					END
				END;
				RETURN TRUE
			END ExportSections;

			PROCEDURE ExportModule (module: Sections.Module): BOOLEAN;
			BEGIN
				WriteHeader(writer,binary);
				RETURN ExportSections (module.sections)
			END ExportModule;

		BEGIN
			IF Trace THEN D.String(">>> export generic object file"); D.Ln END;

			IF ~(module IS Sections.Module) THEN
				diagnostics.Error (module.moduleName, Diagnostics.Invalid, Diagnostics.Invalid, "generated module format does not match object file format");
				RETURN FALSE;
			END;

			IF prefix # "" THEN Files.JoinPath (prefix, module.moduleName, fileName); ELSE COPY (module.moduleName, fileName); END;
			Files.JoinExtension (fileName, extension, fileName);

			IF Trace THEN D.String(">>> filename: "); D.String(fileName); D.Ln END;

			file := Files.New (fileName);
			IF file = NIL THEN
				diagnostics.Error(module.moduleName,Diagnostics.Invalid,Diagnostics.Invalid,"failed to open object file");
				RETURN FALSE;
			END;

			NEW (fingerPrinter, module.system);
			Files.OpenWriter (writer, file, 0);
			IF ExportModule (module(Sections.Module)) THEN
				writer.Update;
				Files.Register (file);
				RETURN TRUE;
			ELSE
				RETURN FALSE
			END
		END Export;

		PROCEDURE DefineOptions* (options: Options.Options);
		BEGIN
			options.Add(0X,"objectFileExtension",Options.String);
			options.Add(0X,"objectFilePrefix",Options.String);
			options.Add(0X,"textualObjectFile",Options.Flag);
		END DefineOptions;

		PROCEDURE GetOptions* (options: Options.Options);
		BEGIN
			IF ~options.GetString("objectFileExtension",extension) THEN extension := ObjectFile.DefaultExtension; END;
			IF ~options.GetString("objectFilePrefix",prefix) THEN prefix := ""; END;
			binary := ~options.GetFlag("textualObjectFile");
		END GetOptions;

		PROCEDURE DefaultSymbolFileFormat(): Formats.SymbolFileFormat;
		BEGIN RETURN SymbolFileFormat.Get();
		END DefaultSymbolFileFormat;

		PROCEDURE GetExtension(VAR ext: ARRAY OF CHAR);
		BEGIN COPY(extension, ext)
		END GetExtension;


	END ObjectFileFormat;

	PROCEDURE GetFingerPrint (section: Sections.Section; fingerPrinter: FingerPrinter.FingerPrinter): LONGINT;
	VAR fingerPrint: SyntaxTree.FingerPrint; fp: LONGINT;
	BEGIN
		IF section.fingerprint # 0 THEN
			fp := section.fingerprint
		ELSIF (section.symbol = NIL) OR (section.symbol.scope = NIL) THEN
			fp := 0;
			IF (section(IntermediateCode.Section).resolved # NIL) & (section.type # Sections.PrototypeSection) THEN
				FingerPrinter.FPString(fp, section.name)
			END
		ELSE
			fingerPrint := fingerPrinter.SymbolFP (section.symbol);
			fp := fingerPrint.shallow;
		END;
		RETURN fp
	END GetFingerPrint;

	PROCEDURE UpdateFixups (section: BinaryCode.Section;  fingerPrinter: FingerPrinter.FingerPrinter);
	VAR fixup: BinaryCode.Fixup; i: INTEGER; fixupList: ObjectFile.Fixups; fixups: LONGINT;
	BEGIN
		fixup := section.fixupList.firstFixup; i := 0; fixups := 0; fixupList := NIL;
		WHILE fixup # NIL DO
			ObjectFile.AddFixup(fixups, fixupList, fixup.symbol.name, GetFingerPrint(fixup.symbol, fingerPrinter), fixup.mode, fixup.displacement, fixup.scale, fixup.patterns, fixup.pattern, fixup.offset);
			fixup := fixup.nextFixup; INC (i);
		END;
		ObjectFile.SetFixups(section^, fixups, fixupList);
	END UpdateFixups;

	PROCEDURE Get*(): Formats.ObjectFileFormat;
	VAR objectFileFormat: ObjectFileFormat;
	BEGIN NEW(objectFileFormat); RETURN objectFileFormat
	END Get;

	PROCEDURE ReadHeader(reader: Streams.Reader; VAR binary: BOOLEAN);
	VAR ch: CHAR; version: LONGINT; string: ARRAY 32 OF CHAR;
	BEGIN
		reader.String(string);
		binary := string="FoxOFB";
		IF ~binary THEN ASSERT(string="FoxOFT") END;
		reader.SkipWhitespace;
		reader.Char(ch); ASSERT(ch='v');
		reader.Int(version,FALSE);
		reader.Char(ch); ASSERT(ch='.');
		IF ~binary THEN reader.SkipWhitespace END;
	END ReadHeader;

	PROCEDURE WriteHeader(writer: Streams.Writer; binary: BOOLEAN);
	BEGIN
		IF binary THEN writer.String("FoxOFB");
		ELSE writer.String("FoxOFT");
		END;
		writer.Char(' ');
		writer.Char('v'); writer.Int(version,0); writer.Char(".");
		IF ~binary THEN writer.Ln END;
	END WriteHeader;

	PROCEDURE Show*(context: Commands.Context);
	VAR
		fileName: Files.FileName; file: Files.File; reader: Files.Reader; writer: Streams.Writer;
		section: ObjectFile.Section; binary: BOOLEAN;
	BEGIN
		IF context.arg.GetString(fileName) THEN
			file := Files.Old(fileName);
			IF file # NIL THEN
				NEW(reader,file,0);
				writer := Basic.GetWriter(Basic.GetDebugWriter(fileName));
				ReadHeader(reader, binary);
				WriteHeader(writer, FALSE);
				WHILE reader.Peek () # 0X DO
					ObjectFile.ReadSection (reader, section,binary);
					ObjectFile.WriteSection(writer, section, FALSE); (* textual *)
					reader.SkipWhitespace;
				END;
				writer.Update;
			ELSE
				context.error.String("file not found "); context.error.String(fileName); context.error.Ln
			END;
		ELSE
			context.error.String("no file specificed"); context.error.Ln
		END;
	END Show;


END FoxGenericObjectFile.
