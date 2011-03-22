MODULE FoxGenericObjectFile; (** AUTHOR "negelef"; PURPOSE "Generic Object File Writer"; *)

IMPORT
	Formats := FoxFormats, Sections := FoxSections, IntermediateCode := FoxIntermediateCode,
	Global := FoxGlobal, SyntaxTree := FoxSyntaxTree, BinaryCode := FoxBinaryCode,
	FingerPrinter := FoxFingerPrinter, Files, Options, ObjectFile, Diagnostics, SymbolFileFormat := FoxTextualSymbolFile, KernelLog;

TYPE ObjectFileFormat* = OBJECT (Formats.ObjectFileFormat)
	VAR path, extension: Files.FileName;

		PROCEDURE Export* (module: Formats.GeneratedModule; symbolFileFormat: Formats.SymbolFileFormat): BOOLEAN;
		VAR moduleName: SyntaxTree.String; fileName: Files.FileName; file: Files.File; writer: Files.Writer; fingerPrinter: FingerPrinter.FingerPrinter;

			PROCEDURE ExportSection (section: IntermediateCode.Section);
			VAR name: ARRAY 128 OF CHAR; (* debugging *)
			BEGIN
				COPY(section.name,name);
				IF (section.symbol # NIL) & (section.symbol.scope # NIL) & (section.symbol.scope.ownerModule # module(Sections.Module).module) THEN
					RETURN
				END;
				section.resolved.identifier.fingerprint := GetFingerPrint (section, fingerPrinter);
				UpdateFixups (section.resolved, fingerPrinter);
				ObjectFile.WriteSection (writer, section.resolved^);
			END ExportSection;

			PROCEDURE ExportSections (sections: Sections.SectionList): BOOLEAN;
			VAR section,test: Sections.Section;
			BEGIN
				section := sections.first;
				WHILE section # NIL DO
					ExportSection (section(IntermediateCode.Section));
					IF section(IntermediateCode.Section).resolved.identifier.fingerprint # 0 THEN
						test := sections.first;
						WHILE test # section DO
							IF test(IntermediateCode.Section).resolved.identifier.fingerprint = section(IntermediateCode.Section).resolved.identifier.fingerprint THEN
								diagnostics.Warning(module.module.sourceName,Diagnostics.Invalid,Diagnostics.Invalid,"duplicate fingerPrints");
								KernelLog.String(section(IntermediateCode.Section).resolved.identifier.name); KernelLog.String(",");
								KernelLog.String(test(IntermediateCode.Section).resolved.identifier.name); KernelLog.Ln;
								(*RETURN FALSE*)
							END;
							test := test.nextSection;
						END;
					END;
					section := section.nextSection;
					END;
					RETURN TRUE
			END ExportSections;

			PROCEDURE ExportModule (module: Sections.Module): BOOLEAN;
			BEGIN
				RETURN ExportSections (module.sections) &
				ExportSections (module.caseTables) &
				ExportSections (module.systemCalls);
			END ExportModule;

		BEGIN
			IF ~(module IS Sections.Module) THEN
				diagnostics.Error (module.module.sourceName, Diagnostics.Invalid, Diagnostics.Invalid, "generated module format does not match object file format");
				RETURN FALSE;
			END;

			Global.ModuleFileName (module.module.name, module.module.context, moduleName);
			IF path # "" THEN Files.JoinPath (path, moduleName, fileName); ELSE COPY (moduleName, fileName); END;
			Files.JoinExtension (fileName, extension, fileName);
			file := Files.New (fileName);
			IF file = NIL THEN
				diagnostics.Error(module.module.sourceName,Diagnostics.Invalid,Diagnostics.Invalid,"failed to open object file");
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
			options.Add(0X,"path",Options.String);
			options.Add(0X,"objectFileExtension",Options.String);
		END DefineOptions;

		PROCEDURE GetOptions* (options: Options.Options);
		BEGIN
			IF ~options.GetString("path",extension) THEN path := ""; END;
			IF ~options.GetString("objectFileExtension",extension) THEN extension := ObjectFile.DefaultExtension; END;
		END GetOptions;

		PROCEDURE DefaultSymbolFileFormat(): Formats.SymbolFileFormat;
		BEGIN RETURN SymbolFileFormat.Get();
		END DefaultSymbolFileFormat;

END ObjectFileFormat;

PROCEDURE GetFingerPrint (section: Sections.Section; fingerPrinter: FingerPrinter.FingerPrinter): LONGINT;
VAR fingerPrint: SyntaxTree.FingerPrint;
BEGIN
	IF (section.symbol = NIL) OR (section.symbol.scope = NIL) THEN
		RETURN 0
	ELSE
		fingerPrint := fingerPrinter.SymbolFP (section.symbol);
		RETURN fingerPrint.shallow;
	END
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

END FoxGenericObjectFile.
