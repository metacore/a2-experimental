MODULE OCGenericObjectFile; (** AUTHOR "negelef"; PURPOSE "Generic Object File Writer"; *)

IMPORT
	Formats := OCFormats, Sections := OCSections, IntermediateCode := OCIntermediateCode,
	Global := OCGlobal, SyntaxTree := OCSyntaxTree, BinaryCode := OCBinaryCode,
	FingerPrint := OCFingerPrint, Files, Options, ObjectFile, Diagnostics, SymbolFileFormat := OCTextualSymbolFile, KernelLog;

TYPE ObjectFileFormat* = OBJECT (Formats.ObjectFileFormat)
	VAR path, extension: Files.FileName;

		PROCEDURE Export* (module: Formats.GeneratedModule; symbolFileFormat: Formats.SymbolFileFormat): BOOLEAN;
		VAR moduleName: SyntaxTree.String; fileName: Files.FileName; file: Files.File; writer: Files.Writer; lookup: FingerPrint.FingerPrinterLookup;

			PROCEDURE ExportSection (section: IntermediateCode.Section);
			VAR name: ARRAY 128 OF CHAR; (* debugging *)
			BEGIN
				COPY(section.name,name);
				IF (section.symbol # NIL) & (section.symbol.scope # NIL) & (section.symbol.scope.ownerModule # module(Sections.Module).module) THEN
					RETURN
				END;
				section.resolved.identifier.fingerprint := GetFingerprint (section, lookup);
				UpdateFixups (section.resolved, lookup);
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
								diagnostics.Error(module.module.sourceName,Diagnostics.Invalid,Diagnostics.Invalid,"duplicate fingerprints");
								KernelLog.String(section(IntermediateCode.Section).resolved.identifier.name); KernelLog.String(",");
								KernelLog.String(test(IntermediateCode.Section).resolved.identifier.name); KernelLog.Ln;
								RETURN FALSE
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

			NEW (lookup, module.system);
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

PROCEDURE GetFingerprint (section: Sections.Section; lookup: FingerPrint.FingerPrinterLookup): LONGINT;
VAR fingerPrinter: FingerPrint.FingerPrinter; fingerPrint: FingerPrint.FingerPrint;
BEGIN
	IF (section.symbol = NIL) OR (section.symbol.scope = NIL) THEN
		RETURN 0
	ELSE
		fingerPrinter := lookup.GetFingerPrinter (section.symbol.scope.ownerModule);
		fingerPrint := fingerPrinter.SymbolFP (section.symbol);
		RETURN fingerPrint.FP;
	END
END GetFingerprint;

PROCEDURE UpdateFixups (section: BinaryCode.Section; lookup: FingerPrint.FingerPrinterLookup);
VAR fixup: BinaryCode.Fixup; i: INTEGER;
BEGIN
	section.fixups := section.fixupList.fixups;
	IF section.fixups # 0 THEN NEW (section.fixup, section.fixups); ELSE section.fixup := NIL; END;
	fixup := section.fixupList.firstFixup; i := 0;
	WHILE fixup # NIL DO
		section.fixup[i] := fixup^;
		COPY (fixup.symbol.name, section.fixup[i].identifier.name);
		section.fixup[i].identifier.fingerprint := GetFingerprint (fixup.symbol, lookup);
		fixup := fixup.nextFixup; INC (i);
	END;
END UpdateFixups;

PROCEDURE Get*(): Formats.ObjectFileFormat;
VAR objectFileFormat: ObjectFileFormat;
BEGIN NEW(objectFileFormat); RETURN objectFileFormat
END Get;

END OCGenericObjectFile.
