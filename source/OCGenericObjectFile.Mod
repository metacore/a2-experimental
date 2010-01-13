MODULE OCGenericObjectFile; (** AUTHOR "negelef"; PURPOSE "Generic Object File Writer"; *)

IMPORT
	Formats := OCFormats, Sections := OCSections, IntermediateCode := OCIntermediateCode,
	Global := OCGlobal, Basic := OCBasic, SyntaxTree := OCSyntaxTree, BinaryCode := OCBinaryCode,
	Files, Options, ObjectFile, Diagnostics;

TYPE ObjectFileFormat* = OBJECT (Formats.ObjectFileFormat)
	VAR extension: ARRAY 10 OF CHAR;

		PROCEDURE Export* (module: Formats.GeneratedModule; symbolFileFormat: Formats.SymbolFileFormat): BOOLEAN;
		VAR moduleName: SyntaxTree.String; fileName: Files.FileName; file: Files.File; writer: Files.Writer;

			PROCEDURE ExportSection (section: BinaryCode.Section);
			BEGIN
				UpdateFixups (section);
				ObjectFile.WriteSection (writer, section^);
			END ExportSection;

			PROCEDURE ExportSections (sections: Sections.SectionList);
			VAR section: Sections.Section;
			BEGIN
				section := sections.first;
				WHILE section # NIL DO ExportSection (section(IntermediateCode.Section).resolved); section := section.nextSection; END;
			END ExportSections;

			PROCEDURE ExportModule (module: Sections.Module);
			BEGIN
				ExportSections (module.sections);
				ExportSections (module.caseTables);
				ExportSections (module.systemCalls);
			END ExportModule;

		BEGIN
			IF ~(module IS Sections.Module) THEN
				diagnostics.Error (module.module.sourceName, Diagnostics.Invalid, Diagnostics.Invalid, "generated module format does not match object file format");
				RETURN FALSE;
			END;

			Global.ModuleFileName (module.module.name, module.module.context, moduleName);
			Basic.Concat (fileName, "", moduleName, extension);
			file := Files.New (fileName);
			IF file = NIL THEN
				diagnostics.Error(module.module.sourceName,Diagnostics.Invalid,Diagnostics.Invalid,"failed to open object file");
				RETURN FALSE;
			END;

			Files.OpenWriter (writer, file, 0);
			ExportModule (module(Sections.Module));
			writer.Update;
			Files.Register (file);
			RETURN TRUE;
		END Export;

		PROCEDURE DefineOptions* (options: Options.Options);
		BEGIN
			options.Add(0X,"objectFileExtension",Options.String);
		END DefineOptions;

		PROCEDURE GetOptions* (options: Options.Options);
		BEGIN
			IF ~options.GetString("objectFileExtension",extension) THEN extension := ".Obg" END;
		END GetOptions;

END ObjectFileFormat;

PROCEDURE UpdateFixups (section: BinaryCode.Section);
VAR fixup: BinaryCode.Fixup; i: INTEGER;
BEGIN
	section.fixups := section.fixupList.fixups;
	IF section.fixups # 0 THEN NEW (section.fixup, section.fixups); ELSE section.fixup := NIL; END;
	fixup := section.fixupList.firstFixup; i := 0;
	WHILE fixup # NIL DO
		section.fixup[i] := fixup^;
		COPY (fixup.symbol.name, section.fixup[i].section);
		fixup := fixup.nextFixup; INC (i);
	END;
END UpdateFixups;

PROCEDURE Get*(): Formats.ObjectFileFormat;
VAR objectFileFormat: ObjectFileFormat;
BEGIN NEW(objectFileFormat); RETURN objectFileFormat
END Get;

END OCGenericObjectFile.
