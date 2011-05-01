MODULE FoxGenericObjectFile; (** AUTHOR "negelef"; PURPOSE "Generic Object File Writer"; *)

IMPORT
	StringPool, Streams, Commands, Basic := FoxBasic, Formats := FoxFormats, Sections := FoxSections, IntermediateCode := FoxIntermediateCode,
	SyntaxTree := FoxSyntaxTree, BinaryCode := FoxBinaryCode,
	FingerPrinter := FoxFingerPrinter, Files, Options, ObjectFile, Diagnostics, SymbolFileFormat := FoxTextualSymbolFile, KernelLog, D := Debugging;

CONST
	version = 1;
	Trace = FALSE;

TYPE ObjectFileFormat* = OBJECT (Formats.ObjectFileFormat)
	VAR prefix, extension: Files.FileName; binary: BOOLEAN;

		PROCEDURE Export* (module: Formats.GeneratedModule; symbolFileFormat: Formats.SymbolFileFormat): BOOLEAN;
		VAR fileName: Files.FileName; file: Files.File; writer: Files.Writer; fingerPrinter: FingerPrinter.FingerPrinter; poolMap: ObjectFile.PoolMap;

			PROCEDURE ExportSection (section: IntermediateCode.Section): BOOLEAN;
			VAR name: ARRAY 128 OF CHAR; (* debugging *)
			BEGIN
				IF section.IsExternal() OR (section.symbol # NIL) & (section.symbol.scope # NIL) & (section.symbol.scope.ownerModule # module(Sections.Module).module) THEN
					(* nothing to do *)
				ELSE
					IF section.resolved = NIL THEN
						Basic.FromPooledName(section.name, name);
						D.String('"section.resolved = NIL" for '); D.String(name); D.Ln;
						RETURN FALSE
					END;
					section.resolved.identifier.fingerprint := GetFingerPrint (section, fingerPrinter);
					UpdateFixups (section.resolved, fingerPrinter);
					ObjectFile.WriteSection(writer,section.resolved^,binary, poolMap)
				END;
				RETURN TRUE
			END ExportSection;

			PROCEDURE ExportSections (sections: Sections.SectionList): BOOLEAN;
			VAR
				section, test: Sections.Section;
				i, j: LONGINT;
				name: ObjectFile.SectionName;
			BEGIN
				FOR i := 0 TO sections.Length() - 1 DO
					section := sections.GetSection(i);
					IF ~ExportSection(section(IntermediateCode.Section)) THEN RETURN FALSE END;
					IF ~section.IsExternal() & (section(IntermediateCode.Section).resolved.identifier.fingerprint # 0) THEN
						FOR j := 0 TO i - 1 DO
							test := sections.GetSection(j);
							IF ~test.IsExternal() & (test(IntermediateCode.Section).resolved.identifier.fingerprint = section(IntermediateCode.Section).resolved.identifier.fingerprint) THEN
								diagnostics.Warning(module.moduleName,Diagnostics.Invalid,Diagnostics.Invalid,"duplicate fingerPrints");
								ObjectFile.FromPooledName(section(IntermediateCode.Section).resolved.identifier.name,name);
								KernelLog.String(name); KernelLog.String(",");
								ObjectFile.FromPooledName(test(IntermediateCode.Section).resolved.identifier.name,name);
								KernelLog.String(name);
								KernelLog.Ln;
							END
						END
					END
				END;
				RETURN TRUE
			END ExportSections;

			PROCEDURE ExportModule (module: Sections.Module): BOOLEAN;
			BEGIN
				WriteHeader(writer,binary,module.allSections,poolMap);
				RETURN ExportSections (module.allSections)
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
	VAR fingerPrint: SyntaxTree.FingerPrint; fp: LONGINT; string: SyntaxTree.String;
	BEGIN
		IF section.fingerprint # 0 THEN
			fp := section.fingerprint
		ELSIF (section.symbol = NIL) OR (section.symbol.scope = NIL) THEN
			fp := 0;
			IF (section(IntermediateCode.Section).resolved # NIL) & ~section.IsExternal() THEN
				Basic.FromPooledName(section.name, string);
				FingerPrinter.FPString(fp, string)
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

	PROCEDURE ReadHeader(reader: Streams.Reader; VAR binary: BOOLEAN; VAR poolMap: ObjectFile.PoolMap);
	VAR ch: CHAR; version: LONGINT; string: ARRAY 32 OF CHAR; i,j,pos,size: LONGINT; name: ObjectFile.SectionName;
	BEGIN
		reader.String(string);
		binary := string="FoxOFB";
		IF ~binary THEN ASSERT(string="FoxOFT") END;
		reader.SkipWhitespace;
		reader.Char(ch); ASSERT(ch='v');
		reader.Int(version,FALSE);
		reader.Char(ch); ASSERT(ch='.');
		IF ~binary THEN reader.SkipWhitespace
		ELSE
			NEW(poolMap,64);
			reader.RawLInt(size);
			pos := 0; j := 0;
			FOR i := 0 TO size-1 DO
				reader.Char(ch);
				IF Trace THEN IF ch # 0X THEN D.Char(ch) ELSE D.Ln END END;
				name[j] := ch; INC(j);
				IF ch = 0X THEN
					poolMap.Put(pos, StringPool.GetIndex1(name));
					pos := i+1; j := 0;
				END;
			END;
			IF Trace THEN D.String("pos "); D.Int(reader.Pos(),1); D.Ln END;
			ASSERT(ch=0X);
		END;
	END ReadHeader;

	PROCEDURE WriteHeader(writer: Streams.Writer; binary: BOOLEAN; sections: Sections.SectionList; VAR poolMap: ObjectFile.PoolMap);
	VAR p1,p2, size,i: LONGINT; section: Sections.Section;

		PROCEDURE Identifier(id: LONGINT);
		VAR i: LONGINT; name: ObjectFile.SectionName; ch: CHAR;
		BEGIN
			IF id >= 0 THEN
				IF ~poolMap.Has(id) THEN
					poolMap.Put(id, size);
					StringPool.GetString(id, name);
					i := 0;
					REPEAT
						ch := name[i];
						INC(i); INC(size);
						writer.Char(ch);
						IF Trace THEN IF ch # 0X THEN D.Char(ch) ELSE D.Ln END; END;
					UNTIL ch = 0X;
				END;
			END;
		END Identifier;

		PROCEDURE ProcessPooledName(CONST pooledName: ObjectFile.PooledName);
		VAR i: LONGINT;
		BEGIN
			FOR i := 0 TO LEN(pooledName)-1 DO
				IF pooledName[i] < 0 THEN RETURN END;
				Identifier(pooledName[i]);
			END;
		END ProcessPooledName;

		PROCEDURE ProcessSection(section: IntermediateCode.Section);
		VAR i: LONGINT;
		BEGIN
			IF section.resolved # NIL THEN
				ProcessPooledName(section.resolved.identifier.name);
				FOR i := 0 TO section.resolved.fixups-1 DO
					ProcessPooledName(section.resolved.fixup[i].identifier.name);
				END;
			END;
		END ProcessSection;

	BEGIN
		IF binary THEN writer.String("FoxOFB");
		ELSE writer.String("FoxOFT");
		END;
		writer.Char(' ');
		writer.Char('v'); writer.Int(version,0); writer.Char(".");
		IF ~binary THEN writer.Ln
		ELSE
			NEW(poolMap,512);
			p1 := writer.Pos(); size := 0;
			writer.RawLInt(0);
			FOR i := 0 TO sections.Length()-1 DO
				section := sections.GetSection(i);
				ProcessSection(section(IntermediateCode.Section));
			END;
			p2 := writer.Pos();
			writer.SetPos(p1);
			writer.RawLInt(size);
			writer.SetPos(p2);
			IF Trace THEN D.String("pos "); D.Int(writer.Pos(),1); D.Ln END;
		END;
	END WriteHeader;

	PROCEDURE Show*(context: Commands.Context);
	VAR
		fileName: Files.FileName; file: Files.File; reader: Files.Reader; writer: Streams.Writer;
		section: ObjectFile.Section; binary: BOOLEAN; poolMap, poolMapDummy: ObjectFile.PoolMap;
	BEGIN
		IF context.arg.GetString(fileName) THEN
			file := Files.Old(fileName);
			IF file # NIL THEN
				NEW(reader,file,0);
				writer := Basic.GetWriter(Basic.GetDebugWriter(fileName));
				ReadHeader(reader, binary, poolMap);
				WriteHeader(writer, FALSE, NIL, poolMapDummy);
				WHILE reader.Peek () # 0X DO
					ObjectFile.ReadSection (reader, section,binary, poolMap);
					ObjectFile.WriteSection(writer, section, FALSE, NIL); (* textual *)
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
