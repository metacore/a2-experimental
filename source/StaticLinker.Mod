MODULE StaticLinker;	(* AUTHOR "negelef"; PURPOSE "Static Object File Linker"; *)

IMPORT Commands, Options, Diagnostics, Files, GenericLinker, ObjectFile, BitSets;

TYPE Arrangement* = OBJECT (GenericLinker.Arrangement);
	VAR
		displacement: GenericLinker.Address;
		bits: BitSets.BitSet;

	PROCEDURE & InitArrangement (displacement: GenericLinker.Address);
	BEGIN SELF.displacement := displacement; NEW (bits, 0);
	END InitArrangement;

	PROCEDURE Allocate* (CONST section: ObjectFile.Section): GenericLinker.Address;
	VAR address, alignment: ObjectFile.Bits;
	BEGIN
		address := bits.GetSize (); alignment := section.alignment * section.unit;
		IF alignment = 0 THEN alignment := section.unit; END;
		INC (address, (alignment - address MOD alignment) MOD alignment);
		bits.Resize (address + section.bits.GetSize ());
		BitSets.CopyBits (section.bits, 0, bits, address, section.bits.GetSize ());
		RETURN address DIV section.unit + displacement;
	END Allocate;

	PROCEDURE Patch* (pos, value: GenericLinker.Address; offset, bits, unit: ObjectFile.Bits);
	BEGIN SELF.bits.SetBits ((pos - displacement) * unit, bits, value);
	END Patch;

END Arrangement;

TYPE FileFormat = PROCEDURE (linker: GenericLinker.Linker; arrangement: Arrangement; writer: Files.Writer);

PROCEDURE ReadObjectFile (CONST moduleName, path, extension: Files.FileName; linker: GenericLinker.Linker);
VAR fileName: Files.FileName; file: Files.File; reader: Files.Reader;
BEGIN
	linker.Information (moduleName, "processing");
	IF path # "" THEN Files.JoinPath (path, moduleName, fileName); ELSE fileName := moduleName; END;
	Files.JoinExtension (fileName, extension, fileName);
	file := Files.Old (fileName);
	IF file = NIL THEN linker.Error (fileName, "failed to open file"); RETURN; END;
	Files.OpenReader (reader, file, 0);
	GenericLinker.Process (reader, linker);
	IF reader.res # Files.Ok THEN linker.Error (fileName, "failed to parse"); END;
END ReadObjectFile;

PROCEDURE WriteOutputFile (arrangement: Arrangement; CONST fileName: Files.FileName; linker: GenericLinker.Linker; fileFormat: FileFormat);
VAR file: Files.File; writer: Files.Writer;
BEGIN
	file := Files.New (fileName);
	Files.OpenWriter (writer, file, 0);
	fileFormat (linker, arrangement, writer);
	writer.Update; Files.Register (file);
	linker.Information (fileName, "written");
END WriteOutputFile;

PROCEDURE WriteBinaryFile (linker: GenericLinker.Linker; arrangement: Arrangement; writer: Files.Writer);
VAR i: LONGINT;
BEGIN
	FOR i := 0 TO arrangement.bits.GetSize () - 1 BY 8 DO
		writer.Char (CHR (arrangement.bits.GetBits (i, 8)));
	END;
END WriteBinaryFile;

PROCEDURE WriteTRMFile (arrangement: Arrangement; writer: Files.Writer; bitsPerLine, lines: LONGINT);
VAR i,j,size: LONGINT;
	PROCEDURE GetBits(pos: LONGINT): LONGINT;
	BEGIN
		IF pos >= size THEN RETURN 0
		ELSIF pos+4 > size THEN RETURN arrangement.bits.GetBits(pos,size-pos)
		ELSE RETURN arrangement.bits.GetBits(pos,4)
		END;
	END GetBits;
BEGIN
	ASSERT (bitsPerLine MOD 4 = 0);
	size := arrangement.bits.GetSize();
	FOR i := 0 TO lines-1 DO
		FOR j := bitsPerLine DIV 4 TO 0 BY -1 DO
			writer.Char(ObjectFile.NibbleToCharacter(GetBits(i*bitsPerLine+j*4)));
		END;
		writer.Ln;
	END;
END WriteTRMFile;

PROCEDURE WriteTRMCodeFile (linker: GenericLinker.Linker; arrangement: Arrangement; writer: Files.Writer);
BEGIN WriteTRMFile (arrangement, writer, 36,2048);
END WriteTRMCodeFile;

PROCEDURE WriteTRMDataFile (linker: GenericLinker.Linker; arrangement: Arrangement; writer: Files.Writer);
BEGIN WriteTRMFile (arrangement, writer, 32,2048);
END WriteTRMDataFile;

PROCEDURE WritePEFile (linker: GenericLinker.Linker; arrangement: Arrangement; writer: Files.Writer; bitmode: INTEGER);
CONST DOSText = "This program cannot be run in DOS mode.$";
CONST DOSHeaderSize = 64; DOSCodeSize = 14; DOSTextSize = 40; DOSStubSize = ((DOSHeaderSize + DOSCodeSize + DOSTextSize + 15) DIV 16) * 16;
CONST BaseAddress = 401000H; FileAlignment = 200H; SectionAlignment = 1000H; HeaderSize = 24; SectionHeaderSize = 40; DirectoryEntries = 16;
VAR OptionalHeaderSize, CodeSize, AlignedCodeSize, HeadersSize, BaseCodeAddress: LONGINT;

	PROCEDURE Reserve (size: LONGINT);
	BEGIN WHILE size # 0 DO writer.Char (0X); DEC (size); END;
	END Reserve;

	PROCEDURE WriteBYTE (value: LONGINT);
	BEGIN writer.Char (CHR (value));
	END WriteBYTE;

	PROCEDURE WriteWORD (value: LONGINT);
	BEGIN WriteBYTE (value MOD 100H); WriteBYTE (value DIV 100H);
	END WriteWORD;

	PROCEDURE WriteDWORD (value: LONGINT);
	BEGIN WriteWORD (value MOD 10000H); WriteWORD (value DIV 10000H);
	END WriteDWORD;

	PROCEDURE WritePTR (value: LONGINT);
	BEGIN WriteDWORD (value); IF bitmode = 64 THEN WriteDWORD (0) END;
	END WritePTR;

	PROCEDURE WriteDOSStub;
	BEGIN
		WriteWORD (5A4DH);	(* e_magic *)
		WriteWORD (DOSStubSize);	(* e_cblp *)
		WriteWORD (1);	(* e_cp *)
		WriteWORD (0);	(* e_crlc *)
		WriteWORD (DOSHeaderSize DIV 16);	(* e_cparhdr *)
		WriteWORD (0);	(* e_minalloc *)
		WriteWORD (0);	(* e_maxalloc *)
		WriteWORD (0);	(* e_ss *)
		WriteWORD (0);	(* e_sp *)
		WriteWORD (0);	(* e_csum *)
		WriteWORD (0);	(* e_ip *)
		WriteWORD (0);	(* e_cs *)
		WriteWORD (DOSHeaderSize);	(* e_lfarlc *)
		WriteWORD (0);	(* e_ovno *)
		Reserve (32);	(* e_res *)
		WriteDWORD (DOSStubSize);	(* e_lfanew *)

		WriteBYTE (00EH); WriteBYTE (01FH); WriteBYTE (0BAH); WriteWORD (DOSCodeSize);
		WriteBYTE (0B4H); WriteBYTE (009H); WriteBYTE (0CDH); WriteBYTE (021H); WriteBYTE (0B8H);
		WriteBYTE (001H); WriteBYTE (04CH); WriteBYTE (0CDH); WriteBYTE (021H); writer.String (DOSText);

		Reserve (DOSStubSize - DOSHeaderSize - DOSCodeSize - DOSTextSize);
	END WriteDOSStub;

	PROCEDURE WriteHeader;
	BEGIN
		WriteDWORD (000004550H);	(* Signature *)
		IF bitmode = 64 THEN
			WriteWORD (08664H);	(* Machine *)
		ELSE
			WriteWORD (0014CH);	(* Machine *)
		END;
		WriteWORD (1);	(* NumberOfSections *)
		WriteDWORD (0);	(* TimeDateStamp *)
		WriteDWORD (0);	(* PointerToSymbolTable *)
		WriteDWORD (0);	(* NumberOfSymbols *)
		WriteWORD (OptionalHeaderSize);	(* SizeOfOptionalHeader *)
		IF bitmode = 64 THEN
			WriteWORD (0022FH);	(* Characteristics *)
		ELSE
			WriteWORD (0032FH);	(* Characteristics *)
		END;
	END WriteHeader;

	PROCEDURE WriteOptionalHeader;
	VAR ImageSize: LONGINT;
	BEGIN
		ImageSize := ((BaseCodeAddress + AlignedCodeSize + (SectionAlignment - 1)) DIV SectionAlignment) * SectionAlignment;

		IF bitmode = 64 THEN
			WriteWORD (0020BH);	(* Magic *)
		ELSE
			WriteWORD (0010BH);	(* Magic *)
		END;
		WriteBYTE (0);	(* MajorLinkerVersion *)
		WriteBYTE (0);	(* MinorLinkerVersion *)
		WriteDWORD (AlignedCodeSize);	(* SizeOfCode *)
		WriteDWORD (0);	(* SizeOfInitializedData *)
		WriteDWORD (0);	(* SizeOfUninitializedData *)
		WriteDWORD (BaseCodeAddress);	(* AddressOfEntryPoint *)
		WriteDWORD (BaseCodeAddress);	(* BaseOfCode *)
		IF bitmode # 64 THEN
			WriteDWORD (ImageSize);	(* BaseOfData *)
		END;
		WritePTR (arrangement.displacement - BaseCodeAddress);	(* ImageBase *)
		WriteDWORD (SectionAlignment);	(* SectionAlignment *)
		WriteDWORD (FileAlignment);	(* FileAlignment *)
		WriteWORD (4);	(* MajorOperatingSystemVersion *)
		WriteWORD (0);	(* MinorOperatingSystemVersion *)
		WriteWORD (0);	(* MajorImageVersion *)
		WriteWORD (0);	(* MinorImageVersion *)
		WriteWORD (4);	(* MajorSubsystemVersion *)
		WriteWORD (0);	(* MinorSubsystemVersion *)
		WriteDWORD (0);	(* Win32VersionValue *)
		WriteDWORD (ImageSize);	(* SizeOfImage *)
		WriteDWORD (HeadersSize);	(* SizeOfHeaders *)
		WriteDWORD (0);	(* CheckSum *)
		WriteWORD (3);	(* Subsystem *)
		WriteWORD (0400H);	(* DllCharacteristics *)
		WritePTR (0100000H);	(* SizeOfStackReserve *)
		WritePTR (01000H);	(* SizeOfStackCommit *)
		WritePTR (0100000H);	(* SizeOfHeapReserve *)
		WritePTR (01000H);	(* SizeOfHeapCommit *)
		WriteDWORD (0);			(* LoaderFlags *)
		WriteDWORD (DirectoryEntries);	(* NumberOfRvaAndSizes *)

		Reserve (8);
		WriteDWORD (0); WriteDWORD (0);
		Reserve ((DirectoryEntries - 2) * 8);
	END WriteOptionalHeader;

	PROCEDURE WriteCodeSection;
	BEGIN
		writer.String (".text"); Reserve (3);	(* Name *)
		WriteDWORD (CodeSize);	(* VirtualSize *)
		WriteDWORD (BaseCodeAddress);	(* VirtualAddress *)
		WriteDWORD (AlignedCodeSize);	(* SizeOfRawData *)
		WriteDWORD (HeadersSize);	(* PointerToRawData *)
		WriteDWORD (0);	(* PointerToRelocations *)
		WriteDWORD (0);	(* PointerToLinenumbers *)
		WriteWORD (0);	(* NumberOfRelocations *)
		WriteWORD (0);	(* NumberOfLinenumbers *)
		WriteDWORD (SHORT (0E0000020H));	(* Characteristics *)
	 	Reserve (HeadersSize - DOSStubSize - HeaderSize - OptionalHeaderSize - SectionHeaderSize);
	 	WriteBinaryFile (linker, arrangement, writer);
		Reserve (AlignedCodeSize - CodeSize);
	END WriteCodeSection;

BEGIN
	ASSERT (arrangement.displacement = BaseAddress);
	OptionalHeaderSize := 96 + DirectoryEntries * 8;
	IF bitmode = 64 THEN INC (OptionalHeaderSize, 16); END;
	CodeSize := arrangement.bits.GetSize () DIV 8;
	AlignedCodeSize := ((CodeSize + (FileAlignment - 1)) DIV FileAlignment) * FileAlignment;
	HeadersSize := ((DOSStubSize + HeaderSize + OptionalHeaderSize + SectionHeaderSize + (FileAlignment - 1)) DIV FileAlignment) * FileAlignment;
	BaseCodeAddress := ((HeadersSize + (SectionAlignment - 1)) DIV SectionAlignment) * SectionAlignment;

	WriteDOSStub; WriteHeader; WriteOptionalHeader; WriteCodeSection;
END WritePEFile;

PROCEDURE WritePE32File (linker: GenericLinker.Linker; arrangement: Arrangement; writer: Files.Writer);
BEGIN WritePEFile (linker, arrangement, writer, 32);
END WritePE32File;

PROCEDURE WritePE64File (linker: GenericLinker.Linker; arrangement: Arrangement; writer: Files.Writer);
BEGIN WritePEFile (linker, arrangement, writer, 64);
END WritePE64File;

PROCEDURE WriteELFFile (linker: GenericLinker.Linker; arrangement: Arrangement; writer: Files.Writer);
CONST ELFHeaderSize = 52; ProgramHeaderSize = 32; HeadersSize = ELFHeaderSize + ProgramHeaderSize;
CONST BaseAddress = 08048000H; EntryAddress = BaseAddress + HeadersSize;

	PROCEDURE Reserve (size: LONGINT);
	BEGIN WHILE size # 0 DO writer.Char (0X); DEC (size); END;
	END Reserve;

	PROCEDURE WriteByte (value: LONGINT);
	BEGIN writer.Char (CHR (value));
	END WriteByte;

	PROCEDURE WriteHalf (value: LONGINT);
	BEGIN WriteByte (value MOD 100H); WriteByte (value DIV 100H);
	END WriteHalf;

	PROCEDURE WriteWord (value: LONGINT);
	BEGIN WriteHalf (value MOD 10000H); WriteHalf (value DIV 10000H);
	END WriteWord;

	PROCEDURE WriteELFHeader;
	BEGIN
		WriteByte (7FH);	(* e_ident[EI_MAG0] *)
		WriteByte (ORD('E'));	(* e_ident[EI_MAG1] *)
		WriteByte (ORD('L'));	(* e_ident[EI_MAG2] *)
		WriteByte (ORD('F'));	(* e_ident[EI_MAG3] *)
		WriteByte (1);		(* e_ident[EI_CLASS] *)
		WriteByte (1);		(* e_ident[EI_DATA] *)
		WriteByte (1);		(* e_ident[EI_VERSION] *)
		WriteByte (0);		(* e_ident[EI_PAD] *)
		Reserve (8);		(* e_ident[EI_NIDENT] *)
		WriteHalf (2);		(* e_type *)
		WriteHalf (3);		(* e_machine *)
		WriteWord (1);	(* e_version *)
		WriteWord (EntryAddress);	(* e_entry *)
		WriteWord (ELFHeaderSize);	(* e_phoff *)
		WriteWord (0);	(* e_phoff *)
		WriteWord (0);	(* e_flags *)
		WriteHalf (ELFHeaderSize);	(* e_ehsize *)
		WriteHalf (ProgramHeaderSize);	(* e_phentsize *)
		WriteHalf (1);		(* e_phnum *)
		WriteHalf (0);		(* e_shentsize *)
		WriteHalf (0);		(* e_shnum *)
		WriteHalf (0);		(* e_shstrndx *)
	END WriteELFHeader;

	PROCEDURE WriteProgramHeader;
	VAR FileSize: LONGINT;
	BEGIN
		FileSize := HeadersSize + arrangement.bits.GetSize () DIV 8;

		WriteWord (1);		(* p_type *)
		WriteWord (0);		(* p_offset *)
		WriteWord (BaseAddress);	(* p_vaddr *)
		WriteWord (0);		(* p_paddr *)
		WriteWord (FileSize);	(* p_filesz *)
		WriteWord (FileSize);	(* p_memsz *)
		WriteWord (7);		(* p_flags *)
		WriteWord (1000H);	(* p_align *)
	END WriteProgramHeader;

BEGIN
	ASSERT (arrangement.displacement = BaseAddress);
	WriteELFHeader;
	WriteProgramHeader;
 	WriteBinaryFile (linker, arrangement, writer);
END WriteELFFile;

PROCEDURE GetFileFormat (options: Options.Options; CONST name: Options.Name; default: FileFormat): FileFormat;
VAR format: ARRAY 10 OF CHAR;
BEGIN
	IF ~options.GetString (name, format) THEN RETURN default;
	ELSIF format = "TRMCode" THEN RETURN WriteTRMCodeFile;
	ELSIF format = "TRMData" THEN RETURN WriteTRMDataFile;
	ELSIF format = "PE32" THEN RETURN WritePE32File;
	ELSIF format = "PE64" THEN RETURN WritePE64File;
	ELSIF format = "ELF" THEN RETURN WriteELFFile;
	ELSE RETURN default; END;
END GetFileFormat;

PROCEDURE Link* (context: Commands.Context);
VAR options: Options.Options;
	verbose: BOOLEAN;
	codeFileFormat, dataFileFormat: FileFormat;
	codeDisplacement, dataDisplacement: GenericLinker.Address;
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
		ReadObjectFile (moduleName, path, extension, linker);
		IF ~linker.error THEN linker.Link; END;
		context.arg.GetString (moduleName);
	END;

	IF ~linker.error THEN
		WriteOutputFile (code, codeFileName, linker, codeFileFormat);
		IF data # code THEN WriteOutputFile (data, dataFileName, linker, dataFileFormat); END;
	END;

	IF linker.error THEN context.result := Commands.CommandError; END;
END Link;

END StaticLinker.

StaticLinker.Link --fileName=test.exe --fileFormat=PE32 --displacement=401000H Test ~
StaticLinker.Link --fileName=a.out --fileFormat=ELF --displacement=08048000H Test ~




