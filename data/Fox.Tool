Fox - Flexible Oberon Cross Compiler
Build and Test Tool
(c) Felix Friedrich (fof), ETH Zürich, 2008-2018
Conceptual design of the compiler has been worked out together with Florian Negele.

Heaps.SetMetaData 
Heaps.SetHeuristic
Kernel.GC 

Compiler.Compile --noInterfaceCheck
(*
	System.DoCommands
	System.Timer start ~

	Compiler.Compile *)

	BitSets.Mod ObjectFile.Mod GenericLinker.Mod Linker.Mod
	FoxBasic.Mod  FoxProgTools.Mod  FoxScanner.Mod FoxCSharpScanner.Mod FoxSyntaxTree.Mod FoxGlobal.Mod
	FoxFormats.Mod FoxFingerprinter.Mod FoxPrintout.Mod
	FoxParser.Mod FoxCSharpParser.Mod FoxSemanticChecker.Mod
	FoxBackend.Mod FoxSections.Mod
	FoxFrontend.Mod
	Compiler.Mod
	FoxOberonFrontend.Mod FoxCSharpFrontend.Mod
	FoxInterfaceComparison.Mod FoxTextualSymbolFile.Mod
	FoxBinaryCode.Mod FoxIntermediateCode.Mod FoxIntermediateBackend.Mod FoxCodeGenerators.Mod
	FoxGenericObjectFile.Mod
	FoxAMD64InstructionSet.Mod FoxAMD64Assembler.Mod FoxAMDBackend.Mod
	FoxAssembler.Mod FoxIntermediateAssembler.Mod FoxDisassembler.Mod
	FoxARMInstructionSet.Mod FoxARMAssembler.Mod FoxARMBackend.Mod	FoxMinosObjectFile.Mod
	FoxIntermediateParser.Mod FoxIntermediateObjectFile.Mod FoxIntermediateLinker.Mod
	FoxTRMInstructionSet.Mod FoxTRMAssembler.Mod FoxTRMBackend.Mod
	FoxInterpreterBackend.Mod FoxTranspilerBackend.Mod
	FoxDocumentationScanner.Mod FoxDocumentationTree.Mod FoxDocumentationPrinter.Mod FoxDocumentationHtml.Mod
	FoxDocumentationParser.Mod FoxDocumentationBackend.Mod
	FoxTestBackend.Mod
	FoxTRMTools.Mod
	ActiveCellsRuntime.mod
	ActiveCellsRunner.mod

	FoxProfiler.Mod
	TextCompiler.Mod FoxA2Interface.Mod Versioning.Mod TestSuite.Mod FoxTest.Mod

	PersistentObjects.Mod FoxInterpreterSymbols.Mod FoxInterpreter.Mod
	InterpreterShell.Mod WMInterpreterShell.Mod
	~
System.Show Time elapsed: ~ System.Ln ~
System.Timer elapsed ~ System.Ln ~
~

System.FreeDownTo FoxBasic ~

compiler options:
		--print			flag		printout source code (for debugging)
		--silent			flag		do not printout success messages
	-c	--check			flag		semantically check module (auto-check if backend is installed)
	-e	--traceError	flag		report a stack traceback for each error (for debugging)
	-I	--interface		flag		printout interface (for debugging)
	-i	--info				flag		report more detailed information in error messages and in printout (for debugging)
	-b	--backend		string	specification of backend (such as, for example, -b=AMD or -b=Intermediate)
	-f	--findPC			integer	specification of a pc to be located in code
		--symbolFile	string	specification of a symbol file format (example: --symbolFile=Textual)
		--objectFile		string	specification of an object file format(example: --objectFile=Generic)
		--activeCells	flag		use active cells language extension
	-w	--warnings		flag		show warnings
		--darwinHost	flag		use Darwin (MacOSX) calling convention for ext. C procedures
		--hardware	string	hardware generation hint for ActiveCells
		--documentation	string	install documentation engine
	-R	--rootPath	string	specification of a root directory path; is prepended to the srcPath (for handling of relative vs full path designators)
	-S	--srcPath	string	specification of a source path; replaces existing path
	-D --destPath		string	specification of a destination path
	-p	--platform		string	compiler options for platforms such as ARMA2, Win32, defined in Compiler.Mod
	-d	--define	string	define comma-separated identifiers for conditional compilation

backend options (intermediate and AMD)
		--trace			string	display trace information for sections (--trace=* : all sections)

generic object file options
		--textualObjectFile		flag		store the object file in textual (UTF8) form
		--objectFileExtension	string	extension to be used for object file

textual symbol file options
		--symbolFileExtension	string	extension to be used for symbol file (for reading only)
		--noRedefinition		flag		redefinition of symbols is forbidden (no new symbols)
		--noModification		flag		modification of symbols is forbidden

AMD backend options
		--bits					number		number of bits (32 or 64)
		--traceable				flag			include instructions in procedure call in order to make a trace possible -- for debugging only
		--useFPU				flag			use FPU for floating point computations (in contrast to SSE and SSE2)

ARM backend options
		--useFPU32				flag			use FPU (32 bit) for floating point computations
		--useFPU64				flag			use FPU (64 bit and 32 bit) for floating point computations

ActiveCells options
		--cellsAreObjects	flag	Cells are compiled to (active) Objects. For simulation/emulation and for code generation.

Regression testing

System.DoCommands
	FoxTest.Compile -l=Test.Log  Oberon.Compilation.Test Oberon.Compilation.AMD64TestDiff ~
	FoxTest.Compile	-l=Test.Log Oberon.Execution.Test Oberon.Execution.AMD64TestDiff ~
	FoxTest.Compile	-l=Test.Log ActiveCells.Execution.Test ActiveCells.Execution.TestDiff ~
	FoxTest.Compile	-l=Test.Log MathArrays.Execution.Test  ~
~
	TextCompiler.CompileClipboard -p=Win32  ~
	TextCompiler.CompileSelection -p=Win32 ~

open regression test files
PET.Open Oberon.Compilation.Test ~
PET.Open Oberon.Execution.Test ~

PET.Open MathArrays.Compilation.Test ~
PET.Open MathArrays.Execution.Test ~

PET.Open MathArrays.Compilation.Test ~
PET.Open MathArrays.Execution.Test ~

some documentation rules
(** text *) ~ documentation line, will be extracted by documentation generator
(*! text *) ~ todo comment
(*? text *) ~ to be examined / open question comment

-----------------------------------------------------------------------------------

Building a library:

	FoxGenericObjectFile.MakeLibrary
		Kernel.Lib Builtins.GofW Trace.GofW
		Kernel32.GofW Machine.GofW Heaps.GofW Modules.GofW Objects.GofW
		Kernel.GofW KernelLog.GofW Streams.GofW Commands.GofW Files.GofW
		WinFS.GofW Clock.GofW Dates.GofW Reals.GofW Strings.GofW Diagnostics.GofW BitSets.GofW StringPool.GofW ObjectFile.GofW GenericLinker.GofW Reflection.GofW
		Loader.GofW
		WinTrace.GofW StdIO.GofW
		~
