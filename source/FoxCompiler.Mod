MODULE Compiler;   (**  AUTHOR "fof & fn"; PURPOSE "Oberon Compiler Command Interface";  **)
(* (c) fof ETH Zürich, 2008 *)

IMPORT
	Basic := FoxBasic, Scanner := FoxScanner, Parser := FoxParser,
	SemanticChecker := FoxSemanticChecker, SyntaxTree := FoxSyntaxTree, Formats := FoxFormats,  D := Debugging,
	Streams, Commands,Diagnostics, Options, Kernel, Printout := FoxPrintout, Backend := FoxBackend,Strings, Global := FoxGlobal
	, ActiveCells := FoxActiveCells, IntermediateCodeAssembler := FoxIntermediateCodeAssembler;

CONST
	(* flags *)
	Print* = 0;
	Silent* = 1;
	Check* = 2;
	TraceError* = 3;
	Info* = 4;
	FindPC* = 5;
	DataFlow*=6;
	Warnings*=7;
	ForceModuleBodies*=8;
	UseDarwinCCalls*=9;	(* use Darwin stack alignment for ext. C procedures *)	(*fld*)
	SingleModule*=10;

	DefaultBackend = "AMD";


TYPE
	TracingDiagnostics=OBJECT (Diagnostics.Diagnostics)
	VAR diagnostics: Diagnostics.Diagnostics;

		PROCEDURE &InitDiagnostics(diagnostics: Diagnostics.Diagnostics);
		BEGIN
			SELF.diagnostics := diagnostics
		END InitDiagnostics;

		PROCEDURE Error(CONST source: ARRAY OF CHAR; position, errorCode : LONGINT; CONST message : ARRAY OF CHAR);
		BEGIN
			IF diagnostics # NIL THEN
				diagnostics.Error(source,position,errorCode,message);
			END;
			D.Ln;
			D.String(" ---------------------- TRACE for COMPILER ERROR  < ");
			D.String(source);
			IF position # Diagnostics.Invalid THEN D.String("@"); D.Int(position,1) END;
			IF errorCode # Diagnostics.Invalid THEN D.String(" "); D.Int(errorCode,1); END;
			D.String(" "); D.String(message);
			D.String(" > ---------------------- ");
			D.TraceBack
		END Error;

		PROCEDURE Warning*(CONST source : ARRAY OF CHAR; position, errorCode : LONGINT; CONST message : ARRAY OF CHAR);
		BEGIN
			IF diagnostics # NIL THEN
				diagnostics.Warning(source,position,errorCode,message);
			END;
		END Warning;

		PROCEDURE Information*(CONST source : ARRAY OF CHAR; position, errorCode : LONGINT; CONST message : ARRAY OF CHAR);
		BEGIN
			IF diagnostics # NIL THEN
				diagnostics.Information(source,position,errorCode,message);
			END;
		END Information;

	END TracingDiagnostics;

	PROCEDURE GetSymbolFileFormat*(CONST name: ARRAY OF CHAR): Formats.SymbolFileFormat;
	VAR
		procname: ARRAY 256 OF CHAR;
		factory: PROCEDURE (): Formats.SymbolFileFormat;
		symbolFileFormat: Formats.SymbolFileFormat;
	BEGIN
		symbolFileFormat := NIL;
		IF Strings.Length(name) > 0 THEN
			GETPROCEDURE(name,"Get", factory); (* try long name for example -G=OCBinarySymbolFile *)
			IF factory = NIL THEN (* try short name for example -G=Binary *)
				procname := "Fox";
				Strings.Append(procname, name);
				Strings.Append(procname, "SymbolFile");
				GETPROCEDURE(procname,"Get", factory);
			END;
			IF factory # NIL THEN
				symbolFileFormat := factory();
				Assert(symbolFileFormat # NIL,"symbol file factory returned NIL symbol file format");
			END;
		END;
		RETURN symbolFileFormat
	END GetSymbolFileFormat;

	PROCEDURE GetObjectFileFormat*(CONST name: ARRAY OF CHAR): Formats.ObjectFileFormat;
	VAR
		procname: ARRAY 256 OF CHAR;
		factory: PROCEDURE (): Formats.ObjectFileFormat;
		objectFileFormat: Formats.ObjectFileFormat;
	BEGIN
		objectFileFormat := NIL;
		IF Strings.Length(name) > 0 THEN
			GETPROCEDURE(name,"Get", factory); (* try long name for example -G=OCBinaryObjectFile *)
			IF factory = NIL THEN (* try short name for example -G=Binary*)
				procname := "Fox";
				Strings.Append(procname, name);
				Strings.Append(procname, "ObjectFile");
				GETPROCEDURE(procname,"Get", factory);
			END;
			IF factory # NIL THEN
				objectFileFormat := factory();
				Assert(objectFileFormat # NIL,"symbol file factory returned NIL symbol file format");
			END;
		END;
		RETURN objectFileFormat
	END GetObjectFileFormat;



	PROCEDURE GetActiveCellsSpecification(CONST name: ARRAY OF CHAR): ActiveCells.Specification;
	VAR
		procname: ARRAY 256 OF CHAR;
		factory: PROCEDURE (): ActiveCells.Specification;
		specification: ActiveCells.Specification;
	BEGIN
		specification := NIL;
		IF Strings.Length(name) > 0 THEN
			GETPROCEDURE(name,"Get", factory); (* try long name for example -G=OCBinaryObjectFile *)
			IF factory = NIL THEN (* try short name for example -G=Binary*)
				procname := "Fox";
				Strings.Append(procname, name);
				GETPROCEDURE(procname,"Get", factory);
			END;
			IF factory # NIL THEN
				specification := factory();
				ASSERT(specification # NIL);
			END;
		END;
		RETURN specification
	END GetActiveCellsSpecification;

	PROCEDURE Modules*(CONST source: ARRAY OF CHAR; (* source file name, for debugging and better error reports *)
			reader: Streams.Reader; (* reader to read from *)
			position: LONGINT; (* starting position in reader *)
			diagnostics: Diagnostics.Diagnostics; (* error output and status report *)
			flags: SET; (* general flags, special options are handled by components *)
			backend: Backend.Backend; (* backend: code generator *)
			symbolFileFormat: Formats.SymbolFileFormat;
			objectFileFormat: Formats.ObjectFileFormat;
			activeCellsSpecification: ActiveCells.Specification;
			log: Streams.Writer;
			VAR importCache: SyntaxTree.ModuleScope;
			CONST findPC: ARRAY OF CHAR (* locate a source code position providing a binary module offset *)
			): BOOLEAN;
	VAR
		module: SyntaxTree.Module;
		scanner: Scanner.Scanner;
		parser: Parser.Parser;
		checker: SemanticChecker.Checker;
		warnings: SemanticChecker.Warnings;
		printer: Printout.Printer;
		system: Global.System;
		generatedModule: Formats.GeneratedModule;
		name: SyntaxTree.String;
		activeCellsBackend: Backend.Backend;
		split: Strings.StringArray;
		sectionOffset: LONGINT;
		traceDiagnostics : TracingDiagnostics;

		PROCEDURE FinalMessage(error: BOOLEAN; CONST msg: ARRAY OF CHAR);
		VAR message,name: ARRAY 256 OF CHAR;
		BEGIN
			message := "";
			IF (module # NIL) & (module.context # SyntaxTree.invalidIdentifier) THEN
				Basic.GetString(module.context,message);
				Strings.Append (message, ".");
			ELSE
				message := "";
			END;
			IF (module # NIL) & (module.name # SyntaxTree.invalidIdentifier) THEN
				Basic.GetString(module.name,name);
				Strings.Append (message, name);
			END;
			Strings.Append (message, msg);
			IF error THEN
				IF diagnostics # NIL THEN
					diagnostics.Error (source, Diagnostics.Invalid, Diagnostics.Invalid, message);
				END;
			ELSE
				IF (log # NIL) & ~(Silent IN flags) & ~(FindPC IN flags) THEN
					log.String("compiling ");
					IF source # "" THEN 	log.String(source); log.String(" => ");	END;
					log.String(message); log.Ln;
				END;
			END;
		END FinalMessage;

		PROCEDURE PrintModule;
		VAR print: Streams.Writer;
		BEGIN
			print := Basic.GetWriter(Basic.GetDebugWriter("Compiler Debug Output"));
			IF Info IN flags THEN
				printer := Printout.NewPrinter(print,Printout.All,Info IN flags);
			ELSE
				printer := Printout.NewPrinter(print,Printout.SourceCode,Info IN flags);
			END;
			print.Ln; printer.Module(module); print.Ln;
			print.Update;
		END PrintModule;


	BEGIN
		IF TraceError IN flags THEN
			NEW(traceDiagnostics,diagnostics); diagnostics := traceDiagnostics
		END;

		IF backend = NIL THEN
			system := Global.DefaultSystem()
		ELSE
			system := backend.GetSystem();
		END;
		IF (objectFileFormat # NIL) & (objectFileFormat.ForceModuleBodies()) THEN INCL(flags, ForceModuleBodies) END;

		scanner := Scanner.NewScanner(source,reader,position,diagnostics);
		IF DataFlow IN flags THEN
			Global.NewBuiltin(Global.Connect,"CONNECT",system.globalScope,FALSE);
			Global.NewBuiltin(Global.Receive,"RECEIVE",system.globalScope,FALSE);
			Global.NewBuiltin(Global.Send,"SEND",system.globalScope,FALSE);
			Global.NewBuiltin(Global.Delegate,"DELEGATE",system.globalScope,FALSE);
			Global.NewBuiltin(Global.systemHardwareAddress,"HWADR",system.systemScope,FALSE);
			activeCellsBackend := Backend.GetBackendByName("FoxActiveCellsBackend");
			IF activeCellsBackend = NIL THEN FinalMessage(TRUE,"could not install activeCells backend"); RETURN FALSE END;
		END;
		parser := Parser.NewParser( scanner, diagnostics );
		IF DataFlow IN flags THEN parser.ActiveCellsSupport END;
		REPEAT
			(** first phase: scan and parse **)
			module := parser.Module();
			IF parser.error THEN
				FinalMessage(TRUE," could not be compiled (parser errors).");
				RETURN FALSE;
			END;
			ASSERT(module # NIL);

			IF Check IN flags THEN
				(** second phase: check and resolve symbols **)
				IF (symbolFileFormat # NIL) THEN
					symbolFileFormat.Initialize(diagnostics,system);
				END;
				checker := SemanticChecker.NewChecker(diagnostics,Info IN flags,UseDarwinCCalls IN flags,system,symbolFileFormat,activeCellsSpecification,importCache);
				checker.Module(module);
				IF checker.error THEN
					FinalMessage(TRUE," could not be compiled (checker errors).");
					RETURN FALSE
				ELSIF Warnings IN flags THEN
					warnings := SemanticChecker.NewWarnings(diagnostics);
					warnings.Module(module);
				END;

				IF Print IN flags THEN PrintModule END;

				IF activeCellsSpecification # NIL THEN
					Global.GetSymbolName(module,name);
					activeCellsSpecification.Init(name,diagnostics,log)
				END;

				(** third phase: generate code, can consist of sub-phases (such as intermediate backend / hardware backend) **)
				IF backend # NIL THEN
					backend.Initialize(diagnostics, log, flags, checker, system, activeCellsSpecification);
					IF findPC # "" THEN
						split := Strings.Split(findPC,":");
						IF LEN(split)>1 THEN
							Strings.StrToInt(split[1]^,sectionOffset);
						ELSE
							sectionOffset := 0;
						END;
						backend.FindPC(module, split[0]^,sectionOffset);
						IF backend.error THEN
							FinalMessage(TRUE," could not be compiled (backend errors).");
							RETURN FALSE
						ELSE
							RETURN TRUE
						END;
					END;
					generatedModule := backend.ProcessSyntaxTreeModule(module);
					IF backend.error THEN
						FinalMessage(TRUE, " could not be compiled (backend errors).");
						RETURN FALSE
					END;
				END;


				(** generate symbol file **)
				IF (symbolFileFormat # NIL) & ~symbolFileFormat.Export(module, importCache) THEN
					FinalMessage(TRUE, " could not be compiled (symbol File errors).");
					RETURN FALSE
				END;

				(** generate object file **)
				IF objectFileFormat # NIL THEN
					objectFileFormat.Initialize(diagnostics);
					IF generatedModule = NIL THEN
						FinalMessage(TRUE, " could not write object file (nothing generated).");
						RETURN FALSE
					ELSIF ~objectFileFormat.Export(generatedModule,symbolFileFormat) THEN
						FinalMessage(TRUE, " could not be compiled (object file errors).");
						RETURN FALSE
					END;
				END;

				IF activeCellsSpecification # NIL THEN
					activeCellsBackend.Initialize(diagnostics,log, flags,checker,system,activeCellsSpecification);
					generatedModule := activeCellsBackend.ProcessSyntaxTreeModule(module);
					IF activeCellsBackend.error THEN
						FinalMessage(TRUE, " could not be compiled (activeCells backend errors)");
						RETURN FALSE
					END;
				END;
				FinalMessage(FALSE, " done.");

				IF activeCellsSpecification = NIL THEN (* no activeCells *)
				ELSIF (activeCellsSpecification.types.Length() = 0) & (activeCellsSpecification.instances.Length()=0) THEN (* nothing defined *)
				ELSE
					IF ~activeCellsSpecification.Link(diagnostics,system.codeUnit, system.dataUnit) THEN
						FinalMessage(TRUE, " could not link"); RETURN FALSE
					ELSIF ~activeCellsSpecification.Emit() THEN
						FinalMessage(TRUE, " could not emit backend specification"); RETURN FALSE;
					END;
				END;
			ELSIF Print IN flags THEN
				PrintModule;
				FinalMessage(FALSE, " done.")
			ELSE
				FinalMessage(FALSE, " done.");
			END;
		UNTIL (SingleModule IN flags) OR ~parser.NextModule();

		RETURN TRUE;
	END Modules;

	PROCEDURE GetOptions*(input: Streams.Reader; error:Streams.Writer; diagnostics: Diagnostics.Diagnostics; VAR flags: SET;
		VAR backend: Backend.Backend;
		VAR symbolFile: Formats.SymbolFileFormat;
		VAR objectFile: Formats.ObjectFileFormat;
		VAR activeCellsSpecification: ActiveCells.Specification;
		VAR findPC: ARRAY OF CHAR
		): BOOLEAN;
	VAR options: Options.Options;  name: ARRAY 256 OF CHAR; result: BOOLEAN; position: LONGINT;
		parsed: BOOLEAN;

		PROCEDURE Error(CONST error: ARRAY OF CHAR);
		BEGIN
			IF diagnostics # NIL THEN
				diagnostics.Error("",Diagnostics.Invalid,Diagnostics.Invalid,error);
			END;
		END Error;

	BEGIN
		result := TRUE;
		NEW(options);
		options.Add("p","print",Options.Flag);
		options.Add(0X,"silent",Options.Flag);
		options.Add("c","check",Options.Flag);
		options.Add("e","traceError",Options.Flag);
		options.Add("I","interface",Options.Flag);
		options.Add("i","info",Options.Flag);
		options.Add("b","backend",Options.String);
		options.Add("f","findPC",Options.String);
		options.Add(0X,"singleModule",Options.Flag);
		options.Add(0X, "symbolFile", Options.String);
		options.Add(0X, "objectFile", Options.String);
		options.Add("d","activeCells", Options.Flag);
		options.Add("w","warnings", Options.Flag);
		options.Add(0X,"darwinHost", Options.Flag);
		options.Add(0X,"activeCellsSpecification", Options.String);


		position := input.Pos();
		parsed := options.Parse(input,NIL);

		IF options.GetString("b", name) THEN
			IF name = "" THEN backend := NIL
			ELSE
				backend := Backend.GetBackendByName(name);
				IF (backend = NIL)  THEN
					Error("backend could not be installed"); result := FALSE;
				END;
			END;
		ELSE backend := Backend.GetBackendByName(DefaultBackend);
			IF backend = NIL THEN Error("default backend could not be installed"); result := FALSE END;
		END;

		IF options.GetString("objectFile",name) THEN
			IF name = "" THEN objectFile := NIL
			ELSE
				objectFile := GetObjectFileFormat(name);
				IF objectFile = NIL THEN Error("object file format could not be installed"); result := FALSE END;
			END;
		ELSIF backend # NIL THEN
			objectFile := backend.DefaultObjectFileFormat();
		END;

		IF options.GetString("symbolFile",name) THEN
			IF name = "" THEN symbolFile := NIL
			ELSE
				symbolFile := GetSymbolFileFormat(name);
				IF symbolFile = NIL THEN Error("symbol file format could not be installed"); result := FALSE END;
			END;
		ELSIF backend # NIL THEN
			symbolFile := backend.DefaultSymbolFileFormat();
			IF (symbolFile = NIL) & (objectFile # NIL) THEN
				symbolFile := objectFile.DefaultSymbolFileFormat();
			END;
		ELSIF objectFile # NIL THEN
			symbolFile := objectFile.DefaultSymbolFileFormat();
		END;

		IF options.GetString("activeCellsSpecification",name) THEN
			activeCellsSpecification := GetActiveCellsSpecification(name);
		ELSIF options.GetFlag("activeCells") THEN
			NEW(activeCellsSpecification,"",diagnostics,NIL);
		END;
		
		IF backend # NIL THEN backend.DefineOptions (options); INCL(flags,Check); END;
		IF symbolFile # NIL THEN symbolFile.DefineOptions(options); INCL(flags,Check) END;
		IF objectFile # NIL THEN objectFile.DefineOptions(options); INCL(flags,Check) END;

		IF result & ~parsed THEN
			options.Clear;
			input.SetPos(position);
			result := options.Parse(input,error)
		END;

		IF result THEN
			IF options.GetFlag("print") THEN INCL(flags, Print) END;
			IF options.GetFlag("silent") THEN INCL(flags, Silent) END;
			IF options.GetFlag("check") THEN INCL(flags, Check) END;
			IF options.GetFlag("traceError") THEN INCL(flags, TraceError) END;
			IF options.GetFlag("info") THEN INCL(flags,Info) END;
			IF options.GetString("findPC",findPC) THEN INCL(flags,FindPC) END;
			IF options.GetFlag("warnings") THEN INCL(flags, Warnings) END;
			IF options.GetFlag("darwinHost") THEN INCL(flags,UseDarwinCCalls) END;	(*fld*)
			IF options.GetFlag("singleModule") THEN INCL(flags,SingleModule) END;
			IF backend # NIL THEN backend.GetOptions (options) END;
			IF symbolFile # NIL THEN symbolFile.GetOptions(options) END;
			IF objectFile # NIL THEN objectFile.GetOptions(options) END;
			IF activeCellsSpecification # NIL THEN INCL(flags, DataFlow) END;
		END;
		RETURN result
	END GetOptions;


	PROCEDURE Compile*(context : Commands.Context);
	VAR
		filename: ARRAY 256 OF CHAR;
		error: BOOLEAN;
		diagnostics: Diagnostics.StreamDiagnostics;
		time: LONGINT; reader: Streams.Reader;
		flags: SET;
		backend: Backend.Backend;
		importCache: SyntaxTree.ModuleScope;
		symbolFileFormat: Formats.SymbolFileFormat;
		objectFile: Formats.ObjectFileFormat;
		activeCellsSpecification: ActiveCells.Specification;
		findPC: SyntaxTree.String;
	BEGIN
		error := FALSE;

		NEW(diagnostics, context.error);
		IF GetOptions(context.arg,context.error,diagnostics,flags,backend,symbolFileFormat,objectFile,activeCellsSpecification,findPC) THEN

			time := Kernel.GetTicks();
			WHILE context.arg.GetString(filename) & (filename # ";") & ~error DO
				reader := Basic.GetFileReader(filename);
				IF reader = NIL THEN
					diagnostics.Error (filename, Diagnostics.Invalid, Diagnostics.Invalid, "failed to open"); error := TRUE;
				ELSE
					error := ~Modules(filename, reader, 0, diagnostics, flags, backend, symbolFileFormat,objectFile,activeCellsSpecification, context.out, importCache,findPC);
				END;
				context.out.Update;
				context.error.Update;
			END;
			IF Silent IN flags THEN
				time := Kernel.GetTicks()-time;
				context.out.Ln; context.out.String("compiler elapsed ms"); context.out.Int(time,10);
			END;
		END;
	END Compile;
	
	PROCEDURE Assemble*(context: Commands.Context);
	VAR
		diagnostics: Diagnostics.StreamDiagnostics;	
		flags: SET;
		defaultBackend: Backend.Backend;
		objectFileFormat: Formats.ObjectFileFormat;
		dummySymbolFileFormat: Formats.SymbolFileFormat;
		dummyDataflowSpecification: ActiveCells.Specification;
		rootModuleName, dummyString: SyntaxTree.String;
		assemblinker: IntermediateCodeAssembler.Assemblinker;
	BEGIN	
		NEW(diagnostics, context.out);
		IF GetOptions(context.arg, context.error, diagnostics, flags, defaultBackend, dummySymbolFileFormat, objectFileFormat, dummyDataflowSpecification, dummyString) THEN
			(* TODO: handle flags, such as 'Print', 'Silent' and 'TraceError'? *)

			(* TODO: handle multiple module names? *)
			IF context.arg.GetString(rootModuleName) THEN
				NEW(assemblinker, diagnostics, defaultBackend);
				IF assemblinker.LoadModule(rootModuleName, FALSE) THEN
					assemblinker.MarkReachabilityOfAll(TRUE);
				 	IF assemblinker.GenerateObjectFile(objectFileFormat, context.out, flags, NIL, NIL) THEN
						diagnostics.Information(rootModuleName, Diagnostics.Invalid, Diagnostics.Invalid, "done.");
					END
				END
			ELSE
				diagnostics.Error("", Diagnostics.Invalid, Diagnostics.Invalid, "root module name not specified");
				context.out.Update
			END	
	 	END
	END Assemble;
	
	PROCEDURE CompileReader*(context: Commands.Context; reader: Streams.Reader);
	VAR
		filename: ARRAY 256 OF CHAR;
		error: BOOLEAN;
		diagnostics: Diagnostics.StreamDiagnostics;
		time: LONGINT;
		flags: SET;
		backend: Backend.Backend;
		importCache: SyntaxTree.ModuleScope;
		symbolFileFormat: Formats.SymbolFileFormat;
		objectFile: Formats.ObjectFileFormat;
		activeCellsSpecification: ActiveCells.Specification;
		findPC: SyntaxTree.String;
	BEGIN
		error := FALSE;
		NEW(diagnostics, context.error);
		IF GetOptions(context.arg,context.error,diagnostics,flags,backend,symbolFileFormat,objectFile,activeCellsSpecification,findPC) THEN

			time := Kernel.GetTicks();
			IF reader = NIL THEN
				diagnostics.Error (filename, Diagnostics.Invalid, Diagnostics.Invalid, "failed to open"); error := TRUE;
			ELSE
				error := ~Modules(filename, reader, 0, diagnostics, flags, backend, symbolFileFormat,objectFile,activeCellsSpecification, context.out, importCache,findPC);
			END;
			context.out.Update;
		END;
	END CompileReader;

	PROCEDURE Assert(b: BOOLEAN; CONST reason: ARRAY OF CHAR);
	BEGIN
		ASSERT(b);
	END Assert;

END Compiler.

