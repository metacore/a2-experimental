MODULE Compiler;   (**  AUTHOR "fof & fn"; PURPOSE "Oberon Compiler Command Interface";  **)
(* (c) fof ETH Zürich, 2008 *)

IMPORT
	Scanner := OCScanner, Parser := OCParser,
	SemanticChecker := OCSemanticChecker, SyntaxTree := OCSyntaxTree, Formats := OCFormats,  WMUtilities, D := Debugging,
	Streams, TextUtilities, Commands,Diagnostics, Options, Kernel, Printout := OCPrintout, Backend := OCBackend,Strings, Global := OCGlobal
	,Texts,CompilerInterface, Dataflow := OCDataflow;

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

	Name = "OC";
	Description = "Oberon Compiler";
	FileExtension = "MOD"; (*! temporary *)
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
				procname := "OC";
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
				procname := "OC";
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

	PROCEDURE GetBackend*(CONST name: ARRAY OF CHAR):Backend.Backend;
	VAR
		procname: ARRAY 256 OF CHAR;
		factory: PROCEDURE (): Backend.Backend;
		backend: Backend.Backend;
	BEGIN
		backend := NIL;
		IF Strings.Length(name) > 0 THEN
			GETPROCEDURE(name,"Get", factory); (* try long name for example -G=OCERABackend *)

			IF factory = NIL THEN (* try short name for example -G=ERA*)
				procname := "OC";
				Strings.Append(procname, name);
				Strings.Append(procname, "Backend");
				GETPROCEDURE(procname,"Get", factory);
			END;

			IF factory # NIL THEN
				backend := factory();
				Assert(backend # NIL,"backend factory returned NIL backend");
			END;
		END;
		RETURN backend
	END GetBackend;

	PROCEDURE GetDataflowSpecification(CONST name: ARRAY OF CHAR): Dataflow.Specification;
	VAR
		procname: ARRAY 256 OF CHAR;
		factory: PROCEDURE (): Dataflow.Specification;
		specification: Dataflow.Specification;
	BEGIN
		specification := NIL;
		IF Strings.Length(name) > 0 THEN
			GETPROCEDURE(name,"Get", factory); (* try long name for example -G=OCBinaryObjectFile *)
			IF factory = NIL THEN (* try short name for example -G=Binary*)
				procname := "OC";
				Strings.Append(procname, name);
				GETPROCEDURE(procname,"Get", factory);
			END;
			IF factory # NIL THEN
				specification := factory();
				ASSERT(specification # NIL);
			END;
		END;
		RETURN specification
	END GetDataflowSpecification;

	PROCEDURE Module*(	CONST source: ARRAY OF CHAR; (* source file name, for debugging and better error reports *)
								reader: Streams.Reader; (* reader to read from *)
								position: LONGINT; (* starting position in reader *)
								diagnostics: Diagnostics.Diagnostics; (* error output and status report *)
								flags: SET; (* general flags, special options are handled by components *)
								backend: Backend.Backend; (* backend: code generator *)
								symbolFileFormat: Formats.SymbolFileFormat;
								objectFileFormat: Formats.ObjectFileFormat;
								dataflowSpecification: Dataflow.Specification;
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
		dataflowBackend: Backend.Backend;
		split: Strings.StringArray;
		sectionOffset: LONGINT;
		traceDiagnostics : TracingDiagnostics;

		PROCEDURE FinalMessage(error: BOOLEAN; CONST msg: ARRAY OF CHAR);
		VAR message,name: ARRAY 256 OF CHAR;
		BEGIN
			IF diagnostics # NIL THEN
				message := "";
				IF (module # NIL) & (module.context # NIL) THEN
					module.context.GetString(message);
					Strings.Append (message, ".");
				ELSE
					message := "";
				END;
				IF (module # NIL) & (module.name # NIL) THEN
					module.name.GetString(name);
					Strings.Append (message, name);
				END;
				Strings.Append (message, msg);
				IF error THEN
					diagnostics.Error (source, Diagnostics.Invalid, Diagnostics.Invalid, message);
				ELSE
					diagnostics.Information (source, Diagnostics.Invalid, Diagnostics.Invalid, message);
				END;
			END
		END FinalMessage;

		PROCEDURE Log;
		BEGIN
			(** logging and tracing **)
			IF (log # NIL) THEN
				IF Print IN flags THEN
					IF Info IN flags THEN
						printer := Printout.NewPrinter(log,Printout.All,Info IN flags);
					ELSE
						printer := Printout.NewPrinter(log,Printout.SourceCode,Info IN flags);
					END;
					log.Ln; printer.Module(module); log.Ln;
					log.Update;
				END;
			END;
		END Log;


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
			dataflowBackend := GetBackend("OCDataflowBackend");
			IF dataflowBackend = NIL THEN FinalMessage(TRUE,"could not install dataflow backend"); RETURN FALSE END;
		END;
		parser := Parser.NewParser( scanner, diagnostics );
		IF DataFlow IN flags THEN
			parser.DataflowSupport
		END;
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
				checker := SemanticChecker.NewChecker(diagnostics,Info IN flags,system,symbolFileFormat,dataflowSpecification,importCache);
				checker.Module(module);
				IF checker.error THEN
					FinalMessage(TRUE," could not be compiled (checker errors).");
					RETURN FALSE
				ELSIF Warnings IN flags THEN
					warnings := SemanticChecker.NewWarnings(diagnostics);
					warnings.Module(module);
				END;

				Log;

				IF dataflowSpecification # NIL THEN
					Global.GetSymbolName(module,name);
					dataflowSpecification.Init(name,diagnostics)
				END;

				(** third phase: generate code, can consist of sub-phases (such as intermediate backend / hardware backend) **)
				IF backend # NIL THEN
					backend.Initialize(diagnostics, flags, checker, system, dataflowSpecification);
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
					generatedModule := backend.Module(module);
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
					ELSE
						(*
						IF FindPC IN flags THEN generatedModule.SetFindPC(findPC) END;
						*)
						IF ~objectFileFormat.Export(generatedModule,symbolFileFormat) THEN
							FinalMessage(TRUE, " could not be compiled (object file errors).");
							RETURN FALSE
						END;
					END;
				END;

				IF dataflowSpecification # NIL THEN
					dataflowBackend.Initialize(diagnostics,flags,checker,system,dataflowSpecification);
					generatedModule := dataflowBackend.Module(module);
					IF dataflowBackend.error THEN
						FinalMessage(TRUE, " could not be compiled (dataflow backend errors)");
						RETURN FALSE
					END;
				END;

				IF dataflowSpecification = NIL THEN (* no dataflow *)
				ELSIF (dataflowSpecification.types.Length() = 0) & (dataflowSpecification.instances.Length()=0) THEN (* nothing defined *)
				ELSIF ~dataflowSpecification.Link(diagnostics,Info IN flags) THEN
					FinalMessage(TRUE, " could not link"); RETURN FALSE
				ELSIF ~dataflowSpecification.Emit() THEN
					FinalMessage(TRUE, " could not emit backend specification"); RETURN FALSE;
				END;

			ELSE Log;
			END;
			IF ~(Silent IN flags) & ~(FindPC IN flags) THEN
				FinalMessage(FALSE, " successfully compiled.")
			END;
		UNTIL ~parser.NextModule();
		RETURN TRUE;
	END Module;

	PROCEDURE GetOptions*(input: Streams.Reader; error:Streams.Writer; diagnostics: Diagnostics.Diagnostics; VAR flags: SET;
		VAR backend: Backend.Backend;
		VAR symbolFile: Formats.SymbolFileFormat;
		VAR objectFile: Formats.ObjectFileFormat;
		VAR dataflowSpecification: Dataflow.Specification;
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
		options.Add(0X, "symbolFile", Options.String);
		options.Add(0X, "objectFile", Options.String);
		options.Add("d","dataflow", Options.Flag);
		options.Add("w","warnings", Options.Flag);
		options.Add(0X,"dataflowSpecification", Options.String);

		position := input.Pos();
		parsed := options.Parse(input,NIL);

		IF options.GetString("b", name) THEN
			IF name = "" THEN backend := NIL
			ELSE
				backend := GetBackend(name);
				IF (backend = NIL)  THEN
					Error("backend could not be installed"); result := FALSE;
				END;
			END;
		ELSE backend := GetBackend(DefaultBackend);
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

		IF options.GetString("dataflowSpecification",name) THEN
			dataflowSpecification := GetDataflowSpecification(name);
		ELSIF options.GetFlag("dataflow") THEN
			NEW(dataflowSpecification,"",diagnostics);
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
			IF backend # NIL THEN backend.GetOptions (options) END;
			IF symbolFile # NIL THEN symbolFile.GetOptions(options) END;
			IF objectFile # NIL THEN objectFile.GetOptions(options) END;
			IF dataflowSpecification # NIL THEN INCL(flags, DataFlow) END;
		END;
		RETURN result
	END GetOptions;

	PROCEDURE GetClipboardReader(): Streams.Reader;
	VAR a, b : LONGINT;
		selectionText: Texts.Text;
		pcStr: POINTER TO ARRAY OF CHAR;
		stringReader: Streams.StringReader;
	BEGIN
		selectionText := Texts.clipboard;
		selectionText.AcquireRead;
		a := 0;
		b := selectionText.GetLength();
		NEW(pcStr,b-a+1);
		TextUtilities.SubTextToStr(selectionText,0,b-a+1,pcStr^);
		selectionText.ReleaseRead;
		NEW(stringReader,b-a+1);
		stringReader.Set(pcStr^);
		RETURN stringReader;
	END GetClipboardReader;

	PROCEDURE GetSelectionReader(): Streams.Reader;
	VAR a, b : LONGINT;
		selectionText: Texts.Text;
		from, to: Texts.TextPosition;
		pcStr: POINTER TO ARRAY OF CHAR;
		stringReader: Streams.StringReader;
	BEGIN
		IF Texts.GetLastSelection(selectionText, from, to) THEN
			selectionText.AcquireRead;
			a := Strings.Min(from.GetPosition(), to.GetPosition());
			b := Strings.Max(from.GetPosition(), to.GetPosition());
			NEW(pcStr,b-a+1);
			TextUtilities.SubTextToStr(selectionText, a, b - a+1, pcStr^);
			selectionText.ReleaseRead;
			NEW(stringReader,b-a+1);
			stringReader.Set(pcStr^);
		ELSE
			stringReader  := NIL;
		END;
		RETURN stringReader;
	END GetSelectionReader;

	PROCEDURE GetTextReader(text: Texts.Text; position: LONGINT): Streams.Reader;
	VAR a, b : LONGINT;
		pcStr: POINTER TO ARRAY OF CHAR;
		stringReader: Streams.StringReader;
	BEGIN
		text.AcquireRead;
		a := position;
		b := text.GetLength();
		NEW(pcStr,b-a+1);
		TextUtilities.SubTextToStr(text,0,b-a+1,pcStr^);
		text.ReleaseRead;
		NEW(stringReader,b-a+1);
		stringReader.Set(pcStr^);
		RETURN stringReader;
	END GetTextReader;


	PROCEDURE Compile*(context : Commands.Context);
	VAR
		filename: ARRAY 256 OF CHAR;
		error: BOOLEAN; log: WMUtilities.WindowWriter;
		diagnostics: Diagnostics.StreamDiagnostics;
		time: LONGINT; reader: Streams.Reader;
		flags: SET;
		backend: Backend.Backend;
		importCache: SyntaxTree.ModuleScope;
		symbolFileFormat: Formats.SymbolFileFormat;
		objectFile: Formats.ObjectFileFormat;
		dataflowSpecification: Dataflow.Specification;
		findPC: SyntaxTree.String;
	BEGIN
		error := FALSE;

		NEW(diagnostics, context.out);
		IF GetOptions(context.arg,context.error,diagnostics,flags,backend,symbolFileFormat,objectFile,dataflowSpecification,findPC) THEN

			IF (Print IN flags) THEN
				NEW(log,"Compiler",600,800,TRUE); log.SetFontSize(10);
			ELSE
				log := NIL;
			END;

			time := Kernel.GetTicks();
			WHILE context.arg.GetString(filename) & (filename # ";") & ~error DO
				IF filename = "@Selection" THEN
					reader := GetSelectionReader();
				ELSIF filename = "@Clipboard" THEN
					reader := GetClipboardReader();
				ELSE
					reader := TextUtilities.GetTextReader(filename);
				END;
				IF reader = NIL THEN
					diagnostics.Error (filename, Diagnostics.Invalid, Diagnostics.Invalid, "failed to open"); error := TRUE;
				ELSE
					error := ~Module(filename, reader, 0, diagnostics, flags, backend, symbolFileFormat,objectFile,dataflowSpecification, log, importCache,findPC);
				END;
				context.out.Update;
			END;
			IF Silent IN flags THEN
				time := Kernel.GetTicks()-time;
				context.out.Ln; context.out.String("compiler elapsed ms"); context.out.Int(time,10);
			END;
		END;
	END Compile;


	PROCEDURE CompileText*(t: Texts.Text; CONST source: ARRAY OF CHAR; pos: LONGINT; CONST pc,opt: ARRAY OF CHAR; log: Streams.Writer;
	diagnostics : Diagnostics.Diagnostics; VAR error: BOOLEAN);
	VAR stringReader: Streams.StringReader;
		backend: Backend.Backend;
		importCache: SyntaxTree.ModuleScope;
		symbolFile: Formats.SymbolFileFormat;
		objectFile: Formats.ObjectFileFormat;
		dataflowSpecification: Dataflow.Specification;
		findPC: SyntaxTree.String; flags: SET;
		reader: Streams.Reader;
	BEGIN
		IF t = NIL THEN
			log.String ("No text available"); log.Ln; log.Update;
			error := TRUE; RETURN
		END;
		NEW(stringReader,LEN(opt));
		stringReader.Set(opt);
		IF GetOptions(stringReader,log,diagnostics,flags,backend,symbolFile,objectFile,dataflowSpecification, findPC) THEN
			reader := GetTextReader(t,pos);
			IF pc # "" THEN INCL(flags,FindPC); COPY(pc, findPC);
			ELSIF findPC # "" THEN INCL(flags,FindPC)
			END;
			error := ~Module(source,reader,0,diagnostics,flags,backend,symbolFile,objectFile,dataflowSpecification, log,importCache,findPC)
		END;
	END CompileText;

	PROCEDURE Assert(b: BOOLEAN; CONST reason: ARRAY OF CHAR);
	BEGIN
		ASSERT(b);
	END Assert;

BEGIN
	CompilerInterface.Register(Name, Description, FileExtension, CompileText);
END Compiler.

