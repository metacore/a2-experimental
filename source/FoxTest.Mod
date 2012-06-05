MODULE FoxTest;	(** AUTHOR "fof"; PURPOSE "Fox tester"; *)
(* (c) fof ETH Zürich, 2008 *)

IMPORT Basic := FoxBasic, TestSuite, Diagnostics, Streams, Commands, Shell, Options, Files;

TYPE
	Command = ARRAY 256 OF CHAR;

	Tester = OBJECT (TestSuite.Tester)
	VAR
		log: Streams.Writer;
		verbose, mayTrap: BOOLEAN;
		command, prolog, epilog: Command;
		fileName: Files.FileName;

		PROCEDURE &InitTester (log: Streams.Writer;  diagnostics: Diagnostics.Diagnostics; verbose,mayTrap: BOOLEAN; CONST prolog, command, epilog: Command; CONST fileName: ARRAY OF CHAR);
		BEGIN
			Init (diagnostics); SELF.log := log; SELF.verbose := verbose; SELF.mayTrap := mayTrap;
			COPY(prolog, SELF.prolog);
			COPY(epilog, SELF.epilog);
			COPY(command, SELF.command);
			COPY(fileName, SELF.fileName);
		END InitTester;

		PROCEDURE Handle (r: Streams.Reader; position: LONGINT; CONST name: ARRAY OF CHAR; type: TestSuite.TestType): INTEGER;
		VAR result: INTEGER; msg: ARRAY 128 OF CHAR; res: LONGINT; f: Files.File; w: Files.Writer; ch: CHAR;
		BEGIN
			result := TestSuite.Failure;
			IF verbose THEN log.String ("testing: "); log.String (name); log.Ln END;

			(* prepare tester input as a file for all test cases *)
			f := Files.New("TesterInput.txt");
			NEW(w,f,0);
			WHILE r.Available() > 0 DO
				r.Char(ch); w.Char(ch)
			END;
			w.Update;
			Files.Register(f);

			res := Commands.Ok;
			IF prolog # "" THEN
				Commands.Call(prolog, {Commands.Wait}, res, msg);
				IF (res # Commands.Ok) & verbose  THEN
					log.String("prolog failed: "); log.String(msg); log.Ln;
				END;
			END;

			IF (command # "") & (res = Commands.Ok) THEN
				Commands.Call(command, {Commands.Wait}, res, msg);
				IF res = Commands.Ok THEN
					result := TestSuite.Positive
				ELSIF (res < 3500) & (res >= 3440) THEN (* loader error *)
					result := TestSuite.Failure
				ELSIF ~mayTrap & (res = Commands.CommandTrapped) THEN (* command error, trap *)
					result := TestSuite.Failure
				ELSE
					result := TestSuite.Negative
				END;
				IF (result # type) & verbose THEN
					log.String (msg); log.Ln;
				END;
			ELSIF (command # "") THEN result := TestSuite.Failure
			END;

			IF epilog # "" THEN
				Commands.Call(epilog, {Commands.Wait}, res, msg);
			END
		FINALLY
			RETURN result;
		END Handle;

	END Tester;

	PROCEDURE DriveTest (context: Commands.Context);
	VAR
		diagnostics: Diagnostics.StreamDiagnostics; tester: Tester; writer: Streams.Writer; prolog, epilog, command: Command;
		options: Options.Options; verbose, mayTrap: BOOLEAN; report: TestSuite.StreamReport; fileName: Files.FileName;
	BEGIN
		IF (context.caller # NIL) & (context.caller IS Shell.Shell) THEN
			writer := context.out
		ELSE
			writer := Basic.GetDebugWriter("Oberon Compiler Test Results")
		END;
		NEW(options);

		options.Add("p","prolog", Options.String);
		options.Add("e","epilog", Options.String);
		options.Add("c","command", Options.String);
		options.Add("v","verbose",Options.Flag);
		options.Add("t","mayTrap",Options.Flag);
		options.Add("f","fileName",Options.String);

		NEW (diagnostics, writer);
		IF options.Parse(context.arg,context.error) THEN
			IF ~options.GetString("p", prolog) THEN prolog := "" END;
			IF ~options.GetString("c",  command) THEN command := "" END;
			IF ~options.GetString("e", epilog) THEN epilog := "" END;
			IF ~options.GetString("f", fileName) THEN fileName := "TesterInput.txt" END;
			mayTrap := options.GetFlag("t");
			verbose := options.GetFlag("verbose");
			NEW (tester, writer, diagnostics, verbose, mayTrap, prolog, command, epilog, fileName);
			NEW (report, writer);
			TestSuite.Drive (context, tester);
			tester.Print (report);
		END;
		writer.Update;
	END DriveTest;

	PROCEDURE Compile* (context: Commands.Context);
	BEGIN DriveTest (context);
	END Compile;

END FoxTest.

SystemTools.Free FoxTest TestSuite~

	FoxTest.Compile
		--verbose --mayTrap
		--prolog="Compiler.Compile TesterInput.txt"
		--command="SystemTools.Free Test Dummy B A;SystemTools.Load Test"
	Oberon.Execution.Test Oberon.Execution.AMD64TestDiff ~

	FoxTest.Compile
		--verbose
		--command="Compiler.Compile TesterInput.txt"
	Oberon.Compilation.Test Oberon.Compilation.AMD64TestDiff ~
