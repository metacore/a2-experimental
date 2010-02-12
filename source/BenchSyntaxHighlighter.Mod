MODULE BenchSyntaxHighlighter; (** AUTHOR "staubesv"; PURPOSE "Benchmarks for SyntaxHighlighter"; *)

IMPORT
	Commands, Options, Dates, Strings, Files, Texts, TextUtilities, SyntaxHighlighter;

CONST
	DefaultHighlighterName = "Oberon";
	DefaultNofIterations = 1000;

PROCEDURE Words(reader : Texts.TextReader; highlighter : SyntaxHighlighter.Highlighter; nofIterations : LONGINT);
VAR
	char32 : Texts.Char32; attributes : Texts.Attributes;
	wordStart, wordEnd, readerPosition, savedPosition, i : LONGINT;
	word : ARRAY 128 OF CHAR;
BEGIN
	ASSERT((reader # NIL) & (highlighter # NIL) & (nofIterations > 0));
	FOR i := 1 TO nofIterations DO
		wordEnd := -1;
		reader.SetPosition(0);
		REPEAT
			readerPosition := reader.GetPosition();
			reader.ReadCh(char32);
			savedPosition := reader.GetPosition();
			IF (savedPosition > wordEnd) & SyntaxHighlighter.IsValid(char32) THEN
				wordStart := SyntaxHighlighter.FindWordStart(reader, readerPosition);
				wordEnd := SyntaxHighlighter.FindWordEnd(reader, readerPosition);
				SyntaxHighlighter.GetWord(reader, wordStart, wordEnd, word);
				attributes := highlighter.GetAttributes(word);
				reader.SetPosition(savedPosition);
			END;
		UNTIL reader.eot;
	END;
END Words;

PROCEDURE Bench*(context : Commands.Context); (** [Options] filename ~ *)
VAR
	filename : Files.FileName; highlighterName : ARRAY 64 OF CHAR; nofIterations : LONGINT;
	options : Options.Options;
	text : Texts.Text; reader : Texts.TextReader;
	format, res : LONGINT;
	highlighter : SyntaxHighlighter.Highlighter;
	startTime, endTime : Dates.DateTime;
BEGIN
	NEW(options);
	options.Add("h", "highlighter"	, Options.String);
	options.Add("n", "nofIterations", Options.Integer);
	IF options.Parse(context.arg, context.error) THEN
		context.arg.GetString(filename);
		IF ~options.GetString("highlighter", highlighterName) THEN highlighterName := DefaultHighlighterName; END;
		IF ~options.GetInteger("nofIterations", nofIterations) THEN nofIterations := DefaultNofIterations; END;
		IF (nofIterations > 0) THEN
			highlighter := SyntaxHighlighter.GetHighlighter(highlighterName);
			IF (highlighter # NIL) THEN
				NEW(text);
				TextUtilities.LoadAuto(text, filename, format, res);
				IF (res = 0) THEN
					NEW(reader, text);
					text.AcquireRead;
					context.out.String("Match words in file "); context.out.String(filename); context.out.String(" ");
					context.out.Int(nofIterations, 0); context.out.String(" times ... "); context.out.Update;
					startTime := Dates.Now();
					Words(reader, highlighter, nofIterations);
					endTime := Dates.Now();
					Strings.ShowTimeDifference(startTime, endTime, context.out);
					context.out.Ln;
					text.ReleaseRead;
				ELSE
					context.error.String("Could not open file "); context.error.String(filename);
					context.error.Ln;
				END;
			ELSE
				context.error.String("Highlighter "); context.error.String(highlighterName);
				context.error.String(" not found."); context.error.Ln;
			END;
		ELSE
			context.error.String("Parameter error: {nofIterations > 0}!"); context.error.Ln;
		END;
	END;
END Bench;

END BenchSyntaxHighlighter.

SystemTools.Free BenchSyntaxHighlighter ~

BenchSyntaxHighlighter.Bench Usb.Mod ~