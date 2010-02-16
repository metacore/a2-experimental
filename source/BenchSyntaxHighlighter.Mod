MODULE BenchSyntaxHighlighter; (** AUTHOR "staubesv"; PURPOSE "Benchmarks for SyntaxHighlighter"; *)

IMPORT
	Streams, Commands, Options, Dates, Strings, Files, Random, Texts, TextUtilities, SyntaxHighlighter;

CONST
	DefaultHighlighterName = "Oberon";
	DefaultNofIterations = 1000;

PROCEDURE Reader(reader : Texts.TextReader; nofIterations : LONGINT; out : Streams.Writer);
VAR char32 : Texts.Char32; startTime, endTime : Dates.DateTime; i : LONGINT;
BEGIN
	ASSERT((reader # NIL) & (nofIterations > 0) & (out # NIL));
	out.String("Reading text "); out.Int(nofIterations, 0); out.String(" times ... "); out.Update;
	startTime := Dates.Now();
	FOR i := 1 TO nofIterations DO
		reader.SetPosition(0);
		REPEAT
			reader.ReadCh(char32);
		UNTIL reader.eot;
	END;
	endTime := Dates.Now();
	Strings.ShowTimeDifference(startTime, endTime, out); out.Ln;
END Reader;

PROCEDURE Words(reader : Texts.TextReader; highlighter : SyntaxHighlighter.Highlighter; nofIterations : LONGINT; out : Streams.Writer);
VAR
	char32 : Texts.Char32; attributes : Texts.Attributes;
	wordEnd, readerPosition, i : LONGINT;
	startTime, endTime : Dates.DateTime;
BEGIN
	ASSERT((reader # NIL) & (highlighter # NIL) & (nofIterations > 0) & (out # NIL));
	out.String("Match words "); out.Int(nofIterations, 0); out.String(" times ... "); out.Update;
	startTime := Dates.Now();
	FOR i := 1 TO nofIterations DO
		wordEnd := -1;
		reader.SetPosition(0);
		REPEAT
			readerPosition := reader.GetPosition();
			reader.ReadCh(char32);
			IF (readerPosition > wordEnd) & highlighter.IsAllowedCharacter(char32) THEN
				attributes := highlighter.GetWordAttributes(reader, readerPosition, wordEnd);
				reader.SetPosition(readerPosition);
				reader.ReadCh(char32);
			END;
		UNTIL reader.eot;
	END;
	endTime := Dates.Now();
	Strings.ShowTimeDifference(startTime, endTime, out); out.Ln;
END Words;

PROCEDURE RebuildRegions(reader : Texts.TextReader; highlighter : SyntaxHighlighter.Highlighter; nofIterations : LONGINT; out : Streams.Writer);
VAR
	state : SyntaxHighlighter.State;
	startTime, endTime : Dates.DateTime;
	i : LONGINT;
BEGIN
	ASSERT((reader # NIL) & (highlighter # NIL) & (nofIterations > 0) & (out # NIL));
	NEW(state);
	out.String("Rebuild regions "); out.Int(nofIterations, 0); out.String(" times ... "); out.Update;
	startTime := Dates.Now();
	FOR i := 1 TO nofIterations DO
		highlighter.RebuildRegions(reader, state);
	END;
	endTime := Dates.Now();
	Strings.ShowTimeDifference(startTime, endTime, out); out.Ln;
END RebuildRegions;

PROCEDURE RegionLookup(reader : Texts.TextReader; highlighter : SyntaxHighlighter.Highlighter; nofIterations : LONGINT; out : Streams.Writer);
VAR
	attributes : Texts.Attributes;
	state : SyntaxHighlighter.State;
	random : Random.Generator;
	length, position, start, end, i : LONGINT;
	startTime, endTime : Dates.DateTime;
BEGIN
	ASSERT((reader # NIL) & (highlighter # NIL) & (nofIterations > 0) & (out # NIL));
	NEW(state);
	NEW(random);
	length := reader.text.GetLength();
	highlighter.RebuildRegions(reader, state);
	out.String("Region lookup"); out.Int(nofIterations, 0); out.String(" times ... "); out.Update;
	startTime := Dates.Now();
	FOR i := 1 TO nofIterations DO
		position := random.Dice(length);
		attributes := highlighter.GetRegionAttributes(position, state, start, end);
	END;
	endTime := Dates.Now();
	Strings.ShowTimeDifference(startTime, endTime, out); out.Ln;
END RegionLookup;

PROCEDURE Full(reader : Texts.TextReader; highlighter : SyntaxHighlighter.Highlighter; nofIterations : LONGINT; out : Streams.Writer);
VAR
	char32 : Texts.Char32; attributes : Texts.Attributes;
	state : SyntaxHighlighter.State;
	startTime, endTime : Dates.DateTime;
	readerPosition, regionStart, regionEnd, lastEnd, i : LONGINT;
BEGIN
	ASSERT((reader # NIL) & (highlighter # NIL) & (nofIterations > 0) & (out # NIL));
	NEW(state);
	out.String("Full highlighting "); out.Int(nofIterations, 0); out.String(" times ... "); out.Update;
	startTime := Dates.Now();
	FOR i := 1 TO nofIterations DO
		reader.SetPosition(0);
		lastEnd := -1;
		REPEAT
			readerPosition := reader.GetPosition();
			reader.ReadCh(char32);
			IF (lastEnd < readerPosition) THEN
				attributes := NIL;
				attributes := highlighter.GetRegionAttributes(readerPosition, state, regionStart, regionEnd);
				IF (attributes # NIL) THEN
					lastEnd := regionEnd;
				ELSE
					IF highlighter.IsAllowedCharacter(char32) THEN
						attributes := highlighter.GetWordAttributes(reader, readerPosition, lastEnd);
						reader.SetPosition(readerPosition);
						reader.ReadCh(char32);
					END;
				END;
			END;
		UNTIL reader.eot;
	END;
	endTime := Dates.Now();
	Strings.ShowTimeDifference(startTime, endTime, out); out.Ln;
END Full;

PROCEDURE Indent(writer : Streams.Writer; width : LONGINT);
VAR i : LONGINT;
BEGIN
	FOR i := 1 TO width DO writer.Char(" "); END;
END Indent;

PROCEDURE Bench*(context : Commands.Context); (** [Options] filename [benchmark] ~ *)
VAR
	filename : Files.FileName; highlighterName, benchmark : ARRAY 64 OF CHAR; nofIterations : LONGINT;
	options : Options.Options;
	text : Texts.Text; reader : Texts.TextReader;
	format, res : LONGINT;
	highlighter : SyntaxHighlighter.Highlighter;
BEGIN
	NEW(options);
	options.Add("h", "highlighter"	, Options.String);
	options.Add("n", "nofIterations", Options.Integer);
	IF options.Parse(context.arg, context.error) THEN
		benchmark := "";
		context.arg.GetString(filename);
		context.arg.GetString(benchmark);
		IF ~options.GetString("highlighter", highlighterName) THEN highlighterName := DefaultHighlighterName; END;
		IF ~options.GetInteger("nofIterations", nofIterations) THEN nofIterations := DefaultNofIterations; END;
		IF (nofIterations > 0) THEN
			highlighter := SyntaxHighlighter.GetHighlighter(highlighterName);
			IF (highlighter # NIL) THEN
				NEW(text);
				TextUtilities.LoadAuto(text, filename, format, res);
				IF (res = 0) THEN
					context.out.String(filename); context.out.String(": ");
					NEW(reader, text);
					text.AcquireRead;
					IF (benchmark = "") THEN
						context.out.Ln;
						Indent(context.out, 4); Reader(reader, nofIterations, context.out); context.out.Update;
						Indent(context.out, 4); Words(reader, highlighter, nofIterations, context.out); context.out.Update;
						Indent(context.out, 4); RebuildRegions(reader, highlighter, nofIterations, context.out); context.out.Update;
						Indent(context.out, 4); RegionLookup(reader, highlighter, nofIterations, context.out); context.out.Update;
						Indent(context.out, 4); Full(reader, highlighter, nofIterations, context.out); context.out.Update;
					ELSIF (benchmark = "reader") THEN
						Reader(reader, nofIterations, context.out);
					ELSIF (benchmark = "words") THEN
						Words(reader, highlighter, nofIterations, context.out);
					ELSIF (benchmark = "rebuildregions") THEN
						RebuildRegions(reader, highlighter, nofIterations, context.out);
					ELSIF (benchmark = "regionlookup") THEN
						RegionLookup(reader, highlighter, nofIterations, context.out);
					ELSIF (benchmark = "full") THEN
						Full(reader, highlighter, nofIterations, context.out);
					ELSE
						context.error.String("Unknown benchmark: "); context.error.String(benchmark); context.error.Ln;
					END;
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

BenchSyntaxHighlighter.Bench Usb.Mod reader ~
BenchSyntaxHighlighter.Bench I386.Machine.Mod reader ~

BenchSyntaxHighlighter.Bench Usb.Mod words ~
BenchSyntaxHighlighter.Bench I386.Machine.Mod words ~

BenchSyntaxHighlighter.Bench Usb.Mod rebuildregions~
BenchSyntaxHighlighter.Bench I386.Machine.Mod rebuildregions ~

BenchSyntaxHighlighter.Bench -n=1000000 Usb.Mod regionlookup~
BenchSyntaxHighlighter.Bench I386.Machine.Mod regionlookup ~

BenchSyntaxHighlighter.Bench Usb.Mod full ~
BenchSyntaxHighlighter.Bench I386.Machine.Mod full ~

BenchSyntaxHighlighter.Bench Usb.Mod  ~
BenchSyntaxHighlighter.Bench I386.Machine.Mod  ~

Test:

SystemTools.DoCommands
	FSTools.Enumerate *.Mod BenchSyntaxHighlighter.Bench -n=1 <#filename#> ~
	FSTools.Enumerate *.XML BenchSyntaxHighlighter.Bench -n=1 <#filename#> ~
	FSTools.Enumerate *.TOOL BenchSyntaxHighlighter.Bench -n=1 <#filename#> ~
	FSTools.Enumerate *.C BenchSyntaxHighlighter.Bench -n=1 <#filename#> ~
~

