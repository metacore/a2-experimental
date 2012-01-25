MODULE FileTrapWriter; (** AUTHOR "fof"; PURPOSE "trap file writer"; *)

IMPORT
	Trace, Modules, Streams, TrapWriters, Files, Dates, Strings;

PROCEDURE GenerateName(VAR str: ARRAY OF CHAR; index: LONGINT);
VAR startTime: Dates.DateTime; num: ARRAY 32 OF CHAR;
BEGIN
	startTime := Dates.Now();
	Strings.FormatDateTime("_yyyymmdd__hhnnss",startTime,str);
	Strings.Concat("Trap",str,str);
	IF index # 0 THEN
		Strings.IntToStr(index,num);
		Strings.Append(str,"_");
		Strings.Concat(str,num,str);
	END;
	Strings.Concat(str,".txt",str);
END GenerateName;

PROCEDURE TrapWriterFactory*(): Streams.Writer;
VAR w: Files.Writer; file: Files.File; name: Files.FileName; index: LONGINT;
BEGIN
	index := 0;
	REPEAT
		GenerateName(name,index);
		INC(index);
	UNTIL (Files.Old(name) = NIL) OR (index > 99);
	file := Files.New(name);
	IF file # NIL THEN
		NEW(w,file,0);
		w.String("File "); w.String(name);  w.Ln;
		w.String("---------------------------");  w.Ln;
		Files.Register(file);
	ELSE
		Trace.String("Could not generate file for trap "); Trace.String(name); Trace.Ln;
		w := NIL
	END;
	RETURN w;
END TrapWriterFactory;

PROCEDURE Install*;
BEGIN
	TrapWriters.InstallTrapWriterFactory (TrapWriterFactory)
END Install;

PROCEDURE Uninstall*;
BEGIN
	TrapWriters.UninstallTrapWriterFactory (TrapWriterFactory)
END Uninstall;

PROCEDURE HaltTest*;
BEGIN
	HALT(100);
END HaltTest;

PROCEDURE Cleanup;
BEGIN
	Uninstall;
END Cleanup;

BEGIN
	Modules.InstallTermHandler(Cleanup);
END FileTrapWriter.

SystemTools.Free FileTrapWriter  ~

FileTrapWriter.Install
WMTrapWriter.Install
WMTrapWriter.Uninstall
TrapWriters.InstallLogWriter
TrapWriters.InstallTraceWriter
FileTrapWriter.Uninstall
FileTrapWriter.HaltTest
