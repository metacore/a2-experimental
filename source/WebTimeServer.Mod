MODULE WebTimeServer; (** AUTHOR "Patrick Hunziker"; PURPOSE "time server RFC 868"; *)

IMPORT Modules, TCP, TCPServices, Streams, Dates;

CONST
	TimePort* = 37;

TYPE
	TimeAgent = OBJECT (TCPServices.Agent)
		VAR 
			days,hours,minutes,seconds: LONGINT; 
			time:HUGEINT;
			w: Streams.Writer;

	BEGIN {ACTIVE}
		Streams.OpenWriter(w, client.Send);
		Dates.TimeDifference(time1900, Dates.Now(), days,hours,minutes,seconds);
		time:=((HUGEINT(days)*24+hours)*60+minutes)*60+seconds;
		w.Net32(LONGINT(time));
		w.Update;
		Terminate
	END TimeAgent;

VAR
	time1900: Dates.DateTime;
	time: TCPServices.Service;

PROCEDURE Open*;
VAR res : LONGINT;
BEGIN
	NEW(time, TimePort, NewTimeAgent, res);
END Open;

PROCEDURE Close*;
BEGIN
	IF time#NIL THEN time.Stop; time := NIL END;
END Close;

PROCEDURE NewTimeAgent(c: TCP.Connection; s: TCPServices.Service): TCPServices.Agent;
VAR a: TimeAgent;
BEGIN
	NEW(a, c, s); RETURN a
END NewTimeAgent;

PROCEDURE Cleanup;
BEGIN
	Close;
END Cleanup;

BEGIN
	time1900.year:=1900; time1900.month:=1; time1900.day:=1;
	Modules.InstallTermHandler(Cleanup)
END WebTimeServer.

SystemTools.Free WebTimeServer ~

WebTimeServer.Open
WebTimeServer.Close
