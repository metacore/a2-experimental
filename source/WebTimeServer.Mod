MODULE WebTimeServer; (** AUTHOR "Patrick Hunziker"; PURPOSE "time server RFC 868"; *)

IMPORT Modules, TCP, TCPServices, Streams, Dates;

CONST
	TimePort* = 37;

TYPE
	TimeAgent = OBJECT (TCPServices.Agent)
		VAR 
			days,hours,minutes,seconds: LONGINT; 
			t: HUGEINT;
			w: Streams.Writer;

	BEGIN {ACTIVE}
		Streams.OpenWriter(w, client.Send);
		Dates.TimeDifference(Dates.ZeroDateRFC868, Dates.Now(), days,hours,minutes,seconds); (* does Dates consider the extra second added to world time in  http://www.timeanddate.com/time/leapseconds.html ?*)
		t:=((HUGEINT(days)*24+hours)*60+minutes)*60+seconds;
		INC(t,25); (*! the 25 leap seconds added to UTC since 1972 are added here. They should instead be done in Dates.Mod. see http://en.wikipedia.org/wiki/Leap_second *)
		w.Net32(LONGINT(t));
		w.Update;
		Terminate
	END TimeAgent;

VAR
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
	Modules.InstallTermHandler(Cleanup)
END WebTimeServer.

SystemTools.Free WebTimeServer ~
SystemTools.FreeDownTo TCP ~

WebTimeServer.Open
WebTimeServer.Close
