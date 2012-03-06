MODULE StreamMonitors; (** AUTHOR "Patrick Hunziker"; PURPOSE "monitoring data flow in a stream"; *)
(* daisychaining of readers or writers with 'logging side-stream' *)

IMPORT Streams (*, KernelLog, Commands*);
	
CONST 
	ReaderBufSize = Streams.DefaultReaderSize;
	WriterBufSize = Streams.DefaultWriterSize;

TYPE	WriterMonitor* = OBJECT
		VAR monitoredW, monitor : Streams.Writer;
			buf: ARRAY WriterBufSize OF CHAR;
			bufPos: LONGINT;
	
		PROCEDURE &Init*(VAR writer: Streams.Writer; monitoredW:Streams.Writer; monitor: Streams.Writer);
		BEGIN
			SELF.monitoredW := monitoredW;	
			SELF.monitor:=monitor;
			bufPos:=0;
			Streams.OpenWriter(writer, Sender);
		END Init;

		PROCEDURE Sender(CONST outBuf: ARRAY OF CHAR; ofs, len: LONGINT; propagate: BOOLEAN; VAR res: LONGINT);
		VAR i: LONGINT;
		BEGIN
			i := ofs;
			res:=monitoredW.res;
			WHILE i < ofs+len DO
				buf[bufPos] := outBuf[i];
				INC(i);
				INC(bufPos);
				IF bufPos = WriterBufSize THEN Write END;
				IF propagate THEN monitoredW.Update; IF monitor#NIL THEN monitor.Update END; END
			END;
		END Sender;
		
		PROCEDURE Write;
		BEGIN
			monitoredW.Bytes(buf, 0, bufPos);
			IF monitor#NIL THEN monitor.Bytes(buf, 0, bufPos) END;
			bufPos := 0
		END Write;
		
		PROCEDURE Update*;
		BEGIN
			Write;
			monitoredW.Update;
			monitor.Update;
		END Update;		
	
	END WriterMonitor;
	
	ReaderMonitor* = OBJECT
		VAR monitoredR: Streams.Reader;
			monitor: Streams.Writer;
	
		PROCEDURE &Init*(VAR reader: Streams.Reader; monitoredR: Streams.Reader; monitor: Streams.Writer);
		BEGIN
			SELF.monitoredR := monitoredR;	
			SELF.monitor:=monitor;
			Streams.OpenReader(reader, Receiver);
		END Init;

		PROCEDURE Receiver(VAR buf: ARRAY OF CHAR; ofs, size, min: LONGINT; VAR len, res: LONGINT);
		BEGIN
			ASSERT((size > 0) & (min <= size) & (min >= 0));
			monitoredR.Bytes(buf, ofs, size, len);
			res:=monitoredR.res;
			IF monitor#NIL THEN monitor.Bytes(buf, ofs, len); monitor.Update END;
		END Receiver;
	END ReaderMonitor;
(*
PROCEDURE Test*(context:Commands.Context);
VAR w, wr: Streams.Writer;
	r:Streams.Reader;
	rm: ReaderMonitor;
	wm: WriterMonitor;
	s: ARRAY 64 OF CHAR;
	res:BOOLEAN;
BEGIN
	Streams.OpenWriter(wr, KernelLog.Send);
	NEW(rm, r, context.arg, wr);
	res:=r.GetString(s); (*read input and send it to monitor stream*)
	
	NEW(wm, w, context.out, wr);(* monitor a writer and send written data also to monitor stream*)
	w.String("holla"); w.Ln; w.Update; 
	wm.Update;
END Test;
*)

END StreamMonitors.

StreamMonitors.Test hello ~
SystemTools.FreeDownTo StreamMonitors ~


