MODULE WebNetworkTimeProtocol; (** AUTHOR "Patrick Hunziker"; PURPOSE "SimpleNetworkTimeProtocol RFC4330 and NetworkTimeProtocol RFC5905 "; *)

(**
NTP operates over the User Datagram Protocol (UDP). An NTP server listens for client NTP packets on port 123. 
The NTP server is stateless and responds to each received client NTP packet in a simple transactional manner 
by adding fields to the received packet and passing the packet back to the original sender, without reference to preceding NTP transactions.

Upon receipt of a client NTP packet, the receiver time-stamps receipt of the packet as soon as possible within the packet assembly logic of the server. 
The packet is then passed to the NTP server process. 
This process interchanges the IP Header Address and Port fields in the packet, overwrites numerous fields in the NTP packet with local clock values, 
time-stamps the egress of the packet, recalculates the checksum, and sends the packet back to the client.

Time is given as 64-bit time-stamp value. 
This value is an unsigned 32-bit seconds value, and a 32-bit fractional part. 
The unit of time is in seconds, and the epoch is 1 January 1900, meaning that the NTP time will cycle in the year 2036 (two years before the 32-bit Unix time cycle event in 2038).

for best NTP server pools for a given region see wikipedia: NTP-Pool


Implementation currently limited to the simple network time protocol
ToDo: full NTP synchronization algorithm.
*)

IMPORT IP,UDP, Streams, Commands, Configuration, DNS, Machine;

CONST NTPPort*=123;

TYPE Packet=RECORD
	Header*:SHORTINT; (* LeapIndicator: 2 MSB bits; Version: 3 bits; mode: 3 LSB bits *)
	Stratum*: SHORTINT;
	Poll*:SHORTINT;
	Precision*:SHORTINT;
	RootDelay*:LONGINT;
	RootDispersion*:LONGINT;
	ReferenceIdentifier*:LONGINT;
	ReferenceTimestamp*:HUGEINT;
	OriginTimestamp*:HUGEINT;
	ReceiveTimestamp*:HUGEINT;
	TransmitTimestamp*:HUGEINT;
	Extensions: ANY;
END;



(** get a single time record from an NTP time server. *)
PROCEDURE Get*(fip:IP.Adr; fport:LONGINT; VAR p:Packet);
VAR socket: UDP.Socket; len, res, high, low:LONGINT;
	buf: ARRAY 1024 OF CHAR;
	sw:Streams.StringWriter;
	sr: Streams.StringReader;
	packet:Packet;
	fip1:IP.Adr; fport1:LONGINT;
BEGIN
	NEW(socket, UDP.NilPort, res);
	IF res=UDP.Ok THEN
		NEW(sw, 1024);
		sw.Net8(0*64 + 3*8 +3); (*leap indicator currently not set; packet version=3; packet.Header = client; *)
		sw.Net8(packet.Stratum);
		sw.Net8(packet.Poll);
		sw.Net8(packet.Precision);
		sw.Net32(packet.RootDelay);
		sw.Net32(packet.RootDispersion);
		sw.Net32(packet.ReferenceIdentifier);
		sw.Net32(LONGINT(packet.ReferenceTimestamp DIV 100000000H)); sw.Net32(LONGINT(packet.ReferenceTimestamp MOD 100000000H));
		sw.Net32(LONGINT(packet.OriginTimestamp DIV 100000000H));           sw.Net32(LONGINT(packet.OriginTimestamp MOD 100000000H));
		sw.Net32(LONGINT(packet.ReceiveTimestamp DIV 100000000H));        sw.Net32(LONGINT(packet.ReceiveTimestamp MOD 100000000H));
		sw.Net32(LONGINT(packet.TransmitTimestamp DIV 100000000H));    sw.Net32(LONGINT(packet.TransmitTimestamp MOD 100000000H));
		sw.Update;
		sw.GetRaw(buf, len);
		socket.Send( fip, fport, buf, 0, 48, res );  
		
		socket.Receive(buf,0,48, 1000, fip1, fport1, len, res);
		IF (res=UDP.Ok)&(len>=48) THEN
			NEW(sr,1024);
			sr.SetRaw(buf,0,len);
			p.Header:=SHORT(SHORT(sr.Net8()));
			p.Stratum:=SHORT(SHORT(sr.Net8()));
			p.Poll:=SHORT(SHORT(sr.Net8()));
			p.Precision:=SHORT(SHORT(sr.Net8()));
			p.RootDelay:=sr.Net32();
			p.RootDispersion:=sr.Net32();
			p.ReferenceIdentifier:=sr.Net32();
			high:=sr.Net32(); low:=sr.Net32(); p.ReferenceTimestamp := 100000000H*high + low MOD 100000000H;
			high:=sr.Net32(); low:=sr.Net32(); p.OriginTimestamp := 100000000H*high + low MOD 100000000H;
			high:=sr.Net32(); low:=sr.Net32(); p.ReceiveTimestamp := 100000000H*high + low MOD 100000000H;
			high:=sr.Net32(); low:=sr.Net32(); p.TransmitTimestamp := 100000000H*high + low MOD 100000000H;
		END;
	END;
END Get;

(* to be done: full NTP synchronization algorithm from RFC5905 to set machine clock *)
PROCEDURE SynchronizeNTP;
END SynchronizeNTP;

(* to be done: simple NTP synchronization algo from RFC 4330 *)
PROCEDURE SynchronizeSNTP;
(*
 The roundtrip delay d and system clock offset t are defined as:
      d = (T4 - T1) - (T3 - T2)     t = ((T2 - T1) + (T3 - T4)) / 2.

This can be used to set the system clock, if a high accuracy clock is settable on this hardware/OS
*)
END SynchronizeSNTP;


PROCEDURE GetSimpleTime*(context:Commands.Context);
VAR ipstr: ARRAY 64 OF CHAR; port, res:LONGINT;machineTimer1,machineTimer2: HUGEINT; fip: IP.Adr; packet:Packet;
BEGIN 
	
	IF ~context.arg.GetString(ipstr) THEN	Configuration.Get("NTP.Server0",ipstr,res); END;
	(* note that DNS.HostByName might also deliver a default NTP server when an empty string and an NTP port number is given*)
	DNS.HostByName(ipstr, fip, port);
	IF ~context.arg.GetInteger(port,FALSE) THEN port:=NTPPort END;
	context.out.String("checking server "); context.out.String(ipstr);context.out.Char(":"); context.out.Int(port,0);  context.out.Ln; context.out.Update;
	
	machineTimer1:=Machine.GetTimer();
	Get(fip, port, packet);
	machineTimer2:=Machine.GetTimer();
	
	(* reference time *)
	context.out.String("SNTP transmit time [seconds, fraction]: "); 
	context.out.Int(packet.TransmitTimestamp DIV 100000000H MOD 100000000H,0); context.out.Char(".");
	context.out.Int(packet.TransmitTimestamp MOD 100000000H,0); context.out.Ln;
	
	(* local machine cycle count since reset *)
	context.out.String("local machine counter: "); 
	context.out.Int(machineTimer1 ,0); context.out.Ln;
	context.out.Int(machineTimer2 ,0); context.out.Ln;
END GetSimpleTime;


END WebNetworkTimeProtocol.

(*each county/region has its own ntp server pools: *)

WebNetworkTimeProtocol.GetSimpleTime 0.ch.pool.ntp.org~
WebNetworkTimeProtocol.GetSimpleTime 1.ch.pool.ntp.org 124~
WebNetworkTimeProtocol.GetSimpleTime 2.ch.pool.ntp.org~
WebNetworkTimeProtocol.GetSimpleTime 3.ch.pool.ntp.org~
WebNetworkTimeProtocol.GetSimpleTime~

SystemTools.Free WebNetworkTimeProtocol~