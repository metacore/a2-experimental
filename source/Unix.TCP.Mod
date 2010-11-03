(* Aos, Copyright 2001, Pieter Muller, ETH Zurich *)

MODULE TCP;   (** AUTHOR "pjm, mvt"; PURPOSE "TCP protocol"; *)


IMPORT Out := KernelLog, IP, Streams,  Glue, Unix, B := NetBase, Objects;

CONST
	NilPort* = 0;

	(** Error codes *)
	Ok* = 0;
	ConnectionRefused* = 3701;
	ConnectionReset* = 3702;
	WrongInterface* = 3703;
	TimedOut* = 3704;
	NotConnected* = 3705;
	NoInterface* = 3706;
	InterfaceClosed* = 3707;


	(** TCP connection states *)
	NumStates* = 4;
	Closed* = 0;
	Listen* = 1;
	Established* = 2;
	Unused* = 4;   (* no real state, only used in this implementation *)

	OpenStates* = {Listen, Established};
	ClosedStates* = {Unused, Closed};
	HalfClosedStates* = ClosedStates + {};
	FinStates* = {Unused, Closed};
		
VAR
	trace: BOOLEAN;

	hex: ARRAY 17 OF CHAR;


TYPE
	(** Connection object.
		NOTE: Only one process should access a Connection!  *)

	Connection* = OBJECT (Streams.Connection)
			VAR
				int-: IP.Interface;	(* Unix port: dummy, only 'int.localAdr' contains valid data *)
				
				lport-: LONGINT;
				fip-: IP.Adr;  (* foreign protocol address *)
				fport-: LONGINT;
				state*: SHORTINT;   (* TCP state *)

				socket: LONGINT;
				localAdr, foreignAdr: B.SocketAdr;
				
				(* Initialization for internal use only. *)

				PROCEDURE & Init;
				BEGIN
					state := Unused;
				END Init;
				


				(** Open a TCP connection (only use once per Connection instance).
					Use TCP.NilPort for lport to automatically assign an unused local port.*)
				PROCEDURE Open*( lport: LONGINT;  fip: IP.Adr;  fport: LONGINT;  VAR res: LONGINT );
				BEGIN {EXCLUSIVE}
					ASSERT( (state = Unused) & (lport >= 0) & (lport < 10000H) & (fport >= 0) & (fport < 10000H) );
					IF trace THEN  Out.String( "Open connection " )  END;
					socket := B.Socket( Unix.AFINET, Unix.SockStream, Unix.IpProtoTCP );
					IF socket # 0 THEN
						IF (~IP.IsNilAdr( fip )) & (fport # NilPort) THEN
							IF trace THEN  Out.String( "(inout) " )  END;
							(* active open (connect) *)
							foreignAdr := B.NewSocketAdr( fip, fport );
							IF B.Connect( socket, foreignAdr ) THEN
								IF B.SetLinger( socket ) THEN  END;
								SELF.fip := fip;  SELF.fport := fport;
								localAdr := B.GetSockName( socket );
								SELF.lport := B.PortNumberOf( localAdr );
								state := Established;  res := Ok
							ELSE  
								Out.String( "connect failed" ); Out.Ln;
								B.Close( socket );  res := ConnectionRefused
							END
						ELSE
							IF trace THEN  Out.String( "(listen) " )  END;
							(* passive open (listen) *)
							ASSERT( (fport = NilPort) & (IP.IsNilAdr( fip )) );
							localAdr := B.NewSocketAdr( IP.NilAdr, lport );
							IF B.Bind( socket, localAdr ) THEN
								localAdr := B.GetSockName( socket );
								SELF.lport := B.PortNumberOf( localAdr );
								IF B.Listen( socket ) THEN
									IF B.SetLinger( socket ) THEN  END;
									SELF.fip := IP.NilAdr;
									state := Listen;  res := Ok
								ELSE  B.Close( socket );  res := NotConnected
								END
							ELSE  B.Close( socket );  res := NotConnected
							END
						END
					ELSE  
						Out.String( "open socket failed" );  Out.Ln;
						res := NotConnected
					END;
					IF res = Ok THEN
						(* create a dummy interface with correct local IP-adr *)
						NEW( int, B.SockAdrToIPAdr( localAdr ) )
					END;
					IF trace THEN
						IF res = Ok THEN
							Out.String( "socket=" );  Out.Int( socket, 0 );
							Out.String( ", locport=" );  Out.Int( SELF.lport, 0 );
							Out.String( " done." )
						ELSE  
							Out.String( " failed." )
						END;
						Out.Ln
					END;
				END Open;


				(** Send data on a TCP connection. *)
				PROCEDURE Send*( CONST data: ARRAY OF CHAR;  ofs, len: LONGINT;  propagate: BOOLEAN;  VAR res: LONGINT );
				VAR n: LONGINT;
				BEGIN (*{EXCLUSIVE}*)
					IF trace THEN  Out.String( "Send: socket=" );  Out.Int( socket, 0 );  ShowBuffer( data, ofs, len )  END;
					IF state = Established THEN
						WHILE len > 0 DO
							n := len;
							IF B.Send( socket, data, ofs, n ) THEN  
								res := Ok;  DEC( len, n );  INC( ofs, n )
							ELSE  
								res := ConnectionReset;  len := 0
							END
						END
					ELSE
						res := NotConnected (* Send on a Connection with state=Listen *)
					END;
					res := Ok;
				END Send;

				(** Receive data on a TCP connection. The data parameter specifies the buffer.
					The ofs parameters specify the position in the buffer where data should be received (usually 0),
					and the size parameters specifies how many bytes of data can be received in the buffer.
					The min parameter specifies the minimum number of bytes to receive before Receive returns
					and must by <= size. The len parameter returns the number of bytes received, and the
					res parameter returns 0 if ok, or a non-zero error code otherwise (e.g. if the connection is closed
					by the communication partner, or by a call of the Close method). *)
				
				PROCEDURE Receive*( VAR data: ARRAY OF CHAR;  ofs, size, min: LONGINT;  VAR len, res: LONGINT );
				VAR p, x: LONGINT;
				BEGIN (*{EXCLUSIVE}*)
					ASSERT( (ofs >= 0) & (ofs + size <= LEN( data )) & (min <= size) );   (* parameter consistency check *)
					IF trace THEN
						Out.String( "Receive: socket=" );  Out.Int( socket, 0 );
						Out.String( " min=" );  Out.Int( min, 0 );
						p := ofs
					END;
					len := 0;  res := Ok;
					IF size = 0 THEN  RETURN  END;
					IF state IN {Listen, Established} THEN
						LOOP
							x := size;
							IF B.Recv( socket, data, ofs, x, 0 ) THEN
								IF x > 0 THEN
									DEC( size, x );  INC( len, x );  INC( ofs, x );
									IF len >= min THEN  
										IF trace THEN  ShowBuffer( data, p, len )  END;
										RETURN  
									END
								ELSE
									(* x = 0: closed by peer *)
									B.Close( socket );  state := Closed;
									res := NotConnected;  RETURN
								END
							ELSE
								B.Close( socket );  state := Closed;
								res := NotConnected;  RETURN
							END
						END; (* loop *)
					ELSE  
						res := NotConnected
					END;
				END Receive;
			
				
				
				(** Enable or disable delayed send (Nagle algorithm).
					If enabled, the sending of a segment is delayed if it is not filled by one call to Send, in order to be able
					to be filled by further calls to Send. This is the default option.
					If disabled, a segment is sent immediatly after a call to Send, even if it is not filled.
					This option is normally chosen by applications like telnet or VNC client, which send verly little data but
					shall not be delayed.*)
				PROCEDURE DelaySend*( enable: BOOLEAN );
					(* dummy *)
				END DelaySend;

				(** Enable or disable keep-alive. (default: disabled) *)
				PROCEDURE KeepAlive*( enable: BOOLEAN );
				VAR dum: BOOLEAN;
				BEGIN
					dum := B.KeepAlive( socket, enable )
				END KeepAlive;


				(** Return number of bytes that may be read without blocking. *)
				PROCEDURE Available*( ): LONGINT;
				VAR available: LONGINT; 
				BEGIN {EXCLUSIVE}
					IF state IN {Established, Listen} THEN
						IF B.Requested( socket ) THEN 
							available := B.Available( socket ); 
							IF available >= 0 THEN  
								RETURN available  
							END;
						END	
					END;
					RETURN  0
				END Available;

				(** Return connection state. *)
				PROCEDURE State*( ): LONGINT;
				BEGIN
					RETURN state
				END State;

				(** Wait until the connection state is either in the good or bad set, up to "ms" milliseconds. *)
				PROCEDURE AwaitState*( good, bad: SET;  ms: LONGINT;  VAR res: LONGINT );
				BEGIN
					WHILE (ms > 0) & ~(state IN (good+bad)) DO  Objects.Sleep( 10 );  DEC( ms, 10 )  END
				END AwaitState;

				(** Close a TCP connection (half-close). *)
				PROCEDURE Close*;
				BEGIN {EXCLUSIVE}
					B.Close( socket );  state := Closed;
				END Close;

				(** Discard a TCP connection (shutdown). *)
				PROCEDURE Discard*;
				BEGIN {EXCLUSIVE}
					B.Close( socket );  state := Closed;
				END Discard;

				(** Accept a client waiting on a listening connection. Blocks until a client is available or the
					  connection is closed. *)
				PROCEDURE Accept*( VAR client: Connection;  VAR res: LONGINT );
				VAR newsocket: LONGINT;  peerAdr: B.SocketAdr;
				BEGIN {EXCLUSIVE}
					IF trace THEN
						Out.String( "Accept: socket=" ); Out.Int( socket, 0 );  Out.String( " ... " )
					END;
					IF state = Listen THEN
						newsocket := B.Accept( socket );
						IF newsocket > 0 THEN
							peerAdr := B.GetPeerName( newsocket );
							NEW( client );
							client.int := int;
							client.socket := newsocket;
							client.state := Established;
							client.fip := B.SockAdrToIPAdr( peerAdr );
							client.fport := B.PortNumberOf( peerAdr );
							IF trace THEN
								Out.String( "Accept done, client socket=" );  Out.Int( newsocket, 0 );  Out.Ln
							END;
							res := Ok
						ELSE
							res := NotConnected ;
							IF trace THEN  Out.String( "Accept failed." );  Out.Ln  END
						END;
					ELSE
						res := NotConnected ;
						IF trace THEN  Out.String( "Accept failed (state # Listen)." );  Out.Ln  END
					END;
				END Accept;

				(** Return TRUE iff a listening connection has clients waiting to be accepted. *)
				PROCEDURE Requested*( ): BOOLEAN;
				BEGIN {EXCLUSIVE}
					RETURN (state = Listen) & B.Requested( socket ) 
				END Requested;


			END Connection;




	PROCEDURE ShowBuffer( CONST buf: ARRAY OF CHAR;  p, l: LONGINT );
	VAR i, pe: LONGINT;  c: CHAR;  x: LONGINT;
	BEGIN
		Out.Ln;  Out.Char( '[' );
		pe := p + l - 1;  i := 0;
		WHILE (p < LEN( buf )) & (p <= pe) DO
			c := buf[p];  INC( p );
			IF (c >= ' ') & (c <= '~') THEN  Out.Char( c )
			ELSE
				x := ORD( c );
				CASE x OF
				|10:  Out.String( "\n" )
				|11:  Out.String( "\t" )
				|13:  Out.String( "\c" )
				ELSE
					Out.Char( '\' );  Out.Char( hex[x DIV 16] );  Out.Char( hex[x MOD 16] );
				END
			END;
			INC( i );
			IF (p < pe) & ((i >= 80) OR (c = 0AX)) THEN  Out.Ln;  i := 0  END
		END;
		Out.Char( ']' );  Out.Ln
	END ShowBuffer;


	(** Aos command - display all errors *)
	PROCEDURE DisplayErrors*( par: ANY ): ANY;
	BEGIN
		RETURN NIL;
	END DisplayErrors;


	(** Aos command - discard and finalize all connections *)
	PROCEDURE DiscardAll*( par: ANY ): ANY;
	BEGIN
		RETURN NIL;
	END DiscardAll;


	(** Temporary trace procedure. *)
	PROCEDURE ToggleTrace*;
	BEGIN
		trace := ~trace;
		Out.Enter;
		Out.String( "TCP trace " );
		IF trace THEN  Out.String( "on" )  ELSE  Out.String( "off" )  END;
		Out.Exit
	END ToggleTrace;


BEGIN
	hex := "0123456789ABCDEF";
	trace := 7 IN Glue.debug;
END TCP.

