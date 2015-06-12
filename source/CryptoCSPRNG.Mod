MODULE CryptoCSPRNG;	(** AUTHOR "GF"; PURPOSE "Cryptographically Secure Pseudo-Random Generator."*)
 
 
IMPORT  Machine, Clock, Heaps, SHA3 := CryptoSHA3 (*, Out := KernelLog*);


	PROCEDURE CSRand*( VAR rand: ARRAY OF CHAR; bits: LONGINT );
	VAR 
		seed: HUGEINT; i: LONGINT;
		h: SHA3.Hash;
		buf: ARRAY 64 OF CHAR;
	BEGIN
		ASSERT( (bits MOD 8 = 0) & (bits DIV 8 <= LEN( rand )) & (bits <= 512) );
		seed := Noise();
		NEW( h );  h.SetNameAndSize( "", 64 );
		FOR i := 0 TO 7 DO  
			buf[i] := CHR( seed MOD 100H );  seed := seed DIV 100H  
		END;
		h.Update( buf, 0, 8 );
		h.GetHash( buf, 0 );
		FOR i := 0 TO (bits DIV 8) - 1 DO  rand[i] := buf[i]  END
	END CSRand;
	
	PROCEDURE Noise( ): HUGEINT;
	VAR tm, dt: HUGEINT; t, d: LONGINT;  total, free, largest: SIZE;
	BEGIN
		tm := Machine.GetTimer( );
		Clock.Get( t, d );  
		dt := LONG( d ) * 1000000H + t;
		Heaps.GetHeapInfo( total, free, largest ); 
		RETURN  (tm + 4*dt + Heaps.Nmark) * Heaps.Ngc + (total - free + largest )
	END Noise;
	
	(*
	PROCEDURE Test*;
	CONST HT = 09X;
	VAR rand: ARRAY 64 OF CHAR; i: LONGINT;
	BEGIN
		CSRand( rand, 512 );
		Out.Ln;
		FOR i := 0 TO 63 DO
			Out.Hex( ORD( rand[i] ), -2 );
			IF (i+1) MOD 4 = 0 THEN  Out.Char( HT )  END;
			IF (i+1) MOD 24 = 0 THEN  Out.Ln  END
		END;
		Out.Ln
	END Test;
	*)

END CryptoCSPRNG.


	CryptoCSPRNG.Test ~
	
	SystemTools.Free CryptoCSPRNG ~