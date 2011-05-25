(* Aos, Copyright 2001, Pieter Muller, ETH Zurich *)

MODULE UnixFiles;   (** AUTHOR "gf"; PURPOSE "Unix file systems" *)

IMPORT S := SYSTEM, UTF8Strings, FileDir IN Oberon, OFiles := Files IN Oberon, Files;

CONST
	ErrFileReadOnly* = 2921;  ErrParentNotFound* = 2922;  ErrInvalidFilename* = 2923;
	ErrTooManySimilarFiles* = 2924;  ErrRootDirFull* = 2925;  ErrFileNotFound* = 2926;  ErrFileExists* = 2927;
	ErrHasOpenFiles* = 2928;  ErrNoRelativePaths* = 2929;  ErrDirectoryProtection* = 2930;
	ErrDirectoryNotEmpty* = 2931;  ErrNotADirectory* = 2932;  ErrDirectoryOpen* = 2933;

	MaxFilenameLen* = 256;

	faReadOnly* = 0;  faHidden* = 1;  faSystem* = 2;  faVolumeID* = 3;  faDirectory* = 4;  faArchive* = 5;

TYPE
	Filename* = ARRAY MaxFilenameLen OF CHAR;

	FileSystem* = OBJECT (Files.FileSystem)

				PROCEDURE & Init;
				BEGIN
					prefix := "";  vol := NIL;  desc := "Unix"
				END Init;


				PROCEDURE New0*( name: ARRAY OF CHAR ): Files.File;
				VAR f: File;
				BEGIN {EXCLUSIVE}
					f := NIL;
					IF UTF8Strings.Valid( name ) THEN
						NEW( f, SELF );
						f.unixfile := OFiles.New( name );  f.key := S.VAL( LONGINT, f.unixfile );  f.fs := SELF
					END;
					RETURN f
				END New0;


				PROCEDURE Old0*( name: ARRAY OF CHAR ): Files.File;
				VAR f: File;  u: OFiles.File;
				BEGIN  {EXCLUSIVE}
					f := NIL;
					IF UTF8Strings.Valid( name ) THEN
						u := OFiles.Old( name );
						IF u # NIL THEN
							NEW( f, SELF );
							f.unixfile := u;  f.key := S.VAL( LONGINT, u );  f.fs := SELF
						END;
					END;
					RETURN f
				END Old0;

				PROCEDURE FileKey*( name: ARRAY OF CHAR ): LONGINT;
				BEGIN
					RETURN 0
				END FileKey;

				PROCEDURE Delete0*( name: ARRAY OF CHAR;  VAR key, res: LONGINT );
				VAR ures: INTEGER;
				BEGIN  {EXCLUSIVE}
					res := ErrInvalidFilename;  key := 0;
					IF UTF8Strings.Valid( name ) THEN  OFiles.Delete( name, ures );  res := ures  END
				END Delete0;


				PROCEDURE Rename0*( old, new: ARRAY OF CHAR;  f: Files.File;  VAR res: LONGINT );
				VAR ures: INTEGER;
				BEGIN {EXCLUSIVE}
					res := ErrInvalidFilename;
					IF UTF8Strings.Valid( old ) & UTF8Strings.Valid( new ) THEN
						OFiles.Rename( old, new, ures );  res := ures
					END
				END Rename0;

				PROCEDURE CreateDirectory0*( path: ARRAY OF CHAR;  VAR res: LONGINT );
				VAR done: BOOLEAN;
				BEGIN {EXCLUSIVE}
					res := Files.Ok;  FileDir.CreateDirectory( path, done );
					IF ~done THEN  res := ErrFileExists  END;
				END CreateDirectory0;

				PROCEDURE RemoveDirectory0*( path: ARRAY OF CHAR;  force: BOOLEAN;  VAR key, res: LONGINT );
				VAR done: BOOLEAN;
				BEGIN {EXCLUSIVE}
					res := Files.Ok;
					FileDir.DeleteDirectory( path, done );
					IF ~done THEN  res := ErrNotADirectory  END;
				END RemoveDirectory0;


				PROCEDURE Enumerate0*( mask: ARRAY OF CHAR;  flags: SET;  enum: Files.Enumerator );
				VAR path, filemask: ARRAY 256 OF CHAR;
				BEGIN {EXCLUSIVE}
					IF UTF8Strings.Valid( mask ) THEN
						Files.SplitPath( mask, path, filemask );
						currEnumerator := enum;
						FileDir.Enumerate( filemask, TRUE , EntryHandler );
					END
				END Enumerate0;

			END FileSystem;

TYPE
	File* = OBJECT (Files.File)
			VAR
				unixfile: OFiles.File;
				long-: Filename;   (** file name *)
				attr: SET;

				PROCEDURE & Init( fs: Files.FileSystem );
				BEGIN
					SELF.fs := fs;  attr := {}
				END Init;

				PROCEDURE Set*( VAR r: Files.Rider;  pos: LONGINT );
				BEGIN  {EXCLUSIVE}
					OFiles.Set( r, unixfile, pos ) ;
					r.file := SELF;  r.fs := r.file.fs
				END Set;

				PROCEDURE Pos*( VAR r: Files.Rider ): LONGINT;
				BEGIN
					RETURN OFiles.Pos( r )
				END Pos;

				PROCEDURE Read*( VAR r: Files.Rider;  VAR x: CHAR );
				BEGIN  {EXCLUSIVE}
					OFiles.Read( r, x )
				END Read;

				PROCEDURE ReadBytes*( VAR r: Files.Rider;  VAR x: ARRAY OF CHAR;  ofs, len: LONGINT );
				VAR buf: ARRAY 4096 OF CHAR;
				BEGIN  {EXCLUSIVE}
					IF ofs = 0 THEN  OFiles.ReadBytes( r, x, len )
					ELSE
						ASSERT( len <= 4096 );
						OFiles.ReadBytes( r, buf, len );
						S.MOVE( S.ADR( buf ), S.ADR( x[ofs] ), len )
					END
				END ReadBytes;

				PROCEDURE Write*( VAR r: Files.Rider;  x: CHAR );
				BEGIN  {EXCLUSIVE}
					OFiles.Write( r, x )
				END Write;

				PROCEDURE WriteBytes*( VAR r: Files.Rider;  CONST x: ARRAY OF CHAR;  ofs, len: LONGINT );
				VAR buf: ARRAY 4096 OF CHAR;
				BEGIN  {EXCLUSIVE}
					IF LEN( x ) - ofs < len THEN  S.HALT( 19 )  END;
					IF len > 0 THEN
						IF ofs = 0 THEN  OFiles.WriteBytes( r, x, len )
						ELSE
							ASSERT( len <= 4096 );
							S.MOVE( S.ADR( x[ofs] ), S.ADR( buf ), len );
							OFiles.WriteBytes( r, buf, len )
						END
					END
				END WriteBytes;

				PROCEDURE Length*( ): LONGINT;
				BEGIN
					RETURN OFiles.Length( unixfile )
				END Length;

				PROCEDURE GetDate*( VAR t, d: LONGINT );
				BEGIN {EXCLUSIVE}
					OFiles.GetDate( unixfile, t, d );
				END GetDate;

				PROCEDURE SetDate*( t, d: LONGINT );
				BEGIN {EXCLUSIVE}
					OFiles.SetDate( unixfile, t, d );
				END SetDate;

				PROCEDURE GetAttributes*( ): SET;
				BEGIN {EXCLUSIVE}
					RETURN attr
				END GetAttributes;

				PROCEDURE SetAttributes*( Attr: SET );
				BEGIN {EXCLUSIVE}
				END SetAttributes;

				PROCEDURE InclAttribute*( Attr: LONGINT );
				BEGIN {EXCLUSIVE}
				END InclAttribute;

				PROCEDURE ExclAttribute*( Attr: LONGINT );
				BEGIN {EXCLUSIVE}
				END ExclAttribute;

				PROCEDURE Register0*( VAR res: LONGINT );
				BEGIN {EXCLUSIVE}
					OFiles.Register( unixfile );  res := Files.Ok
				END Register0;

				PROCEDURE Update*;
				BEGIN {EXCLUSIVE}
					OFiles.Close( unixfile );
				END Update;

				PROCEDURE GetName*( VAR name: ARRAY OF CHAR );
				BEGIN {EXCLUSIVE}
					OFiles.GetName( unixfile, name );
				END GetName;

				PROCEDURE GetFullName*( VAR name: ARRAY OF CHAR;  WithPrefix: BOOLEAN );
				BEGIN {EXCLUSIVE}
					OFiles.GetName( unixfile, name );
				END GetFullName;

			END File;



VAR
	currEnumerator: Files.Enumerator;

	PROCEDURE EntryHandler( filename: ARRAY OF CHAR;  t, d, s: LONGINT;  VAR continue: BOOLEAN );
	VAR  fn: Filename;
	BEGIN
	 	COPY( filename, fn );
		currEnumerator.PutEntry( fn, {}, t, d, s );
		continue := TRUE
	END EntryHandler;


	PROCEDURE Install*;
	VAR fs: FileSystem;
	BEGIN
		NEW( fs );  Files.Add( fs, "Unix" );
	END Install;

END UnixFiles.
