MODULE OCBackend; (**  AUTHOR "kaeserm,fof"; PURPOSE "Oberon Compiler: Common backend module";  **)

IMPORT
	Diagnostics, Global := OCGlobal, Formats := OCFormats, SyntaxTree := OCSyntaxTree, SemanticChecker := OCSemanticChecker, Options;


TYPE
	Backend* = OBJECT
	VAR
		diagnostics-: Diagnostics.Diagnostics;
		flags-: SET;
		system-: Global.System;
		error-: BOOLEAN;
		checker-: SemanticChecker.Checker;
		source-: SyntaxTree.String;

		(* constructor *)
		PROCEDURE & InitBackend *;
		BEGIN
			system := NIL; (* only one instance per backend, never reallocate ! *)
			diagnostics := NIL;
			flags := {};
			error := FALSE;
		END InitBackend;

		PROCEDURE ResetError*;
		BEGIN error := FALSE
		END ResetError;

		(* initialize backend for usage *)
		PROCEDURE Initialize*(diagnostics: Diagnostics.Diagnostics; flags: SET; checker: SemanticChecker.Checker; system: Global.System);
		BEGIN
			error := FALSE;
			SELF.diagnostics := diagnostics;
			SELF.flags := flags;
			SELF.checker := checker;
			SELF.system := system;
		END Initialize;

		(* Get the system used by this backend (singleton) *)
		PROCEDURE GetSystem*():Global.System;
		BEGIN
			RETURN Global.DefaultSystem();
		END GetSystem;

		PROCEDURE Error*(CONST source: ARRAY OF CHAR; errorNumber, errorPosition: LONGINT; CONST err: ARRAY OF CHAR);
		BEGIN
			IF (err # "") & (diagnostics # NIL) THEN
				diagnostics.Error(source,errorNumber, errorPosition,err);
			END;
			error := TRUE;
		END Error;

		(* Work on a module *)
		PROCEDURE Module*(x: SyntaxTree.Module): Formats.GeneratedModule;
		BEGIN
			ASSERT(x # NIL);
			RETURN NIL;
		END Module;

		PROCEDURE DefineOptions*(options: Options.Options);
		END DefineOptions;

		PROCEDURE GetOptions*(options: Options.Options);
		END GetOptions;

		PROCEDURE DefaultObjectFileFormat*(): Formats.ObjectFileFormat;
		BEGIN RETURN NIL
		END DefaultObjectFileFormat;

		PROCEDURE DefaultSymbolFileFormat*(): Formats.SymbolFileFormat;
		BEGIN RETURN NIL
		END DefaultSymbolFileFormat;

	END Backend;

	PROCEDURE GetDummy*():Backend;
	VAR backend: Backend;
	BEGIN
		NEW(backend);
		RETURN backend;
	END GetDummy;

END OCBackend.