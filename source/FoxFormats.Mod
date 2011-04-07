MODULE FoxFormats;

IMPORT SyntaxTree := FoxSyntaxTree, Global := FoxGlobal, Streams, Diagnostics, Options;

CONST
	NoFindPC*=MAX(LONGINT);

TYPE
	(* container for generated code (intermediate code - binary code) *)
	GeneratedModule*=OBJECT
		VAR			
			(* input for (intermediate) code generation *)
			module-: SyntaxTree.Module;
			system-: Global.System;
			findPC-: LONGINT;
			moduleName-: SyntaxTree.String; (* genasm *)

		PROCEDURE SetFindPC*(findPC: LONGINT);
		BEGIN SELF.findPC := findPC
		END SetFindPC;
		
		PROCEDURE & Init*(module: SyntaxTree.Module; system: Global.System);
		BEGIN SELF.module := module; SELF.system := system; findPC := NoFindPC
		END Init;

		PROCEDURE SetModuleName*(moduleName: SyntaxTree.String);
		BEGIN SELF.moduleName := moduleName
		END SetModuleName;

		PROCEDURE Dump*(w: Streams.Writer);
		VAR name: SyntaxTree.String;
		BEGIN
			w.String(".module "); w.String(moduleName); w.Ln;
			w.Ln;
		END Dump;

	END GeneratedModule;

	(* symbol file import / export for different implementations *)
	SymbolFileFormat*=OBJECT
		VAR diagnostics-:  Diagnostics.Diagnostics; system-: Global.System;

		PROCEDURE &Init*;
		BEGIN diagnostics := NIL; system := NIL;
		END Init;

		PROCEDURE Initialize*(diagnostics: Diagnostics.Diagnostics; system: Global.System);
		BEGIN SELF.diagnostics := diagnostics; SELF.system := system;
		END Initialize;

		PROCEDURE Export*(module: SyntaxTree.Module; importCache: SyntaxTree.ModuleScope): BOOLEAN;
		END Export;

		PROCEDURE Import*(CONST name: ARRAY OF CHAR; importCache: SyntaxTree.ModuleScope): SyntaxTree.Module;
		END Import;

		PROCEDURE DefineOptions*(options: Options.Options);
		BEGIN
		END DefineOptions;

		PROCEDURE GetOptions*(options: Options.Options);
		BEGIN
	END GetOptions;

	END SymbolFileFormat;

	(* object file export for different implementations *)
	ObjectFileFormat*= OBJECT
		VAR diagnostics-: Diagnostics.Diagnostics;

		PROCEDURE &Init*;
		BEGIN diagnostics := NIL
		END Init;

		PROCEDURE Initialize*(diagnostics: Diagnostics.Diagnostics);
		BEGIN SELF.diagnostics := diagnostics
		END Initialize;

		PROCEDURE Export*(module: GeneratedModule; symbolFileFormat: SymbolFileFormat): BOOLEAN;
		BEGIN RETURN FALSE
		END Export;

		PROCEDURE DefineOptions*(options: Options.Options);
		BEGIN
		END DefineOptions;

		PROCEDURE GetOptions*(options: Options.Options);
		BEGIN
		END GetOptions;

		PROCEDURE DefaultSymbolFileFormat*(): SymbolFileFormat;
		BEGIN RETURN NIL
		END DefaultSymbolFileFormat;

		PROCEDURE ForceModuleBodies*(): BOOLEAN;
		BEGIN RETURN FALSE
		END ForceModuleBodies;

	END ObjectFileFormat;

END FoxFormats.