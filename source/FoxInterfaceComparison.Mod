MODULE FoxInterfaceComparison; (** AUTHOR "fof"; PURPOSE "compare interfaces / check symbol file compliances"; *)

IMPORT SyntaxTree := FoxSyntaxTree, Formats := FoxFormats, FingerPrint := FoxFingerPrint, Global := FoxGlobal, SemanticChecker := FoxSemanticChecker, Diagnostics, Strings;

CONST
	Redefined*=0;
	Extended*=1;

	PROCEDURE CompareThis*(module: SyntaxTree.Module; symbolFileFormat: Formats.SymbolFileFormat; diagnostics: Diagnostics.Diagnostics; importCache: SyntaxTree.ModuleScope;  VAR flags: SET);
	VAR fname: SyntaxTree.String; importedModule: SyntaxTree.Module; fingerprinterOld,fingerprinterNew: FingerPrint.FingerPrinter;

	PROCEDURE SameType(new,old: SyntaxTree.Type): BOOLEAN;
	VAR fpNew,fpOld: FingerPrint.FingerPrint;
	BEGIN
		old := old.resolved; new := new.resolved;

		IF old IS SyntaxTree.PointerType THEN
			old := old(SyntaxTree.PointerType).pointerBase;
		END;
		IF new IS SyntaxTree.PointerType THEN
			new := new(SyntaxTree.PointerType).pointerBase;
		END;
		fpNew := fingerprinterNew.TypeFP(new);
		fpOld := fingerprinterOld.TypeFP(old);
		RETURN (fpNew.privateFP = fpOld.privateFP) & (fpNew.publicFP = fpOld.publicFP) & (fpNew.FP = fpOld.FP);
	END SameType;

	PROCEDURE CompareSymbols(new,old: SyntaxTree.Symbol): BOOLEAN;
	VAR fpNew,fpOld: FingerPrint.FingerPrint; oldType, newType: SyntaxTree.Type;
	BEGIN
		fpNew := fingerprinterNew.SymbolFP(new);
		fpOld := fingerprinterOld.SymbolFP(old);

		IF (fpNew.FP # fpOld.FP) THEN
			RETURN FALSE
		ELSIF (new IS SyntaxTree.TypeDeclaration) & (old IS SyntaxTree.TypeDeclaration) THEN
			oldType := old(SyntaxTree.TypeDeclaration).declaredType;
			newType := new(SyntaxTree.TypeDeclaration).declaredType;
			IF ~SameType(newType,oldType) THEN
				RETURN FALSE
			END;
		END;
		RETURN TRUE
	END CompareSymbols;

	PROCEDURE ErrorSS(pos: LONGINT; CONST s1,s2: ARRAY OF CHAR);
	VAR msg: ARRAY 256 OF CHAR;
	BEGIN
		COPY(s1,msg);
		Strings.Append(msg,s2);
		IF (diagnostics # NIL) & (module # NIL) THEN
			diagnostics.Information(module.sourceName,pos,Diagnostics.Invalid,msg);
		END;
	END ErrorSS;

	PROCEDURE NextSymbol(symbol: SyntaxTree.Symbol): SyntaxTree.Symbol;
	BEGIN
		WHILE (symbol # NIL) & (symbol IS SyntaxTree.Import) DO
			symbol := symbol.nextSymbol;
		END;
		RETURN symbol
	END NextSymbol;


	PROCEDURE CompareScopes(new,old: SyntaxTree.Scope);
	VAR newSymbol, oldSymbol: SyntaxTree.Symbol;
		newName, oldName: SyntaxTree.String;
		newPublic, oldPublic: BOOLEAN;
	BEGIN
		oldSymbol := NextSymbol(old.firstSymbol);
		newSymbol := NextSymbol(new.firstSymbol);

		WHILE (oldSymbol # NIL) & (newSymbol # NIL) DO
			Global.GetSymbolName(oldSymbol,oldName);
			Global.GetSymbolName(newSymbol,newName);
			oldPublic := oldSymbol.access * SyntaxTree.Public # {};
			newPublic := newSymbol.access * SyntaxTree.Public # {};
			IF oldName = newName THEN
				IF oldPublic = newPublic THEN
					IF ~CompareSymbols(newSymbol, oldSymbol) THEN
						ErrorSS(newSymbol.position,newName," is redefined");
						INCL(flags,Redefined);
					END;
				ELSIF oldPublic THEN
					ErrorSS(newSymbol.position,newName," is no longer visible");
					INCL(flags,Redefined);
				ELSIF newPublic THEN
					ErrorSS(newSymbol.position,newName," is new");
					INCL(flags,Extended);
				END;
				oldSymbol := NextSymbol(oldSymbol.nextSymbol);
				newSymbol := NextSymbol(newSymbol.nextSymbol);
			ELSIF oldName < newName THEN
				IF oldPublic THEN
					ErrorSS(Diagnostics.Invalid,oldName," is no longer visible");
					INCL(flags,Redefined);
				END;
				oldSymbol := NextSymbol(oldSymbol.nextSymbol);
			ELSE
				IF newPublic THEN
					ErrorSS(newSymbol.position,newName," is new");
					INCL(flags,Extended);
				END;
				newSymbol := NextSymbol(newSymbol.nextSymbol);
			END;
		END;

		WHILE (oldSymbol # NIL) DO
			oldSymbol.name.GetString(oldName);
			oldPublic := oldSymbol.access * SyntaxTree.Public # {};
			IF oldSymbol.access * SyntaxTree.Public # {} THEN
				ErrorSS(Diagnostics.Invalid,oldName," is no longer visible");
				INCL(flags,Redefined);
			END;
			oldSymbol := NextSymbol(oldSymbol.nextSymbol);
		END;

		WHILE (newSymbol # NIL) DO
			newSymbol.name.GetString(newName);
			newPublic := newSymbol.access * SyntaxTree.Public # {};
			IF newPublic THEN
				ErrorSS(newSymbol.position,newName," is new");
				INCL(flags,Extended);
			END;
			newSymbol := NextSymbol(newSymbol.nextSymbol);
		END;
	END CompareScopes;

	BEGIN
		Global.ModuleFileName(module.name,module.context,fname);
		importedModule := symbolFileFormat.Import(fname,importCache);
		NEW(fingerprinterOld,importedModule,symbolFileFormat.system);
		NEW(fingerprinterNew,module,symbolFileFormat.system);
		IF importedModule # NIL THEN
			CompareScopes(module.moduleScope,importedModule.moduleScope);
			IF importCache # NIL THEN SemanticChecker.RemoveModuleFromCache(importCache, importedModule) END;
		ELSE
			ErrorSS(Diagnostics.Invalid,fname," new module.");
		END;
	END CompareThis;



END FoxInterfaceComparison.
