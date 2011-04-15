MODULE FoxIntermediateCodeAssembler;
IMPORT
	Strings, Diagnostics, D := Debugging, SyntaxTree := FoxSyntaxTree, Scanner := FoxScanner, Sections := FoxSections,
	IntermediateCode := FoxIntermediateCode, Basic := FoxBasic, Streams, Files, Backend := FoxBackend,
	Global := FoxGlobal, Formats := FoxFormats, SemanticChecker := FoxSemanticChecker, ActiveCells := FoxActiveCells;

TYPE
	(** the intermediate code parser **)
	IntermediateCodeParser* = OBJECT
	CONST
		Trace = FALSE;
		Strict = TRUE;
	VAR
		diagnostics: Diagnostics.Diagnostics;
		error: BOOLEAN;
		symbol: Scanner.Symbol;
		scanner: Scanner.AssemblerScanner;
		system: Global.System;

		PROCEDURE &Init*(diagnostics: Diagnostics.Diagnostics; defaultSystem: Global.System);
		BEGIN
			ASSERT(defaultSystem # NIL); (* a default system object is required in case there is no platform directive *)
			SELF.diagnostics := diagnostics;
			system := defaultSystem;
			error := FALSE
		END Init;

		PROCEDURE Error(pos: LONGINT; CONST msg: ARRAY OF CHAR);
		BEGIN
			error := TRUE;
			IF diagnostics # NIL THEN
				diagnostics.Error(scanner.source,pos,Diagnostics.Invalid,msg);
			END;

			D.Update;
			(*
			D.TraceBack;
			*)
		END Error;

		PROCEDURE NextSymbol;
		BEGIN error := error OR ~scanner.GetNextSymbol(symbol)
		END NextSymbol;

		PROCEDURE ThisToken(x: LONGINT): BOOLEAN;
		BEGIN
			IF ~error & (symbol.token = x) THEN NextSymbol; RETURN TRUE ELSE RETURN FALSE END;
		END ThisToken;

		PROCEDURE GetIdentifier(VAR pos: LONGINT; VAR identifier: ARRAY OF CHAR): BOOLEAN;
		BEGIN
			pos := symbol.start;
			IF symbol.token # Scanner.Identifier THEN RETURN FALSE
			ELSE COPY(symbol.string,identifier); NextSymbol; RETURN TRUE
			END;
		END GetIdentifier;

		PROCEDURE ExpectToken(x: LONGINT): BOOLEAN;
		VAR
			s: Scanner.StringType;
		BEGIN
			IF ThisToken(x) THEN RETURN TRUE
			ELSE
				s := "expected token "; Strings.Append(s,Scanner.tokens[x]); Strings.Append(s," but got "); Strings.Append(s,Scanner.tokens[symbol.token]);
				Error(symbol.start, s);RETURN FALSE
			END;
		END ExpectToken;

		PROCEDURE ThisIdentifier(CONST this: ARRAY OF CHAR): BOOLEAN;
		BEGIN
			IF ~error & (symbol.token = Scanner.Identifier) & (this = symbol.string) THEN NextSymbol; RETURN TRUE ELSE RETURN FALSE END;
		END ThisIdentifier;

		PROCEDURE ExpectAnyIdentifier(VAR pos: LONGINT; VAR identifier: ARRAY OF CHAR): BOOLEAN;
		BEGIN
			IF ~GetIdentifier(pos,identifier)THEN Error(pos,"identifier expected"); RETURN FALSE
			ELSE RETURN TRUE
			END;
		END ExpectAnyIdentifier;

		PROCEDURE IgnoreNewLines;
		BEGIN
			WHILE ThisToken(Scanner.Ln) DO END;
		END IgnoreNewLines;

		(* expect the newline or end-of-text symbol *)
		PROCEDURE ExpectLineDelimiter(): BOOLEAN;
		BEGIN
			IF ~error & ((symbol.token = Scanner.Ln) OR (symbol.token = Scanner.EndOfText)) THEN
				NextSymbol;
				RETURN TRUE
			ELSE
				Error(symbol.start, "end of line/text expected");
				RETURN FALSE
			END;
		END ExpectLineDelimiter;

		PROCEDURE ParseLineNumber(expectedLineNumber: LONGINT);
		VAR
			linePosition, specifiedLineNumber: LONGINT;
			message, tempString: SyntaxTree.String;
		BEGIN
			IF Trace THEN D.String(">>> ParseLineNumber"); D.Ln END;

			linePosition := symbol.start;
			IF ThisToken(Scanner.Number) THEN (* note: line numbers are optional *)
				specifiedLineNumber := symbol.integer;
				IF ExpectToken(Scanner.Colon) THEN
					IF specifiedLineNumber # expectedLineNumber THEN
						message := "invalid code line number (";
						Strings.IntToStr(specifiedLineNumber, tempString); Strings.Append(message, tempString);
						Strings.Append(message, " instead of ");
						Strings.IntToStr(expectedLineNumber, tempString); Strings.Append(message, tempString);
						Strings.Append(message, ")");
						Error(linePosition, message)
					END
				END
			END
		END ParseLineNumber;

		(** consume a single operand **)
		PROCEDURE ParseOperand(VAR operand: IntermediateCode.Operand; sectionList: Sections.SectionList);
		VAR
			operandPosition, pos, registerNumber, symbolOffset, someLongint: LONGINT;
			someHugeint: HUGEINT;
			hasTypeDescriptor, isMemoryOperand, lastWasIdentifier, isNegated: BOOLEAN;
			someLongreal: LONGREAL;
			identifier: SyntaxTree.String;
			type: IntermediateCode.Type;
			symbolSection: Sections.Section;
		BEGIN
			IF Trace THEN D.String(">>> ParseOperand"); D.Ln END;

			operandPosition := symbol.start;

			(* defaults *)
			hasTypeDescriptor := FALSE;
			isMemoryOperand := FALSE;

			(* consume optional type description *)
			lastWasIdentifier := GetIdentifier(pos, identifier);
			IF lastWasIdentifier & IntermediateCode.DenotesType(identifier, type) THEN
				hasTypeDescriptor := TRUE;
				lastWasIdentifier := GetIdentifier(pos, identifier)
			(*
			ELSE
				type := IntermediateCode.UnsignedIntegerType(system.addressSize)
			*)
			END;

			(* consume optional memory operand bracket *)
			IF ~lastWasIdentifier THEN
				isMemoryOperand := ThisToken(Scanner.LeftBracket);
				lastWasIdentifier := GetIdentifier(pos, identifier)
			END;

			IF lastWasIdentifier THEN
				IF IntermediateCode.DenotesRegister(identifier, registerNumber) THEN
					(* register *)
					IntermediateCode.InitRegister(operand, type, registerNumber);
				ELSE
					(* TODO: handle assembly constants *)

					(* symbol name *)
					symbolOffset := 0;

					(* consume optional symbol offset *)
					IF ThisToken(Scanner.Colon) THEN
						(* TODO: ok, if negative values and hugeints are ignored?*)
						IF ThisToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
							symbolOffset := symbol.integer
						ELSE
							Error(symbol.start, "invalid symbol offset")
						END
					END;

					IF Trace THEN D.String(">>> symbol detected"); D.Ln END;
					symbolSection := IntermediateCode.NewSection(sectionList, Sections.UnknownSection, identifier, NIL, TRUE);

					IntermediateCode.InitAddress(operand, IntermediateCode.UnsignedIntegerType(system.addressSize), symbolSection, symbolOffset)
				END
			ELSIF symbol.token = Scanner.String THEN
				IntermediateCode.InitString(operand, Strings.NewString(symbol.string));
				NextSymbol

			ELSE
				(* immediate values/numbers *)
				isNegated := ThisToken(Scanner.Minus);
				IF ThisToken(Scanner.Number) THEN
					CASE symbol.numberType OF
					| Scanner.Integer:
						IF isNegated THEN someLongint := -symbol.integer ELSE someLongint := symbol.integer END;
						IF ~hasTypeDescriptor THEN
							(* if no type description was included: use number type *)
							IntermediateCode.InitNumber(operand, someLongint);
						ELSIF type.form = IntermediateCode.Float THEN
							ASSERT(hasTypeDescriptor);
							IntermediateCode.InitFloatImmediate(operand, type, REAL(someLongint))
						ELSE
							ASSERT(hasTypeDescriptor & (type.form IN IntermediateCode.Integer));
							IntermediateCode.InitImmediate(operand, type, someLongint)
						END
					| Scanner.Hugeint:
						IF isNegated THEN someHugeint := - symbol.hugeint ELSE someHugeint := symbol.hugeint END;
						IF ~hasTypeDescriptor THEN
							(* if no type description was included: use number type *)
							IntermediateCode.InitNumber(operand, someHugeint)
						ELSIF type.form = IntermediateCode.Float THEN
							ASSERT(hasTypeDescriptor);
							IntermediateCode.InitFloatImmediate(operand, type, REAL(someHugeint))
						ELSE
							ASSERT(hasTypeDescriptor & (type.form IN IntermediateCode.Integer));
							IntermediateCode.InitImmediate(operand, type, someHugeint)
						END
					| Scanner.Real, Scanner.Longreal:
						IF isNegated THEN someLongreal := -symbol.real ELSE someLongreal := symbol.real END;
						(* if no type description was included: use default float type *)
						IF ~hasTypeDescriptor THEN
							IntermediateCode.InitType(type, IntermediateCode.Float, 32)
						END;
						IF type.form IN IntermediateCode.Integer THEN
							Error(operandPosition, "floating point immediate value not applicable")
						ELSE
							IntermediateCode.InitFloatImmediate(operand, type, someLongreal)
						END
					ELSE HALT(100)
					END
				ELSE
					Error(operandPosition, "invalid operand")
				END
			END;

			(* consume optional system units offset *)
			IF ThisToken(Scanner.Plus) THEN
				IF ThisToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
					IntermediateCode.SetOffset(operand, symbol.integer)
				ELSE
					Error(symbol.start, "invalid offset")
				END
			ELSIF ThisToken(Scanner.Minus) THEN
				IF ThisToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
					IntermediateCode.SetOffset(operand, -symbol.integer)
				ELSE
					Error(symbol.start, "invalid offset")
				END
			END;

			(* wrap memory operand around current operand if necessary *)
			IF isMemoryOperand & ExpectToken(Scanner.RightBracket) THEN
				IntermediateCode.SetType(operand, IntermediateCode.UnsignedIntegerType(system.addressSize)); (* set the type of the inner operand to the platform's address type *)
				IntermediateCode.InitMemory(operand, type, operand, 0) (* TODO: add offset? *)
			END
		END ParseOperand;

		PROCEDURE ParseInstruction(VAR instruction: IntermediateCode.Instruction; sectionList: Sections.SectionList);
		VAR
			opCode: SHORTINT;
			positionOfInstruction, operandPosition, operandNumber: LONGINT;
			operand: IntermediateCode.Operand;
			operands: ARRAY 3 OF IntermediateCode.Operand;
			operandType: IntermediateCode.Type;
			identifier, message: SyntaxTree.String;
		BEGIN
			IF Trace THEN D.String(">>> ParseInstruction"); D.Ln END;

			positionOfInstruction := symbol.start;
			IF ExpectAnyIdentifier(positionOfInstruction, identifier) THEN
				(* TODO: detect labels of the form << labelName: >> *)
				opCode := IntermediateCode.FindMnemonic(identifier);
				IF opCode = IntermediateCode.None THEN
					Error(positionOfInstruction, "unknown mnemonic")
				ELSE
					(* consume all operands *)
					IntermediateCode.InitType(operandType, IntermediateCode.SignedInteger, 32); (* defaults *)
					IntermediateCode.InitOperand(operands[0]);
					IntermediateCode.InitOperand(operands[1]);
					IntermediateCode.InitOperand(operands[2]);

					operandNumber := 0;
					IF ~ThisToken(Scanner.Ln) & ~ThisToken(Scanner.EndOfText) THEN
						REPEAT
							operandPosition := symbol.start;
							IF operandNumber > 2 THEN
								Error(positionOfInstruction, "instruction has too many operands")
							ELSE
								ParseOperand(operand, sectionList);
								IF ~error THEN
									IF Strict & ~IntermediateCode.CheckOperand(operand, opCode, operandNumber, message) THEN Error(operandPosition, message) END;
									operands[operandNumber] := operand;
									INC(operandNumber)
								END
							END
						UNTIL error OR ~ThisToken(Scanner.Comma);
						IF ~error & ExpectLineDelimiter() THEN END
					END;

					IF ~error THEN
						IntermediateCode.InitInstruction(instruction, opCode, operands[0], operands[1], operands[2]);
						IF Strict & ~IntermediateCode.CheckInstruction(instruction, message) THEN
							IntermediateCode.DumpInstruction(D.Log, instruction); D.Ln;
							Error(positionOfInstruction, message) END;
					END
				END
			END
		END ParseInstruction;

		(** assemble the content of an intermediate code section
		note: 'sectionList' is the list where referenced sections are found/to be created
		**)
		PROCEDURE ParseSectionContent*(scanner: Scanner.AssemblerScanner; assemblySection: IntermediateCode.Section; sectionList: Sections.SectionList);
		VAR
			instruction: IntermediateCode.Instruction;
			lineNumber: LONGINT;
		BEGIN
			IF Trace THEN D.Ln; D.String(">>> ParseSectionContent"); D.Ln END;
			SELF.scanner := scanner;
			IgnoreNewLines;
			lineNumber := 0;
			WHILE ~error & (symbol.token # Scanner.Period) & (symbol.token # Scanner.EndOfText) DO
				(* consume optional line number *)
				ParseLineNumber(lineNumber);
				IF ~error THEN
					ParseInstruction(instruction, sectionList);
					IF ~error THEN
						IF Trace THEN IntermediateCode.DumpInstruction(D.Log, instruction); D.Ln; END;
						assemblySection.Emit(instruction);
						INC(lineNumber)
					END;
				END;
				IgnoreNewLines
			END
		END ParseSectionContent;

		(** parse the content of an intermediate code module **)
		PROCEDURE ParseModuleContent*(scanner: Scanner.AssemblerScanner; sectionList: Sections.SectionList; VAR moduleName: SyntaxTree.String; VAR backend: Backend.Backend; VAR imports: Sections.NameList): BOOLEAN;
		VAR
			pos: LONGINT;
			identifier: Scanner.StringType;
			afterModuleDirective, afterImportsDirective, afterFirstSection: BOOLEAN;
			sectionType: SHORTINT;
			section: IntermediateCode.Section;
			isNegated: BOOLEAN;
		BEGIN
			IF Trace THEN D.Ln; D.String(">>> ParseModuleContent"); D.Ln END;

			moduleName := "";
			NEW(imports, 128);

			ASSERT(scanner # NIL);
			SELF.scanner := scanner;
			NextSymbol; (* read first symbol *)

			(* go through directives *)
			afterModuleDirective := FALSE;
			afterImportsDirective := FALSE;
			afterFirstSection := FALSE;
			WHILE ~error & (symbol.token # Scanner.EndOfText) DO
				IgnoreNewLines;
				IF ExpectToken(Scanner.Period) & ExpectAnyIdentifier(pos, identifier) THEN
					(* module directive *)
					IF identifier = "module" THEN
						IF afterModuleDirective THEN
							Error(pos, "multiple module directives");
						ELSIF ExpectAnyIdentifier(pos, identifier) & ExpectLineDelimiter() THEN
							moduleName := identifier;
							afterModuleDirective := TRUE;
						END

					(* platform directive *)
					ELSIF identifier = "platform" THEN
						IF ~afterModuleDirective THEN
							Error(pos, "platform directive must be preceeded by module directive")
						ELSIF ExpectAnyIdentifier(pos, identifier) & ExpectLineDelimiter() THEN

							(* set the backend *)
							backend := Backend.GetBackendByName(identifier);
							IF backend = NIL THEN
								Error(pos, "unknown platform")
							ELSE
								system := backend.GetSystem()
							END;

						ELSIF afterFirstSection THEN
							Error(pos, "platform directive not before all sections")
						END

					(* imports directive *)
					ELSIF identifier = "imports" THEN
						IF ~afterModuleDirective THEN
							Error(pos, "import directive must be preceeded by module directive")
						ELSIF afterImportsDirective THEN
							Error(pos, "multiple import directives")
						ELSIF afterFirstSection THEN
							Error(pos, "import directive not before all sections")
						ELSE
							REPEAT
								IF ExpectAnyIdentifier(pos, identifier) THEN imports.AddName(identifier) END
							UNTIL error OR ~ThisToken(Scanner.Comma);
							IF ExpectLineDelimiter() THEN
								afterImportsDirective := TRUE
							END
						END

					(* section *)
					ELSE
						IF identifier = "code" THEN sectionType := Sections.CodeSection
						ELSIF identifier = "const" THEN sectionType := Sections.ConstSection
						ELSIF identifier = "var" THEN sectionType := Sections.VarSection
						ELSIF identifier = "bodycode" THEN sectionType := Sections.BodyCodeSection
						ELSIF identifier = "inlinecode" THEN sectionType := Sections.InlineCodeSection
						ELSIF identifier = "initcode" THEN sectionType := Sections.InitCodeSection
						ELSIF identifier = "initcode2" THEN sectionType := Sections.InitCode2Section
						ELSE Error(pos, "invalid directive")
						END;

						IF ~error & ~afterModuleDirective THEN
							Error(pos, "module directive expected first")
						END;

						IF ~error THEN
							IF ExpectAnyIdentifier(pos, identifier) THEN
								section := IntermediateCode.NewSection(sectionList, sectionType, identifier, NIL, TRUE);

								(* set default unit size for the platform, which depends on the  *)
								IF (sectionType = Sections.VarSection) OR (sectionType = Sections.ConstSection) THEN
									section.SetBitsPerUnit(system.dataUnit)
								ELSE
									section.SetBitsPerUnit(system.codeUnit)
								END;
								ASSERT(section.bitsPerUnit # Sections.UnknownSize);

								(* consume optional section properties *)
								WHILE ~error & (symbol.token # Scanner.EndOfText) & (symbol.token # Scanner.Ln) DO
									(* consume optional offset specification *)

									(* offset *)
									IF ThisIdentifier("offset") & ExpectToken(Scanner.Equal) THEN
										isNegated := ThisToken(Scanner.Minus);
										IF ExpectToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
											IF isNegated THEN section.SetOffset(-symbol.integer) ELSE section.SetOffset(symbol.integer) END
										ELSE
											Error(symbol.start, "invalid offset")
										END

									(* fingerprint *)
									ELSIF ThisIdentifier("fingerprint") & ExpectToken(Scanner.Equal) THEN
										isNegated := ThisToken(Scanner.Minus);
										IF ExpectToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
											IF isNegated THEN section.SetFingerprint(-symbol.integer) ELSE section.SetFingerprint(symbol.integer) END
										ELSE
											Error(symbol.start, "invalid fingerprint")
										END

									(* alignment *)
									ELSIF ThisIdentifier("aligned") & ExpectToken(Scanner.Equal) THEN
										IF ExpectToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
											section.SetPositionOrAlignment(FALSE, symbol.integer)
										ELSE
											Error(symbol.start, "invalid alignment")
										END

									(* fixed position *)
									ELSIF ThisIdentifier("fixed") & ExpectToken(Scanner.Equal) THEN
										IF ExpectToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
											section.SetPositionOrAlignment(TRUE, symbol.integer)
										ELSE
											Error(symbol.start, "invalid fixed postion")
										END

									(* unit size *)
									ELSIF ThisIdentifier("unit") & ExpectToken(Scanner.Equal) THEN
										IF ExpectToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
											(* overwrite default unit size *)
											section.SetBitsPerUnit(symbol.integer)
										ELSE
											Error(symbol.start, "invalid unit size")
										END

									(* relocatability *)
									ELSIF ThisIdentifier("relocatable") THEN
										(* TODO *)

									ELSIF ThisIdentifier("size") THEN
										(* ignore *)
										(* note: the size is never set but calculated from the section content *)

									ELSIF ThisIdentifier("fixups") THEN
										(* ignore *)

									ELSE
										Error(symbol.start, "invalid property")
									END
								END;
								IF ~error & ExpectLineDelimiter() THEN
									ParseSectionContent(scanner, section, sectionList);
									afterFirstSection := TRUE
								END
							END
						END
					END
				END
			END;
			RETURN ~error
		END ParseModuleContent;

		PROCEDURE ParseModule*(scanner: Scanner.AssemblerScanner): Sections.Module;
		VAR
			result: Sections.Module;
			moduleName, platformName: SyntaxTree.String;
			backend: Backend.Backend;
			imports: Sections.NameList;
		BEGIN
			NEW(result, NIL, NIL); (* note: 1. there is no syntax tree module, 2. the system object to be used is not yet known *)
			IF ParseModuleContent(scanner, result.sections, moduleName, backend, imports) THEN
				backend.GetDescription(platformName);

				result.SetModuleName(moduleName);
				result.SetSystem(backend.GetSystem());
				result.SetPlatformName(platformName);
				result.SetImports(imports);

				IF Trace THEN
					D.String("++++++++++ PARSED MODULE '"); D.String(result.moduleName); D.String("' ++++++++++"); D.Ln;
					result.Dump(D.Log)
				END
			ELSE
				result := NIL
			END
		END ParseModule;
	END IntermediateCodeParser;

	(** the assemblinker **)
	Assemblinker* = OBJECT
	CONST
		Trace = FALSE;
	TYPE
		ArrangementRestriction = RECORD
			fixed: BOOLEAN;
			positionOrAlignment: LONGINT;
		END;
	VAR
		diagnostics: Diagnostics.Diagnostics;
		backend-: Backend.Backend;
		rootModuleName, platformName: SyntaxTree.String;
		importList, loadedModules: Sections.NameList;
		allSections: Sections.SectionList;
		isSorted, alreadyPrearrangedSinceLastSort: BOOLEAN;
		originalRestrictions: POINTER TO ARRAY OF ArrangementRestriction;

		PROCEDURE & Init*(diagnostics: Diagnostics.Diagnostics; defaultBackend: Backend.Backend);
		BEGIN
			SELF.diagnostics := diagnostics;
			backend := defaultBackend;
			defaultBackend.GetDescription(platformName);
			rootModuleName := "Unnamed";
			NEW(allSections);
			NEW(importList, 128);
			NEW(loadedModules, 128);
			isSorted := FALSE;
		END Init;

		(** load a module given by its name from an IR-file
			- if 'resursive' is TRUE: also load the referenced modules from their corresponding files
			- return TRUE if operation was successful
		**)
		PROCEDURE LoadModule*(moduleName: SyntaxTree.String; isRecursive: BOOLEAN): BOOLEAN;
		BEGIN RETURN LoadModule2(moduleName, isRecursive, TRUE)
		END LoadModule;

		PROCEDURE LoadModule2(moduleName: SyntaxTree.String; isRecursive, isRoot: BOOLEAN): BOOLEAN;
		VAR
			filename, parsedModuleName: SyntaxTree.String;
			parsedImportList: Sections.NameList;
			assemblerScanner: Scanner.AssemblerScanner;
			intermediateCodeParser: IntermediateCodeParser;
			reader: Streams.Reader;
			parsedBackend: Backend.Backend;
			i: LONGINT;
		BEGIN
			IF Trace THEN D.String(">>> LoadModule "); D.String(moduleName); D.Ln END;

			(* check if the module has already been incorporated *)
			IF loadedModules.ContainsName(moduleName) THEN
				IF Trace THEN D.String(">>> module "); D.String(moduleName); D.String(" has already been loaded"); D.Ln END;
				RETURN TRUE
			ELSE
				IF moduleName = "SYSTEM" THEN
					(* nothing to do *)
				ELSE
					(* open corresponding IR file *)
					filename := moduleName; Files.JoinExtension(filename, "ir", filename); (* TODO: include path *)
					reader := Basic.GetFileReader(filename);

					IF reader = NIL THEN
						diagnostics.Error(filename, Diagnostics.Invalid, Diagnostics.Invalid, "failed to open");
						RETURN FALSE
					ELSE
						IF Trace THEN D.String(">>> IR file successfully opened: "); D.String(filename); D.Ln END;

						(* parse IR file *)
						NEW(assemblerScanner, filename, reader, 0, diagnostics);
						NEW(intermediateCodeParser, diagnostics, backend.GetSystem());

						IF intermediateCodeParser.ParseModuleContent(assemblerScanner, allSections, parsedModuleName, parsedBackend, parsedImportList) THEN
							IF Trace THEN
								D.String(">>> IR file successfully parsed: "); D.String(filename); D.Ln;
								DumpAllSections(D.Log);
							END;
							isSorted := FALSE; (* sections are not sorted anymore *)
							IF isRoot THEN
								SELF.rootModuleName := moduleName;
								(* if the root module specifies a platform/backend, the default backend is overwritten *)
								IF parsedBackend # NIL THEN
									backend := parsedBackend;
									backend.GetDescription(platformName)
								END
							END;
							IF isRecursive THEN
								(* go through all imports *)
								FOR i := 0 TO parsedImportList.Length() - 1 DO
									IF ~LoadModule2(parsedImportList.GetName(i), TRUE, FALSE) THEN RETURN FALSE END
								END
								(* note that 'SELF.importList' remains empty *)
							ELSE
								SELF.importList := parsedImportList
							END;
							RETURN TRUE
						ELSE
							diagnostics.Error(filename, Diagnostics.Invalid, Diagnostics.Invalid, "IR file could not be parsed");
							RETURN FALSE
						END
					END
				END;
				loadedModules.AddName(moduleName);
				RETURN TRUE
			END
		END LoadModule2;

		(** mark a section with a certain name as reachable **)
		PROCEDURE MarkAsReachableByName*(CONST name: ARRAY OF CHAR);
		VAR
			section: Sections.Section;
		BEGIN
			section:= allSections.FindByName(name);
			ASSERT(section # NIL);
			MarkAsReachable(section)
		END MarkAsReachableByName;

		(** mark all sections whose names start with a certain prefix as reachable **)
		PROCEDURE MarkAsReachableStartingWith*(CONST prefix: ARRAY OF CHAR);
		VAR
			section: Sections.Section;
			i: LONGINT;
		BEGIN
			(* TODO: could or should one make this faster using a hash table? *)
			(* go through all sections *)
			FOR i := 0 TO allSections.Length() - 1 DO
				section := allSections.GetSection(i);
				IF Strings.StartsWith(prefix, 0, section.name) THEN MarkAsReachable(section) END
			END
		END MarkAsReachableStartingWith;

		(** mark a section as reachable and do the same recursively for all referenced sections **)
		PROCEDURE MarkAsReachable(section: Sections.Section);
		VAR
			intermediateCodeSection: IntermediateCode.Section;
			i: LONGINT;
		BEGIN
			IF ~section.isReachable THEN
				IF Trace THEN D.String(">>> MarkAsReachable "); D.String(section.name); D.Ln END;
				section.SetReachability(TRUE);
				ASSERT(section IS IntermediateCode.Section);
				intermediateCodeSection := section(IntermediateCode.Section);
				(* go through all instructions in the section *)
				FOR i := 0 TO intermediateCodeSection.pc - 1 DO
					IF intermediateCodeSection.instructions[i].op1.symbol # NIL THEN MarkAsReachable(intermediateCodeSection.instructions[i].op1.symbol) END;
					IF intermediateCodeSection.instructions[i].op2.symbol # NIL THEN MarkAsReachable(intermediateCodeSection.instructions[i].op2.symbol) END;
					IF intermediateCodeSection.instructions[i].op3.symbol # NIL THEN MarkAsReachable(intermediateCodeSection.instructions[i].op3.symbol) END
				END
			END
		END MarkAsReachable;

		(** mark all sections as either reachable or unreachable **)
		PROCEDURE MarkReachabilityOfAll*(isReachable: BOOLEAN);
		VAR
			section: Sections.Section;
			i: LONGINT;
		BEGIN
			IF Trace THEN D.String(">>> MarkReachabilityOfAll "); IF isReachable THEN D.String("TRUE") ELSE D.String("FALSE") END; D.Ln END;
			FOR i := 0 TO allSections.Length() - 1 DO
				section := allSections.GetSection(i);
				section.SetReachability(isReachable)
			END
		END MarkReachabilityOfAll;

		(** dump all sections (both reachable and not) **)
		PROCEDURE DumpAllSections*(writer: Streams.Writer);
		VAR
			section: Sections.Section;
			i: LONGINT;
		BEGIN
			FOR i := 0 TO allSections.Length() - 1 DO
				section := allSections.GetSection(i);
				IF section.isReachable THEN
					writer.String("REACHABLE ")
				ELSE
					writer.String("unreachable ")
				END;
				section.Dump(writer)
			END;
			writer.Update
		END DumpAllSections;

		(** store the original arrangment restrictions of all sections **)
		PROCEDURE StoreOriginalRestrictions;
		VAR
			section: Sections.Section;
			i: LONGINT;
		BEGIN
			NEW(originalRestrictions, allSections.Length());
			FOR i := 0 TO allSections.Length() - 1 DO
				section := allSections.GetSection(i);
				originalRestrictions[i].fixed := section.fixed;
				originalRestrictions[i].positionOrAlignment := section.positionOrAlignment
			END
		END StoreOriginalRestrictions;

		(** restore the original arrangment restrictions of all sections **)
		PROCEDURE RestoreOriginalRestrictions;
		VAR
			section: Sections.Section;
			i: LONGINT;
		BEGIN
			ASSERT(LEN(originalRestrictions) = allSections.Length());
			FOR i := 0 TO allSections.Length() - 1 DO
				section := allSections.GetSection(i);
				section.SetPositionOrAlignment(originalRestrictions[i].fixed, originalRestrictions[i].positionOrAlignment)
			END
		END RestoreOriginalRestrictions;

		PROCEDURE PrearrangeReachableDataSections*();
		VAR
			fixedDataSections, flexibleDataSections: Sections.SectionList;
			section, fixedDataSection, flexibleDataSection: Sections.Section;
			i, currentAddress, nextOccupiedAddress, flexibleDataSectionIndex, fixedDataSectionIndex, startAddress, endAddress: LONGINT;
			done: BOOLEAN;
		BEGIN
			(* sort sections if necessary *)
			IF ~isSorted THEN
				IF Trace THEN D.String("++++++++++ before sorting ++++++++++"); DumpAllSections(D.Log) END;
				allSections.Sort(SectionBeforeOther);
				IF Trace THEN D.String("++++++++++ after sorting ++++++++++"); DumpAllSections(D.Log) END;
				isSorted := TRUE;
				alreadyPrearrangedSinceLastSort := FALSE
			END;
			ASSERT(isSorted);
			IF alreadyPrearrangedSinceLastSort THEN RestoreOriginalRestrictions ELSE StoreOriginalRestrictions END;

			IF Trace THEN D.String("before prearrangement"); D.Ln; DumpAllSections(D.Log); D.Ln END;

			(* create new lists for reachable data sections that are fixed or flexible, respectively *)
			NEW(fixedDataSections);
			NEW(flexibleDataSections);

			(* go through all reachable data sections, and put them into one of two lists *)
			FOR i:= 0 TO allSections.Length() - 1 DO
				section := allSections.GetSection(i);
				IF section.isReachable & ((section.type = Sections.ConstSection) OR (section.type = Sections.VarSection)) THEN
					IF section.fixed THEN
						fixedDataSections.AddSection(section)
					ELSE
						flexibleDataSections.AddSection(section)
					END
				END
			END;

			IF Trace THEN
				D.String("++++++++++ reachable fixed data sections ++++++++++"); fixedDataSections.Dump(D.Log); D.Ln;
				D.String("++++++++++ reachable flexible data sections ++++++++++"); flexibleDataSections.Dump(D.Log); D.Ln;
			END;

			(* arrange the sections (i.e. set the fixed attribute) such that the given fixed-positions and alignments are respected *)
			currentAddress := 0;
			flexibleDataSectionIndex := 0;
			(* go through all fixed data sections of the cell *)
			FOR fixedDataSectionIndex := 0 TO fixedDataSections.Length() DO (* note: the index may be out-of-bounds! *)
				IF fixedDataSectionIndex < fixedDataSections.Length() THEN
					fixedDataSection := fixedDataSections.GetSection(fixedDataSectionIndex);
					ASSERT(fixedDataSection.fixed);
					nextOccupiedAddress := fixedDataSection.positionOrAlignment
				ELSE
					(* there is no more fixed data section *)
					nextOccupiedAddress := MAX(LONGINT)
				END;

				done := FALSE;
				WHILE ~done DO
					IF flexibleDataSectionIndex < flexibleDataSections.Length() THEN
						flexibleDataSection := flexibleDataSections.GetSection(flexibleDataSectionIndex);

						(* determine start-address of the next section (respect alignment) *)
						IF flexibleDataSection.IsAligned() & ((currentAddress MOD flexibleDataSection.positionOrAlignment) # 0) THEN
							startAddress := currentAddress + flexibleDataSection.positionOrAlignment - (currentAddress MOD flexibleDataSection.positionOrAlignment)
						ELSE
							startAddress := currentAddress
						END;

						(* determine end-address fo the next section *)
						endAddress := startAddress + flexibleDataSection.GetSize();

						IF endAddress <= nextOccupiedAddress THEN
							(* there is enough space for the section *)
							flexibleDataSection.SetPositionOrAlignment(TRUE, startAddress); (* position is set for section *)
							INC(flexibleDataSectionIndex);
							currentAddress := endAddress
						ELSE
							(* there is no more space for sections *)
							done := TRUE
						END
					ELSE
						(* there are no more flexible data sections *)
						done := TRUE
					END
				END;

				IF fixedDataSectionIndex < fixedDataSections.Length() THEN
					ASSERT(fixedDataSection.GetSize() # Sections.UnknownSize);
					currentAddress := fixedDataSection.positionOrAlignment + fixedDataSection.GetSize()
				END
			END;

			alreadyPrearrangedSinceLastSort := TRUE;

			IF Trace THEN D.String("after prearrangement"); D.Ln; DumpAllSections(D.Log); D.Ln END;
		END PrearrangeReachableDataSections;

		PROCEDURE PatchValueInSection*(CONST sectionName: ARRAY OF CHAR; syntaxTreeValue: SyntaxTree.Value);
		VAR
			section: Sections.Section;
			emptyOperand, dataOperand: IntermediateCode.Operand;
			dataInstruction: IntermediateCode.Instruction;
			hugeintValue: HUGEINT;
		BEGIN
			section := allSections.FindByName(sectionName);
			ASSERT(section # NIL);

			IF syntaxTreeValue IS SyntaxTree.BooleanValue THEN
				(* BOOLEAN *)
				IF syntaxTreeValue(SyntaxTree.BooleanValue).value THEN hugeintValue := 1 ELSE hugeintValue := 0
				END
			ELSIF syntaxTreeValue IS SyntaxTree.IntegerValue THEN
				(* INTEGER *)
				hugeintValue := syntaxTreeValue(SyntaxTree.IntegerValue).hvalue;
			ELSE
				HALT(100)
			END;

			IntermediateCode.InitImmediate(dataOperand, IntermediateCode.GetType(backend.GetSystem(), syntaxTreeValue.type.resolved), hugeintValue);
			IntermediateCode.InitOperand(emptyOperand);
			IntermediateCode.InitInstruction(dataInstruction, IntermediateCode.data, dataOperand, emptyOperand, emptyOperand);

			ASSERT(section IS IntermediateCode.Section);
			section(IntermediateCode.Section).EmitAt(0, dataInstruction)
		END PatchValueInSection;

		(** get all reachable sections in the form of an intermediate code module **)
		PROCEDURE ExtractModule*(): Sections.Module;
		BEGIN RETURN ExtractModuleWithName(rootModuleName)
		END ExtractModule;

		(** get all reachable sections in the form of an intermediate code module with a certain name **)
		PROCEDURE ExtractModuleWithName*(desiredName: SyntaxTree.String): Sections.Module;
		VAR
			result: Sections.Module;
			section: Sections.Section;
			i: LONGINT;
		BEGIN
			NEW(result, NIL, backend.GetSystem()); (* note: there is no syntax tree *)
			result.SetModuleName(desiredName);
			result.SetPlatformName(platformName);
			result.SetImports(importList);

			(* add all of the reachable sections from the cumulative section list into the resulting module's section list *)
			FOR i := 0 TO allSections.Length() - 1 DO
				section := allSections.GetSection(i);

				(* remove any previously generated code *)
				ASSERT(section IS IntermediateCode.Section);
				section(IntermediateCode.Section).SetResolved(NIL);

				IF section.isReachable & (section.type # Sections.UnknownSection) THEN (* note: sections of unknown type are also excluded *)
					result.sections.AddSection(section)
				END
			END;

			IF Trace THEN D.String("+++++++++ intermediate code module ++++++++++"); D.Ln; result.Dump(D.Log); D.Ln; END;

			RETURN result
		END ExtractModuleWithName;

		(** whether a section should appear before another one in an assembly (used for sorting)
			- 1st priority: when sections have fixed positions, the ones with smaller addresses come first
			- 2nd priority: smaller sections come first
		**)
		PROCEDURE SectionBeforeOther(leftObject, rightObject: ANY): BOOLEAN;
		VAR
			leftSection, rightSection: Sections.Section;
			leftPosition, rightPosition, leftSize, rightSize: LONGINT;
		BEGIN
			ASSERT((leftObject IS Sections.Section) & (rightObject IS Sections.Section));
			leftSection := leftObject(Sections.Section);
			rightSection := rightObject(Sections.Section);

			IF leftSection.fixed THEN
				leftPosition := leftSection.positionOrAlignment
			ELSE
				leftPosition := MAX(LONGINT)
			END;
			IF rightSection.fixed THEN
				rightPosition := rightSection.positionOrAlignment
			ELSE
				rightPosition := MAX(LONGINT)
			END;

			IF leftPosition < rightPosition THEN
				RETURN TRUE
			ELSIF leftPosition > rightPosition THEN
				RETURN FALSE
			ELSE
				ASSERT(leftPosition = rightPosition); (* note: this is the case for sections without fixed positions *)
				leftSize := leftSection.GetSize();
				rightSize := rightSection.GetSize();
				IF leftSize = Sections.UnknownSize THEN leftSize := MAX(LONGINT) END;
				IF rightSize = Sections.UnknownSize THEN rightSize := MAX(LONGINT) END;
				RETURN leftSize < rightSize
			END
		END SectionBeforeOther;

		(* generate binary code and write an object file with the current root module's name *)
		PROCEDURE GenerateObjectFile*(objectFileFormat: Formats.ObjectFileFormat; log: Streams.Writer; flags: SET; checker: SemanticChecker.Checker; activeCellsSpecification: ActiveCells.Specification): BOOLEAN;
		BEGIN RETURN GenerateObjectFileWithName(objectFileFormat, log, flags, checker, activeCellsSpecification, rootModuleName)
		END GenerateObjectFile;

		(* generate binary code and write an object file with a desired module name *)
		PROCEDURE GenerateObjectFileWithName*(objectFileFormat: Formats.ObjectFileFormat; log: Streams.Writer; flags: SET; checker: SemanticChecker.Checker; activeCellsSpecification: ActiveCells.Specification; desiredName: SyntaxTree.String): BOOLEAN;
		VAR
			intermediateCodeModule: Sections.Module;
			binaryModule: Formats.GeneratedModule;
			result: BOOLEAN;
		BEGIN
			intermediateCodeModule := ExtractModuleWithName(desiredName);
			result := TRUE;

			(* generate binary code *)
			backend.Initialize(diagnostics, log, flags, checker, backend.GetSystem(), activeCellsSpecification);
			binaryModule := backend.ProcessIntermediateCodeModule(intermediateCodeModule);
			IF binaryModule = NIL THEN
				diagnostics.Error(desiredName, Diagnostics.Invalid, Diagnostics.Invalid, "the specified backend cannot process intermediate code");
				result := FALSE
			ELSIF backend.error THEN
				diagnostics.Error(desiredName, Diagnostics.Invalid, Diagnostics.Invalid, "binary code could not be generated (backend error)");
				result := FALSE
			ELSE
				IF Trace THEN D.String(">>> binary code successfully generated"); D.Ln END;
				IF objectFileFormat = NIL THEN
					diagnostics.Error(desiredName, Diagnostics.Invalid, Diagnostics.Invalid, "no object file format specified");
					result := FALSE
				ELSE
					(* write the generated code into an object file *)
					objectFileFormat.Initialize(diagnostics);
					IF objectFileFormat.Export(binaryModule, NIL) THEN
						IF Trace THEN D.String(">>> object file successfully written"); D.Ln END;
					ELSE
						diagnostics.Error(desiredName, Diagnostics.Invalid, Diagnostics.Invalid, "object file could not be written");
						result := FALSE
					END
				END
			END;
			RETURN result
		END GenerateObjectFileWithName;

	END Assemblinker;

END FoxIntermediateCodeAssembler.
