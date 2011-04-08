MODULE FoxIntermediateCodeAssembler;
IMPORT
	Strings, Diagnostics, D := Debugging, SyntaxTree := FoxSyntaxTree, Scanner := FoxScanner, Sections := FoxSections, 
	IntermediateCode := FoxIntermediateCode, Basic := FoxBasic, Streams, Files, Backend := FoxBackend, Formats := FoxFormats, Global := FoxGlobal, SemanticChecker := FoxSemanticChecker;
CONST
	Trace* = TRUE; (* debugging output *)
	ParserTrace* = FALSE;
TYPE
	ArrangementRestriction = RECORD
		fixed: BOOLEAN;
		positionOrAlignment: LONGINT;
	END;
	
	(** the intermediate code parser **)
	IntermediateCodeParser* = OBJECT
	VAR
		diagnostics: Diagnostics.Diagnostics;
		error: BOOLEAN;
		symbol: Scanner.Symbol;
		scanner: Scanner.AssemblerScanner;

		PROCEDURE &Init*(diagnostics: Diagnostics.Diagnostics);
		BEGIN
			SELF.diagnostics := diagnostics;
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

		PROCEDURE RegisterNumberFromIdentifier(VAR registerNumber: LONGINT; identifier: Scanner.StringType): BOOLEAN;
		VAR
			number, digit, position: LONGINT;			
		BEGIN
			registerNumber := IntermediateCode.None; (* default *)
			IF identifier = "sp" THEN
				(* stack pointer register *)
				registerNumber := IntermediateCode.SP;
				RETURN TRUE
			ELSIF identifier = "fp" THEN
				(* frame pointer register *)
				registerNumber := IntermediateCode.FP;
				RETURN TRUE
			ELSIF (identifier[0] = 'r') OR (identifier[0] = 'h') THEN
				(* TODO: is support for hardware registers needed? *)
				(* read number *)
				position := 1;
				number := 0;
				WHILE identifier[position] # 0X DO
					number := number * 10;
					digit := ORD(identifier[position]) - ORD('0');
					IF (digit >= 0) & (digit <= 9) THEN
						number := number + INTEGER(digit)
					ELSE
						RETURN FALSE
					END;
					position := position + 1
				END;
				IF identifier[0] = 'r' THEN
					(* virtual register *)
					IF number < 1 THEN
						RETURN FALSE
					ELSE
						registerNumber := number;
						RETURN TRUE
					END
				ELSIF identifier[0] = 'h' THEN
					(* hardware register *)
					IF number < 0 THEN 
						RETURN FALSE					
					ELSE
						registerNumber := IntermediateCode.HwRegister - number;
						RETURN TRUE
					END
				END				
			ELSE
				RETURN FALSE
			END
		END RegisterNumberFromIdentifier;

		PROCEDURE TypeFromIdentifier(VAR type: IntermediateCode.Type; identifier: Scanner.StringType): BOOLEAN;
		VAR
			sizeInBits: INTEGER;
			form: SHORTINT;
			digit, position: LONGINT;
		BEGIN
			(* read form *)
			IF identifier[0] = 's' THEN
				form := IntermediateCode.SignedInteger
			ELSIF identifier[0] = 'u' THEN
				form := IntermediateCode.UnsignedInteger
			ELSIF identifier[0] = 'f' THEN
				form := IntermediateCode.Float
			ELSE
				RETURN FALSE
			END;
			
			(* read bit size *)
			position := 1;
			sizeInBits := 0;
			WHILE identifier[position] # 0X DO
				sizeInBits := sizeInBits * 10;
				digit := ORD(identifier[position]) - ORD('0');
				IF (digit >= 0) & (digit <= 9) THEN
					sizeInBits := sizeInBits + INTEGER(digit)
				ELSE
					RETURN FALSE
				END;
				position := position + 1		
			END;
			
			IF (sizeInBits < 1) OR (sizeInBits > 64) THEN RETURN FALSE END;
			IntermediateCode.InitType(type, form, sizeInBits);

			RETURN TRUE
		END TypeFromIdentifier;
		
		(*
		(* whether an symbol name is prefixed with a certain module name*)
		PROCEDURE HasModulePrefix(moduleName, symbolName: Scanner.StringType): BOOLEAN;
		VAR
			localPrefix: Scanner.StringType;
		BEGIN		
			localPrefix := moduleName;
			Strings.Append(localPrefix, ".");
			RETURN Strings.StartsWith(localPrefix, 0, symbolName)
		END HasModulePrefix;
		*)

		(** assemble the content of an intermediate code section
		note: 'sectionList' is the list where referenced sections are found/to be created
		**)
		PROCEDURE ParseSectionContent*(scanner: Scanner.AssemblerScanner; assemblySection: IntermediateCode.Section; sectionList: Sections.SectionList);
		VAR
			operands: ARRAY 3 OF IntermediateCode.Operand;
			operand: IntermediateCode.Operand;
			instruction: IntermediateCode.Instruction;
			symbolSection: IntermediateCode.Section;
			type: IntermediateCode.Type;
			identifier, message, temp: Scanner.StringType;
			pos, lineNumber, specifiedLineNumber, operandNumber, registerNumber, symbolOffset, someInteger: LONGINT;
			lastWasIdentifier, hasTypeDescriptor, isMemoryOperand, isNegated: BOOLEAN;
			someHugeint: HUGEINT;
			someLongreal: LONGREAL;
			opCode: SHORTINT;					
		BEGIN
			IF ParserTrace THEN D.Ln; D.String(">>> AssembleSectionContent"); D.Ln END;
			SELF.scanner := scanner;
			IgnoreNewLines;
			lineNumber := 0;
			WHILE ~error & (symbol.token # Scanner.Period) & (symbol.token # Scanner.EndOfText) DO
				(* consume optional line number *)
				IF ThisToken(Scanner.Number) THEN
					specifiedLineNumber := symbol.integer;
					pos := symbol.start;
					IF ExpectToken(Scanner.Colon) THEN
						IF specifiedLineNumber # lineNumber THEN
							message := "invalid code line number (";
							Strings.IntToStr(specifiedLineNumber, temp); Strings.Append(message, temp);
							Strings.Append(message, " instead of ");
							Strings.IntToStr(lineNumber, temp); Strings.Append(message, temp);
							Strings.Append(message, ")");
							Error(pos, message)
						END
					END
				END;
				IF ~error & ExpectAnyIdentifier(pos, identifier) THEN
					(* TODO: detect labels of the form << labelName: >> *)
					opCode := IntermediateCode.FindMnemonic(identifier);
					IF opCode = IntermediateCode.None THEN
						Error(pos, "unknown mnemonic")
					ELSE
						IF ParserTrace THEN D.String(">>> read instruction"); D.Ln END;
						(* consume all operands *)
						IntermediateCode.InitType(type, IntermediateCode.SignedInteger, 32); (* defaults *)
						IntermediateCode.InitOperand(operands[0]);
						IntermediateCode.InitOperand(operands[1]);
						IntermediateCode.InitOperand(operands[2]);	
						operandNumber := 0;
						IF ~ThisToken(Scanner.Ln) & ~ThisToken(Scanner.EndOfText) THEN
							REPEAT
								IF operandNumber > 2 THEN
									Error(symbol.start, "too many operands")
								ELSE
									(* consume a single operand *)
									IF ParserTrace THEN D.String(">>> read operand #"); D.Int(operandNumber, 0); D.Ln END;
									
									(* defaults *)
									hasTypeDescriptor := FALSE;
									isMemoryOperand := FALSE;
									
									(* consume optional type description *)
									lastWasIdentifier := GetIdentifier(pos, identifier);
									IF lastWasIdentifier & TypeFromIdentifier(type, identifier) THEN
										hasTypeDescriptor := TRUE;
										lastWasIdentifier := GetIdentifier(pos, identifier)
									END;
									
									IF ~lastWasIdentifier THEN
										isMemoryOperand := ThisToken(Scanner.LeftBracket);
										lastWasIdentifier := GetIdentifier(pos, identifier)
									END;	
								
									IF lastWasIdentifier THEN
										IF RegisterNumberFromIdentifier(registerNumber, identifier) THEN
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
											
											IF ParserTrace THEN D.String(">>> symbol detected"); D.Ln END;
											symbolSection := IntermediateCode.NewSection(sectionList, Sections.UnknownSection, identifier, NIL, TRUE);
											
											IntermediateCode.InitAddress(operand, type, symbolSection, symbolOffset)
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
												IF isNegated THEN
													someInteger := -symbol.integer
												ELSE
													someInteger := symbol.integer
												END;
												IF ~hasTypeDescriptor THEN
													(* if no type description was included: use number type *)
													IntermediateCode.InitNumber(operand, someInteger)
												ELSIF type.form = IntermediateCode.Float THEN
													ASSERT(hasTypeDescriptor);
													IntermediateCode.InitFloatImmediate(operand, type, REAL(someInteger))
												ELSE
													ASSERT(hasTypeDescriptor & (type.form IN IntermediateCode.Integer));
													IntermediateCode.InitImmediate(operand, type, someInteger)
												END
											| Scanner.Hugeint:
												IF isNegated THEN
													someHugeint := - symbol.hugeint
												ELSE
													someHugeint := symbol.hugeint
												END;
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
												IF isNegated THEN
													someLongreal := -symbol.real
												ELSE
													someLongreal := symbol.real
												END;
												(* if no type description was included: use default float type *)
												IF ~hasTypeDescriptor THEN
													IntermediateCode.InitType(type, IntermediateCode.Float, 32)
												END;
												IF type.form IN IntermediateCode.Integer THEN
													Error(symbol.start, "floating point immediate value not applicable")
												ELSE
													IntermediateCode.InitFloatImmediate(operand, type, someLongreal)
												END
											ELSE HALT(100)
											END
										ELSE
											Error(pos, "invalid operand")
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
									
									IF isMemoryOperand & ExpectToken(Scanner.RightBracket) THEN
										IntermediateCode.InitMemory(operand, type, operand, 0) (* TODO: add offset *)
									END;
									
									IF ~error THEN
										IF ParserTrace THEN IntermediateCode.DumpOperand(D.Log, operand); D.Ln; END;
										operands[operandNumber] := operand;
										operandNumber := operandNumber + 1
									END
								END;
							UNTIL error OR ~ThisToken(Scanner.Comma);
							IF ~error & ExpectLineDelimiter() THEN END
						END;
						
						(* create and emit instruction into assembly section *)
						IntermediateCode.InitInstruction(instruction, opCode, operands[0], operands[1], operands[2]);
						assemblySection.Emit(instruction);
						
						lineNumber := lineNumber + 1
					END
				END;
				IgnoreNewLines
			END
		END ParseSectionContent;

		(** **)
		PROCEDURE ParseModuleContent*(scanner: Scanner.AssemblerScanner; sectionList: Sections.SectionList; VAR moduleName, platformName: SyntaxTree.String; VAR imports: Sections.NameList): BOOLEAN;
		VAR
			pos: LONGINT;
			identifier: Scanner.StringType;
			afterModuleDirective, afterImportsDirective, afterFirstSection: BOOLEAN;
			sectionType: SHORTINT;
			assemblySection: IntermediateCode.Section;
			isNegated: BOOLEAN;
		BEGIN
			IF ParserTrace THEN D.Ln; D.String(">>> ParseModuleContent"); D.Ln END;

			moduleName := "";
			platformName := "";
			NEW(imports);

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
							platformName := identifier
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
						IF identifier = "code" THEN
							sectionType := Sections.CodeSection
						ELSIF identifier = "const" THEN
							sectionType := Sections.ConstSection
						ELSIF identifier = "var" THEN
							sectionType := Sections.VarSection
						ELSIF identifier = "bodycode" THEN
							sectionType := Sections.BodyCodeSection
						ELSIF identifier = "inlinecode" THEN
							sectionType := Sections.InlineCodeSection
						ELSIF identifier = "initcode" THEN
							sectionType := Sections.InitCodeSection
						ELSIF identifier = "initcode2" THEN
							sectionType := Sections.InitCode2Section
						ELSE
							Error(pos, "invalid directive")
						END;
						
						IF ~error & ~afterModuleDirective THEN
							Error(pos, "module directive expected first")
						END;
						
						IF ~error THEN
							IF ExpectAnyIdentifier(pos, identifier) THEN
								(* old code:
								IF HasModulePrefix(result.moduleName, identifier) THEN
									assemblySection := IntermediateCode.NewSection(result.sections, sectionType, identifier, NIL, TRUE)
								ELSE
									assemblySection := IntermediateCode.NewSection(result.importedSymbols, sectionType, identifier, NIL, TRUE)
								END;
								*)
								assemblySection := IntermediateCode.NewSection(sectionList, sectionType, identifier, NIL, TRUE);
								
								(* TODO: set default unit size for the platform *)
								
								(* consume optional section properties *)
								WHILE ~error & (symbol.token # Scanner.EndOfText) & (symbol.token # Scanner.Ln) DO
									(* consume optional offset specification *)
									
									(* offset *)
									IF ThisIdentifier("offset") & ExpectToken(Scanner.Equal) THEN
										isNegated := ThisToken(Scanner.Minus);
										IF ExpectToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
											IF isNegated THEN
												assemblySection.SetOffset(-symbol.integer)
											ELSE
												assemblySection.SetOffset(symbol.integer)
											END
										ELSE
											Error(symbol.start, "invalid offset")
										END

									(* fingerprint *)
									ELSIF ThisIdentifier("fingerprint") & ExpectToken(Scanner.Equal) THEN
										isNegated := ThisToken(Scanner.Minus);
										IF ExpectToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
											IF isNegated THEN
												assemblySection.SetFingerprint(-symbol.integer)
											ELSE
												assemblySection.SetFingerprint(symbol.integer)
											END
										ELSE
											Error(symbol.start, "invalid fingerprint")
										END
									
									(* alignment *)
									ELSIF ThisIdentifier("aligned") & ExpectToken(Scanner.Equal) THEN
										IF ExpectToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
											assemblySection.SetPositionOrAlignment(FALSE, symbol.integer)
										ELSE
											Error(symbol.start, "invalid alignment")
										END
									
									(* fixed position *)
									ELSIF ThisIdentifier("fixed") & ExpectToken(Scanner.Equal) THEN
										IF ExpectToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
											assemblySection.SetPositionOrAlignment(TRUE, symbol.integer)
										ELSE
											Error(symbol.start, "invalid fixed postion")
										END
									
									(* unit size *)
									ELSIF ThisIdentifier("unit") & ExpectToken(Scanner.Equal) THEN
										IF ExpectToken(Scanner.Number) & (symbol.numberType = Scanner.Integer) THEN
											(* overwrite default unit size *)
											assemblySection.SetBitsPerUnit(symbol.integer)
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
									ParseSectionContent(scanner, assemblySection, sectionList);
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
			imports: Sections.NameList;
		BEGIN
			NEW(result, NIL, NIL); (* note: there is no syntax tree module and system object *)
			IF ParseModuleContent(scanner, result.sections, moduleName, platformName, imports) THEN
				result.SetModuleName(moduleName);
				result.SetPlatformName(platformName);
				result.SetImports(imports);
				
				IF ParserTrace THEN
					D.String("++++++++++ PARSED MODULE '"); D.String(result.moduleName); D.String("' ++++++++++"); D.Ln;					
					result.Dump(D.Log)
				END
			ELSE
				result := NIL
			END
		END ParseModule;
	END IntermediateCodeParser;

	(* collect all sections from a module given by its name
		- check if module has already been incorporated (to avoid multiple imports)
		- open and parse the corresponding IR file
		- recursively do the same for all modules that are imported
		- get the name of the platform that the code in the file is targeting
		- return whether the operation was successful
	*)
	PROCEDURE CollectSectionsOfModule(
			moduleName: SyntaxTree.String;
			diagnostics: Diagnostics.StreamDiagnostics;
			cumulativeSectionList: Sections.SectionList;
			incorporatedModules: Sections.NameList;
			VAR platformName: SyntaxTree.String): BOOLEAN;
	VAR
		error: BOOLEAN;
		i: LONGINT;
		reader: Streams.Reader;
		filename, dummyString: SyntaxTree.String;
		assemblerScanner: Scanner.AssemblerScanner;
		intermediateCodeParser: IntermediateCodeParser;
		imports: Sections.NameList;
	BEGIN	
		IF Trace THEN D.String(">>> collect sections from module "); D.String(moduleName); D.Ln END;
		
		(* check if the module has already been incorporated *)		
		IF incorporatedModules.ContainsName(moduleName) THEN				
			IF Trace THEN D.String(">>> module "); D.String(moduleName); D.String(" has already been incorporated"); D.Ln END;
			RETURN TRUE
		ELSE
			incorporatedModules.AddName(moduleName);
			
			(* determine filename of corresponding IR file *)
			filename := moduleName; Files.JoinExtension(filename, "ir", filename);

			(* open IR file *)
			reader := Basic.GetFileReader(filename);
			IF reader = NIL THEN
				diagnostics.Error(filename, Diagnostics.Invalid, Diagnostics.Invalid, "failed to open");
				RETURN FALSE
			ELSE
				IF Trace THEN D.String(">>> IR file successfully opened: "); D.String(filename); D.Ln END;
				
				(* parse IR file *)
				NEW(assemblerScanner, filename, reader, 0, diagnostics);
				NEW(intermediateCodeParser, diagnostics);
				
				IF intermediateCodeParser.ParseModuleContent(assemblerScanner, cumulativeSectionList, dummyString, platformName, imports) THEN
					IF Trace THEN D.String(">>> IR file successfully parsed: "); D.String(filename); D.Ln END;
					
					(* parsing has been successful: go through all imports and collect their sections *)
					error := FALSE;					
					FOR i := 0 TO imports.Length() - 1 DO					
						IF ~CollectSectionsOfModule(imports.GetName(i), diagnostics, cumulativeSectionList, incorporatedModules, dummyString) THEN RETURN FALSE END
					END;
					RETURN TRUE
				ELSE
					diagnostics.Error(filename, Diagnostics.Invalid, Diagnostics.Invalid, "IR file could not be parsed");
					RETURN FALSE
				END
			END
		END
	END CollectSectionsOfModule;
	
	(** mark a section as reachable and do the same recursively for all referenced sections **)
	PROCEDURE MarkAsReachable(section: Sections.Section);
	VAR
		intermediateCodeSection: IntermediateCode.Section;
		i: LONGINT;
	BEGIN
		IF ~section.isReachable THEN
			IF Trace THEN D.String(">>> the section "); D.String(section.name); D.String(" is marked as reachable"); D.Ln END;
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

	PROCEDURE Assemblink*(
			rootModuleName: SyntaxTree.String;
			diagnostics: Diagnostics.StreamDiagnostics;
			log: Streams.Writer;
			flags: SET;
			semanticChecker: SemanticChecker.Checker;
			backend: Backend.Backend;
			objectFileFormat: Formats.ObjectFileFormat);
	VAR
		allSections, fixedDataSectionsOfCell, flexibleDataSectionsOfCell, codeSectionsOfCell, allSectionsOfCell: Sections.SectionList;
		section, flexibleDataSection, fixedDataSection: Sections.Section;
		platformName, tempString: SyntaxTree.String;
		importList: Sections.NameList;
		ICModuleOfCell: Sections.Module;
		system: Global.System;
		binaryModuleOfCell: Formats.GeneratedModule;
		arrangementRestrictions: POINTER TO ARRAY OF ArrangementRestriction;
		i, j, fixedDataSectionIndex, flexibleDataSectionIndex, currentAddress, startAddress, endAddress, nextOccupiedAddress: LONGINT;
		done: BOOLEAN;
		
		PROCEDURE ProcessCell(cellName: SyntaxTree.String; cellInitializationSection: Sections.Section);		
		BEGIN
			IF Trace THEN D.String(">>>>>> processing active cell '"); D.String(cellName); D.String("':"); D.Ln END;						
			
			(* TODO: use this?
			tempString := "processing active cell "; Strings.Append(tempString, cellName);
			diagnostics.Information(rootModuleName, Diagnostics.Invalid, Diagnostics.Invalid, tempString);
			*)
			
			(* for all sections:
				- restore the original arrangment restrictions
				- mark them as unreachable
				- remove any previously generated binary code
			*)
			FOR j := 0 TO allSections.Length() - 1 DO
				section := allSections.GetSection(j);
				section.SetPositionOrAlignment(arrangementRestrictions[j].fixed, arrangementRestrictions[j].positionOrAlignment);
				section.SetReachability(FALSE);
				ASSERT(section IS IntermediateCode.Section); section(IntermediateCode.Section).SetResolved(NIL)
			END;
			
			MarkAsReachable(cellInitializationSection); (* mark the cell initialization section as reachable *)
			
			(* create lists of sections for different categories *)
			NEW(fixedDataSectionsOfCell);
			NEW(flexibleDataSectionsOfCell);
			NEW(codeSectionsOfCell);
			
			(* go through all reachable sections, and put them into the list of the corresponding category *)
			FOR j := 0 TO allSections.Length() - 1 DO
				section := allSections.GetSection(j);
				IF section.isReachable THEN
					CASE section.type OF
					| Sections.ConstSection, Sections.VarSection:
						IF section.fixed THEN
							fixedDataSectionsOfCell.AddSection(section)
						ELSE
							flexibleDataSectionsOfCell.AddSection(section)
						END
					| Sections.InitCode2Section:
						ASSERT(section = cellInitializationSection)
					ELSE
						codeSectionsOfCell.AddSection(section)
					END
				END
			END;
			
			(*
			IF Trace THEN
				D.Ln;
				D.String("++++++++++ FIXED-DATA SECTIONS OF THE CELL '"); D.String(cellName); D.String("' ++++++++++"); D.Ln;
				fixedDataSectionsOfCell.Dump(D.Log);

				D.Ln;
				D.String("++++++++++ FLEXIBLE-DATA SECTIONS OF THE CELL '"); D.String(cellName); D.String("' ++++++++++"); D.Ln;
				flexibleDataSectionsOfCell.Dump(D.Log);

				D.Ln;
				D.String("++++++++++ CODE SECTIONS OF THE CELL '"); D.String(cellName); D.String("' ++++++++++"); D.Ln;
				codeSectionsOfCell.Dump(D.Log)
			END;
			*)
			
			(* combine the sections from the different lists into a single one.
			arrange the sections such that the fixed-positions and alignments are respected
			*)
			NEW(allSectionsOfCell);
			currentAddress := 0;
			flexibleDataSectionIndex := 0;
			(* go through all fixed data sections of the cell *)
			FOR fixedDataSectionIndex := 0 TO fixedDataSectionsOfCell.Length() DO (* note: the index may be out-of-bounds! *)
				IF fixedDataSectionIndex < fixedDataSectionsOfCell.Length() THEN
					fixedDataSection := fixedDataSectionsOfCell.GetSection(fixedDataSectionIndex);
					ASSERT(fixedDataSection.fixed);							
					nextOccupiedAddress := fixedDataSection.positionOrAlignment
				ELSE
					(* there is no more fixed data section *)
					nextOccupiedAddress := MAX(LONGINT)
				END;
				
				done := FALSE;
				WHILE ~done DO
					IF flexibleDataSectionIndex < flexibleDataSectionsOfCell.Length() THEN
						flexibleDataSection := flexibleDataSectionsOfCell.GetSection(flexibleDataSectionIndex);
						
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
							flexibleDataSection.SetPositionOrAlignment(TRUE, startAddress);
							allSectionsOfCell.AddSection(flexibleDataSection);						
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
									
				IF fixedDataSectionIndex < fixedDataSectionsOfCell.Length() THEN
					allSectionsOfCell.AddSection(fixedDataSection);
					ASSERT(fixedDataSection.GetSize() # Sections.UnknownSize);
					currentAddress := fixedDataSection.positionOrAlignment + fixedDataSection.GetSize()
				END
			END;
			
			(* add cell initialization section *)
			allSectionsOfCell.AddSection(cellInitializationSection);
			
			(* add code sections *)
			FOR j := 0 TO codeSectionsOfCell.Length() - 1 DO
				allSectionsOfCell.AddSection(codeSectionsOfCell.GetSection(j));
			END;
			
			(* create the combined intermediate code module *)
			NEW(ICModuleOfCell, NIL, backend.GetSystem()); (* note: there is no syntax tree node *)
			ICModuleOfCell.SetModuleName(cellName);
			ICModuleOfCell.SetPlatformName(platformName);
			ICModuleOfCell.SetSections(allSectionsOfCell);
			
			IF Trace THEN
				D.Ln;
				D.String("++++++++++ FINAL INTERMEDIATE CODE MODULE FOR CELL '"); D.String(cellName); D.String("' ++++++++++"); D.Ln;
				ICModuleOfCell.Dump(D.Log);
				D.Ln
			END;
			
			(*  apply the backend on the list of sections *)						
			binaryModuleOfCell := backend.ProcessIntermediateCodeModule(ICModuleOfCell);
			IF backend.error OR (binaryModuleOfCell # NIL) THEN
				diagnostics.Error(ICModuleOfCell.moduleName, Diagnostics.Invalid, Diagnostics.Invalid, "binary code could not be generated (backend error)");
			ELSE
				(* write the generated code to a generic object file *)
				ASSERT(objectFileFormat # NIL) ;
				objectFileFormat.Initialize(diagnostics);
				IF objectFileFormat.Export(binaryModuleOfCell, NIL) THEN
					(* TODO: respect 'Silent' flag? *)
					diagnostics.Information(ICModuleOfCell.moduleName, Diagnostics.Invalid, Diagnostics.Invalid, "successfully assembled and linked.");
				ELSE							
					diagnostics.Error(ICModuleOfCell.moduleName, Diagnostics.Invalid, Diagnostics.Invalid, "object file could not be written");
				END
			END
		END ProcessCell;
		
	BEGIN
		NEW(allSections);
		NEW(importList);

		(* collect all sections contained in the module and its imports *)
		IF CollectSectionsOfModule(rootModuleName, diagnostics, allSections, importList, platformName) THEN
		
			(* determine backend to be used *)
			IF platformName # "" THEN
				(* use the backend specified by in the IR file *)
				backend := Backend.GetBackendByName(platformName);
				IF backend = NIL THEN				
					diagnostics.Error(rootModuleName, Diagnostics.Invalid, Diagnostics.Invalid, "backend specified in intermediate code file could not be installed");
				END
			ELSE
				ASSERT(backend # NIL)
			END;
			IF Trace THEN
				D.Ln;
				D.String(">>> backend to be used: ");
				backend.GetDescription(tempString); D.String(tempString);
				D.Ln
			END;
		
			IF backend # NIL THEN
				system := backend.GetSystem();
				IF Trace THEN
					D.String(">>> platform unit size in bits: "); D.Int(system.dataUnit, 0); D.Ln;
					D.Ln
				END;
				
				(* go through all sections that have unkown unit sizes and set the unit size (in bits) of the platform *)
				FOR i := 0 TO allSections.Length() - 1 DO
					section := allSections.GetSection(i);					
					IF section.bitsPerUnit = Sections.UnknownSize THEN
						section.SetBitsPerUnit(system.dataUnit)
					END
				END;
				
				(* sort all sections *)
				allSections.Sort(CombinedSectionComparisonFunction);
				
				IF Trace THEN
					D.String("++++++++++ SORTED CUMULATIVE SECTION LIST ++++++++++"); D.Ln;
					allSections.Dump(D.Log);
					D.Ln
				END;
				
				(* store the original arrangment restrictions of the sections *)
				NEW(arrangementRestrictions, allSections.Length());
				FOR i := 0 TO allSections.Length() - 1 DO
					section := allSections.GetSection(i);
					arrangementRestrictions[i].fixed := section.fixed;
					arrangementRestrictions[i].positionOrAlignment := section.positionOrAlignment
				END;
				
				(* initialize backend *)
				backend.Initialize(diagnostics, log, flags, semanticChecker, system, NIL);

				(* go through all cell initialization sections (i.e. 'initcode2'-sections) *)
				FOR i := 0 TO allSections.Length() - 1 DO
					section := allSections.GetSection(i);
					IF section.type = Sections.InitCode2Section THEN
						ProcessCell(section.name, section)						
					END
				END
			END
		ELSE
			IF Trace THEN D.String(">>> AN ERROR OCCURED"); D.Ln END
		END
	END Assemblink;
	
	(** whether a section should appear before another one in an assembly
		- 1st priority: when sections have fixed positions, the ones with smaller addresses come first
		- 2nd priority: smaller sections come first
	**)
	PROCEDURE CombinedSectionComparisonFunction(leftObject, rightObject: ANY): BOOLEAN;	
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
	END CombinedSectionComparisonFunction;

END FoxIntermediateCodeAssembler.

FoxAssembler.TestScanner

SystemTools.Free FoxIntermediateCodeAssembler ~

FoxAssembler.TestScanner
FoxIntermediateCodeAssembler.Test
;---------------- intermediate code -----------------
.module BitSets

.platform XYZ

.imports SYSTEM

.const BitSets.@moduleSelf offset=3
	 0: data u32 0

.const BitSets.BitSet offset=0
	 0: data u32 0

.code BitSets.BitSet.InitBitSet offset=0
	 0: enter  0,  0
	 1: mov u32 r1, u32 [fp+8]
	 2: mov s32 [r1], s32 [fp+12]
	 3: push s32 [fp+12]
	 4: mov u32 r2, u32 [fp+8]
	 5: add u32 r3, u32 [r2-4], u32 -88
	 6: push u32 r2
	 7: call u32 [r3],  8
	 8: leave  0
	 9: exit  8

.code BitSets.BitSet.Zero offset=0
	 0: enter  0,  8
	 1: mov s32 [fp-4], s32 0
	 2: mov u32 r1, u32 [fp+8]
	 3: mov u32 r2, u32 [r1+4]
	 4: conv s32 r3, u32 [r2+12]
	 5: sub s32 r3, s32 r3, s32 1
	 6: mov s32 [fp-8], s32 r3
	 7: brlt u32 BitSets.BitSet.Zero:21, s32 [fp-8], s32 [fp-4]
	 8: br u32 BitSets.BitSet.Zero:9
	 9: conv u32 r4, s32 [fp-4]
	10: mov u32 r5, u32 r4
	11: mov u32 r6, u32 [fp+8]
	12: mov u32 r7, u32 [r6+4]
	13: brlt u32 BitSets.BitSet.Zero:15, u32 r4, u32 [r7+12]
	14: trap  7
	15: mul u32 r5, u32 r5, u32 4
	16: add u32 r5, u32 r5, u32 r7+16
	17: mov u32 [r5], u32 0
	18: add s32 r8, s32 [fp-4], s32 1
	19: mov s32 [fp-4], s32 r8
	20: br u32 BitSets.BitSet.Zero:7
	21: leave  0
	22: exit  4

.code BitSets.BitSet.Resize offset=0
	 0: enter  0,  12
	 1: brlt u32 BitSets.BitSet.Resize:3, s32 [fp+12], s32 0
	 2: br u32 BitSets.BitSet.Resize:4
	 3: trap  8
	 4: mov u32 r1, u32 [fp+8]
	 5: mov s32 [r1], s32 [fp+12]
	 6: sub s32 r2, s32 [fp+12], s32 1
	 7: brlt u32 BitSets.BitSet.Resize:10, s32 r2, s32 0
	 8: mov s32 r2, s32 r2
	 9: br u32 BitSets.BitSet.Resize:11
	10: mov s32 r2, s32 0, s32 r2
	11: shr s32 r2, s32 r2, s32 5
	12: add s32 r2, s32 r2, s32 1
	13: mov s32 [fp+12], s32 r2
	14: mov u32 r3, u32 [fp+8]
	15: breq u32 BitSets.BitSet.Resize:35, u32 [r3+4], u32 0
	16: br u32 BitSets.BitSet.Resize:17
	17: mov u32 r4, u32 [fp+8]
	18: mov u32 r5, u32 [r4+4]
	19: conv s32 r6, u32 [r5+12]
	20: brlt u32 BitSets.BitSet.Resize:25, s32 r6, s32 [fp+12]
	21: br u32 BitSets.BitSet.Resize:22
	22: leave  0
	23: exit  8
	24: br u32 BitSets.BitSet.Resize:25
	25: mov u32 r7, u32 [fp+8]
	26: mov u32 r8, u32 [r7+4]
	27: conv s32 r9, u32 [r8+12]
	28: shl s32 r9, s32 r9, s32 1
	29: brlt u32 BitSets.BitSet.Resize:32, s32 [fp+12], s32 r9
	30: mov s32 r9, s32 [fp+12]
	31: br u32 BitSets.BitSet.Resize:33
	32: mov s32 r9, s32 r9, s32 r9
	33: mov s32 [fp+12], s32 r9
	34: br u32 BitSets.BitSet.Resize:35
	35: brge u32 BitSets.BitSet.Resize:37, s32 [fp+12], s32 0
	36: trap  9
	37: push s32 [fp+12]
	38: mov s32 r10, s32 [fp+12]
	39: conv u32 r10, s32 r10
	40: mul u32 r10, u32 r10, u32 4
	41: add u32 r10, u32 r10, u32 16
	42: push u32 fp-4
	43: push u32 fp-4
	44: push u32 r10
	45: push u8 0
	46: call u32 @SystemCall2:0,  0
	47: pop u32 r11
	48: mov u32 r12, u32 [r11]
	49: breq u32 BitSets.BitSet.Resize:53, u32 r12, u32 0
	50: pop u32 r13
	51: mov u32 [r12+12], u32 r13
	52: br u32 BitSets.BitSet.Resize:54
	53: add u32 sp, u32 sp, u32 4
	54: mov u32 r14, u32 [fp+8]
	55: breq u32 BitSets.BitSet.Resize:85, u32 [r14+4], u32 0
	56: br u32 BitSets.BitSet.Resize:57
	57: mov s32 [fp-8], s32 0
	58: mov u32 r15, u32 [fp+8]
	59: mov u32 r16, u32 [r15+4]
	60: conv s32 r17, u32 [r16+12]
	61: sub s32 r17, s32 r17, s32 1
	62: mov s32 [fp-12], s32 r17
	63: brlt u32 BitSets.BitSet.Resize:84, s32 [fp-12], s32 [fp-8]
	64: br u32 BitSets.BitSet.Resize:65
	65: conv u32 r18, s32 [fp-8]
	66: mov u32 r19, u32 r18
	67: mov u32 r20, u32 [fp+8]
	68: mov u32 r21, u32 [r20+4]
	69: brlt u32 BitSets.BitSet.Resize:71, u32 r18, u32 [r21+12]
	70: trap  7
	71: mul u32 r19, u32 r19, u32 4
	72: add u32 r19, u32 r19, u32 r21+16
	73: conv u32 r22, s32 [fp-8]
	74: mov u32 r23, u32 r22
	75: mov u32 r24, u32 [fp-4]
	76: brlt u32 BitSets.BitSet.Resize:78, u32 r22, u32 [r24+12]
	77: trap  7
	78: mul u32 r23, u32 r23, u32 4
	79: add u32 r23, u32 r23, u32 r24+16
	80: mov u32 [r23], u32 [r19]
	81: add s32 r25, s32 [fp-8], s32 1
	82: mov s32 [fp-8], s32 r25
	83: br u32 BitSets.BitSet.Resize:63
	84: br u32 BitSets.BitSet.Resize:85
	85: mov u32 r26, u32 [fp+8]
	86: mov u32 [r26+4], u32 [fp-4]
	87: leave  0
	88: exit  8

.code BitSets.BitSet.GetSize offset=0
	 0: enter  0,  0
	 1: mov u32 r1, u32 [fp+8]
	 2: return s32 [r1]
	 3: leave  0
	 4: exit  4
	 5: trap  3
	 
	 
	 
