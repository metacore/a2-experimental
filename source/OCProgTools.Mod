MODULE OCProgTools;   (**  AUTHOR "fof"; PURPOSE "Oberon Compiler: Programming Tools";  **)
(* (c) fof ETH Zürich, 2009 *)

IMPORT WMUtilities,Options,Commands,Files,Strings;

	PROCEDURE Enum*(context: Commands.Context);
	VAR w: WMUtilities.WindowWriter; nr: LONGINT; options: Options.Options; export,incremental,hex: BOOLEAN; start: LONGINT;
		name,oldname: ARRAY 256 OF CHAR; lf: LONGINT;

		(** get next symbol **)
		PROCEDURE GetNextSymbol(VAR s: ARRAY OF CHAR ): BOOLEAN;
		CONST EOT=0X;
		VAR ch: CHAR; i: LONGINT;

			PROCEDURE SkipBlanks;
			BEGIN
				WHILE ch <= " " DO  (*ignore control characters*)
					IF ch = EOT THEN RETURN
					ELSE ch := context.arg.Get();
					END
				END;
			END SkipBlanks;

			PROCEDURE Comment;
			VAR i: LONGINT;
			BEGIN
				i := 0;
				LOOP
					IF (ch = EOT) OR (i>256) THEN EXIT
					ELSIF ch = "(" THEN
						w.Char(ch); ch := context.arg.Get();
						IF ch = "*" THEN
							w.Char(ch); ch := context.arg.Get();
							Comment()
						END;
					ELSIF ch = "*" THEN
						w.Char(ch);
						ch := context.arg.Get();
						IF ch = ")" THEN
							w.Char(ch); ch := context.arg.Get();
							EXIT
						END;
					ELSE w.Char(ch); ch := context.arg.Get();  INC(i);
					END;
				END;
			END Comment;


		BEGIN
			ch := context.arg.Get();
			SkipBlanks;  i := 0;
			LOOP
				IF (ch <= " ") OR (ch = EOT) OR (i>128) THEN EXIT
				ELSIF ch = "(" THEN
					ch := context.arg.Get();
					IF ch = "*" THEN
						ch := context.arg.Get();
						IF (nr-start) MOD lf # 0 (* avoid two linefeeds *)  THEN w.Ln END;
						w.SetFontColor(SHORT(808080FFH));
						w.String("(*");
						Comment();
						w.SetFontColor(000000FFH);
						w.Ln; start := nr;
						SkipBlanks;
					ELSE s[i] := "("; INC(i);
					END;
				ELSE s[i] := ch; INC(i); ch := context.arg.Get();
				END;
			END;
			s[i] := 0X;
			RETURN (i>0);
		END GetNextSymbol;


	BEGIN
		NEW(options);
		options.Add("e", "export", Options.Flag);
		options.Add("i", "incremental", Options.Flag);
		options.Add("s", "start", Options.Integer);
		options.Add("h","hex",Options.Flag);
		options.Add("l","linefeed",Options.Integer);

		IF options.Parse(context.arg,context.error) THEN
			NEW(w,"ProgTools",600,400,TRUE);
			w.SetFontSize(12);
			IF ~options.GetInteger("s",start) THEN start := 0 END;
			export := options.GetFlag("e");
			incremental := options.GetFlag("i");
			hex := options.GetFlag("h");
			IF ~options.GetInteger("l",lf) THEN lf := MAX(LONGINT) END;
			nr := start;
			WHILE GetNextSymbol(name) DO
				w.String(name);
				IF export THEN w.String("*"); END;
				w.String("= ");
				IF incremental THEN
					IF oldname = "" THEN
						IF hex THEN w.Hex(nr,1); w.String("H");  ELSE w.Int(nr,1) END;
					ELSE w.String(oldname); w.String("+1");
					END;
				ELSE
					IF hex THEN w.Hex(nr,1); w.String("H");  ELSE w.Int(nr,1) END;
				END;
				w.String("; ");
				IF  (nr-start+1) MOD lf = 0 THEN w.Ln END;
				INC(nr);
				oldname := name;
				(* context.arg.GetString(name); *)
			END;
			w.Update;
		END;
	END Enum;

	PROCEDURE ParseAMDInstructionSet*(context: Commands.Context);
	CONST   TAB = 9X; CR = 0DX; LF = 0AX;

	TYPE
		Instruction=POINTER TO RECORD
			op1,op2,op3,opcode,target,bitwidth: ARRAY 256 OF CHAR;
			next: Instruction;
		END;

		Mnemonic= POINTER TO RECORD
			name: ARRAY 32 OF CHAR;
			firstInstruction,lastInstruction: Instruction;
			next: Mnemonic;
		END;

		Replacement = POINTER  TO RECORD
			from,to: ARRAY 256 OF CHAR;
			next: Replacement;
		END;

		TYPE Replacer= OBJECT
		VAR first,last: Replacement;

			PROCEDURE &Init;
			BEGIN first := NIL; last := NIL;
			END Init;

			PROCEDURE Add(CONST src,dest: ARRAY OF CHAR);
			VAR r: Replacement;
			BEGIN
				NEW(r); COPY(src,r.from); COPY(dest,r.to);
				IF first = NIL THEN first := r; last := r ELSE last.next := r; last := r END;
			END Add;

			PROCEDURE Do(VAR src: ARRAY OF CHAR);
			VAR pos: LONGINT; r: Replacement;
			BEGIN
				r := first;
				WHILE r # NIL DO
					pos := Strings.Pos(r.from,src);
					IF pos # -1 THEN
						Strings.Delete(src,pos,Strings.Length(r.from));
						Strings.Insert(r.to,src,pos);
					END;
					r := r.next;
				END;
			END Do;

		END Replacer;





	VAR fileName,instr: ARRAY 256 OF CHAR; w: WMUtilities.WindowWriter; reader: Files.Reader; file: Files.File; ch: CHAR;
		line: ARRAY 1024 OF CHAR;

		firstMnemonic,prevmnemonic,mnemonic : Mnemonic;
		instruction: Instruction;

		operandReplacer: Replacer;
		cpuoptionReplacer: Replacer;
		bitwidthReplacer: Replacer;



		numberMnemonics: LONGINT;
		numberInstructions : LONGINT;
		maxMnemonicNameLength: LONGINT;
		maxOpcodeLength: LONGINT;


		PROCEDURE Priority(i: Instruction): LONGINT;
		VAR prio: LONGINT;

			PROCEDURE OP(CONST o: ARRAY OF CHAR): LONGINT;
			BEGIN
				IF o = "" THEN
					RETURN 10
				ELSIF (o = "reg8") OR (o = "reg16") OR (o="reg32") OR (o="reg64") THEN
					RETURN 5
				ELSE
					RETURN 0
				END;
			END OP;

		BEGIN
			prio := 0;
			prio := OP(i.op1) + OP(i.op2) + OP(i.op3);
			RETURN prio
		END Priority;

		PROCEDURE InsertSorted(VAR first: Instruction; this: Instruction);
		VAR temp: Instruction;
		BEGIN
			IF (first = NIL) OR (Priority(this)>Priority(first)) THEN
				this.next := first;
				first := this;
			ELSE
				temp := first;
				WHILE (temp.next # NIL) & (Priority(temp.next) >= Priority(this)) DO
					temp := temp.next;
				END;
				this.next := temp.next;
				temp.next := this;
			END;
		END InsertSorted;

		PROCEDURE SortInstructions(VAR first: Instruction);
		VAR temp,next,newfirst: Instruction;
		BEGIN
			newfirst := NIL;
			temp := first;
			WHILE temp # NIL DO
				next := temp.next;
					InsertSorted(newfirst,temp);
				temp := next;
			END;
			first := newfirst;
		END SortInstructions;

		PROCEDURE GetCh;
		BEGIN
			ch := reader.Get();
		END GetCh;

		PROCEDURE GetLine(VAR line: ARRAY OF CHAR);
		VAR i : LONGINT;
		BEGIN
			 i := 0;
			WHILE(ch # CR) & (ch # LF) & (ch # 0X) DO
				line[i] := ch; INC(i);
				GetCh();
			END;
			line[i] := 0X;
			WHILE(ch = CR) OR (ch=LF) DO
				GetCh();
			END;
		END GetLine;

			PROCEDURE Operand(CONST op: ARRAY OF CHAR);
			VAR i: LONGINT;
			BEGIN
				IF op[0] = 0X THEN w.String("none")
				ELSIF op = "1" THEN w.String("one")
				ELSIF op ="3" THEN w.String("three");
				ELSE
				i := 0;
				WHILE(op[i] # 0X) DO
					IF (op[i] # "/") & (op[i] # ":") & (op[i]# "&")  THEN
						w.Char(op[i]);
					END;
					INC(i);
				END;
				END;
			END Operand;

			PROCEDURE AppendCh(VAR s: ARRAY OF CHAR; c: CHAR);
			VAR i: LONGINT;
			BEGIN
				i := 0;
				WHILE(s[i] # 0X) DO
					INC(i);
				END;
				s[i] := c; s[i+1] := 0X;
			END AppendCh;

			PROCEDURE Append(VAR s: ARRAY OF CHAR; CONST a: ARRAY OF CHAR);
			BEGIN
				Strings.Append(s,a)
			END Append;

			PROCEDURE Follows(CONST s: ARRAY OF CHAR; VAR i: LONGINT; CONST this: ARRAY OF CHAR): BOOLEAN;
			VAR j,k: LONGINT;
			BEGIN
				j := i; k := 0;
				WHILE(s[j] # 0X)  & (this[k] # 0X) & (s[j] = this[k]) DO
					INC(j); INC(k);
				END;
				IF this[k] = 0X THEN
					i := j;
					RETURN TRUE
				ELSE
					RETURN FALSE
				END;
			END Follows;


			PROCEDURE OpCode(CONST code: ARRAY OF CHAR);
			VAR ch: CHAR; i: LONGINT;
				op: ARRAY 3 OF CHAR;
				nOp: LONGINT;
				ModRM:ARRAY 256 OF CHAR; error: BOOLEAN;
				opCodeExtension: LONGINT;
				length: LONGINT;

				PROCEDURE NextOption(VAR s: ARRAY OF CHAR);
				BEGIN
					IF s[0] # 0X THEN Append(s,",") END;
				END NextOption;

				PROCEDURE Hex(ch: CHAR): LONGINT;
				BEGIN
					IF ("0" <= ch) & (ch <= "9") THEN
						RETURN ORD(ch)-ORD("0");
					ELSIF ("A" <= ch) & (ch <= "F") THEN
						RETURN ORD(ch)-ORD("A")+10;
					ELSE error := TRUE; RETURN 0
					END;
				END Hex;


			BEGIN
				error := FALSE;
				ModRM := "";
				op[0] := 0X;
				op[1] := 0X;
				op[2] := 0X;
				opCodeExtension := -1;

				w.String('"');
				i := 0;
				nOp := 0;
				length := 0;
				REPEAT
					ch := code[i]; INC(i);
					CASE ch OF
						0X:
						|" ":
						|"0".."9","A".."F":
							INC(length,2);
							(* options should not occur between opcodes, otherwise the order seems to be important...
								the only case where an option occurs between opcodes is for PAVGUSB: /r option which does not affect any order anyway
							*)
							CASE code[i] OF
							"0".."9","A".."F":
								w.Char(ch); w.Char(code[i]);
								op[nOp] := CHR(16*Hex(ch) + Hex(code[i]));  INC(i);
							ELSE
								w.Char("0"); w.Char(ch);
								op[nOp] := CHR(Hex(ch));
							END;
							INC(nOp);
						|"/":
							ch := code[i]; INC(i);
							NextOption(ModRM);
							w.Char("/");
							CASE ch OF
							"0".."7":
								INC(length,2);
								w.Char(ch);
								Append(ModRM,"modRMExtension");
								opCodeExtension := ORD(ch)-ORD("0");
							|"r":
								INC(length);
								w.Char(ch);
								Append(ModRM,"modRMBoth");
							ELSE error := TRUE
							END;
						|"c":
							INC(length);
							ch := code[i]; INC(i);
							NextOption(ModRM);
							CASE ch OF
							"b","w","d","p": Append(ModRM,"c"); AppendCh(ModRM,ch); w.Char("c"); w.Char(ch);
							ELSE  error := TRUE
							END;
						|"i":
							INC(length);
							ch := code[i]; INC(i);
							NextOption(ModRM);
							CASE ch OF
							"b","w","d","q": Append(ModRM,"i"); AppendCh(ModRM,ch);
							w.Char("i"); w.Char(ch);
							ELSE  error := TRUE
							END;
						|"m":
							INC(length);
							NextOption(ModRM);
							IF Follows(code,i,"64") THEN
								Append(ModRM,"mem64Operand");
								w.String("m6");
							ELSIF Follows(code,i,"128") THEN
								Append(ModRM,"mem128Operand");
								w.String("m1");
							ELSE  error := TRUE
							END;
						|"+":
							INC(length);
							ch := code[i]; INC(i);
							NextOption(ModRM);
							CASE ch OF
							'i': Append(ModRM,"fpStackOperand");
								w.String("+i");
							|'o': Append(ModRM,"directMemoryOffset");
								w.String("+o");
							|'r': Append(ModRM,"r");
								ch := code[i]; INC(i);
								CASE ch OF
								'b','w','d','q': AppendCh(ModRM,ch); w.Char("r"); w.Char(ch);
								ELSE w.String(" ERROR IN "); w.String(code); w.Update; HALT(100);
								END;
							ELSE error := TRUE
							END;
					ELSE
						error := TRUE
					END
				UNTIL error OR (ch = 0X);
				IF error THEN w.String(" ERROR IN "); w.String(code); w.String("at"); w.Int(i,1); w.Update; HALT(100); END;
				w.String('"');
				INC(length);
				IF length > maxOpcodeLength THEN
					maxOpcodeLength := length;
				END;

				(*
				w.Int(nOp,1);
				w.String(",");
				w.Hex(ORD(op[0]),1); w.String("X");
				w.String(",");
				w.Hex(ORD(op[1]),1); w.String("X");
				w.String(",");
				w.Hex(ORD(op[2]),1); w.String("X");
				w.String(",{");
				w.String(ModRM);
				w.String("}");
				w.String(", ");
				w.Int(opCodeExtension,1);
				*)

			END OpCode;

			PROCEDURE Options(CONST prefix,options: ARRAY OF CHAR);
			VAR i: LONGINT; first: BOOLEAN;

			PROCEDURE NextOptions;
			BEGIN
				WHILE(options[i] = ",") DO INC(i) END;
				IF options[i] = 0X THEN RETURN END;

				IF first THEN first := FALSE ELSE w.String(",") END;

				w.String(prefix);
				WHILE (options[i] # ",") & (options[i] # 0X) DO
					w.Char(options[i]);
					INC(i);
				END;
			END NextOptions;

			BEGIN
				i := 0;
				w.String("{");first := TRUE;
				WHILE(options[i] # 0X) DO
					NextOptions()
				END;
				w.String("}");
			END Options;


		PROCEDURE ParseLine(CONST  line: ARRAY OF CHAR);
		VAR ch: CHAR; i : LONGINT;

			PROCEDURE NextSym(VAR sym: ARRAY OF CHAR);
			VAR len: LONGINT;
			BEGIN
				len := 0;
				ch:= line[i]; INC(i);
				WHILE(ch # TAB) & (ch # LF) & (ch # 0X) DO
					WHILE(ch = " ") DO 	ch:= line[i]; INC(i); END;
					sym[len] := ch; INC(len);
					ch:= line[i]; INC(i);
				END;
				sym[len] := 0X;
			END NextSym;




		BEGIN
			i := 0; ch := line[0];
			IF (ch = '"') OR (ch = ";") THEN (* comment line skipped *)
			ELSE
				NextSym(instr);
				IF instr = "" THEN
				ELSE
					mnemonic := firstMnemonic; prevmnemonic := NIL;
					WHILE(mnemonic # NIL) & (mnemonic.name < instr) DO
						prevmnemonic := mnemonic;
						mnemonic := mnemonic.next;
					END;
					IF (mnemonic = NIL) OR (mnemonic.name # instr)  THEN
						NEW(mnemonic);
						COPY(instr,mnemonic.name);

						IF prevmnemonic = NIL THEN
							mnemonic.next := firstMnemonic;
							firstMnemonic := mnemonic;
						ELSE
							mnemonic.next := prevmnemonic.next;
							prevmnemonic.next := mnemonic;
						END;
					END;

					NEW(instruction);
					IF mnemonic.lastInstruction = NIL THEN
						mnemonic.lastInstruction := instruction;
						mnemonic.firstInstruction := instruction;
					ELSE
						mnemonic.lastInstruction.next := instruction;
						mnemonic.lastInstruction := instruction;
					END;

					NextSym(instruction.op1);
					NextSym(instruction.op2);
					NextSym(instruction.op3);
					NextSym(instruction.opcode);
					NextSym(instruction.target);
					NextSym(instruction.bitwidth);

				END;
			END;


		END ParseLine;

	BEGIN
		context.arg.SkipWhitespace; context.arg.String(fileName);
		context.out.String("parsing file "); context.out.String(fileName); context.out.Ln;
		IF fileName # "" THEN

			NEW(operandReplacer);

			operandReplacer.Add ("reg/mem8", "regmem8");
			operandReplacer.Add ("reg/mem16", "regmem16");
			operandReplacer.Add ("reg/mem32", "regmem32");
			operandReplacer.Add ("reg/mem64", "regmem64");
			operandReplacer.Add ("mem14/28env", "mem");
			operandReplacer.Add ("mem16&mem16", "mem");
			operandReplacer.Add ("mem32&mem32", "mem");
			operandReplacer.Add ("mem16:16", "mem");
			operandReplacer.Add ("mem16:32", "mem");
			operandReplacer.Add ("mem16:64", "mem");
			operandReplacer.Add ("mem512env", "mem");
			operandReplacer.Add ("mem80dec", "mem");
			operandReplacer.Add ("mem80real", "mem");
			operandReplacer.Add ("mem94/108env", "mem");
			operandReplacer.Add ("mem2env", "mem16");
			operandReplacer.Add ("xmm1", "xmm");
			operandReplacer.Add ("xmm2", "xmm");
			operandReplacer.Add ("xmm/mem", "xmmmem");
			operandReplacer.Add ("xmm/mem32", "xmmmem32");
			operandReplacer.Add ("xmm/mem64", "xmmmem64");
			operandReplacer.Add ("xmm/mem128", "xmmmem128");
			operandReplacer.Add ("xmm1/mem32", "xmmmem32");
			operandReplacer.Add ("xmm1/mem64", "xmmmem64");
			operandReplacer.Add ("xmm1/mem128", "xmmmem128");
			operandReplacer.Add ("xmm2/mem32", "xmmmem32");
			operandReplacer.Add ("xmm2/mem64", "xmmmem64");
			operandReplacer.Add ("xmm2/mem128", "xmmmem128");
			operandReplacer.Add ("mmx/mem64", "mmxmem64");
			operandReplacer.Add ("mmx1", "mmx");
			operandReplacer.Add ("mmx2", "mmx");
			operandReplacer.Add ("mmx1/mem64", "mmxmem64");
			operandReplacer.Add ("mmx2/mem32", "mmxmem32");
			operandReplacer.Add ("mmx2/mem64", "mmxmem64");
			operandReplacer.Add ("pntr16:16", "pntr1616");
			operandReplacer.Add ("pntr16:32", "pntr1632");
			operandReplacer.Add ("mem16int", "mem16");
			operandReplacer.Add ("mem32int", "mem32");
			operandReplacer.Add ("mem32real", "mem32");
			operandReplacer.Add ("mem64int", "mem64");
			operandReplacer.Add ("mem64real", "mem64");

		(*	operandReplacer.Add ("rel8off", "imm");
			operandReplacer.Add ("rel16off", "imm");
			operandReplacer.Add ("rel32off", "imm");
		*)

			operandReplacer.Add ("ST(0)", "st0");
			operandReplacer.Add ("ST(i)", "sti");

			NEW(cpuoptionReplacer);
			cpuoptionReplacer.Add ("KATMAI", "Katmai");
			cpuoptionReplacer.Add ("PRESCOTT", "Prescott");
			cpuoptionReplacer.Add ("WILLAMETTE", "Willamette");
			cpuoptionReplacer.Add ("PENTIUM", "Pentium");
			cpuoptionReplacer.Add ("3DNOW", "3DNow");
			cpuoptionReplacer.Add ("PRIV", "Privileged");
			cpuoptionReplacer.Add ("PROT", "Protected");
			cpuoptionReplacer.Add ("SW","");
			cpuoptionReplacer.Add ("SB","");
			cpuoptionReplacer.Add ("SMM","");
			cpuoptionReplacer.Add ("AR1","");
			cpuoptionReplacer.Add ("AR2","");
			cpuoptionReplacer.Add ("ND","");

			NEW(bitwidthReplacer);
			bitwidthReplacer.Add("INV","I64");

			file := Files.Old(fileName);
			NEW(reader,file,0);
			GetCh();
			WHILE(ch # 0X) DO
				GetLine(line);
				ParseLine(line);
			END;

			NEW(w,fileName,500,400,TRUE);
			numberMnemonics := 0;
			numberInstructions := 0;
			maxMnemonicNameLength := 0;
			mnemonic := firstMnemonic;
			maxOpcodeLength:= 0;
			WHILE(mnemonic # NIL) DO
				IF Strings.Length(mnemonic.name)+1 > maxMnemonicNameLength THEN maxMnemonicNameLength := Strings.Length(mnemonic.name)+1 END;
				w.Char(09X); w.Char(09X); w.String("StartMnemonic(");
				w.String("op");
				w.String(mnemonic.name);
				w.String(", ");
				w.Char('"');
				w.String(mnemonic.name);
				w.Char('"');
				w.String(", ");
				w.Int(numberInstructions,1);
				w.String(");");
				w.Ln;
				INC(numberMnemonics);
				instruction := mnemonic.firstInstruction;
				WHILE(instruction # NIL) DO
					operandReplacer.Do(instruction.op1);
					operandReplacer.Do(instruction.op2);
					operandReplacer.Do(instruction.op3);
					bitwidthReplacer.Do(instruction.bitwidth);
					cpuoptionReplacer.Do(instruction.target);
					instruction := instruction.next;
				END;

				SortInstructions(mnemonic.firstInstruction);

				instruction := mnemonic.firstInstruction;
				WHILE(instruction # NIL) DO
					w.Char(09X); w.Char(09X); w.String("AddInstruction(");
					w.Int(numberInstructions,1); w.String(", ");
					Operand(instruction.op1); w.String(", ");
					Operand(instruction.op2); w.String(", ");
					Operand(instruction.op3); w.String(", ");
					OpCode(instruction.opcode); w.String(", ");
					Options("opt",instruction.bitwidth); w.String(", ");
					Options("cpu",instruction.target); w.String(");");
					w.Ln;
					INC(numberInstructions);
					instruction := instruction.next;
				END;
				w.Char(09X); w.Char(09X); w.String("EndMnemonic(");
				w.String("op"); w.String(mnemonic.name);
				w.String(", ");
				w.Int(numberInstructions-1,1);
				w.String(");");
				w.Ln;
				w.Ln;


				mnemonic := mnemonic.next;
			END;


			w.Char(09X); w.String("numberMnemonics = "); w.Int(numberMnemonics,1); w.String(";"); w.Ln;
			w.Char(09X); w.String("numberInstructions = "); w.Int(numberInstructions,1); w.String(";");w.Ln;
			w.Char(09X); w.String("maxMnemonicNameLength ="); w.Int(maxMnemonicNameLength,1); w.String(";"); w.Ln;
			w.Char(09X); w.String("maxCodeLength* ="); w.Int(maxOpcodeLength,1); w.String(";"); w.Ln;

			mnemonic := firstMnemonic; numberMnemonics := 0;
			WHILE(mnemonic # NIL) DO
				w.Char(09X); w.String("op"); w.String(mnemonic.name);
				w.String("* = ");
				w.Int(numberMnemonics,1); w.String(";");
				w.Ln;
				INC(numberMnemonics);
				mnemonic := mnemonic.next;
			END;

			w.Update;
			context.out.String("done"); context.out.Ln;
		ELSE
			context.error.String("filename expected"); context.error.Ln;
		END;
	END ParseAMDInstructionSet;

END OCProgTools.

SystemTools.Free OCProgTools ~

OCProgTools.Enum -l=2 a b c (* test (* test *) *)   d e  f g h i j k (* ddd *) d d d ~
OCProgTools.Enum --incremental a b c d e ~
OCProgTools.Enum --start=10 a b c  d e ~
OCProgTools.Enum --start=10 --hex  a b c  d e ~


OCProgTools.ParseAMDInstructionSet  oc/OCInstructionSetAMD64TabSeperated.txt ~