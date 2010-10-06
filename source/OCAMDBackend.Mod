MODULE OCAMDBackend; (** AUTHOR ""; PURPOSE ""; *)

IMPORT
	Scanner := OCScanner, SyntaxTree := OCSyntaxTree, Global := OCGlobal, Backend := OCBackend, Sections := OCSections,
	IntermediateCode := OCIntermediateCode, IntermediateBackend := OCIntermediateBackend, BinaryCode := OCBinaryCode,
	InstructionSet := OCAMD64InstructionSet, Assembler := OCAMD64Assembler, SemanticChecker := OCSemanticChecker, Formats := OCFormats,
	Diagnostics, Streams, Options, WMUtilities, Strings, ObjectFileFormat := OCBinaryObjectFile, Dataflow := OCDataflow
	, D := Debugging, Machine;

CONST

	optimizeExperiment=TRUE;
	SupportPool=FALSE;

	none=-1; free=-1;
	reserved=-2;
	split=-3;
	blocked=-4;
	unusable=-5;


	RAX*=InstructionSet.regRAX; RCX*=InstructionSet.regRCX; RDX*=InstructionSet.regRDX; RBX*=InstructionSet.regRBX;
	RSP*=InstructionSet.regRSP; RBP*=InstructionSet.regRBP; RSI*=InstructionSet.regRSI; RDI*=InstructionSet.regRDI;

	R8*=InstructionSet.regR8; 	R9*=InstructionSet.regR9; 	R10*=InstructionSet.regR10; 	R11*=InstructionSet.regR11;
	R12*=InstructionSet.regR12; 	R13*=InstructionSet.regR13; 	R14*=InstructionSet.regR14; 	R15*=InstructionSet.regR15;

	EAX*=InstructionSet.regEAX; ECX*=InstructionSet.regECX; EDX*=InstructionSet.regEDX; EBX*=InstructionSet.regEBX;
	ESP*=InstructionSet.regESP; EBP*=InstructionSet.regEBP; ESI*=InstructionSet.regESI; EDI*=InstructionSet.regEDI;

	R8D*=InstructionSet.regR8D; 	R9D*=InstructionSet.regR9D; 	R10D*=InstructionSet.regR10D; 	R11D*=InstructionSet.regR11D;
	R12D*=InstructionSet.regR12D; 	R13D*=InstructionSet.regR13D; 	R14D*=InstructionSet.regR14D; 	R15D*=InstructionSet.regR15D;

	AX*=InstructionSet.regAX;	CX*=InstructionSet.regCX;	DX*=InstructionSet.regDX;	BX*=InstructionSet.regBX;
	SI*=InstructionSet.regSI; DI*=InstructionSet.regDI; BP*=InstructionSet.regBP; SP*=InstructionSet.regSP;

	R8W*=InstructionSet.regR8W; 	R9W*=InstructionSet.regR9W; 	R10W*=InstructionSet.regR10W; 	R11W*=InstructionSet.regR11W;
	R12W*=InstructionSet.regR12W; 	R13W*=InstructionSet.regR13W; 	R14W*=InstructionSet.regR14W; 	R15W*=InstructionSet.regR15W;

	AL*=InstructionSet.regAL;	CL*=InstructionSet.regCL;	DL*=InstructionSet.regDL;	BL*=InstructionSet.regBL;
	SIL*=InstructionSet.regSIL; DIL*=InstructionSet.regDIL; BPL*=InstructionSet.regBPL; SPL*=InstructionSet.regSPL;

	R8B*=InstructionSet.regR8B; 	R9B*=InstructionSet.regR9B; 	R10B*=InstructionSet.regR10B; 	R11B*=InstructionSet.regR11B;
	R12B*=InstructionSet.regR12B; 	R13B*=InstructionSet.regR13B; 	R14B*=InstructionSet.regR14B; 	R15B*=InstructionSet.regR15B;

	AH*=InstructionSet.regAH;	CH*=InstructionSet.regCH;	DH*=InstructionSet.regDH;	BH*=InstructionSet.regBH;

	ST0*=InstructionSet.regST0;

	MaxVirtualRegisters=32;
	MaxSpilledRegisters=64;

TYPE


VAR registerOperands: ARRAY InstructionSet.numberRegisters OF Assembler.Operand;
	usePool: BOOLEAN;
	 opEAX, opECX, opEDX, opEBX, opESP, opEBP,
	 opESI, opEDI, opAX, opCX, opDX, opBX, opSI, opDI, opAL, opCL, opDL, opBL, opAH, opCH, opDH, opBH,opST0
	 , opRSP, opRBP: Assembler.Operand;

TYPE
	Register = RECORD
		lowSpilled, highSpilled: BOOLEAN; (* is register spilled on the spill stack ? *)
		low, high: LONGINT; (* real register index or position on spill stack *)
	END;

	Operand = RECORD
		low,high: Assembler.Operand;
	END;

	RegisterAllocator=OBJECT
	VAR
		realToVirtual: ARRAY InstructionSet.numberRegisters OF LONGINT; (* mapping real register -> none / reserved / split / blocked / virtual register (>0) *)

		PROCEDURE &InitRegisterAllocator;
		VAR i: LONGINT;
		BEGIN
			FOR i := 0 TO LEN(realToVirtual)-1 DO
				realToVirtual[i] := free;
			END;
			(* reserve stack and base pointer registers *)
			realToVirtual[BPL] := unusable;
			realToVirtual[SPL] := unusable;
			realToVirtual[BP] := unusable;
			realToVirtual[SP] := unusable;
			realToVirtual[EBP] := unusable;
			realToVirtual[ESP] := unusable;
			realToVirtual[RBP] := unusable;
			realToVirtual[RSP] := unusable;
		END InitRegisterAllocator;

		PROCEDURE Allocate(index: LONGINT; virtualRegister: LONGINT);
		END Allocate;

		PROCEDURE Free(index: LONGINT);
		END Free;

		PROCEDURE NextFree(sizeInBits: LONGINT): SHORTINT;
		END NextFree;

	END RegisterAllocator;

	RegisterAllocator32=OBJECT (RegisterAllocator) (* 32 bit implementation *)

		PROCEDURE & InitRegisterAllocator32;
		VAR i: LONGINT;
		BEGIN
			InitRegisterAllocator;
			(* reserve registers only usable in 64 bit mode *)
			FOR i := 8 TO 15 DO
				realToVirtual[i+AL] := unusable;
				realToVirtual[i+AH] := unusable;
				realToVirtual[i+EAX] := unusable;
				realToVirtual[i+AX] := unusable;
			END;
			FOR i := 4 TO 7 DO
				realToVirtual[i+AL] := unusable;
				realToVirtual[i+AH] := unusable;
			END;
		END InitRegisterAllocator32;

		PROCEDURE Allocate(index: LONGINT; virtualRegister: LONGINT);
		BEGIN
			(*
			D.String("allocate "); D.Int(index,1); D.String(": "); D.Int(virtualRegister,1); D.Ln;
			D.TraceBack;
			*)
			IF index DIV 32 = 2 THEN (* 32 bit *)
				Assert(realToVirtual[index] = free,"register already allocated");
				Assert(realToVirtual[index MOD 32 + AX] = free,"free register split");
				realToVirtual[index] := virtualRegister;
				realToVirtual[index MOD 32 + AX] := blocked;
				IF index MOD 32 < 4 THEN
					Assert(realToVirtual[index MOD 32 + AL] = free,"register already allocated");
					Assert(realToVirtual[index MOD 32 + AH] = free,"register already allocated");
					realToVirtual[index MOD 32 + AL] := blocked;
					realToVirtual[index MOD 32 + AH] := blocked;
				END;
			ELSIF index DIV 32 = 1 THEN (* 16 bit *)
				Assert(realToVirtual[index] = free,"register already allocated");
				Assert(realToVirtual[index MOD 8 + EAX] = free,"free register split");
				realToVirtual[index] := virtualRegister;
				realToVirtual[index MOD 32 + EAX] := split;
				IF index MOD 32 < 4 THEN
					Assert(realToVirtual[index MOD 32 + AL] = free,"register already allocated");
					Assert(realToVirtual[index MOD 32 + AH] = free,"register already allocated");
					realToVirtual[index MOD 32 + AL] := blocked;
					realToVirtual[index MOD 32 + AH] := blocked;
				END;
			ELSIF index DIV 32 = 0 THEN (* 8 bit *)
				Assert(realToVirtual[index] = free,"register already allocated");
				Assert((realToVirtual[index MOD 4 + EAX] = free) OR (realToVirtual[index MOD 4 + EAX] = split),"free register blocked");
				Assert((realToVirtual[index MOD 4 + AX] = free) OR (realToVirtual[index MOD 4 + AX] = split),"free register blocked");
				realToVirtual[index] := virtualRegister;
				realToVirtual[index MOD 4 + EAX] := split;
				realToVirtual[index MOD 4 + AX] := split;
			ELSE Assert( (index >=InstructionSet.regST0) & (index <= InstructionSet.regST7 ),"not a float register"); (* floats *)
				realToVirtual[index] := virtualRegister;
			END;
		END Allocate;

		PROCEDURE Free(index: LONGINT);
		VAR x: LONGINT;
		BEGIN
			(*
			D.String("Release "); D.Int(index,1); D.Ln;
			*)
			x := realToVirtual[index];
			Assert((realToVirtual[index] > 0) OR (realToVirtual[index]=reserved),"register not reserved");
			realToVirtual[index] := free;
			IF index DIV 32 =2  THEN (* 32 bit *)
				Assert(realToVirtual[index MOD 32 + AX] = blocked,"reserved register did not block");
				realToVirtual[index MOD 32 + AX] := free;
				IF index MOD 32 < 4 THEN
					Assert(realToVirtual[index MOD 32 + AL] = blocked,"reserved register did not block");
					Assert(realToVirtual[index MOD 32 + AH] = blocked,"reserved register did not block");
					realToVirtual[index MOD 32 + AL] := free;
					realToVirtual[index MOD 32 + AH] := free;
				END;
			ELSIF index DIV 32 = 1 THEN (* 16 bit *)
				Assert(realToVirtual[index MOD 32 + EAX] = split,"reserved register did not split");
				realToVirtual[index MOD 32 + EAX] := free;
				IF index MOD 32 < 4 THEN
					Assert(realToVirtual[index MOD 32 + AL] = blocked,"reserved register did not block");
					Assert(realToVirtual[index MOD 32 + AH] = blocked,"reserved register did not block");
					realToVirtual[index MOD 32 + AL] := free;
					realToVirtual[index MOD 32 + AH] := free;
				END;
			ELSIF index DIV 32 = 0 THEN (* 8 bit *)
				IF (realToVirtual[index MOD 4 + AL] = free) & (realToVirtual[index MOD 4 + AH] = free) THEN
					Assert(realToVirtual[index MOD 4 + EAX] = split,"reserved register did not split");
					Assert(realToVirtual[index MOD 4 + AX] = split,"reserved register did not split");
					realToVirtual[index MOD 4 + EAX] := free;
					realToVirtual[index MOD 4 + AX] := free;
				END;
			ELSE Assert( (index >=InstructionSet.regST0) & (index <= InstructionSet.regST7 ),"not a float register"); (* floats *)
				realToVirtual[index] := free;
			END;
		END Free;
		(*
		PROCEDURE NextFree(sizeInBits: LONGINT): SHORTINT;
		VAR i: SHORTINT;
		BEGIN
			IF sizeInBits = IntermediateCode.Bits8 THEN
				i := AL;
				WHILE (i<=BL) & (realToVirtual[i] # free)  DO
					INC(i);
				END;
				IF i> BL THEN
					i := AH;
					WHILE (i<=BH) & (realToVirtual[i] # free)  DO
						INC(i);
					END;
					IF i> BH THEN i := none END;
					(* Assert(i >=AH,"not enough 8 bit registers"); *)
				END;
				RETURN i;
			ELSIF sizeInBits = IntermediateCode.Bits16 THEN
				i := AX;
				WHILE (i <= BX) & (realToVirtual[i] # free) DO
					INC(i);
				END;
				IF i> BX THEN
					i := SI;
					WHILE (i <= DI) & (realToVirtual[i] # free) DO
						INC(i);
					END;
					IF i > DI THEN i := none END;
				END;
				RETURN i;
			ELSIF sizeInBits = IntermediateCode.Bits32 THEN
				i := EAX;
				WHILE (i <= EBX) & (realToVirtual[i] # free) DO
					INC(i);
				END;
				IF i> EBX THEN
					i := ESI;
					WHILE (i <= EDI) & (realToVirtual[i] # free) DO
						INC(i);
					END;
					IF i > EDI THEN i := none END;
				END;
				RETURN i;
			ELSE HALT(100)
			END;
		END NextFree;

		*)

		PROCEDURE NextFree(sizeInBits: LONGINT): SHORTINT;
		VAR i: SHORTINT;
		BEGIN
			IF sizeInBits = IntermediateCode.Bits8 THEN
				i := BL;
				WHILE (i>=AL) & (realToVirtual[i] # free)  DO
					DEC(i);
				END;
				IF i< AL THEN
					i := BH;
					WHILE (i>=AH) & (realToVirtual[i] # free)  DO
						DEC(i);
					END;
					IF i< AH THEN i := none END;
					(* Assert(i >=AH,"not enough 8 bit registers"); *)
				END;
				RETURN i;
			ELSIF sizeInBits = IntermediateCode.Bits16 THEN
				i := DI;
				WHILE (i >= SI) & (realToVirtual[i] # free) DO
					DEC(i);
				END;
				IF i < SI THEN
					i := BX;
					WHILE (i >= AX) & (realToVirtual[i] # free) DO
						DEC(i);
					END;
					IF i< AX THEN i := none END;
					(* Assert(i>=AX,"not enough 16 bit registers");*)
				END;
				RETURN i;
			ELSIF sizeInBits = IntermediateCode.Bits32 THEN
				i := EDI;
				WHILE (i>=ESI) & (realToVirtual[i] # free) DO
					DEC(i);
				END;
				IF i < ESI THEN
					i := EBX;
					WHILE (i >= EAX) & (realToVirtual[i] # free)  DO
						DEC(i);
					END;
					IF i< EAX THEN i := none END;
					(*
					Assert(i>=EAX,"not enough 32 bit registers");
					*)
				END;
				RETURN i;
			ELSE HALT(100)
			END;
		END NextFree;


	END RegisterAllocator32;

	RegisterAllocator64=OBJECT (RegisterAllocator) (* 64 bit implementation *)

		PROCEDURE & InitRegisterAllocator64;
		BEGIN
			InitRegisterAllocator;
		END InitRegisterAllocator64;

		PROCEDURE Allocate(index: LONGINT; virtualRegister: LONGINT);
		BEGIN
			(*
			D.String("allocate "); D.Int(index,1); D.String(": "); D.Int(virtualRegister,1); D.Ln;
			D.TraceBack;
			*)
			IF index DIV 32 = 3 THEN (* 64 bit *)
				Assert(realToVirtual[index] = free,"register already allocated");
				Assert(realToVirtual[index MOD 32 + EAX] = free,"free register split");
				realToVirtual[index] := virtualRegister;
				realToVirtual[index MOD 32 + EAX] := blocked;
				realToVirtual[index MOD 32 + AX] := blocked;
				realToVirtual[index MOD 32 + AL] := blocked;
			ELSIF index DIV 32 = 2 THEN (* 32 bit *)
				Assert(realToVirtual[index] = free,"register already allocated");
				Assert(realToVirtual[index MOD 32 + AX] = free,"free register split");
				realToVirtual[index] := virtualRegister;
				realToVirtual[index MOD 32 + RAX] := split;
				realToVirtual[index MOD 32 + AX] := blocked;
				realToVirtual[index MOD 32 + AL] := blocked;
			ELSIF index DIV 32 = 1 THEN (* 16 bit *)
				Assert(realToVirtual[index] = free,"register already allocated");
				realToVirtual[index] := virtualRegister;
				realToVirtual[index MOD 32 + RAX] := split;
				realToVirtual[index MOD 32 + EAX] := split;
				realToVirtual[index MOD 32 + AL] := blocked;
			ELSIF index DIV 32 = 0 THEN (* 8 bit *)
				Assert(realToVirtual[index] = free,"register already allocated");
				realToVirtual[index] := virtualRegister;
				realToVirtual[index MOD 32 + RAX] := split;
				realToVirtual[index MOD 32 + EAX] := split;
				realToVirtual[index MOD 32 + AX] := split;
			ELSE Assert( (index >=InstructionSet.regST0) & (index <= InstructionSet.regST7 ),"not a float register"); (* floats *)
				realToVirtual[index] := virtualRegister;
			END;
		END Allocate;

		PROCEDURE Free(index: LONGINT);
		VAR x: LONGINT;
		BEGIN
			(*
			D.String("Release "); D.Int(index,1); D.Ln;
			*)
			x := realToVirtual[index];
			Assert((realToVirtual[index] > 0) OR (realToVirtual[index]=reserved),"register not reserved");
			realToVirtual[index] := free;
			IF index DIV 32 =3  THEN (* 64 bit *)
				Assert(realToVirtual[index MOD 32 + EAX] = blocked,"reserved register did not block");
				realToVirtual[index MOD 32 + EAX] := free;
				realToVirtual[index MOD 32 + AL] := free;
			ELSIF index DIV 32 =2  THEN (* 32 bit *)
				Assert(realToVirtual[index MOD 32 + RAX] = split,"reserved register did not split");
				Assert(realToVirtual[index MOD 32 + AX] = blocked,"reserved register did not block");
				Assert(realToVirtual[index MOD 32 + AL] = blocked,"reserved register did not block");
				realToVirtual[index MOD 32 + RAX] := free;
				realToVirtual[index MOD 32 + AX] := free;
				realToVirtual[index MOD 32 + AL] := free;
			ELSIF index DIV 32 = 1 THEN (* 16 bit *)
				Assert(realToVirtual[index MOD 32 + RAX] = split,"reserved register did not split");
				Assert(realToVirtual[index MOD 32 + EAX] = split,"reserved register did not split");
				Assert(realToVirtual[index MOD 32 + AL] = blocked,"reserved register did not split");
				realToVirtual[index MOD 32 + RAX] := free;
				realToVirtual[index MOD 32 + EAX] := free;
				realToVirtual[index MOD 32 + AL] := free;
			ELSIF index DIV 32 = 0 THEN (* 8 bit *)
				Assert(realToVirtual[index MOD 32 + RAX] = split,"reserved register did not split");
				Assert(realToVirtual[index MOD 32 + EAX] = split,"reserved register did not split");
				Assert(realToVirtual[index MOD 32 + AX] = split,"reserved register did not split");
				realToVirtual[index MOD 32 + RAX] := free;
				realToVirtual[index MOD 32 + EAX] := free;
				realToVirtual[index MOD 32 + AX] := free;
			ELSE Assert( (index >=InstructionSet.regST0) & (index <= InstructionSet.regST7 ),"not a float register"); (* floats *)
				realToVirtual[index] := free;
			END;
		END Free;
		(*
		PROCEDURE NextFree(sizeInBits: LONGINT): SHORTINT;
		VAR i: SHORTINT;
		BEGIN
			IF sizeInBits = IntermediateCode.Bits8 THEN
				i := AL;
				WHILE (i<=BL) & (realToVirtual[i] # free)  DO
					INC(i);
				END;
				IF i> BL THEN
					i := AH;
					WHILE (i<=BH) & (realToVirtual[i] # free)  DO
						INC(i);
					END;
					IF i> BH THEN i := none END;
					(* Assert(i >=AH,"not enough 8 bit registers"); *)
				END;
				RETURN i;
			ELSIF sizeInBits = IntermediateCode.Bits16 THEN
				i := AX;
				WHILE (i <= BX) & (realToVirtual[i] # free) DO
					INC(i);
				END;
				IF i> BX THEN
					i := SI;
					WHILE (i <= DI) & (realToVirtual[i] # free) DO
						INC(i);
					END;
					IF i > DI THEN i := none END;
				END;
				RETURN i;
			ELSIF sizeInBits = IntermediateCode.Bits32 THEN
				i := EAX;
				WHILE (i <= EBX) & (realToVirtual[i] # free) DO
					INC(i);
				END;
				IF i> EBX THEN
					i := ESI;
					WHILE (i <= EDI) & (realToVirtual[i] # free) DO
						INC(i);
					END;
					IF i > EDI THEN i := none END;
				END;
				RETURN i;
			ELSE HALT(100)
			END;
		END NextFree;

		*)

		PROCEDURE NextFree(sizeInBits: LONGINT): SHORTINT;
		VAR i: SHORTINT;
		BEGIN
			IF sizeInBits = IntermediateCode.Bits8 THEN
				i := R15B;
				WHILE (i>=AL) & (realToVirtual[i] # free)  DO
					DEC(i);
				END;
				IF i< AL THEN
					i := none;
					(* Assert(i >=AH,"not enough 8 bit registers"); *)
				END;
				RETURN i;
			ELSIF sizeInBits = IntermediateCode.Bits16 THEN
				i := R15W;
				WHILE (i >= AX) & (realToVirtual[i] # free) DO
					DEC(i);
				END;
				IF i< AX THEN i := none END;
				RETURN i;
			ELSIF sizeInBits = IntermediateCode.Bits32 THEN
				i := R15D;
				WHILE (i>=EAX) & (realToVirtual[i] # free) DO
					DEC(i);
				END;
				IF i< EAX THEN i := none END;
				RETURN i;
			ELSIF sizeInBits = IntermediateCode.Bits64 THEN
				i := R15;
				WHILE (i>=RAX) & (realToVirtual[i] # free) DO
					DEC(i);
				END;
				IF i< EAX THEN i := none END;
				RETURN i;
			ELSE HALT(100)
			END;
		END NextFree;

	END RegisterAllocator64;

	CodeGenerator= OBJECT (* code generator : generic part, may be moved to generic code generator module *)
	VAR
		diagnostics: Diagnostics.Diagnostics; (* error stream *)
		module: Sections.Module;
		lastUse: ARRAY MaxVirtualRegisters OF LONGINT;
		dump: Streams.Writer;
		in: IntermediateCode.Section; out: BinaryCode.Section;
		inPC: LONGINT;
		toBeReleased: SET; (* registers that will be released after current instruction *)
		currentlyUsed: SET; (* registers that are used in current instruction *)
		error: BOOLEAN;

		(* generic *)
		PROCEDURE & InitGenerator(diagnostics: Diagnostics.Diagnostics);
		VAR i: LONGINT;
		BEGIN
			SELF.module := NIL;
			SELF.diagnostics := diagnostics;
			FOR i := 0 TO LEN(lastUse)-1 DO
				lastUse[i] := -1;
			END;
			SELF.error := FALSE;
		END InitGenerator;

		PROCEDURE SetModule(module: Sections.Module); (* needed for inline code for symbol reference *)
		BEGIN
			SELF.module := module;
		END SetModule;

		PROCEDURE Error( CONST message: ARRAY OF CHAR);
		BEGIN
			diagnostics.Error("",0,Diagnostics.Invalid,message);
			error := TRUE;
		END Error;

		(* generic *)
		PROCEDURE Section(in: IntermediateCode.Section; out: BinaryCode.Section);
		VAR pc: LONGINT; name: SyntaxTree.String; ignore: BOOLEAN;

			PROCEDURE CheckAcquire(CONST instr: IntermediateCode.Instruction);
			VAR i: LONGINT; type: IntermediateCode.Type;
				(*lastUse: ARRAY MaxVirtualRegisters OF LONGINT;*)

				PROCEDURE CheckOperand(CONST operand: IntermediateCode.Operand; register: LONGINT; at: LONGINT);
				BEGIN
					IF operand.register = register THEN lastUse[register] := at;
						IF operand.mode = IntermediateCode.ModeMemory THEN
							type := IntermediateBackend.GetType(module.system,module.system.addressType);
						ELSE
							type := operand.type
						END;
					END;
				END CheckOperand;

				PROCEDURE CheckUsage(CONST instr: IntermediateCode.Instruction; register: LONGINT; at: LONGINT);
				BEGIN
					CheckOperand(instr.op1,register, at);
					CheckOperand(instr.op2,register, at);
					CheckOperand(instr.op3,register, at);
				END CheckUsage;

				PROCEDURE CheckDest(CONST instr: IntermediateCode.Instruction; register: LONGINT): BOOLEAN;
				(* check if instruction uses register as new destination operand
					examples:
						mov $0, $1
						add $0, [$1]
						call (implicit for $res and $res2)
					but not:
						mov [$0], $1
						add $0, $0, 1
				*)
				BEGIN
					RETURN
					(instr.op1.mode = IntermediateCode.ModeRegister)
					& (IntermediateCode.Op1IsDestination IN IntermediateCode.instructionFormat[instr.opcode].flags) (* first operand is destination operand *)
					& (instr.op1.register = register) & (instr.op2.register # register) & (instr.op3.register # register)
					OR (instr.opcode = IntermediateCode.call) & (register IN {IntermediateCode.Result, IntermediateCode.Result2})
				END CheckDest;

				PROCEDURE Reserve(register: LONGINT);
				BEGIN
					IF (register >0) & CheckDest(instr,register) THEN
						Assert(lastUse[register] < 0,"error in register usage");
						type := instr.op1.type;
						i := pc+1; lastUse[register] := pc;
						WHILE (i<in.pc) & ~CheckDest(in.instructions[i],register) DO
							CheckUsage(in.instructions[i],register,i); INC(i);
						END;
						IF (instr.opcode # IntermediateCode.call) OR (lastUse[register] >pc) THEN (* used at all *)
							IF dump # NIL THEN
								dump.String("map virtual register $"); dump.Int(register,1);
								dump.String(", last use:"); dump.Int(lastUse[register],1);
								IntermediateCode.DumpType(dump,type);
								dump.Ln;
							END;
							MapVirtualRegister(register,type);
						ELSE lastUse[register] := -1;
						END;
					END;
				END Reserve;

			BEGIN
				Reserve(instr.op1.register);
				IF instr.opcode = IntermediateCode.call THEN
					Reserve(IntermediateCode.Result);
					Reserve(IntermediateCode.Result2);
				END;
			END CheckAcquire;

			PROCEDURE Prepare(instr: IntermediateCode.Instruction; pc: LONGINT);
			VAR register: LONGINT;
			BEGIN
				FOR register := 0 TO MaxVirtualRegisters-1 DO
					IF lastUse[register] = pc THEN INCL(toBeReleased,register) END;
				END;
				currentlyUsed := {};
				IF instr.opcode = IntermediateCode.call THEN
					INCL(currentlyUsed, IntermediateCode.Result);
					INCL(currentlyUsed, IntermediateCode.Result2);
				END;
				IF instr.op1.register > 0 THEN INCL(currentlyUsed,instr.op1.register) END;
				IF instr.op2.register > 0 THEN INCL(currentlyUsed,instr.op2.register) END;
				IF instr.op3.register > 0 THEN INCL(currentlyUsed,instr.op3.register) END;
			END Prepare;

			PROCEDURE Release(instr: IntermediateCode.Instruction);
			VAR register: LONGINT;
			BEGIN
				FOR register := 0 TO MaxVirtualRegisters-1 DO
					IF register IN toBeReleased THEN
						UnmapVirtualRegister(register);
					END;
				END;
			END Release;

			PROCEDURE CheckRelease;
			VAR register: LONGINT;
			BEGIN
				FOR register := 0 TO MaxVirtualRegisters-1 DO
					IF register IN toBeReleased THEN
						Error("register not released");
					END;
					IF lastUse[register] # -1 THEN
						Error("register still used");
					END;
				END;
			END CheckRelease;


			PROCEDURE ResolveLocalFixups;
			VAR fixup,next: BinaryCode.Fixup;  dest: LONGINT;
			BEGIN
				fixup := out.fixupList.firstFixup;
				out.fixupList.InitFixupList;
				WHILE fixup # NIL DO
					next := fixup.nextFixup;

					IF (fixup.symbol = in) & (fixup.mode = BinaryCode.Relative) THEN (* local fixup *)
						IF dump # NIL THEN
							dump.String("local fixup: "); fixup.Dump(dump); dump.Ln;
						END;
						dest := fixup.symbolOffset;
						IF dest # 0 THEN
							ASSERT(in.pc > dest);
							dest := in.instructions[dest].pc;
						END;
						fixup.SetSymbol(fixup.symbol,0,dest+fixup.displacement);
						IF dump # NIL THEN
							dump.String("local fixup resolved: "); fixup.Dump(dump); dump.Ln;
						END;
						IF ~out.ApplyFixup(fixup) THEN
							Error("local fixup out of range");
						END
					ELSE
						out.fixupList.AddFixup(fixup);
					END;
					fixup := next;
				END;
			END ResolveLocalFixups;

		BEGIN
			ignore := FALSE;
			name := in.name; (*debugging*)
			SELF.in := in; SELF.out := out;
			dump := out.comments;
			(* dump := D.Log;*)
			FOR pc := 0 TO in.pc-1 DO
				IF pc = in.finally THEN out.SetFinally(out.pc) END;
				IF pc = in.validPAFEnter THEN out.EnterValidPAF END;
				IF pc = in.validPAFExit THEN out.ExitValidPAF END;
				CheckAcquire(in.instructions[pc]);
				Prepare(in.instructions[pc],pc);
				IF dump # NIL THEN
					dump.Int(pc,1); dump.String(": "); IntermediateCode.DumpInstruction(dump,in.instructions[pc]);
					IF ignore THEN dump.String(" ignored.") END;
					dump.String(" | ");
					dump.Set(toBeReleased);
					dump.Set(currentlyUsed);
					dump.Ln;
				END;
				inPC := pc;
				in.SetPC(pc,out.pc); (* set pc of (intermediate) instruction at pc to newPC *)
				IF ~ignore THEN
					Generate(in.instructions[pc]);
					Release(in.instructions[pc]);
				END;
			END;
			CheckRelease();

			ResolveLocalFixups;
			IF dump # NIL THEN
				dump.Update
			END
		END Section;

		PROCEDURE MapVirtualRegister(reg: LONGINT; type: IntermediateCode.Type);
		BEGIN HALT(100); (* abstract *)
		END MapVirtualRegister;

		PROCEDURE UnmapVirtualRegister(reg: LONGINT);
		BEGIN HALT(100); (* abstract *)
		END UnmapVirtualRegister;

		PROCEDURE TransferRegister(from, to: LONGINT);
		BEGIN HALT(100);
		END TransferRegister;


		PROCEDURE Generate(CONST instr: IntermediateCode.Instruction);
		BEGIN HALT(100); (* abstract *)
		END Generate;

	END CodeGenerator;


	CodeGeneratorAMD64 = OBJECT (CodeGenerator)
	VAR
		emitter: Assembler.Emitter; (* assembler generating and containing the machine code *)
		bits: LONGINT;
		registerAllocator: RegisterAllocator;
		realRegisters: ARRAY MaxVirtualRegisters OF Register; (* mapping to general purpose registers *)

		stackSize, enterPos: LONGINT;
		spillStack: ARRAY MaxSpilledRegisters OF LONGINT; (* mapping of spill stack position to virtual register, none if unused *)
		spillStackOperand: ARRAY MaxSpilledRegisters OF Assembler.Operand;
		spillStackStart, spillStackSize: LONGINT;
		fpRegisters: ARRAY MaxVirtualRegisters OF LONGINT; (* mapping virtual register => fp stack position *)
		registerType: ARRAY MaxVirtualRegisters OF IntermediateCode.Type;
		fpMapped: ARRAY 9 OF LONGINT; (* mapping fp stack position => virtual register *)
		fpStackPointer: LONGINT; (* floating point stack pointer, increases with allocation, decreases with releasing, used to determine current relative position on stack (as is necessary for intel FP instructions) *)

		temporary: ARRAY 6 OF LONGINT; numberTemporary : LONGINT;
		runtimeModuleName: SyntaxTree.String;

		opBP, opSP, opA: Assembler.Operand;
		BP, SP: LONGINT;

		PROCEDURE &InitGeneratorAMD64(CONST runtime: SyntaxTree.String; diagnostics: Diagnostics.Diagnostics; bits: LONGINT);
		VAR i: LONGINT; registerAllocator32: RegisterAllocator32; registerAllocator64: RegisterAllocator64;
		BEGIN
			runtimeModuleName := runtime;
			InitGenerator(diagnostics);
			NEW(emitter,diagnostics);
			IF bits=32 THEN
				NEW(registerAllocator32); registerAllocator := registerAllocator32; error := ~emitter.SetBits(32);
				opBP := opEBP; opSP := opESP; opA := opEAX;
				SP := ESP; BP := EBP;
				ASSERT(~error);
			ELSIF bits=64 THEN
				NEW(registerAllocator64); registerAllocator := registerAllocator64; error := ~emitter.SetBits(64);
				opBP := opRBP; opSP := opRSP; opA := registerOperands[RAX];
				SP := RSP; BP := RBP;
				ASSERT(~error);
			ELSE Halt("no register allocator for bits other than 32 / 64 ");
			END;
			SELF.bits := bits;
			(*
			registerAllocator.Allocate(EAX,reserved);
			registerAllocator.Allocate(EDX,reserved);
			*)
			(* registers EAX and EDX are reserved as return registers and for multi purpose use during
			the whole code generation process *)
			fpStackPointer := 0;
			FOR i := 0 TO LEN(spillStack)-1 DO
				spillStack[i] := none;
			END;
			FOR i := 0 TO LEN(realRegisters)-1 DO
				realRegisters[i].low := none;
				realRegisters[i].high := none;
				realRegisters[i].lowSpilled := FALSE;
				realRegisters[i].highSpilled := FALSE;
			END;
		END InitGeneratorAMD64;

		PROCEDURE Error( CONST message: ARRAY OF CHAR);
		BEGIN
			diagnostics.Error(emitter.code.identifier.name,(emitter.code.pc),Diagnostics.Invalid,message);
			IF dump # NIL THEN
				dump.String(message); dump.Ln;
			END;
			error := TRUE;
		END Error;

		PROCEDURE Section(in: IntermediateCode.Section; out: BinaryCode.Section);
		BEGIN
			emitter.SetCode(out);
			spillStackSize := 0;
			Section^(in,out);
			IF spillStackSize >0 THEN
				out.Reset;
				Section^(in,out);
			END;
			(*PatchEnter();*)
			error := error OR emitter.error;
		END Section;

		PROCEDURE Supported(CONST instr: IntermediateCode.Instruction; VAR moduleName, procedureName: ARRAY OF CHAR): BOOLEAN;
		BEGIN
			COPY(runtimeModuleName, moduleName);
			IF (bits=32) & (instr.op2.type.sizeInBits = IntermediateCode.Bits64) & (instr.op2.type.form IN IntermediateCode.Integer) THEN
				CASE instr.opcode OF
				IntermediateCode.div:
					procedureName := "DivH"; RETURN FALSE
				| IntermediateCode.mul:
					procedureName := "MulH"; RETURN FALSE
				| IntermediateCode.mod :
					procedureName := "ModH"; RETURN FALSE
				| IntermediateCode.abs :
					procedureName := "AbsH"; RETURN FALSE;
				| IntermediateCode.shl :
					IF instr.op1.type.form = IntermediateCode.SignedInteger THEN
						procedureName := "AslH"; RETURN FALSE;
					ELSE
						procedureName := "LslH"; RETURN FALSE;
					END;
				| IntermediateCode.shr :
					IF instr.op1.type.form = IntermediateCode.SignedInteger THEN
						procedureName := "AsrH"; RETURN FALSE;
					ELSE
						procedureName := "LsrH"; RETURN FALSE;
					END;
				| IntermediateCode.ror :
					procedureName := "RorH"; RETURN FALSE;
				| IntermediateCode.rol :
					procedureName := "RolH"; RETURN FALSE;
				ELSE RETURN TRUE
				END;
			END;
			RETURN TRUE
		END Supported;


		PROCEDURE Spill(vreg: LONGINT);
		VAR low,high,index: LONGINT;

			PROCEDURE NextFree(): LONGINT;
			VAR i,index: LONGINT;
			BEGIN
				i := 0;
				index := spillStack[i];
				WHILE (index # none) DO
					INC(i); index := spillStack[i];
				END;
				IF i >= spillStackSize THEN spillStackSize := i+1 END;
				RETURN i
			END NextFree;

		BEGIN
			IF (vreg <0) THEN RETURN END;
			low := realRegisters[vreg].low;
			IF ~(realRegisters[vreg].lowSpilled) & (low # none) THEN
				index := NextFree();
				spillStack[index] := vreg;
				spillStackOperand[index] := Assembler.NewMem(registerOperands[low].sizeInBytes,BP , -(spillStackStart + 4 + index*4));
				IF dump # NIL THEN
					dump.String("spill "); dump.Int(vreg,1); dump.String(":"); dump.String(InstructionSet.registers[low].name);dump.String(" -> "); dump.Int(index,1); dump.Ln;
				END;
				emitter.Emit2(InstructionSet.opMOV,spillStackOperand[index],registerOperands[low]);
				realRegisters[vreg].low := index;
				registerAllocator.Free(low);
				realRegisters[vreg].lowSpilled := TRUE;
			END;
			high := realRegisters[vreg].high;
			IF ~(realRegisters[vreg].highSpilled) & (high # none) THEN
				index := NextFree();
				spillStack[index] := vreg;
				spillStackOperand[index] := Assembler.NewMem(registerOperands[high].sizeInBytes,BP , -(spillStackStart + 4 + index*4));
				IF dump # NIL THEN
					dump.String("spill "); dump.Int(vreg,1); dump.String(":"); dump.String(InstructionSet.registers[high].name);dump.String(" -> "); dump.Int(index,1); dump.Ln;
				END;
				emitter.Emit2(InstructionSet.opMOV,spillStackOperand[index],registerOperands[high]);
				realRegisters[vreg].high := index;
				registerAllocator.Free(high);
				realRegisters[vreg].highSpilled := TRUE;
			END;
		END Spill;

		PROCEDURE UnSpill(vreg: LONGINT; lowIndex, highIndex: LONGINT);
		VAR low,high,i: LONGINT;
		BEGIN
			IF (vreg < 0) OR (~realRegisters[vreg].lowSpilled) & (~realRegisters[vreg].highSpilled) THEN RETURN END;
			low := realRegisters[vreg].low;
			IF (low # none) & realRegisters[vreg].lowSpilled THEN
				IF lowIndex = none THEN
					lowIndex := TrySpill(spillStackOperand[low].sizeInBytes*8);
				END;
				registerAllocator.Allocate(lowIndex,vreg);
				IF dump # NIL THEN
					dump.String("unspill "); dump.Int(vreg,1); dump.String(":"); dump.Int(low,1); dump.String(" -> "); dump.String(InstructionSet.registers[lowIndex].name); dump.Ln;
				END;
				emitter.Emit2(InstructionSet.opMOV,registerOperands[lowIndex],spillStackOperand[low]);
				spillStack[vreg] := none;
				realRegisters[vreg].low := lowIndex;
				realRegisters[vreg].lowSpilled := FALSE;
			END;

			high := realRegisters[vreg].high;
			IF (high # none) & realRegisters[vreg].highSpilled THEN
				IF highIndex = none THEN
					highIndex := registerAllocator.NextFree(spillStackOperand[high].sizeInBytes*8);
				END;
				registerAllocator.Allocate(highIndex,vreg);
				IF dump # NIL THEN
					dump.String("unspill "); dump.Int(vreg,1); dump.String(":"); dump.Int(high,1); dump.String(" -> "); dump.String(InstructionSet.registers[lowIndex].name); dump.Ln;
				END;
				emitter.Emit2(InstructionSet.opMOV,registerOperands[highIndex],spillStackOperand[high]);
				spillStack[vreg] := none;
				realRegisters[vreg].high := highIndex;
				realRegisters[vreg].highSpilled := FALSE;
			END;
		END UnSpill;

		PROCEDURE FreeRegister(index: LONGINT);
		VAR virtual,new: LONGINT; newOp, oldOp: Operand; type: IntermediateCode.Type; size: LONGINT; high: BOOLEAN;
		BEGIN
			IF index = none THEN RETURN END;
			virtual := registerAllocator.realToVirtual[index];
			IF virtual # free THEN
				IF virtual = blocked THEN
					IF (AL <= index) & (index <= BH) THEN
						FreeRegister(index MOD 4+32);
					ELSIF (AX <= index) & (index <= BX) THEN
						FreeRegister(index + 32)
					ELSE HALT(100) END;
				ELSIF virtual = split THEN
					IF (EAX <= index) & (index <= EBX) THEN
						FreeRegister(index - 32)
					ELSIF (AX <= index) & (index <= BX) THEN
						FreeRegister( (index -32) MOD 4); registerAllocator.Allocate((index - 32) MOD 4, reserved); (* protect from being reused during free *)
						FreeRegister( (index -32) MOD 4 +4); registerAllocator.Free((index - 32) MOD 4);
					ELSE HALT(100)
					END;
				ELSE
					ASSERT((realRegisters[virtual].low = index) OR (realRegisters[virtual].high = index));
					type := registerType[virtual];
					IF type.sizeInBits >= 32 THEN size := 32 ELSE size := type.sizeInBits END;

					(* protect from being spilled *)
					registerAllocator.Free(index);
					registerAllocator.Allocate(index, reserved);
					IF (bits=64) OR (type.sizeInBits <64) OR (realRegisters[virtual].low = index) THEN
						realRegisters[virtual].low := none;
						realRegisters[virtual].lowSpilled := FALSE;
						high := FALSE;
					ELSE ASSERT(realRegisters[virtual].high = index);
						realRegisters[virtual].high := none;
						realRegisters[virtual].highSpilled := FALSE;
						high := TRUE;
					END;
					(* try to replace with new register or spill *)
					new := registerAllocator.NextFree(size);
					IF new = none THEN new := TrySpill(size) END;

					Assembler.InitOperand(newOp.high); Assembler.InitOperand(oldOp.high);
					newOp.low := Assembler.NewRegister(new);
					oldOp.low := Assembler.NewRegister(index);
					Mov(InstructionSet.opMOV, newOp, oldOp);
					IF ~high THEN
						realRegisters[virtual].low := new;
						realRegisters[virtual].lowSpilled := FALSE;
					ELSE
						realRegisters[virtual].high := new;
						realRegisters[virtual].highSpilled := FALSE;
					END;
					registerAllocator.Free(index);
					registerAllocator.Allocate(new, virtual);
				END;
			END;
		END FreeRegister;

		PROCEDURE MapVirtualRegister(reg: LONGINT; type: IntermediateCode.Type);
		VAR index: LONGINT;

			PROCEDURE NextFree(): LONGINT;
			VAR i,index: LONGINT;
			BEGIN
				i := 0;
				index := spillStack[i];
				WHILE (index # none) DO
					INC(i); index := spillStack[i];
				END;
				IF i >= spillStackSize THEN spillStackSize := i+1 END;
				RETURN i
			END NextFree;

		BEGIN
			IF type.form IN IntermediateCode.Integer THEN
				IF (type.sizeInBits = IntermediateCode.Bits64) & (bits = 32) THEN
					IF reg = IntermediateCode.Result THEN
						index := EAX;
						FreeRegister(index);
					ELSE
						index := registerAllocator.NextFree(IntermediateCode.Bits32);
					END;

					IF index = none THEN
						index := NextFree();
						realRegisters[reg].lowSpilled := TRUE;
						realRegisters[reg].low := index;
						spillStack[index] := reg;
						spillStackOperand[index] := Assembler.NewMem(IntermediateCode.Bits32 DIV 8,BP, -(spillStackStart + 4 + index*4));

						IF dump # NIL THEN
							dump.String("acquire register "); dump.Int(reg,1); dump.String("(low, virtual)  : "); dump.Int(index,1); dump.Ln;
						END;
					ELSE
						realRegisters[reg].lowSpilled := FALSE;
						realRegisters[reg].low := index;
						registerAllocator.Allocate(index,reg);
						IF dump # NIL THEN
							dump.String("acquire register "); dump.Int(reg,1); dump.String("(low)  : "); dump.String(InstructionSet.registers[index].name); dump.Ln;
						END;
					END;

					IF reg = IntermediateCode.Result THEN
						index := EDX;
						FreeRegister(index);
					ELSE
						index := registerAllocator.NextFree(IntermediateCode.Bits32);
					END;
					IF index = none THEN
						index := NextFree();
						realRegisters[reg].highSpilled := TRUE;
						realRegisters[reg].high := index;
						spillStack[index] := reg;
						spillStackOperand[index] := Assembler.NewMem(IntermediateCode.Bits32 DIV 8,BP, -(spillStackStart + 4 + index*4));
						IF dump # NIL THEN
							dump.String("acquire register "); dump.Int(reg,1); dump.String("(high, virtual)  : "); dump.Int(index,1); dump.Ln;
						END;
					ELSE
						realRegisters[reg].highSpilled := FALSE;
						realRegisters[reg].high := index;
						registerAllocator.Allocate(index,reg);
						IF dump # NIL THEN
							dump.String("acquire register "); dump.Int(reg,1); dump.String("(high)  : "); dump.String(InstructionSet.registers[index].name); dump.Ln;
						END;
					END;
				ELSE
					ASSERT(bits >= type.sizeInBits);
					IF reg = IntermediateCode.Result THEN
						IF type.sizeInBits = 64 THEN
							index := RAX
						ELSIF type.sizeInBits = 32 THEN
							index := EAX
						ELSIF type.sizeInBits =16 THEN
							index := AX
						ELSIF type.sizeInBits = 8 THEN
							index := AL
						END;
						FreeRegister(index);
					ELSIF reg = IntermediateCode.Result2 THEN
						IF type.sizeInBits = 64 THEN
							index := RDX
						ELSIF type.sizeInBits = 32 THEN
							index := EDX
						ELSIF type.sizeInBits =16 THEN
							index := DX
						ELSIF type.sizeInBits = 8 THEN
							index := DL
						END;
						FreeRegister(index);
					ELSE
						index := registerAllocator.NextFree(type.sizeInBits);
					END;
					IF index = none THEN
						index := NextFree();
						realRegisters[reg].lowSpilled := TRUE;
						realRegisters[reg].low := index;
						realRegisters[reg].high := none;
						realRegisters[reg].highSpilled := FALSE;
						spillStack[index] := reg;
						spillStackOperand[index] := Assembler.NewMem(SHORT(type.sizeInBits DIV 8),BP, -(spillStackStart + 4 + index*4));

						IF dump # NIL THEN
							dump.String("acquire register "); dump.Int(reg,1); dump.String("(low, virtual)  : "); dump.Int(index,1); dump.Ln;
						END;
					ELSE

						realRegisters[reg].lowSpilled := FALSE;
						realRegisters[reg].low := index;
						registerAllocator.Allocate(index,reg);
						realRegisters[reg].high := none;
						realRegisters[reg].highSpilled := FALSE;
						IF dump # NIL THEN
							dump.String("acquire register "); dump.Int(reg,1); dump.String("(low)  : "); dump.String(InstructionSet.registers[index].name); dump.Ln;
						END;
					END;
				END;
			ELSIF reg # IntermediateCode.Result THEN
				(*! think about move assumption, cf. method Mov *)
				index := fpStackPointer+1;
				fpRegisters[reg] := index;
				fpMapped[index] := reg;
				Assert(fpStackPointer < 8,"not enough fp registers");
				IF dump # NIL THEN
					dump.String("acquire register "); dump.Int(reg,1); dump.String("(fp)  : "); dump.Int(fpRegisters[reg],1); dump.Ln;
				END;
			END;
			registerType[reg] := type;
		END MapVirtualRegister;


		PROCEDURE ReleaseFPRegister(reg: LONGINT);
		VAR index,exchangeReg: LONGINT;
		BEGIN
			IF dump # NIL THEN
				dump.String("release register "); dump.Int(reg,1); dump.String("(fp)  : "); dump.Int(fpRegisters[reg],1); dump.Ln;
				(* dump.String("stack pointer is at "); dump.Int(fpStackPointer,1); dump.Ln; *)
			END;
			index := -fpRegisters[reg]+fpStackPointer;
			IF index =0 THEN (* must pop it from stack now *)
				emitter.Emit1(InstructionSet.opFFREE,opST0);
				emitter.Emit0(InstructionSet.opFINCSTP);
				DEC(fpStackPointer);
			ELSIF index >0 THEN (* not on top of stack, we must shuffle around and remap registers *)
				exchangeReg := fpMapped[fpStackPointer]; (* on top of stack *)
				emitter.Emit1(InstructionSet.opFXCH, registerOperands[ST0+index]);
				fpRegisters[exchangeReg] := fpRegisters[reg];
				fpMapped[fpRegisters[reg]] := exchangeReg;

				emitter.Emit1(InstructionSet.opFFREE,opST0);
				emitter.Emit0(InstructionSet.opFINCSTP);
				DEC(fpStackPointer);
			ELSIF reg # IntermediateCode.Result THEN
				Error("compiler implementation error: fp register already released?");
				(*!
				Halt("fp allocation problem: register already released?")
				*)
			END;
		END ReleaseFPRegister;

		PROCEDURE TransferRegister(from,to: LONGINT);
		VAR reg: LONGINT;
		BEGIN
			realRegisters[to] := realRegisters[from];

			reg := realRegisters[to].low;
			IF reg > 0 THEN
				IF realRegisters[to].lowSpilled THEN
					spillStack[reg] := to;
				ELSE
					registerAllocator.realToVirtual[reg] := to;
				END;
			END;
			reg := realRegisters[to].high;
			IF reg > 0 THEN
				IF realRegisters[to].highSpilled THEN
					spillStack[reg] := to;
				ELSE
					registerAllocator.realToVirtual[reg] := to;
				END;
			END;

			realRegisters[from].low := none;
			realRegisters[from].high := none;
			realRegisters[from].lowSpilled := FALSE;
			realRegisters[from].highSpilled := FALSE;
			registerType[to] := registerType[from];
			EXCL(currentlyUsed, from);
		END TransferRegister;

		PROCEDURE UnmapVirtualRegister(reg: LONGINT);
		VAR type: IntermediateCode.Type;
		BEGIN
			type := registerType[reg];
			IF type.form IN IntermediateCode.Integer THEN
				IF realRegisters[reg].lowSpilled THEN
					IF dump # NIL THEN
						dump.String("release register "); dump.Int(reg,1); dump.String("(spilled) : "); dump.Int(realRegisters[reg].low,1); dump.Ln;
					END;
					spillStack[realRegisters[reg].low] := none;
					realRegisters[reg].low := none;
					realRegisters[reg].lowSpilled := FALSE;
				ELSE
					IF dump # NIL THEN
						dump.String("release register "); dump.Int(reg,1); dump.String("(low) : "); dump.String(InstructionSet.registers[realRegisters[reg].low].name); dump.Ln;
					END;
					registerAllocator.Free(realRegisters[reg].low);
					realRegisters[reg].low := none;
				END;

				IF realRegisters[reg].high # none THEN
					IF realRegisters[reg].highSpilled THEN
						IF dump # NIL THEN
							dump.String("release register "); dump.Int(reg,1); dump.String("(spilled) : "); dump.Int(realRegisters[reg].high,1); dump.Ln;
						END;
						spillStack[realRegisters[reg].high] := none;
						realRegisters[reg].high := none;
						realRegisters[reg].highSpilled := FALSE;
					ELSE
						IF dump # NIL THEN
							dump.String("release register "); dump.Int(reg,1); dump.String("(high) : "); dump.String(InstructionSet.registers[realRegisters[reg].high].name);  dump.Ln;
						END;
						registerAllocator.Free(realRegisters[reg].high);
						realRegisters[reg].high := none;
					END;
				END;
			ELSE
				IF (reg IN toBeReleased) & (reg # IntermediateCode.Result) THEN (* otherwise already released *)
					ReleaseFPRegister(reg);
				END
			END;
			EXCL(toBeReleased,reg);
			lastUse[reg] := -1;
		END UnmapVirtualRegister;

		PROCEDURE Generate(CONST instr: IntermediateCode.Instruction);
		VAR opcode: SHORTINT; i: LONGINT;
		BEGIN
			numberTemporary := 0;
			opcode := instr.opcode;
			CASE opcode OF
			IntermediateCode.nop: (* do nothing *)
			|IntermediateCode.mov: EmitMov(instr);
			|IntermediateCode.conv: EmitConv(instr);
			|IntermediateCode.call: EmitCall(instr);
			|IntermediateCode.enter: EmitEnter(instr);
			|IntermediateCode.leave: EmitLeave(instr);
			|IntermediateCode.return: EmitReturn(instr);
			|IntermediateCode.trap: EmitTrap(instr);
			|IntermediateCode.br .. IntermediateCode.brlt: EmitBr(instr)
			|IntermediateCode.pop: EmitPop(instr);
			|IntermediateCode.push: EmitPush(instr);
			|IntermediateCode.neg: EmitNeg(instr);
			|IntermediateCode.not: EmitNot(instr);
			|IntermediateCode.abs: EmitAbs(instr);
			|IntermediateCode.mul: EmitMul(instr);
			|IntermediateCode.div: EmitDiv(instr);
			|IntermediateCode.mod: EmitMod(instr);
			|IntermediateCode.sub: EmitSub(instr);
			|IntermediateCode.add: EmitAdd(instr);
			|IntermediateCode.and: EmitAnd(instr);
			|IntermediateCode.or: EmitOr(instr);
			|IntermediateCode.xor: EmitXor(instr);
			|IntermediateCode.shl: EmitShift(instr);
			|IntermediateCode.shr: EmitShift(instr);
			|IntermediateCode.rol: EmitShift(instr);
			|IntermediateCode.ror: EmitShift(instr);
			|IntermediateCode.copy: EmitCopy(instr);
			|IntermediateCode.fillup: EmitFill(instr,FALSE);
			|IntermediateCode.filldown: EmitFill(instr,TRUE);
			|IntermediateCode.asm: EmitAsm(instr);
			|IntermediateCode.data: EmitData(instr);
			|IntermediateCode.reserve: EmitReserve(instr);
			|IntermediateCode.label: EmitLabel(instr);
			END;

			WHILE numberTemporary > 0 DO
				DEC(numberTemporary);
				registerAllocator.Free(temporary[numberTemporary]);
			END;

			FOR i := 0 TO LEN(registerAllocator.realToVirtual)-1 DO
				IF registerAllocator.realToVirtual[i] = reserved THEN (* temporarily reserved register *)
					registerAllocator.Free(i);
				END;
			END;
		END Generate;

		PROCEDURE Enter(size: LONGINT);
		VAR op1,op2,imm: Assembler.Operand;
		CONST initialize=TRUE;
		BEGIN
			IF TRUE (* OR  size > MAX(INTEGER) DIV 2  *) THEN
				emitter.Emit1(InstructionSet.opPUSH,opBP);
				emitter.Emit2(InstructionSet.opMOV,opBP,opSP);
				IF initialize THEN
					ASSERT(size MOD opA.sizeInBytes = 0);
					size := size DIV opA.sizeInBytes;
					IF size >0  THEN
						emitter.Emit2(InstructionSet.opXOR,opA,opA);
						WHILE size MOD 4 #0 DO
							emitter.Emit1(InstructionSet.opPUSH, opA);
							DEC(size);
						END;
						IF size >4 THEN
							Assembler.InitImm(imm, Assembler.bits32, size DIV 4);
							emitter.Emit2(InstructionSet.opMOV, opECX, imm);
							emitter.Emit1(InstructionSet.opDEC, opECX);
							emitter.Emit1(InstructionSet.opPUSH, opA);
							emitter.Emit1(InstructionSet.opPUSH, opA);
							emitter.Emit1(InstructionSet.opPUSH, opA);
							emitter.Emit1(InstructionSet.opPUSH, opA);
							Assembler.InitImm(imm, Assembler.bits8, -7);
							emitter.Emit1(InstructionSet.opJNZ, imm)
						ELSE
							WHILE size >0  DO
								emitter.Emit1(InstructionSet.opPUSH, opEAX);
								DEC(size);
							END;
						END;
					END;
					IF spillStackSize >0 THEN
						op1 := Assembler.NewImm32(spillStackSize*4);
						emitter.Emit2(InstructionSet.opSUB,opSP,op1);
					END;
				ELSE
					op1 := Assembler.NewImm32(size);
					emitter.Emit2(InstructionSet.opSUB,opSP,op1);
				END;
			ELSE
				op1 := Assembler.NewImm16(size);
				op2 := Assembler.NewImm8(0);
				emitter.Emit2(InstructionSet.opENTER,op1,op2);
			END;
		END Enter;

		PROCEDURE EmitEnter(CONST instr: IntermediateCode.Instruction);
		VAR cc: LONGINT;
		BEGIN
			cc := SHORT(instr.op1.intValue);
			stackSize := SHORT(instr.op2.intValue);
			enterPos := emitter.code.pc;
			Enter((stackSize ));

			IF cc = SyntaxTree.WinAPICallingConvention THEN (* the winapi calling convention presumes that all registers except EAX, EDX and ECX are retained by the callee *)
				emitter.Emit1(InstructionSet.opPUSH,opEBX);
				emitter.Emit1(InstructionSet.opPUSH,opEDI);
				emitter.Emit1(InstructionSet.opPUSH,opESI);
			END;
			(*spillStackSize := 0;*)
			spillStackStart := (stackSize );
		END EmitEnter;

		PROCEDURE PatchEnter;
		VAR pc: LONGINT;
		BEGIN
			RETURN;
			IF spillStackSize > 0 THEN
				pc := emitter.StartEmitAt(enterPos);
				Enter((stackSize )+spillStackSize*4);
				emitter.EndEmitAt(pc);
			END;
		END PatchEnter;

		PROCEDURE EmitLeave(CONST instr: IntermediateCode.Instruction);
		VAR cc: LONGINT;
		BEGIN
			cc := SHORT(instr.op1.intValue);
			IF cc = SyntaxTree.WinAPICallingConvention THEN
				emitter.Emit1(InstructionSet.opPOP,opESI);
				emitter.Emit1(InstructionSet.opPOP,opEDI);
				emitter.Emit1(InstructionSet.opPOP,opEBX);
			END;

			emitter.Emit2(InstructionSet.opMOV,opSP,opBP);
			emitter.Emit1(InstructionSet.opPOP,opBP);
			(*
			emitter.Emit0(InstructionSet.opLEAVE);
			*)
		END EmitLeave;

		PROCEDURE EmitReturn(CONST instr: IntermediateCode.Instruction);
		VAR operand: Assembler.Operand; fpsp: LONGINT;
		BEGIN
			fpsp := fpStackPointer;
			IF fpStackPointer # 0 THEN Error("compiler implementation error: fp stack not cleared") END;
			(*! Assert(fpStackPointer = 0,"fp stack not cleared"); *)
			IF instr.op1.intValue = 0 THEN (* parsize *)
				emitter.Emit0(InstructionSet.opRET);
			ELSE
				operand := Assembler.NewImm16(instr.op1.intValue );
				emitter.Emit1(InstructionSet.opRET,operand)
			END
		END EmitReturn;

		PROCEDURE GetDataSection(): IntermediateCode.Section;
		VAR name: SyntaxTree.String; section: IntermediateCode.Section;
		BEGIN
			Global.GetModuleName(module.module,name);
			Strings.Append(name,".");
			Strings.Append(name,"@Immediates");
			section := IntermediateCode.NewSection(module.sections,Sections.ConstSection,name,NIL,TRUE);
			RETURN section
		END GetDataSection;

		PROCEDURE GetImmediateMem(CONST vop: IntermediateCode.Operand; VAR imm: Operand);
		VAR data: IntermediateCode.Section;pc: LONGINT;
		BEGIN
			data := GetDataSection();
			pc := IntermediateBackend.EnterImmediate(data,vop);
			Assembler.InitMem(imm.low, SHORT(vop.type.sizeInBits DIV 8) , Assembler.none,0);
			Assembler.SetSymbol(imm.low,data,pc,0);
		END GetImmediateMem;

		PROCEDURE MakeOperand(CONST vop: IntermediateCode.Operand; VAR rop: Operand; sizeInBits: INTEGER; thisregister: LONGINT);
		VAR virtualReg, realReg, tempReg: LONGINT; tmp,imm: Assembler.Operand; i: LONGINT;
		BEGIN
			Assembler.InitOperand(rop.high);
			IF sizeInBits = 0 THEN sizeInBits := vop.type.sizeInBits END;
			IF (bits=32) & (sizeInBits = IntermediateCode.Bits64) & (vop.type.form # IntermediateCode.Float) THEN sizeInBits := IntermediateCode.Bits32 END;
			CASE vop.mode OF
			IntermediateCode.ModeMemory:
				IF vop.register # IntermediateCode.None THEN
					UnSpill(vop.register,none,none);
					virtualReg := vop.register;
					IF virtualReg = IntermediateCode.FP THEN realReg := BP;
					ELSIF virtualReg = IntermediateCode.SP THEN  realReg := SP;
					ELSE realReg := realRegisters[virtualReg].low;
					END;
					Assembler.InitMem(rop.low,SHORT(sizeInBits DIV 8) , realReg,(vop.offset ));
					IF (bits=32) & (vop.type.sizeInBits = IntermediateCode.Bits64) THEN
						Assembler.InitMem(rop.high,SHORT(sizeInBits DIV 8) , realReg,(vop.offset )+4);
					END;
				ELSIF vop.symbol # NIL THEN
					Assembler.InitMem(rop.low,SHORT(sizeInBits DIV 8) , Assembler.none,0);
					Assembler.SetSymbol(rop.low,vop.symbol,vop.symbolOffset,vop.offset);
					IF (bits=32) & (vop.type.form # IntermediateCode.Float) & (vop.type.sizeInBits = IntermediateCode.Bits64) THEN
						Assembler.InitMem(rop.high,SHORT(sizeInBits DIV 8) , Assembler.none,0);
						Assembler.SetSymbol(rop.high,vop.symbol,vop.symbolOffset,vop.offset+4);
					END;
				ELSE (* immediate memory operand, for example in SYSTEM.GET(0400H,var) *)
					Assembler.InitMem(rop.low,SHORT(sizeInBits DIV 8) , Assembler.none,SHORT(vop.intValue));
				END;
				IF (thisregister # none) THEN
					ASSERT(sizeInBits DIV 8  = registerOperands[thisregister].sizeInBytes);
					tmp := registerOperands[thisregister];
					emitter.Emit2(InstructionSet.opMOV, tmp,rop.low);
					rop.low := tmp;
				END;
			|IntermediateCode.ModeRegister:
				IF vop.type.form IN IntermediateCode.Integer THEN
					IF (vop.register > 0) & (vop.register < IntermediateCode.Result) THEN
						IF realRegisters[vop.register].lowSpilled THEN
							realReg := realRegisters[vop.register].low;
							rop.low := spillStackOperand[realReg];
							realReg := spillStackOperand[realReg].register;
						ELSE
							realReg := realRegisters[vop.register].low;
							rop.low := registerOperands[realReg];
						END
					ELSIF vop.register = IntermediateCode.FP THEN
						realReg := BP;
						rop.low := opBP;
					ELSIF vop.register = IntermediateCode.SP THEN
						realReg := SP;
						rop.low := opSP;
					ELSIF vop.register = IntermediateCode.Result THEN
						IF (bits=64) & (vop.type.sizeInBits = IntermediateCode.Bits64) THEN
							realReg := RAX;
							rop.low := registerOperands[RAX]
						ELSIF (vop.type.sizeInBits = IntermediateCode.Bits32) OR (vop.type.sizeInBits = IntermediateCode.Bits64) THEN
							realReg := EAX;
							rop.low := opEAX
						ELSIF vop.type.sizeInBits = IntermediateCode.Bits16 THEN
							realReg := AX;
							rop.low := opAX
						ELSIF vop.type.sizeInBits = IntermediateCode.Bits8 THEN
							realReg := AL;
							rop.low := opAL
						ELSE
							Halt("unsupported result register size");
						END;
					ELSIF vop.register = IntermediateCode.Result2 THEN
						ASSERT(vop.type.sizeInBits <= IntermediateCode.Bits32);
						IF (vop.type.sizeInBits = IntermediateCode.Bits64) THEN
							realReg := RDX;
							rop.low := registerOperands[RDX]
						ELSIF (vop.type.sizeInBits = IntermediateCode.Bits32) THEN
							realReg := EDX;
							rop.low := opEDX
						ELSIF vop.type.sizeInBits = IntermediateCode.Bits16 THEN
							realReg := DX;
							rop.low := opDX
						ELSIF vop.type.sizeInBits = IntermediateCode.Bits8 THEN
							realReg := DL;
							rop.low := opDL
						ELSE
							Halt("unsupported result register size");
						END;
					ELSE Halt("invalid register index");
					END;

					IF vop.offset # 0 THEN
						Assert((bits=64) OR (sizeInBits # IntermediateCode.Bits64),"forbidden offset on 64 bit register");
						IF thisregister = none THEN
							tempReg := TrySpill(sizeInBits);
							registerAllocator.Allocate(tempReg,reserved);
							temporary[numberTemporary] := tempReg; INC(numberTemporary);
						ELSE
							ASSERT(sizeInBits DIV 8 = registerOperands[thisregister].sizeInBytes);
							tempReg := thisregister
						END;
						tmp := registerOperands[tempReg];
						IF ~((vop.register > 0) & realRegisters[vop.register].lowSpilled) &  (sizeInBits = IntermediateCode.Bits32) THEN
							ASSERT(realReg # 0);
							Assembler.InitMem(rop.low,SHORT(sizeInBits DIV 8) ,realReg,(vop.offset ));
							emitter.Emit2(InstructionSet.opLEA, tmp,rop.low);
						ELSE
							emitter.Emit2(InstructionSet.opMOV,tmp,rop.low);
							IF sizeInBits=64 THEN
							Assembler.InitImm(imm,(32 DIV 8) ,vop.offset);
							ELSE
							Assembler.InitImm(imm,SHORT(sizeInBits DIV 8) ,vop.offset);
							END;
							emitter.Emit2(InstructionSet.opADD,tmp,imm);
						END;
						rop.low := tmp;
					ELSIF (thisregister # none) THEN
						ASSERT(sizeInBits DIV 8 = registerOperands[thisregister].sizeInBytes);
						tmp := registerOperands[thisregister];
						emitter.Emit2(InstructionSet.opMOV, tmp,rop.low);
						rop.low := tmp;
					END;

					IF (bits=32) & (vop.type.sizeInBits = IntermediateCode.Bits64) THEN
						IF (vop.register > 0) & (vop.register < IntermediateCode.Result) THEN
							IF realRegisters[vop.register].highSpilled THEN
								realReg := realRegisters[vop.register].high;
								rop.high := spillStackOperand[realReg];
							ELSE
								realReg := realRegisters[vop.register].high;
								rop.high := registerOperands[realReg];
							END;
						ELSIF vop.register = IntermediateCode.Result THEN
							rop.high := opEDX;
						ELSIF vop.register = IntermediateCode.Result2 THEN
							HALT(101)
						ELSE HALT(100)
						END;
					END;
				ELSE
					IF vop.register = IntermediateCode.Result THEN
						realReg := fpStackPointer;
						rop.low := registerOperands[ST0+realReg];
					ELSE
						realReg := -fpRegisters[vop.register]+fpStackPointer;
						rop.low := registerOperands[ST0+realReg];
					END;
				END;
			|IntermediateCode.ModeImmediate:
				IF vop.type.form IN IntermediateCode.Integer THEN
					IF (bits=32) & (vop.type.sizeInBits # IntermediateCode.Bits64) THEN
						Assembler.InitImm(rop.low,SHORT(sizeInBits DIV 8) ,vop.intValue);
						Assembler.SetSymbol(rop.low,vop.symbol,vop.symbolOffset,vop.offset);
					ELSE
						Assembler.InitImm(rop.low,SHORT(sizeInBits DIV 8) ,(vop.intValue));
						Assembler.SetSymbol(rop.low,vop.symbol,vop.symbolOffset,vop.offset);
						Assembler.InitImm(rop.high,SHORT(sizeInBits DIV 8) ,SHORT(vop.intValue DIV 10000H DIV 10000H));
						Assembler.SetSymbol(rop.high,vop.symbol,vop.symbolOffset, vop.offset+4);
					END;
				ELSE
					GetImmediateMem(vop,rop);
				END;
				IF (thisregister # none) THEN
					ASSERT(sizeInBits DIV 8 = registerOperands[thisregister].sizeInBytes);
					tmp := registerOperands[thisregister];
					emitter.Emit2(InstructionSet.opMOV, tmp,rop.low);
					rop.low := tmp;
				END;
			END;
		END MakeOperand;

		PROCEDURE TrySpill(sizeInBits: LONGINT): SHORTINT;
		VAR tempReg: SHORTINT; i: LONGINT;
		BEGIN
			tempReg := registerAllocator.NextFree(sizeInBits);
			i := 0;
			WHILE tempReg = none DO
				IF ~(i IN currentlyUsed) (* does implicitly not free locally reserved registers as they refer to reserved < 0 *) THEN
					Spill(i);
					tempReg := registerAllocator.NextFree(sizeInBits);
				END;
				INC(i);
			END;
			RETURN tempReg
		END TrySpill;

		(* allocate temporary operand using EAX and EDX registers *)
		PROCEDURE Temporary(sizeInBits: LONGINT; VAR op: Operand);
		VAR register: LONGINT;
		BEGIN
			IF (sizeInBits < IntermediateCode.Bits64) OR (bits=64)  THEN
				Assembler.InitOperand(op.high);
				register := registerAllocator.NextFree(sizeInBits);
				IF register = none THEN
					register := TrySpill(sizeInBits);
				END;
				ASSERT(register # none);
				op.low := registerOperands[register];
				registerAllocator.Allocate(register, reserved);
			ELSE
				register := registerAllocator.NextFree(32);
				IF register = none THEN
					register := TrySpill(32);
				END;
				ASSERT(register # none);
				op.low := registerOperands[register];
				registerAllocator.Allocate(register, reserved);
				register := registerAllocator.NextFree(32);
				IF register = none THEN
					register := TrySpill(32);
				END;
				ASSERT(register # none);
				op.high := registerOperands[register];
				registerAllocator.Allocate(register, reserved);
			END;
			(*
			IF sizeInBits = IntermediateCode.Bits64 THEN
				op.low := opEAX;
				op.high := opEDX;
			ELSIF sizeInBits = IntermediateCode.Bits32 THEN
				op.low := opEAX;
				Assembler.InitOperand(op.high);
			ELSIF sizeInBits = IntermediateCode.Bits16 THEN
				op.low := opAX;
				Assembler.InitOperand(op.high);
			ELSIF sizeInBits = IntermediateCode.Bits8 THEN
				op.low := opAL;
				Assembler.InitOperand(op.high);
			END
			*)
		END Temporary;

		(* 8 / 16 / 32 / 64 bit move, may destroy EAX by use of temporary *)
		PROCEDURE Mov(op: LONGINT; dest,src: Operand);
		VAR temp: Operand;
		BEGIN
			IF Assembler.IsRegisterOperand(dest.low) OR Assembler.IsRegisterOperand(src.low) THEN
				emitter.Emit2(op,dest.low,src.low);
			ELSE
				Temporary(dest.low.sizeInBytes*8,temp);
				emitter.Emit2(op,temp.low,src.low);
				emitter.Emit2(InstructionSet.opMOV,dest.low,temp.low);
				registerAllocator.Free(temp.low.register);
			END;

			IF  (src.high.type # Assembler.none) & (dest.high.type # Assembler.none) THEN
				IF Assembler.IsRegisterOperand(dest.high) OR Assembler.IsRegisterOperand(src.high) THEN
					emitter.Emit2(op,dest.high,src.high);
				ELSE
					Temporary(dest.high.sizeInBytes*8,temp);
					emitter.Emit2(op,temp.low,src.high);
					emitter.Emit2(InstructionSet.opMOV,dest.high,temp.low);
					registerAllocator.Free(temp.low.register);
				END;
			END;

		END Mov;

		PROCEDURE AllocateStack(sizeInBytes: LONGINT);
		VAR sizeOp: Assembler.Operand; opcode: LONGINT;
		BEGIN
			IF sizeInBytes < 0 THEN
				sizeInBytes := -sizeInBytes; opcode := InstructionSet.opADD;
			ELSIF sizeInBytes > 0 THEN
				opcode := InstructionSet.opSUB;
			ELSE RETURN
			END;
			IF sizeInBytes < 128 THEN sizeOp := Assembler.NewImm8(sizeInBytes);
			ELSE sizeOp := Assembler.NewImm32(sizeInBytes);
			END;
			emitter.Emit2(opcode,opSP,sizeOp);
		END AllocateStack;

		(*
		PROCEDURE AddOffset(op: Assembler.Operand; offset: LONGINT);
		VAR imm: Assembler.Operand;
		BEGIN
			Assembler.InitImm(imm,op.sizeInBytes,offset);
			emitter.Emit2(InstructionSet.opADD,op,imm);
		END AddOffset;
		*)
		PROCEDURE IsMemoryOperand(vop: IntermediateCode.Operand): BOOLEAN;
		VAR r: LONGINT;
		BEGIN
			r := vop.register;
			RETURN (vop.mode = IntermediateCode.ModeMemory) OR (vop.mode = IntermediateCode.ModeRegister) & (vop.register >= 0)
				& ((realRegisters[vop.register].lowSpilled) OR (realRegisters[vop.register].highSpilled));
		END IsMemoryOperand;


		PROCEDURE EmitMov(CONST instr: IntermediateCode.Instruction);
		VAR op1,op2: Operand; tmp: IntermediateCode.Operand;
		BEGIN
			IF instr.op1.type.form IN IntermediateCode.Integer THEN
				MakeOperand(instr.op1,op1,0,none);
				IF IsMemoryOperand(instr.op1) & IsMemoryOperand(instr.op2) THEN
					MakeOperand(instr.op2,op2,0,none);
					Mov(InstructionSet.opMOV,op1,op2);
				ELSIF (instr.op1.mode = IntermediateCode.ModeRegister) & (instr.op2.mode = IntermediateCode.ModeRegister) & (instr.op2.offset # 0) THEN
					tmp := instr.op2; IntermediateCode.MakeMemory(tmp,instr.op2.type);
					MakeOperand(tmp,op2,0,none);
					emitter.Emit2(InstructionSet.opLEA,op1.low,op2.low);
					IF (bits =32) & (instr.op1.type.sizeInBits = IntermediateCode.Bits64) THEN
						emitter.Emit2(InstructionSet.opLEA,op1.high,op2.high);
					END;
				ELSE
					MakeOperand(instr.op2,op2,0,none);
					emitter.Emit2(InstructionSet.opMOV,op1.low,op2.low);
					IF (bits=32) & (instr.op1.type.sizeInBits = IntermediateCode.Bits64) THEN
						emitter.Emit2(InstructionSet.opMOV,op1.high,op2.high);
					END;
				END;
			ELSE
				(*
					the following code is written under the assumption that the result of a procedure is always written to before a return instruction and
					it is read after a call and potential pops of registers (fp or not) from stack.
						MOV #result, src is always the last (floating point relevant) instruction before exiting a procedure
						MOV src, #result is always the first (floating point relevant) instruction after a return from a procedure call
											(except for POPs which may modify the FP stack but they leave the stack bottom untouched)
				*)
				MakeOperand(instr.op2,op2,0,none);
				emitter.Emit1(InstructionSet.opFLD,op2.low);
				INC(fpStackPointer);

				IF (instr.op1.mode # IntermediateCode.ModeRegister) OR (instr.op1.register = IntermediateCode.Result) OR (-fpRegisters[instr.op1.register]+fpStackPointer # 0) THEN
					MakeOperand(instr.op1,op1,0,none);
					emitter.Emit1(InstructionSet.opFSTP,op1.low);
					DEC(fpStackPointer);
				ELSE (* result may stay on top of stack, op1 has been allocated in place *)
				END;

				IF (instr.op2.mode = IntermediateCode.ModeRegister) & (instr.op2.register = IntermediateCode.Result) THEN
					(* result must be removed from stack, as it is on the bottom of stack it can be just freed without further manipulation *)
					IF dump # NIL THEN dump.String("free result on fp stack"); dump.Ln; END;
					 emitter.Emit1(InstructionSet.opFFREE,registerOperands[ST0+fpStackPointer]);
				END;


			END
		END EmitMov;

		PROCEDURE EmitConv(CONST instr: IntermediateCode.Instruction);
		VAR destType, srcType: IntermediateCode.Type; op1,op2: Operand; index: LONGINT; nul,espm,imm: Assembler.Operand; sizeInBytes: LONGINT;
		temp: Operand;
		BEGIN
			srcType := instr.op2.type;
			destType := instr.op1.type;
			CASE destType.form OF
			IntermediateCode.SignedInteger, IntermediateCode.UnsignedInteger:
				CASE srcType.form OF
				IntermediateCode.SignedInteger, IntermediateCode.UnsignedInteger:
					IF destType.sizeInBits < srcType.sizeInBits THEN (* (implicit) SHORT *)
						MakeOperand(instr.op1,op1,0,none);
						MakeOperand(instr.op2,op2,0,none);
						index := op1.low.register;
						CASE srcType.sizeInBits OF
							IntermediateCode.Bits16: index := index MOD 32 + AX;
							|IntermediateCode.Bits32: index := index MOD 32 + EAX;
							|IntermediateCode.Bits64: index := index MOD 32 + EAX;
						END;
						emitter.Emit2(InstructionSet.opMOV,registerOperands[index],op2.low);
					ELSIF destType.sizeInBits > srcType.sizeInBits THEN
						IF srcType.form = IntermediateCode.SignedInteger THEN (* destType.sizeInBits > srcType.sizeInBits *)  (* (implicit) LONG *)
							MakeOperand(instr.op1,op1,0,none);
							MakeOperand(instr.op2,op2,0,none);
							IF (destType.sizeInBits = IntermediateCode.Bits64)  THEN
								IF srcType.sizeInBits = IntermediateCode.Bits32 THEN
									Mov(InstructionSet.opMOV,op1,op2);
								ELSE
									IF IsMemoryOperand(instr.op1) THEN
										Temporary(destType.sizeInBits,temp);
										(*
										CASE destType.sizeInBits OF
											IntermediateCode.Bits16: index :=AX;
											|IntermediateCode.Bits32: index :=EAX;
										END;
										*)
										emitter.Emit2(InstructionSet.opMOVSX,temp.low,op2.low);
										emitter.Emit2(InstructionSet.opMOV,op1.low,temp.low);
										registerAllocator.Free(temp.low.register);
									ELSE
										Mov(InstructionSet.opMOVSX,op1,op2);
									END;
								END;

								IF (registerAllocator.realToVirtual[EAX] # free)  & (EAX # op1.low.register) THEN
									emitter.Emit1(InstructionSet.opPUSH,opEAX);
								END;
								IF (registerAllocator.realToVirtual[EDX] # free)  & (EDX # op1.high.register)  THEN
									emitter.Emit1(InstructionSet.opPUSH,opEDX)
								END;
								emitter.Emit2(InstructionSet.opMOV,opEAX,op1.low);
								emitter.Emit0(InstructionSet.opCDQ);
								emitter.Emit2(InstructionSet.opMOV,op1.high,opEDX);
								IF (registerAllocator.realToVirtual[EDX] # free)  & (EDX # op1.high.register)  THEN
									emitter.Emit1(InstructionSet.opPOP,opEDX)
								END;
								IF (registerAllocator.realToVirtual[EAX] # free)  & (EAX # op1.low.register) THEN
									emitter.Emit1(InstructionSet.opPOP,opEAX);
								END;
							ELSE
								IF IsMemoryOperand(instr.op1) THEN
									(*
									CASE destType.sizeInBits OF
										IntermediateCode.Bits16: index :=AX;
										|IntermediateCode.Bits32: index :=EAX;
									END;
									*)
									Temporary(destType.sizeInBits,temp);
									emitter.Emit2(InstructionSet.opMOVSX,temp.low,op2.low);
									emitter.Emit2(InstructionSet.opMOV,op1.low,temp.low);
								ELSE
									Mov(InstructionSet.opMOVSX,op1,op2);
								END;
							END;
						ELSE
							MakeOperand(instr.op1,op1,0,none);
							MakeOperand(instr.op2,op2,0,none);
							IF (destType.sizeInBits = IntermediateCode.Bits64)  THEN
								IF srcType.sizeInBits = IntermediateCode.Bits32 THEN
									emitter.Emit2(InstructionSet.opMOV,op1.low,op2.low);
								ELSE
									emitter.Emit2(InstructionSet.opMOVZX,op1.low,op2.low);
								END;

								IF (instr.op1.mode = IntermediateCode.ModeRegister) THEN
									emitter.Emit2(InstructionSet.opXOR,op1.high,op1.high)
								ELSE
									Assembler.InitImm(nul,IntermediateCode.Bits32,0);
									emitter.Emit2(InstructionSet.opMOV,op1.high,nul);
								END;
							ELSE
								Mov(InstructionSet.opMOVZX,op1,op2);
							END;
						END;
					ELSE
						MakeOperand(instr.op1,op1,0,none);
						MakeOperand(instr.op2,op2,0,none);
						IF (instr.op1.mode = instr.op2.mode) & (instr.op1.register = instr.op2.register) & (instr.op1.offset = instr.op2.offset) &
							(instr.op1.symbol = instr.op2.symbol) THEN
						ELSE
							Mov(InstructionSet.opMOV,op1,op2);
						END;
					END;
				|IntermediateCode.Float: (* entier *)
					MakeOperand(instr.op1,op1,0,none);
					MakeOperand(instr.op2,op2,0,none);
					emitter.Emit1(InstructionSet.opFLD,op2.low); INC(fpStackPointer);
					Assert(instr.op1.type.form = IntermediateCode.SignedInteger, "no entier as result for unsigned integer");
					IF destType.sizeInBits = IntermediateCode.Bits64 THEN AllocateStack(12) ELSE AllocateStack(8) END;

					Assembler.InitMem(espm,IntermediateCode.Bits16 DIV 8,SP,0);

					emitter.Emit1(InstructionSet.opFNSTCW,espm);
					emitter.Emit0(InstructionSet.opFWAIT);

					Assembler.InitMem(espm,IntermediateCode.Bits32 DIV 8,SP,0);
					Temporary(IntermediateCode.Bits32,temp);
					emitter.Emit2(InstructionSet.opMOV,temp.low,espm);
					imm := Assembler.NewImm32(0F3FFH);
					emitter.Emit2(InstructionSet.opAND,temp.low,imm);
					imm := Assembler.NewImm32(0400H);
					emitter.Emit2(InstructionSet.opOR,temp.low,imm);
					Assembler.InitMem(espm,IntermediateCode.Bits32 DIV 8,SP,4);
					emitter.Emit2(InstructionSet.opMOV,espm,temp.low);
					Assembler.InitMem(espm,IntermediateCode.Bits16 DIV 8,SP,4);
					emitter.Emit1(InstructionSet.opFLDCW,espm);
					IF destType.sizeInBits = IntermediateCode.Bits64 THEN
						Assembler.InitMem(espm,IntermediateCode.Bits64 DIV 8,SP,4);
						emitter.Emit1(InstructionSet.opFISTP,espm);DEC(fpStackPointer);
						emitter.Emit0(InstructionSet.opFWAIT);
					ELSE
						Assembler.InitMem(espm,IntermediateCode.Bits32 DIV 8,SP,4);
						emitter.Emit1(InstructionSet.opFISTP,espm); DEC(fpStackPointer);
						emitter.Emit0(InstructionSet.opFWAIT);
					END;
					Assembler.InitMem(espm,IntermediateCode.Bits16 DIV 8,SP,0);
					emitter.Emit1(InstructionSet.opFLDCW,espm);

					emitter.Emit1(InstructionSet.opPOP,temp.low);

					emitter.Emit1(InstructionSet.opPOP,op1.low);
					IF destType.sizeInBits = IntermediateCode.Bits64 THEN emitter.Emit1(InstructionSet.opPOP,op1.high);
					END;
				END;
			|IntermediateCode.Float:
				CASE srcType.form OF
				|IntermediateCode.Float: (* just a move *)
					MakeOperand(instr.op2,op2,0,none);
					emitter.Emit1(InstructionSet.opFLD,op2.low); INC(fpStackPointer);

					IF (instr.op1.mode # IntermediateCode.ModeRegister) OR (-fpRegisters[instr.op1.register]+fpStackPointer # 0) THEN
						MakeOperand(instr.op1,op1,0,none);
						emitter.Emit1(InstructionSet.opFSTP,op1.low);
						DEC(fpStackPointer);
					ELSE (* result may stay on top of stack, op1 has been allocated in place *)
					END;
				|IntermediateCode.SignedInteger:
					MakeOperand(instr.op2,op2,0,none);
					IF instr.op2.type.sizeInBits < IntermediateCode.Bits32 THEN
						Temporary(32,temp);
						emitter.Emit2(InstructionSet.opMOVSX,temp.low,op2.low);
						Push(temp);
						Assembler.InitMem(espm,IntermediateCode.Bits32 DIV 8,SP,0);
						sizeInBytes := 4
					ELSIF instr.op2.type.sizeInBits = IntermediateCode.Bits64 THEN
						emitter.Emit1(InstructionSet.opPUSH,op2.high);
						emitter.Emit1(InstructionSet.opPUSH,op2.low);
						Assembler.InitMem(espm,IntermediateCode.Bits64 DIV 8,SP,0);
						sizeInBytes := 8
					ELSE
						emitter.Emit1(InstructionSet.opPUSH,op2.low);
						Assembler.InitMem(espm,IntermediateCode.Bits32 DIV 8,SP,0);
						sizeInBytes := 4
					END;
					emitter.Emit1(InstructionSet.opFILD,espm);INC(fpStackPointer);
					AllocateStack(-sizeInBytes);

					IF (instr.op1.mode # IntermediateCode.ModeRegister) OR (-fpRegisters[instr.op1.register]+fpStackPointer # 0) THEN
						MakeOperand(instr.op1,op1,0,none);
						emitter.Emit1(InstructionSet.opFSTP,op1.low);
						DEC(fpStackPointer);
					ELSE (* result may stay on top of stack, op1 has been allocated in place *)
					END;
				END;
			END;
		END EmitConv;

		PROCEDURE EmitCall(CONST instruction: IntermediateCode.Instruction);
		VAR fixup: Sections.Section;  target: Assembler.Operand; op: Operand;
			code: SyntaxTree.Code; emitterFixup,newFixup: BinaryCode.Fixup; resolved: BinaryCode.Section; pc: LONGINT;
		BEGIN
			IF fpStackPointer # 0 THEN Error("compiler implementation error: fp stack not cleared before call") END;
			(*!
			Assert(fpStackPointer = 0,"fp stack not cleared before call");
			*)
			IF instruction.op1.mode = IntermediateCode.ModeImmediate THEN
				fixup := instruction.op1.symbol;
				IF fixup.type = Sections.InlineCodeSection THEN
					code := fixup.symbol(SyntaxTree.Procedure).procedureScope.body.code;
					pc := out.pc;
					IF code.inlineCode # NIL THEN
						emitter.code.CopyBits(code.inlineCode,0,code.inlineCode.GetSize());
					END;
					IF fixup(IntermediateCode.Section).resolved # NIL THEN
						resolved := fixup(IntermediateCode.Section).resolved;
						emitterFixup := resolved.fixupList.firstFixup;
						WHILE (emitterFixup # NIL) DO
							newFixup := BinaryCode.NewFixup(emitterFixup.mode,emitterFixup.offset+pc,emitterFixup.symbol,emitterFixup.symbolOffset,emitterFixup.displacement,emitterFixup.scale,emitterFixup.pattern);
							out.fixupList.AddFixup(newFixup);
							emitterFixup := emitterFixup.nextFixup;
						END;
					(* ELSE ok: imported inline code without fixups *)
					END;
				ELSE
					Assembler.InitOffset32(target,instruction.op1.intValue);
					Assembler.SetSymbol(target,fixup,instruction.op1.offset,0);
					emitter.Emit1(InstructionSet.opCALL,target);
				END;
			ELSE
				MakeOperand(instruction.op1,op,0,none);
				emitter.Emit1(InstructionSet.opCALL,op.low);
			END
		END EmitCall;

		PROCEDURE PrepareOp3(CONST instr: IntermediateCode.Instruction; VAR left,right: Operand);
		VAR op1,op2,op3: Operand; vop1,vop2,vop3: IntermediateCode.Operand;
		BEGIN
			vop1 := instr.op1; vop2 := instr.op2; vop3 := instr.op3;
			IF IntermediateCode.OperandEquals(vop1,vop3) & (IntermediateCode.Commute23 IN IntermediateCode.instructionFormat[instr.opcode].flags) THEN
				vop3 := instr.op2; vop2 := instr.op3;
			END;
			MakeOperand(vop1,op1,0,none);
			MakeOperand(vop3,op3,0,none);
			IF (vop1.mode = IntermediateCode.ModeRegister) & (~IsMemoryOperand(vop1)) & (vop1.register # vop3.register)  THEN
				IF (vop2.mode = IntermediateCode.ModeRegister) & (vop2.register = vop1.register) & (vop2.offset = 0) THEN
					(* same register *)
				ELSE
					MakeOperand(vop2,op2,0,none);
					Mov(InstructionSet.opMOV,op1,op2);
				END;
				left := op1; right := op3;
			ELSIF IntermediateCode.OperandEquals(vop1,vop2) & (~IsMemoryOperand(vop1) OR ~IsMemoryOperand(vop3)) THEN
				left := op1; right := op3;
			ELSE
				MakeOperand(vop2,op2,0,none);
				Temporary(vop1.type.sizeInBits,left);
				Mov(InstructionSet.opMOV,left,op2);
				right := op3;
			END;
		END PrepareOp3;

		PROCEDURE FinishOp3(CONST instr: IntermediateCode.Instruction; left: Operand);
		VAR op1: Operand; vop1,vop2,vop3: IntermediateCode.Operand;
		BEGIN
			vop1 := instr.op1; vop2 := instr.op2; vop3 := instr.op3;
			IF IntermediateCode.OperandEquals(vop1,vop3) & (IntermediateCode.Commute23 IN IntermediateCode.instructionFormat[instr.opcode].flags) THEN
				vop3 := instr.op2; vop2 := instr.op3;
			END;
			IF (vop1.mode = IntermediateCode.ModeRegister) & (~IsMemoryOperand(vop1)) &  (vop1.register # vop3.register)  THEN
			ELSIF IntermediateCode.OperandEquals(vop1,vop2)& (~IsMemoryOperand(vop1) OR ~IsMemoryOperand(vop3))  THEN
			ELSE
				MakeOperand(vop1,op1,0,none);
				Mov(InstructionSet.opMOV,op1,left);
			END;
		END FinishOp3;

		PROCEDURE ThreeOperandInstruction(CONST instr: IntermediateCode.Instruction; opLow,opHigh: LONGINT);
		VAR left,right: Operand;
		BEGIN
			PrepareOp3(instr,left,right);
			emitter.Emit2(opLow,left.low,right.low);
			IF left.high.type # Assembler.none THEN
				emitter.Emit2(opHigh,left.high,right.high);
			END;
			FinishOp3(instr,left);
		END ThreeOperandInstruction;

		PROCEDURE PrepareOp2(CONST instr: IntermediateCode.Instruction; VAR op: Operand);
		VAR op1,op2: Operand; imm: Assembler.Operand; sizeInBits: INTEGER;
		BEGIN
			MakeOperand(instr.op1,op1,0,none); MakeOperand(instr.op2,op2,0,none);
			IF (instr.op1.mode = IntermediateCode.ModeRegister) THEN
				IF (instr.op2.mode = IntermediateCode.ModeRegister) & (instr.op2.register = instr.op1.register) & (instr.op2.offset = 0) THEN
				ELSE
					Mov(InstructionSet.opMOV,op1,op2);
					IF (instr.op2.offset # 0) & ~IsMemoryOperand(instr.op2) THEN
						sizeInBits := instr.op2.type.sizeInBits;
						IF sizeInBits = IntermediateCode.Bits64 THEN sizeInBits := IntermediateCode.Bits32 END;
						Assembler.InitImm(imm,SHORT(sizeInBits DIV 8),instr.op2.offset);
						emitter.Emit2(InstructionSet.opADD,op1.low,imm);
					END;
				END;
				op := op1;
			ELSIF IntermediateCode.OperandEquals(instr.op1,instr.op2) & ((instr.op1.mode # IntermediateCode.ModeMemory) OR (instr.op3.mode # IntermediateCode.ModeMemory)) THEN
				op := op1;
			ELSE
				Temporary(instr.op1.type.sizeInBits,op);
				Mov(InstructionSet.opMOV,op,op2);
			END;
		END PrepareOp2;

		PROCEDURE FinishOp2(CONST instr: IntermediateCode.Instruction; op: Operand);
		VAR op1: Operand;
		BEGIN
			IF (instr.op1.mode = IntermediateCode.ModeRegister) THEN
			ELSIF IntermediateCode.OperandEquals(instr.op1,instr.op2) & ((instr.op1.mode # IntermediateCode.ModeMemory) OR (instr.op3.mode # IntermediateCode.ModeMemory)) THEN
			ELSE
				MakeOperand(instr.op1,op1,0,none);
				Mov(InstructionSet.opMOV,op1,op);
			END;
		END FinishOp2;

		PROCEDURE TwoOperandInstruction(CONST instr: IntermediateCode.Instruction; opLow,opHigh: LONGINT);
		VAR left: Operand;
		BEGIN
			PrepareOp2(instr,left);
			emitter.Emit1(opLow,left.low);
			IF left.high.type # Assembler.none THEN
				emitter.Emit1(opHigh,left.high);
			END;
			FinishOp2(instr,left);
		END TwoOperandInstruction;

		PROCEDURE ThreeOperandFPInstruction(CONST instr: IntermediateCode.Instruction; op: LONGINT);
		VAR op1,op2,op3: Operand;
		BEGIN
				MakeOperand(instr.op2,op2,0,none);
				emitter.Emit1(InstructionSet.opFLD,op2.low);
				INC(fpStackPointer);

				MakeOperand(instr.op3,op3,0,none);
				IF instr.op3.mode = IntermediateCode.ModeRegister THEN
					emitter.Emit2(op,opST0,op3.low);
				ELSE
					emitter.Emit1(op,op3.low);
				END;

				IF (instr.op1.mode # IntermediateCode.ModeRegister) OR (-fpRegisters[instr.op1.register]+fpStackPointer # 0) THEN
					MakeOperand(instr.op1,op1,0,none);
					emitter.Emit1(InstructionSet.opFSTP,op1.low);
					DEC(fpStackPointer);
				ELSE (* result may stay on top of stack, op1 has been allocated in place *)
				END;
		END ThreeOperandFPInstruction;

		PROCEDURE TwoOperandFPInstruction(CONST instr: IntermediateCode.Instruction; opcode: LONGINT);
		VAR op1,op2: Operand;
		BEGIN
			IF (instr.op1.mode = IntermediateCode.ModeRegister) & (instr.op2.mode = IntermediateCode.ModeRegister) &
				(instr.op1.register = instr.op2.register) & (-fpRegisters[instr.op1.register]+fpStackPointer = 0) (* src = dest and top of stack *)
			THEN emitter.Emit0(opcode);
			ELSE
				MakeOperand(instr.op2,op2,0,none);
				emitter.Emit1(InstructionSet.opFLD,op2.low);
				INC(fpStackPointer);
				emitter.Emit0(opcode);
				IF (instr.op1.mode # IntermediateCode.ModeRegister) OR (-fpRegisters[instr.op1.register]+fpStackPointer # 0) THEN
					MakeOperand(instr.op1,op1,0,none);
					emitter.Emit1(InstructionSet.opFSTP,op1.low);
					DEC(fpStackPointer);
				ELSE (* result may stay on top of stack, op1 has been allocated in place *)
				END;
			END;
		END TwoOperandFPInstruction;

		PROCEDURE EmitAdd(CONST instr: IntermediateCode.Instruction);
		BEGIN
			IF instr.op1.type.form IN IntermediateCode.Integer THEN
				ThreeOperandInstruction(instr,InstructionSet.opADD,InstructionSet.opADC);
			ELSE
				ThreeOperandFPInstruction(instr,InstructionSet.opFADD)
			END;
		END EmitAdd;

		PROCEDURE EmitSub(CONST instr: IntermediateCode.Instruction);
		BEGIN
			IF instr.op1.type.form IN IntermediateCode.Integer THEN
				ThreeOperandInstruction(instr,InstructionSet.opSUB,InstructionSet.opSBB);
			ELSE
				ThreeOperandFPInstruction(instr,InstructionSet.opFSUB)
			END;
		END EmitSub;

		PROCEDURE EmitMul(CONST instr: IntermediateCode.Instruction);
		VAR op1,op2,op3,temp: Operand;

			(*
			PROCEDURE IMul64(CONST instr: IntermediateCode.Instruction);
			VAR op1, op2, op3: Operand; op1Temp: Operand;
				virtual: LONGINT;
			BEGIN

				MakeOperand(instr.op1,op1,0,none);
				IF instr.op3.mode = IntermediateCode.ModeImmediate THEN
					MakeOperand(instr.op2,op3,0,none); MakeOperand(instr.op3,op2,0,none);
				ELSE
					MakeOperand(instr.op2,op2,0,none); MakeOperand(instr.op3,op3,0,none);
				END;
				virtual := registerAllocator.realToVirtual[EAX];
				IF (virtual # none) & (virtual # instr.op1.register) & (virtual # instr.op1.register) THEN
					emitter.Emit1(InstructionSet.opPUSH,opEAX);
				END;
				virtual := registerAllocator.realToVirtual[EDX];
				IF (virtual # none) & (virtual # instr.op1.register) & (virtual # instr.op1.register)THEN
					emitter.Emit1(InstructionSet.opPUSH,opEDX);
				END;
				emitter.Emit1(InstructionSet.opPUSH,op1.low);
				emitter.Emit1(InstructionSet.opPUSH,op1.high);
				Assembler.InitMem(op1Temp.low,IntermediateCode.Bits32 DIV 8,ESP,4);
				Assembler.InitMem(op1Temp.high,IntermediateCode.Bits32 DIV 8,ESP,0);
				emitter.Emit2(InstructionSet.opMOV,opEAX,op2.low);
				emitter.Emit1(InstructionSet.opMUL,op3.low);
				emitter.Emit2(InstructionSet.opMOV,op1Temp.low,opEAX);
				emitter.Emit2(InstructionSet.opMOV,op1Temp.high,opEDX);
				emitter.Emit2(InstructionSet.opMOV,opEAX,op2.low);
				emitter.Emit1(InstructionSet.opIMUL,op3.high);
				emitter.Emit2(InstructionSet.opADD,op1Temp.high,opEAX);
				emitter.Emit2(InstructionSet.opMOV,opEAX,op2.high);
				emitter.Emit1(InstructionSet.opIMUL,op3.low);
				emitter.Emit2(InstructionSet.opADD,op1Temp.high,opEAX);

				Mov(InstructionSet.opMOV,op1,op1Temp);
				AllocateStack(-8);

				virtual := registerAllocator.realToVirtual[EDX];
				IF (virtual # none) & (virtual # instr.op1.register) & (virtual # instr.op1.register) THEN
					emitter.Emit1(InstructionSet.opPOP,opEDX);
				END;
				virtual := registerAllocator.realToVirtual[EAX];
				IF (virtual # none) & (virtual # instr.op1.register) & (virtual # instr.op1.register)  THEN
					emitter.Emit1(InstructionSet.opPOP,opEAX);
				END;

			END IMul64;
			*)

		BEGIN
			IF (bits=32) & (instr.op1.type.form IN IntermediateCode.Integer) & (instr.op1.type.sizeInBits = IntermediateCode.Bits64) THEN
				HALT(100); (*! should be implemented by library *)
				(*IMul64(instr)*)
			ELSIF (instr.op1.type.form IN IntermediateCode.Integer) & (instr.op1.type.sizeInBits = IntermediateCode.Bits8) THEN
				MakeOperand(instr.op1,op1,0,none); MakeOperand(instr.op2,op2,0,none); MakeOperand(instr.op3,op3,0,none);
				emitter.Emit2(InstructionSet.opMOV,opAL,op2.low);
				IF instr.op3.mode = IntermediateCode.ModeImmediate THEN
					emitter.Emit2(InstructionSet.opMOV,opAH,op3.low); op3.low := opAH;
				END;
				emitter.Emit1(InstructionSet.opIMUL,op3.low);
				emitter.Emit2(InstructionSet.opMOV,op1.low,opAL);
			ELSIF (instr.op1.type.form IN IntermediateCode.Integer) THEN
				MakeOperand(instr.op1,op1,0,none); MakeOperand(instr.op2,op2,0,none); MakeOperand(instr.op3,op3,0,none);
				IF (instr.op3.mode = IntermediateCode.ModeImmediate) THEN
					IF ~Assembler.IsRegisterOperand(op1.low)  THEN
						Temporary(instr.op1.type.sizeInBits,temp);
						Mov(InstructionSet.opMOV,temp,op3);
						emitter.Emit2(InstructionSet.opIMUL,temp.low,op2.low);
						Mov(InstructionSet.opMOV,op1,temp);
					ELSE
						emitter.Emit3(InstructionSet.opIMUL,op1.low,op2.low,op3.low);
					END;
				ELSIF (instr.op2.mode = IntermediateCode.ModeImmediate) THEN
					MakeOperand(instr.op1,op1,0,none); MakeOperand(instr.op2,op2,0,none); MakeOperand(instr.op3,op3,0,none);
					IF ~Assembler.IsRegisterOperand(op1.low)  THEN
						Temporary(instr.op1.type.sizeInBits,temp);
						Mov(InstructionSet.opMOV,temp,op2);
						emitter.Emit2(InstructionSet.opIMUL,temp.low,op3.low);
						Mov(InstructionSet.opMOV,op1,temp);
					ELSE
						emitter.Emit3(InstructionSet.opIMUL,op1.low,op3.low,op2.low);
					END;
				ELSE
					PrepareOp3(instr,op1,op2);
					IF ~Assembler.IsRegisterOperand(op1.low) THEN
						Temporary(op1.low.sizeInBytes*8,temp);
						emitter.Emit2(InstructionSet.opMOV,temp.low,op1.low);
						emitter.Emit2(InstructionSet.opIMUL,temp.low,op2.low);
						emitter.Emit2(InstructionSet.opMOV,op1.low,temp.low);
					ELSE
						emitter.Emit2(InstructionSet.opIMUL,op1.low,op2.low);
					END;
					FinishOp3(instr,op1);
				END
			ELSE
				ThreeOperandFPInstruction(instr,InstructionSet.opFMUL)
			END;
		END EmitMul;

		PROCEDURE EmitDivMod(CONST instr: IntermediateCode.Instruction);
		VAR
			dividend,quotient,remainder,imm,target,memop: Assembler.Operand;
			op1,op2,op3: Operand;
		BEGIN
			(*
			In general it must obviously hold that
				a = (a div b) * b + a mod b and
			for all integers a,b#0, and c.

			For positive numbers a and b this holds if
				a div b = max{integer i: i*b <= b} = Entier(a/b)
			and
				a mod b = a-(a div b)*b = min{c >=0: c = a-i*b, integer i}

			Example
				11 div 3 = 3 (3*3 = 9)
				11 mod 3 = 2 (=11-9)

			for negative a there are two definitions for mod possible:
				(i) 	mathematical definition with
					a mod b >= 0:
					a mod b = min{ c >=0: c = a-i*b, integer i} >= 0
					this corresponds with rounding down
					a div b = Entier(a/b) <= a/b
		 		(ii) symmetric definition with
		 			(-a) mod' b = -(a mod' b) and
		 			(-a) div' b = -(a div' b)
		 			corresponding with rounding to zero
		 			a div' b = RoundToZero(a/b)

		 	Examples
		 		(i) -11 div 3 = -4  (3*(-4) = -12)
		 			-11 mod 3 = 1 (=-11-(-12))
		 		(ii) -11 div' 3 = -(11 div 3) = -3 (3*(-3)= -9)
		 			-11 mod' 3 = -2 (=-11-(-9))

		 	The behaviour for negative b can, in the symmetrical case, be deduced as
				(ii)	symmetric definition
					a div' (-b) = (-a) div' b = -(a div' b)
					a mod' (-b) = a- a div' (-b) * (-b) = a mod' b

			In the mathematical case it is not so easy. It turns out that the definitions
				a DIV b = Entier(a/b) = max{integer i:  i*b <= b}
			and
				a MOD b = min { c >=0 : c = a-i*b, integer i} >= 0
			are not compliant with
				a = (a DIV b) * b + a MOD b
			if b <= 0.

			Proof: assume that b<0, then
				a - Entier(a/b) * b >= 0
				<=_> a >= Entier(a/b) * b
				<=> Entier(a/b) >= a/b (contradiction to definition of Entier).

			OBERON ADOPTS THE MATHEMATICAL DEFINITION !

			For integers a and b (b>0) it holds that

				a DIV b = Entier(a/b) <= a/b
				a MOD b = min{ c >=0: c = b-i*a, integer i} = a - a DIV b * b

			The behaviour for b < 0 is explicitely undefined.

			*)



			(*
				AX / regMem8 = AL (remainder AH)
				DX:AX / regmem16 = AX (remainder DX)
				EDX:EAX / regmem32 = EAX (remainder EDX)
				RDX:EAX / regmem64 = RAX (remainder RDX)

				1.) EAX <- source1
				2.) CDQ
				3.) IDIV source2
				3.) SHL EDX
				4.) SBB EAX,1
				result is in EAX
			*)


			MakeOperand(instr.op2,op2,0,none);
			CASE instr.op1.type.sizeInBits OF
			IntermediateCode.Bits8:
				FreeRegister(AL); registerAllocator.Allocate(AL,reserved);
				emitter.Emit2(InstructionSet.opMOV,opAL,op2.low);
				dividend := opAX;
				quotient := opAL;
				remainder := opAH;
				emitter.Emit0(InstructionSet.opCBW);
			| IntermediateCode.Bits16:
				FreeRegister(AX);registerAllocator.Allocate(AX,reserved);
				emitter.Emit2(InstructionSet.opMOV,opAX,op2.low);
				FreeRegister(DX);registerAllocator.Allocate(DX,reserved);
				dividend := opAX;
				quotient := dividend;
				remainder := opDX;
				emitter.Emit0(InstructionSet.opCWD);
			| IntermediateCode.Bits32:
				FreeRegister(EAX);registerAllocator.Allocate(EAX,reserved);
				emitter.Emit2(InstructionSet.opMOV,opEAX,op2.low);
				FreeRegister(EDX);registerAllocator.Allocate(EDX,reserved);
				dividend := opEAX;
				quotient := dividend;
				remainder := opEDX;
				emitter.Emit0(InstructionSet.opCDQ);
			END;
			(* registers might have been changed, so we make the operands now *)
			MakeOperand(instr.op1,op1,0,none);
			MakeOperand(instr.op2,op2,0,none);
			MakeOperand(instr.op3,op3,0,none);
			IF instr.op3.mode = IntermediateCode.ModeImmediate THEN
				AllocateStack(instr.op3.type.sizeInBits DIV 8);
				Assembler.InitMem(memop,SHORT(instr.op3.type.sizeInBits DIV 8),SP,0);
				emitter.Emit2(InstructionSet.opMOV,memop,op3.low);
				op3.low := memop;
			END;

			emitter.Emit1(InstructionSet.opIDIV,op3.low);

			IF instr.opcode = IntermediateCode.mod THEN
				imm := Assembler.NewImm8 (0);
				emitter.Emit2(InstructionSet.opCMP, remainder, imm);
				Assembler.InitImm8(target,0);
				emitter.Emit1(InstructionSet.opJGE, target);
				emitter.Emit2( InstructionSet.opADD, remainder, op3.low);
				emitter.code.PutByteAt(target.pc,(emitter.code.pc -target.pc )-1);
				emitter.Emit2(InstructionSet.opMOV, op1.low, remainder);
			ELSE
				imm := Assembler.NewImm8 (1);
				emitter.Emit2(InstructionSet.opSHL, remainder, imm);
				imm := Assembler.NewImm8 (0);
				emitter.Emit2(InstructionSet.opSBB, quotient, imm);
				emitter.Emit2(InstructionSet.opMOV, op1.low, quotient);
			END;

			IF instr.op3.mode = IntermediateCode.ModeImmediate THEN
				AllocateStack(-instr.op3.type.sizeInBits DIV 8);
			END;

		END EmitDivMod;

		PROCEDURE EmitDiv(CONST instr: IntermediateCode.Instruction);
		BEGIN
			IF  instr.op1.type.form = IntermediateCode.Float THEN
				ThreeOperandFPInstruction(instr,InstructionSet.opFDIV)
			ELSE
				Assert(instr.op1.type.sizeInBits # IntermediateCode.Bits64,"hugeint not supported"); (* hugeint implemented as library *)
				EmitDivMod(instr);
			END;
		END EmitDiv;

		(* undefined for float and huegint, huegint version as library *)
		PROCEDURE EmitMod(CONST instr: IntermediateCode.Instruction);
		BEGIN
			Assert(instr.op1.type.form IN IntermediateCode.Integer,"mod only on integers");
			Assert(instr.op1.type.sizeInBits # IntermediateCode.Bits64,"hugeint not supported");
			EmitDivMod(instr);
		END EmitMod;

		PROCEDURE EmitAnd(CONST instr: IntermediateCode.Instruction);
		BEGIN
			IF instr.op1.type.form IN IntermediateCode.Integer THEN
				ThreeOperandInstruction(instr,InstructionSet.opAND,InstructionSet.opAND);
			ELSE Halt("must be integer");
			END
		END EmitAnd;

		PROCEDURE EmitOr(CONST instr: IntermediateCode.Instruction);
		BEGIN
			IF instr.op1.type.form IN IntermediateCode.Integer THEN
				ThreeOperandInstruction(instr,InstructionSet.opOR,InstructionSet.opOR);
			ELSE Halt("must be integer");
			END
		END EmitOr;

		PROCEDURE EmitXor(CONST instr: IntermediateCode.Instruction);
		BEGIN
			IF instr.op1.type.form IN IntermediateCode.Integer THEN
				ThreeOperandInstruction(instr,InstructionSet.opXOR,InstructionSet.opXOR)
			ELSE Halt("must be integer");
			END
		END EmitXor;

		(*! remove?
		PROCEDURE MakeFree(register: LONGINT);
		VAR old,new: LONGINT; virtual: LONGINT;
		BEGIN
			IF registerAllocator.realToVirtual[register] = free THEN RETURN END;
			old := register MOD 32;
			IF registerAllocator.realToVirtual[old + AL] > 0 THEN
				old := old+AL;
				new := registerAllocator.NextFree(IntermediateCode.Bits8);
			ELSIF registerAllocator.realToVirtual[old+AX] > 0 THEN
				old := old+AX;
				new := registerAllocator.NextFree(IntermediateCode.Bits16);
			ELSIF registerAllocator.realToVirtual[old+EAX] > 0 THEN
				old := old+EAX;
				new := registerAllocator.NextFree(IntermediateCode.Bits32);
			END;
			virtual := registerAllocator.realToVirtual[old];
			IF realRegisters[virtual].low = old THEN realRegisters[virtual].low := new;
				IF dump # NIL THEN
					dump.String("replace register "); dump.Int(virtual,1); dump.String("(low) : "); dump.String(InstructionSet.registers[old].name); dump.String(" -> "); dump.String(InstructionSet.registers[new].name); dump.Ln;
				END;
			ELSIF realRegisters[virtual].high = old THEN realRegisters[virtual].high := new;
				IF dump # NIL THEN
					dump.String("replace register "); dump.Int(virtual,1); dump.String("(high) : "); dump.String(InstructionSet.registers[old].name);  dump.String(" -> "); dump.String(InstructionSet.registers[new].name); dump.Ln;
				END;
			END;
			emitter.Emit2(InstructionSet.opMOV,registerOperands[new],registerOperands[old]);
			registerAllocator.Free(old);
			registerAllocator.Allocate(new,virtual);
		END MakeFree;
		*)

		PROCEDURE EmitShift(CONST instr: IntermediateCode.Instruction);
		VAR
			shift: Assembler.Operand;
			op: LONGINT;
			op1,op2,op3,dest,temporary: Operand;

			bits64: BOOLEAN;
			index: SHORTINT; temp: Assembler.Operand;

			left: BOOLEAN;
			ecx,cx,ch,cl: LONGINT;
		BEGIN
			Assert(instr.op1.type.form IN IntermediateCode.Integer,"must be integer operand");
			IF instr.op1.type.form = IntermediateCode.UnsignedInteger THEN
				IF instr.opcode = IntermediateCode.shr THEN op :=  InstructionSet.opSHR; left := FALSE;
				ELSIF instr.opcode = IntermediateCode.shl THEN  op :=  InstructionSet.opSHL; left := TRUE;
				ELSIF instr.opcode = IntermediateCode.ror THEN  op := InstructionSet.opROR; left := FALSE;
				ELSIF instr.opcode = IntermediateCode.rol THEN op := InstructionSet.opROL; left := TRUE;
				END;
			ELSE
				IF instr.opcode = IntermediateCode.shr THEN op :=  InstructionSet.opSAR; left := FALSE;
				ELSIF instr.opcode = IntermediateCode.shl THEN op :=  InstructionSet.opSAL; left := TRUE;
				ELSIF instr.opcode = IntermediateCode.ror THEN op := InstructionSet.opROR; left := FALSE;
				ELSIF instr.opcode = IntermediateCode.rol THEN op := InstructionSet.opROL; left := TRUE;
				END;
			END;
			bits64 := instr.op1.type.sizeInBits = IntermediateCode.Bits64;

			ecx := registerAllocator.realToVirtual[ECX];
			IF ecx # free THEN Spill(ecx) END; (*! can optimize if ecx already contains shift *)
			cx := registerAllocator.realToVirtual[CX];
			IF cx # free THEN Spill(cx) END; (*! can optimize if ecx already contains shift *)
			cl := registerAllocator.realToVirtual[CL];
			IF cl # free THEN Spill(cl) END; (*! can optimize if ecx already contains shift *)
			ch := registerAllocator.realToVirtual[CH];
			IF  ch # free THEN Spill(ch) END; (*! can optimize if ecx already contains shift *)

			registerAllocator.Allocate(ECX,reserved);

			Temporary(instr.op2.type.sizeInBits,dest);
			MakeOperand(instr.op1,op1,0,none);
			MakeOperand(instr.op2,op2,0,none);
			MakeOperand(instr.op3,op3,0,none);
			IF instr.op3.mode = IntermediateCode.ModeImmediate THEN
				Assembler.InitImm8(shift,instr.op3.intValue);
			ELSE
				CASE instr.op3.type.sizeInBits OF
					IntermediateCode.Bits8: index := CL;
					|IntermediateCode.Bits16: index := CX;
					|IntermediateCode.Bits32: index := ECX;
					|IntermediateCode.Bits64: index := ECX;
				END;

				(*
				IF (registerAllocator.realToVirtual[index] # free) & ((registerAllocator.realToVirtual[index] # instr.op1.register) OR (instr.op1.mode # IntermediateCode.ModeRegister)) THEN
					Spill();
					(*
					emitter.Emit1(InstructionSet.opPUSH,opECX);
					ecxPushed := TRUE;
					*)
				END;
				*)
				IF (instr.op3.mode # IntermediateCode.ModeRegister) OR (realRegisters[instr.op3.register].low # index) THEN
					emitter.Emit2(InstructionSet.opMOV,registerOperands[index],op3.low);
				END;
				shift := opCL;
			END;


			IF ~bits64 THEN
				Mov(InstructionSet.opMOV,dest,op2);
				emitter.Emit2 (op, dest.low,shift);
				Mov(InstructionSet.opMOV,op1,dest);
			ELSIF left THEN

				IF ~IntermediateCode.OperandEquals(instr.op1,instr.op2) THEN
					Mov(InstructionSet.opMOV,op1,op2)
				END;

				IF (instr.opcode=IntermediateCode.rol) THEN
					(*  |high| <- |low| <- |temp=high| *)
					Temporary(32,temporary);
					emitter.Emit2( InstructionSet.opMOV, temporary.low, op1.high);
					emitter.Emit3( InstructionSet.opSHLD,op1.high, op1.low, shift);
					emitter.Emit3( InstructionSet.opSHLD, op1.low, temporary.low, shift);
					registerAllocator.Free(temporary.low.index);
				ELSE
					(* |high| <- |low| *)
					emitter.Emit3( InstructionSet.opSHLD, op1.low,op1.high,shift);
					emitter.Emit2( op, op1.low,shift);
				END;
			ELSE
				IF ~IntermediateCode.OperandEquals(instr.op1,instr.op2) THEN
					Mov(InstructionSet.opMOV,op1,op2)
				END;

				IF instr.opcode=IntermediateCode.ror THEN
					(*  |temp=low| -> |high| -> |low| *)
					Temporary(32,temporary);
					emitter.Emit2( InstructionSet.opMOV, temporary.low, op1.low);
					emitter.Emit3( InstructionSet.opSHRD,op1.low, op1.high, shift);
					emitter.Emit3( InstructionSet.opSHRD, op1.high, temporary.low, shift);
					registerAllocator.Free(temporary.low.index);
				ELSE
					(*  |high| -> |low| *)
					emitter.Emit3( InstructionSet.opSHRD, op1.low,op1.high,shift);
					emitter.Emit2( op, op1.high, shift);
				END;

			END;
			registerAllocator.Free(ECX);

			IF ecx # free THEN UnSpill(ecx,ECX,none) END;
			IF cx # free THEN UnSpill(cx,CX,none) END;
			IF cl # free THEN UnSpill(cl,CL,none) END;
			IF ch # free THEN UnSpill(ch,CH,none) END;


		END EmitShift;

		PROCEDURE EmitCopy(CONST instr: IntermediateCode.Instruction);
		VAR op1,op2,op3: Operand; esi, edi, ecx: LONGINT;

		BEGIN
			esi := registerAllocator.realToVirtual[ESI];
			edi := registerAllocator.realToVirtual[EDI];
			ecx := registerAllocator.realToVirtual[ECX];

			IF esi # free THEN Spill(esi) END;
			IF edi # free THEN Spill(edi) END;
			IF ecx # free THEN Spill(ecx) END;

			registerAllocator.Allocate(ESI,reserved);
			registerAllocator.Allocate(EDI,reserved);
			registerAllocator.Allocate(ECX,reserved);

			MakeOperand(instr.op1,op1,0,EDI);
			MakeOperand(instr.op2,op2,0,ESI);
			MakeOperand(instr.op3,op3,0,ECX);
			(*
			emitter.Emit2(InstructionSet.opMOV,opEDI, op1.low);
			emitter.Emit2(InstructionSet.opMOV,opESI, op2.low);
			emitter.Emit2(InstructionSet.opMOV,opECX, op3.low);
			*)

			registerAllocator.Free(ESI);
			registerAllocator.Free(EDI);
			registerAllocator.Free(ECX);


			emitter.Emit0(InstructionSet.opCLD); (* copy upwards *)
			emitter.EmitPrefix (InstructionSet.prfREP);
			emitter.Emit0(InstructionSet.opMOVSB);

		END EmitCopy;


		PROCEDURE EmitFill(CONST instr: IntermediateCode.Instruction; down: BOOLEAN);
		VAR op1,op2,op3: Operand; reg,sizeInBits,i: LONGINT;val,src,dest: Assembler.Operand;
			op: LONGINT;
			edi, ecx: LONGINT;
		BEGIN
			IF FALSE & (instr.op3.mode = IntermediateCode.ModeImmediate) & (instr.op3.symbol = NIL) & (instr.op3.intValue < 5) THEN
				sizeInBits := instr.op2.type.sizeInBits;
				IF sizeInBits = IntermediateCode.Bits8 THEN src := opAL;
				ELSIF sizeInBits = IntermediateCode.Bits16 THEN src := opAX;
				ELSIF sizeInBits = IntermediateCode.Bits32 THEN src := opEAX;
				ELSE HALT(200)
				END;
				MakeOperand(instr.op1,op1,0,none);
				IF instr.op1.mode = IntermediateCode.ModeRegister THEN reg := op1.low.register
				ELSE emitter.Emit2(InstructionSet.opMOV,opEDX,op1.low); reg := EDX;
				END;
				IF (instr.op2.mode = IntermediateCode.ModeImmediate) & (instr.op2.type.form IN IntermediateCode.Integer) & (instr.op2.intValue = 0) THEN
					emitter.Emit2(InstructionSet.opXOR,opEAX,opEAX);
				ELSE
					MakeOperand(instr.op2,op2,0,none);
					emitter.Emit2(InstructionSet.opMOV,src,op2.low);
				END;
				FOR i := 0 TO SHORT(instr.op3.intValue)-1 DO
					IF down THEN
						Assembler.InitMem(dest,SHORT(SHORT(sizeInBits DIV 8)),reg,-i*sizeInBits DIV 8);
					ELSE
						Assembler.InitMem(dest,SHORT(SHORT(sizeInBits DIV 8 )),reg,i*sizeInBits DIV 8);
					END;
					emitter.Emit2(InstructionSet.opMOV,dest,src);
				END;
			ELSE
				edi := registerAllocator.realToVirtual[EDI];
				ecx := registerAllocator.realToVirtual[ECX];
				IF edi # free THEN Spill(edi) END;
				IF ecx # free THEN Spill(ecx) END;
				registerAllocator.Allocate(EDI,reserved);
				registerAllocator.Allocate(ECX,reserved);

				MakeOperand(instr.op1,op1,0,EDI);
				MakeOperand(instr.op3,op3,0,ECX);
				MakeOperand(instr.op2,op2,0,none);
				(*
				emitter.Emit2(InstructionSet.opMOV,opEDI, op1.low);
				emitter.Emit2(InstructionSet.opMOV,opECX, op3.low);
				*)
				CASE instr.op2.type.sizeInBits OF
					IntermediateCode.Bits8: val := opAL; op := InstructionSet.opSTOSB;
					|IntermediateCode.Bits16: val := opAX; op := InstructionSet.opSTOSW;
					|IntermediateCode.Bits32: val := opEAX; op := InstructionSet.opSTOSD;
				ELSE Halt("only supported for upto 32 bit integers ");
				END;

				IF (instr.op2.mode = IntermediateCode.ModeImmediate) & (instr.op2.type.form IN IntermediateCode.Integer) & (instr.op2.intValue = 0) THEN
					emitter.Emit2(InstructionSet.opXOR,opEAX,opEAX);
				ELSE
					emitter.Emit2(InstructionSet.opMOV,val,op2.low);
				END;

				IF down THEN
					emitter.Emit0(InstructionSet.opSTD); (* fill downwards *)
				ELSE
					emitter.Emit0(InstructionSet.opCLD); (* fill upwards *)
				END;
				emitter.EmitPrefix (InstructionSet.prfREP);
				emitter.Emit0(op);
				IF down THEN (* needed as calls to windows crash otherwise *)
					emitter.Emit0(InstructionSet.opCLD);
				END;
				registerAllocator.Free(EDI);
				registerAllocator.Free(ECX);
			END;
		END EmitFill;

		PROCEDURE EmitBr (CONST instr: IntermediateCode.Instruction);
		VAR dest,destPC,offset: LONGINT; target: Operand;lowHit: LONGINT; reverse: BOOLEAN;
			(* jump operands *)  left,right,temp: Operand; hiHit, hiFail: LONGINT;
				fail: Assembler.Operand; failPC: LONGINT;

			PROCEDURE JmpDest(brop: LONGINT);
			BEGIN
				IF instr.op1.mode = IntermediateCode.ModeImmediate THEN
					Assert(instr.op1.symbol # NIL,"branch without symbol destination");
					dest := (instr.op1.symbolOffset); (* this is the offset in the in-data section (intermediate code), it is not byte- *)
					destPC := (in.instructions[dest].pc );
					offset := destPC - (out.pc );
					IF dest > inPC THEN (* forward jump *)
						Assembler.InitOffset32(target.low,0);
						Assembler.SetSymbol(target.low,instr.op1.symbol,instr.op1.symbolOffset,instr.op1.offset);
						emitter.Emit1(brop,target.low);
					ELSIF ABS(offset)  <= 126 THEN
						Assembler.InitOffset8(target.low,destPC);
						emitter.Emit1(brop,target.low);
					ELSE
						Assembler.InitOffset32(target.low,destPC);
						emitter.Emit1(brop,target.low);
					END;
				ELSE
					MakeOperand(instr.op1,target,0,none);
					emitter.Emit1(brop,target.low);
				END;
			END JmpDest;

		BEGIN
			IF (instr.op1.symbol = in) & (instr.op1.symbolOffset = inPC +1) THEN (* jump to next instruction can be ignored *)
				IF dump # NIL THEN dump.String("jump to next instruction ignored"); dump.Ln END;
				RETURN
			END;

			failPC := 0;
			IF instr.opcode = IntermediateCode.br THEN
				lowHit := InstructionSet.opJMP
			ELSIF instr.op2.type.form = IntermediateCode.Float THEN
				CASE instr.opcode OF
				IntermediateCode.breq:	lowHit := InstructionSet.opJE;
				|IntermediateCode.brne:lowHit := InstructionSet.opJNE;
				|IntermediateCode.brge: lowHit := InstructionSet.opJAE
				|IntermediateCode.brlt: lowHit := InstructionSet.opJB
				END;
				MakeOperand(instr.op2,left,0,none);
				emitter.Emit1(InstructionSet.opFLD,left.low); INC(fpStackPointer);
				MakeOperand(instr.op3,right,0,none);
				emitter.Emit1(InstructionSet.opFCOMP,right.low); DEC(fpStackPointer);
				emitter.Emit1(InstructionSet.opFNSTSW,opAX);
				IF (instr.op2.mode = IntermediateCode.ModeRegister) & (instr.op2.register IN toBeReleased) THEN
					ReleaseFPRegister(instr.op2.register);
					EXCL(toBeReleased,instr.op2.register);
					lastUse[instr.op2.register] := -1;
				END;
				IF (instr.op3.mode = IntermediateCode.ModeRegister) & (instr.op3.register IN toBeReleased) THEN
					ReleaseFPRegister(instr.op3.register);
					EXCL(toBeReleased,instr.op3.register);
					lastUse[instr.op3.register] := -1;
				END;
				emitter.Emit0(InstructionSet.opSAHF);
			ELSE
				IF (instr.op2.mode = IntermediateCode.ModeImmediate) & (instr.op3.mode = IntermediateCode.ModeImmediate) THEN
					Temporary(instr.op2.type.sizeInBits,temp);
					MakeOperand(instr.op2,left,0,none);
					MakeOperand(instr.op3,right,0,none);
					Mov(InstructionSet.opMOV,temp,left);
					left := temp;
				ELSIF instr.op2.mode = IntermediateCode.ModeImmediate THEN
					reverse := TRUE;
					MakeOperand(instr.op2,right,0,none);
					MakeOperand(instr.op3,left,0,none);
				ELSIF IsMemoryOperand(instr.op2) & IsMemoryOperand(instr.op3) THEN
					Temporary(instr.op2.type.sizeInBits,temp);
					MakeOperand(instr.op2,left,0,none);
					MakeOperand(instr.op3,right,0,none);
					Mov(InstructionSet.opMOV,temp,right);
					right := temp;
				ELSE
					reverse := FALSE;
					MakeOperand(instr.op2,left,0,none);
					MakeOperand(instr.op3,right,0,none);
				END;
				IF instr.op2.type.sizeInBits # IntermediateCode.Bits64 THEN
					CASE instr.opcode OF
					IntermediateCode.breq:
						lowHit := InstructionSet.opJE;
					|IntermediateCode.brne:
						lowHit := InstructionSet.opJNE;
					|IntermediateCode.brge:
						IF instr.op2.type.form = IntermediateCode.SignedInteger THEN
							IF reverse THEN lowHit := InstructionSet.opJLE ELSE lowHit := InstructionSet.opJGE END;
						ELSIF instr.op2.type.form = IntermediateCode.UnsignedInteger THEN
							IF reverse THEN lowHit := InstructionSet.opJBE ELSE lowHit := InstructionSet.opJAE END;
						END;
					|IntermediateCode.brlt:
						IF instr.op2.type.form = IntermediateCode.SignedInteger THEN
							IF reverse THEN lowHit := InstructionSet.opJG ELSE lowHit := InstructionSet.opJL END;
						ELSIF instr.op2.type.form = IntermediateCode.UnsignedInteger THEN
							IF reverse THEN lowHit := InstructionSet.opJA ELSE lowHit := InstructionSet.opJB END;
						END;
					END;
				ELSE
					Assert(instr.op2.type.form = IntermediateCode.SignedInteger,"no unsigned integer64");
					CASE instr.opcode OF
					IntermediateCode.breq:
						hiHit := 0; hiFail := InstructionSet.opJNE;	lowHit := InstructionSet.opJE
					|IntermediateCode.brne:
						hiHit := InstructionSet.opJNE; hiFail := 0; lowHit := InstructionSet.opJNE
					|IntermediateCode.brge:
						IF reverse THEN
							hiHit := InstructionSet.opJL; hiFail := InstructionSet.opJG; lowHit := InstructionSet.opJBE
						ELSE
							hiHit := InstructionSet.opJG; hiFail := InstructionSet.opJL; lowHit := InstructionSet.opJAE
						END;
					|IntermediateCode.brlt:
						IF reverse THEN
							hiHit := InstructionSet.opJG; hiFail := InstructionSet.opJL; lowHit := InstructionSet.opJA
						ELSE
							hiHit := InstructionSet.opJL; hiFail := InstructionSet.opJG; lowHit := InstructionSet.opJB
						END;
					END;
					emitter.Emit2(InstructionSet.opCMP,left.high,right.high);
					IF hiHit # 0 THEN
						JmpDest(hiHit);
					END;
					IF hiFail # 0 THEN
						failPC := out.pc; (* to avoid potential value overflow problem, will be patched anyway  *)
						Assembler.InitOffset8(fail,failPC );
						emitter.Emit1(hiFail,fail);
						failPC := fail.pc;
					END;
				END;
				emitter.Emit2(InstructionSet.opCMP,left.low,right.low);
			END;
			JmpDest(lowHit);
			IF failPC > 0 THEN out.PutByteAt(failPC,((out.pc-failPC) )-1); END;
		END EmitBr;

		PROCEDURE EmitPop(CONST instr: IntermediateCode.Instruction);
		VAR
			type: IntermediateCode.Type; op1: Operand; memop: Assembler.Operand; sizeInBytes,reg: LONGINT;
		BEGIN
			type := instr.op1.type;

			CASE type.form OF
			IntermediateCode.SignedInteger, IntermediateCode.UnsignedInteger:
				IF type.sizeInBits = IntermediateCode.Bits32 THEN
					MakeOperand(instr.op1,op1,0,none);
					emitter.Emit1(InstructionSet.opPOP,op1.low);
				ELSIF type.sizeInBits = IntermediateCode.Bits8 THEN
					MakeOperand(instr.op1,op1,0,none);
					IF (op1.low.type = Assembler.reg8) & (AL <= op1.low.register) & (op1.low.register <= BL) & (registerAllocator.realToVirtual[op1.low.register + 4] = free) THEN
						emitter.Emit1(InstructionSet.opPOP,registerOperands[op1.low.register+2*32]);
					ELSE
						Assembler.InitMem(memop,IntermediateCode.Bits8 DIV 8,SP,0);
						emitter.Emit2(InstructionSet.opMOV,op1.low,memop);
						AllocateStack(-4);
					END;
				ELSIF type.sizeInBits = IntermediateCode.Bits16 THEN
					MakeOperand(instr.op1,op1,0,none);
					IF op1.low.type = Assembler.reg16 THEN
						emitter.Emit1(InstructionSet.opPOP,registerOperands[op1.low.register+1*32]);
					ELSE
						Assembler.InitMem(memop,IntermediateCode.Bits16 DIV 8,SP,0);
						emitter.Emit2(InstructionSet.opMOV,op1.low,memop);
						AllocateStack(-4);
					END;
				ELSE
					MakeOperand(instr.op1,op1,0,none);
					emitter.Emit1(InstructionSet.opPOP,op1.low);
					emitter.Emit1(InstructionSet.opPOP,op1.high);
				END;
			|IntermediateCode.Float:
				MakeOperand(instr.op1,op1,0,none);
				IF type.sizeInBits = IntermediateCode.Bits32 THEN
					sizeInBytes := 4;
					Assembler.InitMem(memop,IntermediateCode.Bits32 DIV 8,SP,0);
				ELSE
					sizeInBytes := 8;
					Assembler.InitMem(memop,IntermediateCode.Bits64 DIV 8,SP,0);
				END;
				reg := instr.op1.register;
				IF reg # IntermediateCode.Result THEN (* nothing to do, on top of stack anyway *)
					emitter.Emit1(InstructionSet.opFLD,memop); INC(fpStackPointer);
					IF -fpRegisters[reg] + fpStackPointer # 0 THEN
						emitter.Emit1(InstructionSet.opFSTP,op1.low); DEC(fpStackPointer);
					ELSE (* result may stay on top of stack, op1 has been allocated in place *)
					END;
					AllocateStack(-sizeInBytes);
				END;
			END;
		END EmitPop;

		PROCEDURE Push(CONST operand: Operand);
			PROCEDURE Push32(operand: Assembler.Operand);
			BEGIN
				IF (operand.type = Assembler.reg8) THEN
					IF (AL <= operand.register) & (operand.register <= BL)  THEN
						emitter.Emit1(InstructionSet.opPUSH,registerOperands[operand.register+2*32]);
					ELSE
						HALT(100)
					END;
				ELSIF (operand.type = Assembler.reg16) THEN
					emitter.Emit1(InstructionSet.opPUSH,registerOperands[operand.register+32]);
				ELSIF (operand.type = Assembler.reg32) THEN
					emitter.Emit1(InstructionSet.opPUSH,operand);
				ELSE HALT(100)
				END;
			END Push32;
		BEGIN
			IF operand.high.type # Assembler.none THEN
				Push32(operand.high)
			END;
			Push32(operand.low)
		END Push;


		PROCEDURE EmitPush(CONST instr: IntermediateCode.Instruction);
		VAR  index: LONGINT; type: IntermediateCode.Type; op1: Operand; memop: Assembler.Operand;
		BEGIN
			type := instr.op1.type;

			CASE type.form OF
			IntermediateCode.SignedInteger, IntermediateCode.UnsignedInteger:
				IF type.sizeInBits = IntermediateCode.Bits32 THEN
					MakeOperand(instr.op1,op1,0,none);
					emitter.Emit1(InstructionSet.opPUSH,op1.low);
				ELSIF type.sizeInBits = IntermediateCode.Bits8 THEN
					IF (instr.op1.mode = IntermediateCode.ModeRegister) & (realRegisters[instr.op1.register].low >= AL) & (realRegisters[instr.op1.register].low <= BL) THEN
						index := realRegisters[instr.op1.register].low;
						index := index MOD 32 + EAX;
						emitter.Emit1(InstructionSet.opPUSH,registerOperands[index]);
					ELSE
						MakeOperand(instr.op1,op1,IntermediateCode.Bits32,none);
						emitter.Emit1(InstructionSet.opPUSH,op1.low);
						(*
						emitter.Emit2(InstructionSet.opMOV,opAL,op1.low);
						emitter.Emit1(InstructionSet.opPUSH,opEAX);
						*)
					END;
				ELSIF type.sizeInBits < IntermediateCode.Bits32 THEN
					IF instr.op1.mode = IntermediateCode.ModeRegister THEN
						index := realRegisters[instr.op1.register].low;
						index := index MOD 32 + EAX;
						emitter.Emit1(InstructionSet.opPUSH,registerOperands[index]);
					ELSE
						MakeOperand(instr.op1,op1,IntermediateCode.Bits32,none);
						emitter.Emit1(InstructionSet.opPUSH,op1.low);
					END;
				ELSIF type.sizeInBits = IntermediateCode.Bits64 THEN
					MakeOperand(instr.op1,op1,0,none);
					emitter.Emit1(InstructionSet.opPUSH,op1.high);
					emitter.Emit1(InstructionSet.opPUSH,op1.low);
				ELSE Halt("unsupported bit length");
				END;
			|IntermediateCode.Float:
				MakeOperand(instr.op1,op1,0,none);
				IF (instr.op1.mode = IntermediateCode.ModeMemory) & (type.sizeInBits = IntermediateCode.Bits32) THEN
					emitter.Emit1(InstructionSet.opPUSH,op1.low);
				ELSE
					IF type.sizeInBits = IntermediateCode.Bits32 THEN
						AllocateStack(4);
						Assembler.InitMem(memop,IntermediateCode.Bits32 DIV 8,SP,0);
					ELSE
						AllocateStack(8);
						Assembler.InitMem(memop,IntermediateCode.Bits64 DIV 8,SP,0);
					END;
					emitter.Emit1(InstructionSet.opFLD,op1.low); INC(fpStackPointer);
					emitter.Emit1(InstructionSet.opFSTP,memop); DEC(fpStackPointer);
				END;
			END;
		END EmitPush;

		PROCEDURE EmitNeg(CONST instr: IntermediateCode.Instruction);
		VAR op: Operand; minusOne: Assembler.Operand;
		BEGIN
			IF instr.op1.type.form IN IntermediateCode.Integer THEN
				PrepareOp2(instr,op);
				IF instr.op1.type.sizeInBits = IntermediateCode.Bits64 THEN
					emitter.Emit1(InstructionSet.opNOT,op.high);
					emitter.Emit1(InstructionSet.opNEG,op.low);
					Assembler.InitImm8(minusOne,-1);
					emitter.Emit2(InstructionSet.opSBB,op.high,minusOne);
				ELSE
					emitter.Emit1(InstructionSet.opNEG,op.low);
				END;
				FinishOp2(instr,op);
			ELSIF instr.op1.type.form = IntermediateCode.Float THEN
				TwoOperandFPInstruction(instr,InstructionSet.opFCHS)
			(**
			ELSE Halt("does not make sense on unsigned integer");
				counterexample: (-adr MOD alignment)
			*)
			END;
		END EmitNeg;

		PROCEDURE EmitNot(CONST instr: IntermediateCode.Instruction);
		BEGIN
			IF instr.op1.type.form IN IntermediateCode.Integer THEN
				TwoOperandInstruction(instr,InstructionSet.opNOT,InstructionSet.opNOT);
			ELSE HALT(100) (* does not make sense on float *)
			END;
		END EmitNot;

		PROCEDURE EmitAbs(CONST instr: IntermediateCode.Instruction);
		VAR op1,op2: Operand; source,imm: Assembler.Operand;
		BEGIN
			IF instr.op1.type.form  = IntermediateCode.SignedInteger THEN
				Assert(instr.op1.type.sizeInBits # IntermediateCode.Bits64,"64bit not supported"); (* 64 bit version via procedure call, cf. method Supported *)
				FreeRegister(EAX); registerAllocator.Allocate(EAX,reserved);
				MakeOperand(instr.op1,op1,0,none);
				MakeOperand(instr.op2,op2,0,none);

				CASE instr.op1.type.sizeInBits OF
				| IntermediateCode.Bits8: imm := Assembler.NewImm8 (7); source := opAL;
				| IntermediateCode.Bits16: imm := Assembler.NewImm8 (15); source := opAX;
				| IntermediateCode.Bits32: imm := Assembler.NewImm8 (31); source := opEAX;
				END;
				emitter.Emit2 (InstructionSet.opMOV, source,op2.low);
				emitter.Emit2 (InstructionSet.opMOV, op1.low,source);

				emitter.Emit2 (InstructionSet.opSAR, source, imm);
				emitter.Emit2 (InstructionSet.opXOR, op1.low, source);
				emitter.Emit2 (InstructionSet.opSUB, op1.low, source);
			ELSIF instr.op1.type.form = IntermediateCode.Float THEN
				TwoOperandFPInstruction(instr,InstructionSet.opFABS)
			ELSE Halt("does not make sense on unsigned integer")
			END;
		END EmitAbs;

		PROCEDURE EmitTrap(CONST instr: IntermediateCode.Instruction);
		VAR operand: Assembler.Operand;
		BEGIN
			IF instr.op1.intValue < 80H THEN
				operand := Assembler.NewImm8(instr.op1.intValue);
			ELSE
				operand := Assembler.NewImm32(instr.op1.intValue);
			END;
			emitter.Emit1(InstructionSet.opPUSH, operand);
			emitter.Emit0(InstructionSet.opINT3);
		END EmitTrap;

		PROCEDURE EmitAsm(CONST instr: IntermediateCode.Instruction);
		VAR reader: Streams.StringReader;  procedure: SyntaxTree.Procedure; scope: SyntaxTree.Scope;
				len: LONGINT; symbol: SyntaxTree.Symbol; assembler: Assembler.Assembly;
		BEGIN
			len := Strings.Length(instr.op1.string^);
			NEW(reader,len);
			reader.Set(instr.op1.string^);

			symbol := in.symbol;
			procedure := symbol(SyntaxTree.Procedure);
			scope := procedure.procedureScope;
			NEW(assembler,diagnostics,emitter);
			assembler.Assemble(reader,SHORT(instr.op1.intValue),scope,in,in,module,procedure.access * SyntaxTree.Public # {}, procedure.isInline)	;
			error := error OR assembler.error
		END EmitAsm;

	(*
		PROCEDURE Code(source: BackendStructures.Assembly);
		VAR reader: Streams.StringReader;  procedure: SyntaxTree.Procedure; scope: SyntaxTree.Scope;
			inline: BOOLEAN;  inlinecode: Assembler.Code; inlineassembler: Assembler.Assembly; name: ARRAY 256 OF CHAR;
			outer: SyntaxTree.Statement;
		BEGIN
			IF source.code.inlineCode # NIL THEN RETURN END; (* already assembled inline *)
			NEW(reader,source.code.sourceCodeLength);
			reader.Set(source.code.sourceCode^);

			outer := source.code.outer;
			WHILE (outer # NIL) & ~(outer IS SyntaxTree.Body) DO
				outer := outer.outer;
			END;
			IF outer # NIL THEN
				scope := outer(SyntaxTree.Body).inScope;
			ELSE
				scope := NIL;
			END;
			IF (scope # NIL) & (scope IS SyntaxTree.ProcedureScope) THEN
				procedure := scope(SyntaxTree.ProcedureScope).ownerProcedure;
				inline := procedure.HasFlag(SyntaxTree.InlineFlag);
				procedure.name.GetString(name);
			ELSE
				inline := FALSE;
			END;

			IF inline THEN
				NEW(inlinecode);
				NEW(inlineassembler,diagnostics,inlinecode,dump);
				inlineassembler.Assemble(reader,source.code.position,scope,module,source,procedure.access * SyntaxTree.Public # {},TRUE);
				source.code.SetInlineCode(inlinecode.code,inlinecode.pc );
				procedure.name.GetString(name);
			ELSE
				emitter.Assemble(reader, source.code.position , scope, module, source, procedure.access * SyntaxTree.Public # {},FALSE);
			END;
		END Code;
	*)


		PROCEDURE EmitData(CONST instr: IntermediateCode.Instruction);
			VAR type: IntermediateCode.Type; fixup: BinaryCode.Fixup; pc: LONGINT;fiuxpFormat: BinaryCode.FixupPatterns;
		BEGIN
			type := instr.op1.type;
			pc := out.pc;
			IF type.form IN IntermediateCode.Integer THEN
				out.PutBytes(instr.op1.intValue,SHORT(type.sizeInBits DIV 8));
			ELSE
				IF type.sizeInBits = IntermediateCode.Bits32 THEN
					out.PutReal(SHORT(instr.op1.floatValue));
				ELSIF type.sizeInBits = IntermediateCode.Bits64 THEN
					out.PutLongreal(instr.op1.floatValue);
				ELSE Halt("no floats other than 32 or 64 bit")
				END;
			END;
			IF instr.op1.symbol # NIL THEN
				NEW(fiuxpFormat,1);
				fiuxpFormat[0].offset := 0;
				fiuxpFormat[0].bits := type.sizeInBits;
				fixup := BinaryCode.NewFixup(BinaryCode.Absolute,pc,instr.op1.symbol,instr.op1.symbolOffset,instr.op1.offset,0,fiuxpFormat);
				out.fixupList.AddFixup(fixup);
			END;
		END EmitData;

		PROCEDURE EmitReserve(CONST instr: IntermediateCode.Instruction);
		VAR sizeInBytes,i: LONGINT;
		BEGIN
			sizeInBytes := SHORT(instr.op1.intValue);
			ASSERT(sizeInBytes >= 0); (* size is initialized to MIN(LONGINT), this checks if size field has been visited *)
			FOR i := 0 TO sizeInBytes-1 DO
				out.PutByte(0);
			END;
		END EmitReserve;

		PROCEDURE EmitLabel(CONST instr: IntermediateCode.Instruction);
		VAR position: LONGINT;
		BEGIN
			position := SHORT(instr.op1.intValue);
			out.AddLabel(position);
		END EmitLabel;

	END CodeGeneratorAMD64;

			Worker=OBJECT
			VAR start: BOOLEAN; finished: BOOLEAN;
				in: IntermediateCode.Section; next: Worker;
				cg: CodeGeneratorAMD64;
				pool: Pool;

			PROCEDURE &Init(pool: Pool);
			BEGIN
				start := FALSE; SELF.pool := pool;
				NEW(cg, "", NIL, 32);
			END Init;

			PROCEDURE Start(in: IntermediateCode.Section; CONST runtimeModuleName: SyntaxTree.String; diagnostics: Diagnostics.Diagnostics; module: Sections.Module; bits: LONGINT);
			BEGIN{EXCLUSIVE}
				cg.InitGeneratorAMD64(runtimeModuleName, diagnostics, bits);
				cg.SetModule(module);
				SELF.in := in;
				start := TRUE;
			END Start;

			PROCEDURE Do;
			VAR out: BinaryCode.Section; procedure: SyntaxTree.Procedure;
			BEGIN{EXCLUSIVE}
				LOOP
					AWAIT(start);
					(* inline case
					out := ResolvedSection(in(IntermediateCode.Section));
			 		cg.Section(in(IntermediateCode.Section),out);
			 		procedure := in.symbol(SyntaxTree.Procedure);
			 		procedure.procedureScope.body.code.SetBinaryCode(out.bits);
					*)
			 		out := ResolvedSection(in(IntermediateCode.Section));
			 		cg.Section(in(IntermediateCode.Section),out);
			 		IF out.type = Sections.VarSection THEN
			 			IF out.pc = 1 THEN out.SetAlignment(FALSE,1)
			 			ELSIF out.pc = 2 THEN out.SetAlignment(FALSE,2)
			 			ELSIF out.pc > 2 THEN out.SetAlignment(FALSE,4)
			 			END;
			 		ELSIF out.type = Sections.ConstSection THEN
			 			out.SetAlignment(FALSE,4);
			 		END;

					start := FALSE;
					pool.Finished(SELF);
				END;
			END Do;

			BEGIN{ACTIVE}
				Do;
			END Worker;

			Pool=OBJECT
			VAR ready: Worker; numReady, numTotal: LONGINT;

				PROCEDURE &Init();
				VAR i: LONGINT; worker: Worker;
				BEGIN
					FOR i := 1 TO Machine.NumberOfProcessors() DO
						NEW(worker,SELF); worker.next := ready; ready := worker; INC(numReady); INC(numTotal);
					END;
				END Init;

				PROCEDURE Finished(worker: Worker);
				BEGIN{EXCLUSIVE}
					worker.next := ready; ready := worker; INC(numReady);
				END Finished;

				PROCEDURE Work(in: IntermediateCode.Section; CONST runtimeModuleName: SyntaxTree.String; diagnostics: Diagnostics.Diagnostics; module: Sections.Module; bits: LONGINT);
				VAR worker: Worker;
				BEGIN{EXCLUSIVE}
					AWAIT(numReady > 0);
					worker := ready; ready := worker.next; worker.next := NIL; DEC(numReady);
					worker.Start(in,runtimeModuleName, diagnostics, module, bits);
				END Work;

				PROCEDURE Wait;
				BEGIN{EXCLUSIVE}
					AWAIT(numReady = numTotal);
				END Wait;

			END Pool;

	BackendAMD64= OBJECT (IntermediateBackend.IntermediateBackend)
	VAR
		cg: CodeGeneratorAMD64;
		bits: LONGINT;

		PROCEDURE &InitBackendAMD64;
		BEGIN
			InitIntermediateBackend;
			bits := 32;
		END InitBackendAMD64;

		PROCEDURE Initialize(diagnostics: Diagnostics.Diagnostics; flags: SET; checker: SemanticChecker.Checker; system: Global.System; dataflow: Dataflow.Specification);
		BEGIN
			Initialize^(diagnostics,flags,checker,system,dataflow); NEW(cg, runtimeModuleName, diagnostics, bits);
		END Initialize;

		PROCEDURE GetSystem(): Global.System;
		VAR system: Global.System;

			PROCEDURE AddRegister(CONST name: Scanner.StringType; val: LONGINT);
			BEGIN
				Global.NewConstant(name,val,system.shortintType,system.systemScope)
			END AddRegister;

			PROCEDURE AddRegisters;
			BEGIN
				(* system constants *)
				AddRegister("EAX",InstructionSet.regEAX);  AddRegister("ECX", InstructionSet.regECX);
				AddRegister( "EDX", InstructionSet.regEDX);  AddRegister( "EBX", InstructionSet.regEBX);
				AddRegister( "ESP", InstructionSet.regESP);  AddRegister( "EBP", InstructionSet.regEBP);
				AddRegister( "ESI", InstructionSet.regESI);  AddRegister( "EDI", InstructionSet.regEDI);

				AddRegister( "AX", InstructionSet.regAX);  AddRegister( "CX", InstructionSet.regCX);
				AddRegister( "DX", InstructionSet.regDX);  AddRegister( "BX", InstructionSet.regBX);

				AddRegister( "AL", InstructionSet.regAL);  AddRegister( "CL", InstructionSet.regCL);
				AddRegister( "DL", InstructionSet.regDL);  AddRegister( "BL", InstructionSet.regBL);
				AddRegister( "AH", InstructionSet.regAH);  AddRegister( "CH", InstructionSet.regCH);
				AddRegister( "DH", InstructionSet.regDH);  AddRegister( "BH", InstructionSet.regBH);

				AddRegister( "RAX", InstructionSet.regRAX);  AddRegister( "RCX", InstructionSet.regRCX);
				AddRegister( "RDX", InstructionSet.regRDX);  AddRegister( "RBX", InstructionSet.regRBX);
				AddRegister( "RSP", InstructionSet.regRSP);  AddRegister( "RBP", InstructionSet.regRBP);
				AddRegister( "RSI", InstructionSet.regRSI);  AddRegister( "RDI", InstructionSet.regRDI);
				AddRegister( "R8", InstructionSet.regR8);  AddRegister( "R9", InstructionSet.regR9);
				AddRegister( "R10", InstructionSet.regR10);  AddRegister( "R11", InstructionSet.regR11);
				AddRegister( "R12", InstructionSet.regR12);  AddRegister( "R13", InstructionSet.regR13);
				AddRegister( "R14", InstructionSet.regR14);  AddRegister( "R15", InstructionSet.regR15);

				AddRegister( "R8D", InstructionSet.regR8D);  AddRegister( "R9D", InstructionSet.regR9D);
				AddRegister( "R10D", InstructionSet.regR10D);  AddRegister( "R11D", InstructionSet.regR11D);
				AddRegister( "R12D", InstructionSet.regR12D);  AddRegister( "R13D", InstructionSet.regR13D);
				AddRegister( "R14D", InstructionSet.regR14D);  AddRegister( "R15D", InstructionSet.regR15D);

				AddRegister( "R8W", InstructionSet.regR8W);  AddRegister( "R9W", InstructionSet.regR9W);
				AddRegister( "R10W", InstructionSet.regR10W);  AddRegister( "R11W", InstructionSet.regR11W);
				AddRegister( "R12W", InstructionSet.regR12W);  AddRegister( "R13W", InstructionSet.regR13W);
				AddRegister( "R14W", InstructionSet.regR14W);  AddRegister( "R15W", InstructionSet.regR15W);

				AddRegister( "R8B", InstructionSet.regR8B);  AddRegister( "R9B", InstructionSet.regR9B);
				AddRegister( "R10B", InstructionSet.regR10B);  AddRegister( "R11B", InstructionSet.regR11B);
				AddRegister( "R12B", InstructionSet.regR12B);  AddRegister( "R13B", InstructionSet.regR13B);
				AddRegister( "R14B", InstructionSet.regR14B);  AddRegister( "R15B", InstructionSet.regR15B);
			END AddRegisters;

		BEGIN
			IF system = NIL THEN
				IF bits=32 THEN
					NEW(system,8,32, 8,32,32,32,64);
					Global.SetDefaultDeclarations(system,8);
					Global.SetDefaultOperators(system);
				ELSE
					NEW(system,8,64,8,64,64,64,128);
					Global.SetDefaultDeclarations(system,8);
					Global.SetDefaultOperators(system);
				END;
				AddRegisters
			END;
			RETURN system
		END GetSystem;

		PROCEDURE Supported(CONST instruction: IntermediateCode.Instruction; VAR moduleName, procedureName: ARRAY OF CHAR): BOOLEAN;
		BEGIN
			RETURN cg.Supported(instruction,moduleName,procedureName);
		END Supported;

		PROCEDURE GenerateBinary(module: Sections.Module; dump: Streams.Writer);
		VAR
			in,last: Sections.Section;
			out: BinaryCode.Section;
			name: SyntaxTree.String;
			procedure: SyntaxTree.Procedure;

		 	(* recompute fixup positions and assign binary sections *)
		 	PROCEDURE PatchFixups(section: BinaryCode.Section);
			VAR resolved: BinaryCode.Section; fixup: BinaryCode.Fixup; displacement,symbolOffset: LONGINT; in: IntermediateCode.Section;
			BEGIN
				fixup := section.fixupList.firstFixup;
				WHILE fixup # NIL DO
					IF  (fixup.symbol(IntermediateCode.Section).resolved # NIL) THEN
						resolved := fixup.symbol(IntermediateCode.Section).resolved(BinaryCode.Section);
						in := fixup.symbol(IntermediateCode.Section);
						symbolOffset := fixup.symbolOffset;
						IF symbolOffset = in.pc THEN
							displacement := resolved.pc
						ELSIF (symbolOffset # 0) THEN
							ASSERT(in.pc > symbolOffset);
							displacement := in.instructions[symbolOffset].pc;
						ELSE
							displacement := 0;
						END;
						fixup.SetSymbol(fixup.symbol(IntermediateCode.Section),0,fixup.displacement+displacement);
					END;
					fixup := fixup.nextFixup;
				END;
			END PatchFixups;

		BEGIN
		 	cg.SetModule(module);
		 	in := module.sections.first;
		 	WHILE in # NIL DO
		 		IF in.type = Sections.InlineCodeSection THEN
			 		COPY(in.name,name);
			 		out := ResolvedSection(in(IntermediateCode.Section));
			 		cg.Section(in(IntermediateCode.Section),out);
			 		procedure := in.symbol(SyntaxTree.Procedure);
			 		procedure.procedureScope.body.code.SetBinaryCode(out.bits);
			 	END;
		 		in := in.nextSection;
		 	END;

		 	REPEAT
			 	in := module.sections.first;
		 	 	last := module.sections.last;
			 	WHILE (in # NIL) DO
			 		IF (in.type # Sections.InlineCodeSection) & (in(IntermediateCode.Section).resolved = NIL) THEN
				 		COPY(in.name,name);
				 		IF SupportPool & usePool THEN
					 		pool.Work(in(IntermediateCode.Section), runtimeModuleName, diagnostics, module, bits);
				 		ELSE
					 		out := ResolvedSection(in(IntermediateCode.Section));
					 		cg.Section(in(IntermediateCode.Section),out);
					 		IF out.type = Sections.VarSection THEN
					 			IF out.pc = 1 THEN out.SetAlignment(FALSE,1)
					 			ELSIF out.pc = 2 THEN out.SetAlignment(FALSE,2)
					 			ELSIF out.pc > 2 THEN out.SetAlignment(FALSE,4)
					 			END;
					 		ELSIF out.type = Sections.ConstSection THEN
					 			out.SetAlignment(FALSE,4);
					 		END;
				 		END;
			 		END;
			 		IF in = last THEN
			 			in := NIL
			 		ELSE
				 		in := in.nextSection;
				 	END;
			 	END;
			 	IF SupportPool&usePool THEN pool.Wait END;
			UNTIL last = module.sections.last; (* process remaining sections that have been added during traversal of sections *)

		 	in := module.caseTables.first;
		 	WHILE in # NIL DO
		 		IF in(IntermediateCode.Section).resolved = NIL THEN
			 		out := ResolvedSection(in(IntermediateCode.Section));
			 		cg.Section(in(IntermediateCode.Section),out);
			 	END;
		 		in := in.nextSection;
		 	END;

		 	(*
		 	in := module.importedSymbols.first;
		 	WHILE in # NIL DO
		 		IF in(IntermediateCode.Section).resolved = NIL THEN
			 		out := ResolvedSection(in(IntermediateCode.Section));
			 		in := in.nextSection;
			 	END;
		 	END;

		 	in := module.systemCalls.first;
		 	WHILE in # NIL DO
		 		IF in(IntermediateCode.Section).resolved = NIL THEN
			 		out := ResolvedSection(in(IntermediateCode.Section));
			 		in := in.nextSection;
			 	END;
		 	END;
			*)

		 	in := module.sections.first;
		 	WHILE in # NIL DO
		 		PatchFixups(in(IntermediateCode.Section).resolved);
		 		in := in.nextSection;
		 	END;

		 	in := module.caseTables.first;
		 	WHILE in # NIL DO
		 		PatchFixups(in(IntermediateCode.Section).resolved);
		 		in := in.nextSection;
		 	END;

			IF cg.error THEN Error("",Diagnostics.Invalid, Diagnostics.Invalid,"") END;
		END GenerateBinary;

		PROCEDURE Module(x: SyntaxTree.Module): Formats.GeneratedModule;
		VAR
			dump: WMUtilities.WindowWriter;
			intermediateModule: Formats.GeneratedModule;
			dumpName: SyntaxTree.String;
		BEGIN
			intermediateModule := GenerateIntermediate(x);

			IF trace THEN
				dumpName := "AMD64 code trace: ";
				Strings.Append(dumpName,traceString);
				NEW(dump,dumpName,600,400,FALSE);
				dump.String("---------------- intermediate code -----------------"); dump.Ln;
				IF (traceString="") OR (traceString="*") THEN
					intermediateModule.Dump(dump);
					dump.Update
				ELSE
					Sections.DumpFiltered(dump,intermediateModule(Sections.Module),traceString);
				END
			END;

			IF ~error THEN
				GenerateBinary(intermediateModule(Sections.Module),dump);
				IF dump # NIL THEN
					dump.Ln; dump.Ln;
					dump.String("------------------ binary code -------------------"); dump.Ln;
					IF (traceString="") OR (traceString="*") THEN
						intermediateModule.Dump(dump);
						dump.Update
					ELSE
						Sections.DumpFiltered(dump,intermediateModule(Sections.Module),traceString);
						dump.Update;
					END
				END;
			END;
			RETURN intermediateModule
		END Module;

		PROCEDURE FindPC(x: SyntaxTree.Module; CONST sectionName: ARRAY OF CHAR; sectionOffset: LONGINT);
		VAR section:Sections.Section; binarySection: BinaryCode.Section; label: BinaryCode.LabelList; module: Formats.GeneratedModule;
		BEGIN
			module := Module(x);
			section := module(Sections.Module).sections.first;
			WHILE (section # NIL) & (section.name # sectionName) DO
				section := section.nextSection
			END;
			IF section = NIL THEN
				diagnostics.Error(module.module.sourceName,Diagnostics.Invalid,Diagnostics.Invalid," could not locate pc");
			ELSE
				binarySection := section(IntermediateCode.Section).resolved;
				label := binarySection.labels;
				WHILE (label # NIL) & (label.offset >= sectionOffset) DO
					label := label.prev;
				END;
				IF label # NIL THEN
					diagnostics.Information(module.module.sourceName,label.position,Diagnostics.Invalid," pc position");
				ELSE
					diagnostics.Error(module.module.sourceName,Diagnostics.Invalid,Diagnostics.Invalid," could not locate pc");
				END;
			END;
		END FindPC;

		PROCEDURE DefineOptions(options: Options.Options);
		BEGIN
			options.Add(0X,"bits",Options.Integer);
			DefineOptions^(options);
		END DefineOptions;

		PROCEDURE GetOptions(options: Options.Options);
		BEGIN
			IF ~options.GetInteger("bits",bits) THEN bits := 32 END;
			GetOptions^(options);
		END GetOptions;

		PROCEDURE DefaultObjectFileFormat(): Formats.ObjectFileFormat;
		BEGIN RETURN ObjectFileFormat.Get();
		END DefaultObjectFileFormat;

		PROCEDURE DefaultSymbolFileFormat(): Formats.SymbolFileFormat;
		BEGIN
			RETURN NIL
		END DefaultSymbolFileFormat;


	END BackendAMD64;
VAR pool: Pool;

	PROCEDURE Assert(b: BOOLEAN; CONST s: ARRAY OF CHAR);
	BEGIN
		ASSERT(b,100);
	END Assert;

	PROCEDURE Halt(CONST s: ARRAY OF CHAR);
	BEGIN
		HALT(100);
	END Halt;

	PROCEDURE ResolvedSection(in: IntermediateCode.Section): BinaryCode.Section;
	VAR section: BinaryCode.Section;
	BEGIN
		IF in.resolved = NIL THEN
			NEW(section,in.type, 8, in.name,in.comments # NIL,FALSE);
			section.SetAlignment(in.fixed, in.alignment);
			in.SetResolved(section);
		ELSE
			section := in.resolved
		END;
		RETURN section
	END ResolvedSection;

	PROCEDURE Init;
	VAR i: LONGINT;
	BEGIN
		FOR i := 0 TO LEN(registerOperands)-1 DO
			Assembler.InitRegister(registerOperands[i],i);
		END;

		opEAX := registerOperands[EAX];
		opEBX := registerOperands[EBX];
		opECX := registerOperands[ECX];
		opEDX := registerOperands[EDX];
		opESI := registerOperands[ESI];
		opEDI := registerOperands[EDI];
		opEBP := registerOperands[EBP];
		opESP := registerOperands[ESP];
		opRSP := registerOperands[RSP];
		opRBP := registerOperands[RBP];

		opAX := registerOperands[AX];
		opBX := registerOperands[BX];
		opCX := registerOperands[CX];
		opDX := registerOperands[DX];
		opSI := registerOperands[SI];
		opDI := registerOperands[DI];

		opAL := registerOperands[AL];
		opBL := registerOperands[BL];
		opCL := registerOperands[CL];
		opDL := registerOperands[DL];

		opAH := registerOperands[AH];
		opBH := registerOperands[BH];
		opCH := registerOperands[CH];
		opDH := registerOperands[DH];

		opST0 := registerOperands[ST0];

	END Init;

	PROCEDURE Get*(): Backend.Backend;
	VAR backend: BackendAMD64;
	BEGIN NEW(backend); RETURN backend
	END Get;

BEGIN
	Init;
	usePool := Machine.NumberOfProcessors()>1;
	IF SupportPool & usePool THEN NEW(pool) END;
END OCAMDBackend.
