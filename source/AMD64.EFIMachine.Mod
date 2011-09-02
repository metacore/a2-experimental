MODULE EFIMachine; (** AUTHOR ""; PURPOSE ""; *)

IMPORT SYSTEM, EFI;

VAR p0, p1: SYSTEM.ADDRESS;

(*  I386.Machine.Mod uses following registers as arguments:
	eax	: bootFlag (= address of boot table)
	esi	: ?
	edi	: address of frame buffer
*)
PROCEDURE JumpTo*(adr : SYSTEM.ADDRESS; eax,esi,edi,ecx : HUGEINT);
CODE {SYSTEM.AMD64}
	XOR RCX,RCX
	XOR RDX,RDX
	MOV RDI, [RBP+edi];
	MOV RSI, [RBP+esi];
	MOV RAX, [RBP+eax];
	MOV RBX, [RBP+adr]
	MOV RCX, [RBP+ecx]
	CALL RBX
END JumpTo;

PROCEDURE {NOPAF, FIXED(401000H)} EntryPoint;
CODE {SYSTEM.AMD64}
	MOV QWORD EFI.imageHandle, RCX;
	MOV QWORD EFI.table, RDX
END EntryPoint;

END EFIMachine.
