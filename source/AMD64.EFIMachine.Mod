MODULE EFIMachine; (** AUTHOR ""; PURPOSE ""; *)

IMPORT SYSTEM, EFI;

VAR p0, p1: SYSTEM.ADDRESS;

(*  I386.Machine.Mod uses following registers as arguments:
	eax	: bootFlag (= address of boot table)
	esi	: ?
	edi	: address of frame buffer
*)
PROCEDURE JumpTo*(adr : SYSTEM.ADDRESS; eax,esi,edi : HUGEINT);
CODE {SYSTEM.AMD64}
	XOR ECX,ECX
	XOR EDX,EDX
	MOV EDI, [EBP+edi];
	MOV ESI, [EBP+esi];
	MOV EAX, [EBP+eax];
	MOV EBX, [EBP+adr]
	CALL EBX
END JumpTo;

PROCEDURE -GetParameters;
CODE {SYSTEM.AMD64}
	MOV QWORD p0, RDX;
	MOV QWORD p1, RCX
END GetParameters;

BEGIN
	SYSTEM.PUT64(SYSTEM.ADR(EFI.imageHandle), p0);
	SYSTEM.PUT64(SYSTEM.ADR(EFI.table), p1);
END EFIMachine.
