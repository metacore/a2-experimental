MODULE EFIMachine; (** AUTHOR ""; PURPOSE ""; *)

IMPORT SYSTEM, EFI;

(*  I386.Machine.Mod uses following registers as arguments:
	eax	: bootFlag (= address of boot table)
	esi	: ?
	edi	: address of frame buffer
*)
PROCEDURE JumpTo*(adr : SYSTEM.ADDRESS; eax,esi,edi : LONGINT);
CODE {SYSTEM.i386}
	XOR ECX,ECX
	XOR EDX,EDX
	MOV EDI, [EBP+edi];
	MOV ESI, [EBP+esi];
	MOV EAX, [EBP+eax];
	MOV EBX, [EBP+adr]
	CALL EBX
END JumpTo;

PROCEDURE -GetParameter (offset: LONGINT): LONGINT;
CODE {SYSTEM.i386}
	POP EAX
	MOV EAX, [EBP+EAX]
END GetParameter;

BEGIN
	SYSTEM.PUT32 (SYSTEM.ADR (EFI.imageHandle), GetParameter (12));
	SYSTEM.PUT32 (SYSTEM.ADR (EFI.table), GetParameter (16));
END EFIMachine.
