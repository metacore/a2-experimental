(**
	AUTHOR: Alexey Morozov
	PURPOSE: high precision timer support for Windows platforms
*)
MODULE PrecisionTimer;

IMPORT
	Kernel32, KernelLog;

TYPE
	Counter* = SIGNED64;

CONST

	(**
		Query timer counter in ticks
	*)
	PROCEDURE GetCounter*(): Counter;
	VAR counter: Kernel32.LargeInteger;
	BEGIN
		IF Kernel32.QueryPerformanceCounter(counter) # 0 THEN
			RETURN counter.QuadPart;
		ELSE
			RETURN 0;
		END;
	END GetCounter;

	(**
		Query timer tick frequency in Hz
	*)
	PROCEDURE GetFrequency*(): Counter;
	VAR frequencyInHz: Kernel32.LargeInteger;
	BEGIN
		IF Kernel32.QueryPerformanceFrequency(frequencyInHz) # 0 THEN
			RETURN frequencyInHz.QuadPart;
		ELSE
			RETURN 0;
		END;
	END GetFrequency;

	PROCEDURE InitMod;
	BEGIN
		KernelLog.String("PrecisionTimer: timer tick frequency is "); KernelLog.Int(GetFrequency(),0); KernelLog.String(" Hz"); KernelLog.Ln;
	END InitMod;

BEGIN
	InitMod;
END PrecisionTimer.

System.FreeDownTo PrecisionTimer ~