cd \ETHOberon

zip -9 System1.zip .\*.* System\*.* Work\*.* Obj\A*
zip -9 System1.zip Apps\Desk.oaf Apps\GUI.oaf Apps\TUI.oaf Apps\Win32.Win.oaf
zip -9 System1.zip Apps\Win32.Network.oaf Apps\PictConverters.oaf

zip -9 System2.zip Obj\*.* -x Obj\Oberon.EXE Obj\Oberon.DLL Obj\A*

zip -9 Docu.zip Docu\*.*

zip -9 Src.zip Src\*.* Apps\Win32.Developer.oaf

zip -9 AppsAH.zip Apps\A* Apps\B* Apps\C* Apps\E* Apps\F* Apps\H*
zip -9 AppsAH.zip Apps\D* Apps\G* -x Apps\Desk.oaf Apps\GUI.oaf
zip -9 AppsAH.zip Apps\Win32.Backup.oaf Apps\Win32.CUSM.oaf Apps\Win32.Dim3.oaf Apps\Win32.GhostPrinter.oaf

zip -9 AppsIZ.zip Apps\I* Apps\J* Apps\K* Apps\L* Apps\M* Apps\N* Apps\O* Apps\Q* Apps\R* Apps\S* Apps\U* Apps\V* Apps\X* Apps\Y* Apps\Z*
zip -9 AppsIZ.zip Apps\P* Apps\T* Apps\W* -x Apps\PictConverters.oaf Apps\Pr?Fnt.oaf Apps\TUI.oaf Apps\Win32*
zip -9 AppsIZ.zip Apps\Win32.Images.oaf Apps\Win32.Magnifier.oaf Apps\Win32.NPPlugIn.oaf Apps\Win32.OLEObjects.oaf
zip -9 AppsIZ.zip Apps\Win32.Snapshot.oaf Apps\Win32.WinPSPrinter.oaf Apps\WTS.oaf

zip -9 PrFnt.zip Apps\Pr?Fnt.oaf

REM use WinZIP for EXEs
REM copy /b \winnt\sfxwiz32.exe+System1.zip System1.exe
REM copy /b \winnt\sfxwiz32.exe+System2.zip System2.exe
REM copy /b \winnt\sfxwiz32.exe+Docu.zip Docu.exe
REM copy /b \winnt\sfxwiz32.exe+Src.zip Src.exe
REM copy /b \winnt\sfxwiz32.exe+AppsAH.zip AppsAH.exe
REM copy /b \winnt\sfxwiz32.exe+AppsIZ.zip AppsIZ.exe
REM copy /b \winnt\sfxwiz32.exe+PrFnt.zip PrFnt.exe

REM del *.zip
