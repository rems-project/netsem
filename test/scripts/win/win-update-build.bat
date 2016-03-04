@ECHO OFF
D:
cd\Net\TCP\Test
"D:\Program Files\GNU\WinCVS 1.2\cvs" -d \\elmer\grp-th1\netsem\cvs update -Pd

D:\windows\system32\net stop "Netsem TThee CustomRSH"

nmake /f Makefile.win clean
nmake /f Makefile.win all


D:\windows\system32\net start "Netsem TThee CustomRSH"

