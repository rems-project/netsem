@echo off
D:
cd\

D:\windows\system32\net stop "Netsem TThee CustomRSH"

rmdir /Q/S Net

"D:\Program Files\GNU\WinCVS 1.2\cvs" -d \\elmer\grp-th1\netsem\cvs co Net/TCP/Test

cd\Net\TCP\Test
nmake /f Makefile.win clean
nmake /f Makefile.win all

D:\windows\system32\net start "Netsem TThee CustomRSH"

