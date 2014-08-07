@echo off
set EXEC_LIBD=D:/Net/TCP/Test/libd/libd.exe
set EXEC_SLURP=D:/Net/TCP/Test/slurp/slurp.exe
set EXEC_INJECTOR=D:/Net/TCP/Test/injector/injector.exe
set EXEC_HOLTCPCB=

D:
cd \Net\TCP\Test\utils\custom_rsh
custom_rsh 0.0.0.0 100
