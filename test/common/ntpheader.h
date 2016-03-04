#ifndef WIN32
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#else
#include <winsock2.h>
#include <windows.h>
#endif

#include <stdio.h>

#ifndef WIN32
extern void printNTPheader(int outfd);
#else
extern void printNTPheader(SOCKET outfd);
#endif
