// main.cpp : Defines the entry point for the console application.
//

// An example of the use of TSCtime.

#include <windows.h>
#include <stdio.h>
#include <conio.h>
#include <tchar.h>

#include "TSCtime.h"

int _tmain(int argc, _TCHAR* argv[])
{
    const DWORD trialmsec = 10000;

	printf("Gidday, planet!\n");

	// recalibrate
	recalibrate();

	// get start time
	ULONGLONG then = gethectonanotime_last();

	// get later times
	Sleep(trialmsec);
	ULONGLONG now = gethectonanotime_first();

	ULONGLONG delta = now - then;
	printf("Time delta was %I64u.%07I64usec.\n",
		delta/10000000uI64,delta%10000000uI64);
	printf("Time since epoch is %I64u.%07I64usec\n",now/10000000uI64,now%10000000uI64);

	printf("BTW, then was %I64u.%07I64usec after the base time.\n",(then-basest)/1000000uI64,(then-basest)%10000000uI64);

	_getch();
	return 0;
}


