// TimeTest.cpp : Defines the entry point for the console application.
//

#include "stdafx.h"
#include <sys/timeb.h>
#include <math.h>
#include <conio.h>

// be sure to build in Release configuration, and make sure inlining is on.
__forceinline ULONGLONG gettsc(void) {
	ULONG hi,lo;
	LARGE_INTEGER r;
	__asm {
		rdtsc
		mov hi,edx
		mov lo,eax
	}
	r.HighPart = hi;
	r.LowPart = lo;
	return r.QuadPart;
}

static ULONGLONG basetsc = 0;                 // base timestamp in processor clocks
static ULONGLONG basest  = 0;                 // base time in hecto-nanoseconds (100ns units, 10^-7 sec)
static ULONGLONG tscfreq = 500000000uI64;     // timestamp clock frequency in ticks/second
static ULONGLONG tscsd   = 500000000uI64;     // measured error (standard deviation) of above

__forceinline ULONGLONG hectonanotime_of_tsc(ULONGLONG curtsc) {
    // compute seconds and hectonanoseconds separately to avoid overflow problems
	// deltaticks may be negative if we're measuring first and calibrating later
	bool neg = curtsc < basetsc;
	ULONGLONG deltaticks = neg ? basetsc - curtsc : curtsc - basetsc;
	ULONGLONG deltasecs = deltaticks / tscfreq;
	ULONGLONG deltafrac = (10000000 * (deltaticks % tscfreq)) / tscfreq;  /* in hectonanoseconds */
	ULONGLONG delta = deltasecs * 10000000 + deltafrac;
	return (neg ? basest - delta : basest + delta);
}

// store time of last recalibration
static ULONGLONG lastrecal = 0;  // hectonanosecond time since epoch of last recalibration; 0 == never

// recalibrate -- may take up to 100msec or so.  Updates the four static globals above.
void recalibrate(void) {
	const int nreps = 5;  // number of ticks to examine; we take the average.

	ULONGLONG basetscs[nreps];  // basetsc for each round
	ULONGLONG basests[nreps];   // basest for each round

	// read calibration
	HKEY key;
	DWORD cbData;
	RegOpenKeyEx(HKEY_LOCAL_MACHINE,"SOFTWARE\\NetSem\\TTHEE",0,KEY_READ,&key);
	cbData = sizeof(tscfreq);
	RegQueryValueEx(key,"tscfreq",NULL,NULL,(BYTE *)&tscfreq,&cbData);
	cbData = sizeof(tscsd);
	RegQueryValueEx(key,"tscsd",NULL,NULL,(BYTE *)&tscsd,&cbData);
	// double error = double(tscsd) / double(tscfreq);

	// get base times
	for (int i=0; i<nreps; i++) {
		FILETIME baseft;
		Sleep(5);  // to be sure we're on a tick boundary
		basetscs[i] = gettsc();  // get this first because it changes very fast
		GetSystemTimeAsFileTime(&baseft);  // no rush; we have 1/64 sec to read this before it changes
		basests[i] = ULONGLONG(baseft.dwHighDateTime)<<32 | ULONGLONG(baseft.dwLowDateTime);
	}

	basetsc = basetscs[nreps-1];
	/* Now: we want to know the correct basest for the latest basetsc.  Each measurement can be
	   extrapolated to give us a basest for the latest basetsc.  But if there was a delay between the
	   tick and our process being scheduled in a particular round, this will show up as the basetsc
	   being high, a.k.a., the basest being low.  Thus, we take the highest computed basest. */
	basest = basests[nreps-1];
	for (int i=0; i<nreps; i++) {
		ULONGLONG basestx = basests[i] + (10000000 * (basetscs[nreps-1] - basetscs[i])) / tscfreq;
			// don't worry about overflow; at 500MHz (glia) it won't overflow until just over an hour
		if (basestx > basest) {
			basest = basestx;
		}
	}

	lastrecal = basest;  // we just recalibrated.
}

// get current time, without recalibration
__forceinline ULONGLONG gethectonanotime_norecal(void) {
	ULONGLONG curtsc;

	// get the timestamp right up front
	curtsc = gettsc();
	return hectonanotime_of_tsc(curtsc);
}

// interval between automatic recalibrations
const ULONGLONG recalinterval = 1000000000uI64;  // recal every 100sec.

// get time of call, possibly recalibrating before returning
__forceinline ULONGLONG gethectonanotime_first(void) {
	ULONGLONG curtsc = gettsc();
	ULONGLONG now = hectonanotime_of_tsc(curtsc);
	if ((lastrecal == 0) || (now - lastrecal) > recalinterval) {
		recalibrate();
		now = hectonanotime_of_tsc(curtsc);
	}
	return now;
}

// get time of return, possibly recalibrating before returning
__forceinline ULONGLONG gethectonanotime_last(void) {
	(void)gethectonanotime_first();
	return gethectonanotime_norecal();
}

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

	double error = double(tscsd) / double(tscfreq);
	ULONGLONG delta = now - then;
	double deltaerr = (double(now-lastrecal)/ 10000000.0) * error;
	printf("Time delta was %I64u.%07I64usec, +/- %0.7fsec\n",
		delta/10000000uI64,delta%10000000uI64,
		deltaerr);
	printf("Time since epoch is %I64u.%07I64usec\n",now/10000000uI64,now%10000000uI64);

	printf("BTW, then was %I64u.%07I64usec after the base time.\n",(then-basest)/1000000uI64,(then-basest)%10000000uI64);

	_getch();
	return 0;
}

