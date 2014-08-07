// TSCtime.c : high-precision time library
//

// $Id: TSCtime.c,v 1.7 2003/09/25 17:07:23 kw217 Exp $

//
// Copyright (c) 2003, Keith Wansbrough
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//
//     * Redistributions of source code must retain the above
//       copyright notice, this list of conditions and the following
//       disclaimer.
//     * Redistributions in binary form must reproduce the above
//       copyright notice, this list of conditions and the following
//       disclaimer in the documentation and/or other materials provided
//       with the distribution.
//     * Neither the name of the University of Cambridge nor the names of its
//       contributors may be used to endorse or promote products derived
//       from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
// FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
// COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
// HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
// OF THE POSSIBILITY OF SUCH DAMAGE.
//

// (for information only: this is the BSD license as found on
//  http://www.opensource.org/licenses/bsd-license.php)

#include <windows.h>

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

ULONGLONG basetsc = 0;                 // base timestamp in processor clocks
ULONGLONG basest  = 0;                 // base time in hecto-nanoseconds (100ns units, 10^-7 sec)
ULONGLONG tscfreq = 500000000uI64;     // timestamp clock frequency in ticks/second
ULONGLONG tscsd   = 500000000uI64;     // measured error (standard deviation) of above
ULONGLONG ugly_hack_offset = 0;        // correction to add to returned time
  // this accounts for the fact that we never get control exactly at the tick; it's always
  // a bit later than that.  The value is a guesstimate.
  // This is stored as a string value (for easy editing) in the registry.

  // ** Turns out that isn't necessary for our tests; but we leave the hook here just in case.


__forceinline ULONGLONG hectonanotime_of_tsc(ULONGLONG curtsc) {
    // compute seconds and hectonanoseconds separately to avoid overflow problems
	// deltaticks may be negative if we're measuring first and calibrating later
	BOOL neg = curtsc < basetsc;
	ULONGLONG deltaticks = neg ? basetsc - curtsc : curtsc - basetsc;
	ULONGLONG deltasecs = deltaticks / tscfreq;
	ULONGLONG deltafrac = (10000000 * (deltaticks % tscfreq)) / tscfreq;  /* in hectonanoseconds */
	ULONGLONG delta = deltasecs * 10000000 + deltafrac;
	return (neg ? basest - delta : basest + delta);
}

// store time of last recalibration
ULONGLONG lastrecal = 0;  // hectonanosecond time since epoch of last recalibration; 0 == never

// recalibrate -- may take up to 100msec or so.  Updates the four static globals above.
#define nreps 5  // number of ticks to examine; we take the average.
void recalibrate(void) {
	int i;

	ULONGLONG basetscs[nreps];  // basetsc for each round
	ULONGLONG basests[nreps];   // basest for each round

        char buf[100] = "0";

	// read calibration
	HKEY key;
	DWORD cbData;
	RegOpenKeyEx(HKEY_LOCAL_MACHINE,"SOFTWARE\\NetSem\\TTHEE",0,KEY_READ,&key);
	cbData = sizeof(tscfreq);
	RegQueryValueEx(key,"tscfreq",NULL,NULL,(BYTE *)&tscfreq,&cbData);
	cbData = sizeof(tscsd);
	RegQueryValueEx(key,"tscsd",NULL,NULL,(BYTE *)&tscsd,&cbData);
	// double error = double(tscsd) / double(tscfreq);
        cbData = sizeof(buf)-1;
	RegQueryValueEx(key,"ugly_hack_offset",NULL,NULL,(BYTE *)buf,&cbData);
        buf[cbData] = '\0';
        ugly_hack_offset = _atoi64(buf);

	// get base times
	for (i=0; i<nreps; i++) {
		FILETIME baseft;
		Sleep(5);  // to be sure we're on a tick boundary
		basetscs[i] = gettsc();  // get this first because it changes very fast
		GetSystemTimeAsFileTime(&baseft);  // no rush; we have 1/64 sec to read this before it changes
		basests[i] = ((ULONGLONG)baseft.dwHighDateTime)<<32 | ((ULONGLONG)baseft.dwLowDateTime);
	}

	basetsc = basetscs[nreps-1];
	/* Now: we want to know the correct basest for the latest basetsc.  Each measurement can be
	   extrapolated to give us a basest for the latest basetsc.  But if there was a delay between the
	   tick and our process being scheduled in a particular round, this will show up as the basetsc
	   being high, a.k.a., the basest being low.  Thus, we take the highest computed basest. */
	basest = basests[nreps-1];
	for (i=0; i<nreps; i++) {
		ULONGLONG basestx = basests[i] + (10000000 * (basetscs[nreps-1] - basetscs[i])) / tscfreq;
			// don't worry about overflow; at 500MHz (glia) it won't overflow until just over an hour
		if (basestx > basest) {
			basest = basestx;
		}
	}

        basest -= ugly_hack_offset;   // apply the hack offset.

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
ULONGLONG recalinterval = 1000000000uI64;  // recal every 100sec.

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
