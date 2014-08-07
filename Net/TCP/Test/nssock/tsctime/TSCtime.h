// TSCtime.h : header file for high-precision time library
//

// $Id: TSCtime.h,v 1.4 2003/09/25 17:07:23 kw217 Exp $

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

// NB: epoch for hectonanotime is January 1, 1601 UTC,
//     so subtract 11644473600 seconds to get Unix time.
//     (369 years, 89 of which are leap years;
//      = 134774 days)

#define UNIX_EPOCH 116444736000000000ui64

// be sure to build in Release configuration, and make sure inlining is on.
extern __forceinline ULONGLONG gettsc(void) {
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

extern ULONGLONG basetsc;
extern ULONGLONG basest;
extern ULONGLONG tscfreq;
extern ULONGLONG tscsd;

extern __forceinline ULONGLONG hectonanotime_of_tsc(ULONGLONG curtsc) {
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
extern ULONGLONG lastrecal;

// recalibrate -- may take up to 100msec or so.  Updates the four static globals above.
void recalibrate(void);

// get current time, without recalibration
extern __forceinline ULONGLONG gethectonanotime_norecal(void) {
	ULONGLONG curtsc;

	// get the timestamp right up front
	curtsc = gettsc();
	return hectonanotime_of_tsc(curtsc);
}

// interval between automatic recalibrations
extern ULONGLONG recalinterval;

// get time of call, possibly recalibrating before returning
extern __forceinline ULONGLONG gethectonanotime_first(void) {
	ULONGLONG curtsc = gettsc();
	ULONGLONG now = hectonanotime_of_tsc(curtsc);
	if ((lastrecal == 0) || (now - lastrecal) > recalinterval) {
		recalibrate();
		now = hectonanotime_of_tsc(curtsc);
	}
	return now;
}

// get time of return, possibly recalibrating before returning
extern __forceinline ULONGLONG gethectonanotime_last(void) {
	(void)gethectonanotime_first();
	return gethectonanotime_norecal();
}
