// TSCcal.cpp : Defines the entry point for the console application.
//

// $Id: TSCcal.cpp,v 1.3 2004/01/19 14:00:22 smb50 Exp $

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
#include <stdio.h>
#include <tchar.h>
#include <math.h>

//#define DEBUG

#ifdef DEBUG
#include <conio.h>
#endif

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

int _tmain(int argc, _TCHAR* argv[])
{
#ifdef DEBUG
	printf("Gidday, planet!\n");
#endif

	ULONGLONG basetsc,curtsc;  // in processor clocks
	FILETIME baseft,curft;     // in hecto-nanoseconds (100ns units, 10^-7 sec)
	ULONGLONG basest, curst;

	int numtrials = 10;
	DWORD trialmsec = 10000;
	if (argc==3) {
		numtrials = _ttoi(argv[1]);
		trialmsec = _ttoi(argv[2]);
	}
#ifdef DEBUG
	else {
		printf("WARNING: Usage: %s numtrials trialmsec\n",argv[0]);
	}
#endif

	double *rate = new double[numtrials];
	ULONGLONG *dur = new ULONGLONG[numtrials];


#ifdef DEBUG
   	LARGE_INTEGER ld;
	QueryPerformanceFrequency(&ld);
	printf("For comparison, QueryPerformanceFrequency says %I64u\n",ld.QuadPart);
#endif

	for (int i=0; i<numtrials; i++) {  // let's do it a few times for good measure

	// get base times
	Sleep(5);  // to be sure we're on a tick boundary
    basetsc = gettsc();  // get this first because it changes very fast
    GetSystemTimeAsFileTime(&baseft);  // no rush; we have 1/64 sec to read this before it changes

	// get later times
	Sleep(trialmsec);
    curtsc = gettsc();
    GetSystemTimeAsFileTime(&curft);

    // coerce filetimes
	basest = ULONGLONG(baseft.dwHighDateTime)<<32 | ULONGLONG(baseft.dwLowDateTime);
    curst = ULONGLONG(curft.dwHighDateTime)<<32 | ULONGLONG(curft.dwLowDateTime);

    // do calibration
	// NB: dwLowDateTime wraps every 429.5 seconds, so don't just use that!
	ULONGLONG deltsc = curtsc - basetsc;
	ULONGLONG delst = curst - basest;
	double tscrate = double(deltsc) / (double(delst) / 1e7);

#ifdef DEBUG
	printf("Tick delta %I64u, hectonanosecond delta %I64u.\nSo ticks/sec = %0.4f\n",deltsc,delst,tscrate);
#endif

	rate[i] = tscrate;
	dur[i] = delst;
	}

	ULONGLONG sumdur = 0;
	for (int i=0; i<numtrials; i++) {
		sumdur += dur[i];
	}
	double avdur = double(sumdur) / numtrials / 1e7;

	double minrate, maxrate;
	minrate = maxrate = rate[0];
	for (int i=1; i<numtrials; i++) {
		if (rate[i]<minrate) { minrate = rate[i]; }
		if (rate[i]>maxrate) { maxrate = rate[i]; }
	}
	double sum = 0;
	for (int i=0; i<numtrials; i++) { sum += rate[i]; }
	double av = sum / numtrials;
	double sumsqdiff = 0;
	for (int i=0; i<numtrials; i++) { double diff = rate[i] - av; sumsqdiff += diff*diff; }
	double sd = sqrt(sumsqdiff/numtrials);

#ifdef DEBUG
	printf("Mean rate  %14.4f ticks/sec\n      min -%14.4f\n      max +%14.4f\n      s.d. %14.4f\n",av,av-minrate,maxrate-av,sd);

	printf("Scheduling noise (TSC measurement precision):\n  min -%14.4f ticks\n  max +%14.4f\n  s.d. %14.4f\n",
			avdur * (av-minrate), avdur * (maxrate-av), avdur * sd);
#endif

	ULONGLONG tcsfreq = ULONGLONG(floor(av+0.5));
	ULONGLONG tcssd = ULONGLONG(floor(sd+0.5));
	SYSTEMTIME syst;
	GetSystemTime(&syst);
	char buf[100];
	sprintf(buf,"%04d-%02d-%02dT%02d:%02d:%02dZ",syst.wYear,syst.wMonth,syst.wDay,syst.wHour,syst.wMinute,syst.wSecond);

	HKEY key;
	RegCreateKeyEx(HKEY_LOCAL_MACHINE,"SOFTWARE\\NetSem\\TTHEE",0,NULL,REG_OPTION_NON_VOLATILE,KEY_ALL_ACCESS,NULL,&key,NULL);
    RegSetValueEx(key,"tscfreq",0,REG_QWORD,(const BYTE *)&tcsfreq,8);
	RegSetValueEx(key,"tscsd",0,REG_QWORD,(const BYTE *)&tcssd,8);
	RegSetValueEx(key,"tcslastupdate",0,REG_SZ,(const BYTE *)buf,DWORD(strlen(buf))+1);

#ifdef DEBUG
	_getch();
#endif

	return 0;
}

