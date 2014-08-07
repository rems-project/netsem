#include "ntpheader.h"

#ifdef WIN32
#include <winsock2.h>
#include <windows.h>
#endif
#include <string.h>

#ifndef WIN32
void printNTPheader(int outfd)
{
  pid_t pid;
  int status;
  FILE *outfile;

  outfile = fdopen(outfd, "a");

  if((pid = fork()) == 0) {
    if(dup2(outfd, 1) == -1 ) {
      fprintf(outfile, " printNTPheader: error duplicating fd\n");
      return;
    }
    if(execl("/usr/bin/ntpq", "/usr/bin/ntpq", "-c", "readvar 0 offset", NULL) == -1) {
      fprintf(outfile, " printNTPheader: error executing ntpd\n");
      return;
    }
  } else {
    wait(&status);
  }

  return;
}

#else
void print_ntp(SOCKET sd, char *str)
{
  int i, res;
  size_t len;
  char *string;

  len = strlen(str);
  string = str;

  //Write the string to the socket, trying
  //NUMSENDRETRIES times.
  for(i=0; i<10; i++) {
    res = send(sd, string, (int)len, 0);

    if(res != -1) {
      if(len != res) { //whole string not sent
	string += res; //so send the remainder
	len = strlen(string);
	i=0;           //reset number of retries
	continue;	   //and try again
      } else {         //else all is written
	return;		   //so return
      }
    } else {				//an error occured so retry send
      if(WSAGetLastError() == WSAEWOULDBLOCK)   //if error is EAGAIN then reset
	i=0;				//the number of retries counter
        continue;
    }
  }

  printf("ntpheader(): failed to write to connected socket");
  exit(1);
}

void printNTPheader(SOCKET outfd)
{
	char buf[200];
	STARTUPINFO startupinfo;
	PROCESS_INFORMATION pi;

/* Thanks to MSDN
   /library/en-us/dllproc/base/creating_a_child_process_with_redirected_input_and_output.asp
   for this code. */

        HANDLE hChildStdoutRd, hChildStdoutWr, hChildStdoutRdDup, hSaveStdout;
        SECURITY_ATTRIBUTES saAttr;
        BOOL fSuccess;

#define BUFSIZE 4096
        DWORD dwRead;
        CHAR chBuf[BUFSIZE+1];   /* for terminal NUL */

// Set the bInheritHandle flag so pipe handles are inherited.

        saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
        saAttr.bInheritHandle = TRUE;
        saAttr.lpSecurityDescriptor = NULL;

   // The steps for redirecting child process's STDOUT:
   //     1. Save current STDOUT, to be restored later.
   //     2. Create anonymous pipe to be STDOUT for child process.
   //     3. Set STDOUT of the parent process to be write handle to
   //        the pipe, so it is inherited by the child process.
   //     4. Create a noninheritable duplicate of the read handle and
   //        close the inheritable read handle.

// Save the handle to the current STDOUT.

        hSaveStdout = GetStdHandle(STD_OUTPUT_HANDLE);

// Create a pipe for the child process's STDOUT.

        if (! CreatePipe(&hChildStdoutRd, &hChildStdoutWr, &saAttr, 0))
          print_ntp(outfd,"Stdout pipe creation failed\n");

// Set a write handle to the pipe to be STDOUT.

        if (! SetStdHandle(STD_OUTPUT_HANDLE, hChildStdoutWr))
          print_ntp(outfd,"Redirecting STDOUT failed");

// Create noninheritable read handle and close the inheritable read
// handle.

        fSuccess = DuplicateHandle(GetCurrentProcess(), hChildStdoutRd,
                                   GetCurrentProcess(), &hChildStdoutRdDup , 0,
                                   FALSE,
                                   DUPLICATE_SAME_ACCESS);
        if( !fSuccess )
          print_ntp(outfd,"DuplicateHandle failed");
        CloseHandle(hChildStdoutRd);

	ZeroMemory(&startupinfo,sizeof(startupinfo));
	startupinfo.cb = sizeof(startupinfo);
        ZeroMemory(&pi,sizeof(pi));
	strcpy(buf,"\"D:\\Program Files\\NTP\\ntp-4.1.2-nt\\ntpq.exe\" -c \"readvar 0 offset\"");
	if (0 == CreateProcess(
				"D:\\Program Files\\NTP\\ntp-4.1.2-nt\\ntpq.exe",
				buf,
				NULL,
				NULL,
				TRUE,
				0,
				NULL,
				NULL,
				&startupinfo,
				&pi)) {
		print_ntp(outfd," printNTPheader: error executing ntpd\n");
	}
        // (to wait for termination, do: WaitForSingleObject(pi.hProcess, INFINITE);)
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);

// After process creation, restore the saved STDOUT.

        if (! SetStdHandle(STD_OUTPUT_HANDLE, hSaveStdout))
          print_ntp(outfd,"Re-redirecting Stdout failed\n");
		if (!CloseHandle(hChildStdoutWr)) {
			print_ntp(outfd,"Error closing hChildStdoutWr\n");
		}

// Copy from pipe that is the standard output for child process, to outfd socket:
		for (;;) {
	      dwRead = 0;
		  if (!ReadFile(hChildStdoutRdDup, chBuf, BUFSIZE, &dwRead, NULL) || dwRead == 0) {
            break;
          }
		  chBuf[dwRead] = '\0';
          print_ntp(outfd,chBuf);
        }

// all done!
        CloseHandle(hChildStdoutRdDup);
        return;
}

#endif
