/* Modified version by Steve Bishop, University of Cambridge Computer Laboratory
 * $Id: holtcpcb-v8.c,v 1.17 2005/02/04 10:14:35 kw217 Exp $
 */

/*
 * Copyright (c) 1983, 1988, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *	This product includes software developed by the University of
 *	California, Berkeley and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/* Licensing stuff */
#ifndef lint
static const char copyright[] =
"@(#) Copyright (c) 1983, 1988, 1993\n\
	The Regents of the University of California.  All rights reserved.\n";
#endif /* not lint */
#ifndef lint
#if 0
static char sccsid[] = "@(#)trpt.c	8.1 (Berkeley) 6/6/93";
#endif
static const char rcsid[] =
  "$FreeBSD: src/usr.sbin/trpt/trpt.c,v 1.12 2000/01/29 11:49:07 shin Exp $";
#endif /* not lint */

/* -------------------------------- */

#include <sys/param.h>
#include <sys/queue.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/socketvar.h>
#define PRUREQUESTS
#include <sys/protosw.h>
#include <sys/file.h>
#include <sys/time.h>
#include <sys/errno.h>

#include <net/route.h>
#include <net/if.h>

#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#ifdef INET6
#include <netinet/ip6.h>
#endif
#include <netinet/ip_var.h>
#include <netinet/tcp.h>
#define TCPSTATES
#include <netinet/tcp_fsm.h>
#include <netinet/tcp_seq.h>
#define	TCPTIMERS
#include <netinet/tcp_timer.h>
#include <netinet/tcp_var.h>
#include <netinet/tcpip.h>
#define	TANAMES
#include <netinet/tcp_debug.h>

#include <arpa/inet.h>

#include <err.h>
#include <nlist.h>
#include <paths.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <unistd.h>

#include <time.h>
#include "../../common/ntpheader.h"
/* -------------------------------- */


/* Partially define an initial name list.
 *
 * This is completed by the nlist function
 * which looks up the defined names in a file's
 * (in our case, the Kernel's) symbols table
 * and completes with their offsets.
 */
struct nlist nl[] = {
#define	N_TCP_DEBUG	0
	{ "_tcp_debug" },
#define	N_TCP_DEBX	1
	{ "_tcp_debx" },
	{ "" },
};

//Some definitiions
#define SOCKET_ERROR -1
#define ERRNO errno
#define NUMSENDRETRIES 5

//Amount of time we sleep before polling for updates
//in the ringbuffer
struct timespec sleeptime;

//Time variable (time since utc in usecs)
//Holds time of the trace record that is currently
//being processed
static struct timeval* ntime;

//Cmd-line options
static int nmask, showzero, port;
static char *ipaddr;

//Socket to write output to
//If no IP/Port are specified on the command-line
//this defaults to stdout
static int sd = 1;

//Handle to kernel core
static int memf;

//Sequence numbers used by timestamp pretty printer
unsigned long printing_seqno = 0;

//Function definitions for functions implemented
//later in this file
void dotrace();
void tcp_hol_trace(struct tcpcb *tp, struct ip *ip4,
		   struct tcphdr *th, short ostate, struct tcpcb *realtp,
		   short action);
void tcp_trace(struct tcp_debug *td, struct tcpcb *tp, struct ip *ip4,
	       struct tcphdr *th, short ostate);
static void usage __P((void));
void klseek __P((int, off_t, int));
void printtimestamp(void);
void print(char *str, ...);

/* -------------------------------- */

int main(int argc, char **argv)
{
  int ch, ret, dummy=1;
  char *system, *core;
  char *timestr, hostname[100];
  time_t currtime;
  struct sockaddr_in dest;

  /* Default values */
  nmask = 15;    //don't mask any tcp actions
  showzero = 1;  //print zero tcpcb entries

  //Amount of time we sleep before polling for updates
  //in the ringbuffer
  sleeptime.tv_sec = 0;
  sleeptime.tv_nsec = 1000;

  //Parse cmd-line args
  while ((ch = getopt(argc, argv, "n:z")) != -1)
    switch (ch) {
    case 'n':
      (void)sscanf(optarg, "%d", (int *)&nmask);
      break;
    case 'z':
      showzero = 0;
      break;
    case '?':
    default:
      usage();
    }
  argc -= optind;
  argv += optind;

  //If ip/port specified on command-line then connect
  //to it
  if(argc == 2) {
    ipaddr = *(argv++);
    port = atoi(*(argv++));

    //Create the socket we write debug to
    sd = socket(PF_INET, SOCK_STREAM, 0);
    if(sd == SOCKET_ERROR) {
      fprintf(stderr, "Failed to create socket");
      exit(1);
    }

    setsockopt(sd, SOL_SOCKET, SO_REUSEADDR, &dummy, sizeof(int));

    //Connect the socket to a listening server
    //using the ip/port specified on the cmd line
    bzero(&dest, sizeof(dest));
    dest.sin_family = AF_INET;
    dest.sin_addr.s_addr = inet_addr(ipaddr);
    dest.sin_port = htons(port);
    ret = connect(sd, (struct sockaddr*)&dest, sizeof(dest));
    if(ret == SOCKET_ERROR) {
      fprintf(stderr, "Failed to connect to socket %s:%d\n",
	      ipaddr, port);
      close(sd);
    }
  }
  else if(argc > 2)
    usage();

  //Open kernel memory and read namelist
  core = _PATH_KMEM;
  system = (char *)getbootfile();
  if (nlist(system, nl) < 0 || !nl[0].n_value)
    errx(1, "%s: no namelist", system);
  if ((memf = open(core, O_RDONLY)) < 0)
    err(2, "%s", core);

  //Read tcp_debug array and the pointer into it (tcp_debx)
  (void)klseek(memf, (off_t)nl[N_TCP_DEBX].n_value, L_SET);
  if (read(memf, (char *)&tcp_debx, sizeof(tcp_debx)) !=  sizeof(tcp_debx))
    err(3, "tcp_debx");
  (void)klseek(memf, (off_t)nl[N_TCP_DEBUG].n_value, L_SET);
  if (read(memf, (char *)tcp_debug, sizeof(tcp_debug)) !=  sizeof(tcp_debug))
    err(3, "tcp_debug");

  //Print our output header
  gethostname(hostname, 100);
  time(&currtime);
  timestr = ctime(&currtime);
  timestr[strlen(timestr)-1] = '\0';

  print("(* Netsem holtcpcb (trpt) tool -- Host: %s *)\n", hostname);
  print("(* Date: %s *)\n", timestr);
  print("(* NTP STATUS:\n");
  printNTPheader(sd);
  print(" *)\n");
  print("(* -------------------------------------------------------------------------- *)\n");
  print("(* BEGIN *)\n");

  //Go away and generate the trace
  dotrace();

  exit(0);
}

/* -------------------------------- */

//Monitor the tcp_debug ring buffer for new traces
//and output these if they are not excluded by the
//action mask (nmask).
void dotrace()
{
  register struct tcp_debug *td;

  int prev_debx;   //index of last trace record we've looked at
  register int i;

  //Read the current index into the tcp_debug buffer
  (void)klseek(memf, (off_t)nl[N_TCP_DEBX].n_value, L_SET);
  if (read(memf, (char *)&tcp_debx, sizeof(tcp_debx)) !=
      sizeof(tcp_debx))
    err(3, "tcp_debx");

  //To start up correctly we should say that
  //we have seen all of the traces in the buffer
  //so far
  prev_debx = tcp_debx;

  while(1) {
    //Check to see it there are any new trace records available
    //in the ring buffer. We do this by comparing the current
    //index into the ring buffer with the index of the previous
    //record we looked at
    do {
      nanosleep(&sleeptime, (struct timespec *)NULL);
      (void)klseek(memf, (off_t)nl[N_TCP_DEBX].n_value, L_SET);
      if (read(memf, (char *)&tcp_debx, sizeof(tcp_debx)) !=
	  sizeof(tcp_debx))
	err(3, "tcp_debx");
    } while (tcp_debx == prev_debx);

    //Read in the new ring buffer array (of pointers)
    (void)klseek(memf, (off_t)nl[N_TCP_DEBUG].n_value, L_SET);
    if (read(memf, (char *)tcp_debug, sizeof(tcp_debug)) !=
	sizeof(tcp_debug))
      err(3, "tcp_debug");

    //For each new message in the buffer
    for(i=prev_debx; i != tcp_debx; i = ++i % TCP_NDEBUG) {
      //Get the tcp_debug struct and its timestamp
      td = &tcp_debug[i];
      ntime = &(td->td_time);

      //If we are not interested in the type of message
      //then continue
      switch(td->td_act) {
	case TA_INPUT:
	  if(~nmask & 1)
	    continue;
	  break;
	case TA_OUTPUT:
	  if(~nmask & 2)
	    continue;
	  break;
	case TA_DROP:
	  if(~nmask & 4)
	    continue;
	  break;
	case TA_USER:
	  if(~nmask & 8)
	    continue;
	  break;
      }

      if(td->td_tcb == 0) {
	if(showzero) {  //if the control block pointer is 0 and we are showing zero entries
	  printtimestamp();
	  print("(* Got a debug message that did not have a control block *)\n");
	  print("\n");
	} else { /* Do nothing */ }
      }	else {
	//Print HOL style timestamp
	printtimestamp();
	//Print old trpt style output as a comment
	tcp_trace(td, &td->td_cb, (struct ip*)&td->td_ti.ti_i, &td->td_ti.ti_t, td->td_ostate);
	//Print HOL tcp_trace record
	tcp_hol_trace(&td->td_cb, (struct ip*)&td->td_ti.ti_i, &td->td_ti.ti_t, td->td_ostate, td->td_tcb, td->td_act);
	print("\n");
      }
    }

    //Update the previous record index we saw before looping
    prev_debx = i;
  } //while

}

/* -------------------------------- */

//Prints a HOL style timestamp
void printtimestamp()
{
  print("(** %lu.%6.6lu \"debug%lu\" **)\n", (unsigned long)ntime->tv_sec, (unsigned long)ntime->tv_usec,
	 printing_seqno++);
}


/* -------------------------------- */

//Print the old trpt style output as a comment line
void tcp_trace(struct tcp_debug *td,  struct tcpcb *tp, struct ip *ip4,
	       struct tcphdr *th, short ostate)
{
  tcp_seq seq, ack;
  short act = td->td_act;
  int flags, len, win, timer, req;

  //Print current state and action
  print("(* %s:%s ", tcpstates[ostate], tanames[act]);

  switch(act) {
    case TA_INPUT:
    case TA_OUTPUT:
    case TA_DROP:
      //Copy values to local variables
      seq = th->th_seq;
      ack = th->th_ack;
      len = ip4->ip_len;
      win = th->th_win;
      if (act == TA_OUTPUT) {
	seq = ntohl(seq);
	ack = ntohl(ack);
	len = ntohs(len);
	win = ntohs(win);
	len -= sizeof(struct tcphdr);
      }

      if (len) //if data in tcp_segment output its seq num range
	print("[%lx..%lx)", seq, seq + len);
      else     //else output just its seq num
	print("%lx", seq);
      //Output the current ack num
      print("@%lx", ack);

      //Output the window size if non-zero
      if (win)
	print("(win=%x)", win);

      //Ouput any flags that are set in the tcp header
      flags = th->th_flags;
      if (flags) {
	register char *cp = "<";
#define	pf(flag, string) { \
	if (th->th_flags&flag) { \
		(void)print("%s%s", cp, string); \
		cp = ","; \
	} \
}
	pf(TH_SYN, "SYN");
	pf(TH_ACK, "ACK");
	pf(TH_FIN, "FIN");
	pf(TH_RST, "RST");
	pf(TH_PUSH, "PUSH");
	pf(TH_URG, "URG");
	print(">");
      }
      break;
    case TA_USER:
      //If the user mode event was a timer
      //then print the timer name
      req = td->td_req;
      timer = req >> 8;
      req &= 0xff;
      print("%s", prurequests[req]);
      if (req == PRU_SLOWTIMO || req == PRU_FASTTIMO)
	print("<%s>", tcptimers[timer]);
      break;
  }

  //Print the state that the tcpcb is left in after the action
  print(" -> %s *)\n", tcpstates[tp->t_state]);

}

/* -------------------------------- */

//Print a hol tcp style trace of the
//TCP protocol control block
void tcp_hol_trace(struct tcpcb *tp, struct ip *ip4,
		   struct tcphdr *th, short ostate,
		   struct tcpcb *realtp,
		   short action)
{
  char tmp[255], is1[30], is2[30], ps1[30], ps2[30], tmp2[50];
  char tcpcb_ptr[255], flavour[30];
  int i;
  char all_zero = 1;

  sprintf(tcpcb_ptr, "SID %u", (unsigned int)realtp);

  //Construct the src ip/port and dst ip/port pairs
  if((ip4 == 0) && (th == 0))
    all_zero = 1;
  else {
    if(ip4->ip_src.s_addr == 0)
      sprintf(is1, "NONE");
    else {
      sprintf(is1, "SOME(IP %s)", inet_ntoa(ip4->ip_src));
      all_zero = 0;
    }

    for(i=0; i<strlen(is1); i++)
      if(is1[i] == '.')
	is1[i] = ' ';

    if(ip4->ip_dst.s_addr == 0)
      sprintf(is2, "NONE");
    else {
      sprintf(is2, "SOME(IP %s)", inet_ntoa(ip4->ip_dst));
      all_zero = 0;
    }

    for(i=0; i<strlen(is2); i++)
      if(is2[i] == '.')
	is2[i] = ' ';

    if(th == 0) {
      sprintf(ps1, "NONE");
      sprintf(ps2, "NONE");
    } else {
      if(th->th_sport == 0)
	sprintf(ps1, "NONE");
      else {
	sprintf(ps1, "SOME(Port %d)", ntohs(th->th_sport));
	all_zero = 0;
      }

      if(th->th_dport == 0)
	sprintf(ps2, "NONE");
      else {
	sprintf(ps2, "SOME(Port %d)", ntohs(th->th_dport));
	all_zero = 0;
      }
    }
  }

  if(all_zero)
    sprintf(tmp, "NONE");
  else {
    switch(action) {
      case(TA_INPUT):
      case(TA_DROP):
	// Switch the quad over if the action was an input rule
	sprintf(tmp, "SOME(%s, %s, %s, %s)", is2, ps2, is1, ps1);
        break;
      case(TA_OUTPUT):
      case(TA_USER):
      case(TA_RESPOND):
      default:
	// otherwise don't
	sprintf(tmp, "SOME(%s, %s, %s, %s)", is1, ps1, is2, ps2);
        break;
    }
  }

  //Construct the state
  switch(tp->t_state) {
    case TCPS_CLOSED:
      sprintf(tmp2, "CLOSED");
      break;
    case TCPS_LISTEN:
      sprintf(tmp2, "LISTEN");
      break;
    case TCPS_SYN_SENT:
      sprintf(tmp2, "SYN_SENT");
      break;
    case TCPS_SYN_RECEIVED:
      sprintf(tmp2, "SYN_RECEIVED");
      break;
    case TCPS_ESTABLISHED:
      sprintf(tmp2, "ESTABLISHED");
      break;
    case TCPS_CLOSE_WAIT:
      sprintf(tmp2, "CLOSE_WAIT");
      break;
    case TCPS_FIN_WAIT_1:
      sprintf(tmp2, "FIN_WAIT_1");
      break;
    case TCPS_CLOSING:
      sprintf(tmp2, "CLOSING");
      break;
    case TCPS_LAST_ACK:
      sprintf(tmp2, "LAST_ACK");
      break;
    case TCPS_FIN_WAIT_2:
      sprintf(tmp2, "FIN_WAIT_2");
      break;
    case TCPS_TIME_WAIT:
      sprintf(tmp2, "TIME_WAIT");
      break;
    default:
      sprintf(tmp2, "UNKNOWN_STATE");
      break;
  }

  switch(action) {
    case(TA_INPUT):
      sprintf(flavour, "TA_INPUT");
      break;
    case(TA_OUTPUT):
      sprintf(flavour, "TA_OUTPUT");
      break;
    case(TA_USER):
      sprintf(flavour, "TA_USER");
      break;
    case(TA_RESPOND):
      sprintf(flavour, "TA_RESPOND");
      break;
    case(TA_DROP):
      sprintf(flavour, "TA_DROP");
      break;
    default:
      sprintf(flavour, "(*** UNKNOWN flavour: ERROR ***)");
      break;
  }

  //Print the Lh_trace record
  print("Lh_trace(\n %s, %s, %s,\n %s,\n", flavour, tcpcb_ptr, tmp, tmp2);

  print(" <|\n");
  print("   snd_una := tcp_seq_local(n2w %u);\n", tp->snd_una);
  print("   snd_max := tcp_seq_local(n2w %u);\n", tp->snd_max);
  print("   snd_nxt := tcp_seq_local(n2w %u);\n", tp->snd_nxt);
  print("   snd_wl1 := tcp_seq_foreign(n2w %u);\n", tp->snd_wl1);
  print("   snd_wl2 := tcp_seq_local(n2w %u);\n", tp->snd_wl2);
  print("   iss := tcp_seq_local(n2w %u);\n", tp->iss);
  print("   snd_wnd := %lu;\n", tp->snd_wnd);
  print("   snd_cwnd := %lu;\n", tp->snd_cwnd);
  print("   snd_ssthresh := %lu;\n", tp->snd_ssthresh);
  print("   rcv_wnd := %lu;\n", tp->rcv_wnd);
  print("   rcv_nxt := tcp_seq_foreign(n2w %u);\n", tp->rcv_nxt);
  print("   rcv_up := tcp_seq_foreign(n2w %u);\n", tp->rcv_up);
  print("   irs := tcp_seq_foreign(n2w %u);\n", tp->irs);
  print("   rcv_adv := tcp_seq_foreign(n2w %u);\n", tp->rcv_adv);
  print("   snd_recover := tcp_seq_local(n2w %u);\n", tp->snd_recover);
  print("   t_maxseg := %u;\n", tp->t_maxseg);
  print("   t_dupacks := %u;\n", tp->t_dupacks);
  sprintf(tmp,"SOME(ts_seq(n2w %lu),tcp_seq_local(n2w %u))", tp->t_rtttime, tp->t_rtseq);
  print("   t_rttseg := %s;\n", tp->t_rtttime ? tmp : "NONE");
  print("   snd_scale := %u;\n", tp->snd_scale);
  print("   rcv_scale := %u;\n", tp->rcv_scale);
  sprintf(tmp,"TimeWindow(ts_seq(n2w %lu), never_timer)", tp->ts_recent);
  print("   ts_recent := %s;\n", tp->ts_recent ? tmp : "TimeWindowClosed");
  print("   last_ack_sent := tcp_seq_foreign(n2w %u)\n", tp->last_ack_sent);
  print(" |> );\n");

}
/* -------------------------------- */

//Print string to the connected socket (sd)
//Supports printf style arguments
//Tries to ensure the whole string is sent
void print(char *str, ...)
{
  va_list args;
  int i, res;
  size_t len;
  char message[16000], *string;

  va_start(args, str);
  vsprintf(message, str, args);

  len = strlen(message);
  string = message;

  va_end(args);

  //Write the string to the socket, trying
  //NUMSENDRETRIES times.
  for(i=0; i<NUMSENDRETRIES; i++) {
    res = write(sd, string, (int)len);
    fflush(stdout);
    if(res != SOCKET_ERROR) {
      if(len != res) { //whole string not sent
	string += res; //so send the remainder
	len = strlen(string);
	i=0;           //reset number of retries
	continue;	   //and try again
      } else {         //else all is written
	return;		   //so return
      }
    } else {				//an error occured so retry send
      if(ERRNO == EAGAIN)   //if error is EAGAIN then reset
	i=0;				//the number of retries counter
        continue;
    }
  }

  //Couldn't write all the data to the socket
  fprintf(stderr, "Failed to write to connected socket\n");
  exit(1);
}

/* -------------------------------- */

/* Print usage information */
static void usage()
{
  fprintf(stderr, "Usage: holtcpcb-v8 [-n actmask] [-z] {ipaddress port}\n");
  fprintf(stderr, "       actmask: 0x01(input) 0x02(output) 0x04(drop) 0x08(user)\n");
  fprintf(stderr, "       -z: hide zero tcpcb messages\n");
  exit(1);
}

/* -------------------------------- */

//Seek to corrrect location in kernel memory
void klseek(int fd, off_t base, int off)
{
  (void)lseek(fd, base, off);
}

