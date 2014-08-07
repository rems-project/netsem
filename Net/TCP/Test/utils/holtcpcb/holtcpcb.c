
/*
****************************
* THIS TOOL IS DEPRECATED  *
* USED holtcpcb-v8 instead *
****************************
*/


/* Modified version by Steve Bishop, University of Cambridge Computer Laboratory
 * $Id: holtcpcb.c,v 1.12 2003/01/28 16:52:31 smb50 Exp $
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
#include <sys/socket.h>
#include <sys/socketvar.h>
#define PRUREQUESTS
#include <sys/protosw.h>
#include <sys/file.h>
#include <sys/time.h>

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

//Array of pointers to tcp_pcbs
static caddr_t tcp_pcbs[TCP_NDEBUG];

//Time variable (milliseconds since midnight)
static n_time ntime;

//Cmd-line option flags
static int aflag, kflag, nflag, nfollow, memf, follow, sflag, tflag, nmask;
unsigned long printing_seqno = 0;

/* Function definitions for functions implemented
 * later in this file
 */
void dotrace __P((caddr_t));
void klseek __P((int, off_t, int));
int numeric __P((caddr_t *, caddr_t *));
void tcp_trace __P((short, short, struct tcpcb *, struct tcpcb *,
			int, void *, struct tcphdr *, int));
static void usage __P((void));
void tcp_hol_trace(struct tcpcb *tp, struct ip *ip4,
		   struct tcphdr *th, short ostate);

/* -------------------------------- */

/* Program entry point
 * See usage() for cmd-line arguments
 */
int main(int argc, char **argv)
{
  int ch, i, jflag, npcbs;
  char *system, *core;
  char *timestr, hostname[100];
  time_t currtime;

  jflag = npcbs = nflag = nfollow = 0;
  while ((ch = getopt(argc, argv, "afjn:p:stF")) != -1)
    switch (ch) {
    case 'a':
      ++aflag;
      break;
    case 'F':
      ++nfollow;
      setlinebuf(stdout);
      break;
    case 'f':
      ++follow;
      setlinebuf(stdout);
      break;
    case 'j':
      ++jflag;
      break;
    case 'n':
      ++nflag;
      (void)sscanf(optarg, "%d", (int *)&nmask);
      break;
    case 'p':
      if (npcbs >= TCP_NDEBUG)
	errx(1, "too many pcb's specified");
      (void)sscanf(optarg, "%x", (int *)&tcp_pcbs[npcbs++]);
      break;
    case 's':
      ++sflag;
      break;
    case 't':
      ++tflag;
      break;
    case '?':
    default:
      usage();
    }
  argc -= optind;
  argv += optind;

  core = _PATH_KMEM;
  if (argc > 0) {
    system = *argv;
    argc--, argv++;
    if (argc > 0) {
      core = *argv;
      argc--, argv++;
      ++kflag;
    }
    /*
     * Discard setgid privileges if not the running kernel so that
     * bad guys can't print interesting stuff from kernel memory.
     */
    setgid(getgid());
  }
  else
    system = (char *)getbootfile();

  if (nlist(system, nl) < 0 || !nl[0].n_value)
    errx(1, "%s: no namelist", system);
  if ((memf = open(core, O_RDONLY)) < 0)
    err(2, "%s", core);
  if (kflag)
    errx(1, "can't do core files yet");

  (void)klseek(memf, (off_t)nl[N_TCP_DEBX].n_value, L_SET);
  if (read(memf, (char *)&tcp_debx, sizeof(tcp_debx)) !=
      sizeof(tcp_debx))
    err(3, "tcp_debx");
  (void)klseek(memf, (off_t)nl[N_TCP_DEBUG].n_value, L_SET);
  if (read(memf, (char *)tcp_debug, sizeof(tcp_debug)) !=
      sizeof(tcp_debug))
    err(3, "tcp_debug");

  /*
   * If no control blocks have been specified, figure
   * out how many distinct ones we have and summarize
   * them in tcp_pcbs for sorting the trace records
   * below.
   */
  if (!npcbs && !nfollow) {
    for (i = 0; i < TCP_NDEBUG; i++) {
      register struct tcp_debug *td = &tcp_debug[i];
      register int j;

      if (td->td_tcb == 0)
	continue;
      for (j = 0; j < npcbs; j++)
	if (tcp_pcbs[j] == td->td_tcb)
	  break;
      if (j >= npcbs)
	tcp_pcbs[npcbs++] = td->td_tcb;
    }
    if (!npcbs)
      exit(0);
  }


  //Sort the trace records
  qsort(tcp_pcbs, npcbs, sizeof(caddr_t), numeric);

  if(nflag || nfollow) {
    gethostname(hostname, 100);
    time(&currtime);
    timestr = ctime(&currtime);
    timestr[strlen(timestr)-1] = '\0';
    printf("(* Netsem holtcpcb (trpt) tool -- Host: %s *)\n", hostname);
    printf("(* Date: %s *)\n", timestr);
    printf("(* --- NTP status ---\n");
    fflush(stdout);
    printNTPheader(1);  (* fd 1 == stdout *)
    printf("   ------------------ *)\n");
    printf("(* BEGIN *)\n");
  }

  //if '-j' specified, just print the number of distinct
  //control blocks in the ring buffer
  if (jflag) {
    for (i = 0;;) {
      printf("%x", (int)tcp_pcbs[i]);
      if (++i == npcbs)
	break;
      fputs(", ", stdout);
    }
    putchar('\n');
  }
  else if(nfollow) {
    npcbs = 1;
    tcp_pcbs[0] = 0;
    dotrace(tcp_pcbs[0]);
  }
  //otherwise, print the traces for each record
  else for (i = 0; i < npcbs; i++) {
    printf("\n%x:\n", (int)tcp_pcbs[i]);
    dotrace(tcp_pcbs[i]);
  }
  exit(0);
}

/* -------------------------------- */


/* Print usage information */
static void usage()
{
  fprintf(stderr, "Usage: holtcpcb [-afjstF] [-n actmask] [-p hex-address] [system [core]]\n");
  fprintf(stderr, "       actmask: 0x01(input) 0x02(output) 0x04(drop) 0x08(user)\n");
  exit(1);
}

/* -------------------------------- */


/* Prints the debug trace for a given tcpcb
 * by chaining through the ring buffer
 */
void dotrace(register caddr_t tcpcb)
{
  register struct tcp_debug *td;
  register int i;
  int prev_debx = tcp_debx, family;


  if(nfollow) {
    if (--tcp_debx < 0)
      tcp_debx = TCP_NDEBUG - 1;
    goto done;
  }

 again:
  if (--tcp_debx < 0)
   tcp_debx = TCP_NDEBUG - 1;
  for (i = prev_debx % TCP_NDEBUG; i < TCP_NDEBUG; i++) {
   td = &tcp_debug[i];
   if (tcpcb && td->td_tcb != tcpcb) {
     if(nfollow && (i == tcp_debx))
       goto done;
     else
       continue;
    }

    ntime = ntohl(td->td_time);

#ifdef INET6
    family = td->td_family;
#else
    family = AF_INET;
#endif
    switch(family) {
    case AF_INET:
      tcp_trace(td->td_act, td->td_ostate,
		(struct tcpcb *)td->td_tcb,
		&td->td_cb, td->td_family, &td->td_ti.ti_i,
		&td->td_ti.ti_t, td->td_req);
      break;
#ifdef INET6
    case AF_INET6:
      tcp_trace(td->td_act, td->td_ostate,
		(struct tcpcb *)td->td_tcb,
		&td->td_cb, td->td_family, &td->td_ti6.ip6,
		&td->td_ti6.th, td->td_req);
      break;
#endif
    }
    if (i == tcp_debx)
      goto done;
  }


  //...and the same code again, just in case we
  //didn't make it all the way around the ring
  //buffer the first time -- SMB ;-)
  for (i = 0; i <= tcp_debx % TCP_NDEBUG; i++) {
   td = &tcp_debug[i];
    if (tcpcb && td->td_tcb != tcpcb)
      continue;
    ntime = ntohl(td->td_time);

#ifdef INET6
    family = td->td_family;
#else
    family = AF_INET;
#endif
    switch(family) {
    case AF_INET:
      tcp_trace(td->td_act, td->td_ostate,
		(struct tcpcb *)td->td_tcb,
		&td->td_cb, td->td_family, &td->td_ti.ti_i,
		&td->td_ti.ti_t, td->td_req);
      break;
#ifdef INET6
    case AF_INET6:
      tcp_trace(td->td_act, td->td_ostate,
		(struct tcpcb *)td->td_tcb,
		&td->td_cb, td->td_family, &td->td_ti6.ip6,
		&td->td_ti6.th, td->td_req);
      break;
#endif
    }
  }

  //are we done yet?
done:
  if (follow || nfollow) {
   prev_debx = tcp_debx + 1;
   if (prev_debx >= TCP_NDEBUG)
     prev_debx = 0;

   do {
     sleep(1);
     (void)klseek(memf, (off_t)nl[N_TCP_DEBX].n_value, L_SET);
     if (read(memf, (char *)&tcp_debx, sizeof(tcp_debx)) !=
	 sizeof(tcp_debx))
       err(3, "tcp_debx");
   } while (tcp_debx == prev_debx);

   (void)klseek(memf, (off_t)nl[N_TCP_DEBUG].n_value, L_SET);
   if (read(memf, (char *)tcp_debug, sizeof(tcp_debug)) !=
       sizeof(tcp_debug))
     err(3, "tcp_debug");
   if(nfollow && (tcpcb == 0))
     tcpcb = (&tcp_debug[tcp_debx!=0 ? (tcp_debx-1) : (TCP_NDEBUG-1)])->td_tcb;
   goto again;
 }
}


/* -------------------------------- */


/*
 * Prints the tcp trace (trpt style)
 */
void tcp_trace(short act, short ostate, struct tcpcb *atp,
	       struct tcpcb *tp, int family, void *ip,
	       struct tcphdr *th, int req)
{
  tcp_seq seq, ack;
  int flags, len, win, timer;
  struct ip *ip4;
  time_t t, timen;
  struct tm *times;

#ifdef INET6
  int isipv6, nopkt = 1;
  struct ip6_hdr *ip6;
  char ntop_buf[INET6_ADDRSTRLEN];
#endif

  if(nflag) {
    switch(act) {
      case TA_INPUT:
	if(~nmask & 0x1)
	  return;
	break;
      case TA_OUTPUT:
	if(~nmask & 0x2)
	  return;
	break;
      case TA_DROP:
	if(~nmask & 0x4)
	  return;
	break;
      case TA_USER:
	if(~nmask & 0x8)
	  return;
	break;
      default:
	return;
	break;
    }

    //Get the number of seconds since the epoch
    if((t = time(NULL)) == (time_t)-1)
      t = (time_t)0;

    //Convert this to a time struct and zero todays time
    times = gmtime(&t);
    times->tm_sec = 0;
    times->tm_min = 0;
    times->tm_hour = 0;

    //Convert time struct back to time_t
    timen = mktime(times);
    t = timen + ntime/1000;
    printf("(** %lu.%6.6lu \"debug%lu\" **)\n", (long int)t, (ntime%1000)*1000,
	   printing_seqno++);

    printf("(* ");
  }

#ifdef INET6
  switch (family) {
  case AF_INET:
    nopkt = 0;
    isipv6 = 0;
    ip4 = (struct ip *)ip;
    break;
  case AF_INET6:
    nopkt = 0;
    isipv6 = 1;
    ip6 = (struct ip6_hdr *)ip;
  case 0:
  default:
    break;
  }
#else
  ip4 = (struct ip *)ip;
#endif
  printf("%03ld %s:%s ",(ntime/10) % 1000, tcpstates[ostate],
	 tanames[act]);
  switch (act) {
  case TA_INPUT:
  case TA_OUTPUT:
  case TA_DROP:
#ifdef INET6
    if (nopkt != 0)
      break;
#endif
    if (aflag) {
      printf("(src=%s,%u, ",

#ifdef INET6
	     isipv6
	     ? inet_ntop(AF_INET6, &ip6->ip6_src, ntop_buf,
			 sizeof(ntop_buf)) :
#endif
	     inet_ntoa(ip4->ip_src),
	     ntohs(th->th_sport));
      printf("dst=%s,%u)",
#ifdef INET6
	     isipv6
	     ? inet_ntop(AF_INET6, &ip6->ip6_dst, ntop_buf,
			 sizeof(ntop_buf)) :
#endif
	     inet_ntoa(ip4->ip_dst),
	     ntohs(th->th_dport));
    }
    seq = th->th_seq;
    ack = th->th_ack;

    len =
#ifdef INET6
      isipv6 ? ip6->ip6_plen :
#endif
      ip4->ip_len;
    win = th->th_win;
    if (act == TA_OUTPUT) {
      seq = ntohl(seq);
      ack = ntohl(ack);
      len = ntohs(len);
      win = ntohs(win);
    }
    if (act == TA_OUTPUT)
      len -= sizeof(struct tcphdr);
    if (len)
      printf("[%lx..%lx)", seq, seq + len);
    else
      printf("%lx", seq);
    printf("@%lx", ack);
    if (win)
      printf("(win=%x)", win);
    flags = th->th_flags;
    if (flags) {
      register char *cp = "<";
#define	pf(flag, string) { \
	if (th->th_flags&flag) { \
		(void)printf("%s%s", cp, string); \
		cp = ","; \
	} \
}
      pf(TH_SYN, "SYN");
      pf(TH_ACK, "ACK");
      pf(TH_FIN, "FIN");
      pf(TH_RST, "RST");
      pf(TH_PUSH, "PUSH");
      pf(TH_URG, "URG");
      printf(">");
    }
    break;
  case TA_USER:
    timer = req >> 8;
    req &= 0xff;
    printf("%s", prurequests[req]);
    if (req == PRU_SLOWTIMO || req == PRU_FASTTIMO)
      printf("<%s>", tcptimers[timer]);
    break;
  }
  printf(" -> %s", tcpstates[tp->t_state]);
  /* print out internal state of tp !?! */
  printf("%s\n", (nflag && !sflag) ? " *)" : "");
  if (sflag) {
    printf("\trcv_nxt %lx rcv_wnd %x snd_una %lx snd_nxt %lx snd_max %lx\n",
	   tp->rcv_nxt, tp->rcv_wnd, tp->snd_una, tp->snd_nxt,
	   tp->snd_max);
    printf("\tsnd_wl1 %lx snd_wl2 %lx snd_wnd %x%s\n", tp->snd_wl1,
	   tp->snd_wl2, tp->snd_wnd, nflag ? " *)" : "");
  }

  /* print out timers? */
#if 0
  /*
   * XXX
   * kernel now uses callouts, not integer time values.
   */
  if (tflag) {
    register char *cp = "\t";
    register int i;

    for (i = 0; i < TCPT_NTIMERS; i++) {
      if (tp->t_timer[i] == 0)
	continue;
      printf("%s%s=%d", cp, tcptimers[i], tp->t_timer[i]);
      if (i == TCPT_REXMT)
	printf(" (t_rxtshft=%d)", tp->t_rxtshift);
      cp = ", ";
    }
    if (*cp != '\t')
      putchar('\n');
  }
#endif

#ifndef INET6
  if(nflag)
    tcp_hol_trace(tp, ip4, th, ostate);
#endif

}

/* -------------------------------- */

/* Print a hol tcp style trace of the
 * TCP protocol control block
 */
void tcp_hol_trace(struct tcpcb *tp, struct ip *ip4,
		   struct tcphdr *th, short ostate)
{
  char tmp[255], is1[30], is2[30], ps1[30], ps2[30], tmp2[50];
  int i;

  if((ip4 == 0) || (th == 0))
    sprintf(tmp, "NONE");
  else {
    if(ip4->ip_src.s_addr == 0)
      sprintf(is1, "NONE");
    else
      sprintf(is1, "SOME(IP %s)", inet_ntoa(ip4->ip_src));

    for(i=0; i<strlen(is1); i++)
      if(is1[i] == '.')
	is1[i] = ' ';

    if(ip4->ip_dst.s_addr == 0)
      sprintf(is2, "NONE");
    else
      sprintf(is2, "SOME(IP %s)", inet_ntoa(ip4->ip_dst));

    for(i=0; i<strlen(is2); i++)
      if(is2[i] == '.')
	is2[i] = ' ';

    if(th->th_sport == 0)
      sprintf(ps1, "NONE");
    else
      sprintf(ps1, "SOME(Port %d)", ntohs(th->th_sport));

   if(th->th_dport == 0)
      sprintf(ps2, "NONE");
    else
      sprintf(ps2, "SOME(Port %d)", ntohs(th->th_dport));

    sprintf(tmp, "SOME(%s, %s, %s, %s)",
    is1, ps1, is2, ps2);
  }

  switch(ostate) {
    case TCPS_CLOSED:
      sprintf(tmp2, "CLOSED");
      break;
    case TCPS_LISTEN:
      sprintf(tmp2, "LISTEN");
      break;
    case TCPS_SYN_SENT:
      sprintf(tmp2, "SYN_SENT");
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

  printf("Lh_trace(\n %s,\n %s,\n", tmp, tmp2);

  printf(" <|\n");
  printf("   snd_una := tcp_seq_local(n2w %u);\n", tp->snd_una);
  printf("   snd_max := tcp_seq_local(n2w %u);\n", tp->snd_max);
  printf("   snd_nxt := tcp_seq_local(n2w %u);\n", tp->snd_nxt);
  printf("   snd_up := tcp_seq_local(n2w %u);\n", tp->snd_up);
  printf("   snd_wl1 := tcp_seq_foreign(n2w %u);\n", tp->snd_wl1);
  printf("   snd_wl2 := tcp_seq_local(n2w %u);\n", tp->snd_wl2);
  printf("   iss := tcp_seq_local(n2w %u);\n", tp->iss);
  printf("   snd_wnd := %u;\n", tp->snd_wnd);
  printf("   snd_cwnd := %u;\n", tp->snd_cwnd);
  printf("   snd_ssthresh := %u;\n", tp->snd_ssthresh);
  printf("   rcv_wnd := %u;\n", tp->rcv_wnd);
  printf("   rcv_nxt := tcp_seq_foreign(n2w %u);\n", tp->rcv_nxt);
  printf("   rcv_up := tcp_seq_foreign(n2w %u);\n", tp->rcv_up);
  printf("   irs := tcp_seq_foreign(n2w %u);\n", tp->irs);
  printf("   rcv_adv := tcp_seq_foreign(n2w %u);\n", tp->rcv_adv);
  printf("   snd_recover := tcp_seq_local(n2w %u);\n", tp->snd_recover);
  printf("   t_maxseg := %u;\n", tp->t_maxseg);
  printf("   t_dupacks := %u;\n", tp->t_dupacks);
  printf("   t_rtseq  := tcp_seq_local(n2w %u);\n", tp->t_rtseq);
  printf("   snd_scale := %u;\n", tp->snd_scale);
  printf("   rcv_scale := %u;\n", tp->rcv_scale);
  sprintf(tmp, "SOME(Timed(ts_seq(n2w %u), time_zero))", tp->ts_recent);
  printf("   ts_recent := %s;\n", (tp->ts_recent == 0) ? "NONE" : tmp);
  printf("   last_ack_sent := tcp_seq_foreign(n2w %u)\n", tp->last_ack_sent);
  printf(" |> );\n");

}
/* -------------------------------- */

int numeric(caddr_t *c1, caddr_t *c2)
{
  return(*c1 - *c2);
}

/* -------------------------------- */

void klseek(int fd, off_t base, int off)
{
  (void)lseek(fd, base, off);
}
