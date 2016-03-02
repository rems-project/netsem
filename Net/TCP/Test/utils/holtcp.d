#!/usr/sbin/dtrace -Cs
/*
 * Copyright (c) 2015 George V. Neville-Neil
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * $FreeBSD$
 *
 * The tcpdebug D script uses the tcp:kernel::debug tracepoints
 * to replicate the action of turning on TCPDEBUG in a kernel configuration.
 *
 * A TCP debug statement shows a connection's
 *
 * direction:	input, output, user, drop
 * state:	CLOSED,	LISTEN,	SYN_SENT, SYN_RCVD, ESTABLISHED,
 *              CLOSE_WAIT, FIN_WAIT_1, CLOSING, LAST_ACK, FIN_WAIT_2,TIME_WAIT
 * sequence:	sequence space
 *
 * congestion:	rcv_nxt, rcv_wnd, rcv_up, snd_una, snd_nxt, snx_max,
 *		snd_wl1, snd_wl2, snd_wnd
 *
 * NOTE: Only sockets with SO_DEBUG set will be shown.
 *
 * Usage: tcpdebug
 */

inline string tcp_state_str[int32_t state] =
	state == TCPS_CLOSED ?		"CLOSED" :
	state == TCPS_LISTEN ?		"LISTEN" :
	state == TCPS_SYN_SENT ?	"SYN_SENT" :
	state == TCPS_SYN_RECEIVED ?	"SYN_RCVD" :
	state == TCPS_ESTABLISHED ?	"ESTABLISHED" :
	state == TCPS_CLOSE_WAIT ?	"CLOSE_WAIT" :
	state == TCPS_FIN_WAIT_1 ?	"FIN_WAIT_1" :
	state == TCPS_CLOSING ?		"CLOSING" :
	state == TCPS_LAST_ACK ?	"LAST_ACK" :
	state == TCPS_FIN_WAIT_2 ?	"FIN_WAIT_2" :
	state == TCPS_TIME_WAIT ?	"TIME_WAIT" :
	"<unknown>";

//XXX: IP used to be in 192 168 0 1, now 192.168.0.1
#define print_ips(ipinfo) printf("%s -> %s\n", ipinfo->ip_saddr, ipinfo->ip_daddr)

//XXX: `t_rttseg` used to be NONE if rtttime = 0
//XXX: `ts_recent` used to be TimeWindowClosed if ts_recent is 0
#define print_tcb(tcb) \
 printf(" %s,\n", tcp_state_str[tcb->tcps_state]);                          \
 printf(" <|\n");                                                           \
 printf("   snd_una := tcp_seq_local(n2w %u);\n", tcb->tcps_suna);          \
 printf("   snd_max := tcp_seq_local(n2w %u);\n", tcb->tcps_smax);          \
 printf("   snd_nxt := tcp_seq_local(n2w %u);\n", tcb->tcps_snxt);          \
 printf("   snd_wl1 := tcp_seq_foreign(n2w %u);\n", tcb->tcps_swl1);        \
 printf("   snd_wl2 := tcp_seq_local(n2w %u);\n", tcb->tcps_swl2);          \
 printf("   iss := tcp_seq_local(n2w %u);\n", tcb->tcps_iss);               \
 printf("   snd_wnd := %u;\n", tcb->tcps_swnd);                             \
 printf("   snd_cwnd := %u;\n", tcb->tcps_cwnd);                            \
 printf("   snd_ssthresh := %u;\n", tcb->tcps_cwnd_ssthresh);               \
 printf("   rcv_wnd := %u;\n", tcb->tcps_rwnd);                             \
 printf("   rcv_nxt := tcp_seq_foreign(n2w %u);\n", tcb->tcps_rnxt);        \
 printf("   rcv_up := tcp_seq_foreign(n2w %u);\n", tcb->tcps_rup);          \
 printf("   irs := tcp_seq_foreign(n2w %u);\n", tcb->tcps_irs);             \
 printf("   rcv_adv := tcp_seq_foreign(n2w %u);\n", tcb->tcps_radv);        \
 printf("   snd_recover := tcp_seq_local(n2w %u);\n", tcb->tcps_srecover);  \
 printf("   t_maxseg := %u;\n", tcb->tcps_mss);                             \
 printf("   t_dupacks := %u;\n", tcb->tcps_dupacks);                        \
 printf("   t_rttseg := SOME(ts_seq(n2w %u), tcp_seq_local(n2w %u));\n",    \
        tcb->tcps_rtttime, tcb->tcps_rtseq);                                \
 printf("   snd_scale := %u;\n", tcb->tcps_snd_ws);                         \
 printf("   rcv_scale := %u;\n", tcb->tcps_rcv_ws);                         \
 printf("   ts_recent := TimeWindow(ts_seq(n2w %u), never_timer);\n",       \
        tcb->tcps_ts_recent);                                               \
 printf("   last_ack_send := tcp_seq_foreign(n2w %u)\n", tcb->tcps_rack);   \
 printf(" |>);\n");

#pragma D option quiet
tcp:kernel::debug-input
/args[0]->tcps_debug/
{
  printf("Lh_trace(\n TA_INPUT,\n SID %u,\n", arg0);
  printf(" SOME(SOME(IP %s), SOME(Port %d), SOME(IP %s), SOME(Port %d)), \n",
         args[2]->ip_daddr, args[1]->tcp_dport, args[2]->ip_saddr, args[1]->tcp_sport);
  print_tcb(args[0])
}

tcp:kernel::debug-output
/args[0]->tcps_debug/
{
  printf("Lh_trace(\n TA_OUTPUT,\n SID %u,\n", arg0);
  printf(" SOME(SOME(IP %s), SOME(Port %d), SOME(IP %s), SOME(Port %d)), \n",
         args[2]->ip_saddr, args[1]->tcp_sport, args[2]->ip_daddr, args[1]->tcp_dport);
  print_tcb(args[0])
}

tcp:kernel::debug-drop
/args[0]->tcps_debug/
{
  printf("Lh_trace(\n TA_DROP,\n SID %u,\n", arg0);
  printf(" SOME(SOME(IP %s), SOME(Port %d), SOME(IP %s), SOME(Port %d)), \n",
         args[2]->ip_daddr, args[1]->tcp_dport, args[2]->ip_saddr, args[1]->tcp_sport);
  print_tcb(args[0])
}

tcp:kernel::debug-user
/args[0]->tcps_debug/
{
  //printf("TA_USER %s\n", prureq_string[args[1]]);
  printf("Lh_trace(\n TA_USER,\n SID %u,\n", arg0);
  printf(" NONE,\n");
  print_tcb(args[0]);
}

/*
tcp:kernel::state-change
/args[3]->tcps_debug/
{
        print_state(args[5]->tcps_state);
        printf("%p state change: %s -> %s\n", arg3,
               tcp_state_str[args[5]->tcps_state],
               tcp_state_str[args[3]->tcps_state]);
}
*/