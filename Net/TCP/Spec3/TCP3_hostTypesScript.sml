(* A HOL98 specification of TCP *)

(* Type definitions of the host and its components: file, socket, TCPCB etc *)

(*[ RCSID "$Id: TCP3_hostTypesScript.sml,v 1.9 2009/02/20 10:35:33 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

local open (*TCP1_errorsTheory
           TCP1_baseTypesTheory
           TCP1_timersTheory
           TCP1_netTypesTheory
	   TCP1_paramsTheory
           TCP3_streamTypesTheory*)
	   TCP1_preHostTypesTheory
in end

local open arithmeticTheory stringTheory pred_setTheory integerTheory
           finite_mapTheory realTheory in end;

val _ = new_theory "TCP3_hostTypes";

val _ = Version.registerTheory "$RCSfile: TCP3_hostTypesScript.sml,v $" "$Revision: 1.9 $" "$Date: 2009/02/20 10:35:33 $";

(*: @chapter [[TCP3_hostTypes]] Host types

This file defines types for the internal state of the host and its components:
files, TCP control blocks, sockets, interfaces, routing table, thread
states, and so on, culminating in the definition of the [[host]] type.
%
It also defines TCP trace records, building on the definition of TCP control blocks.


Broadly following the implementations, each protocol endpoint has a
[[socket]] structure which has some common fields (e.g.~the associated
IP addresses and ports), and some protocol-specific information.

For TCP, which involves a great deal of local state, the
protocol-specific information (of type [[tcp_socket]]) consists of a
\emph{TCP state} ([[CLOSED]], [[LISTEN]], etc.), send and receive
queues, and a \emph{TCP control block}, of type [[tcpcb]], with many
window parameters, timers, etc.
%
Roughly, the [[socket]] structure and [[tcp_socket]] substructure contain all the information required by most sockets rules, whereas the [[tcpcb]] contains fields required only by the protocol information.



:*)


(* -------------------------------------------------- *)
(*                       TCP CONTROL BLOCK            *)
(* -------------------------------------------------- *)

(*: @section [[hostty_tcpcp]] TCP The TCP control block

TODO3
:*)


(* \textbf{OLDER INTERNAL STUFF}

\textbf{Level rationale:}

Level 3 is supposed to be a fully-detailed spec, st anything
conforming to it[*] would be a satisfactory implementation, doing
congestion control etc and with reasonable timeouts.

The yet-to-be-considered-much Level 4 will resolve enough
nondeterminism in Level 3 to make an algorithm, for the HOL-TCP
implementation.

The point of Level 2 is to be a stepping stone on the way to Level 3,
as the latter involves quite a lot of detail. It might end up being
transient (for our use only), or we might find it useful in testing
and exposition - don't know.

What should we aim for Level 2 to cover?  I guess it should guarantee
partial correctness of communication (so must deal correctly with
received window size bounds), but not communication efficiency (so
should be nondeterministic about advertised window sizes, abstracting
from flow control).

I'm inclined also to make it nondeterministic about the TCP timers and
retransmission (maybe that will make some forms of testing easier?).


[*] what does it mean for an impl to conform to a spec?  The simplest
answer to this (old) question is inclusion of infinite traces.  That
ignores many important liveness or responsiveness properties,
though, which we must consider in due course...

Some of the Level 3 data we might replace with a more explicit history
of segments received and transmitted.



\textbf{Level HOL coding:}

I think we want to have the level 2 and 3 code in the same source
files, somehow.  I don't know how... (HOL ifdefs?).  At present it's
unclear if the types will be different or just the behaviour.
If the latter then we can have a global logic switch.

We also want the different architectures in the same source file, but
this should certainly be controlled by logic and a host-arch-field.

For now, at least, I'm keeping snippets of the BSD sources in the HOL
as comments.



\textbf{States:}

Take states with spelling and sequence as in our BSD |tcp_fsm.h|.

We could treat CLOSED and LISTEN separately (and pull out of this
type), giving all the others a tcpcb.  That seems logically proper,
but (a) TCPv2 says that the tcpcb is created when the socket is, so I
guess it's possible that fields get filled in between then and when we
leave CLOSED/LISTEN; and (b) I guess it will be nice to do case
analysis across all states, eg when a segment is received. Therefore
putting the tcpcb at top level in the socket.  Not absolutely sure
about this, but...

Decision: a socket *always* has a tcpcb (which contains the tcpstate
probably).

Now need to revisit where the LISTEN queues are kept.

Could have a socket-level state of CLOSED | LISTEN of q*q0 | OTHER,
but that's mighty ugly.  Instead, just have a q*q0 option (which is
also ugly). (and an invariant).

\textbf{Socket versus CB:}
*)

val _ = Hol_datatype`(*: the TCP control block :*)
   tcpcb = <|

  (*: timers :*)
  tt_keep       : one timed option;         (*: keepalive timer :*)

  (*: other :*)
  t_softerror : error option      (*: current transient error; reported only if failure becomes permanent :*)
  (*: could cut this down to the actually-possible errors? :*)
  |>
`;

(* Differences between this control block and that in the BSD implemention:

- state t_state now stored in the socket not the cb.
- tt_keep in BSD overloaded with tt_conn_est as well; separated here
- tt_2msl in BSD overloaded with tt_fin_wait_2 as well; separated here
- snd_up - send urgent pointer is modelled at sockets layer by sndurp
- t_maxopd is calculable, so not stored
- char t_force - 1 if forcing out a byte - this is only ever set to 0
        or 1 in the BSD sources (KSW 2002-08-05); it should really be
        another TCP flag, in t_flags.  Weird BSD implementors!!.  In
        fact, we deal with this by parameter-passing, and don't need
        to store it in the CB.
- t_starttime - not needed (time connection was established)
- max_sndwnd (largest window peer has offered) not needed
- out-of-band data handled in socket
- requested_s_scale not needed
- cc_send, cc_recv (RFC1644) we don't implement connection-counting and TTCP

*)



(* POSIX errors now listed separately to save compile time! *)



(* -------------------------------------------------- *)
(*                       SOCKETS                      *)
(* -------------------------------------------------- *)

(*: @section [[hostty_sockets]] ALL Sockets
TODO3
:*)

(* X *)
val _ = Hol_datatype`(*: details of a TCP socket :*)
   tcp_socket
     = <| st   : tcpstate;  (*: here rather than in [[tcpcb]] for convenience as heavily used.  Called |t_state| in BSD :*)
          cb   : tcpcb;
          lis  : socket_listen option (*: invariant: [[NONE]] iff not [[LISTEN]] :*)
      |>
`;

val _ = Hol_datatype`(*: protocol-specific socket data :*)
   protocol_info = TCP_PROTO of tcp_socket
                 | UDP_PROTO of udp_socket
`;

val _ = Hol_datatype`(*: details of a socket :*)
   socket
     = <| fid  : fid option;    (*: associated open file description if any :*)
          sf   : sockflags;     (*: socket flags :*)
          is1  : ip option;     (*: local IP address if any :*)
          ps1  : port option;   (*: local port if any :*)
          is2  : ip option;     (*: remote IP address if any :*)
          ps2  : port option;   (*: remote port if any :*)
          es   : error option;  (*: pending error if any :*)
	  cantsndmore : bool;   (*: output stream ends at end of send queue :*)
	  cantrcvmore : bool;   (*: input stream ends at end of receive queue :*)
          pr   : protocol_info  (*: protocol-specific information :*)
       |>
`;

val TCP_Sock0_def = Phase.phase 1 Define`(*: helper constructor :*)
  TCP_Sock0(st, cb, lis)
    = <| st:=st; cb:=cb; lis:=lis |>
`(*:@mergewithnext:*);
val TCP_Sock_def = Phase.phase 1 Define`(*: helper constructor :*) TCP_Sock v = TCP_PROTO(TCP_Sock0 v)`(*:@mergewithnext:*);

val UDP_Sock0_def = Phase.phase 1 Define`(*: helper constructor :*)
  (UDP_Sock0:dgram list->udp_socket) rcvq = <| rcvq:=rcvq |>
`(*:@mergewithnext:*);
val UDP_Sock_def = Phase.phase 1 Define`(*: helper constructor :*) UDP_Sock v = UDP_PROTO(UDP_Sock0 v)`(*:@mergewithnext:*);

val Sock_def = xDefine "Sock" `(*: helper constructor :*)
  Sock(fid, sf, is1, ps1, is2, ps2, es, csm, crm, pr)
    = <| fid:=fid; sf:=sf; is1:=is1; ps1:=ps1; is2:=is2; ps2:=ps2;
         es:=es; cantsndmore := csm; cantrcvmore := crm; pr:=pr |>`(*:@mergewithnext:*);
(* added manually to phase 1 in testEval *)

val tcp_sock_of_def = Phase.phase 1 Define`(*: helper accessor (beware ARBitrary behaviour on non-TCP socket) :*)
  tcp_sock_of sock = case sock.pr of TCP_PROTO(tcp_sock) -> tcp_sock || _ -> ARB
`(*:@mergewithnext:*);
val udp_sock_of_def = Phase.phase 1 Define`(*: helper accessor (beware ARBitrary behaviour on non-UDP socket) :*)
  udp_sock_of sock = case sock.pr of UDP_PROTO(udp_sock) -> udp_sock || _ -> ARB
`(*:@mergewithnext:*);

val proto_of_def = Phase.phase 1 Define`(*: helper accessor :*)
  proto_of (TCP_PROTO(_1)) = PROTO_TCP /\
  proto_of (UDP_PROTO(_3)) = PROTO_UDP
`(*:@mergewithnext:*);

val proto_eq_def = Phase.phase 1 Define`(*: compare protocol of two protocol info structures :*)
  proto_eq pr pr' = (proto_of pr = proto_of pr')
`(*:
@description
Various convenience functions.

:*);



(* -------------------------------------------------- *)
(*                        HOST                        *)
(* -------------------------------------------------- *)

(*: @section [[hostty_host]] ALL The host
TODO3
:*)

(*
Speculation: POSIX should perhaps be an architecture, one that yields
a very underspecified response.
*)

val _ = Hol_datatype `(*: host details :*)
                      host = <|
                                arch  : arch;  (* architecture *)
                                privs : bool;  (* whether process has root/CAP_NET_ADMIN privilege *)
                                ifds  : ifid |-> ifd; (* interfaces *)
                                rttab : routing_table;  (* routing table *)
                                ts    : tid |-> hostThreadState timed; (* host view of each thread state *)
                                files : fid |-> file; (* files *)
                                socks : sid |-> socket; (* sockets *)
                                listen : sid list; (* list of listening sockets *)
				bound : sid list; (* list of sockets bound: head of list was first to be bound *)
                                iq    : msg list timed; (* input queue *)
                                oq    : msg list timed; (* output queue *)
                                bndlm : bandlim_state; (* bandlimiting *)
                                ticks : ticker;  (* ticker *)
                                fds   : fd |-> fid; (* file descriptors (per-process) *)
                                params: hostParams (* configuration info*)
                             |>`
(*: @description
The input and output queue timers model the interrupt scheduling delay; the first element (if any) must be processed by the timer expiry. :*)
;



                                (* the [[fds]] are per-process state,
                                but the specification considers only
                                one process for now) *)

                                (* add stuff like signal handlers and
                                masks here *)


val privileged_ports_def = Phase.phase 1 Define`
  privileged_ports h = { Port n | n < 1024 }
`(*: @mergewithnext :*);

val ephemeral_ports_def = Phase.phase 1 Define`
  ephemeral_ports h = { Port n | n >= h.params.min_eph_port /\ n <= h.params.max_eph_port }
`
(*:
@description
Ports below 1024 (on all systems that we know of) are reserved, and can be bound
by privileged users only.  Additionally there is a range of ports (1024 through
2048, 3072 or 4999 or 32768 through 61000 inclusive, depending on configuration,
are used for autobinding, when no specific port is specified; these ports are
called "ephemeral".
:*)
;



(* -------------------------------------------------- *)
(*                     TRACE RECORD                   *)
(* -------------------------------------------------- *)

(*: @section [[hostty_trace]] ALL Trace records

   For BSD testing we make use of the BSD |TCP_DEBUG| option, which
   enables TCP debug trace records at various points in the code.  This
   permits earlier resolution of nondeterminism in the trace checking
   process.

   Debug records contain IP and TCP headers, a timestamp, and a copy
   of the implementation TCP control block.
%
   Three issues complicate their use: firstly, not all the relevant
   state appears in the trace record; secondly, the model deviates in
   its internal structures from the BSD implementation in several
   ways; and thirdly, BSD generates trace records in the middle of
   processing messages, whereas the model performs atomic transitions
   (albeit split for blocking invocations).
 %
   These mean that in different circumstances we can use only some of
   the debug record fields.
%
   To save defining a whole new datatype, we reuse [[tcpcb]].  However, we
   define a special equality that only inspects certain fields, and
   leaves the others unconstrained.

   Frustratingly, the |is1| |ps1| |is2| |ps2| are not always
   available, since although the TCP control block is structure-copied
   into the trace record, the embedded Internet control block is not!
   However, in cases where these are not available, the |iss| should
   be sufficiently unique to identify the socket of interest.

:*)

val _ = type_abbrev ("tracerecord", ``: traceflavour
                                       # sid
                                       # (ip option (* is1 *)
                                           # port option (* ps1 *)
                                           # ip option (* is2 *)
                                           # port option (* ps2 *)
                                       ) option (* not always available! *)
                                       # tcpstate (* st *)
                                       # tcpcb (* cb subset *)
                                    ``);

(* TCPCB fields of interest *)
(* we've tried to pick out the ones that are specified in RFCs *)
val tracecb_eq = Phase.phase 2 Define`(*: compare two control blocks for "equality" modulo known issues :*)
  tracecb_eq (flav:traceflavour) (st:tcpstate) (es:error option) (cb:tcpcb) (cb':tcpcb)
    = T (*: placeholder :*)
`;


val tracesock_eq = Phase.phase 2 Define`(*: compare two sockets for "equality" modulo known issues :*)
  tracesock_eq (flav,sid,quad,st,cb) sid' sock
    = (proto_of sock.pr = PROTO_TCP /\
       let tcp_sock = tcp_sock_of sock in
       sid = sid' /\
       (*: If trace is [[TA_DROP]] then the [[is2,ps2]] values in the trace may
          not match those in the socket record --- the segment is
          dropped because it is somehow invalid (and thus not safe to
          compare) :*)
       (case quad of
         SOME (is1,ps1,is2,ps2) -> is1 = sock.is1 /\
                                   ps1 = sock.ps1 /\
                                   (if flav = TA_DROP then T else is2 = sock.is2) /\
                                   (if flav = TA_DROP then T else ps2 = sock.ps2) ||
         NONE                   -> T) /\
       st  = tcp_sock.st /\
       tracecb_eq flav st sock.es cb tcp_sock.cb)
`;



(* -------------------------------------------------- *)

val _ = export_theory();




