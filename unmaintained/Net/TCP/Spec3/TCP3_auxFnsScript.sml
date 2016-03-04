(* A HOL98 specification of TCP *)

(* Host auxiliary functions *)

(*[ RCSID "$Id: TCP3_auxFnsScript.sml,v 1.16 2009/02/20 13:08:08 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

local open (*TCP1_baseTypesTheory
           TCP1_utilsTheory
           TCP1_paramsTheory *)
           TCP3_hostTypesTheory
	   TCP3_streamTypesTheory

           containerTheory  (* for LIST_TO_SET *)
in end;

(*
val dep_tokens = fn s =>
		    let
		       val delim = fn c => c = #" "
		   in
			String.tokens delim s
		    end;

val loadDeps = fn s => app (load o (implode o rev o tl o tl o tl o rev o explode)) (tl (dep_tokens s));

loadDeps "TCP3_auxFnsScript.uo: /local/scratch/tjr22/hol98/sigobj/bossLib.ui Version.ui TCP1_baseTypesTheory.ui TCP1_utilsTheory.ui HolDoc.ui TCP3_hostTypesTheory.ui /local/scratch/tjr22/hol98/sigobj/Parse.ui /local/scratch/tjr22/hol98/sigobj/HolKernel.ui TCP1_paramsTheory.ui /local/scratch/tjr22/hol98/sigobj/boolLib.ui /local/scratch/tjr22/hol98/sigobj/containerTheory.ui Phase.ui";

*)

val Term = Parse.Term;

val _ = new_theory "TCP3_auxFns";

val _ = Version.registerTheory "$RCSfile: TCP3_auxFnsScript.sml,v $" "$Revision: 1.16 $" "$Date: 2009/02/20 13:08:08 $";

(*: @chapter [[TCP3_auxFns]] Auxiliary functions

This file defines a large number of auxiliary functions to the host
specification.

:*)


(* ------------------------------------------------------------------ *)
(*:
@section [[stream_routing]] ALL Stream versions of routing functions


:*)

val stream_test_outroute_def = Define`(*: if destination IP specified, do [[test_outroute_ip]] :*)
  stream_test_outroute(is2,rttab,ifds,arch)
    = case is2 of
        SOME i2 -> SOME (test_outroute_ip(i2,rttab,ifds,arch))
     || _ -> NONE
`
(*:
@description
Version for streams.
:*)
;

val stream_loopback_on_wire_def = Phase.phase 1 Define`(*: check if a message bears a loopback address :*)
  stream_loopback_on_wire (is1,is2) (ifds:ifid |-> ifd) =
     case (is1, is2) of
        (NONE, NONE) -> F
     || (NONE, SOME j) -> F
     || (SOME i, NONE) -> F
     || (SOME i, SOME j) -> in_loopback i /\ ~in_local ifds j
`
(*:
@description
Version for streams.
:*)
;


(* ------------------------------------------------------------------ *)
(*:
@section [[aux_files]] ALL Files, file descriptors, and sockets

   The open files of a host are modelled by a set of open file
   descriptions, indexed by [[fid]].  The open files of a process are
   identified by file descriptor [[fd]], which is an index into a
   table of [[fid]]s.  This table is modelled by a finite map.
   File descriptors are isomorphic to the natural numbers.

:*)
(* ------------------------------------------------------------------ *)


val sane_socket_def = Phase.phase 1 Define`(*: socket sanity invariants hold :*)
  sane_socket sock = T
`
(*:
@description
 There are some demonstrable invariants on a socket; this definition
 asserts them.  These are largely here to provide explicit bounds to
 the symbolic evaluator.

:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[aux_binding]] ALL Binding

Both TCP and UDP have a concept of a socket being \emph{bound} to a
local port, which means that that socket may receive datagrams
addressed to that port.  A specific local IP address may also be
specified, and a remote IP address and/or port.  This `quadruple'
(really a quintuple, since the protocol is also relevant) is used to
determine the socket that best matches an incoming datagram.

The functions in this section determine this best-matching socket,
using rules appropriate to each protocol.  Support is also provided
for determining which ports are available to be bound by a new socket,
and for automatically choosing a port to bind to in cases where the
user does not specify one.

:*)
(* ------------------------------------------------------------------ *)


(* DON'T phase: in betters *)
val bound_ports_protocol_autobind_def  = Define `(*: the set of ports currently bound by a socket for a protocol :*)
  bound_ports_protocol_autobind pr socks = {p | ?s:socket.
						 s IN FRANGE socks /\ s.ps1 = SOME p /\
                                                 proto_of s.pr = pr}
`(*:
@description
Rebinding of ports already bound is often restricted. [[bound_ports_protocol_autobind]] is a list of all ports having
a socket of the given protocol binding that port.

:*)
 ;



(* DON'T phase: in betters *)
val bound_port_allowed_def = Define`(*: is it permitted to bind the given (IP,port) pair? :*)
  bound_port_allowed pr socks sf arch is p =
    p NOTIN
     {port | ?s:socket.
        s IN FRANGE socks /\ s.ps1 = SOME port /\
        proto_eq s.pr pr /\
        (if bsd_arch arch /\ SO_REUSEADDR IN sf.b then
           s.is2 = NONE /\ s.is1 = is
         else if linux_arch arch /\ SO_REUSEADDR IN sf.b /\ SO_REUSEADDR IN s.sf.b /\
                 ((?tcp_sock. TCP_PROTO(tcp_sock) = s.pr /\ ~(tcp_sock.st = LISTEN)) \/
                   ?udp_sock. UDP_PROTO(udp_sock) = s.pr) then
            F (* If socket is not in LISTEN state or is a UDP socket can always rebind here *)
	 else if windows_arch arch /\ SO_REUSEADDR IN sf.b then
	    F (* can rebind any UDP address; not sure about TCP - assume the same for now *)
         else
            (is = NONE \/ s.is1 = NONE \/ (?i:ip. is = SOME i /\ s.is1 = SOME i))) }
`
(*:
@description
   This determines whether binding a socket (of protocol [[pr]]) to local address [[is,p]] is
   permitted, by considering the other bound sockets on the host and the
   state of the sockets' [[SO_REUSEADDR]] flags.
   Note: SB believes this definition is correct for TCP and UDP on BSD
   and Linux through exhaustive manual verification.
   Note: WinXP is still to be checked.
:*)
;

(* old bound_ports_protocol and bound_ipports_protocol removed;
OBSELETED by bound_port_allowed.  See CVS, v1.166 and before *)

val autobind_def = Phase.phase 1 Define`(*: set of ports available for autobinding :*)
  autobind(SOME p,_,_,_) = {p} /\
  autobind(NONE,pr,h,socks) = (ephemeral_ports h) DIFF (bound_ports_protocol_autobind pr socks)
`
(*:
@description
Note that [[SO_REUSEADDR]] is not considered when choosing a port to
autobind to.

:*);

val bound_after_def = Phase.phase 1 Define `(*: was [[sid]] bound more recently than [[sid']]? :*)
  bound_after sid sid' [] = ASSERTION_FAILURE "bound_after" (* should never reach this case *) /\
  bound_after sid sid' (sid0::bound) =
    if sid = sid0 then T  (* newly-bound sockets are added to the head *)
    else if sid' = sid0 then F
	else bound_after sid sid' bound
`(*:@mergewithnext:*);

val match_score_def =
  Phase.phase 1  Define`(*: score the match against the given pattern of the given quadruple :*)
    (match_score (_,NONE,_,_) _ = 0n) /\
    (match_score (NONE, SOME p1, NONE, NONE) (i3,ps3,i4,ps4) =
       if ps4 = SOME p1 then 1 else 0) /\
    (match_score (SOME i1, SOME p1, NONE, NONE) (i3,ps3,i4,ps4) =
       if (i1 = i4) /\ (SOME p1 = ps4) then 2 else 0) /\
    (match_score (SOME i1, SOME p1, SOME i2, NONE) (i3,ps3,i4,ps4) =
       if (i2 = i3) /\ (i1 = i4) /\ (SOME p1 = ps4) then 3 else 0) /\
    (match_score (SOME i1, SOME p1, SOME i2, SOME p2) (i3,ps3,i4,ps4) =
       if (SOME p2 = ps3) /\ (i2 = i3) /\ (i1 = i4) /\ (SOME p1 = ps4) then 4
       else 0)
`
(*:
@description
These two functions are used to match an incoming UDP datagram to a
socket. The [[bound_after]] function returns [[T]] if the socket
[[sid]] (the first agrument) was bound after the socket [[sid']] (the
second argument) according to a list of bound sockets (the third
argument).

The [[match_score]] function gives a score specifying how closely two
address quads, one from a socket and one from a datagram, correspond;
a higher score indicates a more specific match.

:*)
;

val lookup_udp_def = Phase.phase 2 Define `(*: the set of sockets matching an address quad, for UDP :*)
  lookup_udp socks quad bound arch =
           { sid | sid IN FDOM socks /\
	           let s = socks ' sid in
		   let sn = match_score (s.is1,s.ps1,s.is2,s.ps2) quad in
		       sn > 0 /\
		       if windows_arch arch  then
			   if sn = 1 then
			       ~(? (sid',s') :: (socks \\ sid). match_score (s'.is1,s'.ps1,s'.is2,s'.ps2) quad > sn)
			   else T
		       else
			   ~(?(sid',s') :: (socks \\ sid).
				       (match_score (s'.is1,s'.ps1,s'.is2,s'.ps2) quad > sn \/
					(linux_arch arch /\ match_score (s'.is1,s'.ps1,s'.is2,s'.ps2) quad = sn /\
                                         bound_after sid' sid bound))) }
`
(*:

@description
This function returns a set of UDP sockets which the datagram with
address quad [[quad]] may be delivered to. For FreeBSD and Linux there
is only one such socket; for WinXP there may be multiple.

For each socket in the finite map of sockets [[socks]], the score,
[[sn]], of the matching of the socket's address quad and [[quad]] is
computed using [[match_score]].

@variation FreeBSD

For FreeBSD, the set contains the sockets for which  the score is greater than zero and there is no other
socket in [[socks]] with a higher score.

@variation Linux

For Linux, the set contains the sockets for which the score is greater than zero, there are no sockets
with a higher score, and the socket was bound to its local port after
all the other sockets with the same score.

@variation WinXP

For WinXP, the set contains all the sockets with score greater than one and also the sockets for which the score is one, [[sn=1]], and there are no sockets
with greater scores.

:*);

val tcp_socket_best_match_def = Phase.phase 2 Define `(*: the set of sockets matching a quad, for TCP :*)
  tcp_socket_best_match (socks : sid |-> socket) (sid,sock) (seg : tcpSegment) arch =
    (* is the socket sid the best match for segment seg? *)
    let s = sock in
    let score = match_score (s.is1, s.ps1, s.is2, s.ps2)
                            (THE seg.is1, seg.ps1, THE seg.is2, seg.ps2) in
    ~(?(sid',s') :: socks \\ sid.
                match_score (s'.is1, s'.ps1, s'.is2, s'.ps2)
                            (THE seg.is1, seg.ps1, THE seg.is2, seg.ps2) > score)
`
(*:

 @description
 This function determines whether a given socket [[sid]] is the best match for a
 received TCP segment [[seg]].

 The score (obtained using [[match_score]]) for the given
 socket is determined, and compared with the score for each other
 socket in [[socks]].  If none have a greater score, this is the best
 match and true is returned; otherwise, false is returned.

:*);

val lookup_icmp_def = Phase.phase 2 Define `(*: the set of sockets matching a quad, for ICMP :*)
  lookup_icmp socks icmp arch bound =
       { sid0 | ? (sid,sock) :: socks.
	       sock.ps1 = icmp.ps3 /\ proto_of sock.pr = icmp.proto /\ sid0 = sid /\
	       if windows_arch arch then T
               else
		   sock.is1 = icmp.is3 /\ sock.is2 = icmp.is4 /\
                   (sock.ps2 = icmp.ps4 \/
                    (linux_arch arch /\
		     proto_of sock.pr = PROTO_UDP /\ sock.ps2 = NONE /\
		     ~(? (sid',s) :: (socks \\ sid).
		     	     s.is1 = icmp.is3 /\ s.is2 = icmp.is4 /\
		     	     s.ps1 = icmp.ps3 /\ s.ps2 = icmp.ps4 /\
		     	     proto_of s.pr = icmp.proto /\
		     	     bound_after sid' sid bound)
                    )) }
`(*:

  @description

  This function returns the set of sockets matching a received ICMP
  datagram [[icmp]].

  An ICMP datagram contains the initial portion of the header of the
  original message to which it is a response.  For a socket to match,
  it must at least be bound to the same port and protocol as the
  source of the original message.  Beyond this, architectures differ.
  Usually, the socket must be connected, and connected to the same
  port as the original destination; and the source and destination IP
  addresses must agree.

  @variation WinXP

  For Windows, the socket need not be connected, and the source and
  destination IP addresses need not agree; an ICMP is delivered to
  one socket bound to the same port and protocol as the original
  source.

  @variation Linux

  For Linux, UDP ICMPs may also be delivered to unconnected sockets,
  as long as no matching connected socket was bound more recently than
  that socket.

  @variation FreeBSD

  For FreeBSD, the behaviour is as described above.


:*);



(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[misc_aux]] TCP TCP Options

TCP option handling.

     :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)



(* ----------------------------------------------------------- *)
(* WARNING: the two definitions following must be kept in sync *)
(* ----------------------------------------------------------- *)


(* Don't phase: handled in testEval *)
val do_tcp_options_def = Define`
(*: Constrain the TCP timestamp option values that appear in an outgoing segment :*)
  do_tcp_options cb_tf_doing_tstmp cb_ts_recent cb_ts_val  =
    if cb_tf_doing_tstmp then
       let ts_ecr' = option_case (ts_seq 0w) I (timewindow_val_of cb_ts_recent) in
           SOME(cb_ts_val,ts_ecr')
     else
         NONE
`;


val calculate_tcp_options_len_def =  Phase.phase 1 Define`
(*: Calculate the length consumed by the TCP options in a real TCP segment :*)
  calculate_tcp_options_len cb_tf_doing_tstmp =
    if cb_tf_doing_tstmp then 12 else 0 : num
`
(*: @description
This calculation omits
   window-scaling and mss options as these only appear in SYN segments during connection setup.
%
   The total length consumed by all options will always be a multiple of 4 bytes due to padding.
   If more TCP options were added to the model, the space consumed by options would be
   architecture/options/alignment/padding dependent.
:*);

(*:
 @section [[aux_buffers]] ALL Buffers, windows, and queues

Various functions that compute buffer sizes, window sizes, and
remaining send queue space.  Some of these computations are
architecture-specific.

:*)

(* Don't Phase: handled by testEval *)
val calculate_buf_sizes_def = Define`
(*: Calculate buffer sizes for [[rcvbufsize]], [[sndbufsize]], [[t_maxseg]], and [[snd_cwnd]]
:*)
  calculate_buf_sizes cb_t_maxseg seg_mss bw_delay_product_for_rt is_local_conn
                       rcvbufsize sndbufsize cb_tf_doing_tstmp arch =

    let t_maxseg' =
      (*: TCPv2p901 claims min 32 for "sanity"; FreeBSD4.6 has 64 in |tcp_mss()|.
         BSD has the route MTU if avail, or [[MIN MSSDFLT (link MTU)]] otherwise, as the first argument
         of the MIN below.  That is the same calculation as we did in [[connect_1]]. We don't repeat it,
         but use the cached value in [[cb.t_maxseg]]. :*)
      let maxseg = (MIN cb_t_maxseg (MAX 64 (option_case MSSDFLT I seg_mss))) in
          if linux_arch arch then
            maxseg
          else
            (*: BSD subtracts the size consumed by options in the TCP
            header post connection establishment. The WinXP and Linux
            behaviour has not been fully tested but it appears Linux
            does not do this and WinXP does. :*)
            maxseg - (calculate_tcp_options_len cb_tf_doing_tstmp)
    in
    (*: round down to multiple of cluster size if larger (as BSD).
    From BSD code; assuming true for WinXP for now :*)
    let t_maxseg'' = if linux_arch arch then t_maxseg'  (* from tests *)
                     else rounddown MCLBYTES t_maxseg' in

    (* buffootle: rcv *)
    let rcvbufsize' = option_case rcvbufsize I bw_delay_product_for_rt in
    let (rcvbufsize'',t_maxseg''') = (if rcvbufsize' < t_maxseg''
                                     then (rcvbufsize',rcvbufsize')
                                     else (MIN SB_MAX (roundup t_maxseg'' rcvbufsize'),
                                           t_maxseg'')) in

    (* buffootle: snd *)
    let sndbufsize' = option_case sndbufsize I bw_delay_product_for_rt in
    let sndbufsize'' = (if sndbufsize' < t_maxseg'''
                        then sndbufsize'
                        else MIN SB_MAX (roundup t_maxseg'' sndbufsize')) in

    let do_rfc3390 = T in

    (* compute initial cwnd *)
    let snd_cwnd =
      if do_rfc3390 then MIN (4 * t_maxseg''') (MAX (2 * t_maxseg''') 4380)
      else
        (t_maxseg''' * (if is_local_conn then SS_FLTSZ_LOCAL else SS_FLTSZ)) in
    (rcvbufsize'',sndbufsize'',t_maxseg''',snd_cwnd)
`
(*: @description
Used in [[deliver_in_1]] and [[deliver_in_2]]. :*)
;

(* FIXME not sure about do_rfc3390 = T *)

(* REMARK remove this defn - no longer used *)
val send_queue_space_def = Phase.phase 1 Define `
    send_queue_space (sndq_max : num) sndq_size oob arch maxseg i2 =
       { n | if bsd_arch arch then
	        n <= (sndq_max - sndq_size) + (if oob then oob_extra_sndbuf else 0)
	     else if linux_arch arch then
		 (if in_loopback i2 then
		      n = maxseg + ((sndq_max - sndq_size) DIV 16816) * maxseg
		  else
		      n = (2 * maxseg) + ((sndq_max - sndq_size - 1890) DIV 1888) * maxseg)
	     else n >= 0 }
`
(*:
 @description
   Calculation of the usable send queue space.

   FreeBSD calculates send buffer space based on the byte-count size and
   max, and the number and max of mbufs. As we do not model mbuf usage precisely we are somewhat nondeterministic
   here.

   Linux calculates it based on the MSS: the space is some multiple of
   the MSS; the number of bytes for each MSS-sized segment is the
   MSS+overhead where overhead is 420+(20 if using IP), which is why
   the i2 argument is needed.

   Windows is very strange.  Leaving it completely unconstrained is not
   what actually happens, but more investigation is needed in future to determine the actual behaviour.

 :*) ;


(* ------------------------------------------------------------------ *)
(*:
@section [[aux_udp]] UDP UDP support

Performing a UDP send, filling in required details as necessary.

:*)
(* ------------------------------------------------------------------ *)

val dosend_def =
  Phase.phase 1 Define`(*: do a UDP send, filling in source address and port as necessary :*)
   (dosend (ifds, rttab, (NONE, data), (SOME i1, SOME p1, SOME i2, ps2), oq, oq', ok) =
      enqueue_oq(oq,UDP(<| is1 := SOME i1; is2 := SOME i2;
			   ps1 := SOME p1; ps2 := ps2;
			   data := data |>),
		 oq',ok)) /\
   (dosend (ifds, rttab, (SOME(i,p), data), (NONE, SOME p1, NONE, NONE), oq, oq', ok) =
      (?i1'.enqueue_oq(oq,UDP(<| is1 := SOME i1'; is2 := SOME i;
		   	         ps1 := SOME p1;  ps2 := SOME p;
			         data := data |>),
		       oq',ok) /\ i1' IN auto_outroute(i,NONE,rttab,ifds))) /\
   (dosend (ifds, rttab, (SOME(i,p), data),(SOME i1, SOME p1, is2, ps2), oq, oq', ok) =
      enqueue_oq(oq,UDP(<| is1 := SOME i1; is2 := SOME i;
			   ps1 := SOME p1; ps2 := SOME p;
			   data := data |>),
		 oq',ok))`
(*:
@description
 For use in UDP [[sendto()]].
:*)
;


(* ------------------------------------------------------------------ *)
(*:
@section [[aux_pmtu]] TCP Path MTU Discovery

For efficiency and reliability, it is best to send datagrams that do
not need to be fragmented in the network.  However, TCP has direct
access only to the maximum packet size (MTU) for the interfaces at
either end of the connection -- it has no information about routers
and links in between.

To determine the MTU for the entire path, TCP marks all datagrams `do
not fragment'.  It begins by sending a large datagram; if it receives
a `fragmentation needed' ICMP in return it reduces the size of the
datagram and repeats the process.  Most modern routers include the
link MTU in the ICMP message; if the message does not contain an MTU,
however, TCP uses the next lower MTU in the table below.

:*)
(* This is needed by icmp_2 *)
(* ------------------------------------------------------------------ *)


val next_smaller_def = Phase.phase 1 Define`(*: find next-smaller element of a set :*)
  (next_smaller:(num->bool) -> num -> num) xs y = @x::xs. x < y /\ !x'::xs. x' > x ==> x' >= y
`(*:@mergewithnext:*);

val mtu_tab_def = Phase.phase 1 Define`(*: path MTU plateaus to try :*)
  mtu_tab arch = if linux_arch arch then
                     {32000; 17914; 8166; 4352; 2002; 1492; 576; 296; 216; 128; 68} : num set
                 else
                     {65535; 32000; 17914; 8166; 4352; 2002; 1492; 1006; 508; 296; 68}
`
(*:
@description
 MTUs to guess for path MTU discovery.  This table is from RFC1191,
   and is the one that appears in BSD.

   On |comp.protocols.tcp-ip, Sun, 15 Feb 2004 01:38:26 -0000,
   <102tjcifv6vgm02@corp.supernews.com>, kml@bayarea.net (Kevin Lahey)|
   suggests that this is out-of-date, and 2312 (WiFi 802.11), 9180
   (common ATM), and 9000 (jumbo Ethernet) should be added.  For some
   polemic discussion, see |http://www.psc.edu/~mathis/MTU/|.

   RFC1191 says explicitly "We do not expect that the values in the
   table [...] are going to be valid forever.  The values given here
   are an implementation suggestion, NOT a specification or
   requirement.  Implementors should use up-to-date references to pick
   a set of plateaus [...]".  BSD is therefore not compliant here.

   Linux adds 576, 216, 128 and drops 1006.  576 is used in X.25
   networks, and the source says 216 and 128 are needed for AMPRnet
   AX.25 paths.  1006 is used for SLIP, and was used on the ARPANET.
   Linux does not include the modern MTUs listed above.

:*)
;


(* ------------------------------------------------------------------ *)
(*:
@section [[initial_cb]] TCP The initial TCP control block

The initial state of the TCP control block.

:*)
(* ------------------------------------------------------------------ *)


(* the all-bits-zero TCPCB, i.e., bzero(), as updated by tcp_newtcpcb *)
(* Don't Phase: handled specially by testEval *)
val initial_cb_def = Define`
  initial_cb =
    <|
       tt_keep           := NONE;
       t_softerror       := NONE
    |>
`;



(* ALL THIS BELOW WAS AT THE START OF TCP1_hostLTSSCript.sml *)

(*: @chapter [[TCPmajorAuxFns]] Auxiliary functions for TCP segment creation and drop

We gather here all the general TCP segment generation and processing
functions that are used in the host LTS.

:*)


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_segment_creation]] TCP General Segment Creation

The TCP output routines.  These, together with the input routines in
[[deliver_in_3]], form the heart of TCP.


:*)


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* Don't Phase: handled specially by netEval *)
val tcp_output_required_def = Define`
(*: determine whether TCP output is required :*)
  tcp_output_required (do_output, persist_fun) =
  (do_output IN {T;F} /\
  persist_fun IN {NONE; SOME (\cb:tcpcb.cb)})`

(*:

  @description

  This function determines if it is currently necessary to emit a
  segment.  It is not quite a predicate, because in certain
  circumstances the operation of testing may start or reset the
  persist timer, and alter [[snd_nxt]].  Thus it returns a pair of a
  flag [[do_output]] (with the obvious meaning), and an optional
  mutator function [[persist_fun]] which, if present, performs the
  required updates on the TCP control block.

  @internal

  we feel that there should be a simpler version of tcp_output, that is called from various places
  in deliver_in_3.  The full glory of tcp_output below should only be needed by deliver_out_1.  In
  order to write the simpler version, though, we need to work out exactly when all the various
  conditions in tcp_output hold, particularly at the moments it is called from deliver_in_3.

  NB: whenever tcp\_output.c has nothing to do, absolutely nothing happens, even though this might
  not be immediately apparent; we know [[~do_output ==> ~force_output ==> tt_persist' =
  cb.tt_persist]], and nothing else has changed.

  ARGH!  Not quite true - snd_cwnd may change if idle!

  About cb.tf_shouldacknow:  -- explicit output requested
      ? on receiving a keepalive probe; or
      ? on receiving a repeated old ACK (fast retransmit); or
      ? by recv() when a zero-size (or teeny) window is opened
      ? by send() when new urgent data is sent, changing sndurp
      ? when performing dropafterack

  BSD uses cb.tf_acknow for some of these; P thinks we should have distinct semaphores (with
  sensible names) for each case (cantsndmore should have a similar name).  Are these all pure
  boolean semaphores?  When we come to Level 3, not sure our urgency idiom is going to be very lucid
  - guess BSD just doesn't allow interleaving between (eg) such a recv() and the call to
  tcp_output.

  -- delayed ack timer (tt_delack) expires - dealt with by timer_tt_delack_1

  force_output -- persist timer expires (or send_OOB called) - believe dealt with by snd_wnd_unused
  munging above

  -- retransmission timer (tt_rexmt) expires - currently dealt with by timer_tt_rexmt_1

  IS_SOME tcp_sock.sndurp:

  This condition cannot made false by emitting a segment, whereas the other disjuncts may be. OTOH,
  this condition is superfluous as it is (really) contained within have_data_{or_fin_}to_send

:*);

val tcp_output_really_def = Phase.phase 2 Define`
(*: do TCP output :*)
  tcp_output_really sock (sock',outsegs') =
    let tcp_sock = tcp_sock_of sock in
    let cb = tcp_sock.cb in

    (*: Assert that the socket is fully bound and connected :*)
    sock.is1 <> NONE /\
    sock.is2 <> NONE /\
    sock.ps1 <> NONE /\
    sock.ps2 <> NONE /\

    (*: Is it possible that a [[FIN]] may need to be transmitted? :*)
    let fin_required = (sock.cantsndmore /\ tcp_sock.st NOTIN {FIN_WAIT_2;TIME_WAIT}) in

    (*: Should [[FIN]] be set in this segment? :*)
    choose snd_nxt_plus_length_data_to_send_ge_last_sndq_data_seq :: {T;F}.
    let FIN = (fin_required /\ snd_nxt_plus_length_data_to_send_ge_last_sndq_data_seq) in

    ? snd_nxt' rcv_nxt URG ACK PSH win urp_ ts data_to_send.
    let seg = <| is1  := sock.is1;
                 is2  := sock.is2;
                 ps1  := sock.ps1;
                 ps2  := sock.ps2;
                 seq  := snd_nxt';
                 ack  := rcv_nxt;
                 URG  := URG;
                 ACK  := ACK;
                 PSH  := PSH;
                 RST  := F;
                 SYN  := F;
                 FIN  := FIN;
                 win  := win;
                 ws   := NONE;
                 urp  := urp_;
                 mss  := NONE;
                 ts   := ts;
                 data := data_to_send
               |> in

    (*: If emitting a [[FIN]] for the first time then change TCP state :*)
    let st' = if FIN then
                case tcp_sock.st of
                  SYN_SENT     -> tcp_sock.st ||    (*: can't move yet -- wait until connection established (see [[deliver_in_2]]/[[deliver_in_3]]) :*)
                  SYN_RECEIVED -> tcp_sock.st ||    (*: can't move yet -- wait until connection established (see [[deliver_in_2]]/[[deliver_in_3]]) :*)
                  ESTABLISHED  -> FIN_WAIT_1 ||
                  CLOSE_WAIT   -> LAST_ACK ||
                  FIN_WAIT_1   -> tcp_sock.st ||    (*: FIN retransmission :*)
                  FIN_WAIT_2   -> tcp_sock.st ||    (*: can't happen       :*)
                  CLOSING      -> tcp_sock.st ||    (*: FIN retransmission :*)
                  LAST_ACK     -> tcp_sock.st ||    (*: FIN retransmission :*)
                  TIME_WAIT    -> tcp_sock.st       (*: can't happen       :*)
              else
                tcp_sock.st in


    (*: Update the socket :*)
    sock' = sock with <| pr := TCP_PROTO(tcp_sock with <| st := st' |>) |> /\

    (*: Constrain the list of output segments to contain just the segment being emitted :*)
    outsegs' = [TCP seg]
`
(*:

  @description

  This function constructs the next segment to be output.  It is
  usually called once [[tcp_output_required]] has returned true, but
  sometimes is called directly when we wish always to emit a segment.
  A large number of TCP state variables are modified also.

  Note that while constructing the segment a variety of errors such as
  [[ENOBUFS]] are possible, but this is not modelled here. Also,
  window shrinking is not dealt with properly here.


  @internal

  Deliberately not requiring the FIN to fit in the window, only the actual data.  We think this is
  the only sensible way; we're not sure what BSD does

  The BSD code jumps to roughly the top of tcp_output again if 'sendalot' has been set.  Instead, we
  rely on the fact that deliver_out_1 can fire again if required, with any (possibly zero) time
  delay.

  If attempting to emit a segment when [[snd_nxt]] is past the end of the send queue and we a
  previous [[FIN]] that is unacked, then set [[snd_nxt]] temporarily to be the seq number of the
  [[FIN]] in order to construct a valid segment. This arises if a [[FIN]] was sent and the remote
  end sends a [[FIN]],[[ACK]] segment where the [[ack]] value does not acknowledge our [[FIN]]. When
  we [[ACK]] their [[FIN]] our seq number must be in range (and thus [[FIN]] should be set too)

:*);

val stream_tcp_output_really_def = Phase.phase 2 Define`
(*: do TCP output :*)
  stream_tcp_output_really sock (sock',FIN) =
    let tcp_sock = tcp_sock_of sock in
    let cb = tcp_sock.cb in

    (*: Assert that the socket is fully bound and connected :*)
    sock.is1 <> NONE /\
    sock.is2 <> NONE /\
    sock.ps1 <> NONE /\
    sock.ps2 <> NONE /\

    (*: Is it possible that a [[FIN]] may need to be transmitted? :*)
    let fin_required = (sock.cantsndmore /\ tcp_sock.st NOTIN {FIN_WAIT_2;TIME_WAIT}) in

    (*: Should [[FIN]] be set in this segment? :*)
    choose snd_nxt_plus_length_data_to_send_ge_last_sndq_data_seq :: {T;F}.
    FIN = (fin_required /\ snd_nxt_plus_length_data_to_send_ge_last_sndq_data_seq) /\

    (*: If emitting a [[FIN]] for the first time then change TCP state :*)
    let st' = if FIN then
                case tcp_sock.st of
                  SYN_SENT     -> tcp_sock.st ||    (*: can't move yet -- wait until connection established (see [[deliver_in_2]]/[[deliver_in_3]]) :*)
                  SYN_RECEIVED -> tcp_sock.st ||    (*: can't move yet -- wait until connection established (see [[deliver_in_2]]/[[deliver_in_3]]) :*)
                  ESTABLISHED  -> FIN_WAIT_1 ||
                  CLOSE_WAIT   -> LAST_ACK ||
                  FIN_WAIT_1   -> tcp_sock.st ||    (*: FIN retransmission :*)
                  FIN_WAIT_2   -> tcp_sock.st ||    (*: can't happen       :*)
                  CLOSING      -> tcp_sock.st ||    (*: FIN retransmission :*)
                  LAST_ACK     -> tcp_sock.st ||    (*: FIN retransmission :*)
                  TIME_WAIT    -> tcp_sock.st       (*: can't happen       :*)
              else
                tcp_sock.st in


    (*: Update the socket :*)
    sock' = sock with <| pr := TCP_PROTO(tcp_sock with <| st := st' |>) |>

`
(*:

  @description

  This function constructs the next segment to be output.  It is
  usually called once [[tcp_output_required]] has returned true, but
  sometimes is called directly when we wish always to emit a segment.
  A large number of TCP state variables are modified also.

  Note that while constructing the segment a variety of errors such as
  [[ENOBUFS]] are possible, but this is not modelled here. Also,
  window shrinking is not dealt with properly here.

  @internal

  Deliberately not requiring the FIN to fit in the window, only the actual data.  We think this is
  the only sensible way; we're not sure what BSD does

  The BSD code jumps to roughly the top of tcp_output again if 'sendalot' has been set.  Instead, we
  rely on the fact that deliver_out_1 can fire again if required, with any (possibly zero) time
  delay.

  If attempting to emit a segment when [[snd_nxt]] is past the end of the send queue and we a
  previous [[FIN]] that is unacked, then set [[snd_nxt]] temporarily to be the seq number of the
  [[FIN]] in order to construct a valid segment. This arises if a [[FIN]] was sent and the remote
  end sends a [[FIN]],[[ACK]] segment where the [[ack]] value does not acknowledge our [[FIN]]. When
  we [[ACK]] their [[FIN]] our seq number must be in range (and thus [[FIN]] should be set too)

:*);


(* combine both chunks into something a bit like tcp_output.c; sometimes useful *)
val tcp_output_perhaps_def = Phase.phase 2 Define`
(*: combination of [[tcp_output_required]] and [[tcp_output_really]] :*)
  tcp_output_perhaps sock (sock',outsegs) =
    ? do_output persist_fun.
    (tcp_output_required (do_output,persist_fun) /\
    let sock'' = sock in
    if do_output then
      tcp_output_really sock'' (sock',outsegs)
    else
      (sock' = sock'' /\ outsegs = []))
`;

val stream_tcp_output_perhaps_def = Phase.phase 2 Define`
(*: combination of [[tcp_output_required]] and [[tcp_output_really]] :*)
(*: [[FINs]] argument records whether any messages were sent, and if so, whether they were a [[FIN]] :*)
  stream_tcp_output_perhaps sock (sock',FINs) =
    ? do_output persist_fun.
    (tcp_output_required (do_output,persist_fun) /\
    let sock'' = sock in
    if do_output then
      ? FIN.
      stream_tcp_output_really sock'' (sock',FIN) (* definitely does send a seg *) /\
      FINs = SOME FIN
    else
      (sock' = sock'' /\ FINs = NONE))
`;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_segment_queueing]] TCP Segment Queueing

Once a segment is generated for output, it must be enqueued for
transmission.  This enqueuing may fail.  These functions model what
happens in this case, and encapsulate the
enqueuing-and-possibly-rolling-back process.

    :*)


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* Don't Phase: handled specially by testEval *)
val rollback_tcp_output_def = Define`
(*: Attempt to enqueue segments, reverting appropriate socket fields if the enqueue fails :*)
  rollback_tcp_output rcvdsyn seg arch rttab ifds is_connect cb_in (cb',es',outsegs') =

    (*: NB: from [[cb0]], only [[snd_nxt]], [[tt_delack]], [[last_ack_sent]], [[rcv_adv]],
        [[tf_rxwin0sent]], [[t_rttseg]], [[snd_max]], [[tt_rexmt]] are
        used. :*)

     (choose allocated :: (if INFINITE_RESOURCES then {T} else {T;F}).
      let route = test_outroute (seg,rttab,ifds,arch) in
      let f1 = \cb. if ~rcvdsyn then
                        cb
                    else
                        cb with <| (* set soft error flag; on ip_output routing failure *)
                                   t_softerror := THE route  (* assumes route = SOME (SOME e) *)
                                |> in
      if ~allocated then  (* allocation failure *)
          cb' = cb_in /\ outsegs' = [] /\ es' = SOME ENOBUFS
      else if route = NONE then  (* ill-formed segment *)
          ASSERTION_FAILURE "rollback_tcp_output:1"  (* should never happen *)
      else if ?e. route = SOME (SOME e) then  (* routing failure *)
          cb' = f1 cb_in /\ outsegs' = [] /\ es' = THE route
      else if loopback_on_wire seg ifds then (* loopback not allowed on wire - RFC1122 *)
          (if windows_arch arch then
               cb' = cb_in /\ outsegs' = [] /\ es' = NONE  (* Windows silently drops segment! *)
           else if bsd_arch arch then
               cb' = cb_in /\ outsegs' = [] /\ es' = SOME EADDRNOTAVAIL
           else if linux_arch arch then
               cb' = cb_in /\ outsegs' = [] /\ es' = SOME EINVAL
           else
               ASSERTION_FAILURE "rollback_tcp_output:2" (* never happen *)
          )
      else
          (?queued.
           outsegs' = [(seg,queued)] /\
           if ~queued then  (* queueing failure *)
               cb' = cb_in /\ es' = SOME ENOBUFS
           else  (* success *)
               cb' = cb_in /\ es' = NONE)
     )
`(* @description
   Attempt to enqueue segments, reverting appropriate socket fields if
   the enqueue fails.  Models failure behaviour of FreeBSD 4.6-RELEASE's
   |tcp_output()|.  We must return whether the queueing succeeded because
   in a few instances we pass the error on up.  Note that we model not
   just failure of |ip_output| with |ENOBUFS|, but also failure of
   |tcp_output| to allocate an mbuf (also |ENOBUFS|).  If enqueue fails, we
   may treat it as either of these two types of failure.  This isn't
   quite right, as the second type is not really an enqueue failure.

   Arguments: segments to emit (zero or one only!), queue on which to
   place them, original socket state (from which rollback values are
   taken), socket state at emit time.  Result (relational): resulting
   socket state, resulting queue, queueing succeeded flag.

    Roll back |tcp_output|'s behaviour if an output error
   (ENOBUFS, of whichever type, or routing failure) occurred.
    Allocation failure is decided internally; routing failure is decided
    canonically; queueing failure is decided externally.

    This code deals with allocation failure in |tcp_output|, routing
    failure, and queueing failure (due to full queue).  [[rcvdsyn]]
    should be set if [[HAVERCVDSYN]], i.e., if routing errors should be
    stored in [[t_softerror]].  [[seg]] is the segment to attempt to
    output.  [[rttab]] and [[ifds]] are from the host, for use by the
    router.  [[cb0]] is the tcpcb before [[tcp_output]], [[cb_in]] is
    that after, and [[cb']] is the output tcpcb.  [[es']] is the output
    error if any.  [[outsegs']] is the output list (empty or singleton)
    of pairs of segments and queueing success flags.
:*)
;

(* Don't Phase: handled specially by testEval *)
val stream_rollback_tcp_output_def = Define`
(*: Attempt to enqueue segments, reverting appropriate socket fields if the enqueue fails :*)
  stream_rollback_tcp_output rcvdsyn (is1,is2) arch rttab ifds cb_in (cb',es',outsegs') =

    (*: NB: from [[cb0]], only [[snd_nxt]], [[tt_delack]], [[last_ack_sent]], [[rcv_adv]],
        [[tf_rxwin0sent]], [[t_rttseg]], [[snd_max]], [[tt_rexmt]] are
        used. :*)

     (choose allocated :: (if INFINITE_RESOURCES then {T} else {T;F}).
      let route = stream_test_outroute (is2,rttab,ifds,arch) in
      let f1 = \cb. if ~rcvdsyn then
                        cb
                    else
                        cb with <| (* set soft error flag; on ip_output routing failure *)
                                   t_softerror := THE route  (* assumes route = SOME (SOME e) *)
                                |> in
      if ~allocated then  (* allocation failure *)
          cb' = cb_in /\ outsegs' = F /\ es' = SOME ENOBUFS
      else if route = NONE then  (* ill-formed segment *)
          ASSERTION_FAILURE "stream_rollback_tcp_output:1"  (* should never happen *)
      else if ?e. route = SOME (SOME e) then  (* routing failure *)
          cb' = f1 cb_in /\ outsegs' = F /\ es' = THE route
      else if stream_loopback_on_wire (is1,is2) ifds then (* loopback not allowed on wire - RFC1122 *)
          (if windows_arch arch then
               cb' = cb_in /\ outsegs' = F /\ es' = NONE  (* Windows silently drops segment! *)
           else if bsd_arch arch then
               cb' = cb_in /\ outsegs' = F /\ es' = SOME EADDRNOTAVAIL
           else if linux_arch arch then
               cb' = cb_in /\ outsegs' = F /\ es' = SOME EINVAL
           else
               ASSERTION_FAILURE "stream_rollback_tcp_output:2" (* never happen *)
          )
      else
          (?queued.
           outsegs' = T /\
           if ~queued then  (* queueing failure *)
               cb' = cb_in /\ es' = SOME ENOBUFS
           else  (* success *)
               cb' = cb_in /\ es' = NONE)
     )
`;


val enqueue_or_fail_def = Phase.phase 2 Define`
(*: wrap [[rollback_tcp_output]] together with enqueue :*)
  enqueue_or_fail rcvdsyn arch rttab ifds outsegs oq cb0 cb_in (cb',oq') =
    (case outsegs of
        []    -> cb' = cb0 /\ oq' = oq
     || [seg] -> (?outsegs' es'.
                  rollback_tcp_output rcvdsyn seg arch rttab ifds F (* X cb0 X *) cb_in (cb',es',outsegs') /\
                  enqueue_oq_list_qinfo (oq,outsegs',oq'))
     || _other84 -> ASSERTION_FAILURE "enqueue_or_fail" (* only 0 or 1 segments at a time *)
    )
`;

(* specialise to stream spec, only deal with one seg to be output *)
val stream_enqueue_or_fail_def = Phase.phase 2 Define`
(*: wrap [[rollback_tcp_output]] together with enqueue :*)
  stream_enqueue_or_fail rcvdsyn arch rttab ifds (is1,is2) cb_in cb' =
    (? es' outsegs'.stream_rollback_tcp_output rcvdsyn (is1,is2) arch rttab ifds cb_in (cb',es',outsegs'))
`;

val stream_enqueue_or_fail_sock_def = Phase.phase 2 Define`
  (*: version of [[enqueue_or_fail]] that works with sockets rather than cbs :*)
  stream_enqueue_or_fail_sock rcvdsyn arch rttab ifds (is1,is2) sock0 sock sock' =
    (*: NB: could calculate [[rcvdsyn]], but clearer to pass it in :*)
    let tcp_sock = tcp_sock_of sock in
    let tcp_sock0 = tcp_sock_of sock0 in
    (?cb'.
     stream_enqueue_or_fail rcvdsyn arch rttab ifds (is1,is2) (tcp_sock_of sock).cb cb' /\
     sock' = sock with <| pr := TCP_PROTO(tcp_sock_of sock with <|
                                             cb := cb'
                        |>) |>)
`;

val enqueue_and_ignore_fail_def = Phase.phase 2 Define`
(*: version of [[enqueue_or_fail]] that ignores errors and doesn't touch the tcpcb :*)
  enqueue_and_ignore_fail arch rttab ifds outsegs oq oq' =
    ?rcvdsyn cb0 cb_in cb'.
    enqueue_or_fail rcvdsyn arch rttab ifds outsegs oq cb0 cb_in (cb',oq')
`;

val enqueue_each_and_ignore_fail_def = Phase.phase 2 Define`
(*: version of above that ignores errors and doesn't touch the tcpcb :*)
  (enqueue_each_and_ignore_fail arch rttab ifds [] oq oq' = (oq = oq')) /\
  (enqueue_each_and_ignore_fail arch rttab ifds (seg::segs) oq oq''
     = ?oq'. enqueue_and_ignore_fail arch rttab ifds [seg] oq oq' /\
             enqueue_each_and_ignore_fail arch rttab ifds segs oq' oq'')
`;

val stream_mlift_tcp_output_perhaps_or_fail_def = Phase.phase 2 Define`
(*: do mliftc for function returning at most one segment and not dealing with queueing flag :*)
  stream_mlift_tcp_output_perhaps_or_fail (* X ts_val X *) arch rttab ifds0 s (s',FIN) =
              ?s1 FINs.
              stream_tcp_output_perhaps s (s1,FINs) /\
              case FINs of
                 NONE       -> s' = s1 /\ FIN = F
              || SOME FIN'  -> (?cb' es' outsegs'.  (* ignore error return *)
                              stream_rollback_tcp_output T (s1.is1,s1.is2) arch rttab ifds0
                                                  (* X (tcp_sock_of s).cb X *) (tcp_sock_of s1).cb (cb',es',outsegs') /\
                              s' = s1 with <| pr := TCP_PROTO(tcp_sock_of s1 with <| cb := cb' |>) |> /\
                              FIN = (outsegs' /\ FIN') )
`;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_incoming_segment]] TCP Incoming Segment Functions

Updates performed to the idle, keepalive, and |FIN_WAIT_2| timers for
every incoming segment.

     :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* Don't Phase: handled by testEval *)
val update_idle_def = Define`
(*: Do updates appropriate to receiving a new segment on a connection :*)
  update_idle tcp_sock tt_keep' =
    choose tf_needfin :: {T;F}.
    tt_keep' = (if ~(tcp_sock.st = SYN_RECEIVED /\ tf_needfin) then
                      (*: reset keepalive timer to 2 hours. :*)
                      SOME (Timed((),slow_timer TCPTV_KEEP_IDLE))
                    else
                      tcp_sock.cb.tt_keep)
`;

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_drop_segment]] TCP Drop Segment Functions

When an erroneous or unexpected segment arrives, it is usually dropped
(i.e, ignored).  However, the peer is usually informed immediately by
means of a RST or ACK segment.

     :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)


val dropwithreset_def = Phase.phase 2 Define`
(*: emit a RST segment corresponding to the passed segment, unless that would be stupid. :*)
  dropwithreset segRST (is1,is2) ifds0 RST =
   (*: Needs list of the host's interfaces, to verify that the incoming segment wasn't broadcast.
   Returns a list of segments. :*)

    if  (* never RST a RST *)
        segRST \/
        (* is segment a (link-layer?) broadcast or multicast? *)
        F \/
        (* is source or destination broadcast or multicast? *)
        (?i1. is1 = SOME i1 /\ is_broadormulticast FEMPTY i1) \/
        (?i2. is2 = SOME i2 /\ is_broadormulticast ifds0 i2)
          (* BSD only checks incoming interface, but should have same effect as long as interfaces don't overlap *)
    then
        RST = F
    else
        RST IN {T;F}
`;

(*
val mlift_dropafterack_or_fail_def = Phase.phase 2 Define`
(*: send immediate ACK to segment, but otherwise process it no further :*)
  mlift_dropafterack_or_fail seg arch rttab ifds ticks (sock,bndlm) ((sock',bndlm',outsegs'),continue) =
   (*:    [[ifds]] is just in case we need to send a RST, to make sure we don't
   send it to a broadcast address. :*)
   let tcp_sock = tcp_sock_of sock in
    (continue = T /\
     let cb = tcp_sock.cb in
     choose ACK :: {T;F}.
     choose ack_lt_snd_una_or_snd_max_lt_ack :: {T;F}.
     if tcp_sock.st = SYN_RECEIVED /\
        seg.ACK /\
        (let ack = tcp_seq_flip_sense seg.ack in
          ack_lt_snd_una_or_snd_max_lt_ack)
     then
         (*: break loop in "LAND" DoS attack, and also prevent ACK
            storm between two listening ports that have been sent
            forged SYN segments, each with the source address of
            the other. (|tcp_input.c:2141|) :*)
         sock' = sock /\
         dropwithreset seg.RST (sock.is1,sock.is2) ifds ticks BANDLIM_RST_OPENPORT bndlm bndlm' (MAP FST outsegs')
              (* ignore queue full error *)
     else
         (?sock1 msg cb' es'.  (* ignore errors *)
          let tcp_sock1 = tcp_sock_of sock1 in
          tcp_output_really sock (sock1,[msg]) /\  (*: did set [[tf_acknow]] and call [[tcp_output_perhaps]], which seemed a bit silly :*)
          (*: notice we here bake in the assumption that the timestamps use the same counter as the band limiter; perhaps this is unwise :*)
          rollback_tcp_output T msg arch rttab ifds F (* X tcp_sock.cb X *) tcp_sock1.cb (cb',es',outsegs') /\
          sock' = sock1 with <| pr := TCP_PROTO(tcp_sock1 with <| cb := cb' |>) |> /\
          bndlm' = bndlm))
;
*)

val stream_mlift_dropafterack_or_fail_def = Phase.phase 2 Define`
(*: send immediate ACK to segment, but otherwise process it no further :*)
   stream_mlift_dropafterack_or_fail segRST arch rttab ifds sock (sock',FIN,RST,stop') =
   (*:    [[ifds]] is just in case we need to send a RST, to make sure we don't
   send it to a broadcast address. :*)
   let continue = ~ stop' in
   let tcp_sock = tcp_sock_of sock in
    (continue = T /\
     let cb = tcp_sock.cb in
     choose ACK :: {T;F}.
     choose ack_lt_snd_una_or_snd_max_lt_ack :: {T;F}.
     if tcp_sock.st = SYN_RECEIVED /\
        ACK /\
        ack_lt_snd_una_or_snd_max_lt_ack
     then
         (*: break loop in "LAND" DoS attack, and also prevent ACK
            storm between two listening ports that have been sent
            forged SYN segments, each with the source address of
            the other. (|tcp_input.c:2141|) :*)
         sock' = sock /\
         FIN = F /\
         dropwithreset segRST (sock.is1,sock.is2) ifds RST
              (* ignore queue full error *)
     else
         (? sock1 msgFIN.  (* ignore errors *)
          let tcp_sock1 = tcp_sock_of sock1 in
          stream_tcp_output_really sock (sock1,msgFIN) /\  (*: did set [[tf_acknow]] and call [[tcp_output_perhaps]], which seemed a bit silly :*)
          (*: notice we here bake in the assumption that the timestamps use the same counter as the band limiter; perhaps this is unwise :*)
          ? outsegs' cb' es'.
          stream_rollback_tcp_output T (sock.is1,sock.is2) arch rttab ifds tcp_sock1.cb (cb',es',outsegs') /\
          sock' = sock1 with <| pr := TCP_PROTO(tcp_sock1 with <| cb := cb' |>) |> /\
          FIN = (if outsegs' then msgFIN else F) /\
          RST = F))
`;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_close]] TCP Close Functions

Closing a connection, updating the socket and TCP control block
appropriately.

     :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* Don't Phase: handled by testEval *)
val tcp_close_def = Define`
(*: close the socket and remove the TCPCB :*)
  tcp_close arch sock = sock with
    <| cantrcvmore := T; (* MF doesn't believe this is correct for Linux or WinXP *)
       cantsndmore := T;
       is1 := if bsd_arch arch then NONE else sock.is1;
       ps1 := if bsd_arch arch then NONE else sock.ps1;
       pr := TCP_PROTO(tcp_sock_of sock with
         <| st := CLOSED;
            cb := initial_cb |>)
     |>
`(*: @description
   This is similar to BSD's |tcp_close()|, except
   that we do not actually remove the protocol/control blocks. The quad of the socket is
   cleared, to enable another socket to bind to the port we were previously using --- this
   isn't actually done by BSD, but the effect is the same. The [[bsd_cantconnect]] flag is
   set to indicate that the socket is in such a detached state. :*)
;

(* Don't Phase: handled by testEval *)
val tcp_drop_and_close_def = Define`
(*: drop TCP connection, reporting the specified error.  If synchronised, send RST to peer :*)
  tcp_drop_and_close arch err sock (sock',(oflgs,odata:char list)) =
    let tcp_sock = tcp_sock_of sock in (
      (if tcp_sock.st NOTIN {CLOSED;LISTEN;SYN_SENT} then
         (oflgs = oflgs with <| SYN := F; SYNACK := F; FIN := F; RST := T |> /\
          odata IN UNIV)
       else
         (oflgs = oflgs with <| SYN := F; SYNACK := F; FIN := F; RST := F |> /\
          odata = [])) /\
    let es' =
      if err = SOME ETIMEDOUT then
       (if tcp_sock.cb.t_softerror <> NONE then
          tcp_sock.cb.t_softerror
        else
          SOME ETIMEDOUT)
      else if err <> NONE then err
      else sock.es
    in
      sock' = tcp_close arch (sock with <| es := es' |>))
`(*: @description
 BSD calls this |tcp_drop| :*)
;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[quad]] TCP Socket quad testing and extraction

Testing and extracting the quad of a connection from the socket.

:*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)


val _ = Define `
(*: test whether a socket quad is set :*)
    exists_quad_of (sock:TCP3_hostTypes$socket) =
        ? i1 p1 i2 p2. (SOME i1,SOME p1,SOME i2,SOME p2) = (sock.is1,sock.ps1,sock.is2,sock.ps2)
`;


val _ = Define `
(*: extract the quad from the socket :*)
    quad_of (sock:TCP3_hostTypes$socket) =
        (THE sock.is1,THE sock.ps1,THE sock.is2,THE sock.ps2)
`;


(* -------------------------------------------------- *)

val _ = export_theory();
