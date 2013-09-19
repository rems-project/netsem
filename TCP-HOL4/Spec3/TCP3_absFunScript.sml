(* standard prefix *)
open HolKernel boolLib Parse

open bossLib containerTheory

open HolDoc

local open (* TCP1_net1_to_netTheory *)
	       TCP1_netTheory
	   TCP3_netTheory
           fmapUtilsTheory
in end;

val Term = Parse.Term;

val _ = new_theory "TCP3_absFun";

val _ = Version.registerTheory "$RCSfile: TCP3_absFunScript.sml,v $" "$Revision: 1.34 $" "$Date: 2009/02/17 12:56:26 $";


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[absFun]] Abstraction function

This file defines the abstraction function, from protocol-level network states (and transition
labels) to service-level network states (and transition labels).

:*)

(*: @section [[absFun_aux]] ALL Auxiliary functions

Basic abstraction functions for basic TCP host types.

:*)

val tcpcb1_to_3_def = Define `
     (*: abstract a [[tcpcb]] :*)
     (tcpcb1_to_3:TCP1_hostTypes$tcpcb->TCP3_hostTypes$tcpcb) cb = (
         <|  tt_keep := cb.tt_keep;
             t_softerror := cb.t_softerror
         |>)
`;

val tcp_socket1_to_3_def = Define `
     (*: abstract a [[tcp_socket]] :*)
     (tcp_socket1_to_3:TCP1_hostTypes$tcp_socket->TCP3_hostTypes$tcp_socket) s = (
         <|  st := s.st;
             cb := tcpcb1_to_3 s.cb;
             lis := s.lis
         |>)
`;

val socket1_to_3_def = Define `
     (*: abstraction a [[socket]] :*)
     (socket1_to_3:TCP1_hostTypes$socket->TCP3_hostTypes$socket) s = (
         <|  fid := s.fid;
             sf := s.sf;
             is1 := s.is1;
             ps1 := s.ps1;
             is2 := s.is2;
             ps2 := s.ps2;
             es := s.es;
             cantsndmore := s.cantsndmore;
             cantrcvmore := s.cantrcvmore;
             pr := (case s.pr of TCP_PROTO tcp_sock -> TCP_PROTO (tcp_socket1_to_3 tcp_sock)
              ||  UDP_PROTO udp_sock -> UDP_PROTO udp_sock)
         |>)
`;

val host1_to_3_def = Define `
     (*: abstract a [[host]] :*)
     (host1_to_3:TCP1_hostTypes$host->TCP3_hostTypes$host) h = (
         let filter_non_TCP_msgs =
           \ q. case q of Timed(msgs,d) -> Timed(FILTER (\ msg. case msg of TCP _1 -> F || _2 -> T) msgs,d)
         in
         <|  arch := h.arch;
             privs := h.privs;
             ifds := h.ifds;
             rttab := h.rttab;
             ts := h.ts;
             files := h.files;
             socks := socket1_to_3 o_f h.socks;
             listen := h.listen;
             bound := h.bound;
             iq := filter_non_TCP_msgs h.iq;
             oq := filter_non_TCP_msgs h.oq;
             bndlm := h.bndlm;
             ticks := h.ticks;
             fds := h.fds;
             params := h.params
         |>)
`;



(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[absFun_aux]] ALL Stream reassembly

For the case where the sender is absent, we have to recover the stream contents from segments on
the wire, using a stream reassembly function.

:*)

(* reassemble function, after TCP1_auxFnsTheory.tcp_reass *)
val stream_reass_def = Define `
    (*: reassemble the stream from segments on the wire :*)
    stream_reass (seq:tcpLocal seq32) (segs: tcpSegment set) = (
    (* REMARK first arg should be  word32 *)
        let myrel = { (i,c) |
                ? seg. seg IN segs /\
                Num (i - seg.seq) < LENGTH seg.data /\
                c = EL (Num (i - seg.seq)) seg.data } in
        let cs = { (cs:byte list) |
                (! n:num. n < LENGTH cs ==> myrel (seq + n, EL n cs)) /\
                (~?c. (seq+(LENGTH cs),c) IN myrel) } in
        CHOICE cs)

`
(*: @description

This stream reassembly function is closely based on that defined in the protocol-level specification.

:*)
;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[absFun_aux]] ALL Abstraction function

The full abstraction function builds on a unidirectional version. Both are presented in this section.

:*)


val ERROR_def = Define `
    (*: a simple way to indicate that an error has occurred :*)
    ERROR (a:'a) = (ARB:'b)
`;

val abs_hosts_one_sided_def = Define `
    (*: unidirectional abstraction function :*)
    abs_hosts_one_sided (i1,p1,i2,p2) (h,msgs,i) = (

        (*: get the messages that we are interested in, including those in [[oq]] and [[iq]] :*)
        let (hoq,iiq) =
            case (h.oq,i.iq) of (Timed (omsgs,_1), Timed (imsgs,_2)) -> (omsgs,imsgs) in
        let msgs = LIST_TO_SET hoq UNION msgs UNION (LIST_TO_SET iiq) in
        (*: only consider TCP messages \ldots :*)
        let msgs = {msg | TCP msg IN msgs} in
        (*: \ldots that match the quad :*)
        let msgs = msgs INTER
            {msg | msg = msg with <| is1 := SOME i1; ps1 := SOME p1; is2 := SOME i2; ps2 := SOME p2 |> } in

        (*: pick out the send and receive sockets :*)
        let smatch i1 p1 i2 p2 s = ((s.is1,s.ps1,s.is2,s.ps2) = (SOME i1,SOME p1,SOME i2,SOME p2)) in
        let snd_sock = Punique_range (smatch i1 p1 i2 p2) h.socks in
        let rcv_sock = Punique_range (smatch i2 p2 i1 p1) i.socks in

        let tcpsock_of sock = case sock.pr of
            TCP1_hostTypes$TCP_PROTO tcpsock -> tcpsock
         || _3 -> ERROR "abs_hosts_one_sided:tcpsock_of"
        in

        (*: the difficult part of the abstraction function is to compute [[data]] :*)
        let (data:byte list) = case (snd_sock,rcv_sock) of
            (SOME (_8,hsock),SOME(_9,isock)) -> (
                let htcpsock = tcpsock_of hsock in
                let itcpsock = tcpsock_of isock in
                let (snd_una, sndq) = (htcpsock.cb.snd_una, htcpsock.sndq) in
                let (rcv_nxt, rcvq) = (itcpsock.cb.rcv_nxt, itcpsock.rcvq) in
                let rcv_nxt = tcp_seq_flip_sense rcv_nxt in
                let sndq' = DROP ((Num (rcv_nxt - snd_una))) sndq in
                rcvq ++ sndq')

         || (SOME (_8,hsock),NONE) -> (
                let htcpsock = tcpsock_of hsock in
                htcpsock.sndq)

         || (NONE,SOME(_9,isock)) -> (
                let itcpsock = tcpsock_of isock in
                let (rcv_nxt:tcpLocal seq32,rcvq:byte list) =
                    (tcp_seq_flip_sense (itcpsock.cb.rcv_nxt),itcpsock.rcvq) in
                rcvq ++ (stream_reass rcv_nxt msgs))

         || (NONE,NONE) -> ERROR "abs_hosts_one_sided:data"
        in
        <|  i := i1;
            p := p1;
            flgs :=
            <|  SYN    := (? msg. msg IN msgs /\ msg = msg with <| SYN := T; ACK := F|>);
                SYNACK := (? msg. msg IN msgs /\ msg = msg with <| SYN := T; ACK := T|>);
                FIN    := (? msg. msg IN msgs /\ msg = msg with <| FIN := T|>);
                RST    := (? msg. msg IN msgs /\ msg = msg with <| RST := T|>)
            |>;
            data := data;
            destroyed := (case snd_sock of
                SOME (sid,hsock) -> ((tcpsock_of hsock).st = CLOSED)
             || NONE -> T)
        |>)
`
(*: @description

The core of the abstraction function is to compute the [[data]] in the stream, given the connection
endpoints and the segments on the wire.

Normally the sender and receiver endpoints are both active. In this case, the sender [[sndq]] and
the receiver [[rcvq]] contain bytes corresponding to sequence number intervals. These intervals
overlap, so to recover the data in the stream, we must drop some data from the [[sndq]]. We drop
[[rcv_nxt - snd_una]] bytes and then append the resulting [[sndq']] to [[rcvq]] to form the contents
of the stream.

The other cases are handled in a similar way. If the receiver endpoint is absent, the data is just
that data in the sender's [[sndq]]. If the sender endpoint is absent, the data is reassembled from
segments on the wire, using [[stream_reass]].

The [[flgs]] are calculated based on the flags set in segments on the wire. In fact, this should
also take into account segment validity, but currently this is not handled correctly at the
protocol-level, and we want to maintain the invariant that every protocol-level trace maps to a
service-level trace.

The destroyed flag is true iff the socket is [[CLOSED]] or no longer exists.

:*)
;

val abs_hosts = Define `
    (*: the full abstraction function for host states :*)
    abs_hosts (i1,p1,i2,p2) (h1,msgs,h2) = (
        let n1 = host1_to_3 h1 in
        let n2 = host1_to_3 h2 in
        let (streams:tcpStreams option) =
            let s12 = abs_hosts_one_sided (i1,p1,i2,p2) (h1,msgs,h2) in
            let s21 = abs_hosts_one_sided (i2,p2,i1,p1) (h2,msgs,h1) in
            (case s12.destroyed /\ s21.destroyed of
                T -> NONE
             || F -> SOME <| streams := {s12;s21} |>)
        in
        (n1,streams,n2))
`
(*: @description

The abstraction function maps protocol-level host states and segments on the wire to service-level
host states and streams. It uses the unidirectional abstraction function [[abs_hosts_one_sided]]
twice to form streams [[s12]] and [[s21]]. If these streams are both destroyed, then the resulting
[[streams]] (an option) is [[NONE]], otherwise it is a pair of the unidirectional streams.

:*)
;

val abs_lbl_def = Define `
    (*: abstract transition labels :*)
    abs_lbl lbl = (case lbl of
        Ln0_call (hid, tid, lib) -> Ln_call (hid, tid, lib)
     || Ln0_return (hid, tid, tlang) -> Ln_return (hid,tid,tlang)
     || Ln0_interface (hid,ifid,up) -> ERROR "absfn: Ln0_interface"
     || Ln0_tau -> Ln_tau
     || Ln0_epsilon dur -> Ln_epsilon dur
     || Ln0_trace tr -> Ln_tau)

`
(*: @description

The abstraction function must also map protocol-level transition labels to service-level transition
labels. This is a straightforward bijection. Interface changes are not currently handled at the
service level.

:*)
;

val abs_trans_def = Define `
    (*: abstract a full protocol-level network transition :*)
    abs_trans (i1,p1,i2,p2) (h1,msgs,h2) lbl (h1',msgs',h2') = (
        let n = abs_hosts (i1,p1,i2,p2) (h1,msgs,h2) in
        let n' = abs_hosts (i1,p1,i2,p2) (h1',msgs',h2') in
        let nlbl = abs_lbl lbl in
        (n,nlbl,n'))
`
(*: @description

The [[abs_trans]] function ties together the previous host and label abstraction functions to
produce a service-level transition from a protocol-level transition.

:*)
;

(* ******************************************************************************** *)

val _ = export_theory ();

(* Local Variables: *)
(* fill-column: 100 *)
(* End: *)


