(* A HOL98 specification of TCP *)

(* Type definitions of the network and its components *)

(*[ RCSID "$Id: TCP1_netTypesScript.sml,v 1.45 2004/12/09 15:43:08 kw217 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

local open TCP1_baseTypesTheory
in end

local open arithmeticTheory stringTheory pred_setTheory bagTheory
           integerTheory finite_mapTheory realTheory in end;

val _ = new_theory "TCP1_netTypes";

val _ = Version.registerTheory "$RCSfile: TCP1_netTypesScript.sml,v $" "$Revision: 1.45 $" "$Date: 2004/12/09 15:43:08 $";

(*: @chapter [[TCP1_netTypes]] Network datagram types

This file defines the types of the datagrams that appear on the
network, with an IP message being either a TCP segment, a UDP
datagram, or an ICMP datagram.

These types abstract from most fields of the IP header: version, header
length, type of service, identification, DF, MF, and fragment offset,
time to live, header checksum, and IP options.
%
They faithfully model the IP header fields: protocol (TCP, UDP,
or ICMP), total length, source address, and destination address.
%
The [[tcpSegment]] type abstracts from the TCP checksum, reserved, and
padding fields of the TCP header, from the ordering of TCP options,
and from ill-formed TCP options.
It faithfully models all other fields.
%
The [[udpDatagram]] type abstracts from the UDP checksum but
faithfully models all other fields.
%
Lengths are represented by allowing simple lists of data bytes rather
than explicit length fields.
%
All these types collapse the encapsulation of TCP/UDP/ICMP within IP,
flattening them into single records, to reduce syntactic noise
throughout the specification.

For ease of comparison we reproduce the RFC 791/793/768 header formats below.

\begin{alltt}
\input{inetheaders.inc}
\end{alltt}


:*)


(* -------------------------------------------------- *)
(*                        TCP Level 2,3               *)
(* -------------------------------------------------- *)

(*: @section [[netty_tcp]] TCP TCP segments

TCP segments (really \emph{datagrams}, since we include the IP data)
are modelled as follows.

:*)

(* this is the spec's basic view of what appears on the wire.  In some
   places (host outqueues, network rules) we want to treat TCP
   segments and ICMP messages uniformly.  We do this by record overlay
   magic, making it appear as if all share some record accessors. *)

(* this is taken from slurp.ml 1.11, with type changes that should perhaps be reverse propagated *)

(* arith types need sorting out *)

(* really, of course, this is a type of TCP _datagrams_...*)


val _ = Hol_datatype
  `
(*: TCP datagram type :*)
tcpSegment
  = <| is1 : ip option ;      (* source IP *)
       is2 : ip option ;      (* destination IP *)
       ps1 : port option;     (* source port *)
       ps2 : port option;     (* destination port *)
       seq : tcp_seq_local;   (* sequence number       *)
       ack : tcp_seq_foreign; (* acknowledgment number *)
       URG : bool;
       ACK : bool;
       PSH : bool;
       RST : bool;
       SYN : bool;
       FIN : bool;
       win : word16;        (* window size (unsigned) *)
       ws  : byte option;   (* TCP option: window scaling; typically 0..14 *)
       urp : word16;        (* urgent pointer (unsigned) *)
       mss : word16 option;             (* TCP option: maximum segment size (unsigned) *)
       ts  : (ts_seq # ts_seq) option;  (* TCP option: RFC1323 timestamp value and echo-reply *)
       data : byte list
    |>
`

(*: @description
The use of "local" and "foreign" here is with respect to the \emph{sending} TCP.

:*)

;

(* we say this in the TR, so not repeating it here (?)

consider handling TCP options differently: store just the
          raw bytes here, and interpret them with a function.  That
          function would be like |tcp_dooptions|, reading the options
          into a record of options like the tail of the above.  The
          difference is that the rules for doing this would be in the
          HOL model, rather than prior to it.
*)



(* For the mss field cf TCPv2p865.  For the _val and _ecr fields cf TCPv2p867. *)


val sane_seg_def = Phase.phase 1 Define`
(*:
segment well-formedness test (physical constraints imposed by format)
:*)
  sane_seg seg <=> LENGTH seg.data < (65536 - 40)
`
;

(*: @section [[netty_udp]] UDP UDP datagrams

UDP datagrams are very simple.  They are modelled as follows.

:*)

val _ = Hol_datatype  `
  (*: UDP datagram type :*)
udpDatagram
  = <| is1 : ip option ;      (* source IP *)
       is2 : ip option ;      (* destination IP *)
       ps1 : port option;     (* source port *)
       ps2 : port option;     (* destination port *)
       data : byte list
    |>
`;

val sane_udpdgm_def = Phase.phase 1 Define`
(*:
message well-formedness test (physical constraints imposed by format)
:*)
  sane_udpdgm dgm <=> LENGTH dgm.data < (65536-20-8)
`
;



(*: @section [[netty_icmp]] ALL ICMP datagrams

ICMP messages have \emph{type} and \emph{code} fields, both 8 bits wide.
The specification deals only with some of these types, as
characterised in the HOL type [[icmpType]] below.  For each type we
identify some or all of the codes that have conventional symbolic
representations, but to ensure the model can faithfully represent
arbitrary codes each code (HOL type) also has an [[OTHER]] constructor
carrying a byte.  The values carried are assumed not to overlap with
the symbolically-represented values.

In retrospect, there seems to be no reason not to have types
and codes simply particular byte constants.

:*)


val _ = Hol_datatype
  `
(*:
protocol type for use in ICMP messages
:*)
protocol = PROTO_TCP | PROTO_UDP`
;


(* we believe our semantics does the right thing for all type-3 ICMPs (destination unreachable), hence we list them all here *)
val _ = Hol_datatype
  `icmp_unreach_code =
    NET
  | HOST
  | PROTOCOL
  | PORT
  | SRCFAIL
  | NEEDFRAG of word16 option
  | NET_UNKNOWN
  | HOST_UNKNOWN
  | ISOLATED
  | NET_PROHIB
  | HOST_PROHIB
  | TOSNET
  | TOSHOST
  | FILTER_PROHIB
  | PREC_VIOLATION
  | PREC_CUTOFF
  | OTHER of byte # word32  (* really want this not to overlap *)
`;
(* BSD drops ICMPs on the floor if their code is unrecognised, even if the type *is* recognised. *)

val _ = Hol_datatype
  `icmp_source_quench_code =
    QUENCH
  | SQ_OTHER of byte # word32 (*: writen [[OTHER]] :*)
`;
val _ = overload_on("OTHER", ``SQ_OTHER``);

val _ = Hol_datatype
  `icmp_redirect_code =
    RD_NET                     (*: written [[NET]] :*)
  | RD_HOST                    (*: written [[HOST]] :*)
  | RD_TOSNET                  (*: written [[TOSNET]] :*)
  | RD_TOSHOST                 (*: written [[TOSHOST]] :*)
  | RD_OTHER of byte # word32  (*: written [[OTHER]] :*)
`;
val _ = overload_on("NET",     ``RD_NET``);
val _ = overload_on("HOST",    ``RD_HOST``);
val _ = overload_on("TOSNET",  ``RD_TOSNET``);
val _ = overload_on("TOSHOST", ``RD_TOSHOST``);
val _ = overload_on("OTHER",   ``RD_OTHER``);

val _ = Hol_datatype
  `icmp_time_exceeded_code =
    INTRANS
  | REASS
  | TX_OTHER of byte # word32  (*: written [[OTHER]] :*)
`;
val _ = overload_on("OTHER", ``TX_OTHER``);

val _ = Hol_datatype
  `icmp_paramprob_code =
    BADHDR
  | NEEDOPT
  | PP_OTHER of byte # word32  (*: written [[OTHER]] :*)
`;
val _ = overload_on("OTHER", ``PP_OTHER``);


(* we list here only those ICMPs we handle.  The rest we explicitly do not specify in this semantics. *)
val _ = Hol_datatype
  `icmpType =
    ICMP_UNREACH       of icmp_unreach_code
  | ICMP_SOURCE_QUENCH of icmp_source_quench_code
  | ICMP_REDIRECT      of icmp_redirect_code
  | ICMP_TIME_EXCEEDED of icmp_time_exceeded_code
  | ICMP_PARAMPROB     of icmp_paramprob_code
  (* FreeBSD 4.6-RELEASE also does: ICMP_ECHO, ICMP_TSTMP, ICMP_MASKREQ *)
`;


val _  = Hol_datatype `
(*: ICMP datagram type :*)
  icmpDatagram
  = <| is1 : ip option ;     (* this is the sender of this ICMP *)
       is2 : ip option ;     (* this is the intended receiver of this ICMP *)

       (* we assume the enclosed IP always has at least 8 bytes of data, i.e., enough
          for all the fields below *)
       is3 : ip option ;     (* source of enclosed IP datagram *)
       is4 : ip option ;     (* destination of enclosed IP datagram *)
       ps3 : port option;    (* source port *)
       ps4 : port option;    (* destination port *)
       proto : protocol;     (* protocol *)
       seq : tcp_seq_local option;  (* seq *)
       t   : icmpType
    |>
`;

(* The above used to say: we assume the enclosed IP has proto=TCP; if
not, it's beyond the scope of this spec. But that now appears
outdated. *)


(*: @section [[netty_ip]] ALL IP messages

  An IP datagram is (for our purposes) either a TCP segment, an ICMP
  datagram, or a UDP datagram.  We use the type [[msg]] for IP
  datagrams.  IP datagrams may be checked for sanity, and may have
  their [[is1]] and [[is2]] fields inspected.

:*)

val _ = Hol_datatype `
(*: IP message type :*)
  msg = TCP of tcpSegment | ICMP of icmpDatagram | UDP of udpDatagram`;

val sane_msg_def = Phase.phase 1 Define`
(*: message well-formedness test (physical constraints imposed by format) :*)
  sane_msg (TCP seg) = sane_seg seg /\
  sane_msg (ICMP dgm) = T /\
  sane_msg (UDP dgm') = sane_udpdgm dgm'
`;

val msg_is1_def = Phase.phase 1 Define`
  (*: source IP of a message, written [[x.is1]] :*)
  msg_is1 (TCP seg)  = seg.is1 /\
  msg_is1 (ICMP dgm) = dgm.is1 /\
  msg_is1 (UDP dgm') = dgm'.is1
` (*: @mergewithnext :*);
val msg_is2_def = Phase.phase 1 Define`
  (*: destination IP of a message, written [[x.is2]] :*)
  msg_is2 (TCP seg)  = seg.is2 /\
  msg_is2 (ICMP dgm) = dgm.is2 /\
  msg_is2 (UDP dgm') = dgm'.is2
`;
val _ = Parse.add_record_field("is1",``msg_is1``);  (* overload x.is1 *)
val _ = Parse.add_record_field("is2",``msg_is2``);  (* overload x.is2 *)


(* -------------------------------------------------- *)

val _ = export_theory();
