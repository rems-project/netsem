open Nettypes;;
open Netconv;;
open Net2hol;;
open Netipreass;;

(* tcp segments as used by our HOL model (isomorphic to the HOL record
type, perhaps modulo the word16-ness ).  We expect to have a
(slightly) lossy and partial map from tcp_packet into tcp_segment. *)

(* HOL-model TCP segment *)
type tcp_segment = {
    is1 : ip option ;
    is2 : ip option ;
    ps1 : port option;
    ps2 : port option;
    seq : word32;         (* sequence_number       *)
    ack : word32;         (* acknowledgment_number *)
    uRG : bool;
    aCK : bool;
    pSH : bool;
    rST : bool;
    sYN : bool;
    fIN : bool;
    win : word16;        (* window size *)
    urp : word16;

    (* and TCP options, which we pull out as follows.  We need to find
       out the correct names *)

    mss : word16 option;            (* maximum segment size TCPv2p865 *)
    scale : byte option;            (* window scaling; probably 0..14? *)
    ts :  (word32 * word32) option; (* _val and _ecr TCPv2p867: RFC1323, value and echo-reply *)

    data : byte list
}

val tcp_segment_of_tcp_packet: tcp_datagram -> tcp_segment

type protocol =
    PROTO_UDP
  | PROTO_TCP

type icmp_unreach_code =
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

type icmp_source_quench_code =
    QUENCH
  | SQ_OTHER of byte * word32

type icmp_redirect_code =
    RD_NET
  | RD_HOST
  | RD_TOSNET
  | RD_TOSHOST
  | RD_OTHER of byte * word32

type icmp_time_exceeded_code =
    INTRANS
  | REASS
  | TX_OTHER of byte * word32

type icmp_paramprob_code =
    BADHDR
  | NEEDOPT
  | PP_OTHER of byte * word32

type icmp_type =
    ICMP_UNREACH of icmp_unreach_code
  | ICMP_SOURCE_QUENCH of icmp_source_quench_code
  | ICMP_REDIRECT of icmp_redirect_code
  | ICMP_TIME_EXCEEDED of icmp_time_exceeded_code
  | ICMP_PARAMPROB of icmp_paramprob_code
  | ICMP_NONE

type icmp_message_hol = {
    icmp_hol_is1 : ip option;
    icmp_hol_is2 : ip option;
    icmp_hol_is3 : ip option;
    icmp_hol_is4 : ip option;
    icmp_hol_ps3 : port option;
    icmp_hol_ps4 : port option;
    icmp_hol_proto : protocol;
    icmp_hol_seq : word32 option;
    icmp_hol_type : icmp_type;
  }


type lh_dgram_render = SENDDGRAM | LOOPDGRAM | RECVDGRAM;;

val hol_icmp_of_icmp_datagram: icmp_datagram -> icmp_message_hol


val data_of_string: string -> byte list

type udp_datagram_hol = {
    udp_hol_is1 : ip option ;
    udp_hol_is2 : ip option ;
    udp_hol_ps1 : port option ;
    udp_hol_ps2 : port option ;
    udp_hol_data : byte list
  }

val hol_udp_of_udp_datagram: udp_datagram -> udp_datagram_hol

type holmsg =
    TCPMSG of tcp_segment
  | UDPMSG of udp_datagram_hol
  | ICMPMSG of icmp_message_hol;;
