open Unix;;
open Nettypes;;
open Netconv;;
open Holtypes;;

exception ParseWarning of string;;
exception ParseError of string;;

val assertw: bool -> string -> unit
val asserte: bool -> string -> unit

type icmp_partial =
    HOL_ICMP_IS1 of ip option
  | HOL_ICMP_IS2 of ip option
  | HOL_ICMP_IS3 of ip option
  | HOL_ICMP_IS4 of ip option
  | HOL_ICMP_PS3 of port option
  | HOL_ICMP_PS4 of port option
  | HOL_ICMP_PROTO of protocol
  | HOL_ICMP_SEQ of word32 option
  | HOL_ICMP_TYPE of icmp_type
;;

type icmp_status = {
    is1_up : bool;
    is2_up : bool;
    is3_up : bool;
    is4_up : bool;
    ps3_up : bool;
    ps4_up : bool;
    proto_up : bool;
    seq_up : bool;
    type_up : bool;
  } ;;

val clear_icmp_status: icmp_status

val chk_missing_icmp: icmp_status -> unit

val clear_icmp_hol: icmp_message_hol

val update_icmp: icmp_partial -> icmp_status -> icmp_message_hol ->
  (icmp_status * icmp_message_hol)

type tcp_partial =
    HOL_TCP_IS1 of ip option
  | HOL_TCP_IS2 of ip option
  | HOL_TCP_PS1 of port option
  | HOL_TCP_PS2 of port option
  | HOL_TCP_SEQ of word32
  | HOL_TCP_ACK of word32
  | HOL_TCP_URG of bool
  | HOL_TCP_ACKF of bool
  | HOL_TCP_PSH of bool
  | HOL_TCP_RST of bool
  | HOL_TCP_SYN of bool
  | HOL_TCP_FIN of bool
  | HOL_TCP_WIN of word16
  | HOL_TCP_URP of word16
  | HOL_TCP_MSS of word16 option
  | HOL_TCP_SCALE of byte option
  | HOL_TCP_TS of (word32 * word32) option
  | HOL_TCP_DATA of byte list;;

type tcp_status = {
    is1_tup : bool;
    is2_tup : bool;
    ps1_tup : bool;
    ps2_tup : bool;
    seq_tup : bool;
    ack_tup : bool;
    urg_tup : bool;
    ackf_tup : bool;
    psh_tup : bool;
    rst_tup : bool;
    syn_tup : bool;
    fin_tup : bool;
    win_tup : bool;
    urp_tup : bool;
    mss_tup : bool;
    scale_tup : bool;
    ts_tup : bool;
    data_tup : bool;
  } ;;

val clear_tcp_status: tcp_status

val chk_missing_tcp: tcp_status -> unit

val clear_tcp_hol: tcp_segment

val update_tcp: tcp_partial -> tcp_status -> tcp_segment ->
  (tcp_status * tcp_segment)


type udp_partial =
    HOL_UDP_IS1 of ip option
  | HOL_UDP_IS2 of ip option
  | HOL_UDP_PS1 of port option
  | HOL_UDP_PS2 of port option
  | HOL_UDP_DATA of byte list;;

type udp_status = {
    udp_is1_up : bool;
    udp_is2_up : bool;
    udp_ps1_up : bool;
    udp_ps2_up : bool;
    udp_data_up : bool;
  };;

val clear_udp_status: udp_status

val chk_missing_udp: udp_status -> unit

val clear_udp_hol: udp_datagram_hol

val update_udp: udp_partial -> udp_status -> udp_datagram_hol -> (udp_status * udp_datagram_hol)

(*val foldlist: ('a -> 'b -> ('a * 'b)) list -> 'a -> 'b -> 'a * 'b*)

