open Nettypes;;
open Netconv;;
open Holtypes;;

val tcp_flatten: tcp_segment -> (uint * uint * uint list)

val icmp_flatten: icmp_message_hol -> (uint * uint * uint list)

val udp_flatten: udp_datagram_hol -> (uint * uint * uint list)

val ip_encapsulate: uint -> uint -> uint -> uint list -> uint list

val uint_list_to_string: uint list -> string
