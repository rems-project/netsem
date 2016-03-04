open Nettypes;;
open Holtypes;;
open Unix;;

(* FIXME remove funs without no_semicolon, i.e. those that print a semicolon *)

(* used in render_tcp|udp|icmp_to_socket, which are now in slurp *)
val check_host_ip: ip option -> string -> bool

val render_tcp_inner: (*file_descr ->*) tcp_segment -> lh_dgram_render -> string

val render_tcp_inner_no_semicolon: (*file_descr ->*) tcp_segment -> lh_dgram_render -> string

val render_icmp_inner: (*file_descr ->*) icmp_message_hol -> lh_dgram_render -> string

val render_icmp_inner_no_semicolon: (*file_descr ->*) icmp_message_hol -> lh_dgram_render -> string

val render_udp_inner: (*file_descr ->*) udp_datagram_hol -> lh_dgram_render -> string

val render_udp_inner_no_semicolon: (*file_descr ->*) udp_datagram_hol -> lh_dgram_render -> string







(* The below are used in frender. This minor ugliness will no longer be
   necessary when (if) we rewrite the rendering code to remove the awful
   pass-a-socket idiom. *)

(*
val is_loopback_tcp: tcp_segment -> bool
val is_loopback_icmp: icmp_message_hol -> bool
val is_loopback_udp: udp_datagram_hol -> bool

val render_data: byte list -> string
val render_datastr: byte list -> string
val render_icmp_proto: protocol -> string
val render_icmp_type: icmp_type -> string
val render_bool: bool -> string
*)

(*val render_tcp_to_socket: file_descr -> tcp_segment -> timestamp -> string option -> iface -> unit*)
(*val render_icmp_to_socket: file_descr -> icmp_message_hol -> timestamp -> string option -> iface -> unit*)
(*val render_udp_to_socket: file_descr -> udp_datagram_hol -> timestamp -> string option -> iface -> unit*)

