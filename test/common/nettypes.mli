type uint = int64
type sint = int32
type word32 = uint
type word16 = uint
type byte = uint
type ip = word32
type port = word16
type ip_option = uint list
type ifid = string

val float_add : float -> float -> float;;
val float_div : float -> float -> float;;
val float_mul : float -> float -> float;;

(* Ethernet header TCPv1; see RFC894 for IP-in-Ethernet encapsulation *)
type eth_header = {
    eth_dst  : uint;
    eth_src  : uint;
    eth_type : uint;
  }


(* IP header (lossless representation) *)
type ip_header = {
    ip_v    : uint ;
    ip_hl   : uint ;
    ip_tos  : uint ;
    ip_len  : uint ;
    ip_id   : uint ;
    ip_zf   : bool        ;
    ip_df   : bool        ;
    ip_mf   : bool        ;
    ip_off  : uint ;
    ip_ttl  : uint ;
    ip_p    : uint ;
    ip_sum  : uint ;
    ip_src  : uint ;
    ip_dst  : uint ;
    ip_opts : ip_option list ;
  }

(* IP packet or datagram (lossless representation) *)
type ip_packet = {
    ip_h : ip_header ;
    ip_data : char list ;  (* length not necessarily checked! *)
  }

(* an option in a TCP datagram, maybe interpreted *)
type tcp_option = TCPOPT_EOL
                | TCPOPT_NOP
                | TCPOPT_MAXSEG of uint                (* 16 bits *)
                | TCPOPT_WINDOW of uint                (* 8 bits, 0..14 *)
                | TCPOPT_TIMESTAMP of uint * uint      (* ts_val, ts_ecr *)
                | TCPOPT_unknown of uint * uint list   (* uninterp: num, args (len not stored) *)
                | TCPOPT_tail of uint list             (* filler *)

(* TCP header (lossless representation) *)
type tcp_header = {
   tcp_sport : uint ;
   tcp_dport : uint ;
   tcp_seq   : uint ;
   tcp_ack   : uint ;
   tcp_off   : uint ;
   tcp_x2    : uint ;
   tcp_URG   : bool ;
   tcp_ACK   : bool ;
   tcp_PSH   : bool ;
   tcp_RST   : bool ;
   tcp_SYN   : bool ;
   tcp_FIN   : bool ;
   tcp_win   : uint ;
   tcp_sum   : uint ;
   tcp_urp   : uint ;
   tcp_opts  : tcp_option list ;
  }

(* TCP datagram (lossless representation) *)
type tcp_datagram = {
    tcp_iph  : ip_header ;
    tcp_h    : tcp_header ;
    tcp_data : byte list ;
  }

val iCMP_UNREACH_NET : uint * uint
val iCMP_UNREACH_HOST : uint * uint
val iCMP_UNREACH_PROTOCOL : uint * uint
val iCMP_UNREACH_PORT : uint * uint
val iCMP_UNREACH_NEEDFRAG : uint * uint
val iCMP_UNREACH_SRCFAIL : uint * uint
val iCMP_UNREACH_NET_UNKNOWN : uint * uint
val iCMP_UNREACH_HOST_UNKNOWN : uint * uint
val iCMP_UNREACH_ISOLATED : uint * uint
val iCMP_UNREACH_NET_PROHIB : uint * uint
val iCMP_UNREACH_HOST_PROHIB : uint * uint
val iCMP_UNREACH_TOSNET : uint * uint
val iCMP_UNREACH_TOSHOST : uint * uint
val iCMP_UNREACH_FILTER_PROHIB : uint * uint
val iCMP_UNREACH_PREC_VIOLATION : uint * uint
val iCMP_UNREACH_PREC_CUTOFF : uint * uint
val iCMP_SOURCE_QUENCH : uint * uint
val iCMP_SOURCE_QUENCH_OTHER : uint * uint
val iCMP_TIME_EXCEEDED_INTRANS : uint * uint
val iCMP_TIME_EXCEEDED_REASS : uint * uint
val iCMP_TIME_EXCEEDED_OTHER : uint * uint
val iCMP_PARAMPROB_BADHDR : uint * uint
val iCMP_PARAMPROB_NEEDOPT : uint * uint
val iCMP_PARAMPROB_OTHER : uint * uint
val iCMP_REDIRECT_NET : uint * uint
val iCMP_REDIRECT_HOST : uint * uint
val iCMP_REDIRECT_TOSNET : uint * uint
val iCMP_REDIRECT_TOSHOST : uint * uint
val iCMP_REDIRECT_OTHER : uint * uint

type icmp_body_type =
    ICMP_ERROR of uint * uint * word16 option * ip_header * port * port
  | ICMP_QUERY of char list
  | ICMP_ECHO_REQUEST of uint * uint * char list
  | ICMP_ECHO_REPLY of uint * uint * char list;;


type icmp_message = {
    icmp_type   : uint ;
    icmp_code   : uint ;
    icmp_sum    : uint ;
    icmp_body   : icmp_body_type;
  }

type icmp_datagram = {
    icmp_iph : ip_header ;
    icmp_msg : icmp_message ;
  }

type timestamp = {
    t_sec  : uint ;
    t_usec : uint ;
  }


type iface = LOOPIFACE_LINUX | LOOPIFACE_BSD | LOOPIFACE_WIN | OTHERIFACE;;


type sock_type = SOCK_STREAM | SOCK_DGRAM;;

type udp_header = {
    udp_sport : uint ;
    udp_dport : uint ;
    udp_len   : uint ;
    udp_sum   : uint ;
  }

type udp_datagram = {
    udp_iph  : ip_header ;
    udp_h    : udp_header ;
    udp_data : byte list ;
  }

val uint_zero: uint
val (|.) : uint -> uint -> uint
val (&.) : uint -> uint -> uint
val (&:) : uint -> int -> uint
val (<<) : uint -> int -> uint
val (>>) : uint -> int -> uint
val (<.) : uint -> uint -> bool
val (>.) : uint -> uint -> bool
val (<=.) : uint -> uint -> bool
val (>=.) : uint -> uint -> bool
val (==.) : uint -> uint -> bool
val (!=.) : uint -> uint -> bool
val (+.) : uint -> uint -> uint
val (-.) : uint -> uint -> uint
val ( *. ) : uint -> uint -> uint
val (/.): uint -> uint -> uint
val (%): uint -> uint -> uint
val ch : char -> uint
val uint : int -> uint
val int : uint -> int

val ip_option_of_uint: uint -> ip option
val port_option_of_uint: uint -> port option
val ip_proto_tcp: uint
val ip_proto_icmp: uint
val ip_proto_udp: uint

val icmp_echo_reply: uint
val icmp_echo_request: uint
val icmp_destination_unreachable: uint
val icmp_time_exceeded : uint
val icmp_source_quench : uint
val icmp_parameter_problem : uint

val lpad_numeric_string : string -> int -> string;;

(* moved from render *)

exception Fatal of string

val render_ip: uint -> string

val render_ip_dots: uint -> string

val render_ip_option: ip option -> string

val render_port_option: port option -> string

val render_byte_option: byte option -> string

val render_word16_option: word16 option -> string

val render_timestamp_option: (uint * uint) option -> string

val render_tcp_seq_local: uint -> string

val render_tcp_seq_foreign: uint -> string
