open Printf;;

(* **************************************** *)
(* a nice type big enough to hold an uint32 *)
(* **************************************** *)

(* A hack.... hmmmm as we overload the floating *)
(* point infix operators *)
let float_add n m = n +. m;;
let float_div n m = n /. m;;
let float_mul n m = n *. m;;

type uint = int64
let uint_zero = Int64.of_int 0
let (|.) n m = Int64.logor n m
let (&.) n m = Int64.logand n m
let (&:) n m = Int64.logand n (Int64.of_int m)
let (<<) n m = Int64.shift_left n m
let (>>) n m = Int64.shift_right_logical n m
let (+.) n m = Int64.add n m
let (-.) n m = Int64.sub n m
let ( *. ) n m = Int64.mul n m
let (/.) n m = Int64.div n m
let (%) n m = Int64.rem n m
let (<.) n m = if(Int64.compare n m < 0) then true else false
let (>.) n m = if(Int64.compare n m > 0) then true else false
let (>=.) n m = if (Int64.compare n m >= 0) then true else false
let (<=.) n m = if (Int64.compare n m <= 0) then true else false
let (==.) n m = if (Int64.compare n m == 0) then true else false
let (!=.) n m = if (Int64.compare n m != 0) then true else false
let ch c = Int64.of_int (int_of_char c)
let uint n = Int64.of_int n
let int n = Int64.to_int n (* could do a range check here *)


(* ********************************************* *)
(* a nice type big enough to hold a signed int32 *)
(* ********************************************* *)

type sint = int32


(* **************************************)
(* types for things snarfed off the net *)
(* **************************************)

(*
Regarding all the numeric fields as uint, for simplicity - just want
to ensure (a) there's an injection from real IPv4 packets into these
types, and (b) there's enough structure to let us write
defragmentation etc easily.

For doing defrag, we obviously want just the IP bits split off.

We should really define OCaml well-formedness functions and the
inverse function (and that should be used by our raw socket output
code?)
*)

type word32 = uint
type word16 = uint
type byte = uint

type ip = word32
type port = word16

type ifid = string


(* recall that a wildcard (zero) IP/port maps to None *)
let ip_option_of_uint (n : uint) =
  if n = uint 0 then None else (Some n : ip option)
let port_option_of_uint (n : uint) =
  if n = uint 0 then None else (Some n : port option)

(* an option in an IP packet, uninterpreted *)
type ip_option = uint list

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

let ip_proto_tcp = uint 6
let ip_proto_icmp = uint 1
let ip_proto_udp = uint 17

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

let icmp_echo_reply = uint 0;;
let icmp_echo_request = uint 8;;
let icmp_destination_unreachable = uint 3;;
let icmp_time_exceeded = uint 11
let icmp_source_quench = uint 4
let icmp_parameter_problem = uint 12

let iCMP_UNREACH_NET = (uint 3, uint 0)
let iCMP_UNREACH_HOST = (uint 3, uint 1)
let iCMP_UNREACH_PROTOCOL = (uint 3, uint 2)
let iCMP_UNREACH_PORT = (uint 3, uint 3)
let iCMP_UNREACH_NEEDFRAG = (uint 3, uint 4)
let iCMP_UNREACH_SRCFAIL = (uint 3, uint 5)
let iCMP_UNREACH_NET_UNKNOWN = (uint 3, uint 6)
let iCMP_UNREACH_HOST_UNKNOWN = (uint 3, uint 7)
let iCMP_UNREACH_ISOLATED = (uint 3, uint 8)
let iCMP_UNREACH_NET_PROHIB = (uint 3, uint 9)
let iCMP_UNREACH_HOST_PROHIB = (uint 3, uint 10)
let iCMP_UNREACH_TOSNET = (uint 3, uint 11)
let iCMP_UNREACH_TOSHOST = (uint 3, uint 12)
let iCMP_UNREACH_FILTER_PROHIB = (uint 3, uint 13)
let iCMP_UNREACH_PREC_VIOLATION = (uint 3, uint 14)
let iCMP_UNREACH_PREC_CUTOFF = (uint 3, uint 15)
let iCMP_SOURCE_QUENCH = (uint 4, uint 0)
let iCMP_SOURCE_QUENCH_OTHER = (uint 4, uint 1)
let iCMP_REDIRECT_NET = (uint 5, uint 0)
let iCMP_REDIRECT_HOST = (uint 5, uint 1)
let iCMP_REDIRECT_TOSNET = (uint 5, uint 2)
let iCMP_REDIRECT_TOSHOST = (uint 5, uint 3)
let iCMP_REDIRECT_OTHER = (uint 5, uint 4)
let iCMP_TIME_EXCEEDED_INTRANS = (uint 11, uint 0)
let iCMP_TIME_EXCEEDED_REASS = (uint 11, uint 1)
let iCMP_TIME_EXCEEDED_OTHER = (uint 11, uint 2)
let iCMP_PARAMPROB_BADHDR = (uint 12, uint 0)
let iCMP_PARAMPROB_NEEDOPT = (uint 12, uint 1)
let iCMP_PARAMPROB_OTHER = (uint 12, uint 2)

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



let lpad_numeric_string s n =
  let len = String.length s in
  if(len < n) then
    let pad = String.make (n-len) '0' in
    pad^s
  else
    s;;

(* moved from render *)

exception Fatal of string

let render_ip (ipaddr: uint) =
  let a = Int64.to_string ((ipaddr >> 24) &: 0xff) in
  let b = Int64.to_string ((ipaddr >> 16) &: 0xff) in
  let c = Int64.to_string ((ipaddr >> 8) &: 0xff) in
  let d = Int64.to_string (ipaddr &: 0xff) in
  a^" "^b^" "^c^" "^d

let render_ip_dots (ipaddr: uint) =
  let a = Int64.to_string ((ipaddr >> 24) &: 0xff) in
  let b = Int64.to_string ((ipaddr >> 16) &: 0xff) in
  let c = Int64.to_string ((ipaddr >> 8) &: 0xff) in
  let d = Int64.to_string (ipaddr &: 0xff) in
  a^"."^b^"."^c^"."^d

let render_ip_option ips =
  match ips with
    None -> sprintf "NONE"
  | Some ipaddr -> sprintf "SOME(IP %s)" (render_ip ipaddr);;

let render_port_option pss =
  match pss with
    None -> sprintf "NONE"
  | Some ps -> sprintf "SOME(Port %s)" (Int64.to_string ps);;

let render_byte_option x =
  match x with
    None -> "NONE"
  | Some y -> sprintf "SOME(CHR %s)" (Int64.to_string y);;

let render_word16_option x =
  match x with
    None -> "NONE"
  | Some y -> sprintf "SOME(n2w %s)" (Int64.to_string y);;

let render_timestamp_option x =
  match x with
    None -> "NONE"
  | Some(a,b) -> sprintf "SOME(ts_seq (n2w %s), ts_seq (n2w %s))" (Int64.to_string a) (Int64.to_string b);;

let render_tcp_seq_local x =
  sprintf "tcp_seq_local(n2w %s)" (Int64.to_string x);;

let render_tcp_seq_foreign x =
  sprintf "tcp_seq_foreign(n2w %s)" (Int64.to_string x);;
