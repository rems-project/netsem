open Tthee;;
open Nettypes;;
open Netconv;;

type ip = (int*int*int*int);;

(* IP address constructors *)
let hol_ip (a,b,c,d) =
  ((((((Int64.of_int a) << 8) |. (Int64.of_int b)) << 8)
  |. (Int64.of_int c)) << 8) |. (Int64.of_int d);;

let string_ip (a,b,c,d) =
  (string_of_int a)^"."^(string_of_int b)^"."^
  (string_of_int c)^"."^(string_of_int d);;

(* Command socket helpers *)
let cmd_tcp_create (a,b,c,d) p =
  TCP(ip_of_ints a b c d, port_of_int p);;

(* Slurper helpers *)
(* create_filter hostip1 hostip2 = string *)
let create_filter ip1 ip2 =
  let ip1,ip2 = string_ip ip1, string_ip ip2 in
  Some("(tcp or icmp or udp) and (((ip src "^ip1^" and ip dst "^ip2^") or (ip src "^ip2^" and ip dst "^ip1^")))");;

(* create_virutal filter hostip1 hostip2 virtualip = string *)
let create_virtual_filter ip1 ip2 ipv ipb ipm ipu =
  let ip1,ip2,ipv = string_ip ip1, string_ip ip2, string_ip ipv in
  let ipb, ipm, ipu = string_ip ipb, string_ip ipm, string_ip ipu in
  Some("(tcp or udp or icmp) and ((ip src "^ip1^" and ip dst "^ip2^") or (ip src "^ip2^" and ip dst "^ip1^") or (ip src "^ip1^" and ip dst "^ipv^") or (ip src "^ipv^" and ip dst "^ip1^") or (ip src "^ipb^" and ip dst "^ip1^") or (ip src "^ipm^" and ip dst "^ip1^") or (ip src "^ip1^" and ip dst "^ipb^") or (ip src "^ip1^" and ip dst "^ipm^") or (ip dst "^ipu^") or (ip src "^ipu^") or (ip src "^ip1^" and ip dst "^ip1^") or (ip src "^ip2^" and ip dst "^ip2^"))");;
