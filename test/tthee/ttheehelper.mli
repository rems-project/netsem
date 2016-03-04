open Tthee;;
open Nettypes;;

type ip = (int*int*int*int);;

(* IP address constructors *)
val string_ip: ip -> string;;
val hol_ip: ip -> uint;;

(* Command socket helpers *)
val cmd_tcp_create: ip -> int -> Tthee.sock_type;;

(* Slurper helpers *)
(* create_filter hostip1 hostip2 = string *)
val create_filter: ip -> ip -> string option;;

(* create_virutal filter hostip1 hostip2 virtualip broadcast_ip multicast_ip unused_ip = string *)
val create_virtual_filter: ip -> ip -> ip -> ip -> ip -> ip -> string option;;
