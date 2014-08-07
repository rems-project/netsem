(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Common Code UDP                           *)
(* Matthew Fairbairn - Created 20040114                                   *)
(* $Id: common_udp.mli,v 1.4 2004/04/01 16:41:44 mf266 Exp $                  *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread;;
open Unix;;
open ThreadUnix;;
open Printf;;

(* Our libraries *)
open Nettypes;;
open Netconv;;
open Ocamllib;;
open Tthee;;
open Ttheehelper;;
open Libcalls;;
open Testscommon;;
open Common;;
open Dual;;
open Dualdriven;;

type port_flavour =
    WILDCARD_PORT
  | ICMP_PORT
  | PRIVILEGED_PORT
  | UNAVAILABLE_PORT
  | AVAILABLE_PORT
  | KNOWN_PORT

type ip_flavour =
    BOGUS_IP
  | ICMP_IP
  | REMOTE_IP
  | WILDCARD_IP
  | LOCAL_IP

type sock_flavour_ip =
    SF_IP_UNSPEC
  | SF_IP_SPEC

type sock_flavour_port =
    SF_PORT_UNSPEC
  | SF_PORT_SPEC
  | SF_PORT_ERROR

type sock_flavour = sock_flavour_ip * sock_flavour_port * sock_flavour_ip * sock_flavour_port

val sf_UUUU : sock_flavour
val sf_UPUU : sock_flavour
val sf_IPUU : sock_flavour
val sf_IPIU : sock_flavour
val sf_IPIP : sock_flavour
val sf_UEUU : sock_flavour
val sf_IEUU : sock_flavour
val sf_IEIU : sock_flavour
val sf_IEIP : sock_flavour

val all_sock_flavours: (sock_flavour_ip * sock_flavour_port * sock_flavour_ip * sock_flavour_port) list

val all_address_flavours: ip_flavour list

val all_port_flavours: port_flavour list

val get_ip_udp: ip_flavour -> tthee_init_dual -> dual_test_state -> Ocamllib.ip option

val get_port_udp: port_flavour -> tthee_init_dual -> dual_test_state -> Ocamllib.port option

val string_of_bound_udp_quad : (sock_flavour_ip * sock_flavour_port * sock_flavour_ip * sock_flavour_port) -> string

val string_of_port_flavour : port_flavour -> string

val string_of_ip_flavour: ip_flavour -> string

val all_sf_af_pf : ((sock_flavour_ip * sock_flavour_port * sock_flavour_ip * sock_flavour_port) -> (ip_flavour -> (port_flavour -> 'a))) -> (sock_flavour_ip * sock_flavour_port * sock_flavour_ip * sock_flavour_port) list -> ip_flavour list -> port_flavour list -> 'a list

val get_real_port : tthee_init_dual -> dual_test_state -> (sock_flavour_ip * sock_flavour_port * sock_flavour_ip * sock_flavour_port) -> Nettypes.uint option

val get_foreign_ip : tthee_init_dual -> dual_test_state -> (sock_flavour_ip * sock_flavour_port * sock_flavour_ip * sock_flavour_port) -> Nettypes.ip option

val get_foreign_port : tthee_init_dual -> dual_test_state -> (sock_flavour_ip * sock_flavour_port * sock_flavour_ip * sock_flavour_port) -> Nettypes.uint option

val get_port_udp_inject : Ocamllib.port option -> Nettypes.port option
