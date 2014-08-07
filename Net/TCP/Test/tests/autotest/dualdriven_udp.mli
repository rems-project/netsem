(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Dualdriven Code UDP                       *)
(* Matthew Fairbairn - Created 20040114                                   *)
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
open Common_udp;;

exception Drive_Failure of string

val get_bound_state_udp: libd_handle -> fd -> unit

val get_socket_udp: libd_handle -> fd

val get_local_bound_socket_udp: libd_handle -> Ocamllib.ip option -> port option -> fd

val get_autobound_connected_socket_udp: libd_handle -> Ocamllib.ip -> port -> fd

val get_local_bound_connected_socket_udp: libd_handle -> Ocamllib.ip option -> port option -> Ocamllib.ip -> port -> fd

val bound_udp_quads: (sock_flavour * string) list

val rst_udp_socket: tthee_init_dual -> dual_test_state -> fd -> unit

val exhaust_proc_fds_udp: dual_test_state -> tthee_init_dual -> unit

val exhaust_sys_fds_udp: dual_test_state -> tthee_init_dual -> (log_handle * libd_handle) list

val get_bound_socket_udp: tthee_init_dual -> dual_test_state -> sock_flavour -> fd

val get_bound_socket_reuse_udp: tthee_init_dual -> dual_test_state -> sock_flavour -> fd
