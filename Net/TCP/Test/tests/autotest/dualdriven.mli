(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Dual Tests TCP State Driver Code                *)
(* Steve Bishop - Created 20030505                                        *)
(* $Id: dualdriven.mli,v 1.8 2004/09/07 11:25:36 mjas2 Exp $                  *)
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

exception Drive_Failure of string;;

(* Get a socket's bound state *)
val get_bound_state: libd_handle -> fd -> unit

(* Get new socket on host *)
val get_socket: libd_handle -> fd

(* Get new bound socket on host *)
val get_local_bound_socket:
    libd_handle -> Ocamllib.ip option -> port option -> fd

(* Get an autobound, connected socket on host *)
val get_autobound_connected_socket:
    libd_handle -> Ocamllib.ip -> port -> fd

(* Get a non-auto bound, connected socket on host *)
val get_local_bound_connected_socket:
    libd_handle -> Ocamllib.ip option -> port option -> Ocamllib.ip -> port -> fd

(* ---------------------------------------------------------------------- *)
(* Create socket and drive to a TCP state transition diagram style state  *)
(* ---------------------------------------------------------------------- *)

(* The state of a TCP connection wrt whether it has sent *)
(* or received data or not *)
type tcp_data_status =
    NO_DATA
  | DATA_SENT
  | DATA_RCVD
  | DATA_SENT_RCVD;;

(* The last datagram seen on the wire (and whether it was sent or *)
(* received by the test host), if any *)
type last_datagram_seen =
    NO_DATAGRAMS
  | SENT_DATAGRAM of Holtypes.tcp_segment
  | RECV_DATAGRAM of Holtypes.tcp_segment;;

val timestamp_update_swap: (word32 * word32) option -> uint -> (word32 * word32) option
val timestamp_update: (word32 * word32) option -> uint -> (word32 * word32) option
val ts_incr: uint

(* The TCP states you can be in a la TCP state transition diagram *)
type tcp_state_diagram_state =
    ST_CLOSED
  | ST_LISTEN
  | ST_SYN_RCVD
  | ST_SYN_SENT
  | ST_ESTABLISHED of tcp_data_status
  | ST_CLOSE_WAIT of tcp_data_status
  | ST_LAST_ACK of tcp_data_status
  | ST_FIN_WAIT_1 of tcp_data_status
  | ST_CLOSING of tcp_data_status
  | ST_FIN_WAIT_2 of tcp_data_status
  | ST_TIME_WAIT of tcp_data_status;;

(* Create a fresh socket forcing it into state tcp_state_diagram_state. *)
(* Returns the socket's fd and the related last datagram seen on the wire *)
(* If requested also produce a duplicate fd *)
val tcp_state_diagram_driver:
    tthee_init_dual -> dual_test_state -> tcp_state_diagram_state -> bool ->
      fd * last_datagram_seen * fd option;;

val all_driven_states: (tcp_state_diagram_state * string) list

val all_interesting_driven_states: (tcp_state_diagram_state * string) list

val drive_socket_established_nomss:
    tthee_init_dual -> dual_test_state -> bool ->
      fd * last_datagram_seen * fd option;;

val rst_driven_socket: dual_test_state -> tthee_init_dual -> fd -> last_datagram_seen -> unit

(* ---------------------------------------------------------------------- *)
(* Exhausting file descriptors                                            *)
(* ---------------------------------------------------------------------- *)

val exhaust_proc_fds: dual_test_state -> tthee_init_dual -> unit

val exhaust_sys_fds: dual_test_state -> tthee_init_dual ->
  (log_handle * libd_handle) list

(* ---------------------------------------------------------------------- *)
(* Getting bound and/or connected sockets                                 *)
(* ---------------------------------------------------------------------- *)

type bound_ip =
    LOCAL_IP
  | LOOPBACK_IP
  | FOREIGN_IP
  | UNSPECIFIED_IP

type bound_port =
    PRIV_PORT
  | EPHM_PORT
  | NPOE_PORT
  | UNSPECIFIED_PORT
  | SOME_PORT  (* used for connect() *)

type bound_pair = bound_ip * bound_port
type bound_quad = bound_ip * bound_port * bound_ip * bound_port

val local_bindings_list: bound_pair list

val foreign_bindings_list: bound_pair list

val all_bindings_list: bound_quad list

val get_bound_socket: tthee_init_dual -> dual_test_state -> bound_quad ->
  fd option * fd option

val string_of_bound_quad: bound_quad -> string
(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)

