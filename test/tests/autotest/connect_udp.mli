(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: connect() UDP                          *)
(* Matthew Fairbairn - Created 20040116                                   *)
(* $Id: connect_udp.mli,v 1.1 2004/02/17 21:47:03 mf266 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread;;

(* Our libraries *)
open Nettypes
open Tthee
open Ttheehelper
open Ocamllib
open Libcalls
open Common
open Dual
open Dualdriven_udp
open Common_udp

val do_connect_udp_tests: autotest_handle -> host_info list -> test_type -> bool
