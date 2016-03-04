(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: send() UDP                          *)
(* Matthew Fairbairn - Created 20040116                                   *)
(* $Id: send_to.mli,v 1.1 2004/02/17 21:47:04 mf266 Exp $ *)
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

val do_send_to_tests: autotest_handle -> host_info list -> test_type -> bool
