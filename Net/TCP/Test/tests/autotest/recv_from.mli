(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: recv() UDP                          *)
(* Matthew Fairbairn - Created 20040116                                   *)
(* $Id: recv_from.mli,v 1.1 2004/02/19 12:21:49 mf266 Exp $ *)
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

val do_recv_from_tests: autotest_handle -> host_info list -> test_type -> bool
