(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: pselect()                           *)
(* Matthew Fairbairn - Created 20040621                                   *)
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

val do_pselect_tests: autotest_handle -> host_info list -> test_type -> bool
