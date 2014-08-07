(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: deliver_icmp                        *)
(* Matthew Fairbairn - Created 20040419                                   *)
(* $Id: deliver_icmp.mli,v 1.1 2004/04/19 16:42:38 mf266 Exp $ *)
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

val do_deliver_icmp_tests: autotest_handle -> host_info list -> test_type -> bool
