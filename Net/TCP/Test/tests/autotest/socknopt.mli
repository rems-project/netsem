(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: getsocknopt()/setsocknopt()         *)
(* Steve Bishop - Created 20030702                                        *)
(* $Id: socknopt.mli,v 1.2 2003/09/23 14:23:52 smb50 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread;;
open Printf;;

(* Our libraries *)
open Nettypes;;
open Tthee;;
open Ttheehelper;;
open Libcalls;;
open Common;;
open Dual;;

val do_socknopt_tests: autotest_handle -> host_info list -> test_type -> bool;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
