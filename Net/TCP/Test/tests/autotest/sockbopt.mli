(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: getsockbopt()/setsockbopt()         *)
(* Steve Bishop - Created 20030702                                        *)
(* $Id: sockbopt.mli,v 1.2 2003/09/23 14:23:52 smb50 Exp $ *)
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

val do_sockbopt_tests: autotest_handle -> host_info list -> test_type -> bool;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
