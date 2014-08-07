(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: loopback                            *)
(* Steve Bishop - Created 20031009                                        *)
(* $Id: loopback.mli,v 1.1 2003/10/10 14:05:10 smb50 Exp $ *)
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

val do_loopback_tests: autotest_handle -> host_info list -> test_type -> bool;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
