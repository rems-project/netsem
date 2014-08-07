(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: accept()                            *)
(* Steve Bishop - Created 20030430                                        *)
(* $Id: accept.mli,v 1.3 2003/09/23 14:23:51 smb50 Exp $ *)
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

val do_accept_tests: autotest_handle -> host_info list -> test_type -> bool;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
