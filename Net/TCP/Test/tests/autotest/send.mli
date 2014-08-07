(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: send()                              *)
(* Steve Bishop - Created 20030707                                        *)
(* $Id: send.mli,v 1.3 2003/09/23 14:23:52 smb50 Exp $ *)
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

val do_send_tests: autotest_handle -> host_info list -> test_type -> bool;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
