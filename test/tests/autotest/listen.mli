(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: listen()                            *)
(* Steve Bishop - Created 20030430                                        *)
(* $Id: listen.mli,v 1.4 2003/09/23 14:23:52 smb50 Exp $ *)
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

val do_listen_tests: autotest_handle -> host_info list -> test_type -> bool;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
