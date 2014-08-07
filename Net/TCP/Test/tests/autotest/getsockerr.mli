(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: getsockerr()                        *)
(* Steve Bishop - Created 20030721                                        *)
(* $Id: getsockerr.mli,v 1.2 2003/09/23 14:23:51 smb50 Exp $ *)
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

val do_getsockerr_tests: autotest_handle -> host_info list -> test_type -> bool

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
