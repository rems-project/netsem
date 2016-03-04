(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: deliver_in_3                        *)
(* Steve Bishop - Created 20030922                                        *)
(* $Id: deliver_in_3.mli,v 1.2 2004/01/08 17:37:52 smb50 Exp $ *)
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

val do_deliver_in_3_tests: autotest_handle -> host_info list -> test_type -> bool

val get_deliver_in_3_test_descriptions: unit -> unit

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
