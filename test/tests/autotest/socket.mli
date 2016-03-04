(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Common Code                               *)
(* Steve Bishop - Created 20030430                                        *)
(* $Id: socket.mli,v 1.6 2006/06/06 15:05:03 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread;;
open Unix;;
open ThreadUnix;;

(* Our libraries *)
open Common;;

(* do_socket_tests autotest_handle host_list test_type  = bool          *)
(* For each host in host_list perform a suite of tests designed to test *)
(* the socket() system call.  For more information on the tests refer   *)
(* to the auto-testing documentation                                    *)
val do_socket_tests: autotest_handle -> host_info list -> test_type -> bool;;


