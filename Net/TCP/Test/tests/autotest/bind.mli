(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: bind()                              *)
(* Steve Bishop - Created 20030503                                        *)
(* $Id $ *)
(* ---------------------------------------------------------------------- *)

(* Our libraries *)
open Common;;
open Simple;;

(* do_bind_tests handle host_pair_list test_type = bool                        *)
(* For each pair of hosts in host_pair_list perform a suite of tests designed  *)
(* to test the bind() system call.  For more information on the tests          *)
(* refer to the auto-testing documentation                                     *)
val do_bind_tests: autotest_handle -> (host_info * host_info) list ->
  test_type -> bool;;
