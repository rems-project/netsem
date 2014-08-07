(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: getsocklistening()                  *)
(* Steve Bishop - Created 20030626                                        *)
(* $Id: getsocklistening.ml,v 1.13 2006/06/07 11:52:45 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread
open Printf

(* Our libraries *)
open Nettypes
open Tthee
open Ttheehelper
open Ocamllib
open Libcalls
open Common
open Dual
open Dualdriven
open Common_udp
open Dualdriven_udp
open Testscommon
(* ---------------------------------------------------------------------- *)

let test1 = (
  function (st, str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let getsocklistening_call = (tid_of_int_private 0, GETSOCKLISTENING(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) getsocklistening_call);
    rst_driven_socket ts id fd last_dg),
  "getsocklistening() -- for a TCP socket in state " ^ str ^ ", call getsocklistening()",
  ((true, false), true, true, false),
  ((false, false), false, false, true))

let test2 = (
  function (sf,sfdescr) ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let getsocklisteningcall = (tid_of_int_private 0, GETSOCKLISTENING(fd)) in
      ignore(libd_call (the ts.th_libd_hnd) getsocklisteningcall);
      rst_udp_socket id ts fd),
     "getsocklistening() -- for a UDP socket with address quad " ^ sfdescr ^ ", call getsocklistening()",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )

let test_from_all_states =  List.map test1 all_interesting_driven_states

let tcp_tests = test_from_all_states

let udp_tests = (List.map test2 bound_udp_quads)

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_getsocklistening_tests handle hosts_list test_type =
  begin_next_test_group handle "getsocklistening()";
  let done_a_test = ref false in
  let num_of_tests = ref 0 in

  let tests = match test_type with
    TCP_NORMAL -> tcp_tests
  | UDP_NORMAL -> udp_tests
  | ALL_NORMAL -> normal_tests
  | TCP_EXHAUSTIVE -> tcp_exhaustive_tests
  | UDP_EXHAUSTIVE -> udp_exhaustive_tests
  | ALL_EXHAUSTIVE -> exhaustive_tests
  | STREAM_NORMAL -> []
  | STREAM_EXHAUSTIVE -> [] in

  List.iter
    (function host ->
      List.iter
	(function (test_thunk, descr, thts, ahts) ->
	  let _ =
	    (if(!num_of_tests = 10) then
	      let _ =  num_of_tests := 0 in
	      ntp_update 60.0) in
	  let rec do_test test_thunk descr thts ahts n =
	    try
	      if not(skip_test handle) then
		let _ = done_a_test := true in
		let test_fname = fmt_fname handle !trace_name_number_size in
		let id = {
		  tthee_host = handle.tthee_host_ip;
		  virtual_host_ip = handle.vhost_ip;
		  virtual_host_port = handle.vhost_port;
		  seq_fname = test_fname;
		  test_descr = (test_type_str test_type) ^ " " ^descr;

		  test_host = host;
		  test_host_tools = thts;
		  test_host_bound = [];

		  aux_host = pick_any_other_host hosts_list host;
		  aux_host_tools =  ahts;
		  aux_host_bound = [];
		} in

		let ts = dual_tthee_init id debug_OFF !tthee_baseport_1
		!tthee_baseport_2 !merger_delta in
		let _ =
		  try test_thunk id ts
		  with e -> report_test_failure handle descr e
		in

		dual_tthee_cleanup ts
	      else ();
	      next_test handle
	    with Unix.Unix_error(e,_,_) ->
	      if n = 0 then raise (Test_failed ("Unix_error:" ^ (Unix.error_message e)))
	      else
		(delay (float_of_int (n * 30));
		 do_test test_thunk descr thts ahts (n-1)) in
	  do_test test_thunk descr thts ahts 10;
	  if host.platform_type = ARCH_WINXP then num_of_tests := !num_of_tests + 1;)
	tests
    )
    hosts_list;
  !done_a_test

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
