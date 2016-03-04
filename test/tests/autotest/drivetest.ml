(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: socket driver test                  *)
(* Steve Bishop - Created 20030430                                        *)
(* $Id: drivetest.ml,v 1.15 2006/06/07 11:52:45 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread
open Printf

(* Our libraries *)
open Nettypes
open Holtypes
open Holparselib
open Tthee
open Ttheehelper
open Ocamllib
open Libcalls
open Common
open Dual
open Dualdriven

(* ---------------------------------------------------------------------- *)

let test (st,descr) = (
  (function id -> function ts ->
    let fd, last_datagram, _ = tcp_state_diagram_driver id ts st false in
    rst_driven_socket ts id fd last_datagram),
  "Check the test harness driver code that returns a socket in state " ^ descr ^ " functions as expected",
  ((true, false), true, true, false),
  ((false, false), false, false, true))

let tcp_tests = List.map test all_driven_states

let udp_tests = []

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_driver_tests handle hosts_list test_type =
  begin_next_test_group handle "driver";
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
	      (*ntp_update 60.0*)()) in
	  if not(skip_test handle) then
	    let _ = done_a_test := true in
	    let test_fname = fmt_fname handle !trace_name_number_size in
	    let id = {
	      tthee_host = handle.tthee_host_ip;
	      virtual_host_ip = handle.vhost_ip;
	      virtual_host_port = handle.vhost_port;
	      seq_fname = test_fname;
	      test_descr = (test_type_str test_type) ^ " " ^ descr;

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
	    num_of_tests := !num_of_tests + 1;
	    dual_tthee_cleanup ts
	  else ();
	  next_test handle)
	tests
    )
    hosts_list;
  !done_a_test

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
