(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: loopback()                          *)
(* Steve Bishop - Created 20031009                                        *)
(* $Id: loopback.ml,v 1.14 2006/06/19 11:57:45 amgb2 Exp $ *)
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
open Testscommon

(* ---------------------------------------------------------------------- *)

let test1 = (
   (function id -> function ts ->
   let slurper_log =
     let log = create_fresh_log (string_ip id.tthee_host) in
     let _ = merger_register_log ts.th_merge_hnd log None in
     log in
   let slurper_hnd =
     let slurp_filter = Some("tcp") in
     let slurp_hostip = Some(hol_ip (127,0,0,1)) in
     let slurp_iface = id.test_host.loopback_name in
   slurper_create id.test_host.ns_tools_exec_params slurper_log slurp_iface slurp_filter slurp_hostip in
  let fd = get_socket (the ts.th_libd_hnd) in
  let connect_call = (tid_of_int_private 0, CONNECT(fd, mk_ip (127,0,0,1), Some(mk_port 10000))) in
  ignore(libd_call (the ts.th_libd_hnd) connect_call);
  delay 1.0 ;
  ignore(slurper_destroy slurper_hnd);
  ignore(destroy_log slurper_log);
  delay 10.00),
  "loopback test -- create a socket and attempt to connect to a local ip/port. Additional slurper running on loopback interface",
  ((true, false), false, false, false),
  ((false, false), false, false, false)
 )

let tcp_tests = [test1]

let udp_tests = []

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = tcp_tests
let stream_exhaustive_tests = tcp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_loopback_tests handle hosts_list test_type =
  begin_next_test_group handle "loopback";
  let done_a_test = ref false in
  let num_of_tests = ref 0 in

  let tests = match test_type with
    TCP_NORMAL -> tcp_tests
  | UDP_NORMAL -> udp_tests
  | ALL_NORMAL -> normal_tests
  | TCP_EXHAUSTIVE -> tcp_exhaustive_tests
  | UDP_EXHAUSTIVE -> udp_exhaustive_tests
  | ALL_EXHAUSTIVE -> exhaustive_tests
  | STREAM_NORMAL -> stream_tests
  | STREAM_EXHAUSTIVE -> stream_exhaustive_tests in

  List.iter
    (function host ->
      List.iter
	(function (test_thunk, descr, thts, ahts) ->
	  let _ =
	    (if(!num_of_tests = 10) then
	      let _ =  num_of_tests := 0 in
	      ntp_update 60.0) in
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
