(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: disconnect()                        *)
(* Matthew Fairbairn - Created 20040113                                   *)
(* $Id: disconnect.ml,v 1.12 2006/06/20 10:48:22 amgb2 Exp $               *)
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

(* ---------------------------------------------------------------------- *)

let test1 =
  function sf -> (
    (function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let disconnect_call = (tid_of_int_private 0, DISCONNECT(fd)) in
      ignore(libd_call (the ts.th_libd_hnd) disconnect_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
    "disconnect() -- call disconnect() on UDP socket with bound quad " ^ (string_of_bound_udp_quad sf),
    ((true,false),true,false,false),
    ((false,false),false,false,true))

let test2 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let disconnect_call = (tid_of_int_private 0, DISCONNECT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) disconnect_call)),
  "disconnect() -- on a fresh, unbound TCP socket",
  ((true,false),true,true,false),
  ((false,false),false,false,false))

let test3 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let connect_call = (tid_of_int_private 0, CONNECT(fd, mk_ip id.virtual_host_ip, Some(mk_port id.virtual_host_port))) in
    ignore(libd_call (the ts.th_libd_hnd) connect_call);
    let disconnect_call = (tid_of_int_private 0, DISCONNECT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) disconnect_call);
    rst_driven_socket ts id fd NO_DATAGRAMS),
  "disconnect() -- for a socket that has failed to connect, call disconnect()",
  ((true,false),true,true,false),
  ((false,false),false,false,false))

let test4 = (
  function (st, str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let disconnect_call = (tid_of_int_private 0, DISCONNECT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) disconnect_call);
    rst_driven_socket ts id fd last_dg),
  "disconnect() -- for a TCP socket in state " ^ str ^ ", call disconnect()",
  ((true, false), true, true, false),
  ((false, false), false, false, true))



let tcp_tests = [test2; test3] @ (List.map test4 all_driven_states)

let udp_tests = (List.map test1 all_sock_flavours)

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = [test2; test3]
let stream_exhaustive_tests = []

(* ---------------------------------------------------------------------- *)

let do_disconnect_tests handle hosts_list test_type =
  begin_next_test_group handle "disconnect()";
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
