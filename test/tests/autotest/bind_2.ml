(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: bind()                              *)
(* Steve Bishop - Created 20030717                                        *)
(* $Id: bind_2.ml,v 1.11 2006/06/19 11:57:44 amgb2 Exp $ *)
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
    let fd = get_socket (the ts.th_libd_hnd) in
    let bind_call1 = (tid_of_int_private 0,
		     BIND(fd, None, Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call1);
    let bind_call2 = (tid_of_int_private 0,
		     BIND(fd, Some(mk_ip id.test_host.test_ip_address),
			  Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call2);
    rst_driven_socket ts id fd NO_DATAGRAMS),
  "bind() -- call bind() twice: once with only a port then again with an (ip,port) pair to test incremental binding capabilities",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test2 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let bind_call1 = (tid_of_int_private 0,
		     BIND(fd, Some(mk_ip id.test_host.test_ip_address), None)) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call1);
    let bind_call2 = (tid_of_int_private 0,
		     BIND(fd, Some(mk_ip id.test_host.test_ip_address),
			  Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call2);
    rst_driven_socket ts id fd NO_DATAGRAMS),
  "bind() -- call bind() twice: once with only an ip address then again with an (ip,port) pair to test incremental binding capabilities",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test3 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let bind_call1 = (tid_of_int_private 0,
		     BIND(fd, Some(mk_ip id.test_host.test_ip_address),
			  Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call1);
    let bind_call1 = (tid_of_int_private 0,
		     BIND(fd, Some(mk_ip id.test_host.test_ip_address),
			  Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call1);
    rst_driven_socket ts id fd NO_DATAGRAMS),
  "bind() -- call bind() on an already bound socket to check whether rebinding of a socket is permitted",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test4 = (
  (function id -> function ts ->
    let fd,last_dg,_ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let bind_call1 = (tid_of_int_private 0,
		     BIND(fd, Some(mk_ip id.test_host.test_ip_address),
			  Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call1);
    rst_driven_socket ts id fd last_dg),
  "bind() -- call bind() on an already connected socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
 )


let udp_tests = []

let tcp_tests = [test1; test2; test3; test4]

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = [test1; test2; test3]
let stream_exhaustive_tests = []

(* ---------------------------------------------------------------------- *)

let do_bind_2_tests handle hosts_list test_type =
  begin_next_test_group handle "bind() (second set)";
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
