(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: socket()                            *)
(* Steve Bishop - Created 20030430                                        *)
(* $Id: socket.ml,v 1.19 2006/06/19 11:57:45 amgb2 Exp $ *)
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

 let test1 = (
  (function id -> function ts ->
    let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
    try ignore(libd_call (the ts.th_libd_hnd) socket_call) with _ -> ()),
  "socket() -- call socket() and return normally with a fresh file descriptor",
  ((true, false), false, false, false),
  ((false, false), false, false, false)
 )

let test2 = (
  (function id -> function ts ->
    (* Make a socket call to get things merging *)
    let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
    (try ignore(libd_call (the ts.th_libd_hnd) socket_call) with _ -> ());
    (* Exhaust process file descriptors *)
    exhaust_proc_fds ts id;
    (* Attempt to call socket *)
    let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
    try ignore(libd_call (the ts.th_libd_hnd) socket_call) with _ -> ()),
  "socket() --  call socket() many times to eventually exhaust all of the processes file descriptors",
  ((true, false), false, false, false),
  ((false, false), false, false, false)
 )

let test3 = (
  (function id -> function ts ->
    (* Make a socket call to get things merging *)
    let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
    (try ignore(libd_call (the ts.th_libd_hnd) socket_call) with _ -> ());
    (* Exhaust sys file descriptors *)
    let exhaust_results = exhaust_sys_fds ts id in
    (* Attempt to call socket *)
    let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
    (try ignore(libd_call (the ts.th_libd_hnd) socket_call) with _ -> ());
    clearup_libd_list exhaust_results),
  "socket() -- call socket() manytime from several different processes to exhaust all of the system-wide file descriptors",
  ((true, false), false, false, false),
  ((false, false), false, false, false)
 )


let test4 = (
  (function id -> function ts ->
    let socket_call = (tid_of_int_private 0, SOCKET(SOCK_DGRAM)) in
    try ignore(libd_call (the ts.th_libd_hnd) socket_call) with _ -> ()),
  "socket() -- call socket() and return normally with a fresh file descriptor",
  ((true, false), false, false, false),
  ((false, false), false, false, false)
 )

let test5 = (
  (function id -> function ts ->
    (* Make a socket call to get things merging *)
    let socket_call = (tid_of_int_private 0, SOCKET(SOCK_DGRAM)) in
    (try ignore(libd_call (the ts.th_libd_hnd) socket_call) with _ -> ());
    (* Exhaust process file descriptors *)
    exhaust_proc_fds ts id;
    (* Attempt to call socket *)
    let socket_call = (tid_of_int_private 0, SOCKET(SOCK_DGRAM)) in
    try ignore(libd_call (the ts.th_libd_hnd) socket_call) with _ -> ()),
  "socket() --  call socket() many times to eventually exhaust all of the processes file descriptors",
  ((true, false), false, false, false),
  ((false, false), false, false, false)
 )

let test6 = (
  (function id -> function ts ->
    (* Make a socket call to get things merging *)
    let socket_call = (tid_of_int_private 0, SOCKET(SOCK_DGRAM)) in
    (try ignore(libd_call (the ts.th_libd_hnd) socket_call) with _ -> ());
    (* Exhaust sys file descriptors *)
    let exhaust_results = exhaust_sys_fds ts id in
    (* Attempt to call socket *)
    let socket_call = (tid_of_int_private 0, SOCKET(SOCK_DGRAM)) in
    (try ignore(libd_call (the ts.th_libd_hnd) socket_call) with _ -> ());
    clearup_libd_list exhaust_results),
  "socket() -- call socket() manytime from several different processes to exhaust all of the system-wide file descriptors",
  ((true, false), false, false, false),
  ((false, false), false, false, false)
 )


let tcp_tests = [test1]

let udp_tests = [test4]

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = [test2; test3]
let udp_exhaustive_tests = [test5; test6]
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = tcp_tests
let stream_exhaustive_tests = tcp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

(* do_socket_tests autotest_handle host_list test_type  = bool          *)
(* For each host in host_list perform a suite of tests designed to test *)
(* the socket() system call.  For more information on the tests refer   *)
(* to the auto-testing documentation                                    *)
let do_socket_tests handle hosts_list test_type =
  begin_next_test_group handle "socket()";
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

		dual_tthee_cleanup ts
	      else ();
	      next_test handle
	    with Unix.Unix_error(e,_,_) ->
	      if n = 0 then raise (Test_failed ("Unix_error:" ^ (Unix.error_message e)))
	      else
		(delay (float_of_int (n * 30));
		 do_test test_thunk descr thts ahts (n-1)) in
	  do_test test_thunk descr thts ahts 10;
	  num_of_tests := !num_of_tests + 1;)
	tests
    )
    hosts_list;
  !done_a_test;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
