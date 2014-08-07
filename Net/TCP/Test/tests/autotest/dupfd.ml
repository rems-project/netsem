1(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: dupfd()                             *)
(* Steve Bishop - Created 20030430                                        *)
(* $Id: dupfd.ml,v 1.15 2006/06/26 13:45:56 amgb2 Exp $ *)
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
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd, Ocamllib.int_of_fd fd)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call)),
  "dupfd() --  get a fresh socket and try to dupfd() to itself",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test2 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd, 2)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call)),
  "dupfd() --  attempt to dupfd() a fresh socket to a file descriptor that is already in use",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test3 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd, 300)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call)),
  "dupfd() --  attempt to dupfd() a fresh socket to a file descriptor that is unallocated",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test4 = (
  (function id -> function ts ->
    let fd1 = get_socket (the ts.th_libd_hnd) in
    let fd2 = get_socket (the ts.th_libd_hnd) in
    let fd3 = get_socket (the ts.th_libd_hnd) in
    let fd4 = get_socket (the ts.th_libd_hnd) in
    let fd5 = get_socket (the ts.th_libd_hnd) in
    let close_call = (tid_of_int_private 0, CLOSE(fd3)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd4)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd1, int_of_fd fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call)),
  "dupfd() -- attempt to dupfd() a fresh socket to a file descriptor that is already in use with some available fds in a higher numbered gap",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test5 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd, 5000)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call)),
  "dupfd() --  attempt to dupfd() a fresh socket to a file descriptor that is out of range",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test6 = (
  (function id -> function ts ->
    let fd1 = get_socket (the ts.th_libd_hnd) in
    let fd2 = get_socket (the ts.th_libd_hnd) in
    (* Exhaust process file descriptors *)
    exhaust_proc_fds ts id;
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd1, int_of_fd fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call);
 (*   clearup_libd_list fdlist*)),
  "dupfd() --  attempt to dupfd() a fresh socket to an allocated file descriptor when process file descriptors are exhausted",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test7 = (
  (function id -> function ts ->
    let fd1 = get_socket (the ts.th_libd_hnd) in
    let fd2 = get_socket (the ts.th_libd_hnd) in
    (* Exhaust system file descriptors *)
    let libd_list = exhaust_sys_fds ts id in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd1, int_of_fd fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call);
    clearup_libd_list libd_list),
  "dupfd() -- attempt to dupfd() a fresh socket to an allocated file descriptor when system-wide file descriptors are exhausted",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )
let test8 = (
  (function id -> function ts ->
    let fd1 = get_socket (the ts.th_libd_hnd) in
    (* Exhaust process file descriptors *)
    exhaust_proc_fds ts id;
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd1, int_of_fd fd1)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call);
 (*   clearup_libd_list fdlist*)),
  "dupfd() --  attempt to dupfd() a fresh socket to itself when process file descriptors are exhausted",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test9 = (
  (function id -> function ts ->
    let fd1 = get_socket (the ts.th_libd_hnd) in
    (* Exhaust system file descriptors *)
    let libd_list = exhaust_sys_fds ts id in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd1, int_of_fd fd1)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call);
    clearup_libd_list libd_list),
  "dupfd() --  attempt to dupfd() a fresh socket to itself with system-wide file descriptors exhausted",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )


let test10 = (
  (function id -> function ts ->
    let fd = get_socket_udp (the ts.th_libd_hnd) in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd, Ocamllib.int_of_fd fd)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call)),
  "dupfd() --  get a fresh UDP socket and try to dupfd() to itself",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test11 = (
  (function id -> function ts ->
    let fd = get_socket_udp (the ts.th_libd_hnd) in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd, 2)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call)),
  "dupfd() --  attempt to dupfd() a fresh UDP socket to a file descriptor that is already in use",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test12 = (
  (function id -> function ts ->
    let fd = get_socket_udp (the ts.th_libd_hnd) in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd, 300)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call)),
  "dupfd() --  attempt to dupfd() a fresh UDP socket to a file descriptor that is unallocated",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test13 = (
  (function id -> function ts ->
    let fd1 = get_socket_udp (the ts.th_libd_hnd) in
    let fd2 = get_socket_udp (the ts.th_libd_hnd) in
    let fd3 = get_socket_udp (the ts.th_libd_hnd) in
    let fd4 = get_socket_udp (the ts.th_libd_hnd) in
    let fd5 = get_socket_udp (the ts.th_libd_hnd) in
    let close_call = (tid_of_int_private 0, CLOSE(fd3)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd4)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd1, int_of_fd fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call)),
  "dupfd() -- attempt to dupfd() a fresh UDP socket to a file descriptor that is already in use with some available fds in a higher numbered gap",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test14 = (
  (function id -> function ts ->
    let fd = get_socket_udp (the ts.th_libd_hnd) in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd, 5000)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call)),
  "dupfd() --  attempt to dupfd() a fresh UDP socket to a file descriptor that is out of range",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test15 = (
  (function id -> function ts ->
    let fd1 = get_socket_udp (the ts.th_libd_hnd) in
    let fd2 = get_socket_udp (the ts.th_libd_hnd) in
    (* Exhaust process file descriptors *)
    exhaust_proc_fds ts id;
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd1, int_of_fd fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call);
 (*   clearup_libd_list fdlist*)),
  "dupfd() --  attempt to dupfd() a fresh UDP socket to an allocated file descriptor when process file descriptors are exhausted",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test16 = (
  (function id -> function ts ->
    let fd1 = get_socket_udp (the ts.th_libd_hnd) in
    let fd2 = get_socket_udp (the ts.th_libd_hnd) in
    (* Exhaust system file descriptors *)
    let libd_list = exhaust_sys_fds ts id in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd1, int_of_fd fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call);
    clearup_libd_list libd_list),
  "dupfd() -- attempt to dupfd() a fresh UDP socket to an allocated file descriptor when system-wide file descriptors are exhausted",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )
let test17 = (
  (function id -> function ts ->
    let fd1 = get_socket_udp (the ts.th_libd_hnd) in
    (* Exhaust process file descriptors *)
    exhaust_proc_fds ts id;
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd1, int_of_fd fd1)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call);
 (*   clearup_libd_list fdlist*)),
  "dupfd() --  attempt to dupfd() a fresh UDP socket to itself when process file descriptors are exhausted",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test18 = (
  (function id -> function ts ->
    let fd1 = get_socket_udp (the ts.th_libd_hnd) in
    (* Exhaust system file descriptors *)
    let libd_list = exhaust_sys_fds ts id in
    let dupfd_call = (tid_of_int_private 0, DUPFD(fd1, int_of_fd fd1)) in
    ignore(libd_call (the ts.th_libd_hnd) dupfd_call);
    clearup_libd_list libd_list),
  "dupfd() --  attempt to dupfd() a fresh UDP socket to itself with system-wide file descriptors exhausted",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let tcp_tests = [test1; test2; test3; test4; test5]

let udp_tests = [test10; test11; test12; test13; test14]

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = [test6; test7; test8; test9]
let udp_exhaustive_tests = [test15; test16; test17; test18]
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = tcp_tests
let stream_exhaustive_tests = tcp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_dupfd_tests handle hosts_list test_type =
  begin_next_test_group handle "dupfd()";
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
		  test_descr =(test_type_str test_type) ^ " " ^ descr;

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
