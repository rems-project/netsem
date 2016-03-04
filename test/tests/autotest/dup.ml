(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: dup()                               *)
(* Steve Bishop - Created 20030430                                        *)
(* $Id: dup.ml,v 1.15 2006/06/19 11:57:45 amgb2 Exp $ *)
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
    let dup_call = (tid_of_int_private 0, DUP(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call)),
  "dup() -- for a fresh socket call dup()",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test2 = (
  (function id -> function ts ->
    let fd1 = get_socket (the ts.th_libd_hnd) in
    let fd2 = get_socket (the ts.th_libd_hnd) in
    let fd3 = get_socket (the ts.th_libd_hnd) in
    let fd4 = get_socket (the ts.th_libd_hnd) in
    let fd5 = get_socket (the ts.th_libd_hnd) in
    let fd6 = get_socket (the ts.th_libd_hnd) in
    let fd7 = get_socket (the ts.th_libd_hnd) in
    let fd8 = get_socket (the ts.th_libd_hnd) in
    let fd9 = get_socket (the ts.th_libd_hnd) in
    let fd19 = get_socket (the ts.th_libd_hnd) in
    let close_call = (tid_of_int_private 0, CLOSE(fd3)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd4)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd8)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let dup_call = (tid_of_int_private 0, DUP(fd1)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call);
    let dup_call = (tid_of_int_private 0, DUP(fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call);
    let dup_call = (tid_of_int_private 0, DUP(fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call)),
  "dup() -- get 10 fresh file descriptors and close the 3rd, 4th and 8th in the allocation range. Call dup() once on the 1st  and twice on the 2nd file descriptor to check that the minimal fd available is allocated in each case (should be one of the file descriptors that we freed)",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test3 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    (* Exhaust process file descriptors *)
    let fdlist = exhaust_proc_fds ts id in
    let dup_call = (tid_of_int_private 0, DUP(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call)),
  "dup() -- get a fresh socket, exhaust of the process file descriptors and try to dup() our socket",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test4 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    (* Exhaust process file descriptors *)
    let fdlist = exhaust_sys_fds ts id in
    let dup_call = (tid_of_int_private 0, DUP(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call)),
  "dup() -- get a fresh socket, exhaust all of the system-wide file descriptors and try to dup() our socket",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )


let test5 = (
  (function id -> function ts ->
    let fd = get_socket_udp (the ts.th_libd_hnd) in
    let dup_call = (tid_of_int_private 0, DUP(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call)),
  "dup() -- for a fresh UDP socket call dup()",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test6 = (
  (function id -> function ts ->
    let fd1 = get_socket_udp (the ts.th_libd_hnd) in
    let fd2 = get_socket_udp (the ts.th_libd_hnd) in
    let fd3 = get_socket_udp (the ts.th_libd_hnd) in
    let fd4 = get_socket_udp (the ts.th_libd_hnd) in
    let fd5 = get_socket_udp (the ts.th_libd_hnd) in
    let fd6 = get_socket_udp (the ts.th_libd_hnd) in
    let fd7 = get_socket_udp (the ts.th_libd_hnd) in
    let fd8 = get_socket_udp (the ts.th_libd_hnd) in
    let fd9 = get_socket_udp (the ts.th_libd_hnd) in
    let fd19 = get_socket_udp (the ts.th_libd_hnd) in
    let close_call = (tid_of_int_private 0, CLOSE(fd3)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd4)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd8)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let dup_call = (tid_of_int_private 0, DUP(fd1)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call);
    let dup_call = (tid_of_int_private 0, DUP(fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call);
    let dup_call = (tid_of_int_private 0, DUP(fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call)),
  "dup() -- get 10 fresh UDP file descriptors and close the 3rd, 4th and 8th in the allocation range. Call dup() once on the 1st  and twice on the 2nd file descriptor to check that the minimal fd available is allocated in each case (should be one of the file descriptors that we freed)",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test7 = (
  (function id -> function ts ->
    let fd = get_socket_udp (the ts.th_libd_hnd) in
    (* Exhaust process file descriptors *)
    let fdlist = exhaust_proc_fds ts id in
    let dup_call = (tid_of_int_private 0, DUP(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call)),
  "dup() -- get a fresh UDP socket, exhaust of the process file descriptors and try to dup() our socket",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test8 = (
  (function id -> function ts ->
    let fd = get_socket_udp (the ts.th_libd_hnd) in
    (* Exhaust process file descriptors *)
    let fdlist = exhaust_sys_fds ts id in
    let dup_call = (tid_of_int_private 0, DUP(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) dup_call)),
  "dup() -- get a fresh UDP socket, exhaust all of the system-wide file descriptors and try to dup() our socket",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let tcp_tests = [test1; test2]

let udp_tests = [test5; test6]

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = [test3; test4]
let udp_exhaustive_tests = [test7; test8]
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = tcp_tests
let stream_exhaustive_tests = tcp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_dup_tests handle hosts_list test_type =
  begin_next_test_group handle "dup()";
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
	  if host.platform_type = ARCH_WINXP then num_of_tests := !num_of_tests + 1;)
	tests
    )
    hosts_list;
  !done_a_test

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
