(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: demo for paper                      *)
(* Matthew Fairbairn - Created 20041130                                   *)
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
    let fd_aux = get_socket (the ts.ah_libd_hnd) in
    let bind_call = (tid_of_int_private 0, BIND(fd_aux, Some(mk_ip id.aux_host.test_ip_address), Some(mk_port id.aux_host.test_ephm_port))) in
    ignore(libd_call (the ts.ah_libd_hnd) bind_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd_aux,3)) in
    ignore(libd_call (the ts.ah_libd_hnd) listen_call);
    let connect_call = (tid_of_int_private 0, CONNECT(fd,mk_ip id.aux_host.test_ip_address, Some(mk_port id.aux_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) connect_call);
    delay 0.5;
    let accept_call = (tid_of_int_private 0, ACCEPT(fd_aux)) in
    let libret = libd_call (the ts.ah_libd_hnd) accept_call in
    (* get the fd *)
    let fd_acc =
      match libret with
	(_, OK_FD_IP_PORT(fd,_)) -> fd
      | _ -> raise(Drive_Failure("accept() failed")) in
    let send_call = (tid_of_int_private 0, SEND(fd,None,"Hello!",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let recv_call = (tid_of_int_private 0, RECV(fd_acc,6,[])) in
    ignore(libd_call (the ts.ah_libd_hnd) recv_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd_acc)) in
    ignore(libd_call (the ts.ah_libd_hnd), close_call);
    delay 5.0),
  "Demonstration: create a listening socket on the auxiliary host; create a socket on the local host and connect to the listening socket; accept the connection; send a string and then receive the string on the auxiliary host; close both sockets",
  ((true,false),true,true,false),
  ((true,false),true,false,true))


(* ---------------------------------------------------------------------- *)

let udp_tests = []

let tcp_tests = [test1]

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_demo_tests handle hosts_list test_type =
  begin_next_test_group handle "demo tests";
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
