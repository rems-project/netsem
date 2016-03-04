(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: send() for UDP                      *)
(* Matthew Fairbairn - Created 20040113                                   *)
(* $Id: send_to.ml,v 1.9 2006/06/07 11:52:45 amgb2 Exp $               *)
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
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"Test",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a non-blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send() data",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test1a = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let send_call = (tid_of_int_private 0, SEND(fd,None,"Test",[MSG_DONTWAIT])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a non-blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send() data",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test1b = (
  function sf -> function af -> function pf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let ip = get_ip_udp af id ts in
      let port = get_port_udp pf id ts in
      let send_call = (tid_of_int_private 0, SEND(fd,Some(the ip, the port),"Test",[MSG_DONTWAIT])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a non-blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send() data to " ^ (string_of_ip_flavour af) ^":"^ (string_of_port_flavour pf),
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test1c = (
  function sf -> function af -> function pf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let ip = get_ip_udp af id ts in
      let port = get_port_udp pf id ts in
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let send_call = (tid_of_int_private 0, SEND(fd,Some(the ip, the port),"Test",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a non-blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send() data to " ^ (string_of_ip_flavour af) ^":"^ (string_of_port_flavour pf),
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test2 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let send_call = (tid_of_int_private 0, SEND(fd,None,"Test",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send() data",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test2a = (
  function sf -> function af -> function pf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let ip = get_ip_udp af id ts in
      let port = get_port_udp pf id ts in
      let send_call = (tid_of_int_private 0, SEND(fd,Some(the ip, the port),"Test",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send() data to " ^ (string_of_ip_flavour af) ^":"^ (string_of_port_flavour pf),
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test3 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let send_call = (tid_of_int_private 0, SEND(fd,None,"Test",[MSG_WAITALL])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send() with MSG_WAITALL flag set and expect to fail",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )


let test3a = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let send_call = (tid_of_int_private 0, SEND(fd,None,"Test",[MSG_PEEK])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send() with MSG_PEEK flag set and expect to fail",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )


let test4 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let send_call = (tid_of_int_private 0, SEND(fd,None,"Test",[MSG_OOB])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send() with MSG_OOB flag set",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test5 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let rec mkdata x n =
	if n < 17 then mkdata (x^x) (n+1)
	else x in
      let data = mkdata "a" 0 in
      let send_call = (tid_of_int_private 0, SEND(fd,None,data,[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send() with data size > UDPPayloadMax",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test6 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
      ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
      let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILLFILL", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      rst_udp_socket id ts fd),
     "send() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send with a reduced send buffer that is full - should fail",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test6a = (
  function sf -> function af -> function pf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let ip = get_ip_udp af id ts in
      let port = get_port_udp pf id ts in
      let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
      ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
      let send_call = (tid_of_int_private 0, SEND(fd, Some(the ip, the port), "FILLFILLFILL", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      let send_call = (tid_of_int_private 0, SEND(fd, Some(the ip, the port), "### Test data ###", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send some data to " ^ (string_of_ip_flavour af) ^":"^ (string_of_port_flavour pf) ^ "with a reduced send buffer that is full - should fail",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test7 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
      ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
      let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILL", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send with a reduced send buffer that is full, should give a partial send",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test7a = (
  function sf -> function af -> function pf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let ip = get_ip_udp af id ts in
      let port = get_port_udp pf id ts in
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
      ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
      let send_call = (tid_of_int_private 0, SEND(fd, Some(the ip, the port), "FILLFILL", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd, Some(the ip, the port), "### Test data ###", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "send() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", attempt to send to " ^ (string_of_ip_flavour af) ^ ":" ^ (string_of_port_flavour pf) ^ ", with a reduced send buffer that is full, should give a partial send",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test8 = (
  function sf -> function af -> function pf ->
    ((function id -> function ts ->
      let fd1 = get_bound_socket_reuse_udp id ts sf in
      let ip = get_ip_udp af id ts in
      let port = get_port_udp pf id ts in
      let connect_call = (tid_of_int_private 0, CONNECT(fd1, the ip, port)) in
      ignore(libd_call (the ts.th_libd_hnd) connect_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd1;
      let fd2 = get_bound_socket_reuse_udp id ts sf in
      let send_call = (tid_of_int_private 0, SEND(fd2, Some(the ip,the port), "Test", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd2;
      rst_udp_socket id ts fd1;
      rst_udp_socket id ts fd2),
     "send() -- create two UDP sockets with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", then connect the first to " ^ (string_of_ip_flavour af) ^":"^ (string_of_port_flavour pf) ^ ", then try to send data from the other socket to that same address - should fail",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
  )

let test9 = (
   function sf -> function af -> function pf ->
     ((function id -> function ts ->
       let fd1 = get_bound_socket_reuse_udp id ts sf in
       let ip = get_ip_udp af id ts in
       let port = get_port_udp pf id ts in
       let connect_call = (tid_of_int_private 0, CONNECT(fd1, the ip, port)) in
       ignore(libd_call (the ts.th_libd_hnd) connect_call);
       get_bound_state_udp (the ts.th_libd_hnd) fd1;
       let fd2 = get_socket_udp (the ts.th_libd_hnd) in
       let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd2, SO_REUSEADDR,true)) in
       ignore(libd_call (the ts.th_libd_hnd) reuse_call);
       let bind_call = (tid_of_int_private 0, BIND(fd2, None, get_port_udp KNOWN_PORT id ts)) in
       ignore(libd_call (the ts.th_libd_hnd) bind_call);
       get_bound_state_udp (the ts.th_libd_hnd) fd2;
       let send_call = (tid_of_int_private 0, SEND(fd2, Some(the ip, the port), "Test", [])) in
       ignore(libd_call (the ts.th_libd_hnd) send_call);
       get_bound_state_udp (the ts.th_libd_hnd) fd2;
       rst_udp_socket id ts fd1; rst_udp_socket id ts fd2),
      "send() -- create two UDP sockets, one with binding quad " ^ (string_of_bound_udp_quad sf) ^ " and SO_REUSEADDR set; connect it to " ^ (string_of_ip_flavour af) ^ ":" ^ (string_of_port_flavour pf) ^ " then bind the other to the same local port, and try to send data to the same address",
      ((true,true),true,false,false),
      ((false,false),false,false,true))
 )


(* ---------------------------------------------------------------------- *)

let tcp_tests = []

let udp_tests = (List.map test1 all_sock_flavours) @ (List.map test1a all_sock_flavours) @ (List.map test2 all_sock_flavours)
                  @ (List.map test3 all_sock_flavours) @ (List.map test3a all_sock_flavours) @ (List.map test4 all_sock_flavours)
                  @ (List.map test5 all_sock_flavours) @ (all_sf_af_pf test1b all_sock_flavours [REMOTE_IP; BOGUS_IP] [PRIVILEGED_PORT; KNOWN_PORT])
                  @ (all_sf_af_pf test1c all_sock_flavours [REMOTE_IP; BOGUS_IP] [PRIVILEGED_PORT; KNOWN_PORT])
                  @ (all_sf_af_pf test2a all_sock_flavours [REMOTE_IP; BOGUS_IP] [PRIVILEGED_PORT; KNOWN_PORT])
                  @ (all_sf_af_pf test6a all_sock_flavours [REMOTE_IP; BOGUS_IP] [PRIVILEGED_PORT; KNOWN_PORT])
                  @ (all_sf_af_pf test7a all_sock_flavours [REMOTE_IP; BOGUS_IP] [PRIVILEGED_PORT; KNOWN_PORT])
                  @ (all_sf_af_pf test8 [sf_IPUU] [REMOTE_IP; BOGUS_IP] [PRIVILEGED_PORT; KNOWN_PORT]) @ (all_sf_af_pf test9 [sf_IPUU] [REMOTE_IP; BOGUS_IP] [PRIVILEGED_PORT; KNOWN_PORT])

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests


(* ---------------------------------------------------------------------- *)

let do_send_to_tests handle hosts_list test_type =
  begin_next_test_group handle "send() for UDP";
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
	    if(!num_of_tests = 10) then
	      let _ = num_of_tests := 1 in
	      ntp_update 60.0; in
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
