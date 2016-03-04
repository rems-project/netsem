(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: bind() for UDP                     *)
(* Matthew Fairbairn - Created 20040114                                  *)
(* $Id: bind_udp.ml,v 1.9 2006/06/07 11:52:45 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

open Thread

(* Our libraries *)
open Tthee
open Ttheehelper
open Ocamllib
open Libcalls
open Common
open Simple
open Dual
open Common_udp
open Dualdriven_udp
open Testscommon
(* ---------------------------------------------------------------------- *)
(* Testing of bind() *)
(* ---------------------------------------------------------------------- *)

let test1 = (
  function sf -> function af -> function pf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let port = get_port_udp pf id ts in
      let ip = get_ip_udp af id ts in
      let _ = match pf with
	UNAVAILABLE_PORT ->
	  (* create a new socket and bind to this port first *)
	  let fd_tmp = get_socket_udp (the ts.th_libd_hnd) in
	  let bind_call = (tid_of_int_private 0, BIND(fd_tmp,ip,port)) in
	  ignore(libd_call (the ts.th_libd_hnd) bind_call);
	  get_bound_state_udp (the ts.th_libd_hnd) fd_tmp
      | _ -> () in
      let bind_call = (tid_of_int_private 0, BIND(fd,ip,port)) in
      ignore(libd_call (the ts.th_libd_hnd) bind_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
    "bind() -- call bind(fd," ^ (string_of_ip_flavour af) ^ ", " ^ (string_of_port_flavour pf) ^ ") on un-privileged UDP socket with bound quad " ^ (string_of_bound_udp_quad sf),
    ((true,false),true,false,false),
    ((false,false),false,false,true))
 )

let test2 = (
  function sf -> function af -> function pf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let port = get_port_udp pf id ts in
      let ip = get_ip_udp af id ts in
      let _ = match pf with
	UNAVAILABLE_PORT ->
	  (* creat a new socket and bind to this port first *)
	  let fd_tmp = get_socket_udp (the ts.th_libd_hnd) in
	  let bind_call = (tid_of_int_private 0, BIND(fd_tmp,ip,port)) in
	  ignore(libd_call (the ts.th_libd_hnd) bind_call);
	  get_bound_state_udp (the ts.th_libd_hnd) fd_tmp
      | _ -> () in
      let bind_call = (tid_of_int_private 0, BIND(fd,ip,port)) in
      ignore(libd_call (the ts.th_libd_hnd) bind_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
     "bind() -- call bind(fd, " ^ (string_of_ip_flavour af) ^ ", " ^ (string_of_port_flavour pf) ^ ") on privileged UDP socket with bound quad " ^ (string_of_bound_udp_quad sf),
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test3 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let bind_call = (tid_of_int_private 0, BIND(fd, Some(Ocamllib.ip_of_string (string_ip id.aux_host.test_ip_address)), Some(Ocamllib.port_of_int id.aux_host.test_ephm_port))) in
      ignore(libd_call (the ts.th_libd_hnd) bind_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd),
     "bind() -- for a UDP socket with bound quad " ^ (string_of_bound_udp_quad sf) ^ ", call bind() on an IP address not on the local machine",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )

let test4 = (
  function sf -> function af -> function pf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let ip = get_ip_udp af id ts in
      let port = get_port_udp pf id ts in
      let auxfd = get_socket_udp (the ts.th_libd_hnd) in
      let bind_call = (tid_of_int_private 0, BIND(auxfd, ip, port)) in
      ignore(libd_call (the ts.th_libd_hnd) bind_call);
      get_bound_state_udp (the ts.th_libd_hnd) auxfd;
      let bind_call = (tid_of_int_private 0, BIND(fd, ip, port)) in
      ignore(libd_call (the ts.th_libd_hnd) bind_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts auxfd;
      rst_udp_socket id ts fd),
     "bind() -- for a UDP socket with bound quad " ^ (string_of_bound_udp_quad sf) ^ ", call bind(ip,port) on two different sockets",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )


let udp_tests = (all_sf_af_pf test1 all_sock_flavours all_address_flavours all_port_flavours) @ (all_sf_af_pf test2 all_sock_flavours all_address_flavours [PRIVILEGED_PORT]) @ (List.map test3 all_sock_flavours)

let tcp_tests = []

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_bind_udp_tests handle hosts_list test_type =
  begin_next_test_group handle "bind() for UDP";
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
	      let _ = num_of_tests := 0 in
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
