(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: deliver_icmp                        *)
(* Matthew Fairbairn - Created 20040419                                   *)
(* $Id: deliver_icmp.ml,v 1.6 2006/06/07 11:52:45 amgb2 Exp $               *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread
open Printf

(* Our libraries *)
open Nettypes
open Tthee
open Ttheehelper
open Holtypes
open Holparselib
open Ocamllib
open Libcalls
open Common
open Dual
open Dualdriven
open Common_udp
open Dualdriven_udp
open Testscommon
(* ---------------------------------------------------------------------- *)

let test1 =
  function sf -> (
    (function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let send_call = (tid_of_int_private 0, SEND(fd,None,"ICMP Test",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      delay 10.0;
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      rst_udp_socket id ts fd),
    "deliver_icmp -- for a UDP socket with binding quad, "^(string_of_bound_udp_quad sf)^", send a datagram, wait for an ICMP, then attempt to send again",
    ((true,false),true,false,false),
    ((false,false),false,false,true))

let test1a =
  function sf -> (
    (function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let send_call = (tid_of_int_private 0, SEND(fd,
						  Some(Ocamllib.ip_of_string (string_ip id.aux_host.test_ip_address),
						       Ocamllib.port_of_int id.aux_host.test_priv_port),"ICMP Test",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      delay 10.0;
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      rst_udp_socket id ts fd),
    "deliver_icmp -- for a UDP socket with binding quad, "^(string_of_bound_udp_quad sf)^", send a datagram with address specified, wait for an ICMP, then attempt to send again",
    ((true,false),true,false,false),
    ((false,false),false,false,true))

let test2 =
  function sf -> (
    (function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let nonblockcall = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblockcall);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"ICMP Test",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      delay 10.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,2,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
    "deliver_icmp -- for a UDP socket with binding quad, "^(string_of_bound_udp_quad sf)^", send a datagram, wait for an ICMP, then call recv()",
    ((true,false),true,false,false),
    ((false,false),false,false,true))


let test2a =
  function sf -> (
    (function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let nonblockcall = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblockcall);
      let send_call = (tid_of_int_private 0, SEND(fd,
						  Some(Ocamllib.ip_of_string (string_ip id.aux_host.test_ip_address),
						       Ocamllib.port_of_int id.aux_host.test_priv_port),"ICMP Test",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      delay 10.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,2,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
    "deliver_icmp -- for a UDP socket with binding quad, "^(string_of_bound_udp_quad sf)^", send a datagram with address specified, wait for an ICMP, then call recv()",
    ((true,false),true,false,false),
    ((false,false),false,false,true))


let test3 =
  function n -> function sf -> (
    (function id -> function ts ->
      let fd_1 = get_bound_socket_reuse_udp id ts sf in
      let fd_2 = get_bound_socket_reuse_udp id ts sf in
      let fd_3 = get_bound_socket_reuse_udp id ts sf in
      let fd_4 = get_bound_socket_reuse_udp id ts sf in
      let fd = if n = 1 then fd_1 else if n=2 then fd_2 else if n=3 then fd_3 else fd_4 in
      let send_call = (tid_of_int_private 0, SEND(fd, None,"ICMP Test", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      delay 10.0;
      let send_call = (tid_of_int_private 0, SEND(fd_1, None,"ICMP FD1", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd_2, None, "ICMP FD2", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd_3, None, "ICMP FD3", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd_4, None,"ICMP FD4", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      rst_udp_socket id ts fd),
    "deliver_icmp -- create 4 UDP sockets with binding quad, "^(string_of_bound_udp_quad sf)^", send a datagram from fd_"^(Int64.to_string (uint n))^", then call send() on each socket",
    ((true,false),true,false,false),
    ((false,false),false,false,true))

let test4 =
  function n -> function sf -> (
    (function id -> function ts ->
      let fd_1 = get_bound_socket_reuse_udp id ts sf in
      let fd_2 = get_bound_socket_reuse_udp id ts sf in
      let fd_3 = get_bound_socket_reuse_udp id ts sf in
      let fd_4 = get_bound_socket_reuse_udp id ts sf in
      let nonblock = (tid_of_int_private 0, SETFILEFLAGS(fd_1, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock);
      let nonblock = (tid_of_int_private 0, SETFILEFLAGS(fd_2, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock);
      let nonblock = (tid_of_int_private 0, SETFILEFLAGS(fd_3, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock);
      let nonblock = (tid_of_int_private 0, SETFILEFLAGS(fd_4, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock);
      let fd = if n = 1 then fd_1 else if n=2 then fd_2 else if n=3 then fd_3 else fd_4 in
      let send_call = (tid_of_int_private 0, SEND(fd, None,"ICMP Test", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      delay 10.0;
      let recv_call = (tid_of_int_private 0, RECV(fd_1, 2, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd_2, 2, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd_3, 2, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd_4, 2, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
    "deliver_icmp -- create 4 UDP sockets with binding quad, "^(string_of_bound_udp_quad sf)^", send a datagram from fd_"^(Int64.to_string (uint n))^", then call recv() on each socket",
    ((true,false),true,false,false),
    ((false,false),false,false,true))

let test5 =
  function n -> function (sf1,sf2,sf3,sf4) -> (
    (function id -> function ts ->
      let fd_1 = get_bound_socket_reuse_udp id ts sf1 in
      let fd_2 = get_bound_socket_reuse_udp id ts sf2 in
      let fd_3 = get_bound_socket_reuse_udp id ts sf3 in
      let fd_4 = get_bound_socket_reuse_udp id ts sf4 in
      let fd = if n = 1 then fd_1 else if n=2 then fd_2 else if n=3 then fd_3 else fd_4 in
      let sendcall = (tid_of_int_private 0, SEND(fd,None,"ICMP Test", [])) in
      ignore(libd_call (the ts.th_libd_hnd) sendcall);
      delay 10.0;
      let sendcall = (tid_of_int_private 0, SEND(fd_1,None,"ICMP1",[])) in
      ignore(libd_call (the ts.th_libd_hnd) sendcall);
      let sendcall = (tid_of_int_private 0, SEND(fd_2,None,"ICMP2",[])) in
      ignore(libd_call (the ts.th_libd_hnd) sendcall);
      let sendcall = (tid_of_int_private 0, SEND(fd_3,None,"ICMP3",[])) in
      ignore(libd_call (the ts.th_libd_hnd) sendcall);
      let sendcall = (tid_of_int_private 0, SEND(fd_4,None,"ICMP4",[])) in
      ignore(libd_call (the ts.th_libd_hnd) sendcall);
      rst_udp_socket id ts fd),
    "deliver_icmp -- create 4 UDP sockets with binding quads: "^(string_of_bound_udp_quad sf1)^", "^(string_of_bound_udp_quad sf2)^", "^(string_of_bound_udp_quad sf3)^", "^(string_of_bound_udp_quad sf4)^". Call send() from fd_"^(Int64.to_string (uint n))^", then call send() on each socket",
    ((true,false),true,false,false),
    ((false,false),false,false,true))

let test6 =
  function n -> function (sf1,sf2,sf3,sf4) -> (
    (function id -> function ts ->
      let fd_1 = get_bound_socket_reuse_udp id ts sf1 in
      let fd_2 = get_bound_socket_reuse_udp id ts sf2 in
      let fd_3 = get_bound_socket_reuse_udp id ts sf3 in
      let fd_4 = get_bound_socket_reuse_udp id ts sf4 in
      let nonblock = (tid_of_int_private 0, SETFILEFLAGS(fd_1, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock);
      let nonblock = (tid_of_int_private 0, SETFILEFLAGS(fd_2, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock);
      let nonblock = (tid_of_int_private 0, SETFILEFLAGS(fd_3, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock);
      let nonblock = (tid_of_int_private 0, SETFILEFLAGS(fd_4, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock);
      let fd = if n = 1 then fd_1 else if n=2 then fd_2 else if n=3 then fd_3 else fd_4 in
      let sendcall = (tid_of_int_private 0, SEND(fd,None,"ICMP Test", [])) in
      ignore(libd_call (the ts.th_libd_hnd) sendcall);
      delay 10.0;
      let recv_call = (tid_of_int_private 0, RECV(fd_1, 2, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd_2, 2, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd_3, 2, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd_4, 2, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
    "deliver_icmp -- create 4 UDP sockets with binding quads: "^(string_of_bound_udp_quad sf1)^", "^(string_of_bound_udp_quad sf2)^", "^(string_of_bound_udp_quad sf3)^", "^(string_of_bound_udp_quad sf4)^". Call send() from fd_"^(Int64.to_string (uint n))^", then call send() on each socket",
    ((true,false),true,false,false),
    ((false,false),false,false,true))


let test7 =
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let lp = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let pac = {
	udp_hol_is1 = fip;
	udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
	udp_hol_ps1 = fp;
	udp_hol_ps2 = lp;
	udp_hol_data = [uint(Char.code 'I')]
      } in
      injector_inject (the ts.th_injector_hnd) (UDPMSG(pac));
      delay 5.0;
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd,[O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let send_call = (tid_of_int_private 0, SEND(fd, None, "Blah", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      delay 5.0;
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
    "deliver_icmp -- for UDP socket with binding quad "^(string_of_bound_udp_quad sf)^", inject a packet, call send() to generate an ICMP then call recv() when there is data available, and then call it again",
    ((true,false),true,false,false),
    ((false,false),false,false,true)
   )

let test8 =
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let lp = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let pac = {
	udp_hol_is1 = fip;
	udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
	udp_hol_ps1 = fp;
	udp_hol_ps2 = lp;
	udp_hol_data = [uint(Char.code 'I')]
      } in
      injector_inject (the ts.th_injector_hnd) (UDPMSG(pac));
      delay 5.0;
      injector_inject (the ts.th_injector_hnd) (UDPMSG(pac));
      delay 5.0;
      injector_inject (the ts.th_injector_hnd) (UDPMSG(pac));
      delay 5.0;
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd,[O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let send_call = (tid_of_int_private 0, SEND(fd, None, "Blah", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      delay 5.0;
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      injector_inject (the ts.th_injector_hnd) (UDPMSG(pac));
      delay 5.0;
      injector_inject (the ts.th_injector_hnd) (UDPMSG(pac));
      delay 5.0;
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let send_call = (tid_of_int_private 0, SEND(fd, None, "Blah", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      delay 5.0;
      injector_inject (the ts.th_injector_hnd) (UDPMSG(pac));
      delay 5.0;
      injector_inject (the ts.th_injector_hnd) (UDPMSG(pac));
      delay 5.0;
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
    "deliver_icmp -- for UDP socket with binding quad "^(string_of_bound_udp_quad sf)^", inject some packets, and call send() to generate ICMPs several times, with recv() calls made as well",
    ((true,false),true,false,false),
    ((false,false),false,false,true)
   )



(* ---------------------------------------------------------------------- *)

let tcp_tests = []

let udp_tests = (List.map test1 all_sock_flavours) @ (List.map test1a all_sock_flavours) @
                (List.map test2 all_sock_flavours) @ (List.map test2a all_sock_flavours) @
                (List.map (test3 1) all_sock_flavours) @ (List.map (test3 2) all_sock_flavours) @
	        (List.map (test3 2) all_sock_flavours) @ (List.map (test3 4) all_sock_flavours) @
                (List.map (test4 1) all_sock_flavours) @ (List.map (test4 2) all_sock_flavours) @
		(List.map (test4 3) all_sock_flavours) @ (List.map (test4 4) all_sock_flavours) @
                (List.map (test5 1) [(sf_IPUU,sf_IPUU,sf_IPIU,sf_IPIU);(sf_IPUU,sf_IPUU,sf_IPUU,sf_IPIU);
				     (sf_IPIU,sf_IPIU,sf_IPIP,sf_IPIP)]) @
                (List.map (test5 2) [(sf_IPUU,sf_IPUU,sf_IPIU,sf_IPIU);(sf_IPUU,sf_IPUU,sf_IPUU,sf_IPIU);
				     (sf_IPIU,sf_IPIU,sf_IPIP,sf_IPIP)]) @
                (List.map (test5 3) [(sf_IPUU,sf_IPUU,sf_IPIU,sf_IPIU);(sf_IPUU,sf_IPUU,sf_IPUU,sf_IPIU);
				     (sf_IPIU,sf_IPIU,sf_IPIP,sf_IPIP)]) @
                (List.map (test5 4) [(sf_IPUU,sf_IPUU,sf_IPIU,sf_IPIU);(sf_IPUU,sf_IPUU,sf_IPUU,sf_IPIU);
				     (sf_IPIU,sf_IPIU,sf_IPIP,sf_IPIP)]) @
                (List.map (test6 1) [(sf_IPUU,sf_IPUU,sf_IPIU,sf_IPIU);(sf_IPUU,sf_IPUU,sf_IPUU,sf_IPIU);
				     (sf_IPIU,sf_IPIU,sf_IPIP,sf_IPIP)]) @
                (List.map (test6 2) [(sf_IPUU,sf_IPUU,sf_IPIU,sf_IPIU);(sf_IPUU,sf_IPUU,sf_IPUU,sf_IPIU);
				     (sf_IPIU,sf_IPIU,sf_IPIP,sf_IPIP)]) @
                (List.map (test6 3) [(sf_IPUU,sf_IPUU,sf_IPIU,sf_IPIU);(sf_IPUU,sf_IPUU,sf_IPUU,sf_IPIU);
				     (sf_IPIU,sf_IPIU,sf_IPIP,sf_IPIP)]) @
                (List.map (test6 4) [(sf_IPUU,sf_IPUU,sf_IPIU,sf_IPIU);(sf_IPUU,sf_IPUU,sf_IPUU,sf_IPIU);
				     (sf_IPIU,sf_IPIU,sf_IPIP,sf_IPIP)]) @
                (List.map test7 all_sock_flavours) @ (List.map test8 all_sock_flavours)


let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests


(* ---------------------------------------------------------------------- *)

let do_deliver_icmp_tests handle hosts_list test_type =
  begin_next_test_group handle "deliver_icmp";
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
