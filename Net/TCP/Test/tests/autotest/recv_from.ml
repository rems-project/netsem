(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: recv() UDP                          *)
(* Matthew Fairbairn - Created 20040118                                   *)
(* $Id: recv_from.ml,v 1.10 2006/06/19 11:57:45 amgb2 Exp $ *)
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

let test_msg = [uint(Char.code 'T'); uint(Char.code 'e'); uint(Char.code 's');
		uint(Char.code 'T');]

let test_msg2 = [uint(Char.code 'b'); uint(Char.code 'l'); uint(Char.code 'a');
		uint(Char.code 'h');]

(* ---------------------------------------------------------------------- *)

let test1 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd,[O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 2, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      get_bound_state_udp (the ts.th_libd_hnd) fd),
    "recv() -- for a non-blocking UDP socket with binding quad " ^ string_of_bound_udp_quad sf ^ ", call recv() (should fail) - test1",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )

let test1a = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd,[O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,true,false)) in
      ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 2, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)),
    "recv() -- for a non-blocking UDP socket that has been shutdown for reading, with binding quad " ^ string_of_bound_udp_quad sf ^ ", call recv() (should fail) - test1a",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )


let test1b = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      let t = Thread.create (function () ->
	let recv_call = (tid_of_int_private 0, RECV(fd, 2, [MSG_DONTWAIT])) in
	ignore(libd_call (the ts.th_libd_hnd) recv_call)) () in
      delay 15.00;
      injector_inject (the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 3.0;
      rst_udp_socket id ts fd),
    "recv() -- for a UDP socket with binding quad " ^ string_of_bound_udp_quad sf ^ ", call recv() with MSG_DONTWAIT set (should fail) - test1b",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )


let test1c = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,true,false)) in
      ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 2, [MSG_DONTWAIT])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)),
    "recv() -- for a UDP socket that has been shutdown for reading, with binding quad " ^ string_of_bound_udp_quad sf ^ ", call recv() with MSG_DONTWAIT set (should fail) - test1c",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )

let test2 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 10.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,3,[MSG_OOB])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)),
     "recv() -- for a UDP socket with binding quad " ^ string_of_bound_udp_quad sf ^ ", call recv() with the MSG_OOB flag set (should fail) - test2",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test2a = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 3.0;
      let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,true,false)) in
      ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
      let recv_call = (tid_of_int_private 0, RECV(fd,3,[MSG_OOB])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)),
     "recv() -- for a UDP socket that has been shutdown for reading, with binding quad " ^ string_of_bound_udp_quad sf ^ ", call recv() with the MSG_OOB flag set (should fail) - test2a",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test2b = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 3.0;
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd,[O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let recv_call = (tid_of_int_private 0, RECV(fd, 2, [MSG_OOB])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)),
    "recv() -- for a non-blocking UDP socket with binding quad " ^ string_of_bound_udp_quad sf ^ ", call recv() with MSG_OOB set (should fail) - test2b",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )

let test3 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let local_port = get_real_port id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 3.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,4,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
     "recv() -- for a blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " attempt to recv() some data - test3",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test3a = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 3.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,2,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
     "recv() -- for a blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " attempt to recv() some data, but not all of the available data - test3a",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test3b = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 3.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,4,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
     "recv() -- for a blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " attempt to recv() more data than is available - test3b",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test3c = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      let t = Thread.create (function () ->
	let recv_call = (tid_of_int_private 0, RECV(fd,4,[])) in
	ignore(libd_call (the ts.th_libd_hnd) recv_call)) () in
      delay 5.0;
      injector_inject (the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 5.0;
      rst_udp_socket id ts fd),
     "recv() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " attempt to recv some data - should block and then receive the data - test3c",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )


let test4 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      (* wait a bit *)
      delay 3.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,4,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
     "recv() -- for a non-blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " attempt to recv() some data - test4",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test4a = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      (* wait a bit *)
      delay 3.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,20,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
     "recv() -- for a non-blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " attempt to recv() some data, more than there is available - test4a",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test5 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      let packet_to_inject2 = {udp_hol_is1 = fip;
			       udp_hol_ps1 = fp;
			       udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			       udp_hol_ps2 = local_port;
			       udp_hol_data = test_msg2} in
      (* wait a bit *)
      delay 3.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,4,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject2));
      delay 3.0;
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
     "recv() -- for a non-blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " send a packet from auxillary host, make a recv() call, then send another packet and make another recv() call - test5",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test5a = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      let packet_to_inject2 = {udp_hol_is1 = fip;
			       udp_hol_ps1 = fp;
			       udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			       udp_hol_ps2 = local_port;
			       udp_hol_data = test_msg2} in
      (* wait a bit *)
      delay 3.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,2,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject2));
      delay 3.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,4,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
     "recv() -- for a non-blocking UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " send a packet from auxillary host, make a recv() call but don't get all the data, then send another packet and make another recv() call - test5a",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test6 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      let t = Thread.create (function () ->
	let recv_call = (tid_of_int_private 0, RECV(fd,0,[])) in
	ignore(libd_call (the ts.th_libd_hnd) recv_call)) () in
      delay 15.00;
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 3.0;
      rst_udp_socket id ts fd),
     "recv() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " call recv() on an empty receive queue - test6",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test7 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      let packet_to_inject2 = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg2} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      injector_inject (the ts.th_injector_hnd) (UDPMSG(packet_to_inject2));
      delay 5.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,4,[MSG_PEEK])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let recv_call = (tid_of_int_private 0, RECV(fd,4,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
     "recv() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " with two packets in the rcvq, call recv with MSG_PEEK set, then call it again without MSG_PEEK set - test7",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

let test8 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let local_port = get_real_port id ts sf in
      let fp = get_foreign_port id ts sf in
      let fip = get_foreign_ip id ts sf in
      let packet_to_inject = {udp_hol_is1 = fip;
			      udp_hol_ps1 = fp;
			      udp_hol_is2 = Some(hol_ip id.test_host.test_ip_address);
			      udp_hol_ps2 = local_port;
			      udp_hol_data = test_msg} in
      injector_inject(the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      let recv_call = (tid_of_int_private 0, RECV(fd,4,[MSG_WAITALL])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      rst_udp_socket id ts fd),
     "recv() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " with a packet in the rcvq, call recv() with MSG_WAITALL set - test8",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

(*

(* removing this test because at the moment libd can't cope with it -- that is,
   our libd is single-threaded, so it can't deal with making a call in one
   thread while waiting for a call in another thread to return. at the moment,
   running this test causes autotest to hang --amgb *)

(* 20060619 -- if we ever want to fix these, looks like it could be done by
   changing some libd_calls to libd_call_asyncs --amgb *)

let test9 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let t = Thread.create (function () ->
	let recv_call = (tid_of_int_private 0, RECV(fd,2,[])) in
	ignore(libd_call (the ts.th_libd_hnd) recv_call)) () in
print_endline "after forking thread";
      delay 3.0;
      let send_call = (tid_of_int_private 1, SEND(fd,None,"blah",[])) in
print_endline "making libd call";
      ignore(libd_call (the ts.th_libd_hnd) send_call);
print_endline "after calling send()";
      delay 5.0;
      rst_udp_socket id ts fd),
     "recv() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ " call recv() on an empty recv queue then in a different thread send a datagram out to generate an error on the socket",
     ((true,true),true,false,false),
     ((false,false),false,false,true))
 )

*)

(* ---------------------------------------------------------------------- *)

let tcp_tests = []

let recv_real = [sf_IPUU; sf_IPIU; sf_IPIP]

let udp_tests = (List.map test1 all_sock_flavours) @ (List.map test2 recv_real) @ (List.map test3 recv_real) @  (List.map test4 recv_real)
                 @ (List.map test1a all_sock_flavours) @ (List.map test1b recv_real) @ (List.map test1c all_sock_flavours) @ (List.map test2a all_sock_flavours)
                 @ (List.map test2b all_sock_flavours) @ (List.map test3a recv_real) @ (List.map test3b recv_real) @ (List.map test4a recv_real) @ (List.map test5 recv_real) @ (List.map test7 recv_real) @ (List.map test8 recv_real) @ (List.map test3 recv_real) @ (List.map test6 recv_real) (*@ (List.map test9 all_sock_flavours)*)

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_recv_from_tests handle hosts_list test_type =
  begin_next_test_group handle "recvfrom()";
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
	      ntp_update 10.0; in
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
		  aux_host_tools = ahts;
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
