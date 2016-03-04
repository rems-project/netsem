(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: accept()                            *)
(* Steve Bishop - Created 20030430                                        *)
(* $Id: accept.ml,v 1.25 2006/08/17 10:28:24 tjr22 Exp $ *)
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
open Holtypes
open Holparselib
open Common
open Dual
open Dualdriven
open Common_udp
open Dualdriven_udp
open Testscommon
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) setfflag_call);
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a listening non-blocking socket, with one connection waiting, call accept() to remove the connection from the queue of accepted connections",
  ((true, false), true, true, false),
  ((true, false), true, true, false)


let test2 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) setfflag_call);
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let aux_fd2 = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call_async (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in

    (* Put another connection on the connection queue *)
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd2, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call_async (the ts.ah_libd_hnd) connect_call)) in

    let thread = Thread.create thread_body () in
    delay 3.00;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a listening non-blocking socket, with two connections waiting, call accept() to remove a connection from the queue of accepted connections",
  ((true, false), true, true, false),
  ((true, false), true, true, false))


let test3 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) setfflag_call);
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a listening non-blocking socket, with no connections waiting, call accept()",
  ((true, false), true, true, false),
  ((false, false), false, false, false))


let test4 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a listening blocking socket, with one connection waiting, call accept() to remove a connection from the queue of accepted connections",
  ((true, false), true, true, false),
  ((true, false), true, true, false))


let test5 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let aux_fd2 = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call_async (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in

    (* Put another connection on the connection queue *)
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd2, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call_async (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 3.00;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a listening blocking socket, with two connections waiting, call accept() to remove a connection from the queue of accepted connections",
  ((true, false), true, true, false),
  ((true, false), true, true, false))


let test6 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in

    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call_async (the ts.th_libd_hnd) accept_call);
    delay 5.00),
  "accept(): for a listening blocking socket, with no connections waiting, call accept()",
  ((true, false), true, true, false),
  ((false, false), false, false, false))


let test7 =
  function (st, str) ->
    (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) setfflag_call);
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call);
    rst_driven_socket ts id fd last_dg),
    "accept(): for a non-blocking socket in state " ^ str ^ ", call accept()",
    ((true, false), true, true, false),
    ((false, false), false, false, true)


let test8 =
  function (st, str) ->
     (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call);
    rst_driven_socket ts id fd last_dg),
    "accept(): for a blocking socket  in state " ^ str ^ ", call accept()",
    ((true, false), true, true, false),
    ((false, false), false, false, true)


let test9 =
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) setfflag_call);
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Exhaust process fds *)
    exhaust_proc_fds ts id;

    (* Put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a non-blocking listening socket with one connection waiting and with all the process file descriptors exhausted, call accept()",
  ((true, false), true, true, false),
  ((true, false), true, true, false)


let test10 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) setfflag_call);
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Exhaust process fds *)
    exhaust_proc_fds ts id;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a non-blocking listening socket with no connections waiting and with all the process file descriptors exhausted, call accept()",
  ((true, false), true, true, false),
  ((false, false), false, false, false))


let test11 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Exhaust process fds *)
    exhaust_proc_fds ts id;

    (* Put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a blocking listening socket with one connection waiting and with all the process file descriptors exhausted, call accept()",
  ((true, false), true, true, false),
  ((true, false), true, true, false))


let test12 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in

    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Exhaust process fds *)
    exhaust_proc_fds ts id;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call_async (the ts.th_libd_hnd) accept_call);
    delay 5.00),
  "accept(): for a blocking listening socket with no connections waiting and with all the process file descriptors exhausted, call accept()",
  ((true, false), true, true, false),
  ((false, false), false, false, false))

let test13 =
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) setfflag_call);
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Exhaust process fds *)
    exhaust_proc_fds ts id;

    (* Put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a non-blocking listening socket with one connection waiting and with all the system-wide file descriptors exhausted, call accept()",
  ((true, false), true, true, false),
  ((true, false), true, true, false)


let test14 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) setfflag_call);
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Exhaust process fds *)
    exhaust_proc_fds ts id;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a non-blocking listening socket with no connections waiting and with all the system-wide file descriptors exhausted, call accept()",
  ((true, false), true, true, false),
  ((false, false), false, false, false))


let test15 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Exhaust process fds *)
    exhaust_proc_fds ts id;

    (* Put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a blocking listening socket with one connection waiting and with all the system-wide file descriptors exhausted, call accept()",
  ((true, false), true, true, false),
  ((true, false), true, true, false))


let test16 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in

    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Exhaust process fds *)
    exhaust_proc_fds ts id;

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call_async (the ts.th_libd_hnd) accept_call);
    delay 5.00),
  "accept(): for a blocking listening socket with no connections waiting and with all the system-wide file descriptors exhausted, call accept()",
  ((true, false), true, true, false),
  ((false, false), false, false, false))

(* ---------------------------------------------------------------------- *)

let test17 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* A slurper callback function that signals a condition once the host *)
    (* has sent out its SYN,ACK in response to a SYN *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if datagram.sYN  && datagram.aCK &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let syn_ack_datagram = {
	      datagram with is1 = datagram.is2; is2 = datagram.is1;
				ps1 = datagram.ps2; ps2 = datagram.ps1;
				aCK = true; pSH = false; rST = false;
				sYN = false; fIN = false;
				seq = datagram.ack; ack = datagram.seq +. (uint 1)
			      }	in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_datagram));
	    let rst_datagram = {
	       datagram with is1 = datagram.is2; is2 = datagram.is1;
				ps1 = datagram.ps2; ps2 = datagram.ps1;
				aCK = true; pSH = false; rST = true;
				sYN = false; fIN = false;
				seq = datagram.ack; ack = datagram.seq +. (uint 1)
			      }	in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(rst_datagram))
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_datagram = {
      is1 = Some(hol_ip id.virtual_host_ip);
      is2 = Some(hol_ip id.test_host.test_ip_address);
      ps1 = Some(uint id.virtual_host_port);
      ps2 = Some(uint id.test_host.test_ephm_port);
      seq = uint 5000;
      ack = uint 0;
      uRG = false;
      aCK = false;
      pSH = false;
      rST = false;
      sYN = true;
      fIN = false;
      win = uint 1024;
      urp = uint 0;
      mss = None;
      scale = None;
      ts = None;
      data = []
    } in

    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_datagram));

    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call);
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd),
  "accept(): for a blocking listening socket, call accept() to accept a connection that is aborted whilst on listen queue",
  ((true, false), true, true, false),
  ((false, false), false, false, true))

let test18 = (
  function (sf,sfdescr) ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
      ignore(libd_call (the ts.th_libd_hnd) accept_call);
      rst_udp_socket id ts fd),
     "accept(): for a UDP socket with bound quad " ^ sfdescr ^ ", call accept() and expect to fail",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )

let test19 = (
  function id -> function ts ->
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some(mk_ip id.test_host.test_ip_address))
	(Some(mk_port id.test_host.test_ephm_port)) in
    let listen_call = (tid_of_int_private 0, LISTEN(fd,3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;

    (* shut socket down for reading *)
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,true,false)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);

    (* put another connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;

    (* Accept the first connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call);
    (* Accept the second *)
    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a listening blocking socket, put a connection on the queue, call shutdown(_,true,false), put another connection on, then call accept() twice",
  nts_to_ts {libd=true; libd_is_p=false; slurper=true; holtcpcb=true; injector=false},
  nts_to_ts {libd=true; libd_is_p=false; slurper=true; holtcpcb=false; injector=false}

(* this test has been temporarily disabled because it fails for some reason
   we don't really understand---old records show that the second accept()
   call used to return ECONNABORTED, but running it now appears to hang
   indefinitely (bug?) --amgb *)

(*
let test20 = (
  function id -> function ts ->
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some(mk_ip id.test_host.test_ip_address))
	(Some(mk_port id.test_host.test_ephm_port)) in
    let listen_call = (tid_of_int_private 0, LISTEN(fd,3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;

    (* shut socket down for writing *)
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,false,true)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);

    (* put another connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;

    (* Accept the first connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call);
    (* Accept the second *)
    (* Here's a super fugly hack because it seems that sometimes, for reasons
       we don't understand and aren't investigating right now, the next call
       may or may not block. So, we just see if it returns within 30s, and
       if it doesn't, we end the test. I don't *think* this will leave autotest
       in a broken state for the next test --amgb *)

    ignore(libd_call (the ts.th_libd_hnd) accept_call)),
  "accept(): for a listening blocking socket, put a connection on the queue, call shutdown(_,false,true), put another connection on, then call accept() twice",
  ((true,false),true,true,false),
  ((true,false),false,false,false)
*)

(* ---------------------------------------------------------------------- *)

let driven_states =
  let rec remove_listen_state driven_list =
    match driven_list with
      [] -> []
    | (ST_LISTEN,y)::xs -> remove_listen_state xs
    | (x,y)::xs -> (x,y)::(remove_listen_state xs) in
  remove_listen_state all_interesting_driven_states

let test_from_all_states =
  (List.map test7 driven_states) @ (List.map test8 driven_states)

let tcp_tests = [test1; test2; test3; test4; test5; test6]
  @ test_from_all_states @ [test17; test19(*; test20*)]

let udp_tests = List.map test18 bound_udp_quads

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = [test9; test10; test11; test12; test13; test14; test15; test16]
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = [test1;test2;test3;test4;test5;test6;test19(*;test20*)]
let stream_exhaustive_tests = tcp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_accept_tests handle hosts_list test_type =
  begin_next_test_group handle "accept()";
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
		  aux_host_tools = ahts;
		  aux_host_bound = [];
		} in

		let ts = dual_tthee_init id debug_OFF !tthee_baseport_1
		    !tthee_baseport_2 !merger_delta in
		let _ =
		  try test_thunk id ts
		  with e -> report_test_failure handle descr e
		in

		dual_tthee_cleanup ts;
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
