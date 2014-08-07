(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: listen()                            *)
(* Steve Bishop - Created 20030430                                        *)
(* $Id: listen.ml,v 1.27 2006/06/19 15:46:55 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread
open Printf

(* Our libraries *)
open Nettypes
open Holtypes
open Holparselib
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

let syn_segment = {
  is1 = None; is2 = None;
  ps1 = None; ps2 = None;
  seq = uint 5000;
  ack = uint 0;
  uRG = false; aCK = false;
  pSH = false; rST = false;
  sYN = true;  fIN = false;
  win = uint 0; urp = uint 0;
  mss = None; scale = None;
  ts = None; data = []
}

let test1 = (
  (function id -> function ts ->
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call)),
  "listen() --  get a fresh bound socket, call listen() with a backlog of 3 and call getsockname()/getpeername() to report the status of the socket",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test2 = (
  (function id -> function ts ->
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	None (Some (mk_port id.test_host.test_ephm_port)) in
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call)),
  "listen() --  get a fresh socket bound only to a port, call listen() with a backlog of 3 and call getsockname()/getpeername() to report the status of the socket",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test3 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call)),
  "listen() --  get a fresh unbound socket, call listen() with a backlog of 3 (which should fail) and call getsockname()/getpeername() to report the status of the socket",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
  )

let test5 = (
  (function id -> function ts ->
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    let listen_call = (tid_of_int_private 0, LISTEN(fd, id.test_host.so_max_conns + 1)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call)),
  "listen() --  get a fresh bound socket, call listen() with a backlog value greater than the maximum allowed and call getsockname()/getpeername() to report the status of the socket",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )


let test6 = (
  (function id -> function ts ->
    let fd1 = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    let fd2 = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    let listen_call = (tid_of_int_private 0, LISTEN(fd1, 1)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd2, 1)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd1)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd1)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd2)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call)),
  "listen() --  get two fresh sockets bound to the same ip/port and attempt to listen() on both",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test6a = (
  (function id -> function ts ->
    let fd1 = get_socket (the ts.th_libd_hnd) in
    let fd2 = get_socket (the ts.th_libd_hnd) in
    let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd1,SO_REUSEADDR,true)) in
    ignore(libd_call (the ts.th_libd_hnd) reuse_call);
    let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd2,SO_REUSEADDR,true)) in
    ignore(libd_call (the ts.th_libd_hnd) reuse_call);
    let bind_call = (tid_of_int_private 0, BIND(fd1,None,Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    let bind_call = (tid_of_int_private 0, BIND(fd2,None,Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd1,3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd2,3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call)),
  "listen () -- get two fresh sockets bound to (NONE,ephm_port) and attempt to listen() on both",
  ((true,false),true,true,false),
  ((false,false),false,false,false)
 )

let test6b = (
  (function id -> function ts ->
    let fd1 = get_socket (the ts.th_libd_hnd) in
    let fd2 = get_socket (the ts.th_libd_hnd) in
    let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd1,SO_REUSEADDR,true)) in
    ignore(libd_call (the ts.th_libd_hnd) reuse_call);
    let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd2,SO_REUSEADDR,true)) in
    ignore(libd_call (the ts.th_libd_hnd) reuse_call);
    let bind_call = (tid_of_int_private 0, BIND(fd1,Some(mk_ip id.test_host.test_ip_address),Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    let bind_call = (tid_of_int_private 0, BIND(fd2,None,Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd1,3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd2,3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call)),
  "listen () -- get two fresh sockets, one bound to (None,port) the other to (test_ip_address,port) and attempt to listen() on both",
  ((true,false),true,true,false),
  ((false,false),false,false,false)
 )


let test6c = (
  (function id -> function ts ->
    let fd1 = get_socket (the ts.th_libd_hnd) in
    let fd2 = get_socket (the ts.th_libd_hnd) in
    let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd1,SO_REUSEADDR,true)) in
    ignore(libd_call (the ts.th_libd_hnd) reuse_call);
    let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd2,SO_REUSEADDR,true)) in
    ignore(libd_call (the ts.th_libd_hnd) reuse_call);
    let bind_call = (tid_of_int_private 0, BIND(fd1,Some(mk_ip id.test_host.test_ip_address),Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    let bind_call = (tid_of_int_private 0, BIND(fd2,Some(mk_ip id.test_host.test_ip_address),Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd1,3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd2,3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call)),
  "listen () -- get two fresh sockets bound to (ip_address,ephm_port) and attempt to listen() on both",
  ((true,false),true,true,false),
  ((false,false),false,false,false)
 )

let test6d = (
  (function id -> function ts ->
    let fd1 = get_socket (the ts.th_libd_hnd) in
    let fd2 = get_socket (the ts.th_libd_hnd) in
    let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd1,SO_REUSEADDR,true)) in
    ignore(libd_call (the ts.th_libd_hnd) reuse_call);
    let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd2,SO_REUSEADDR,true)) in
    ignore(libd_call (the ts.th_libd_hnd) reuse_call);
    let bind_call = (tid_of_int_private 0, BIND(fd1,Some(mk_ip id.test_host.test_ip_address),Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    let bind_call = (tid_of_int_private 0, BIND(fd2,Some(mk_ip (127,0,0,1)),Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd1,3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd2,3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call)),
  "listen () -- get two fresh sockets, one bound to (ip_address,ephm_port) and the other to (local_address,ephm_port) and attempt to listen() on both",
  ((true,false),true,true,false),
  ((false,false),false,false,false)
 )


let test7a = (
  (function id -> function ts ->
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 1)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call)),
  "listen() --  get a fresh bound socket that is already listening. Attempt to call listen() again, finally calling getsockname()/getpeername() to report the status of the socket",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test7b = (
  (function id -> function ts ->
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 1)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let listen_call2 = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call2);
    let listen_call3 = (tid_of_int_private 0, LISTEN(fd, 5)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call3);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call)),
  "listen() --  get a fresh bound socket and call listen() multiple times with different backlog values to determine whether updating the backlog value is permitted. Finally call getsockname()/getpeername() to report the status of the socket",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test7c = (
  function (st, str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,false,true)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 1)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call);
    delay 30.00;
    rst_driven_socket ts id fd last_dg),
  "listen() -- for a fresh socket in state " ^ str ^ " that is shutdown for writing, call listen() and finally call getsockname()/getpeername() to report the status of the socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
)

let test7d = (
  function (st, str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,true,false)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 1)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call);
    rst_driven_socket ts id fd last_dg),
  "listen() -- for a fresh socket in state " ^ str ^ " that is shutdown for reading, call listen() and finally call getsockname()/getpeername() to report the status of the socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
)

let test7e = (
  function (shutrd, shutwr) -> (function id -> function ts ->
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,shutrd,shutwr)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 1)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call);
    let syn_segment = { syn_segment with
                        is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port) } in
    let last_dg = RECV_DATAGRAM(syn_segment) in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));
    delay 15.00;
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) setfflag_call);
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call);
    rst_driven_socket ts id fd last_dg),
  "listen() -- for a fresh bound socket, call shutdown(" ^ (if shutrd then "T" else "F") ^ "," ^ (if shutwr then "T" else "F") ^ ") followed by listen() and then call getsockname()/getpeername() to report the status of the socket. The listening socket then receives a SYN segment, and the user calls accept()",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
)

let test8 = (
  function (st, str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 1)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call);
    rst_driven_socket ts id fd last_dg),
  "listen() -- for a fresh socket in state " ^ str ^ ", call listen() and finally call getsockname()/getpeername() to report the status of the socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
)


let test9 =
  (function id -> function ts ->
    let listen_call = (tid_of_int_private 0, LISTEN(fd_of_int_private 1, 1)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call)),
  "listen() -- call listen() on a non-socket file descriptor",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
(* SB this test may not work under Windows due to the reliance on fd1. *)


let test10 = (
  function backlog ->
    (function id -> function ts ->
      let fd = get_local_bound_socket (the ts.th_libd_hnd)
	  (Some (mk_ip id.test_host.test_ip_address))
	  (Some (mk_port id.test_host.test_ephm_port)) in
      let listen_call = (tid_of_int_private 0, LISTEN(fd, 1)) in
      ignore(libd_call (the ts.th_libd_hnd) listen_call);

      let syn_datagram = {
	is1 = Some(hol_ip id.virtual_host_ip);
	ps1 = Some(uint id.virtual_host_port);
	is2 = Some(hol_ip id.test_host.test_ip_address);
	ps2 = Some(uint id.test_host.test_ephm_port);
	seq = uint 1000;
	ack = uint 0;
	sYN = true; aCK = false; rST = false;
	uRG = false; pSH = false; fIN = false;
	urp = uint 0;
	win = uint 8192;
	mss = Some(uint 512);
	scale = None;
	ts = Some(uint 1000, uint 0);
	data = [];
      }	 in

      let rec syn_sender_loop n dg =
	if n=0 then () else
	(let datagram = {dg with seq = dg.seq +. (uint 5000); ps1 = Some(the dg.ps1 +. (uint 1));
			   ts = timestamp_update dg.ts (uint 1) } in
	injector_inject (the ts.th_injector_hnd) (TCPMSG(datagram));
	syn_sender_loop (n-1) datagram)
      in syn_sender_loop 30 syn_datagram;
      rst_driven_socket ts id fd (NO_DATAGRAMS)),
    "listen() --  fresh listening socket with backlog=" ^ (string_of_int backlog) ^ ", attempt to fill incomplete connection queue",
    ((true, false), true, true, false),
    ((false, false), false, false, true))


let test11 = (
  function backlog ->
    (function id -> function ts ->
      let fd = get_local_bound_socket (the ts.th_libd_hnd)
	  (Some (mk_ip id.test_host.test_ip_address))
	  (Some (mk_port id.test_host.test_ephm_port)) in
      let listen_call = (tid_of_int_private 0, LISTEN(fd, 1)) in
      ignore(libd_call (the ts.th_libd_hnd) listen_call);

      let syn_ack_list = ref [] in

      (* A slurper callback function that signals a condition when the *)
      (* required SYN/ACK packets are actually seen on the wire *)
      let slurper_callback_fun holmsg =
	match holmsg with
	  TCPMSG(datagram) ->
	    if datagram.sYN = true && datagram.aCK = true &&
	      (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	      (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	      (datagram.ps2 = Some(uint id.virtual_host_port))
	    then
	      syn_ack_list := !syn_ack_list @ [datagram]
	| _ -> ()
      in
       let slurper_callback_hnd = slurper_register_callback
	   (the ts.th_slurper_hnd) slurper_callback_fun in

      let syn_datagram = {
	is1 = Some(hol_ip id.virtual_host_ip);
	ps1 = Some(uint id.virtual_host_port);
	is2 = Some(hol_ip id.test_host.test_ip_address);
	ps2 = Some(uint id.test_host.test_ephm_port);
	seq = uint 1000;
	ack = uint 0;
	sYN = true; aCK = false; rST = false;
	uRG = false; pSH = false; fIN = false;
	urp = uint 0;
	win = uint 8192;
	mss = Some(uint 512);
	scale = None;
	ts = None;
	data = [];
      }	 in

      let latest_syn_datagram =
	let rec syn_sender_loop n dg =
	  if n=0 then dg else
	  (let datagram = {dg with seq = dg.seq +. (uint 5000); ps1 = Some(the dg.ps1 +. (uint 1))} in
	  injector_inject (the ts.th_injector_hnd) (TCPMSG(datagram));
	  syn_sender_loop (n-1) datagram)
	in syn_sender_loop 15 syn_datagram;
      in

      delay 0.5; (* Wait until we have collected all of the SYN/ACKS *)
     (* Unregister the callback *)
      slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

      (* Now clock out a new SYN datagram with each ACK datagram generated from a rcvd SYN/ACK *)
      let latest_syn_datagram =
	let rec syn_ack_clocked ack_list syn_dg =
	  match ack_list with
	    [] -> syn_dg
	  | x::xs ->
	      let ack_dg = {x with
			    is1 = x.is2; is2 = x.is1; ps1 = x.ps2; ps2 = x.ps1; ts = timestamp_update_swap x.ts (uint 1);
			    seq = x.ack; ack = x.seq +. (uint 1); sYN = false; data = []} in
	      injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_dg));
	      let syn_dg = {syn_dg with seq = syn_dg.seq +. (uint 5000); ps1 = Some(the syn_dg.ps1 +. (uint 1))} in
	      injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_dg));
	      syn_ack_clocked xs syn_dg
	in syn_ack_clocked !syn_ack_list latest_syn_datagram
      in

      let latest_syn_datagram =
	let rec syn_sender_loop n dg =
	  if n=0 then dg else
	  (let datagram = {dg with seq = dg.seq +. (uint 5000); ps1 = Some(the dg.ps1 +. (uint 1));
			     ts = timestamp_update dg.ts (uint 1);} in
	  injector_inject (the ts.th_injector_hnd) (TCPMSG(datagram));
	  syn_sender_loop (n-1) datagram)
	in syn_sender_loop 15 latest_syn_datagram;
      in

      rst_driven_socket ts id fd (NO_DATAGRAMS)),
    "listen() --  fresh listening socket with backlog=" ^ (string_of_int backlog) ^ ". Flood with many new connections and collect synack responses. For each ack in reply, clock out a new connection syn. This should allow one to determine the size of the different connection queues and how they interact.",
    ((true, false), true, true, false),
    ((false, false), false, false, true))

let test12 = (
  function (sf,sfdescr) ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let listen_call = (tid_of_int_private 0, LISTEN(fd,1)) in
      ignore(libd_call (the ts.th_libd_hnd) listen_call);
      rst_udp_socket id ts fd),
     "listen() -- UDP sock with address quad " ^ sfdescr ^ ", call listen() and expect to fail.",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )


let driven_states =
  let rec remove_listen_state driven_list =
    match driven_list with
      [] -> []
    | (ST_LISTEN, y)::xs -> remove_listen_state xs
    | (x, y)::xs -> (x, y)::(remove_listen_state xs) in
  remove_listen_state all_interesting_driven_states

let test_from_all_states =
  List.map test8 driven_states @ List.map test7c all_driven_states @ List.map test7d all_driven_states


let tcp_tests = [test1; test2; test3; test5; test6; test6a; test6b; test6c; test6d; test7a; test7b; test9]
  @ test_from_all_states @
  List.map test7e [(true,false);(false,true);(true,true)] @
  List.map test10 [1;2;3;5;0] @ (* try these different backlog values *)
  List.map test11 [1;2;3;5;0]  (* try these different backlog values *)

let udp_tests =  List.map test12 bound_udp_quads

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = [test1; test2; test3; test5; test6; test6a; test6b; test6c; test6d; test7a; test7b; test9]
let stream_exhaustive_tests = []

(* ---------------------------------------------------------------------- *)

let do_listen_tests handle hosts_list test_type =
  begin_next_test_group handle "listen()";
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
  !done_a_test;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
