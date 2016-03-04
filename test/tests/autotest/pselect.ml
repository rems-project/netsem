(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: pselect()                           *)
(* Matthew Fairbairn - Created 20040621                                   *)
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

(* ------------------------------------------------------------------------ *)

let test1 = (
  function (st,str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let fd_bad = fd_of_int_private 751 in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let thread_body = (function () ->
      let pselect_call = (tid_of_int_private 0,
                          PSELECT([fd;fd_bad],[fd;fd_bad],[fd;fd_bad],None,None)) in
      ignore(libd_call (the ts.th_libd_hnd) pselect_call))  in
    let thread = Thread.create thread_body () in
    delay 5.00;
    rst_driven_socket ts id fd last_dg),
  "pselect() -- for a fresh socket in state " ^ str ^ ", call pselect() on that socket and some bad FDs",
  ((true,false),true,true,false),
  ((false,false),false,false,true))

let test2 = (
  function (st,str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let thread_body = (function () ->
      let pselect_call = (tid_of_int_private 0, PSELECT([fd],[fd],[fd],Some(-1,0),None)) in
      ignore(libd_call (the ts.th_libd_hnd) pselect_call))  in
    let thread = Thread.create thread_body () in
    delay 5.00;
    rst_driven_socket ts id fd last_dg),
  "pselect() -- for a fresh socket in state " ^ str ^ ", call pselect() on that socket with a negative timeout",
  ((true,false),true,true,false),
  ((false,false),false,false,true))

let test3 = (
  (function id -> function ts ->
    let pselect_call = (tid_of_int_private 0, PSELECT([],[],[],Some(10,0),None)) in
    ignore(libd_call (the ts.th_libd_hnd) pselect_call)),
  "pselect() -- call pselect() with no FDs and a 10s timeout",
  ((true,false),false,false,false),
  ((false,false),false,false,false))

let test4 = (
  function (st,str) -> (function id -> function ts ->
    let fd, last_dg,_ = tcp_state_diagram_driver id ts st false in
    let last_dgram = ref last_dg in
    let t = Thread.create (function () ->
      let pselect_call = (tid_of_int_private 0, PSELECT([fd],[],[],Some(30,0),None)) in
      ignore(libd_call (the ts.th_libd_hnd) pselect_call)) () in
    delay 15.0;
    (* A slurper callback function that signals a condition when the *)
    (* required ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if datagram.aCK &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    last_dgram := SENT_DATAGRAM(datagram)
	  else ()
      | _ -> ()
    in
    (* Inject the packet sent by psyche *)
    let packet_to_inject =
      match !last_dgram with
	RECV_DATAGRAM(dg) ->
	  Some({dg with seq = dg.seq +. (uint (List.length(dg.data)));
		sYN = false; aCK = true; fIN = false; ts = timestamp_update dg.ts (uint 1);
		data = test_msg})
      | SENT_DATAGRAM(dg) ->
	  Some({dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; fIN = false; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg})
      | _ ->
	  None (*raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))*)
    in
    (match packet_to_inject with
      None -> ()
    | Some(pci) ->
	let slurper_callback_hnd = slurper_register_callback
	    (the ts.th_slurper_hnd) slurper_callback_fun in
	injector_inject (the ts.th_injector_hnd) (TCPMSG(pci));
	last_dgram := RECV_DATAGRAM(pci); delay 0.2);
    delay 15.0;
    rst_driven_socket ts id fd !last_dgram),
  "pselect() -- for fresh socket, fd, in state " ^ str ^ ", call pselect([fd],[],[],Some(30,0),None) then inject a datagram for the socket",
  ((true,false),true,true,false),
  ((false,false),false,false,true))

let test5 = (
  function (st,str) -> (function id -> function ts ->
    let fd, last_dg,_ = tcp_state_diagram_driver id ts st false in
    let last_dgram = ref last_dg in
    let ps_call = (tid_of_int_private 0, PSELECT([],[fd],[],Some(3,0),None)) in
    ignore(libd_call (the ts.th_libd_hnd) ps_call);
    rst_driven_socket ts id fd !last_dgram),
    "pselect() -- for a fresh TCP socket, fd, in state " ^ str ^ ", call pselect([],[fd],[],Some(3,0),None)",
    ((true,true),true,true,false),
    ((false,false),false,false,true))

let test6 = (
  function (st, str) -> (function id -> function ts ->
    let fd, last_dg,_ = tcp_state_diagram_driver id ts st false in
    let last_dgram = ref last_dg in
    let sd_call = (tid_of_int_private 0, SHUTDOWN(fd,true,true)) in
    ignore(libd_call (the ts.th_libd_hnd) sd_call);
    let ps_call = (tid_of_int_private 0, PSELECT([fd],[fd],[fd],Some(3,0),None)) in
    ignore(libd_call (the ts.th_libd_hnd) ps_call);
    rst_driven_socket ts id fd !last_dgram),
    "pselect() -- for a fresh TCP socket, fd, in state " ^ str ^ ", that has been shutdown for both writing and reading, call pselect([fd],[fd],[fd])",
    ((true,true),true,true,false),
    ((false,false),false,false,true))

let test7 = (
  function (st,str) -> (function id -> function ts ->
    let fd,last_dg,_ = tcp_state_diagram_driver id ts st false in
    let last_dgram = ref last_dg in
    let nb_call = (tid_of_int_private 0, SETFILEFLAGS(fd,[O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nb_call);
    let ps_call = (tid_of_int_private 0, PSELECT([fd],[fd],[fd],Some(3,0),None)) in
    ignore(libd_call (the ts.th_libd_hnd) ps_call);
    rst_driven_socket ts id fd !last_dgram),
    "pselect() -- for a fresh, non-blocking TCP socket fd in state " ^ str ^ ", call pselect([fd],[fd],[fd],Some(3,0),None)",
    ((true,true),true,true,false),
    ((false,false),false,false,true))

let test8 = (
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

    let ps_call = (tid_of_int_private 0, PSELECT([fd],[fd],[fd],Some(3,0),None)) in
    ignore(libd_call (the ts.th_libd_hnd) ps_call)),
  "pselect() -- for a listening, non-blocking TCP socket fd with one connection waiting, call pselect([fd],[fd],[fd],Some(3,0),None)",
  ((true,true),true,true,false),
  ((true,true),true,true,false))


let test9 = (
  (function id -> function ts ->
    let fd,last_dg,_ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_ack = ref false in
    (* A slurper callback function that signals a condition when the *)
    (* required ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if datagram.aCK &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock;
	     seen_ack := true;
	     last_dgram := SENT_DATAGRAM(datagram);
	     Condition.signal cond;
	   Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    (* Inject the packet sent by psyche *)
    let packet_to_inject =
      match last_dg with
	RECV_DATAGRAM(dg) ->
	  {dg with seq = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; uRG = true;
	   urp = dg.seq +. (uint 3);ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; uRG = true;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   urp = dg.ack +. (uint 3);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In test20() got a NO_DATAGRAMS!"))
    in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    let pselect_call = (tid_of_int_private 0, PSELECT([],[],[fd],Some(3,0),None)) in
    ignore(libd_call (the ts.th_libd_hnd) pselect_call);
    rst_driven_socket ts id fd !last_dgram),
  "pselect() -- for a socket in stae ESTABLISHED with urgent data, call pselect([],[],[fd],Some(3,0),None)",
  ((true,true),true,true,false),
  ((false,false),false,false,true))





(* UDP Tests *)
let test10 = (
  function  sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let pselect_call = (tid_of_int_private 0, PSELECT([fd],[fd],[fd],Some(10,0),None)) in
      ignore(libd_call (the ts.th_libd_hnd) pselect_call);
      rst_udp_socket id ts fd),
     "pselect() -- for UDP socket, fd, with binding quad " ^ string_of_bound_udp_quad sf ^ ", call pselect([fd],[fd],[fd],Some(30,0),None)",
     ((true,false),true,false,false),
     ((false,false),false,false,false))
 )

let test11 = (
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
			      udp_hol_data = [uint (Char.code 'h')]} in
      let t = Thread.create (function () ->
	let pselect_call = (tid_of_int_private 0, PSELECT([fd],[],[],Some(30,0),None)) in
	ignore(libd_call (the ts.th_libd_hnd) pselect_call)) () in
      delay 15.0;
      injector_inject (the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 20.0;
      rst_udp_socket id ts fd),
     "pselect() -- for a UDP Socket with binding_quad " ^ string_of_bound_udp_quad sf ^ ", call pselect([fd],[],[],Some(30,0),None) then inject a packet destined for it",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )

let test12 = (
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
			      udp_hol_data = [uint (Char.code 'h')]} in
      injector_inject (the ts.th_injector_hnd) (UDPMSG(packet_to_inject));
      delay 5.0;
      let pselect_call = (tid_of_int_private 0, PSELECT([fd],[fd],[],Some(10,0),None)) in
      ignore(libd_call (the ts.th_libd_hnd) pselect_call);
      rst_udp_socket id ts fd),
     "pselect() -- for a UDP Socket with binding quad " ^ string_of_bound_udp_quad sf ^ " and data on its rcvq, call pselect([fd],[fd],[],SOme(10,0),None)",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )

let test13 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let t = Thread.create (function () ->
	let pselect_call = (tid_of_int_private 0, PSELECT([],[],[fd],Some(30,0),None)) in
	ignore(libd_call (the ts.th_libd_hnd) pselect_call)) () in
      delay 3.0;
      let send_call = (tid_of_int_private 0, SEND(fd,None,"blah",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      rst_udp_socket id ts fd),
     "pselect() -- for a UDP socket fd with binding quad " ^ string_of_bound_udp_quad sf ^ ", call pselect([],[],[fd],Some(30,0),None) then generate a pending error on the socket",
     ((true,false),true,false,false),
     ((false,false),false,false,false))
 )

let test13a = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let t = Thread.create (function () ->
	let pselect_call = (tid_of_int_private 0, PSELECT([fd],[],[],Some(30,0),None)) in
	ignore(libd_call (the ts.th_libd_hnd) pselect_call)) () in
      delay 3.0;
      let send_call = (tid_of_int_private 0, SEND(fd,None,"blah",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      rst_udp_socket id ts fd),
     "pselect() -- for a UDP socket fd with binding quad " ^ string_of_bound_udp_quad sf ^ ", call pselect([fd],[],[],Some(30,0),None) then generate a pending error on the socket",
     ((true,false),true,false,false),
     ((false,false),false,false,false))
 )

let test14 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let fd_bad = fd_of_int_private 751  in
      let pselect_call = (tid_of_int_private 0, PSELECT([fd;fd_bad],[fd;fd_bad],[fd;fd_bad],Some(3,0),None)) in
      ignore(libd_call (the ts.th_libd_hnd) pselect_call);
      rst_udp_socket id ts fd),
     "pselect() -- for a UDP socket with binding quad " ^ string_of_bound_udp_quad sf ^", call pselect() with it and some bad FDs",
     ((true,false),true,false,false),
     ((false,false),false,false,false))
 )

let test15 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd,[O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
      let thread = (function  () ->
        let pselect_call = (tid_of_int_private 0, PSELECT([fd],[fd],[fd],Some(-10,0),None)) in
        ignore(libd_call (the ts.th_libd_hnd) pselect_call)) in
      let _ = Thread.create thread () in
      delay 20.00;
      rst_udp_socket id ts fd),
     "pselect() -- for a UDP socket fd with binding quad " ^ string_of_bound_udp_quad sf ^ ", call pselect() with a negative timeout",
     ((true,false),true,false,false),
     ((false,false),false,false,false))
 )

let test16 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let pselect_call = (tid_of_int_private 0, PSELECT([],[fd],[],Some(5,0),None)) in
      ignore(libd_call (the ts.th_libd_hnd) pselect_call);
      rst_udp_socket id ts fd),
     "pselect() -- for a UDP socket fd with binding quad " ^ string_of_bound_udp_quad sf ^ ", call pselect([],[fd],[],Some(5,0),None)",
     ((true,false),true,false,false),
     ((false,false),false,false,false))
 )

let test17 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, true, true)) in
      ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
      let pselect_call = (tid_of_int_private 0, PSELECT([fd], [fd], [fd], Some(5,0), None)) in
      ignore(libd_call (the ts.th_libd_hnd) pselect_call);
      rst_udp_socket id ts fd),
     "pselect() -- for a UDP socket fd with binding quad " ^ string_of_bound_udp_quad sf ^ " that has been shutdown for writing, call pselect([fd],[fd],[fd],Some(5,0),None)",
     ((true,false),true,false,false),
     ((false,false),false,false,false))
 )

let test18 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let nb_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nb_call);
      let ps_call = (tid_of_int_private 0, PSELECT([fd],[],[],Some(3,0),None)) in
      ignore(libd_call (the ts.th_libd_hnd) ps_call);
      rst_udp_socket id ts fd),
     "pselect() -- for a non-blocking UDP socket fd with binding quad " ^ string_of_bound_udp_quad sf ^ ", call pselect([fd],[],[],Some(3,0),None)",
     ((true,false),true,false,false),
     ((false,false),false,false,false))
 )



(* ------------------------------------------------------------------------ *)


let tcp_tests =
  (List.map test1 (List.filter (fun (x,d) -> x != ST_CLOSED && x != ST_LISTEN) all_interesting_driven_states)) @
  (List.map test2 (List.filter (fun (x,d) -> x != ST_CLOSED && x != ST_LISTEN) all_interesting_driven_states)) @ [test3] @
  (List.map test4 all_interesting_driven_states) @
  (List.map test5 all_interesting_driven_states) @
  (List.map test6 all_interesting_driven_states) @
  (List.map test7 all_interesting_driven_states) @ [test8; test9]

let udp_tests =
  (List.map test10 all_sock_flavours) @
  (List.map test11 all_sock_flavours) @
  (List.map test12 all_sock_flavours) @
  (List.map test13 all_sock_flavours) @
  (List.map test13a all_sock_flavours) @
  (List.map test14 all_sock_flavours) @
  (List.map test15 all_sock_flavours) @
  (List.map test16 all_sock_flavours) @
  (List.map test17 all_sock_flavours)

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = [test3; test8]
let stream_exhaustive_tests = []

(* ------------------------------------------------------------------------ *)

let do_pselect_tests handle hosts_list test_type =
  begin_next_test_group handle "pselect()";
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
