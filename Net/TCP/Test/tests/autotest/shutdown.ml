(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: shutdown()                          *)
(* Steve Bishop - Created 20030709                                        *)
(* $Id: shutdown.ml,v 1.17 2006/06/07 11:52:45 amgb2 Exp $ *)
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

let test1 = (
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps1 = Some(uint id.virtual_host_port))
	  then
	     last_datagram_seen := RECV_DATAGRAM(datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, true, false)) in
    ignore(libd_call th_libd shutdown_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 10, [])) in
    ignore(libd_call th_libd recv_call);

    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "shutdown() -- for a fresh TCP socket in state ST_ESTABLISHED(DATA_SENT_RCVD), call shutdown() on the receive side only and attempt to receive more data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
 )

let test2 = (
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps1 = Some(uint id.virtual_host_port))
	  then
	     last_datagram_seen := RECV_DATAGRAM(datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, false, true)) in
    ignore(libd_call th_libd shutdown_call);
    let name_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call th_libd name_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FOOTLE", [])) in
    ignore(libd_call th_libd send_call);

    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "shutdown() -- for a fresh TCP socket in state ST_ESTABLISHED(DATA_SENT_RCVD), call shutdown() on the send side only and attempt to send more data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
 )

let test3 = (
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps1 = Some(uint id.virtual_host_port))
	  then
	     last_datagram_seen := RECV_DATAGRAM(datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, true, true)) in
    ignore(libd_call th_libd shutdown_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FOOTLE", [])) in
    ignore(libd_call th_libd send_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 10, [])) in
    ignore(libd_call th_libd recv_call);

    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "shutdown() -- for a fresh TCP socket in ST_ESTABLISHED(DATA_SENT_RCVD), call shutdown() on both the send and receive halves of the socket and attempt to send and receive further data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
 )

let test4 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,true,false)) in
      ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
      let recv_call = (tid_of_int_private 0, RECV(fd,10,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)),
      "shutdown() -- for a fresh UDP socket with bound quad "^ (string_of_bound_udp_quad sf) ^ ", call shutdown() on the receive side only and attempt to receive more data",
      ((true,false),true,false,false),
      ((false,false),false,false,true))
 )

let test4a = (
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
      let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,true,false)) in
      ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
      injector_inject (the ts.th_injector_hnd) (UDPMSG(pac));
      delay 5.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,10,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)),
      "shutdown() -- for a fresh UDP socket with bound quad "^ (string_of_bound_udp_quad sf) ^ ", call shutdown() on the receive side only and attempt to receive more data when there is data on the rcvq",
      ((true,false),true,false,false),
      ((false,false),false,false,true))
 )

let test5 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,false,true)) in
      ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"FOOTLE",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)),
      "shutdown() -- for a fresh UDP socket with bound quad "^ (string_of_bound_udp_quad sf) ^ ", call shutdown() on the send side only and attempt to send more data",
      ((true,false),true,false,false),
      ((false,false),false,false,true))
 )

let test6 = (
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
      let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,true,true)) in
      ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
      injector_inject (the ts.th_injector_hnd) (UDPMSG(pac));
      delay 5.0;
      let recv_call = (tid_of_int_private 0, RECV(fd,10,[])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"FOOTLE",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)),
      "shutdown() -- for a fresh UDP socket with bound quad "^ (string_of_bound_udp_quad sf) ^ ", call shutdown() on the receive side only and attempt to receive more data when there is data on the rcvq",
      ((true,false),true,false,false),
      ((false,false),false,false,true))
 )

let test7 = (
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts (ST_SYN_SENT) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_ack = ref false in
    let last_datagram_seen = ref last_dgram in

    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) &&
            (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_ack := true;
	     last_datagram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, false, true)) in
    ignore(libd_call th_libd shutdown_call);

    if (id.test_host.platform_type = ARCH_BSD) then ( (* don't do under linux *)

      (* Inject the packet sent by psyche *)
      let packet_to_inject =
	match last_dgram with
	  RECV_DATAGRAM(dg) ->
	    {dg with seq = dg.seq;
             ack = dg.seq +. (uint 1);
	     sYN = true; aCK = true; fIN = false; ts = timestamp_update dg.ts (uint 1);
	     data = []}
	| SENT_DATAGRAM(dg) ->
	    {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	     seq = dg.ack; ack = dg.seq +. (uint 1); ts = timestamp_update_swap dg.ts (uint 1);
	     sYN = true; aCK = true; fIN = false;
	     data = []}
	| _ ->
	    raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
      in
      delay 10.00;
      injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));

      (* Block on condition variable here until we verify that the ACK packet has been seen *)
      Mutex.lock lock;
      while !seen_ack = false do
	Condition.wait cond lock;
      done;
      Mutex.unlock lock;

      delay 10.00;

     )
    else ();

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.0;
    rst_driven_socket ts id fd !last_datagram_seen),
  "shutdown() -- for a fresh TCP socket in ST_SYN_SENT, call shutdown() on the send side only, with the remote host not ACKing the FIN",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
  )

let test7b = (
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts (ST_SYN_SENT) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_fin = ref false in
    let seen_ack = ref false in
    let last_datagram_seen = ref last_dgram in

    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    if (datagram.fIN = true) then
	      (Mutex.lock lock; seen_fin := true;
	       last_datagram_seen := SENT_DATAGRAM(datagram);
	       Condition.signal cond; Mutex.unlock lock)
	    else if (datagram.aCK = true) then
	      (Mutex.lock lock; seen_ack := true;
	       last_datagram_seen := SENT_DATAGRAM(datagram);
	       Condition.signal cond; Mutex.unlock lock)
	    else ()
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, false, true)) in
    ignore(libd_call th_libd shutdown_call);

    if (id.test_host.platform_type = ARCH_BSD) then ( (* don't do under linux *)

      (* Block on condition variable here until we verify that the FIN packet has been seen *)
      Mutex.lock lock;
      while !seen_fin = false do
	Condition.wait cond lock;
      done;
      Mutex.unlock lock;

      (* Inject the packet sent by psyche *)
      let packet_to_inject =
	match !last_datagram_seen with
	  RECV_DATAGRAM(dg) ->
	    {dg with seq = dg.seq;
             ack = dg.seq +. (uint 1);
	     sYN = true; aCK = true; fIN = false; ts = timestamp_update dg.ts (uint 1);
	     data = []}
	| SENT_DATAGRAM(dg) ->
	    {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	     seq = dg.ack; ack = dg.seq +. (uint 1); ts = timestamp_update_swap dg.ts (uint 1);
	     sYN = true; aCK = true; fIN = false;
	     data = []}
	| _ ->
	    raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
      in
      delay 10.00;
      injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));

      (* Block on condition variable here until we verify that the ACK packet has been seen *)
      Mutex.lock lock;
      while !seen_ack = false do
	Condition.wait cond lock;
      done;
      Mutex.unlock lock;

      delay 10.00;

     )
    else ();

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.0;
    rst_driven_socket ts id fd !last_datagram_seen),
  "shutdown() -- for a fresh TCP socket in ST_SYN_SENT, call shutdown() on the send side only, with the remote host ACKing the FIN",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
 )

let test8 = (
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts (ST_SYN_RCVD) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_ack = ref false in
    let last_datagram_seen = ref last_dgram in

    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) &&
            (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
            (Mutex.lock lock; seen_ack := true;
	     last_datagram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, false, true)) in
    ignore(libd_call th_libd shutdown_call);

    if (id.test_host.platform_type = ARCH_BSD) then ( (* don't do under linux *)

      (* Inject the packet sent by psyche *)
      let packet_to_inject =
	match last_dgram with
	  RECV_DATAGRAM(dg) ->
	    {dg with seq = dg.seq;
	     ack = dg.seq +. (uint 1);
	     sYN = false; aCK = true; fIN = false; ts = timestamp_update dg.ts (uint 1);
	     data = []}
	| SENT_DATAGRAM(dg) ->
	    {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	     seq = dg.ack; ack = dg.seq +. (uint 1); ts = timestamp_update_swap dg.ts (uint 1);
	     sYN = false; aCK = true; fIN = false;
	     data = []}
	| _ ->
	    raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
      in
      delay 10.00;
      injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));

      (* Block on condition variable here until we verify that the ACK packet has been seen *)
      Mutex.lock lock;
      while !seen_ack = false do
	Condition.wait cond lock;
      done;
      Mutex.unlock lock;

      delay 10.00;

     )
    else ();

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.0;
    rst_driven_socket ts id fd !last_datagram_seen),
  "shutdown() -- for a fresh TCP socket in ST_SYN_RCVD, call shutdown() on the send side only, with the remote host not ACKing the FIN",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
 )

let test8b = (
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts (ST_SYN_RCVD) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_fin = ref false in
    let seen_ack = ref false in
    let last_datagram_seen = ref last_dgram in

    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) &&
            (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    if (datagram.fIN = true) then
              (Mutex.lock lock; seen_fin := true; seen_ack := true;
	       last_datagram_seen := SENT_DATAGRAM(datagram);
	       Condition.signal cond; Mutex.unlock lock)
	    else
	      (Mutex.lock lock; seen_ack := true;
	       last_datagram_seen := SENT_DATAGRAM(datagram);
	       Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, false, true)) in
    ignore(libd_call th_libd shutdown_call);

    if (id.test_host.platform_type = ARCH_BSD) then ( (* don't do under linux *)

      (* Block on condition variable here until we verify that the FIN packet has been seen *)
      Mutex.lock lock;
      while !seen_fin = false do
	Condition.wait cond lock;
      done;
      Mutex.unlock lock;

      (* Inject the packet sent by psyche *)
      let packet_to_inject =
	match !last_datagram_seen with
	  RECV_DATAGRAM(dg) ->
	    {dg with seq = dg.seq;
	     ack = dg.seq +. (uint 1);
	     sYN = false; aCK = true; fIN = false; ts = timestamp_update dg.ts (uint 1);
	     data = []}
	| SENT_DATAGRAM(dg) ->
	    {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	     seq = dg.ack; ack = dg.seq +. (uint 1); ts = timestamp_update_swap dg.ts (uint 1);
	     sYN = false; aCK = true; fIN = false;
	     data = []}
	| _ ->
	    raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
      in
      delay 10.00;
      injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));

      (* Block on condition variable here until we verify that the ACK packet has been seen *)
      Mutex.lock lock;
      while !seen_ack = false do
	Condition.wait cond lock;
      done;
      Mutex.unlock lock;

      delay 10.00;

     )
    else ();

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.0;
    rst_driven_socket ts id fd !last_datagram_seen),
  "shutdown() -- for a fresh TCP socket in ST_SYN_RCVD, call shutdown() on the send side only, with the remote host ACKing the FIN",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
 )

(* tjr first test *)
exception Error_occurred of int;;
let test9 = (
  (function id -> function ts ->
     let server_libd_hnd = the ts.th_libd_hnd in
     let client_libd_hnd = the ts.ah_libd_hnd in
     let server_ip = id.test_host.test_ip_address in

let call_wrap x = (tid_of_int_private 0, x) in

(* test starts here *)
let c = call_wrap

(SOCKET SOCK_STREAM) in

let r = libd_call server_libd_hnd c in
let sfd = match r with (_, OK_FD(fd)) -> fd | _ -> raise (Error_occurred 0) in
let c = call_wrap

(LISTEN(sfd, 5)) in

let r = libd_call server_libd_hnd c in
let c = call_wrap

(GETSOCKNAME(sfd)) in

let r = libd_call server_libd_hnd c in
let sport = match r with (_, OK_IPOPT_PORTOPT(_,Some port)) -> port | _ -> raise (Error_occurred 1) in
let _ = print_string ("Server bound to port: "^string_of_int (int_of_port sport)) in
let _ = print_newline() in
(* CLIENT socket and connect *)
let _ = print_string "CLIENT socket" in
let _ = print_newline() in
let c = call_wrap

(SOCKET SOCK_STREAM) in

let r = libd_call client_libd_hnd c in
let cfd = match r with (_,OK_FD(fd)) -> fd | _ -> raise (Error_occurred 2) in
let _ = print_string "CLIENT connect" in
let _ = print_newline() in
let c = call_wrap

(CONNECT(cfd, mk_ip server_ip, Some sport)) in

let r = libd_call client_libd_hnd c in
(* SERVER accept, then half shutdown *)
let c = call_wrap

(ACCEPT sfd) in

let r = libd_call server_libd_hnd c in
(* get handle for accepted connection *)
let sfd' = match r with (_, OK_FD_IP_PORT (fd, (ip, port))) -> fd | _ -> raise (Error_occurred 4) in
(* cut to make CheckTrace succeed
let c = call_wrap

(SHUTDOWN(sfd,false,true)) in

let r = libd_call server_libd_hnd c in
let _ = print_string "CLIENT send" in
let _ = print_newline() in
(* CLIENT send *)
let c = call_wrap

(SEND(cfd,None,"Hello",[])) in

let r = libd_call client_libd_hnd c in
let _ = Thread.delay 2.00 in
(* SERVER READ *)
let c = call_wrap

(RECV(sfd',5,[])) in (* ignore N.B. only read 4 bytes *)

let r = libd_call server_libd_hnd c in
let s = match r with (_, OK_STRING_IP_PORT_BOOL(s,_)) -> s | _ -> raise (Error_occurred 3) in
let _ = print_string ("Returned string: "^s) in (* "hell" ? *)
let _ = print_newline() in
*)
(* SERVER close *)
let c = call_wrap

(CLOSE(sfd')) in

let r = libd_call server_libd_hnd c in
let c = call_wrap

(CLOSE(sfd)) in

let r = libd_call server_libd_hnd c in
(* CLIENT close *)
let c = call_wrap

(CLOSE(cfd)) in

let r = libd_call client_libd_hnd c in
delay 2.0
 ),
  "shutdown() -- setup server client connection, server shutdown for writing, client writes, server reads, server closes, client closes",
  ((true, false), true, true, false),
  ((true, false), false, false, false)
 )

let tcp_tests = [test1; test2; test3; test7; test7b; test8; test8b]

let udp_tests = (List.map test4 all_sock_flavours) @ (List.map test5 all_sock_flavours) @ (List.map test6 all_sock_flavours) @ (List.map test4a all_sock_flavours)

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_shutdown_tests handle hosts_list test_type =
  begin_next_test_group handle "shutdown()";
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
