(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: recv()                              *)
(* Steve Bishop - Created 20030708                                        *)
(* $Id: recv.ml,v 1.22 2006/06/07 11:52:45 amgb2 Exp $ *)
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
open Testscommon

let test_msg = [uint(Char.code 'T'); uint(Char.code 'e'); uint(Char.code 's');
		uint(Char.code 't');]

let urg_msg = [uint(Char.code 'U'); uint(Char.code 'R'); uint(Char.code 'G');
		uint(Char.code 'E'); uint(Char.code 'N'); uint(Char.code 'D');]

(* ---------------------------------------------------------------------- *)

let test1 = (
  function (st, str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 20, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd last_dg),
  "recv() -- for a non-blocking socket in state " ^ str ^ ", attempt to recv() some data (should fail)",
  ((true, false), true, true, false),
  ((false, false), false, false, true))


let test2 = (
  function (st, str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 20, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd last_dg),
  "recv() -- for a blocking socket in state " ^ str ^ ", attempt to recv() some data (should fail)",
  ((true, false), true, true, false),
  ((false, false), false, false, true))

(* ---------------------------------------------------------------------- *)


let test3a = (
 function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_FIN_WAIT_1(DATA_SENT_RCVD)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	  {dg with seq = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; fIN = false; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; fIN = false;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    last_dgram := RECV_DATAGRAM(packet_to_inject); delay 0.2;
    let recv_call = (tid_of_int_private 0, RECV(fd, 20, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    delay 0.5;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state FIN_WAIT_1, attempt to recv() some data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test3b = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_FIN_WAIT_2(DATA_SENT_RCVD)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
    (* Inject the packet sent by psyche *)
    let packet_to_inject =
      match !last_dgram with
	RECV_DATAGRAM(dg) ->
	  {dg with seq = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; fIN = false;
	   ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; fIN = false;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    last_dgram := RECV_DATAGRAM(packet_to_inject);
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    let recv_call = (tid_of_int_private 0, RECV(fd, 20, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state FIN_WAIT_2, attempt to recv() some data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test4a = (
 function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_FIN_WAIT_1(DATA_SENT_RCVD)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	  {dg with seq = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; fIN = false;
	   ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; fIN = false;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    last_dgram := RECV_DATAGRAM(packet_to_inject); delay 0.2;
    let recv_call = (tid_of_int_private 0, RECV(fd, 20, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    delay 0.5;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state FIN_WAIT_1, attempt to recv() some data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test4b = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_FIN_WAIT_2(DATA_SENT_RCVD)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
    (* Inject the packet sent by psyche *)
    let packet_to_inject =
      match !last_dgram with
	RECV_DATAGRAM(dg) ->
	  {dg with seq = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; fIN = false;
	   ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; fIN = false;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    last_dgram := RECV_DATAGRAM(packet_to_inject);
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    let recv_call = (tid_of_int_private 0, RECV(fd, 20, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state FIN_WAIT_2, attempt to recv() some data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test5 =
 (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_FIN_WAIT_1(DATA_SENT_RCVD)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	  {dg with seq = dg.seq;
	   sYN = false; aCK = true; fIN = false; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack = dg.seq; ts = timestamp_update_swap dg.ts (uint 1);
	   sYN = false; aCK = true; fIN = false;
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
    in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    injector_inject (the ts.th_injector_hnd)
      (TCPMSG({packet_to_inject with
	       fIN = true; data=[]; seq = packet_to_inject.seq +. (uint 4)}));
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    let recv_call = (tid_of_int_private 0, RECV(fd, 20, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state CLOSING, attempt to recv() some of the data left on the queue",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test6 =
 (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_FIN_WAIT_1(DATA_SENT_RCVD)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	  {dg with seq = dg.seq;
	   sYN = false; aCK = true; fIN = false;
	   ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq;
	   sYN = false; aCK = true; fIN = false;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
    in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    injector_inject (the ts.th_injector_hnd)
      (TCPMSG({packet_to_inject with
	       fIN = true; data=[]; seq = packet_to_inject.seq +. (uint 4)}));
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    let recv_call = (tid_of_int_private 0, RECV(fd, 20, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state CLOSING, attempt to recv() some of the data left on the queue",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


(* ---------------------------------------------------------------------- *)

let test7 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	   sYN = false; aCK = true;
	   ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED, with data on the receive queue, call recv()",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test7a =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	   sYN = false; aCK = true;
	   ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 0, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED, with data on the receive queue, call recv() requesting 0 bytes of data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test8 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
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
	   sYN = false; aCK = true;
	   ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state ESTABLISHED and with data on the receive queue, call recv()",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test8a =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
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
	   sYN = false; aCK = true; fIN = true;
	   ts = timestamp_update dg.ts (uint 1);
	   data = []}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; fIN = true;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = []}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state ESTABLISHED after having received a FIN from the remote host, call recv()",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test9 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- from state ESTABLISHED, non-blocking, empty rcvq",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test9a =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 0, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED and empty receive queue, call recv() requesting 0 bytes of data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test10 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let t = Thread.create (function () ->
      let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)) () in
    delay 15.00;
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state ESTABLISHED, call recv() on an empty receive queue",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test10a =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let t = Thread.create (function () ->
      let recv_call = (tid_of_int_private 0, RECV(fd, 0, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)) () in
    delay 15.00;
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state ESTABLISHED, call recv() on an empty receive queue requesting 0 bytes of data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test11 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 6, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED and with data on the receive queue, call recv() requesting more data that is available (should get a partial receive)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test12 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 6, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state ESTABLISHED and with data on the receive queue, call recv() requesting more data than is available (should get a partial receive)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test13 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [MSG_PEEK])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram;
    delay 3.00),
  "recv() -- for a non-blocking socket in state ESTABLISHED with an empty receive queue, call recv() with the MSG_PEEK flag set, then call recv() again without MSG_PEEK",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test14 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 2, [MSG_PEEK])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 2, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED and with data on the receive queue, call recv() to request some of the data with the MSG_PEEK flag set, then call recv() again without MSG_PEEK to ensure the data is still there",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test15 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 6, [MSG_PEEK])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 6, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED and with data on the receive queue, call recv() requesting more data than is available with the MSG_PEEK flag set and call recv() again without MSG_PEEK to ensure the data is still there",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test16 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
    in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    let t = Thread.create (function () ->
      let recv_call = (tid_of_int_private 0, RECV(fd, 6, [MSG_PEEK; MSG_WAITALL])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)) () in
    delay 15.00;
    rst_driven_socket ts id fd !last_dgram;
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 6, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 3.00),
  "recv() -- for a blocking socket in state ESTABLISHED with some data on the receive queue, call recv() requesting more data than is available with the MSG_PEEK and MSG_WAITALL flags set (may block forever). After the socket is RST call receive again (non-blocking) without MSG_PEKK and MSG_WAITALL to check the socket's state and the real effect of the MSG flags",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test16a =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true;
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
    in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    let t = Thread.create (function () ->
      let recv_call = (tid_of_int_private 0, RECV(fd, 6, [MSG_PEEK; MSG_WAITALL])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)) () in
    delay 5.00;

    let packet_to_inject = {packet_to_inject with seq = packet_to_inject.seq +. (uint (List.length test_msg));
			    ts = timestamp_update packet_to_inject.ts (uint 1) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    delay 5.00;

    rst_driven_socket ts id fd !last_dgram;
    delay 3.00;

    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 6, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 3.00),
  "recv() -- for a blocking socket in state ESTABLISHED with some data on the receive queue, call recv() requesting more data than is available with the MSG_PEEK and MSG_WAITALL flags set. More data eventually arrives and the recv() call should return. After the socket is RST call receive again (non-blocking) without MSG_PEKK and MSG_WAITALL to check the socket's state and the real effect of the MSG flags",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test17 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
    in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [MSG_WAITALL])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 3.00;
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state ESTABLISHED with data on the receive queue, call recv() requesting all the data that is available with MSG_WAITALL set. Call recv() again with no flags to check the socket's buffer state",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test18 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
    in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject));
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    let t = Thread.create (function () ->
      let recv_call = (tid_of_int_private 0, RECV(fd, 6, [MSG_WAITALL])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)) () in
    delay 15.00;
    rst_driven_socket ts id fd !last_dgram;
    delay 3.00;
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 6, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 3.00),
  "recv() -- for a blocking socket in state ESTABLISHED and with some data on the receive queue, call recv() requesting more data than is available with the MSG_WAITALL flag set (may block forever)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test19 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 3, [MSG_OOB])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED with no oob data available, call recv() with the MSG_OOB flag set",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test19b =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 0, [MSG_OOB])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED with no oob data available, call recv() with the MSG_OOB flag set request 0 bytes of data.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test19a =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let oobinline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, true)) in
    ignore(libd_call (the ts.th_libd_hnd) oobinline_call);
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
	   urp = dg.seq +. (uint 3); ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; uRG = true;
	   urp = dg.ack +. (uint 3); ts = timestamp_update_swap dg.ts (uint 1);
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let sockatmark_call = (tid_of_int_private 0, SOCKATMARK(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sockatmark_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 1, [MSG_OOB])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 1, [MSG_OOB])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 0, [MSG_OOB])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let sockatmark_call = (tid_of_int_private 0, SOCKATMARK(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sockatmark_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED with oob data available inline, call recv() with the MSG_OOB flag set (requesting non-inline urgent data). The call recv MSG_OOB again requesting the same amount of data. And then call it again requesting 0 bytes of data.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test20 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let oobinline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, true)) in
    ignore(libd_call (the ts.th_libd_hnd) oobinline_call);
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
	   urp = dg.seq +. (uint 3); ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; uRG = true; ts = timestamp_update_swap dg.ts (uint 1);
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
    let sockatmark_call = (tid_of_int_private 0, SOCKATMARK(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sockatmark_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let sockatmark_call = (tid_of_int_private 0, SOCKATMARK(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sockatmark_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 1, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let sockatmark_call = (tid_of_int_private 0, SOCKATMARK(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sockatmark_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED and with oob-data available inline, call recv(), sockatmark() and then recv() again to retrieve the urgent data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test20a =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let oobinline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, true)) in
    ignore(libd_call (the ts.th_libd_hnd) oobinline_call);
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
	   urp = dg.seq +. (uint 3); ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; uRG = true;
	   urp = dg.ack +. (uint 3); ts = timestamp_update_swap dg.ts (uint 1);
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let sockatmark_call = (tid_of_int_private 0, SOCKATMARK(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sockatmark_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 0, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED, with oob data available inline, call recv() requesting zero bytes of data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test21 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
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
	   urp = dg.seq +. (uint 3); ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; uRG = true;
	   urp = dg.ack +. (uint 3); ts = timestamp_update_swap dg.ts (uint 1);
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 1, [MSG_OOB])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED, with oob data not available inline, call recv() with the MSG_OOB flag set",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test22 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let oobinline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, true)) in
    ignore(libd_call (the ts.th_libd_hnd) oobinline_call);
    let rcvbuf_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_RCVBUF, 8)) in
    ignore(libd_call (the ts.th_libd_hnd) rcvbuf_call);
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
    let packet_to_inject1 =
      match last_dg with
	RECV_DATAGRAM(dg) ->
	  {dg with seq = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; uRG = true;
	   urp = dg.seq +. (uint 11); ts = timestamp_update dg.ts (uint 1);
	   data = test_msg @ test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; uRG = true;
	   urp = dg.ack +. (uint 11); ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg @ test_msg}
      | _ ->
	  raise(Drive_Failure("In test20() got a NO_DATAGRAMS!"))
    in
    let packet_to_inject2 =
      {packet_to_inject1 with seq = packet_to_inject1.seq +. (uint 8);
       data = urg_msg} in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject1));
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject2));
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    let recv_call = (tid_of_int_private 0, RECV(fd, 20, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    let sockatmark_call = (tid_of_int_private 0, SOCKATMARK(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sockatmark_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 6, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED, with a full receive queue, call recv(), sockatmark() and then recv() attempting to retrieve the urgent data?!?!",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test23 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let rcvbuf_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_RCVBUF, 8)) in
    ignore(libd_call (the ts.th_libd_hnd) rcvbuf_call);
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
    let packet_to_inject1 =
      match last_dg with
	RECV_DATAGRAM(dg) ->
	  {dg with seq = dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; uRG = true;
	   urp = dg.seq +. (uint 11); ts = timestamp_update dg.ts (uint 1);
	   data = test_msg @ test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; uRG = true;
	   urp = dg.ack +. (uint 11); ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg @ test_msg}
      | _ ->
	  raise(Drive_Failure("In test20() got a NO_DATAGRAMS!"))
    in
    let packet_to_inject2 =
      {packet_to_inject1 with seq = packet_to_inject1.seq +. (uint 8);
       data = urg_msg} in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject1));
    injector_inject (the ts.th_injector_hnd) (TCPMSG(packet_to_inject2));
    (* Block on condition variable here until we verify that the send *)
    (* occured and the ACK has been received back *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    let recv_call = (tid_of_int_private 0, RECV(fd, 1, [MSG_OOB])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED, with a full receive queue and oob data not available inline, call recv() with the MSG_OOB flag set",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test24 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let rcvlowat_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_RCVLOWAT, 10)) in
    ignore(libd_call (the ts.th_libd_hnd) rcvlowat_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED and a receive queue length less than SO_RCVLOWAT, call recv(). NOTE: THIS TEST MAY NOT WORK CORRECTLY ON WINXP AS SO_RCVLOWAT IS NOT AVAILABLE.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test25 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let rcvlowat_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_RCVLOWAT, 8)) in
    ignore(libd_call (the ts.th_libd_hnd) rcvlowat_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg @ test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg @ test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 10, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED, with a receive queue length equal to SO_RCVLOWAT, call recv(). NOTE: THIS TEST MAY NOT WORK CORRECTLY ON WINXP AS SO_RCVLOWAT IS NOT AVAILABLE.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test26 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let rcvlowat_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_RCVLOWAT, 6)) in
    ignore(libd_call (the ts.th_libd_hnd) rcvlowat_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg @ test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg @ test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 8, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED with a receive queue length greater than SO_RCVLOWAT, call recv(). NOTE: THIS TEST MAY NOT WORK CORRECTLY ON WINXP AS SO_RCVLOWAT IS NOT AVAILABLE.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test27 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let rcvlowat_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_RCVLOWAT, 10)) in
    ignore(libd_call (the ts.th_libd_hnd) rcvlowat_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [MSG_PEEK])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED, with a rcvq len less than SO_RCVLOWAT, call recv() with the MSG_PEEK flag set. NOTE: THIS TEST MAY NOT WORK CORRECTLY ON WINXP AS SO_RCVLOWAT IS NOT AVAILABLE.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test28 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let rcvtimeo_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_RCVTIMEO, None)) in
    ignore(libd_call (the ts.th_libd_hnd) rcvtimeo_call);
    let t = Thread.create (function () ->
      let recv_call = (tid_of_int_private 0, RECV(fd, 10, [])) in
      ignore(libd_call (the ts.th_libd_hnd) recv_call)) () in
    delay 15.00;
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state ESTABLISHED, blocking, with SO_RCVTIMEO=0 and an empty receive queue, call recv(). (No data arrives so should block forever). NOTE: THIS TEST MAY NOT WORK CORRECTLY ON WINXP AS SO_RCVTIMEO IS NOT AVAILABLE.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test29 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let rcvtimeo_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_RCVTIMEO, Some(5,5))) in
    ignore(libd_call (the ts.th_libd_hnd) rcvtimeo_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 10, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state ESTABLISHED, with SO_RCVTIMEO!=0 and an empty receive queue, call recv(). (No data arrives so will timeout eventually). NOTE: THIS TEST MAY NOT WORK CORRECTLY ON WINXP AS SO_RCVTIMEO IS NOT AVAILABLE.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test30 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let rcvtimeo_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_RCVTIMEO, Some(5,5))) in
    ignore(libd_call (the ts.th_libd_hnd) rcvtimeo_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 4, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state ESTABLISHED, with SO_RCVTIMEO!=0 and an empty receive queue, call recv(). (Data arrives before timeout occurs). NOTE: THIS TEST MAY NOT WORK CORRECTLY ON WINXP AS SO_RCVTIMEO IS NOT AVAILABLE.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test31 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let rcvtimeo_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_RCVTIMEO, Some(5,5))) in
    ignore(libd_call (the ts.th_libd_hnd) rcvtimeo_call);
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
	   sYN = false; aCK = true; ts = timestamp_update dg.ts (uint 1);
	   data = test_msg}
      | SENT_DATAGRAM(dg) ->
	  {dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	   sYN = false; aCK = true; ts = timestamp_update_swap dg.ts (uint 1);
	   data = test_msg}
      | _ ->
	  raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
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
    let recv_call = (tid_of_int_private 0, RECV(fd, 8, [MSG_WAITALL])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a blocking socket in state ESTABLISHED, with SO_RCVTIMEO!=0 and the requested amount of data not on queue, call recv() with MSG_WAITALL set and allow the timeout to occur. NOTE: THIS TEST MAY NOT WORK CORRECTLY ON WINXP AS SO_RCVTIMEO IS NOT AVAILABLE.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test32 =
  (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, true, false)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 10, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);
    rst_driven_socket ts id fd !last_dgram),
  "recv() -- for a non-blocking socket in state ESTABLISHED, with the receive side of the connection shutdown(), call recv()",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let states1 =
  let rec remove_states driven_list =
    match driven_list with
      [] -> []
    | (ST_ESTABLISHED(_), y)::xs -> remove_states xs
    | (ST_FIN_WAIT_1(_), y)::xs -> remove_states xs
    | (ST_FIN_WAIT_2(_), y)::xs -> remove_states xs
    | (ST_CLOSING(_), y)::xs -> remove_states xs
    | (x, y)::xs -> (x, y)::(remove_states xs) in
  remove_states all_interesting_driven_states

let tcp_tests =
  List.map test1 states1 @
  List.map test2 states1 @
  [test3a; test3b; test4a; test4b] @
  [test5; test6; test7; test7a; test8; test8a; test9; test9a; test10; test10a; test11;
   test12; test13; test14; test15; test16; test16a; test17; test18; test19;
   test19a; test20; test20a; test21; test22; test23; test24; test25;
   test26; test27; test28; (*test29;*) test30; (*test31;*) test32;]

let udp_tests = []

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_recv_tests handle hosts_list test_type =
  begin_next_test_group handle "recv()";
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

  let snd_of_quad (a,b,c,d) = b in

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
