(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: send()                              *)
(* Steve Bishop - Created 20030707                                        *)
(* $Id: send.ml,v 1.24 2006/06/07 11:52:45 amgb2 Exp $ *)
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

(* ---------------------------------------------------------------------- *)

let test1 = (
  function zero_data -> (
  function (st, str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = if zero_data then
      (tid_of_int_private 0, SEND(fd, None, "", []))
    else
      (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd last_dg),
  "send() -- for a fresh non-blocking socket in state " ^ str ^ ", send() " ^ (if zero_data then "zero bytes of" else "some bytes of") ^ " data (should fail)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)))

let test2 = (
  function zero_data -> (
  function (st, str) -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts st false in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = if zero_data then
      (tid_of_int_private 0, SEND(fd, None, "", []))
    else
      (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd last_dg),
  "send() -- for a fresh blocking socket in state " ^ str ^ ", send() " ^ (if zero_data then "zero bytes of" else "some bytes of") ^ " data (should fail)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)))

(* ---------------------------------------------------------------------- *)

let test3 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_CLOSE_WAIT(DATA_SENT_RCVD)) false in
    let last_dgram = ref last_dg in
    (* A slurper callback function that waits to rcv some data on the wire *)
    (* and ACKs it appropriately *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    delay 5.00;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a fresh non-blocking socket in state CLOSE_WAIT(DATA_SENT_RCVD), send() some data (should fail)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test4 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_CLOSE_WAIT(DATA_SENT_RCVD)) false in
    let last_dgram = ref last_dg in
    (* A slurper callback function that waits to rcv some data on the wire *)
    (* and ACKs it appropriately *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    delay 5.00;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a fresh blocking socket in state CLOSE_WAIT(DATA_SENT_RCVD), send() some data (should fail)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test5 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    (* A slurper callback function that waits to rcv some data on the wire *)
    (* and ACKs it appropriately *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    delay 5.00;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a fresh non-blocking socket in state ESTABLISHED(NO_DATA), send() some data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test6 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    (* A slurper callback function that waits to rcv some data on the wire *)
    (* and ACKs it appropriately *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    delay 5.00;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a fresh blocking socket in state ESTABLISHED(NO_DATA), send() some data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test7 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a fresh non-blocking socket in state ESTABLISHED(NO_DATA), send() no data",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test8 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a fresh blocking socket in state ESTABLISHED(NO_DATA), send() no data",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test9 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [MSG_PEEK])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a fresh blocking socket in state ESTABLISHED(NO_DATA), send() no data with the MSG_PEEK flag set (should fail)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test10 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [MSG_WAITALL])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a fresh blocking socket in state ESTABLISHED(NO_DATA), send() no data with the MSG_WAITALL flag set (should fail)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test11 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, false, true)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a fresh blocking socket in state ESTABLISHED(NO_DATA) but with the send half of the connection shutdown(), attempt to send() some data (should fail)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test12 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILLFILL", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is full, attempt to send() some data (should fail)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test12a = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 15)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDLOWAT,10)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILLFILL", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "bl", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with a send buffer with 3 bytes of space and SO_SNDLOWAT set to 10, try to send some data (should fail)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test12b = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 15)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDLOWAT,10)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILLFILL", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let _ = Thread.create (function () ->
      let send_call = (tid_of_int_private 0, SEND(fd, None, "bl", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)) () in
    delay 30.0;
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a send buffer with 3 bytes of space and SO_SNDLOWAT set to 10, try to send some data (should block)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test12c = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    delay 0.8;
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,15)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDLOWAT,8)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "abcdefghijkl",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let _ = Thread.create (function () ->
      let send_call = (tid_of_int_private 0, SEND(fd,None,"mnopq",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"rstuvwxy",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)) () in
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is almost full, attempt to send() more data that there is not enough space available for but less than SO_SNDLOWAT; then the data is acked and see what happens to the send call",
  ((true,false),true,true,false),
  ((false,false),false,false,true)

let test12d = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    delay 0.8;
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,false,true)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,15)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDLOWAT,8)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "abcdefghijkl",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let _ = Thread.create (function () ->
      let send_call = (tid_of_int_private 0, SEND(fd,None,"mnopq",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"rstuvwxy",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)) () in
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a blocking socket in state ESTABLISHED(NO_DATA) that is shutdown for writing, with a reduced send buffer that is almost full, attempt to send() more data that there is space available but less than SO_SNDLOWAT; then the data is acked and see what happens to the send call",
  ((true,false),true,true,false),
  ((false,false),false,false,true)

let test12e = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_CLOSE_WAIT(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    delay 0.2;
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,15)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDLOWAT,8)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "abcdefghijkl",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let _ = Thread.create (function () ->
      let send_call = (tid_of_int_private 0, SEND(fd,None,"mnopq",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"rstuvwxy",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)) () in
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a blocking socket in state CLOSE_WAIT(NO_DATA), with a reduced send buffer that is almost full, attempt to send() more data that there is space available but less than SO_SNDLOWAT; then the data is acked and see what happens to the send call",
  ((true,false),true,true,false),
  ((false,false),false,false,true)

let test12f = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    delay 0.8;
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,15)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDLOWAT,8)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "abcdefghijkl",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let _ = Thread.create (function () ->
      let send_call = (tid_of_int_private 0, SEND(fd,None,"mn",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"rstuvwxy",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)) () in
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is almost full, attempt to send() more data that there is space available but less than SO_SNDLOWAT; then the data is acked and see what happens to the send call",
  ((true,false),true,true,false),
  ((false,false),false,false,true)

let test12g = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    delay 0.8;
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,15)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDLOWAT,1)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "abcdefghijkl",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let _ = Thread.create (function () ->
      let send_call = (tid_of_int_private 0, SEND(fd,None,"mn",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"rstuvwxy",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)) () in
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is almost full, attempt to send() more data that there is not enough space available and greater than SO_SNDLOWAT; then the data is acked and see what happens to the send call",
  ((true,false),true,true,false),
  ((false,false),false,false,true)

let test12h = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    delay 0.8;
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,33)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDLOWAT,6)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "abcde",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let _ = Thread.create (function () ->
      let send_call = (tid_of_int_private 0, SEND(fd,None,"m",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"n",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call);
      let send_call = (tid_of_int_private 0, SEND(fd,None,"rstuvwxy",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)) () in
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is almost full, attempt to send() more data: make two send() calls of one byte of data then another of 8 bytes data (should test the nagle algorithm)",
  ((true,false),true,true,false),
  ((false,false),false,false,true)

let test13 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILL", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is almost full, attempt to send() more data than there is space available(should give a partial send)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test14 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsocknopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocknopt_call);
    let setsocktopt_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_SNDTIMEO, None)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocktopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILLFI", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let _ = Thread.create (function () ->
      let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)) () in
    delay 15.00;
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is full and with SO_SNDTIMEO=0, attempt to send() some data (may block completely)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test14a = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsocknopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocknopt_call);
    let setsocktopt_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_SNDTIMEO, None)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocktopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILLFI", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let _ = Thread.create (function () ->
      let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)) () in
    delay 5.00;
    (* A slurper callback function that waits to rcv some data on the wire *)
    (* and ACKs it appropriately *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    delay 5.00;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is full and with SO_SNDTIMEO=0, attempt to send() some data and allow it to succeed eventually by forcing psyche to ACK some of the earlier segments",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test15 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsocknopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocknopt_call);
    let setsocktopt_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_SNDTIMEO, Some(5,0))) in
    ignore(libd_call (the ts.th_libd_hnd) setsocktopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILLFI", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is full and with SO_SNDTIMEO!=0, attempt to send() some data (send should eventually timeout)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test16 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsocknopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocknopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILLFI", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [MSG_DONTWAIT])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is full, send() some data with the MSG_DONTWAIT flag set (should behave like a non-blocking call)",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test17 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
     let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [MSG_DONTWAIT])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with space available in the send buffer, attempt to send() some data with the MSG_DONTWAIT set",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test18 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsocknopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDLOWAT, 5)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocknopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with SO_SNDLOWAT set to 5, attempt to send() more than 5 bytes. Note: THIS TEST MAY NOT WORK ON WINXP as SO_SNDLOWAT is not available.",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test19 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsocknopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDLOWAT, 5)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocknopt_call);
     let send_call = (tid_of_int_private 0, SEND(fd, None, "Test#", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with SO_SNDLOWAT set to 5, attempt to send exactly 5 bytes of data. Note: THIS TEST MAY NOT WORK ON WINXP as SO_SNDLOWAT is not available.",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test20 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsocknopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDLOWAT, 5)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocknopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "Tst", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with SO_SNDLOWAT set to 5, attempt to send less than 5 bytes of data. Note: THIS TEST MAY NOT WORK ON WINXP as SO_SNDLOWAT is not available.",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test21 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "Tst", [MSG_OOB])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with adequate space available in the send buffer, attempt to send() some data with the MSG_OOB flag set",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

let test22 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsocknopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocknopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILLFI", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "U", [MSG_OOB])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is full, attempt to send() one byte of data with the MSG_OOB flag set",
    ((true, false), true, true, false),
    ((false, false), false, false, true)


let test23 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let setsocknopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd, SO_SNDBUF, 10)) in
    ignore(libd_call (the ts.th_libd_hnd) setsocknopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FILLFILLFI", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "URGENT!URGENT!URGENT!", [MSG_OOB])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd !last_dgram),
    "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is full, attempt to send() lots of data (21 bytes) with the MSG_OOB flag set",
    ((true, false), true, true, false),
    ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test24 = (
  function zero_data -> (function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_FIN_WAIT_2(DATA_SENT_RCVD)) false in
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, true, false)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
    let send_call = if zero_data then
      (tid_of_int_private 0, SEND(fd, None, "", []))
    else
      (tid_of_int_private 0, SEND(fd, None, "### Test data ###", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    rst_driven_socket ts id fd last_dg),
  "send() -- for a fresh non-blocking socket in state FIN_WAIT_2(DATA_SENT_RCVD) and with the receive-half of the connection shutdown, send() " ^ (if zero_data then "zero bytes of" else "some bytes of") ^ " data (should fail)",
  ((true, false), true, true, false),
  ((false, false), false, false, true))

(* ---------------------------------------------------------------------- *)

let test25 = (
  function id -> function ts ->
    let fd,last_dg,_ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				rST = true;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let send_call = (tid_of_int_private 0, SEND(fd,None,"blah",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    delay 1.0;
    let send_call = (tid_of_int_private 0, SEND(fd,None,"hmph",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a socket in state ESTABLISHED send it a RST and then call send() (should fail with ECONNRESET)",
  ((true,false),true,true,false),
  ((false,false),false,false,true)

let test26 = (
  function id -> function ts ->
    let fd, last_dg, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				rST = true;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    delay 0.5;
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,15)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDLOWAT,8)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd, None, "abcdefghijkl",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    let _ = Thread.create (function () ->
      let send_call = (tid_of_int_private 0, SEND(fd,None,"mnopq",[])) in
      ignore(libd_call (the ts.th_libd_hnd) send_call)) () in
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer that is almost full, attempt to send() more data that there is space available but less than SO_SNDLOWAT; so that the call blocks; then send a RST and see if the call fails with a pending error",
  ((true,false),true,true,false),
  ((false,false),false,false,true)



(* ---------------------------------------------------------------------- *)

let test27 = (
  function id -> function ts ->
    let fd,last_dg,_ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				rST = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,3)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd,None,"abcdefghijklmnopqrstuvwxyz",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer of 3, send a long string (should result in several segments with data of length 3 being sent)",
  ((true,false),true,true,false),
  ((false,false),false,false,true)

let test28 = (
  function id -> function ts ->
    let fd,last_dg,_ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				rST = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    delay 0.5;
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,3)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd,None,"abcdefghijklmnopqrstuvwxyz",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer of 3, send a long string with the ack delayed",
  ((true,false),true,true,false),
  ((false,false),false,false,true)

let test29 = (
  function id -> function ts ->
    let fd,last_dg,_ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				rST = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,3)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd,[O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = (tid_of_int_private 0, SEND(fd,None,"abcdefghijklmnopqrstuvwxyz",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer of 3, send a long string",
  ((true,false),true,true,false),
  ((false,false),false,false,true)


let test30 = (
  function id -> function ts ->
    let fd,last_dg,_ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				rST = false;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    delay 0.5;
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,3)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd,[O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let send_call = (tid_of_int_private 0, SEND(fd,None,"abcdefghijklmnopqrstuvwxyz",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    delay 5.0;
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a non-blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer of 3, send a long string with the ack delayed by half a second",
  ((true,false),true,true,false),
  ((false,false),false,false,true)

let test31 = (
  function id -> function ts ->
    let fd,last_dg,_ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let last_dgram = ref last_dg in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (List.length datagram.data > 0) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let ack_datagram = {datagram with
				is1 = datagram.is2;
				is2 = datagram.is1;
				ps1 = datagram.ps2;
				ps2 = datagram.ps1;
				sYN = false;
				aCK = true;
				fIN = false;
				rST = true;
				seq = datagram.ack;
				ack = datagram.seq +. (uint (List.length datagram.data)) +.
				if datagram.fIN = true then (uint 1) else (uint 0);
				ts = timestamp_update_swap datagram.ts (uint 1);
				data = []} in
	    delay 0.5;
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram));
	    last_dgram := RECV_DATAGRAM(ack_datagram)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let setsockopt_call = (tid_of_int_private 0, SETSOCKNOPT(fd,SO_SNDBUF,3)) in
    ignore(libd_call (the ts.th_libd_hnd) setsockopt_call);
    let send_call = (tid_of_int_private 0, SEND(fd,None,"abcdefghijklmnopqrstuvwxyz",[])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    delay 5.0;
    let getsockname_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) getsockname_call);
    let getpeername_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) getpeername_call);
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_dgram),
  "send() -- for a blocking socket in state ESTABLISHED(NO_DATA), with a reduced send buffer of 3, send a long string with a RST-ACK sent after half a second. Should show that a blocking send will fail if the socket is shutdown for writing.",
  ((true,false),true,true,false),
  ((false,false),false,false,true)





(* ---------------------------------------------------------------------- *)

let states1 =
  let rec remove_states driven_list =
    match driven_list with
      [] -> []
    | (ST_ESTABLISHED(_), y)::xs -> remove_states xs
    | (ST_CLOSE_WAIT(_), y)::xs -> remove_states xs
    | (x, y)::xs -> (x, y)::(remove_states xs) in
  remove_states all_interesting_driven_states

let make_test_1_2_list test =
  List.flatten (
    List.map (function t -> List.map t states1)
     (List.map test [true; false]))

let tcp_tests =
  make_test_1_2_list test1 @ make_test_1_2_list test2 @
  [test3; test4; test5; test6; test7; test8;
   test9; test10; test11; test12; test12a; test12b;
   test12c; test12d; test12e; test12f; test12g; test12h; test13;
   test14; test14a; (*test15; test16;*) test17;
   test18; test19; test20; test21; test22; test23;] @
  (List.map test24 [true; false]) @ [test25; test26; test27; test28; test29; test30; test31]
(*[test12h; test12; test12a; test12b; test12c;test12d;test12e;test12f;test12g;test27;test28;test29;test30]*)

let udp_tests = []

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_send_tests handle hosts_list test_type =
  begin_next_test_group handle "send()";
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
