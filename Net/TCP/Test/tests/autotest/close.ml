(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: close()                             *)
(* Steve Bishop - Created 20030430                                        *)
(* $Id: close.ml,v 1.28 2006/06/07 11:52:45 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread
open Printf

(* Our libraries *)
open Nettypes
open Tthee
open Ttheehelper
open Testscommon
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
(* ALL STATES EXCEPT LISTEN, ESTABLISHED *)

let test1 = (function (st, stdescr) ->
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts st false in
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
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a blocking socket in state " ^ stdescr ^ ", call close()",
  ((true, false), true, true, false),
  ((false, false), false, false, true))

let test2 = (function (st, stdescr) ->
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts st false in
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
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a non-blocking socket in state " ^ stdescr ^ ", call close()",
  ((true, false), true, true, false),
  ((false, false), false, false, true))

(* ---------------------------------------------------------------------- *)
(* FROM CLOSE_WAIT STATE *)

let test3 = (function (linger, lingerdescr) ->
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_CLOSE_WAIT(DATA_SENT_RCVD)) false in
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
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* Set the linger *)
    let linger_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_LINGER, linger)) in
    ignore(libd_call th_libd linger_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a non-blocking socket in state CLOSE_WAIT(DATA_SENT_RCVD), call close() with " ^ lingerdescr,
  ((true, false), true, true, false),
  ((false, false), false, false, true))

let test4 = (function (linger, lingerdescr) ->
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_CLOSE_WAIT(DATA_SENT_RCVD)) false in
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
    (* Set the linger *)
    let linger_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_LINGER, linger)) in
    ignore(libd_call th_libd linger_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a blocking socket in state CLOSE_WAIT(DATA_SENT_RCVD), call close() with " ^ lingerdescr,
  ((true, false), true, true, false),
  ((false, false), false, false, true))

(* ---------------------------------------------------------------------- *)
(* FROM LISTEN STATE *)

let test5 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts ST_LISTEN false in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 2.0; rst_driven_socket ts id fd NO_DATAGRAMS),
  "close(): for non-blocking socket in the LISTEN state and with no connections waiting, call close()",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test6 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts ST_LISTEN false in
    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_syn_ack = ref false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    (datagram.sYN = true) && (datagram.aCK = true)
	  then
	    (Mutex.lock lock;
	     seen_syn_ack := true;
	     last_datagram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond;
	     Mutex.unlock lock)
	   else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
     (* Inject a SYN packet *)
    let syn_packet = {
      is1 = Some(hol_ip id.virtual_host_ip);
      is2 = Some(hol_ip id.test_host.test_ip_address);
      ps1 = Some(uint id.virtual_host_port);
      ps2 = Some(uint id.test_host.test_ephm_port);
      seq = uint 10000;
      ack = uint 0;
      uRG = false;
      aCK = false;
      pSH = false;
      rST = false;
      sYN = true;
      fIN = false;
      win = uint 512;
      urp = uint 0;
      mss = None;
      scale = None;
      ts = None;
      data = [];
    } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_packet));
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* Block on condition variable here until we verify that the SYN was sent *)
    Mutex.lock lock;
    while !seen_syn_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 10.0;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a non-blocking socket in the LISTEN state and with a connection in the syn cache, call close()",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test7 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    let ah_libd = the ts.ah_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts ST_LISTEN false in
    (* Make a connection of the aux host to the test host listening socket *)
    let afd = get_socket ah_libd in
    let connect_call = (tid_of_int_private 0,
			CONNECT(afd, Ocamllib.ip_of_string (string_ip id.test_host.test_ip_address),
				Some(Ocamllib.port_of_int (id.test_host.test_ephm_port)))) in
    ignore(libd_call ah_libd connect_call);
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    delay 1.00;
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    let close_call = (tid_of_int_private 0, CLOSE(afd)) in
    ignore(libd_call ah_libd close_call);
    delay 2.0; rst_driven_socket ts id fd NO_DATAGRAMS),
  "close(): for a non-blocking socket in the LISTEN state and with a connection on the accept queue, call close()",
  ((true, false), true, true, false),
  ((true, false), false, false, true)

let test8 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts ST_LISTEN false in
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 2.0; rst_driven_socket ts id fd NO_DATAGRAMS),
  "close(): for a blocking socket in the LISTEN state and with no connections waiting, call close()",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test9 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts ST_LISTEN false in
    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_syn_ack = ref false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    (datagram.sYN = true) && (datagram.aCK = true)
	  then
	    (Mutex.lock lock;
	     seen_syn_ack := true;
	     last_datagram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond;
	     Mutex.unlock lock)
	   else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    (* Inject a SYN packet *)
    let syn_packet = {
      is1 = Some(hol_ip id.virtual_host_ip);
      is2 = Some(hol_ip id.test_host.test_ip_address);
      ps1 = Some(uint id.virtual_host_port);
      ps2 = Some(uint id.test_host.test_ephm_port);
      seq = uint 10000;
      ack = uint 0;
      uRG = false;
      aCK = false;
      pSH = false;
      rST = false;
      sYN = true;
      fIN = false;
      win = uint 512;
      urp = uint 0;
      mss = None;
      scale = None;
      ts = None;
      data = [];
    } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_packet));
    (* Block on condition variable here until we verify that the SYN was sent *)
    Mutex.lock lock;
    while !seen_syn_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 10.0; rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a blocking socket in the LISTEN state and with a connection in the syn cache, call close()",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test10 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    let ah_libd = the ts.ah_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts ST_LISTEN false in
    (* Make a connection of the aux host to the test host listening socket *)
    let afd = get_socket ah_libd in
    let connect_call = (tid_of_int_private 0,
			CONNECT(afd, Ocamllib.ip_of_string (string_ip id.test_host.test_ip_address),
				Some(Ocamllib.port_of_int (id.test_host.test_ephm_port)))) in
    ignore(libd_call ah_libd connect_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    let close_call = (tid_of_int_private 0, CLOSE(afd)) in
    ignore(libd_call ah_libd close_call);
    delay 2.0; rst_driven_socket ts id fd NO_DATAGRAMS),
  "close(): for a blocking socket in the LISTEN state and with a connection on the accept queue, call close()",
  ((true, false), true, true, false),
  ((true, false), false, false, true)

(* ---------------------------------------------------------------------- *)
(* FROM ESTABLISHED STATE *)

let test11 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) true in
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
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a non-blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, duplicate the file descriptor and close the original descriptor",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test12 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) true in
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
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(the fd2)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a non-blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, duplicate the file descriptor and close the duplicate",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test13 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) true in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* A slurper callback function sends a FIN,ACK when a FIN is seen and signals *)
    (* a condition when it has seen its own FIN,ACK *)
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_finack = ref false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps1 = Some(uint id.virtual_host_port)) &&
	    (datagram.fIN = true) && (datagram.aCK = true)
	  then
	    (Mutex.lock lock;
	     seen_finack := true;
	     last_datagram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond;
	     Mutex.unlock lock)
	  else if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    (datagram.fIN = true)
	  then
	    let finack_datagram = {datagram with
				   is1 = datagram.is2;
				   is2 = datagram.is1;
				   ps1 = datagram.ps2;
				   ps2 = datagram.ps1;
				   sYN = false; aCK = true; fIN = true;
				   seq = datagram.ack;
				   ack = datagram.seq +. (uint (List.length datagram.data)) +. (uint 1);
				   ts = timestamp_update_swap datagram.ts (uint 1);
				   data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(finack_datagram))
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    (* Make the close calls *)
    let close_call = (tid_of_int_private 0, CLOSE(the fd2)) in
    ignore(libd_call th_libd close_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Block on condition variable here until we verify that the FIN,ACK was seen *)
    Mutex.lock lock;
    while !seen_finack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd),
  "close(): for a non-blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, duplicate the file descriptor and close both the original and duplicate descriptors",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test14 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) true in
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
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, duplicate the file descriptor and close the original descriptor",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test15 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) true in
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
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(the fd2)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, duplicate the file descriptor and close the duplicate",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test16 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) true in
    (* A slurper callback function sends a FIN,ACK when a FIN is seen and signals *)
    (* a condition when it has seen its own FIN,ACK *)
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_finack = ref false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps1 = Some(uint id.virtual_host_port)) &&
	    (datagram.fIN = true) && (datagram.aCK = true)
	  then
	    (Mutex.lock lock;
	     seen_finack := true;
	     last_datagram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond;
	     Mutex.unlock lock)
	  else if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    (datagram.fIN = true)
	  then
	    let finack_datagram = {datagram with
				   is1 = datagram.is2;
				   is2 = datagram.is1;
				   ps1 = datagram.ps2;
				   ps2 = datagram.ps1;
				   sYN = false; aCK = true; fIN = true;
				   seq = datagram.ack;
				   ack = datagram.seq +. (uint (List.length datagram.data)) +. (uint 1);
				   ts = timestamp_update_swap datagram.ts (uint 1);
				   data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(finack_datagram))
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    (* Make the close calls *)
    let close_call = (tid_of_int_private 0, CLOSE(the fd2)) in
    ignore(libd_call th_libd close_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Block on condition variable here until we verify that the FIN,ACK was seen *)
    Mutex.lock lock;
    while !seen_finack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Tidy up, if required *)
    delay 3.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, duplicate the file descriptor and close both the original and duplicate descriptors",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test17 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    let last_datagram_seen = ref last_dgram in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    delay 5.0;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a non-blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, call close() such that close does not succeed (as psyche does not respond to the FIN)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test18 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* A slurper callback function sends a FIN,ACK when a FIN is seen and signals *)
    (* a condition when it has seen its own FIN,ACK *)
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_ack = ref false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps1 = Some(uint id.virtual_host_port)) &&
	    (datagram.aCK = true)
	  then
	    (Mutex.lock lock;
	     seen_ack := true;
	     last_datagram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond;
	     Mutex.unlock lock)
	  else if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    (datagram.fIN = true)
	  then
	    let ack_datagram = {datagram with
				   is1 = datagram.is2;
				   is2 = datagram.is1;
				   ps1 = datagram.ps2;
				   ps2 = datagram.ps1;
				   sYN = false; aCK = true; fIN = false;
				   seq = datagram.ack;
				   ack = datagram.seq +. (uint (List.length datagram.data)) +. (uint 1);
				ts = timestamp_update_swap datagram.ts (uint 1);
				   data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_datagram))
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    (* Make the close calls *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Block on condition variable here until we verify that the ACK was seen *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Tidy up, if required *)
    delay 5.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a non-blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, call close with no linger",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test19 =
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
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* Set zero linger *)
    let linger_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_LINGER, Some(0,0))) in
    ignore(libd_call th_libd linger_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 5.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a non-blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, call close() with zero linger",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test20 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* A slurper callback function sends a FIN,ACK when a FIN is seen and signals *)
    (* a condition when it has seen its own FIN,ACK *)
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_ack = ref false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps1 = Some(uint id.virtual_host_port)) &&
	    (datagram.aCK = true)
	  then
	    (Mutex.lock lock;
	     seen_ack := true;
	     last_datagram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond;
	     Mutex.unlock lock)
	  else if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    (datagram.fIN = true)
	  then
	    let finack_datagram = {datagram with
				   is1 = datagram.is2;
				   is2 = datagram.is1;
				   ps1 = datagram.ps2;
				   ps2 = datagram.ps1;
				   sYN = false; aCK = true; fIN = false;
				   seq = datagram.ack;
				   ack = datagram.seq +. (uint (List.length datagram.data)) +. (uint 1);
				   ts = timestamp_update_swap datagram.ts (uint 1);
				   data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(finack_datagram))
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    (* Set zero linger *)
    let linger_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_LINGER, Some(5,0))) in
    ignore(libd_call th_libd linger_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Block on condition variable here until we verify that the FIN,ACK was seen *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Tidy up, if required *)
    delay 15.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a non-blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, call close() with a non-zero linger (psyche responds to the FIN before the linger timer expires)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test21 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    (* Set non-blocking mode *)
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd setfflag_call);
    (* A slurper callback function sends a FIN,ACK when a FIN is seen and signals *)
    (* a condition when it has seen its own FIN,ACK *)
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_finack = ref false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    ((datagram.rST = true) || (datagram.fIN = true))
	  then
	    (Mutex.lock lock;
	     seen_finack := true;
	     last_datagram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond;
	     Mutex.unlock lock)
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    (* Send some data *)
    let send_call = (tid_of_int_private 0, SEND(fd, None, "SOME DATA TO TEST LINGER", [])) in
    ignore(libd_call th_libd send_call);
    (* Set zero linger *)
    let linger_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_LINGER, Some(5,5))) in
    ignore(libd_call th_libd linger_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    delay 10.0;
    if(id.test_host.platform_type = ARCH_WINXP) then
      (inter_test_delay 240.0;
       (* Make the close call again (as we probably got EAGAIN the first time! *)
       let close_call = (tid_of_int_private 0, CLOSE(fd)) in
       ignore(libd_call th_libd close_call);
       (* Make the close call again (to confirm that the fd went away) *)
       let close_call = (tid_of_int_private 0, CLOSE(fd)) in
       ignore(libd_call th_libd close_call)
      )
    else
      (
      (* Block on condition variable here until we verify that the FIN,ACK was seen *)
       Mutex.lock lock;
       while !seen_finack = false do
	 Condition.wait cond lock;
       done;
       Mutex.unlock lock
      );
    (* Tidy up, if required *)
    delay 5.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a non-blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, call close() with a non-zero linger and allow the timeout to occur (as psyche does not respond)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* ---------------------------------------------------------------------- *)

let test22 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    (* A slurper callback function sends a FIN,ACK when a FIN is seen and signals *)
    (* a condition when it has seen its own FIN,ACK *)
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_ack = ref false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps1 = Some(uint id.virtual_host_port)) &&
	    (datagram.aCK = true)
	  then
	    (Mutex.lock lock;
	     seen_ack := true;
	     last_datagram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond;
	     Mutex.unlock lock)
	  else if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    (datagram.fIN = true)
	  then
	    let finack_datagram = {datagram with
				   is1 = datagram.is2;
				   is2 = datagram.is1;
				   ps1 = datagram.ps2;
				   ps2 = datagram.ps1;
				   sYN = false; aCK = true; fIN = false;
				   seq = datagram.ack;
				   ack = datagram.seq +. (uint (List.length datagram.data)) +. (uint 1);
				   ts = timestamp_update_swap datagram.ts (uint 1);
				   data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(finack_datagram))
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    (* Make the close calls *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Block on condition variable here until we verify that the FIN,ACK was seen *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Tidy up, if required *)
    delay 5.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, call close() with no linger",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test23 =
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
    (* Set zero linger *)
    let linger_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_LINGER, Some(0,0))) in
    ignore(libd_call th_libd linger_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    delay 5.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, call close() with zero linger",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test24 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    (* A slurper callback function sends a FIN,ACK when a FIN is seen and signals *)
    (* a condition when it has seen its own FIN,ACK *)
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_ack = ref false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps1 = Some(uint id.virtual_host_port)) &&
	    (datagram.aCK = true)
	  then
	    (Mutex.lock lock;
	     seen_ack := true;
	     last_datagram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond;
	     Mutex.unlock lock)
	  else if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    (datagram.fIN = true)
	  then
	    let finack_datagram = {datagram with
				   is1 = datagram.is2;
				   is2 = datagram.is1;
				   ps1 = datagram.ps2;
				   ps2 = datagram.ps1;
				   sYN = false; aCK = true; fIN = false;
				   seq = datagram.ack;
				   ack = datagram.seq +. (uint (List.length datagram.data)) +. (uint 1);
				   ts = timestamp_update_swap datagram.ts (uint 1);
				   data = []} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(finack_datagram))
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    (* Set zero linger *)
    let linger_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_LINGER, Some(5,0))) in
    ignore(libd_call th_libd linger_call);
    (* Make the close call *)
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Block on condition variable here until we verify that the FIN,ACK was seen *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;
    (* Tidy up, if required *)
    delay 15.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, call close() with a non-zero linger (psyche responds to the FIN before the linger timer expires)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test25 =
  (function id -> function ts ->
    let th_libd = the ts.th_libd_hnd in
    (* Get a socket in specific state *)
    let fd, last_dgram, fd2 = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    (* A slurper callback function sends a FIN,ACK when a FIN is seen and signals *)
    (* a condition when it has seen its own FIN,ACK *)
    let lock = Mutex.create () in
    let cond = Condition.create () in
    let seen_rst = ref false in
    let last_datagram_seen = ref last_dgram in
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
            ((datagram.rST = true)  || (datagram.fIN = true))
	  then
	    (Mutex.lock lock;
	     seen_rst := true;
	     last_datagram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond;
	     Mutex.unlock lock)
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    (* Send some data *)
    let send_call = (tid_of_int_private 0, SEND(fd, None, "SOME DATA TO TEST LINGER", [])) in
    ignore(libd_call th_libd send_call);
    (* Make the close call *)
    (* Set zero linger *)
    let linger_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_LINGER, Some(5,0))) in
    ignore(libd_call th_libd linger_call);
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call th_libd close_call);
    (* Tidy up, if required *)
    inter_test_delay 25.0;
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd !last_datagram_seen),
  "close(): for a blocking socket in the ESTABLISHED(DATA_SENT_RVCD) state, call close() with a non-zero linger. Pysche does not repond to the FIN and thus the linger timeout occurs",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test26 = (
  function sf ->
    ((function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      let close_call = (tid_of_int_private 0, CLOSE(fd)) in
      ignore(libd_call (the ts.th_libd_hnd) close_call)),
     "close() -- for a UDP socket with binding quad " ^ (string_of_bound_udp_quad sf) ^ ", call close()",
     ((true,false),true,false,false),
     ((false,false),false,false,true))
 )

(* ---------------------------------------------------------------------- *)

let ds1 =
  let rec remove_states driven_list =
    match driven_list with
      [] -> []
    | (ST_LISTEN,y)::xs -> remove_states xs
    | (ST_ESTABLISHED(_),y)::xs -> remove_states xs
    | (x,y)::xs -> (x,y)::(remove_states xs) in
  remove_states all_interesting_driven_states

let tcp_tests =
  (List.map test1 ds1) @
  (List.map test2 ds1) @
  [test5; test6; test7; test8; test9; test10; test17; test18;
   test19; test20; test21; test22; test23; test24; test25;] @
  (List.map test3 [(None, "no linger"); (Some(0,0), "zero linger");
		   (Some(2,2), "non-zero linger");]) @
  (List.map test4  [(None, "no linger"); (Some(0,0), "zero linger");
		   (Some(2,2), "non-zero linger");])

let non_win32_normal_tests = [test11; test12; test13; test14; test15; test16;]

let udp_tests = List.map test26 all_sock_flavours

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []

let udp_exhaustive_tests = []

let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_close_tests handle hosts_list test_type =
  begin_next_test_group handle "close()";
  let done_a_test = ref false in
  let num_of_tests = ref 0 in

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
	      next_test handle;
	    with Unix.Unix_error(e,_,_) ->
	      if n = 0 then raise (Test_failed ("Unix_error:" ^ (Unix.error_message e)))
	      else
		(delay (float_of_int (n * 30));
		 do_test test_thunk descr thts ahts (n-1)) in
	  do_test test_thunk descr thts ahts 10;
	  if host.platform_type = ARCH_WINXP then num_of_tests := !num_of_tests + 1;)

	(match test_type with
	  TCP_NORMAL ->
	    (if host.platform_type = ARCH_WINXP then tcp_tests
	    else tcp_tests @ non_win32_normal_tests)
	| UDP_NORMAL -> udp_tests
	| ALL_NORMAL ->
	    (if host.platform_type = ARCH_WINXP then normal_tests
	    else normal_tests @ non_win32_normal_tests)
	| TCP_EXHAUSTIVE -> tcp_exhaustive_tests
	| UDP_EXHAUSTIVE -> udp_exhaustive_tests
	| ALL_EXHAUSTIVE -> exhaustive_tests
  | STREAM_NORMAL -> []
  | STREAM_EXHAUSTIVE -> [])
    )
    hosts_list;
  !done_a_test

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
