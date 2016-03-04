(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: deliver_in                          *)
(* Steve Bishop - Created 20030725                                        *)
(* $Id: deliver_in.ml,v 1.24 2006/06/07 11:52:45 amgb2 Exp $ *)
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
open Testscommon
open Dual
open Dualdriven
open Testscommon
(* ---------------------------------------------------------------------- *)
(* deliver_in_1 *)
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

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip broadcast_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment from broadcast address",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test1a =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    let broadcast_addr =
      let a,b,c,d = id.test_host.test_ip_address in
      let s,t,u,v = id.test_host.test_subnet_mask in
      ((a land s) lor ((lnot s) mod 256),
       (b land t) lor ((lnot t) mod 256),
       (c land u) lor ((lnot u) mod 256),
       (d land v) lor ((lnot v) mod 256)) in
    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip broadcast_addr)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip broadcast_addr);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment to a broadcast address",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test2 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip multicast_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment from multicast address",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* test3 removed as doesn't work on a switched network *)

(*
let test3 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip unused_ip)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip unused_ip);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment to ip address that is not assigned to tests hosts interface",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
*)
let test4 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment to ip address that is assigned to tests hosts interface",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test6 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			pSH = true;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with PSH set",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test7 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			ack = uint 123456;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with non-zero ack",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test8 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			urp = uint 123456;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with non-zero urp",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test9 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			mss = Some(uint 1024);
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with mss set(1024)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test10 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			mss = Some(uint 512);
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with mss set(512)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test11 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			mss = Some(uint 550);
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with mss set(550)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test11a =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			mss = Some(uint 60000);
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with mss set(60000)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test12 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			scale = Some(uint 1);
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with scale option set(1)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test13 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			scale = Some(uint 14);
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with scale option set(14)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test13a =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			scale = Some(uint 15);
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with scale option set(15)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test14 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			win = uint 8192;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with window size set(8192)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test15 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			ts = Some(uint 89898989, uint 0);
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with timestamp set",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test16 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			mss = Some(uint 1046);
			win = uint 32786;
			scale = Some(uint 5);
			ts = Some(uint 89898989, uint 0);
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment with timestamp set, mss 1046, win 32786, scale 5",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test17 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_TIME_WAIT(NO_DATA)) false in
    let fd2, last_dgram2, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram2 in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			seq = uint 5000;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment to a listening socket that has socket quad associate with a TIME_WAIT socket. ISS < snd_nxt for TIME_WAIT socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test18 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_TIME_WAIT(NO_DATA)) false in
    let fd2, last_dgram2, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram2 in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			seq = uint 500000;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1: passive open, SYN segment to a listening socket that has socket quad associate with a TIME_WAIT socket. ISS > snd_nxt for TIME_WAIT socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let deliver_in_1 = [test1; (*test1a;*) test2; (*test3;*) test4; test6; test7;
        test8;
		    test9; test10; test11; test11a; test12; test13; (*test13a;*)
		    test14; test15; test16; test17; test18]


(* ---------------------------------------------------------------------- *)
(* deliver_in_1b *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip broadcast_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			sYN = true; aCK = true;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1b: passive open, bad datagram: SYN,ACK segment from broadcast address",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test1a =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

  let broadcast_addr =
      let a,b,c,d = id.test_host.test_ip_address in
      let s,t,u,v = id.test_host.test_subnet_mask in
      ((a land s) lor ((lnot s) mod 256),
       (b land t) lor ((lnot t) mod 256),
       (c land u) lor ((lnot u) mod 256),
       (d land v) lor ((lnot v) mod 256)) in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip broadcast_addr)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip broadcast_addr);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			sYN = true; aCK = true;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1b: passive open, bad datagram: SYN,ACK segment to broadcast address",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test2 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip multicast_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			sYN = true; aCK = true;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1b: passive open, bad datagram: SYN,ACK segment from multicast address",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* test3 currently disabled, as it doesn't work correctly (read: hangs
   forever) on a switched network *)

(*
let test3 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip unused_ip)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip unused_ip);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			sYN = true; aCK = true;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1b: passive open, bad datagram: SYN,ACK segment to non-local IP address",
  ((true, false), true, true, false),
  ((false, false), false, false, true)
*)

let test4 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.test_host.test_ip_address);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.test_host.test_ephm_port);
			ps2 = Some(uint id.test_host.test_ephm_port) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1b: passive open, forged SYN segment from the listening port (from self)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test5 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.test_host.test_ip_address);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.test_host.test_ephm_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			aCK = true;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1b: passive open, forged SYN,ACK segment from the listening port (from self)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test6 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			sYN = false; aCK = true;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1b: passive open, bad datagram: segment has only ACK set (not SYN)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test7 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = false) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port);
			sYN = false; aCK = false;
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1b: passive open, bad datagram: segment has only ACK set (not SYN)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test8 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.test_host.test_ephm_port)) &&
	    (datagram.ps1 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some((uint id.virtual_host_port) +. (uint 3));
			ps2 = Some(uint id.test_host.test_ephm_port);
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    let syn_segment = { syn_segment with
			ps1 = Some((uint id.virtual_host_port) +. (uint 2))
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    let syn_segment = { syn_segment with
			ps1 = Some((uint id.virtual_host_port) +. (uint 1))
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    let syn_segment = { syn_segment with
			ps1 = Some(uint id.virtual_host_port)
		      } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_1b: passive open, bad datagram: listening queue full",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

(* Test 3 removed as hangs forever on switched network (packet never reaches host) *)
(* Tests 4,5 removed as can't have is1=is2 in an injected packet -- injector dies *)
let deliver_in_1b = [test1; (*test1a;*) test2; (*test3;*) (*test4; test5;*) test6; test7; test8]


(* ---------------------------------------------------------------------- *)
(* deliver_in_2 *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2: test1: expected a SENT_DATAGRAM here")) in

    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = true;
			   seq = uint 1000; ack = dg.seq +. (uint 1)} in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2: completion of active open",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test1a =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2: test1: expected a SENT_DATAGRAM here")) in

    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = true;
			   seq = uint 1000; ack = dg.seq +. (uint 1);
                           data = [uint(Char.code 'b');
                                   uint(Char.code 'a');
                                   uint(Char.code 'r');]} in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* try to receive the data on the SYN,ACK segment *)
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let recv_call = (tid_of_int_private 0, RECV(fd, 3, [])) in
    ignore(libd_call (the ts.th_libd_hnd) recv_call);

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2: completion of active open with data sent on the SYN,ACK segment",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test1b =
  (function id -> function ts ->
    let fd, last_dgram, _ = drive_socket_established_nomss id ts false in
    delay 5.00;
    rst_driven_socket ts id fd NO_DATAGRAMS),
  "deliver_in_2: completion of active open with no MSS option on the SYN,ACK segment, followed by data being sent and received",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test2 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2: test2: expected a SENT_DATAGRAM here")) in

    let syn_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = false;
			   seq = uint 1000; ack = uint 0} in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    let dg' = match !last_dgram_seen with
      SENT_DATAGRAM(dg') -> dg'
    | _ -> raise(Assertion_failed("deliver_in_2: test2: expected a SENT_DATAGRAM here")) in

    (* Send the ACK to complete simultaneous open *)
    let ack_segment = {dg' with
                            is1 = dg.is2; is2 = dg.is1;
			    ps1 = dg.ps2; ps2 = dg.ps1;
			    sYN = false; aCK = true;
			    seq = uint 1001; ack = dg'.seq +. (uint 1);
                            mss = None; scale = None} in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_segment));

    delay 10.00;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2: completion of simultaneous open",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test3 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2: test3: expected a SENT_DATAGRAM here")) in

    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = true;
			   seq = uint 1000; ack = dg.seq +. (uint 1);
			   data = [uint(Char.code 'b'); uint(Char.code 'a');
				   uint(Char.code 'r');] } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2: completion of active open with data",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test4 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2: test4: expected a SENT_DATAGRAM here")) in

    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = true; fIN = true;
			   seq = uint 1000; ack = dg.seq +. (uint 1); } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2: completion of active open with FIN set",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test5 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2: test5: expected a SENT_DATAGRAM here")) in

    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = true;
			   seq = uint 1000; ack = dg.seq +. (uint 1)} in
    let send_call = (tid_of_int_private 0, SEND(fd, None, "FOOfoo", [])) in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));
    ignore(libd_call (the ts.th_libd_hnd) send_call);

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2: completion of active open, don't delay the ack",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test6 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let oobinline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, false)) in
    ignore(libd_call (the ts.th_libd_hnd) oobinline_call);

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2: test6: expected a SENT_DATAGRAM here")) in

    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = true; uRG = true;
			   seq = uint 1000; ack = dg.seq +. (uint 1);
			   urp = uint 1003;
			   data = [uint(Char.code 'b'); uint(Char.code 'a');
				   uint(Char.code 'r'); uint(Char.code 'b');
				   uint(Char.code 'a'); uint(Char.code 'r'); ] } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2: completion of active open with data, OOB data not inline in segment",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test7 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let oobinline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, false)) in
    ignore(libd_call (the ts.th_libd_hnd) oobinline_call);

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2: test7: expected a SENT_DATAGRAM here")) in

    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = true; uRG = true;
			   seq = uint 1000; ack = dg.seq +. (uint 1);
			   urp = uint 1005;
			   data = [uint(Char.code 'b'); uint(Char.code 'a');
				   uint(Char.code 'r');] } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2: completion of active open with data, OOB data not inline, not in segment",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test8 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let oobinline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, true)) in
    ignore(libd_call (the ts.th_libd_hnd) oobinline_call);

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2: test8: expected a SENT_DATAGRAM here")) in

    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = true; uRG = true;
			   seq = uint 1000; ack = dg.seq +. (uint 1);
			   urp = uint 1003;
			   data = [uint(Char.code 'b'); uint(Char.code 'a');
				   uint(Char.code 'r'); uint(Char.code 'b');
				   uint(Char.code 'a'); uint(Char.code 'r'); ] } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2: completion of active open with data, OOB data inline in segment",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test9 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let oobinline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, true)) in
    ignore(libd_call (the ts.th_libd_hnd) oobinline_call);

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2: test9: expected a SENT_DATAGRAM here")) in

    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = true; uRG = true;
			   seq = uint 1000; ack = dg.seq +. (uint 1);
			   urp = uint 1005;
			   data = [uint(Char.code 'b'); uint(Char.code 'a');
				   uint(Char.code 'r');] } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2: completion of active open with data, OOB data inline, not in segment",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let deliver_in_2 = [test1; test1a; test1b; test2; test3; test4; test5; test6; test7; test8; test9]

(* ---------------------------------------------------------------------- *)
(* deliver_in_2a *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     (*last_dgram_seen := RECV_DATAGRAM(datagram);*)
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2a: test1: expected a SENT_DATAGRAM here")) in
    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = true; aCK = true;
			   seq = uint 1000; ack = dg.seq -. (uint 10)} in  (* incorrect ACK *)
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2a: receive bad or boring datagram and RST or ignore for SYN_SENT socket: ack not in correct range",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test2 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = false) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     (*last_dgram_seen := RECV_DATAGRAM(datagram);*)
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2a: test2: expected a SENT_DATAGRAM here")) in
    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = false; aCK = false;
			   seq = uint 1000; ack = dg.seq +. (uint 1)} in  (* incorrect ACK *)
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2a: receive bad or boring datagram and RST or ignore for SYN_SENT socket: no SYN, no ACK (ignored)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test3 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) && (datagram.sYN = false) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     (*last_dgram_seen := RECV_DATAGRAM(datagram);*)
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let dg = match last_dgram with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_2a: test3: expected a SENT_DATAGRAM here")) in
    let syn_ack_segment = {dg with
			   is1 = dg.is2; is2 = dg.is1;
			   ps1 = dg.ps2; ps2 = dg.ps1;
			   sYN = false; aCK = true;
			   seq = uint 1000; ack = dg.seq +. (uint 1)} in  (* incorrect ACK *)
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_ack_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_2a: receive bad or boring datagram and RST or ignore for SYN_SENT socket: no SYN, ACK, ack in range",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let deliver_in_2a = [test1; test2; test3]


(* ---------------------------------------------------------------------- *)
(* deliver_in_3 *)
(* THIS RULES IS TESTED BY devlier_in_3.ml *)
(* --------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------- *)
(* deliver_in_4 *)
(* ---------------------------------------------------------------------- *)

(* TODO: checksum not valid, invalid options -- not possible with current *)
(* model *)

(* Testing with martian segments is performed in deliver_in_1 and deliver_in 1b *)
let deliver_in_4 = []

(* ---------------------------------------------------------------------- *)
(* deliver_in_5 *)
(* ---------------------------------------------------------------------- *)

let sane_segment = {
  is1 = None; is2 = None;
  ps1 = None; ps2 = None;
  seq = uint 5000;
  ack = uint 100;
  uRG = false; aCK = true;
  pSH = false; rST = false;
  sYN = false;  fIN = false;
  win = uint 0; urp = uint 0;
  mss = None; scale = None;
  ts = None; data = []
}

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_CLOSED false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint (id.test_host.test_ephm_port - 1)))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { sane_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint (id.test_host.test_ephm_port - 1)) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd last_dgram),
  "deliver_in_5: receive and drop (maybe with RST) a sane segment that doesn't match
any socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let deliver_in_5 = [test1]


(* ---------------------------------------------------------------------- *)
(* deliver_in_6 *)
(* ---------------------------------------------------------------------- *)

let sane_segment = {
  is1 = None; is2 = None;
  ps1 = None; ps2 = None;
  seq = uint 5000;
  ack = uint 100;
  uRG = false; aCK = true;
  pSH = false; rST = false;
  sYN = false;  fIN = false;
  win = uint 0; urp = uint 0;
  mss = None; scale = None;
  ts = None; data = []
}

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_CLOSED false in

    let bind_call = (tid_of_int_private 0, BIND(fd, Some (mk_ip id.test_host.test_ip_address),
	Some (mk_port id.aux_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_seg = ref false in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint (id.test_host.test_ephm_port)))
	  then
	    (Mutex.lock lock; seen_seg := true;
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { sane_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint (id.test_host.test_ephm_port)) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_seg = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd last_dgram),
  "deliver_in_6: receive and drop (silently) a sane segment that matches a CLOSED socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let deliver_in_6 = [test1]


(* ---------------------------------------------------------------------- *)
(* deliver_in_7 *)
(* ---------------------------------------------------------------------- *)

let test1 = (function (st, stdescr) ->
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
    rst_driven_socket ts id fd last_dgram;
    delay 5.00),
  "deliver_in_7: receive RST and zap a " ^stdescr^ " socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true))

let reqd_driven_states = [
  ST_ESTABLISHED(DATA_SENT_RCVD), "ESTABLISHED(data sent rcvd)";
  ST_CLOSE_WAIT(DATA_SENT_RCVD), "CLOSE_WAIT(data sent rcvd)";
  ST_LAST_ACK(DATA_SENT_RCVD), "LAST_ACK(data sent rcvd)";
  ST_FIN_WAIT_1(DATA_SENT_RCVD), "FIN_WAIT_1(data sent rcvd)";
  ST_CLOSING(DATA_SENT_RCVD), "CLOSING(data sent rcvd)";
  ST_FIN_WAIT_2(DATA_SENT_RCVD), "FIN_WAIT_2(data sent rcvd)";
]

let deliver_in_7 = List.map test1 reqd_driven_states

(* ---------------------------------------------------------------------- *)
(* deliver_in_7a *)
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

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in

	let lock, cond = Mutex.create (), Condition.create () in
    let seen_synack = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN,ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) && (datagram.aCK = true) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_synack := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = Some(uint id.test_host.test_ephm_port) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_synack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 1.00;
    rst_driven_socket ts id fd !last_dgram_seen;
	delay 5.00),
  "deliver_in_7a: receive RST and zap a SYN_RECEIVED socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let deliver_in_7a = [test1;]

(* ---------------------------------------------------------------------- *)
(* deliver_in_7b *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in
    rst_driven_socket ts id fd last_dgram;
    delay 5.00),
  "deliver_in_7b: receive RST and ignore it for a LISTENing socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let deliver_in_7b = [test1;]

(* ---------------------------------------------------------------------- *)
(* deliver_in_7c *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_TIME_WAIT(NO_DATA)) false in
    rst_driven_socket ts id fd last_dgram;
    delay 5.00),
  "deliver_in_7c: receive RST and ignore it for a ST_TIME_WAIT(NO_DATA) socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test2 =
  (function id -> function ts ->
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref NO_DATAGRAMS in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

	let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
	last_dgram_seen := last_dgram;
    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

    let dg = match !last_dgram_seen with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_7c test2: can't get here")) in
    let ackrst_segment = { dg with
		is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
		sYN = false; aCK = true; rST = true; fIN = false; uRG = false;
		ts = timestamp_update_swap dg.ts (uint 1);
		seq = uint 1000; ack = dg.seq -. (uint 500);	data = []; } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(ackrst_segment));
	delay 5.00),
  "deliver_in_7c: send ACK,RST segment with invalid ack to SYN_SENT socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let deliver_in_7c = [test1; test2;]

(* ---------------------------------------------------------------------- *)
(* deliver_in_7d *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref NO_DATAGRAMS in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

	let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
	last_dgram_seen := last_dgram;
    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

    let dg = match !last_dgram_seen with
      SENT_DATAGRAM(dg) -> dg
    | _ -> raise(Assertion_failed("deliver_in_7d test 1: can't get here")) in
    let ackrst_segment = { dg with
		is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
		sYN = false; aCK = true; rST = true; fIN = false; uRG = false;
		ts = timestamp_update_swap dg.ts (uint 1);
		seq = uint 1000; ack = dg.seq +. (uint 1); data = []; } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(ackrst_segment));
	delay 5.00),
  "deliver_in_7d: send ACK,RST segment with valid ack to SYN_SENT socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let deliver_in_7d = [test1;]

(* ---------------------------------------------------------------------- *)
(* deliver_in_8 *)
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

let test1 = (function (st,stdescr) ->
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    let ps = match last_dgram with
      SENT_DATAGRAM(dg) -> dg.ps1
    | RECV_DATAGRAM(dg) -> dg.ps2
    | _ -> raise(Assertion_failed("deliver_in_8: test1: expected a SENT/RECV_DATAGRAM here")) in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = ps)
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = ps } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00),
  "deliver_in_8: receive SYN in state" ^ stdescr,
  ((true, false), true, true, false),
  ((false, false), false, false, true))

let reqd_driven_states = [
  ST_ESTABLISHED(DATA_SENT_RCVD), "ESTABLISHED(data sent rcvd)";
  ST_CLOSE_WAIT(DATA_SENT_RCVD), "CLOSE_WAIT(data sent rcvd)";
  ST_LAST_ACK(DATA_SENT_RCVD), "LAST_ACK(data sent rcvd)";
  ST_FIN_WAIT_1(DATA_SENT_RCVD), "FIN_WAIT_1(data sent rcvd)";
  ST_CLOSING(DATA_SENT_RCVD), "CLOSING(data sent rcvd)";
  ST_FIN_WAIT_2(DATA_SENT_RCVD), "FIN_WAIT_2(data sent rcvd)";
]

let deliver_in_8 = List.map test1 reqd_driven_states

(* ---------------------------------------------------------------------- *)
(* deliver_in_9 *)
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

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_TIME_WAIT(DATA_SENT_RCVD)) false in
    let fd2, last_dgram2, _ = tcp_state_diagram_driver id ts ST_CLOSED false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram2 in

    let ps = match last_dgram with
      SENT_DATAGRAM(dg) -> dg.ps1
    | RECV_DATAGRAM(dg) -> dg.ps2
    | _ -> raise(Assertion_failed("deliver_in_9: test1: expected a SENT/RECV_DATAGRAM here")) in

    let bind_call = (tid_of_int_private 0, BIND(fd2, Some (mk_ip id.test_host.test_ip_address),
						Some (mk_port (Int64.to_int (the ps))))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd2, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = ps)
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = ps;
			seq = match last_dgram with
			  SENT_DATAGRAM(dg) -> dg.ack -. (uint 5)
			| RECV_DATAGRAM(dg) -> dg.seq -. (uint 5)
			| _ -> uint 0 (* should not get here *) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd2 !last_dgram_seen),
  "deliver_in_9: receive SYN in TIME_WAIT state, iss <= rcv_nxt and new socket in LISTEN state",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test2 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_TIME_WAIT(DATA_SENT_RCVD)) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    let ps = match last_dgram with
      SENT_DATAGRAM(dg) -> dg.ps1
    | RECV_DATAGRAM(dg) -> dg.ps2
    | _ -> raise(Assertion_failed("deliver_in_8: test1: expected a SENT/RECV_DATAGRAM here")) in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = ps)
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = ps;
			seq = match last_dgram with
			  SENT_DATAGRAM(dg) -> dg.ack -. (uint 5)
			| RECV_DATAGRAM(dg) -> dg.seq -. (uint 5)
			| _ -> uint 0 (* should not get here *) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd),
  "deliver_in_9: receive SYN in TIME_WAIT state, iss <= rcv_nxt and no matching LISTEN socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test3 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_TIME_WAIT(DATA_SENT_RCVD)) false in
    let fd2, last_dgram2, _ = tcp_state_diagram_driver id ts ST_CLOSED false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram2 in

    let ps = match last_dgram with
      SENT_DATAGRAM(dg) -> dg.ps1
    | RECV_DATAGRAM(dg) -> dg.ps2
    | _ -> raise(Assertion_failed("deliver_in_8: test1: expected a SENT/RECV_DATAGRAM here")) in

    let bind_call = (tid_of_int_private 0, BIND(fd2, Some (mk_ip id.test_host.test_ip_address),
						Some (mk_port (Int64.to_int (the ps))))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    let listen_call = (tid_of_int_private 0, LISTEN(fd2, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = ps)
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = ps;
			seq = match last_dgram with
			  SENT_DATAGRAM(dg) -> dg.ack +. (uint 5000)
			| RECV_DATAGRAM(dg) -> dg.seq +. (uint 5000)
			| _ -> uint 0 (* should not get here *) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd2 !last_dgram_seen),
  "deliver_in_9: receive SYN in TIME_WAIT state, valid iss and a matching LISTENing socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test4 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_TIME_WAIT(DATA_SENT_RCVD)) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn = ref false in
    let last_dgram_seen = ref last_dgram in

    let ps = match last_dgram with
      SENT_DATAGRAM(dg) -> dg.ps1
    | RECV_DATAGRAM(dg) -> dg.ps2
    | _ -> raise(Assertion_failed("deliver_in_8: test1: expected a SENT/RECV_DATAGRAM here")) in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) &&
	    (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = ps)
	  then
	    (Mutex.lock lock; seen_syn := true;
	     last_dgram_seen := RECV_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let syn_segment = { syn_segment with
			is1 = Some(hol_ip id.virtual_host_ip);
			is2 = Some(hol_ip id.test_host.test_ip_address);
			ps1 = Some(uint id.virtual_host_port);
			ps2 = ps;
			seq = match last_dgram with
			  SENT_DATAGRAM(dg) -> dg.ack +. (uint 5000)
			| RECV_DATAGRAM(dg) -> dg.seq +. (uint 5000)
			| _ -> uint 0 (* should not get here *) } in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(syn_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_syn = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd),
  "deliver_in_9: receive SYN in TIME_WAIT state, valid iss and no matching LISTEN socket",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let deliver_in_9 = [test1; test2; test3; test4;]

(* ---------------------------------------------------------------------- *)

let tcp_tests =
  [deliver_in_1, "deliver_in_1";
   deliver_in_1b, "deliver_in_1b";
   deliver_in_2, "deliver_in_2";
   deliver_in_2a, "deliver_in_2a";
   deliver_in_4, "deliver_in_4";
   deliver_in_5, "deliver_in_5";
   deliver_in_6, "deliver_in_6";
   deliver_in_7, "deliver_in_7";
   deliver_in_7a, "deliver_in_7a";
   deliver_in_7b, "deliver_in_7b";
   deliver_in_7c, "deliver_in_7c";
   deliver_in_7d, "deliver_in_7d";
   deliver_in_8, "deliver_in_8";
   deliver_in_9, "deliver_in_9";]

let udp_tests = []

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let do_deliver_in_tests handle hosts_list test_type =
  let tests = match test_type with
    TCP_NORMAL -> tcp_tests
  | UDP_NORMAL -> udp_tests
  | ALL_NORMAL -> normal_tests
  | TCP_EXHAUSTIVE -> tcp_exhaustive_tests
  | UDP_EXHAUSTIVE -> udp_exhaustive_tests
  | ALL_EXHAUSTIVE -> exhaustive_tests
  | STREAM_NORMAL -> []
  | STREAM_EXHAUSTIVE -> [] in

  let done_a_test = ref false in
  let num_of_tests = ref 0 in
  List.iter
    (function (next_test_set, test_set_descr) ->
      begin_next_test_group handle test_set_descr;
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
	    next_test_set)
	hosts_list)
    tests;
  !done_a_test

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
