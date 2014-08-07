(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: timers                              *)
(* Steve Bishop - Created 20030801                                        *)
(* $Id: timers.ml,v 1.15 2006/06/07 11:52:45 amgb2 Exp $ *)
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
open Testscommon
(* ---------------------------------------------------------------------- *)
(* timer_tt_rexmtsyn_1 / timer_tt_conn_est_1 *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_SENT false in
    inter_test_delay 800.0;  (* needs to be larger than 777 seconds, I think! *)
    rst_driven_socket ts id fd last_dgram),
  "timer_tt_rexmtsyn_1/timer_tt_conn_est_1: for a fresh blocking socket, transmit a SYN segment and allow the syn retransmit timer to expire",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let timer_tt_rexmtsyn = [test1]

(* ---------------------------------------------------------------------- *)
(* timer_tt_rexmt_1 *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in
    let send_call = (tid_of_int_private 0, SEND(fd, None, "Testdata", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);
    inter_test_delay 2000.0;  (* Just being careful *)
    rst_driven_socket ts id fd last_dgram),
  "timer_tt_rexmt_1: for a fresh blocking socket, transmit a segment in the ESTABLISHED state and allow the retransmit timer to expire (psyche does not ACK the segments)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test2 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, false, true)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
    inter_test_delay 700.0;  (* Just being careful *)
    rst_driven_socket ts id fd last_dgram),
  "timer_tt_rexmt_1: for a fresh blocking socket, transmit a FIN segment in the ESTABLISHED state and allow the retransmit timer to expire whilst in state FIN_WAIT_1",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test3 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_CLOSE_WAIT(DATA_SENT_RCVD)) false in
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) close_call);
    inter_test_delay 700.0;  (* Just being careful *)
    rst_driven_socket ts id fd last_dgram),
  "timer_tt_rexmt_1: for a fresh blocking socket, send a FIN segment in teh CLOSE_WAIT state and allowthe retransmit timer to expire whilst in the LAST_ACK state",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

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

let test4 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_LISTEN false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_syn_ack = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.sYN = true) && (datagram.aCK = true) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_syn_ack := true;
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
    while !seen_syn_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    inter_test_delay 500.0;
    rst_driven_socket ts id fd !last_dgram_seen),
  "timer_tt_rexmt_1: for a fresh blocking socket, transmit a SYN,ACK segment whilst in the LISTEN state and allow the retransmit timer to expire in state SYN_RCVD (simultaneous open)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let timer_tt_rexmt = [test1; test2; test3; test4]


(* ---------------------------------------------------------------------- *)
(* timer_tt_persist_1 *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_persist_ack = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required SYN packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    ((List.length datagram.data) > 1)
	  then
	    (last_dgram_seen := SENT_DATAGRAM(datagram);
	     let ack_seg = { datagram with
			     is1 = datagram.is2; is2 = datagram.is1;
			     ps1 = datagram.ps2; ps2 = datagram.ps1;
			     aCK = true; pSH = true; uRG = false;
			     seq = datagram.ack;
			     ack = datagram.seq +. uint (List.length datagram.data);
			     ts = timestamp_update_swap datagram.ts (uint 1);
			     win = uint 0; urp = uint 0; data = []; } in
	     injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_seg));
	    )
	  else if (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port)) &&
	    ((List.length datagram.data) <= 1)
	  then
	    (Mutex.lock lock; seen_persist_ack := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     let ack_seg = { datagram with
			     is1 = datagram.is2; is2 = datagram.is1;
			     ps1 = datagram.ps2; ps2 = datagram.ps1;
			     aCK = true; pSH = true; uRG = false;
			     seq = datagram.ack; ack = datagram.seq;
			     ts = timestamp_update_swap datagram.ts (uint 1);
			     win = uint 0; urp = uint 0; data = []; } in
	     injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_seg));
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let send_call = (tid_of_int_private 0,
		     SEND(fd, None, "TestTest!!TestTest!!TestTest!!TestTest!!TestTest!!", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);

    (* We want to send some more, so persist kicks into action !! *)
    let send_call = (tid_of_int_private 0,
		     SEND(fd, None, "123...123...123...123...", [])) in
    ignore(libd_call (the ts.th_libd_hnd) send_call);

    (* Block on condition variable here until we verify that some *)
    (* persist acks have been seen *)
    Mutex.lock lock;
    while !seen_persist_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    inter_test_delay 500.0;  (* Just being careful *)
    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    rst_driven_socket ts id fd last_dgram),
  "timer_tt_persist_1: for a fresh established socket, psyche advertises a receiver's window of 0 and does not send updates. Wait until the test host transmit some packets due to the persist timer expiring.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let timer_tt_persist = [test1]

(* ---------------------------------------------------------------------- *)
(* timer_tt_keep_1 *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts
	(ST_ESTABLISHED(DATA_SENT_RCVD)) false in
    let keepalive_call = (tid_of_int_private 0,
			  SETSOCKBOPT(fd, SO_KEEPALIVE, true)) in
    ignore(libd_call (the ts.th_libd_hnd) keepalive_call);

    inter_test_delay 8050.0;  (* Just being careful *)
    rst_driven_socket ts id fd last_dgram),
  "timer_tt_keep_1: for a fresh established socket, set SO_KEEPALIVE and don't send data for 2 hours. The keepalive timer eventually expires. Then wait for the 10x75second timeouts to occur (as the remote host psyche still fails to respond)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let timer_tt_keep = [test1]


(* ---------------------------------------------------------------------- *)
(* timer_tt_2msl_1 *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_TIME_WAIT(DATA_SENT_RCVD)) false in
    inter_test_delay 500.0;  (* Just being careful *)
    rst_driven_socket ts id fd last_dgram),
  "timer_tt_2msl_1: for a socket in the TIME_WAIT state, wait for the 2msl timer to expire",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let timer_tt_2msl = [test1]


(* ---------------------------------------------------------------------- *)
(* timer_tt_delack_1 *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_ack = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_ack := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let data_segment =
      match last_dgram with
	SENT_DATAGRAM(dg) ->
	  {dg  with
	   is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   aCK = true; sYN = false; pSH = true; uRG = false; fIN = false;
	   seq = dg.ack; ack = dg.seq +. uint(List.length dg.data);
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = [uint(Char.code 'b'); uint(Char.code 'a');  uint(Char.code 'r');]}
      |	_ -> raise(Assertion_failed("timer_tt_delack_1: should not get here")) in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(data_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.0;
    rst_driven_socket ts id fd !last_dgram_seen),
  "timer_tt_delack_1:  for a socket in the established state, receive some data but don't attempt to send any. Wait for timer to expire and emit the delayed ack",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test2 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(NO_DATA)) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_ack = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) &&
	    (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    (Mutex.lock lock; seen_ack := true;
	     last_dgram_seen := SENT_DATAGRAM(datagram);
	     Condition.signal cond; Mutex.unlock lock)
	  else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let data_segment =
      match last_dgram with
	SENT_DATAGRAM(dg) ->
	  {dg  with
	   is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	   aCK = true; sYN = false; pSH = true; uRG = false; fIN = false;
	   seq = dg.ack; ack = dg.seq +. uint(List.length dg.data);
	   ts = timestamp_update_swap dg.ts (uint 1);
	   data = [uint(Char.code 'b'); uint(Char.code 'a');  uint(Char.code 'r');]}
      |	_ -> raise(Assertion_failed("timer_tt_delack_1: should not get here")) in

    let send_call = (tid_of_int_private 0, SEND(fd, None, "Testdata", [])) in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(data_segment));
    ignore(libd_call (the ts.th_libd_hnd) send_call);

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.0;
    rst_driven_socket ts id fd !last_dgram_seen),
  "timer_tt_delack_1:  for a socket in the established state, receive some data but do a send before the delack timer expires",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let timer_tt_delack = [test1; test2]


(* ---------------------------------------------------------------------- *)
(* timer_tt_fin_wait_2_1 *)
(* ---------------------------------------------------------------------- *)

let test1 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_FIN_WAIT_2(DATA_SENT_RCVD)) false in
    inter_test_delay 1000.0;  (* Just being careful *)
    rst_driven_socket ts id fd last_dgram),
  "timer_tt_fin_wait_2_1: for a socket in state FIN_WAIT_2, receive no datagrams to allow the fin_wait_2 timer to fire",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let test2 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_FIN_WAIT_2(DATA_SENT_RCVD)) false in
    inter_test_delay 30.0;  (* Just being careful *)

    let data_segment =
      match last_dgram with
	RECV_DATAGRAM(dg) ->
	  {dg  with
	   aCK = true; sYN = false; pSH = true; uRG = false; fIN = false; ts = timestamp_update dg.ts (uint 1);
	   data = [uint(Char.code 'b'); uint(Char.code 'a');  uint(Char.code 'r');]}
      |	_ -> raise(Assertion_failed("timer_tt_delack_1: should not get here")) in
    injector_inject (the ts.th_injector_hnd) (TCPMSG(data_segment));

    inter_test_delay 1500.0;  (* Just being careful *)
    rst_driven_socket ts id fd last_dgram),
  "timer_tt_fin_wait_2_1: for a socket in state FIN_WAIT_2, receive some datagrams to reset the fin_wait_2 timer, then eventually send no datagrams to the socket to allow the timer to fire",
  ((true, false), true, true, false),
  ((false, false), false, false, true)

let timer_tt_fin_wait_2_1 = [test1; test2]

(* ---------------------------------------------------------------------- *)

let tcp_tests =
  [timer_tt_rexmtsyn, "timer_tt_rexmtsyn";
   timer_tt_rexmt, "timer_tt_rexmt";
   timer_tt_persist, "timer_tt_persist";
(* timer_tt_keep, "timer_tt_keep"; MOVED TO END *)
   timer_tt_2msl, "timer_tt_2msl";
   timer_tt_delack, "timer_tt_delack";
   timer_tt_fin_wait_2_1, "timer_tt_fin_wait_2";
   timer_tt_keep, "timer_tt_keep"
 ]

let udp_tests = []

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

(* ---------------------------------------------------------------------- *)

let do_timer_tests handle hosts_list test_type =

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
    (function (test_set, test_set_name) ->
      begin_next_test_group handle test_set_name;
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
	    test_set
	)
	hosts_list
    ) tests;
  !done_a_test

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
