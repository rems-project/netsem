(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: deliver_in_3                        *)
(* Steve Bishop - Created 20030919                                        *)
(* $Id: deliver_in_3.ml,v 1.26 2006/06/07 11:52:45 amgb2 Exp $ *)
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

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=--=-=-=-=-=-=- *)
(* Important:
   - the ackstuff tests assume that the TCP NewReno extensions are turned
     on.  This is the default behaviour in most modern TCP stacks.  All
     ackstuff tests should always be performed a second time with NewReno
     disabled if possible (this may not be possible on some platforms,
     e.g. Linux, WinXP). To be investigated....

   - SB TODO: think about testing ackstuff and datastuff from all
     >=ESTABLISHED states  *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=--=-=-=-=-=-=- *)

let post_established_driven_states = [
  ST_ESTABLISHED(DATA_SENT_RCVD), "ESTABLISHED(data sent rcvd)";
  ST_CLOSE_WAIT(DATA_SENT_RCVD), "CLOSE_WAIT(data sent rcvd)";
  ST_LAST_ACK(DATA_SENT_RCVD), "LAST_ACK(data sent rcvd)";
  ST_FIN_WAIT_1(DATA_SENT_RCVD), "FIN_WAIT_1(data sent rcvd)";
  ST_CLOSING(DATA_SENT_RCVD), "CLOSING(data sent rcvd)";
  ST_FIN_WAIT_2(DATA_SENT_RCVD), "FIN_WAIT_2(data sent rcvd)";
  ST_TIME_WAIT(DATA_SENT_RCVD), "TIME_WAIT(data sent rcvd)";
]

let established_close_wait_states = [
  ST_ESTABLISHED(DATA_SENT_RCVD), "ESTABLISHED(data sent rcvd)";
  ST_CLOSE_WAIT(DATA_SENT_RCVD), "CLOSE_WAIT(data sent rcvd)";
]

let established_fin_wait_states = [
  ST_ESTABLISHED(DATA_SENT_RCVD), "ESTABLISHED(data sent rcvd)";
  ST_FIN_WAIT_1(DATA_SENT_RCVD), "FIN_WAIT_1(data sent rcvd)";
  ST_FIN_WAIT_2(DATA_SENT_RCVD), "FIN_WAIT_2(data sent rcvd)";
]

(* ---------------------------------------------------------------------- *)
(* topstuff: dropping a segment *)
(* ---------------------------------------------------------------------- *)

type ackval = LT_UNA | EQ_UNA | GT_MAX | STD

let test1_template =
  (function ackval -> function invalid_seq ->
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts ST_SYN_RCVD false in

    let last_dgram_seen = ref last_dgram in

    let ack_segment =
      match !last_dgram_seen with
	SENT_DATAGRAM(dg) ->
	  { dg with
	    is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	    ack = dg.seq +. (uint 1) -.
	      (match ackval with
		LT_UNA -> uint 2
	      |	EQ_UNA -> uint 1
	      |	GT_MAX -> uint (-5)
	      |	_ -> uint 0);
	    seq = dg.ack -. if invalid_seq then (uint 5) else (uint 0);
	    sYN = false; aCK = true; rST = false; fIN = false;
	    ts = timestamp_update_swap dg.ts (uint 1);
	    uRG = false; urp = uint 0; data = [] }
      | _ -> raise(Assertion_failed("deliver_in_3: test1: expected a SENT_DATAGRAM here")) in

    injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_segment));

    delay 5.00;
    rst_driven_socket ts id fd (RECV_DATAGRAM(ack_segment))),
    (let ack_str = match ackval with
		LT_UNA -> "ack<snd_una"
	      |	EQ_UNA -> "ack==snd_una"
	      |	GT_MAX -> "ack>snd_max"
	      |	_ -> "ack > snd_una (normal case)" in
    let seq_str = if invalid_seq then ", seq < irs" else "" in
    "deliver_in_3: in state SYN_RECEIVED, receive an ACK packet with " ^ ack_str ^ seq_str ^ ", should dropwithreset"),
  ((true, false), true, true, false),
  ((false, false), false, false, true))


let test2_template =
  (function (st, ststr) ->
    (function id -> function ts ->
      let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in

      let ack_segment =
	match last_dgram with
	  SENT_DATAGRAM(dg) ->
	    { dg with
	      is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	      ack = dg.seq +. (uint (List.length dg.data)); seq = dg.ack;
	      sYN = false; aCK = true; rST = false; fIN = false;
	      ts = timestamp_update_swap dg.ts (uint 1);
	      uRG = false; urp = uint 0; data = [uint(Char.code 'b'); uint(Char.code 'a'); uint(Char.code 'r');] }
	| RECV_DATAGRAM(dg) ->
	    { dg with data = [uint(Char.code 'b'); uint(Char.code 'a'); uint(Char.code 'r');]; }
	| _ -> raise(Assertion_failed("deliver_in_3: test2: expected a }SENT,RECV}_DATAGRAM here")) in

      injector_inject (the ts.th_injector_hnd) (TCPMSG(ack_segment));

      delay 5.00;
      rst_driven_socket ts id fd (RECV_DATAGRAM({ack_segment with seq = ack_segment.seq +. (uint 3)}));
      rst_driven_socket ts id fd (RECV_DATAGRAM({ack_segment with seq = ack_segment.seq +. (uint 3);
						                  ack = ack_segment.ack +. (uint 1)}))

),
    "deliver_in_3: in state " ^ ststr ^ ", once the process has gone away receive an ACK segment with data past rcv_nxt",
  ((true, false), true, true, false),
  ((false, false), false, false, true))


let test3 =
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
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
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
      match !last_dgram_seen with
	SENT_DATAGRAM(dg) ->
	  { dg with
	    is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	    ack = dg.seq +. (uint (List.length dg.data)); seq = dg.ack +. dg.win +. (uint 10);
	    sYN = false; aCK = true; rST = false; fIN = false;
	    ts = timestamp_update_swap dg.ts (uint 1);
	    uRG = false; urp = uint 0; data = [uint(Char.code 'b'); uint(Char.code 'a'); uint(Char.code 'r');] }
      | _ -> raise(Assertion_failed("deliver_in_3: test2: expected a SENT_DATAGRAM here")) in

    injector_inject (the ts.th_injector_hnd) (TCPMSG(data_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_3: in state ESTABLISHED, data past RHS of window (dropafterack)",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test4 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(DATA_RCVD)) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_ack = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
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
      match !last_dgram_seen with
	SENT_DATAGRAM(dg) ->
	  { dg with
	    is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	    ack = dg.seq +. (uint (List.length dg.data)); seq = dg.ack -. (uint 3);
	    sYN = false; aCK = true; rST = false; fIN = false;
	    ts = timestamp_update_swap dg.ts (uint 1);
	    uRG = false; urp = uint 0; data = [uint(Char.code 'b'); uint(Char.code 'a');] }
      | _ -> raise(Assertion_failed("deliver_in_3: test2: expected a SENT_DATAGRAM here")) in

    injector_inject (the ts.th_injector_hnd) (TCPMSG(data_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_3: in state ESTABLISHED(DATA_RCVD), whole segment lies within acknowledged region of rcv_q",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let test5 =
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(DATA_RCVD)) false in

    let lock, cond = Mutex.create (), Condition.create () in
    let seen_window_probe = ref false in
    let seen_zero_window = ref false in
    let last_dgram_seen = ref last_dgram in

    (* A slurper callback function that signals a condition when the *)
    (* required ACK packet is actually seen on the wire *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(datagram) ->
	  if (datagram.aCK = true) &&
	    (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (datagram.ps2 = Some(uint id.virtual_host_port))
	  then
	    let dg = datagram in
	    if datagram.win <> uint 0 then
	      (* If window still open, continue sending more data *)
	      let data_segment =
		{ dg with
		  is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
		  ack = dg.seq +. (uint (List.length(dg.data))); seq = dg.ack;
		  sYN = false; aCK = true; rST = false; fIN = false;
		  ts = timestamp_update_swap dg.ts (uint 1);
		  win = (try tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1 with
		    Not_found -> dg.win);
		  uRG = false; urp = uint 0; data = data_500_bytes } in
	      injector_inject (the ts.th_injector_hnd) (TCPMSG(data_segment));
	    else if !seen_zero_window = false then
	      (* If window is closed, send a window probe *)
	      (let data_segment =
		{ dg with
		  is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
		  ack = dg.seq +. (uint (List.length(dg.data))); seq = dg.ack;
		  sYN = false; aCK = true; rST = false; fIN = false;
		  ts = timestamp_update_swap dg.ts (uint 1);
		  uRG = false; urp = uint 0; data = [uint(Char.code 'b');] } in
	      injector_inject (the ts.th_injector_hnd) (TCPMSG(data_segment));
	      seen_zero_window := true;
	      last_dgram_seen := RECV_DATAGRAM(datagram))
	    else if !seen_zero_window = true then
	      (Mutex.lock lock; seen_window_probe := true;
	      Condition.signal cond; Mutex.unlock lock)
	    else ()
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in
    let data_segment =
      match !last_dgram_seen with
	SENT_DATAGRAM(dg) ->
	  { dg with
	    is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	    ack = dg.seq +. (uint 1); seq = dg.ack;
	    sYN = false; aCK = true; rST = false; fIN = false;
	    ts = timestamp_update_swap dg.ts (uint 1);
	    win = (try tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1 with
		    Not_found -> dg.win);
	    uRG = false; urp = uint 0; data = data_500_bytes }
      | _ -> raise(Assertion_failed("deliver_in_3: test2: expected a SENT_DATAGRAM here")) in

    injector_inject (the ts.th_injector_hnd) (TCPMSG(data_segment));

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_window_probe = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 5.00;
    rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_3: in state ESTABLISHED(DATA_RCVD) keep sending until the receivers buffer is full and a zero window is advertised. Then send a window probe and await a reply",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


let topstuff = [test1_template LT_UNA false; test1_template EQ_UNA false;
	        test1_template GT_MAX false; test1_template STD true;
		test1_template STD false;
		test2_template (ST_FIN_WAIT_1(DATA_SENT_RCVD), "FIN_WAIT_1(DATA_SENT_RCVD)");
		test2_template (ST_CLOSING(DATA_SENT_RCVD), "CLOSING(DATA_SENT_RCVD)");
		test2_template (ST_LAST_ACK(DATA_SENT_RCVD), "LAST_ACK(DATA_SENT_RCVD)");
		test2_template (ST_FIN_WAIT_2(DATA_SENT_RCVD), "FIN_WAIT_2(DATA_SENT_RCVD)");
		test2_template (ST_TIME_WAIT(DATA_SENT_RCVD), "TIME_WAIT(DATA_SENT_RCVD)");
	        test3; test4; test5;
	      ]


(* ---------------------------------------------------------------------- *)
(* ackstuff: dealing with flow control *)
(* ---------------------------------------------------------------------- *)


let test1 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let last_dgram_seen = ref last_dgram in

  let lock, cond = Mutex.create (), Condition.create () in
  let transmitted_dupacks = ref false in


  (* Store what we believe is snd_una before testing commences *)
  let snd_una = match !last_dgram_seen with
    SENT_DATAGRAM(dg) -> dg.seq +. (uint (List.length dg.data)) +.
	(if dg.sYN then uint 1 else uint 0) +.
	(if dg.fIN then uint 1 else uint 0)
  | RECV_DATAGRAM(dg) -> dg.ack
  | NO_DATAGRAMS -> raise(Assertion_failed("deliver_in_3.test1")) in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
  let slurper_callback_fun holmsg =
    Mutex.lock lock;
    if !transmitted_dupacks then (Mutex.unlock lock; ())
    else (Mutex.unlock lock;
	  match holmsg with
	    TCPMSG(dg) ->
	      if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
		(dg.ps2 = Some(uint id.virtual_host_port)) &&
		(List.length dg.data > 0)
	      then
		let dg = {dg with is1=dg.is2; is2=dg.is1; ps1=dg.ps2; ps2=dg.ps1;
			  seq=dg.ack; ack=snd_una; sYN=false; aCK=true; rST=false;
			  fIN=false; pSH=true; ts = timestamp_update_swap dg.ts (uint 1);
			  win=tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1; (*snd_wnd*)
			  data=[]} in
		injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
		injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
		injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
		injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

		Mutex.lock lock;
		transmitted_dupacks := true;
		Condition.signal cond;
		Mutex.unlock lock
	      else ()
	  | _ -> ())
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'A', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'B', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'C', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'D', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  (* Unregister the callback *)
  (* Block on condition variable here until we verify that the SYN packet has been seen *)
  Mutex.lock lock;
  while !transmitted_dupacks = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  delay 5.0;
  rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_3: in state " ^ stdescr ^ ", the test host transmit 4 segments to the virtual aux host. The first of these is deliberately 'lost', thus duplicate acknowledgments are normally generated. The duplicate acks should eventually force a fast retransmit or a NewReno-style retransmit and fiddle with ssthresh, cwnd and perhaps snd_nxt. This test behaves differently when TCP NewReno is enabled and depending on the initial TCP state of the test host.",
  ((true, false), true, true, false),
  ((false, false), false, false, true))


type test2_change = DATA | WIN

let test2 = (function test2_change ->
  (function (st,stdescr) ->
  (function id -> function ts ->
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in

    let last_dgram_seen = ref last_dgram in
    let lock, cond = Mutex.create (), Condition.create () in
    let seen_ack = ref false in

    (* Store what we believe is snd_una before testing commences *)
    let snd_una = match !last_dgram_seen with
      SENT_DATAGRAM(dg) -> dg.seq +. (uint (List.length dg.data)) +.
	  (if dg.sYN then uint 1 else uint 0) +.
	  (if dg.fIN then uint 1 else uint 0)
    | RECV_DATAGRAM(dg) -> dg.ack
    | NO_DATAGRAMS -> raise(Assertion_failed("deliver_in_3.test2")) in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
    let slurper_callback_fun holmsg =
      match holmsg with
	TCPMSG(dg) ->
	  if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (dg.ps2 = Some(uint id.virtual_host_port)) &&
	    (List.length dg.data > 0)
	  then
	    (let dg = {dg with is1=dg.is2; is2=dg.is1; ps1=dg.ps2; ps2=dg.ps1;
		       seq=dg.ack; ack=snd_una; sYN=false; aCK=true; rST=false;
		       fIN=false; pSH=true; ts = timestamp_update_swap dg.ts (uint 1);
		       win=(match test2_change with
			 DATA ->
			   tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1
		       | WIN ->
			   let newwin = (tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1) -. (uint 350)
			   in let _ = tcpcb_update_win ts dg.is2 dg.is1 dg.ps2 dg.ps1 newwin in
			   newwin);
		       data=(match test2_change with DATA -> data_n_bytes 100 | WIN -> []);
		     } in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
	    last_dgram_seen := SENT_DATAGRAM(dg))
	  else if (dg.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	    (dg.ps1 = Some(uint id.virtual_host_port)) &&
	    ((List.length dg.data > 0) || dg.win = (tcpcb_get_win ts dg.is1 dg.is2 dg.ps1 dg.ps2))
	  then
	    (Mutex.lock lock;
	     seen_ack := true;
	     last_dgram_seen := RECV_DATAGRAM(dg);
	     Condition.signal cond; Mutex.unlock lock)
      | _ -> ()
    in
    let slurper_callback_hnd = slurper_register_callback
	(the ts.th_slurper_hnd) slurper_callback_fun in

    let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 350 'A', [])) in
    ignore(libd_call (the ts.th_libd_hnd) snd_call);

    (* Block on condition variable here until we verify that the SYN packet has been seen *)
    Mutex.lock lock;
    while !seen_ack = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

    (* Unregister the callback *)
    slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
    delay 1.00;
    rst_driven_socket ts id fd NO_DATAGRAMS),
  "deliver_in_3: in state " ^ stdescr ^ ", the test host transmits a segment and the virtual host psyche sends a segment " ^ (match test2_change with DATA -> "(with data)" | _ -> "(with a window update)") ^ " containing a duplicate ack. This ack should not be treated as a duplicate ack by the test host",
  ((true, false), true, true, false),
  ((false, false), false, false, true)))


let test3 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let last_dgram_seen = ref last_dgram in
  let pkt_count = ref 0 in

  let lock, cond = Mutex.create (), Condition.create () in
  let transmitted_dupacks = ref false in

  (* Store what we believe is snd_una before testing commences *)
  let snd_una = match !last_dgram_seen with
    SENT_DATAGRAM(dg) -> dg.seq +. (uint (List.length dg.data)) +.
	(if dg.sYN then uint 1 else uint 0) +.
	(if dg.fIN then uint 1 else uint 0)
  | RECV_DATAGRAM(dg) -> dg.ack
  | NO_DATAGRAMS -> raise(Assertion_failed("deliver_in_3.test1")) in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
  let slurper_callback_fun holmsg =
    Mutex.lock lock;
    if !transmitted_dupacks then (Mutex.unlock lock; ())
    else (Mutex.unlock lock;
	  match holmsg with
	    TCPMSG(dg) ->
	      if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
		(dg.ps2 = Some(uint id.virtual_host_port)) &&
		(List.length dg.data > 0)
	      then
		(last_dgram_seen := SENT_DATAGRAM(dg);
		let dg = {dg with is1=dg.is2; is2=dg.is1; ps1=dg.ps2; ps2=dg.ps1;
			  seq=dg.ack; ack=snd_una; sYN=false; aCK=true; rST=false;
			  fIN=false; pSH=true; ts = timestamp_update_swap dg.ts (uint 1);
			  win=tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1; (*snd_wnd*)
			  data=[]} in
		injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
		injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
		let dg = {dg with data = data_n_bytes 50;} in
		injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
		injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

		Mutex.lock lock;
		transmitted_dupacks := true;
		Condition.signal cond;
		Mutex.unlock lock)
	      else ()
	  | _ -> ())
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'A', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'B', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'C', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'D', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

   (* Block on condition variable here until we are signalled that testing has completed *)
    Mutex.lock lock;
    while !transmitted_dupacks = false do
      Condition.wait cond lock;
    done;
    Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
  delay 2.00;
  rst_driven_socket ts id fd NO_DATAGRAMS;
  delay 5.00),
  "deliver_in_3: in state " ^ stdescr ^ ", the test host transmits 4 segments to the virtual aux host. The first of these is deliberately 'lost', thus duplicate acknowledgments are generated. After several duplicate acks the virtual host transmits a segment (with data) containing a duplicate ack value. (SB: If our spec is correct then this resets the dupack counter?)",
  ((true, false), true, true, false),
  ((false, false), false, false, true))


let test4 = (function (st, stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let last_dgram_seen = ref last_dgram in
  let pkt_count = ref 0 in

  let lock, cond = Mutex.create (), Condition.create () in
  let finished = ref false in

  (* Store what we believe is snd_una before testing commences *)
  let snd_una = match !last_dgram_seen with
    SENT_DATAGRAM(dg) -> dg.seq +. (uint (List.length dg.data)) +.
	(if dg.sYN then uint 1 else uint 0) +.
	(if dg.fIN then uint 1 else uint 0)
  | RECV_DATAGRAM(dg) -> dg.ack
  | NO_DATAGRAMS -> raise(Assertion_failed("deliver_in_3.test1")) in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(dg) ->
	if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (dg.ps2 = Some(uint id.virtual_host_port)) &&
	  (List.length dg.data > 0)
	then
	  (pkt_count := !pkt_count + 1;
	   if !pkt_count = 2 then
	     let dg1 = {dg with is1=dg.is2; is2=dg.is1; ps1=dg.ps2; ps2=dg.ps1;
			seq=dg.ack; ack=snd_una; sYN=false; aCK=true; rST=false;
			fIN=false; pSH=true; ts = timestamp_update_swap dg.ts (uint 1);
			win=tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1; (*snd_wnd*)
			data=[]} in
	     injector_inject (the ts.th_injector_hnd) (TCPMSG(dg1))
	   else if !pkt_count = 3 then
	     (let dg2 = {dg with is1=dg.is2; is2=dg.is1; ps1=dg.ps2; ps2=dg.ps1;
			seq=dg.ack; sYN=false; aCK=true; rST=false;
			fIN=false; pSH=true; ts = timestamp_update_swap dg.ts (uint 1);
			win=tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1; (*snd_wnd*)
			data=[]; ack = dg.seq +.(uint (List.length dg.data)) +.
			  (if dg.sYN then uint 1 else uint 0) +.
			  (if dg.fIN then uint 1 else uint 0)} in
	     injector_inject (the ts.th_injector_hnd) (TCPMSG(dg2));
	     Mutex.lock lock; finished := true; Condition.signal cond;
	     Mutex.unlock lock));
	last_dgram_seen := SENT_DATAGRAM(dg)
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'A', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'B', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'C', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  (* Block on condition variable here until we are signalled that testing has completed *)
  Mutex.lock lock;
  while !finished = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
  delay 2.00;
  rst_driven_socket ts id fd !last_dgram_seen;
  delay 5.00;),
  "deliver_in_3: in state " ^ stdescr ^ ", the test host transmits 3 segments to the virtual host. The first of these is deliberately 'delayed', thus a duplicate acknowledgment is generated for the second. When the third segment arrives, the first segment also arrives thus the whole datastream is acknowledged (and dupacks should be reset to zero)",
  ((true, false), true, true, false),
  ((false, false), false, false, true))


let test5 = (function mode ->
 (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let last_dgram_seen = ref last_dgram in
  let pkt_count = ref 0 in

  let lock, cond = Mutex.create (), Condition.create () in
  let finished = ref false in

  (* Store what we believe is snd_una before testing commences *)
  let snd_una = match !last_dgram_seen with
    SENT_DATAGRAM(dg) -> dg.seq +. (uint (List.length dg.data)) +.
	(if dg.sYN then uint 1 else uint 0) +.
	(if dg.fIN then uint 1 else uint 0)
  | RECV_DATAGRAM(dg) -> dg.ack
  | NO_DATAGRAMS -> raise(Assertion_failed("deliver_in_3.test1")) in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(dg) ->
	if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (dg.ps2 = Some(uint id.virtual_host_port)) &&
	  (List.length dg.data > 0)
	then
	  (pkt_count := !pkt_count + 1;
	   if !pkt_count =  1 then
	     (let dg = {dg with is1 = dg.is2; is2 = dg.is1;
			ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
			sYN = false; fIN = false; data = [];
			ts = timestamp_update_swap dg.ts (uint 1);
			seq = dg.ack; ack = snd_una} in
	     injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
	     injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
	     injector_inject (the ts.th_injector_hnd) (TCPMSG(dg)))
	   else if !pkt_count = 5 then
	     (let dg = {dg with is1 = dg.is2; is2 = dg.is1;
		       ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
		       sYN = false; fIN = false; data = [];
			ts = timestamp_update_swap dg.ts (uint 1);
		       seq = dg.ack;
		       ack = if not mode then dg.seq else dg.seq +.
			 (uint (List.length dg.data)) +.(if dg.sYN then uint 1 else uint 0) +.
			 (if dg.fIN then uint 1 else uint 0) } in
	     injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
	     injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
	     Mutex.lock lock; finished := true; Condition.signal cond;
	     Mutex.unlock lock)
	  );
	last_dgram_seen := SENT_DATAGRAM(dg)
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'A', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'B', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'C', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'D', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'E', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  (* Block on condition variable here until we are signalled that testing has completed *)
  Mutex.lock lock;
  while !finished = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
  rst_driven_socket ts id fd NO_DATAGRAMS;
  delay 10.00),
  "deliver_in_3: in state " ^ stdescr ^ ", the test host transmits 5 segments to the virtual host. The first of these is deliberately 'delayed' and duplicate acks are produced for the 2nd, 3rd and 4th segments." ^
  (if not mode then " The first segment eventually arrives (perhaps because of a retransmit) and a partial ack is generated. The 5th segment upon arrival also generates a duplicate ack (this is probably not possible in reality; although it would be interesting to see how the test hosts cope)"
  else "The first segment eventually arrives (perhaps because of a retransmit) and a partial ack is generated. The 5th segment upon arrival is acked and a complete recovery has occured."),
  ((true, false), true, true, false),
  ((false, false), false, false, true)))


let test6 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let last_dgram_seen = ref last_dgram in
  let lock, cond = Mutex.create (), Condition.create () in
  let finished = ref false in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(dg) ->
	if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (dg.ps2 = Some(uint id.virtual_host_port)) &&
	  (List.length dg.data > 0)
	then
	  (let dg = {dg with is1 = dg.is2; is2 = dg.is1;
		    ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
		    sYN = false; fIN = false; data = [];
  	            ts = timestamp_update_swap dg.ts (uint 1);
		    seq = dg.ack;
		    ack = dg.seq +.(uint (List.length dg.data)) +.
		       (if dg.sYN then uint 1 else uint 0) +.
		       (if dg.fIN then uint 1 else uint 0) +.
		       uint 500 (* bogus value to take us past snd_max *) } in
	  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
	  Mutex.lock lock; finished := true; Condition.signal cond;
	  Mutex.unlock lock);
	last_dgram_seen := SENT_DATAGRAM(dg)
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  delay 1.00;
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 300 '#', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  (* Block on condition variable here until we are signalled that testing has completed *)
  Mutex.lock lock;
  while !finished = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
  delay 1.00;
  rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_3: in state " ^ stdescr ^ ", the test host transmits a segment to the virtual host. The virtual host generates an acknowledgement that acknowledges past snd_max.",
  ((true, false), true, true, false),
  ((false, false), false, false, true))


(* rtt estimator footling *)
type ack_test7_option =
    TIMESTAMP
  | TIMED
  | NOTTIMED

let test7 = (function opt ->
  (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let last_dgram_seen = ref last_dgram in
  let lock, cond = Mutex.create (), Condition.create () in
  let finished = ref false in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(dg) ->
	if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (dg.ps2 = Some(uint id.virtual_host_port)) &&
	  (List.length dg.data > 0)
	then
	  (let dg = {dg with is1 = dg.is2; is2 = dg.is1;
		    ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
		    sYN = false; fIN = false; data = [];
 	            seq = dg.ack;
		    ack = dg.seq +.(uint (List.length dg.data)) +.
		       (if dg.sYN then uint 1 else uint 0) +.
		       (if dg.fIN then uint 1 else uint 0);
		    ts =
		     match opt with
		       TIMESTAMP -> timestamp_update_swap dg.ts ts_incr
	     | _ -> None
		   } in
	  last_dgram_seen := RECV_DATAGRAM(dg);
	  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
	  Mutex.lock lock; finished := true; Condition.signal cond;
	  Mutex.unlock lock)
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 20 'F', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  if opt = TIMED then
     (let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 20 'G', [])) in
     ignore(libd_call (the ts.th_libd_hnd) snd_call));

  (* Block on condition variable here until we are signalled that testing has completed *)
  Mutex.lock lock;
  while !finished = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 20 'H', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  delay 5.00;
  rst_driven_socket ts id fd !last_dgram_seen),
  "deliver_in_3: in state " ^ stdescr ^ ", the test host transmits a segment with a timestamp value. The virtual host replies with an ACK segment " ^
  (if opt = TIMESTAMP then "echoing the timestamp value. " else "without a timestamp value. ") ^
  (if opt = TIMED then "Hopefully the test host was timing its initial segment. If not we force the test host to transmit another segment which it should time."
  else if opt = NOTTIMED then "Hopefully the test host was not timing its initial segment."
  else ""),
  ((true, false), true, true, false),
  ((false, false), false, false, true)))


(* rexmt footling *)
type ack_test8_options =
    DONE
  | NOTIMER
  | REXMTSET
  | PERSISTSET

let test8 = (function opt ->
  (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let last_dgram_seen = ref last_dgram in
  let lock, cond = Mutex.create (), Condition.create () in
  let finished = ref false in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(dg) ->
	if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (dg.ps2 = Some(uint id.virtual_host_port)) &&
	  (List.length dg.data > 5)
	then
	  (let dg = {dg with is1 = dg.is2; is2 = dg.is1;
		    ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
		    sYN = false; fIN = false; data = [];
		    seq = dg.ack;
		    ack = dg.seq +.(uint (List.length dg.data)) +.
		       (if dg.sYN then uint 1 else uint 0) +.
		       (if dg.fIN then uint 1 else uint 0) -.
		       (match opt with
			 DONE -> uint 0
		       | _ -> uint 5);
		     win = (match opt with
		       PERSISTSET -> uint 0
		     | _ -> dg.win -. (uint 20));
		    ts = timestamp_update_swap dg.ts ts_incr
		   } in
	  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

(*	  if opt <> DONE then
	    (let dg = {dg with ack = dg.ack +. uint 10} in
	    injector_inject (the ts.th_injector_hnd) (TCPMSG(dg)));*)

	  Mutex.lock lock; finished := true; Condition.signal cond;
	  Mutex.unlock lock);
	last_dgram_seen := SENT_DATAGRAM(dg)
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 20 'F', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);
  if opt = NOTIMER then
     (let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 5 'G', [])) in
     ignore(libd_call (the ts.th_libd_hnd) snd_call));

  (* Block on condition variable here until we are signalled that testing has completed *)
  Mutex.lock lock;
  while !finished = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  delay 3.00;
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 20 'H', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  delay 2.00;
  rst_driven_socket ts id fd NO_DATAGRAMS),
  "deliver_in_3: in state " ^ stdescr ^ ", " ^
  (if opt = DONE then "test host sends a segment. The virtual host replies with an ACK segment where ack = snd_max, resetting the test host's rexmt timer"
  else if opt = NOTIMER then "test host sends a segment for which the rexmt timer is not set. The virtual host replies with an ACK segment where ack != snd_max and the rexmt timer is restarted"
  else if opt = REXMTSET then "test host sends a segment for which the rexmt timer is set. The virtual host replies with an ACK segment where ack != snd_max and the rexmt timer is restarteed"
  else "test host sends a segment for which the persit timer is set. The virtual host replies with an ACK segment where ack !=  snd_max and the persist timer is left alone"),
  ((true, false), true, true, false),
  ((false, false), false, false, true)))



(* cwnd footling *)
let test9 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let last_dgram_seen = ref last_dgram in
  let lock, cond = Mutex.create (), Condition.create () in
  let retransmit_from_loss = ref false in
  let finished = ref false in
  let counter = ref 1 in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(dg) ->
	if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (dg.ps2 = Some(uint id.virtual_host_port)) &&
	  (List.length dg.data > 5)
	then
	  Mutex.lock lock;
	  if !counter != 14 then
	    (Mutex.unlock lock;
	     last_dgram_seen := RECV_DATAGRAM(dg);
	     let dg = {dg with is1 = dg.is2; is2 = dg.is1;
		       ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
		       sYN = false; fIN = false; data = [];
		       seq = dg.ack;
		       ack = dg.seq +.(uint (List.length dg.data)) +.
			 (if dg.sYN then uint 1 else uint 0) +.
			 (if dg.fIN then uint 1 else uint 0);
		       ts = timestamp_update_swap dg.ts ts_incr
		     } in
	     injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
	     Mutex.lock lock;
	     if !counter = 45 then
	       (finished := true;
		Condition.signal cond;
		Mutex.unlock lock)
	     else Mutex.unlock lock)
	  else if !counter = 14 then
	    (retransmit_from_loss := true;
	     Condition.signal cond;
	     Mutex.unlock lock);
	Mutex.lock lock;
	counter := !counter + 1;
	Mutex.unlock lock;
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in
  delay 2.00;

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'F', [])) in
  let rec loop x =
    if x = 15 then ()
    else (ignore(libd_call (the ts.th_libd_hnd) snd_call);
	  delay 0.5;
	  loop (x+1))
  in loop 0;


  (* Block on condition variable here until we are signalled that the retransmit has happened *)
  (* ssthresh should now equal cwnd/2 *)
  Mutex.lock lock;
  while !retransmit_from_loss = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  delay 1.00; (* to guarentee a retransmit of the 15th packet *)

  (* cwnd should grow exponentially at first and linearly once >ssthresh *)
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'G', [])) in
   let rec loop x =
    if x = 30 then ()
    else (ignore(libd_call (the ts.th_libd_hnd) snd_call);
	  delay 0.2;
	  loop (x+1))
  in loop 0;

  (* Block on condition variable here until we are signalled that testing has completed *)
  Mutex.lock lock;
  while !finished = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  delay 5.00;
  rst_driven_socket ts id fd NO_DATAGRAMS),
  "deliver_in_3: in state " ^ stdescr ^ ", the test host transmits many segments. All but the last are acknowledged. The last segment is eventually retransmitted (hopefully setting ssthresh=cwnd/2 and reducing cwnd). The retransmited segment is ACKed and the test host sends many more segments all of which are ACKed. This should lead to the cwnd growing exponentially at first (upto ssthresh) and linearly afterwards.",
  ((true, false), true, true, false),
  ((false, false), false, false, true))



let ackstuff =
  (List.map test1 established_close_wait_states) @
  (List.map (test2 WIN) established_close_wait_states) @
  (List.map (test2 DATA) established_close_wait_states) @
  (List.map test3 established_close_wait_states) @
  (List.map test4 established_close_wait_states) @
  (List.map (test5 false) established_close_wait_states) @
  (List.map (test5 true) established_close_wait_states) @
  (List.map test6 established_close_wait_states) @
  (List.map (test7 TIMESTAMP) established_close_wait_states) @
  (List.map (test7 TIMED) established_close_wait_states) @
  (List.map (test7 NOTTIMED) established_close_wait_states) @
  (List.map (test8 DONE) established_close_wait_states) @
  (List.map (test8 NOTIMER) established_close_wait_states) @
  (List.map (test8 REXMTSET) established_close_wait_states) @
  (List.map (test8 PERSISTSET) established_close_wait_states) @
  (List.map test9 established_close_wait_states)


(* ---------------------------------------------------------------------- *)
(* datastuff: dealing with urgent and non-urgent data *)
(* ---------------------------------------------------------------------- *)

(* Updating snd_wnd *)
let test1 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let last_dgram_seen = ref last_dgram in
  let lock, cond = Mutex.create (), Condition.create () in
  let finished = ref false in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(dg) ->
	if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (dg.ps2 = Some(uint id.virtual_host_port)) &&
	  (List.length dg.data > 0)
	then
	  (let dg = {dg with is1 = dg.is2; is2 = dg.is1;
		     ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
		     sYN = false; fIN = false; data = [];
		     seq = dg.ack;
		     ack = dg.seq +.(uint (List.length dg.data)) +.
		       (if dg.sYN then uint 1 else uint 0) +.
		       (if dg.fIN then uint 1 else uint 0);
		     win=tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1; (*snd_wnd*)
		     ts = timestamp_update_swap dg.ts ts_incr;
		   } in
	  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
	  (* increase the windows size (so that win > snd_wnd) *)
	  let dg = { dg with win = dg.win +. (uint 20) } in
	  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
	  Mutex.lock lock; finished := true; Condition.signal cond;
	  Mutex.unlock lock);
	last_dgram_seen := SENT_DATAGRAM(dg)
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'F', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  (* Block on condition variable here until we are signalled that testing has completed *)
  Mutex.lock lock;
  while !finished = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 1448 'H', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  delay 5.00;
  rst_driven_socket ts id fd NO_DATAGRAMS),
  "deliver_in_3: in state " ^ stdescr ^ ", test host sends a segment that the virtual host acknowledges. The virtual host then duplicates the acknowledgement segment increasing the advertised window by 20 bytes. This should force the test host to update snd_wnd.",
  ((true, false), true, true, false),
  ((false, false), false, false, true))



let test2 =
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts
      (ST_SYN_RCVD) false in

  let dg =
    match last_dgram with
      SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1;
	 ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	 sYN = false; fIN = false; data = [];
	 seq = dg.ack;
	 ack = dg.seq +.(uint (List.length dg.data)) +.
	   (if dg.sYN then uint 1 else uint 0) +.
	   (if dg.fIN then uint 1 else uint 0);
	 ts = timestamp_update_swap dg.ts ts_incr;
	 win = dg.win +. (uint 4096);}
    | RECV_DATAGRAM(dg) ->
	{dg with sYN = false; fIN = false; aCK = true;
	 data = []; win = dg.win +. (uint 4096);
	 ts = timestamp_update dg.ts ts_incr;}
    | _ -> raise(Assertion_failed("deliver_in_3.datastuff.test2 got invalid last dgram"))
  in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  delay 2.00;
  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 20 'F', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  delay 1.00;
  rst_driven_socket ts id fd NO_DATAGRAMS),
  "deliver_in_3: in state ST_SYN_RECEIVED, host receives the final ACK segment establishing the connection. This does not have FIN set but does include a window update.",
  ((true, false), true, true, false),
  ((false, false), false, false, true)


(* urgent data processing *)
let test3 = (function (st, stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let last_dgram_seen = ref last_dgram in
  let lock, cond = Mutex.create (), Condition.create () in
  let finished = ref false in

  let outline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, false)) in
  ignore(libd_call (the ts.th_libd_hnd) outline_call);

  let dg =
    match !last_dgram_seen with
      SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1;
	 ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	 sYN = false; fIN = false; uRG = true;
	 seq = dg.ack;
	 ack = dg.seq +.(uint (List.length dg.data)) +.
	   (if dg.sYN then uint 1 else uint 0) +.
	   (if dg.fIN then uint 1 else uint 0);
	 ts = timestamp_update_swap dg.ts ts_incr;
	 urp = uint 10;
	 data = [uint 65; uint 66; uint 67; uint 68; uint 69;
		 uint 70; uint 71; uint 72; uint 73; uint 74;
		 uint 75; uint 76; uint 77; uint 78; uint 79;];}
    | RECV_DATAGRAM(dg) ->
	{dg with sYN = false; fIN = false; aCK = true; uRG = true;
	 ts = timestamp_update dg.ts ts_incr; urp = uint 10;
	 data = [uint 65; uint 66; uint 67; uint 68; uint 69;
		 uint 70; uint 71; uint 72; uint 73; uint 74;
		 uint 75; uint 76; uint 77; uint 78; uint 79;];}
    | _ -> raise(Assertion_failed("deliver_in_3.datastuff.test3 got invalid last dgram"))
  in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  let dg = { dg with seq = dg.seq +. uint 15; urp = uint 20; } in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  let inline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, true)) in
  ignore(libd_call (the ts.th_libd_hnd) inline_call);

  let dg = { dg with seq = dg.seq +. uint 15; urp = uint 6; } in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
  ignore(libd_call (the ts.th_libd_hnd) nonblock_call);

  delay 3.00;
  let rcv_call = (tid_of_int_private 0, RECV(fd, 45 ,[])) in
  ignore(libd_call (the ts.th_libd_hnd) rcv_call);

  let rcv_call = (tid_of_int_private 0, RECV(fd, 45 ,[])) in
  ignore(libd_call (the ts.th_libd_hnd) rcv_call);

  let rcv_call = (tid_of_int_private 0, RECV(fd, 45 ,[])) in
  ignore(libd_call (the ts.th_libd_hnd) rcv_call);

  delay 2.00;
  rst_driven_socket ts id fd (NO_DATAGRAMS)),
  "deliver_in_3: in state " ^ stdescr ^ ", the virtual host sends a segment to the test host with the urgent pointer set to a byte within the segment. This is received out-of-line. A further urgent segment is sent with the urgent pointer set to a byte in a future segment. SO_OOBLINE is then set on the test host and a further segment is sent, advancing the urgent pointer by one place, but now still pointing within the current segment. This byte is kept in-line. All urgent pointers in this test are valid (ie urp+(len rcvq)<=SB_MAX)",
  ((true, false), true, true, false),
  ((false, false), false, false, true))

let test4 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in

  let outline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, false)) in
  ignore(libd_call (the ts.th_libd_hnd) outline_call);

  let dg =
    match last_dgram with
      SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1;
	 ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	 sYN = false; fIN = false; uRG = true;
	 seq = dg.ack;
	 ack = dg.seq +.(uint (List.length dg.data)) +.
	   (if dg.sYN then uint 1 else uint 0) +.
	   (if dg.fIN then uint 1 else uint 0);
	 ts = timestamp_update_swap dg.ts ts_incr;
	 urp = uint 20;
	 data = [uint 65; uint 66; uint 67; uint 68; uint 69;
		 uint 70; uint 71; uint 72; uint 73; uint 74;
		 uint 75; uint 76; uint 77; uint 78; uint 79;];}
    | RECV_DATAGRAM(dg) ->
	{dg with sYN = false; fIN = false; aCK = true; uRG = true;
	 ts = timestamp_update dg.ts ts_incr; urp = uint 20;
	 data = [uint 65; uint 66; uint 67; uint 68; uint 69;
		 uint 70; uint 71; uint 72; uint 73; uint 74;
		 uint 75; uint 76; uint 77; uint 78; uint 79;];}
    | _ -> raise(Assertion_failed("deliver_in_3.datastuff.test4 got invalid last dgram"))
  in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  let dg = { dg with seq = dg.seq +. uint 15; urp = uint 5; } in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  let dg = { dg with seq = dg.seq +. uint 15; urp = uint 40; } in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  let dg = { dg with seq = dg.seq +. uint 15; urp = uint 25; } in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  let inline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, true)) in
  ignore(libd_call (the ts.th_libd_hnd) inline_call);

  let dg = { dg with seq = dg.seq +. uint 15; urp = uint 10; } in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
  ignore(libd_call (the ts.th_libd_hnd) nonblock_call);

  delay 3.00;
  let rcv_call = (tid_of_int_private 0, RECV(fd, 75 ,[])) in
  ignore(libd_call (the ts.th_libd_hnd) rcv_call);
  let rcv_call = (tid_of_int_private 0, RECV(fd, 75 ,[])) in
  ignore(libd_call (the ts.th_libd_hnd) rcv_call);
  let rcv_call = (tid_of_int_private 0, RECV(fd, 75 ,[])) in
  ignore(libd_call (the ts.th_libd_hnd) rcv_call);
  let rcv_call = (tid_of_int_private 0, RECV(fd, 75 ,[])) in
  ignore(libd_call (the ts.th_libd_hnd) rcv_call);

  delay 2.00;
  rst_driven_socket ts id fd (NO_DATAGRAMS)),
  "deliver_in_3: in state " ^ stdescr ^ ", the virtual host sends a segment to the test host with the urgent pointer set to a byte in the next segment. The next segment has the urgent pointer set to the same byte and the byte is received out-of-line. A further urgent segment is sent with the urgent pointer set to a byte in a future segment. The next segment also points to the same byte in a future segment (which happens to be the next segment due). SO_OOBLINE is then set on the test host and a further segment is sent, again pointing to the same urgent point, but is now pointing within the current segment. This byte is kept in-line. All urgent pointers in this test are valid (ie urp+(len rcvq)<=SB_MAX)",
  ((true, false), true, true, false),
  ((false, false), false, false, true))



let test5 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in

  let outline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, false)) in
  ignore(libd_call (the ts.th_libd_hnd) outline_call);

  let dg =
    match last_dgram with
      SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1;
	 ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	 sYN = false; fIN = false; uRG = true;
	 seq = dg.ack;
	 ack = dg.seq +.(uint (List.length dg.data)) +.
	   (if dg.sYN then uint 1 else uint 0) +.
	   (if dg.fIN then uint 1 else uint 0);
	 ts = timestamp_update_swap dg.ts ts_incr;
	 urp = uint 40;
	 data = [uint 65; uint 66; uint 67; uint 68; uint 69;
		 uint 70; uint 71; uint 72; uint 73; uint 74;
		 uint 75; uint 76; uint 77; uint 78; uint 79;];}
    | RECV_DATAGRAM(dg) ->
	{dg with sYN = false; fIN = false; aCK = true; uRG = true;
	 ts = timestamp_update dg.ts ts_incr; urp = uint 40;
	 data = [uint 65; uint 66; uint 67; uint 68; uint 69;
		 uint 70; uint 71; uint 72; uint 73; uint 74;
		 uint 75; uint 76; uint 77; uint 78; uint 79;];}
    | _ -> raise(Assertion_failed("deliver_in_3.datastuff.test5 got invalid last dgram"))
  in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  let dg = { dg with seq = dg.seq +. uint 15; urp = uint 5; } in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  delay 5.00;
  rst_driven_socket ts id fd (NO_DATAGRAMS)),
  "deliver_in_3: in state " ^ stdescr ^ ". The virtual host sends a segment to the test host with the urgent pointer set to a byte in a future segment. The next segment has the urgest pointer set to a byte within itself (which is earlier in the data stream than the previously flagged urgent byte). This should be ignored. All urgent pointers in this test are valid (ie urp+(len rcvq)<=SB_MAX)",
  ((true, false), true, true, false),
  ((false, false), false, false, true))



let test6 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let outline_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_OOBINLINE, false)) in
  ignore(libd_call (the ts.th_libd_hnd) outline_call);

  let dg =
    match last_dgram with
      SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1;
	 ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	 sYN = false; fIN = false; uRG = true;
	 seq = dg.ack;
	 ack = dg.seq +.(uint (List.length dg.data)) +.
	   (if dg.sYN then uint 1 else uint 0) +.
	   (if dg.fIN then uint 1 else uint 0);
	 ts = timestamp_update_swap dg.ts ts_incr;
	 urp = uint 500000;
	 data = [uint 65; uint 66; uint 67; uint 68; uint 69;
		 uint 70; uint 71; uint 72; uint 73; uint 74;
		 uint 75; uint 76; uint 77; uint 78; uint 79;];}
    | RECV_DATAGRAM(dg) ->
	{dg with sYN = false; fIN = false; aCK = true; uRG = true;
	 ts = timestamp_update dg.ts ts_incr; urp = uint 500000;
	 data = [uint 65; uint 66; uint 67; uint 68; uint 69;
		 uint 70; uint 71; uint 72; uint 73; uint 74;
		 uint 75; uint 76; uint 77; uint 78; uint 79;];}
    | _ -> raise(Assertion_failed("deliver_in_3.datastuff.test6 got invalid last dgram"))
  in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
  ignore(libd_call (the ts.th_libd_hnd) nonblock_call);

  delay 3.00;
  let rcv_call = (tid_of_int_private 0, RECV(fd, 15 ,[])) in
  ignore(libd_call (the ts.th_libd_hnd) rcv_call);

  delay 2.00;
  rst_driven_socket ts id fd (NO_DATAGRAMS)),
  "deliver_in_3: in state " ^ stdescr ^ ". The virtual host sends a segment to the test host with the urgent pointer set to a byte in a future segment. The urgent pointer is invalid as urp+(len rcvq) > SB_MAX",
  ((true, false), true, true, false),
  ((false, false), false, false, true))



(* processing normal data and FINs *)
let test7 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let lock, cond = Mutex.create (), Condition.create () in
  let finished = ref false in

 let original_dg =
    match last_dgram with
      SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1;
	 ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	 sYN = false; fIN = false; uRG = true;
	 seq = dg.ack;
	 ack = dg.seq +.(uint (List.length dg.data)) +.
	   (if dg.sYN then uint 1 else uint 0) +.
	   (if dg.fIN then uint 1 else uint 0);
	 ts = timestamp_update_swap dg.ts ts_incr;
	 data = data_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";}
    | RECV_DATAGRAM(dg) ->
	{dg with sYN = false; fIN = false; aCK = true; uRG = true;
	 ts = timestamp_update dg.ts ts_incr;
	 data = data_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";}
    | _ -> raise(Assertion_failed("deliver_in_3.datastuff.test7 got invalid last dgram"))
 in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
 let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(dg) ->
	if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (dg.ps2 = Some(uint id.virtual_host_port)) &&
	  dg.aCK
	then
	  (let new_dg = {original_dg with seq = original_dg.seq +. uint 1;
			 data = all_but_last(List.tl(original_dg.data));} in
	  injector_inject (the ts.th_injector_hnd) (TCPMSG(new_dg));
	  Mutex.lock lock; finished := true; Condition.signal cond;
	  Mutex.unlock lock);
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  injector_inject (the ts.th_injector_hnd) (TCPMSG(original_dg));

  (* Block on condition variable here until we are signalled that testing has completed *)
  Mutex.lock lock;
  while !finished = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  let snd_call = (tid_of_int_private 0, SEND(fd, None, String.make 20 'F', [])) in
  ignore(libd_call (the ts.th_libd_hnd) snd_call);

  delay 3.00;
  rst_driven_socket ts id fd NO_DATAGRAMS),
  "deliver_in_3: in state " ^ stdescr ^ ", virtual host sends a segment to the test host and waits for its acknowledgement. It then sends a segment that lies within the previous sent sequence number range (duplicating the data). This should trigger a dropwithack. ",
  ((true, false), true, true, false),
  ((false, false), false, false, true))



let test8 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
  let lock, cond = Mutex.create (), Condition.create () in
  let finished = ref false in

 let original_dg =
    match last_dgram with
      SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1;
	 ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	 sYN = false; fIN = false; uRG = true;
	 seq = dg.ack;
	 ack = dg.seq +.(uint (List.length dg.data)) +.
	   (if dg.sYN then uint 1 else uint 0) +.
	   (if dg.fIN then uint 1 else uint 0);
	 ts = timestamp_update_swap dg.ts ts_incr;
	 data = data_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";}
    | RECV_DATAGRAM(dg) ->
	{dg with sYN = false; fIN = false; aCK = true; uRG = true;
	 ts = timestamp_update dg.ts ts_incr;
	 data = data_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";}
    | _ -> raise(Assertion_failed("deliver_in_3.datastuff.test8 got invalid last dgram"))
 in

  (* A slurper callback function that generates some ACKs for *)
  (* incoming segments *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(dg) ->
	if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (dg.ps2 = Some(uint id.virtual_host_port)) &&
	  dg.aCK
	then
	  (let new_dg = {original_dg with seq = original_dg.seq +. dg.win +. uint 1000 ;
			 data = all_but_last(List.tl(original_dg.data));} in
	  injector_inject (the ts.th_injector_hnd) (TCPMSG(new_dg));
	  Mutex.lock lock; finished := true; Condition.signal cond;
	  Mutex.unlock lock);
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  injector_inject (the ts.th_injector_hnd) (TCPMSG(original_dg));

  (* Block on condition variable here until we are signalled that testing has completed *)
  Mutex.lock lock;
  while !finished = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  delay 5.00;
  rst_driven_socket ts id fd NO_DATAGRAMS),
  "deliver_in_3: in state " ^ stdescr ^ ", virtual host sends a segment to the test host and waits for its acknowledgement. It then sends a segment that lies completely off the right hand edge of the window just advertised by the test host ",
  ((true, false), true, true, false),
  ((false, false), false, false, true))


(* -=-=-=-=-=-=-=-=- *)


let exhaust_window inj_hnd dg win_now =
  let iters = (Int64.div win_now (uint 500)) +. (uint 1) in
  let dg = {dg with data = data_500_bytes;} in
  let rec loop i dg =
    if i = iters then (dg.seq +. (uint 500))
    else
      let _ = injector_inject inj_hnd (TCPMSG(dg)) in
      delay 0.5;
      loop (i +. uint 1) {dg with seq = dg.seq +. (uint 500)};
  in loop Int64.zero dg


let test9 = (function (st,stdescr) ->
  (function id -> function ts ->
  let fd, last_dgram, _ = tcp_state_diagram_driver id ts
      (ST_ESTABLISHED(DATA_SENT_RCVD)) false in
  let last_dgram_seen = ref last_dgram in
  let lock, cond = Mutex.create (), Condition.create () in
  let finished = ref false in

  let original_dg =
    match last_dgram with
      SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1;
	 ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	 sYN = false; fIN = false; uRG = true;
	 seq = dg.ack;
	 ack = dg.seq +.(uint (List.length dg.data)) +.
	   (if dg.sYN then uint 1 else uint 0) +.
	   (if dg.fIN then uint 1 else uint 0);
	 ts = timestamp_update_swap dg.ts ts_incr;
	 data = data_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";}
    | RECV_DATAGRAM(dg) ->
	{dg with sYN = false; fIN = false; aCK = true; uRG = true;
	 ts = timestamp_update dg.ts ts_incr;
	 data = data_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";}
    | _ -> raise(Assertion_failed("deliver_in_3.datastuff.test9 got invalid last dgram"))
  in

  let win = ref Int64.zero in

  (* A slurper callback function *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(dg) ->
	if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (dg.ps2 = Some(uint id.virtual_host_port)) &&
	  dg.aCK
	then
	  (Mutex.lock lock; finished := true; Condition.signal cond;
	   Mutex.unlock lock; last_dgram_seen := SENT_DATAGRAM(dg);
	   win := dg.win);
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  injector_inject (the ts.th_injector_hnd) (TCPMSG(original_dg));
  (* Block on condition variable here until we are signalled that the slurping has completed *)
  Mutex.lock lock;
  while !finished = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
  delay 2.00;

  let exhausting_dg =
    match !last_dgram_seen with
      SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1;
	 ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	 sYN = false; fIN = false; uRG = true;
	 seq = dg.ack;
	 ack = dg.seq +.(uint (List.length dg.data)) +.
	   (if dg.sYN then uint 1 else uint 0) +.
	   (if dg.fIN then uint 1 else uint 0);
	 ts = timestamp_update_swap dg.ts ts_incr;
	 data = [];}
    | _ -> raise(Assertion_failed("deliver_in_3.datastuff.test9.2 expected a SENT_DATAGRAM"))
  in

  (* Exhaust the window *)
  let cseq = exhaust_window (the ts.th_injector_hnd) exhausting_dg !win in
  (* Pause momentarily *)
  delay 2.00;
  (* Emit a window probe *)
  let dg = {exhausting_dg with seq = cseq; data = [(uint (Char.code 'P'));]} in
  injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

  delay 5.00;
  rst_driven_socket ts id fd NO_DATAGRAMS),
  "deliver_in_3: in state " ^ stdescr ^ ", continually send 500 byte segments to the test host until its receive window is exhausted. Finally send a one-byte segment to perform a window probe.",
  ((true, false), true, true, false),
  ((false, false), false, false, true))


(* -=-=-=-=-=-=-=-=- *)


let test10_thunk =
  (function seq_diff -> function data_len -> function escape_win -> function sendfin ->
    (function (st,stdescr) -> (function id -> function ts ->
      let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
      let last_dgram_seen = ref last_dgram in
      let lock, cond = Mutex.create (), Condition.create () in
      let finished = ref false in

      let original_dg =
	match last_dgram with
	  SENT_DATAGRAM(dg) ->
	    {dg with is1 = dg.is2; is2 = dg.is1;
	     ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	     sYN = false; fIN = false; uRG = false;
	     seq = dg.ack;
	     ack = dg.seq +.(uint (List.length dg.data)) +.
	       (if dg.sYN then uint 1 else uint 0) +.
	       (if dg.fIN then uint 1 else uint 0);
	     ts = timestamp_update_swap dg.ts ts_incr;
	     data = data_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";}
	| RECV_DATAGRAM(dg) ->
	    {dg with sYN = false; fIN = false; aCK = true; uRG = false;
	     ts = timestamp_update dg.ts ts_incr;
	     data = data_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";}
	| _ -> raise(Assertion_failed("deliver_in_3.datastuff.test10 got invalid last dgram"))
      in

      let win = ref Int64.zero in

     (* A slurper callback function that generates some ACKs for *)
     (* incoming segments *)
      let slurper_callback_fun holmsg =
	match holmsg with
	  TCPMSG(dg) ->
	    if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	      (dg.ps2 = Some(uint id.virtual_host_port)) &&
	      dg.aCK
	    then
	      (win := dg.win; last_dgram_seen := SENT_DATAGRAM(dg);
	       Mutex.lock lock; finished := true; Condition.signal cond;
	       Mutex.unlock lock; );
	| _ -> ()
      in
      let slurper_callback_hnd = slurper_register_callback
	  (the ts.th_slurper_hnd) slurper_callback_fun in

      injector_inject (the ts.th_injector_hnd) (TCPMSG(original_dg));
      (* Block on condition variable here until we are signalled that the slurping has completed *)
      Mutex.lock lock;
      while !finished = false do
	Condition.wait cond lock;
      done;
      Mutex.unlock lock;
      (* Unregister the callback *)
      slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

      let exhausting_dg =
	match !last_dgram_seen with
	  SENT_DATAGRAM(dg) ->
	    {dg with is1 = dg.is2; is2 = dg.is1;
	     ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	     sYN = false; fIN = false; uRG = false;
	     seq = dg.ack;
	     ack = dg.seq +.(uint (List.length dg.data)) +.
	       (if dg.sYN then uint 1 else uint 0) +.
	       (if dg.fIN then uint 1 else uint 0);
	     ts = timestamp_update_swap dg.ts ts_incr;
	     data = [];}
	| _ -> raise(Assertion_failed("deliver_in_3.datastuff.test10.2 expected a SENT_DATAGRAM"))
      in

      (* Exhaust the window *)
      let cseq = if escape_win then
	let s = exhaust_window (the ts.th_injector_hnd) exhausting_dg !win in
	let recv_call = (tid_of_int_private 0, RECV(fd, data_len/2, [])) in
	ignore(libd_call (the ts.th_libd_hnd) recv_call);
	s
      else
	exhausting_dg.seq in
      (* Pause momentarily *)
      delay 0.25;

      (* Emit the data packet *)
      let dg = {exhausting_dg with seq = cseq +. seq_diff;
		fIN = sendfin; data = data_n_bytes data_len; } in
      injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
      delay 5.00;
      rst_driven_socket ts id fd (NO_DATAGRAMS)),
    "deliver_in_3: in state " ^ stdescr ^ ": the test host " ^
    (if escape_win then ", with an almost exhausted receive window, " else "") ^
    "receives a segment with seq=rcv_nxt" ^ (if seq_diff = uint 0 then "" else "-1") ^
    " and with " ^ (string_of_int data_len) ^ " bytes of data so that seq+length(data)" ^
    (if data_len = 20 then ">" else "=") ^ ". The segment also has the FIN flag " ^
    (if sendfin then "set." else "unset."),
    ((true, false), true, true, false),
    ((false, false), false, false, true)))



let test10 = [test10_thunk (uint 0) 20 false false;
	      test10_thunk (uint (-1)) 20 false false;
	      test10_thunk (uint 0) 0 false false;
	      test10_thunk (uint (-1)) 1 false false;
	      test10_thunk (uint 0) 20 false true;
	      test10_thunk (uint (-1)) 20 false true;
	      test10_thunk (uint 0) 0 false true;
	      test10_thunk (uint (-1)) 1 false true;
	      test10_thunk (uint 0) 20 true false;
	      test10_thunk (uint (-1)) 20 true false;
	      test10_thunk (uint 0) 20 true true;
	      test10_thunk (uint (-1)) 20 true true;
	      test10_thunk (uint 0) 0 true true;
	      test10_thunk (uint (-1)) 0 true true;]


let test11 =
  (function sendfin ->
    (function (st,stdescr) -> (function id -> function ts ->
      let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in

      let dg_first =
	match last_dgram with
	  SENT_DATAGRAM(dg) ->
	    {dg with is1 = dg.is2; is2 = dg.is1;
	     ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	     sYN = false; fIN = sendfin; uRG = true;
	     seq = dg.ack +. uint 2000;
	     ack = dg.seq +.(uint (List.length dg.data)) +.
	       (if dg.sYN then uint 1 else uint 0) +.
	       (if dg.fIN then uint 1 else uint 0);
	     ts = timestamp_update_swap dg.ts ts_incr;
	     urp = uint 500000;
	     data = data_n_bytes 1000;}
	| RECV_DATAGRAM(dg) ->
	    {dg with sYN = false; fIN = sendfin; aCK = true; uRG = true;
	     seq = dg.seq +. uint 2000;
	     ts = timestamp_update dg.ts ts_incr; urp = uint 500000;
	     data = data_n_bytes 1000;}
	| _ -> raise(Assertion_failed("deliver_in_3.datastuff.test11 got invalid last dgram"))
      in
      injector_inject (the ts.th_injector_hnd) (TCPMSG(dg_first));

      let dg = {dg_first with seq = dg_first.seq -. (uint 1000);} in
      injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

      let dg = {dg with seq = dg.seq -. (uint 1000);} in
      injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));

      let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
      ignore(libd_call (the ts.th_libd_hnd) nonblock_call);

      delay 5.00;
      let rcv_call = (tid_of_int_private 0, RECV(fd, 1000 ,[])) in
      ignore(libd_call (the ts.th_libd_hnd) rcv_call);
      let rcv_call = (tid_of_int_private 0, RECV(fd, 1000 ,[])) in
      ignore(libd_call (the ts.th_libd_hnd) rcv_call);
      let rcv_call = (tid_of_int_private 0, RECV(fd, 1000 ,[])) in
      ignore(libd_call (the ts.th_libd_hnd) rcv_call);

      delay 2.00;
      rst_driven_socket ts id fd NO_DATAGRAMS),
    "deliver_in_3: in state " ^ stdescr ^ ", the virtual host sends a segment to the test host that has seq>rcv_nxt and seq<(rcv_nxt+rcv_wnd) and the FIN flag " ^ (if sendfin then "set" else "clear") ^ ". This segment is an out-of-order segment. Further segments arrive later to plug the hole.",
    ((true, false), true, true, false),
    ((false, false), false, false, true)))


let test12 =
    (function id -> function ts ->
      let fd, last_dgram, _ = tcp_state_diagram_driver id ts (ST_ESTABLISHED(DATA_SENT_RCVD)) false in
      let last_dgram_seen = ref last_dgram in
      let lock, cond = Mutex.create (), Condition.create () in
      let finished = ref false in

      let original_dg =
	match last_dgram with
	  SENT_DATAGRAM(dg) ->
	    {dg with is1 = dg.is2; is2 = dg.is1;
	     ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	     sYN = false; fIN = false; uRG = true;
	     seq = dg.ack;
	     ack = dg.seq +.(uint (List.length dg.data)) +.
	       (if dg.sYN then uint 1 else uint 0) +.
	       (if dg.fIN then uint 1 else uint 0);
	     ts = timestamp_update_swap dg.ts ts_incr;
	     data = data_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";}
	| RECV_DATAGRAM(dg) ->
	    {dg with sYN = false; fIN = false; aCK = true; uRG = false;
	     ts = timestamp_update dg.ts ts_incr;
	     data = data_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";}
	| _ -> raise(Assertion_failed("deliver_in_3.datastuff.test10 got invalid last dgram"))
      in

      let win = ref Int64.zero in

     (* A slurper callback function that generates some ACKs for *)
     (* incoming segments *)
      let slurper_callback_fun holmsg =
	match holmsg with
	  TCPMSG(dg) ->
	    if (dg.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	      (dg.ps2 = Some(uint id.virtual_host_port)) &&
	      dg.aCK
	    then
	      (win := dg.win; last_dgram_seen := SENT_DATAGRAM(dg);
	       Mutex.lock lock; finished := true; Condition.signal cond;
	       Mutex.unlock lock; );
	| _ -> ()
      in
      let slurper_callback_hnd = slurper_register_callback
	  (the ts.th_slurper_hnd) slurper_callback_fun in

      injector_inject (the ts.th_injector_hnd) (TCPMSG(original_dg));
      (* Block on condition variable here until we are signalled that the slurping has completed *)
      Mutex.lock lock;
      while !finished = false do
	Condition.wait cond lock;
      done;
      Mutex.unlock lock;
      (* Unregister the callback *)
      slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

      let exhausting_dg =
	match !last_dgram_seen with
	  SENT_DATAGRAM(dg) ->
	    {dg with is1 = dg.is2; is2 = dg.is1;
	     ps1 = dg.ps2; ps2 = dg.ps1; aCK = true;
	     sYN = false; fIN = false; uRG = true;
	     seq = dg.ack;
	     ack = dg.seq +.(uint (List.length dg.data)) +.
	       (if dg.sYN then uint 1 else uint 0) +.
	       (if dg.fIN then uint 1 else uint 0);
	     ts = timestamp_update_swap dg.ts ts_incr;
	     data = [];}
	| _ -> raise(Assertion_failed("deliver_in_3.datastuff.test10.2 expected a SENT_DATAGRAM"))
      in

      (* Exhaust the window *)
      let cseq = exhausting_dg.seq in
      (* Pause momentarily *)
      delay 0.25;

      (* Emit the data packet *)
      let dg = {exhausting_dg with seq = cseq +. (uint 1);
		fIN = false; data = data_n_bytes 20 } in
      injector_inject (the ts.th_injector_hnd) (TCPMSG(dg));
      delay 5.00;
      rst_driven_socket ts id fd (NO_DATAGRAMS)),
    "deliver_in_3: in state ESTABLISHED the test host receives a segment with seq=rcv_nxt-1, the URG flag set, and with 20 bytes of data so that seq+length(data) >.",
    ((true, false), true, true, false),
    ((false, false), false, false, true)



let datastuff =
  (List.map test1 established_close_wait_states) @
  [test2] @
  (List.map test3 post_established_driven_states) @
  (List.map test4 post_established_driven_states) @
  (List.map test5 post_established_driven_states) @
  (List.map test6 post_established_driven_states) @
  (List.map test7 established_fin_wait_states) @
  (List.map test8 established_fin_wait_states) @
  (List.map test9 established_fin_wait_states) @
  (List.flatten (List.map (function st ->
    List.map (function thunk -> thunk st) test10)
		   established_fin_wait_states)) @
  (List.map (test11 false) post_established_driven_states) @
  (List.map (test11 true) post_established_driven_states) @
  [test12]


(* ---------------------------------------------------------------------- *)


let tcp_tests = [
  topstuff, "deliver_in_3 topstuff";
  ackstuff, "deliver_in_3 ackstuff";
  datastuff, "deliver_in_3 datastuff";
]

let udp_tests = []

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests


let do_deliver_in_3_tests handle hosts_list test_type =
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

let get_deliver_in_3_test_descriptions () =
  prerr_endline "\n";
  List.iter
    (function (next_test_set, set_descr) ->
      prerr_endline (set_descr ^ "\n------------------\n\n");
      List.iter
	(function (test_thunk, descr, thts, ahts) ->
	  prerr_endline (descr ^ "\n\n")
	) next_test_set
    ) normal_tests

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
