(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: network tests                       *)
(* Adam Biltcliffe - Created 20060612                                     *)
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

(*open Render*)

(* ---------------------------------------------------------------------- *)

(* nb. all network tests should have tool selectors for the form:         *)
(*  ((true, priv), true, true, false)                                     *)
(* that is, both hosts should be fully instrumented, while cheating using *)
(* the injector is strictly not allowed                                   *)

(* ---------------------------------------------------------------------- *)

(* A fairly quick-and-dirty hack to allow rotating port numbers for each
   test so we don't have to wait for the 2MSL timeout (since adding this
   to the code below would bring it out of sync with the many
   duplications we might want to refactor back together one day, this
   seems a better solution) -- amgb *)
let port_counter = ref 0

let get_next_port_for_host host =
    let n = !port_counter in
    port_counter := (n + 1);
    host.test_listening_port_base + (n mod host.test_listening_port_range)

(* ---------------------------------------------------------------------- *)

let make_bind_call hnd fd (addr, port) =
    let bind_call = (tid_of_int_private 0, BIND(fd, addr, port)) in
    ignore (libd_call hnd bind_call)

let make_listen_call hnd fd backlog =
    let listen_call = (tid_of_int_private 0, LISTEN(fd, backlog)) in
    ignore (libd_call hnd listen_call)

let make_connect_call hnd fd (addr, port) =
    let connect_call = (tid_of_int_private 0, CONNECT(fd, addr, port)) in
    ignore (libd_call hnd connect_call)

let make_close_call hnd fd =
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore (libd_call hnd close_call);;

let accept_connection hnd fd =
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    let libret = libd_call hnd accept_call in
    match libret with
      (_, OK_FD_IP_PORT(fd,_)) -> fd
    | _ -> raise (Drive_Failure("accept() failed"));;

let dup_fd hnd fd =
    let dup_call = (tid_of_int_private 0, DUP(fd)) in
    let libret = libd_call hnd dup_call in
    match libret with
      (_, OK_FD(fd)) -> fd
    | _ -> raise (Drive_Failure("dup() failed"));;

(* shorthand for a couple of common cases *)
let establish_connection id ts =
    let listening_port_no = get_next_port_for_host id.aux_host in
    let fd = get_socket (the ts.th_libd_hnd) in
    let fd_aux_listening = get_socket (the ts.ah_libd_hnd) in
    make_bind_call (the ts.ah_libd_hnd) fd_aux_listening (Some (mk_ip id.aux_host.test_ip_address), Some(mk_port listening_port_no));
    make_listen_call (the ts.ah_libd_hnd) fd_aux_listening 3;
    make_connect_call (the ts.th_libd_hnd) fd (mk_ip id.aux_host.test_ip_address, Some(mk_port listening_port_no));
    let fd_acc = accept_connection (the ts.ah_libd_hnd) fd_aux_listening in
    make_close_call (the ts.ah_libd_hnd) fd_aux_listening;
    (fd, fd_acc);;

(* shorthand for a common case---note that this expects the first fd to   *)
(* be on the test host and the second to be on the aux host, don't try to *)
(* use it for anything else!                                              *)
let teardown_connection id ts fd fd_aux =
    make_close_call (the ts.th_libd_hnd) fd;
    make_close_call (the ts.ah_libd_hnd) fd_aux;;

(* same, but aux host initiates the close *)
let teardown_connection_aux_first id ts fd fd_aux =
    make_close_call (the ts.ah_libd_hnd) fd_aux;
    make_close_call (the ts.th_libd_hnd) fd;;

let make_send_call hnd fd data =
    let send_call = (tid_of_int_private 0, SEND(fd, None, data, [])) in
    ignore (libd_call hnd send_call)

let make_send_call_with_flags hnd fd data flags =
    let send_call = (tid_of_int_private 0, SEND(fd, None, data, flags)) in
    ignore (libd_call hnd send_call)

let make_recv_call hnd fd n =
    let recv_call = (tid_of_int_private 0, RECV(fd, n, [])) in
    ignore (libd_call hnd recv_call);;

let make_recv_call_with_flags hnd fd n flags =
    let recv_call = (tid_of_int_private 0, RECV(fd, n, flags)) in
    ignore (libd_call hnd recv_call);;

let make_names_calls hnd fd =
    let getsockname_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore (libd_call hnd getsockname_call);
    let getpeername_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore (libd_call hnd getpeername_call);;

let make_setfileflags_call hnd fd flags =
    let sff_call = (tid_of_int_private 0, SETFILEFLAGS(fd, flags)) in
    ignore (libd_call hnd sff_call);;

let make_shutdown_call hnd fd (r,w) =
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, r, w)) in
    ignore (libd_call hnd shutdown_call);;

let make_close_call hnd fd =
    let close_call = (tid_of_int_private 0, CLOSE(fd)) in
    ignore (libd_call hnd close_call);;

let make_disconnect_call hnd fd =
    let disco_call = (tid_of_int_private 0, DISCONNECT(fd)) in
    ignore (libd_call hnd disco_call);;

let make_setsockbopt_call hnd fd opt v =
    let ssbo_call = (tid_of_int_private 0, SETSOCKBOPT(fd, opt, v)) in
    ignore (libd_call hnd ssbo_call);;

let make_setsocknopt_call hnd fd opt v =
    let ssno_call = (tid_of_int_private 0, SETSOCKNOPT(fd, opt, v)) in
    ignore (libd_call hnd ssno_call);;

let make_setsocktopt_call hnd fd opt v =
    let ssto_call = (tid_of_int_private 0, SETSOCKTOPT(fd, opt, v)) in
    ignore (libd_call hnd ssto_call);;

let make_getsocklistening_call hnd fd =
    let gsl_call = (tid_of_int_private 0, GETSOCKLISTENING(fd)) in
    ignore (libd_call hnd gsl_call);;

let make_pselect_call hnd (rl, wl, el) time sigs =
    let pselect_call = (tid_of_int_private 0, PSELECT(rl,wl,el, time, sigs)) in
    ignore (libd_call hnd pselect_call);;

(* do this at the end of every test, so we don't get TIME_WAIT sockets
   hanging around *)
let destroy_socket hnd fd =
    make_setsocktopt_call hnd fd SO_LINGER (Some(0,0));
    make_close_call hnd fd

let destroy_sockets id ts fd fd_aux =
    destroy_socket (the ts.th_libd_hnd) fd;
    destroy_socket (the ts.ah_libd_hnd) fd_aux;;

(* some tests require a socket which has already been used to send data *)
let send_some_data id ts fd fd_aux =
    make_send_call (the ts.th_libd_hnd) fd "ping";
    make_recv_call (the ts.ah_libd_hnd) fd_aux 4;;

(* other tests require a socket which has already received data *)
let recv_some_data id ts fd fd_aux =
    make_send_call (the ts.ah_libd_hnd) fd_aux "pong";
    make_recv_call (the ts.th_libd_hnd) fd 4;;

(* ---------------------------------------------------------------------- *)

(* Now, some code to create connections in various states. This doesn't yet
   cover all the possible states we might want to investigate, but some of
   them are impossible to achieve and maintain for any length of time
   without the ability to delay packets in transit *)

let all_achievable_network_states = [
    ST_CLOSED;
    ST_LISTEN;
    ST_ESTABLISHED(NO_DATA);
    ST_ESTABLISHED(DATA_SENT);
    ST_ESTABLISHED(DATA_RCVD);
    ST_ESTABLISHED(DATA_SENT_RCVD);
    ST_CLOSE_WAIT(NO_DATA);
    ST_CLOSE_WAIT(DATA_SENT);
    ST_CLOSE_WAIT(DATA_RCVD);
    ST_CLOSE_WAIT(DATA_SENT_RCVD);
    ST_FIN_WAIT_2(NO_DATA);
    ST_FIN_WAIT_2(DATA_SENT);
    ST_FIN_WAIT_2(DATA_RCVD);
    ST_FIN_WAIT_2(DATA_SENT_RCVD);
    ST_TIME_WAIT(NO_DATA);
    ST_TIME_WAIT(DATA_SENT);
    ST_TIME_WAIT(DATA_RCVD);
    ST_TIME_WAIT(DATA_SENT_RCVD)
  ]

let all_interesting_network_states = [
    ST_CLOSED;
    ST_LISTEN;
    ST_ESTABLISHED(DATA_SENT_RCVD);
    ST_CLOSE_WAIT(DATA_SENT_RCVD);
    ST_FIN_WAIT_2(DATA_SENT_RCVD);
    ST_TIME_WAIT(DATA_SENT_RCVD);
  ]

(* would like to add to this list: SYN_SENT, SYN_RCVD, FIN_WAIT_1,
   CLOSING, LAST_ACK, if it ever becomes possible *)

let string_of_data_state d =
  match d with
    NO_DATA -> "(no data)"
  | DATA_SENT -> "(data sent)"
  | DATA_RCVD -> "(data rcvd)"
  | DATA_SENT_RCVD -> "(data sent/rcvd)"

let string_of_st st =
  match st with
    ST_CLOSED -> "CLOSED"
  | ST_LISTEN -> "LISTEN"
  | ST_SYN_SENT -> "SYN_SENT"
  | ST_SYN_RCVD -> "SYN_RCVD"
  | ST_ESTABLISHED(d) -> "ESTABLISHED" ^ (string_of_data_state d)
  | ST_CLOSE_WAIT(d) -> "CLOSE_WAIT" ^ (string_of_data_state d)
  | ST_LAST_ACK(d) -> "LAST_ACK" ^ (string_of_data_state d)
  | ST_FIN_WAIT_1(d) -> "FIN_WAIT_1" ^ (string_of_data_state d)
  | ST_FIN_WAIT_2(d) -> "FIN_WAIT_2" ^ (string_of_data_state d)
  | ST_CLOSING(d) -> "CLOSING" ^ (string_of_data_state d)
  | ST_TIME_WAIT(d) -> "TIME_WAIT" ^ (string_of_data_state d)

let make_fin_callback lock cond srcip dstip srcport dstport =
(* callback to watch for a FIN and record its sequence no. *)
  let seq = ref None in
  let f holmsg =
    match holmsg with
      TCPMSG(dg) ->
        if (dg.fIN = true) && (dg.is1 = Some (hol_ip srcip)) &&
            (dg.is2 = Some (hol_ip dstip)) && (dg.ps1 = Some (uint srcport))
             && (dg.ps2 = Some(uint dstport)) then
          (Mutex.lock lock; seq := Some dg.seq;
           Condition.signal cond; Mutex.unlock lock)
        else ()
    | _ -> () in
  f, seq

let make_ack_callback lock cond srcip dstip srcport dstport =
(* callback to watch for ACKs and track the sequence no. acked *)
  let ack = ref None in
  let f holmsg =
    match holmsg with
      TCPMSG(dg) ->
        if (dg.aCK = true) && (dg.is1 = Some (hol_ip srcip)) &&
            (dg.is2 = Some (hol_ip dstip)) && (dg.ps1 = Some (uint srcport))
             && (dg.ps2 = Some(uint dstport)) then
          (Mutex.lock lock; ack := Some dg.ack;
           Condition.signal cond; Mutex.unlock lock)
        else ()
    | _ -> () in
  f, ack

let drive_connection_to_state id ts state =
  let t_ip = id.test_host.test_ip_address in
  let t_port = id.test_host.test_ephm_port in
  let a_ip = id.aux_host.test_ip_address in
  let a_port = (get_next_port_for_host id.aux_host) in
  let rec dv st =
  match st with
    ST_CLOSED ->
      let fd = get_socket (the ts.th_libd_hnd) in
      let fd_aux = get_socket (the ts.ah_libd_hnd) in
      make_setsockbopt_call (the ts.th_libd_hnd) fd SO_REUSEADDR true;
      make_setsockbopt_call (the ts.ah_libd_hnd) fd_aux SO_REUSEADDR true;
      fd, fd_aux
  | ST_LISTEN ->
      let fd, fd_aux1 = dv ST_CLOSED in
      make_bind_call (the ts.th_libd_hnd) fd (Some (mk_ip t_ip),
                                              Some (mk_port t_port));
      make_listen_call (the ts.th_libd_hnd) fd 1;
      fd, fd_aux1
  | ST_ESTABLISHED(NO_DATA) ->
      let fd, fd_aux1 = dv ST_CLOSED in
      make_bind_call (the ts.ah_libd_hnd) fd_aux1 (Some (mk_ip a_ip),
                                                   Some (mk_port a_port));
      make_listen_call (the ts.ah_libd_hnd) fd_aux1 1;
      make_bind_call (the ts.th_libd_hnd) fd (Some (mk_ip t_ip),
                                              Some (mk_port t_port));
      make_connect_call (the ts.th_libd_hnd) fd (mk_ip a_ip,
                                                 Some (mk_port a_port));
      let fd_aux2 = accept_connection (the ts.ah_libd_hnd) fd_aux1 in
      make_close_call (the ts.ah_libd_hnd) fd_aux1;
      fd, fd_aux2
  | ST_ESTABLISHED(DATA_SENT) ->
      let fd, fd_aux2 = dv (ST_ESTABLISHED NO_DATA) in
      send_some_data id ts fd fd_aux2;
      fd, fd_aux2
  | ST_ESTABLISHED(DATA_RCVD) ->
      let fd, fd_aux2 = dv (ST_ESTABLISHED NO_DATA) in
      recv_some_data id ts fd fd_aux2;
      fd, fd_aux2
  | ST_ESTABLISHED(DATA_SENT_RCVD) ->
      let fd, fd_aux2 = dv (ST_ESTABLISHED DATA_SENT) in
      recv_some_data id ts fd fd_aux2;
      fd, fd_aux2
  | ST_CLOSE_WAIT(d) ->
      let fd, fd_aux2 = dv (ST_ESTABLISHED d) in
      (* have the slurper watch for the FIN *)
      let lock, cond = Mutex.create (), Condition.create () in
      let callback, fin = make_fin_callback lock cond a_ip t_ip a_port t_port in
      let callback_hnd =
               slurper_register_callback (the ts.th_slurper_hnd) callback in
      make_shutdown_call (the ts.ah_libd_hnd) fd_aux2 (false, true);
      (* now wait until the test host sees the FIN *)
      Mutex.lock lock;
      while !fin = None do Condition.wait cond lock; done;
      Mutex.unlock lock;
      slurper_deregister_callback (the ts.th_slurper_hnd) callback_hnd;
      fd, fd_aux2
  | ST_FIN_WAIT_2(d) ->
      let fd, fd_aux2 = dv (ST_ESTABLISHED d) in
      (* have the slurper on the aux host watch for the FIN *)
      let lock, cond = Mutex.create (), Condition.create () in
      let fcallback, fin = make_fin_callback lock cond
                                                t_ip a_ip t_port a_port in
      let fcallback_hnd =
                slurper_register_callback (the ts.ah_slurper_hnd) fcallback in
      (* and have the slurper on the test host watch for that FIN's ACK *)
      let acallback, ack = make_ack_callback lock cond
                                                a_ip t_ip a_port t_port in
      let acallback_hnd =
                slurper_register_callback (the ts.th_slurper_hnd) acallback in
      make_shutdown_call (the ts.th_libd_hnd) fd (false, true);
      (* now wait until we see that the FIN has been ACKed *)
      Mutex.lock lock;
      let is_acked () =
        match !fin, !ack with
          Some f, Some a -> a >= f
        | _ -> false in
      while (not (is_acked ())) do Condition.wait cond lock; done;
      Mutex.unlock lock;
      slurper_deregister_callback (the ts.ah_slurper_hnd) fcallback_hnd;
      slurper_deregister_callback (the ts.th_slurper_hnd) acallback_hnd;
      fd, fd_aux2
  | ST_TIME_WAIT(d) ->
      let fd, fd_aux2 = dv (ST_FIN_WAIT_2 d) in
      (* have the slurper watch for the FIN *)
      let lock, cond = Mutex.create (), Condition.create () in
      let callback, fin = make_fin_callback lock cond a_ip t_ip a_port t_port in
      let callback_hnd =
               slurper_register_callback (the ts.th_slurper_hnd) callback in
      make_shutdown_call (the ts.ah_libd_hnd) fd_aux2 (false, true);
      (* now wait until the test host sees the FIN *)
      Mutex.lock lock;
      while !fin = None do Condition.wait cond lock; done;
      Mutex.unlock lock;
      slurper_deregister_callback (the ts.th_slurper_hnd) callback_hnd;
      fd, fd_aux2
  | _ -> raise (Drive_Failure "don't know how to drive to some state")
  in dv state;;

let drive_test = function st -> (
  (function id-> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    destroy_sockets id ts fd fd_aux),
  "network: test the code to get a socket in state " ^ (string_of_st st),
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests = List.map drive_test all_achievable_network_states
let exhaustive_tests = []

(* ---------------------------------------------------------------------- *)

let test1 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test2 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.th_libd_hnd) fd "data";
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a string on the test host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test3 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.th_libd_hnd) fd "data";
    make_recv_call (the ts.ah_libd_hnd) fd_aux 4;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a string on the test host; receive the whole string on the auxiliary host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test4 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.th_libd_hnd) fd "blah";
    make_recv_call (the ts.ah_libd_hnd) fd_aux 2;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a string on the test host; receive part of the string on the auxiliary host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test5 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.ah_libd_hnd) fd_aux "woof";
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a string on the auxiliary host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test6 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.ah_libd_hnd) fd_aux "meow";
    make_recv_call (the ts.th_libd_hnd) fd 4;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a string on the auxiliary host; receive the whole string on the test host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test7 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.ah_libd_hnd) fd_aux "boom";
    make_recv_call (the ts.ah_libd_hnd) fd 2;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a string on the auxiliary host; receive part of the string on the test host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test8 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.ah_libd_hnd) fd_aux "eeek";
    make_recv_call (the ts.th_libd_hnd) fd 2;
    make_recv_call (the ts.th_libd_hnd) fd 2;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a string on the auxiliary host; receive part of the string on the test host; receive the remainder of the string on the test host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test9 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.th_libd_hnd) fd "cats";
    make_recv_call (the ts.ah_libd_hnd) fd_aux 4;
    make_send_call (the ts.ah_libd_hnd) fd_aux "dogs";
    make_recv_call (the ts.th_libd_hnd) fd 4;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a string on the test host; receive the string on the auxiliary host; send a string on the auxiliary host; receive the string on the test host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test10 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.ah_libd_hnd) fd_aux "sock";
    make_recv_call (the ts.th_libd_hnd) fd 4;
    make_send_call (the ts.th_libd_hnd) fd "whap";
    make_recv_call (the ts.ah_libd_hnd) fd_aux 4;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a string on the auxiliary host; receive the string on the test host; send a string on the test host; receive the string on the auxiliary host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test11 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.th_libd_hnd) fd "pink";
    make_send_call (the ts.th_libd_hnd) fd "blue";
    make_recv_call (the ts.ah_libd_hnd) fd_aux 8;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send two strings on the test host in succession; receive something on the auxiliary host (might be one or both strings)",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test12 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.th_libd_hnd) fd "warm";
    make_send_call (the ts.ah_libd_hnd) fd_aux "cool";
    make_recv_call (the ts.th_libd_hnd) fd 4;
    make_recv_call (the ts.ah_libd_hnd) fd_aux 4;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a string on the test host and the auxiliary host in succession; receive a string on each host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test13 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.th_libd_hnd) fd very_long_string;
    make_recv_call (the ts.ah_libd_hnd) fd_aux 4;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a very large string on the auxiliary host; receive a small part of it on the test host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test14 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.th_libd_hnd) fd very_long_string;
    make_recv_call (the ts.ah_libd_hnd) fd_aux 2000;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; send a very large string on the auxiliary host; try to receive all of it on the test host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test15 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    let _ = Thread.create (function () ->
      make_recv_call (the ts.th_libd_hnd) fd 4) () in
    delay 5.0;
    make_send_call (the ts.ah_libd_hnd) fd_aux "plip";
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; have the test host make a blocking call to recv(); send a string on the auxiliary host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let test16 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    let _ = Thread.create (function () ->
       make_recv_call (the ts.ah_libd_hnd) fd_aux 4) () in
    delay 5.0;
    make_send_call (the ts.th_libd_hnd) fd "plop";
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; have the auxiliary host make a blocking call to recv(); send a string on the test host",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests = normal_tests @ [test1; test2; test3; test4; test5; test6;
                    test7; test8; test9; test10; test11; test12; test13; test14;
                    test15; test16]
let exhaustive_tests = exhaustive_tests @ []

(* ---------------------------------------------------------------------- *)

let close_test1 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    teardown_connection id ts fd fd_aux;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; close both sockets, test host first",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let close_test2 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    teardown_connection_aux_first id ts fd fd_aux;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; close both sockets, auxiliary host first",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let close_test3 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.th_libd_hnd) fd "gosh";
    teardown_connection id ts fd fd_aux;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; test host sends data; close both sockets, test host first",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let close_test4 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.th_libd_hnd) fd "gosh";
    teardown_connection_aux_first id ts fd fd_aux;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; test host sends data; close both sockets, auxiliary host first",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let close_test5 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.ah_libd_hnd) fd_aux "whoa";
    teardown_connection id ts fd fd_aux;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; auxiliary host sends data; close both sockets, test host first",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let close_test6 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.ah_libd_hnd) fd_aux "whoa";
    teardown_connection_aux_first id ts fd fd_aux;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; auxiliary host sends data; close both sockets, auxiliary host first",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let close_test7 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.ah_libd_hnd) fd_aux "sock";
    make_send_call (the ts.th_libd_hnd) fd "shoe";
    teardown_connection id ts fd fd_aux;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; both hosts send data; close both sockets",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let close_test8 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    make_send_call (the ts.ah_libd_hnd) fd_aux "show";
    make_send_call (the ts.th_libd_hnd) fd "tell";
    teardown_connection_aux_first id ts fd fd_aux;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; both hosts send data; close both sockets, auxiliary host first",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let close_test9 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    let t = Thread.create (function () ->
      make_recv_call (the ts.ah_libd_hnd) fd_aux 4) () in
    delay 5.0;
    make_close_call (the ts.th_libd_hnd) fd;
    Thread.join t;
    make_close_call (the ts.ah_libd_hnd) fd_aux),
  "network: establish a connection; have the auxiliary host make a blocking call to recv(); close both sockets, test host first",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let close_test10 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    let t = Thread.create (function () ->
      make_recv_call (the ts.th_libd_hnd) fd 4) () in
    delay 5.0;
    teardown_connection_aux_first id ts fd fd_aux),
  "network: establish a connection; have the test host make a blocking call to recv(); close both sockets, auxiliary host first",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests = normal_tests @ [close_test1; close_test2; close_test3;
                   close_test4; close_test5; close_test6; close_test7;
                   close_test8; close_test9; close_test10]

(* ---------------------------------------------------------------------- *)

let bind_test1 = (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    let bind_call = (tid_of_int_private 0,
		     BIND(fd, Some(mk_ip id.test_host.test_ip_address),
			   Some(mk_port id.test_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) bind_call);
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; try to bind one of the connected sockets",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests = normal_tests @ [bind_test1]

(* ---------------------------------------------------------------------- *)

let shutdown_test = function (r,w,desc) -> (
  (function id -> function ts ->
    let fd, fd_aux = establish_connection id ts in
    send_some_data id ts fd fd_aux;
    recv_some_data id ts fd fd_aux;
    make_shutdown_call (the ts.th_libd_hnd) fd (false, true);
    make_send_call (the ts.th_libd_hnd) fd "asdf";
    recv_some_data id ts fd fd_aux;
    destroy_sockets id ts fd fd_aux),
  "network: establish a connection; shut down test host socket for " ^ desc ^ "; try to send and receive more data",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests = normal_tests @ [shutdown_test (true, false,"reading");
                                   shutdown_test (false, true, "writing");
                         shutdown_test (true, true, "reading and writing")]

(* ---------------------------------------------------------------------- *)

let listen_test1 = function (r,w,desc) -> (
  (function id -> function ts ->
    let fd_lis = get_socket (the ts.th_libd_hnd) in
    let portnum = get_next_port_for_host id.test_host in
    make_bind_call (the ts.th_libd_hnd) fd_lis (Some (mk_ip id.test_host.test_ip_address), Some (mk_port portnum));
    make_shutdown_call (the ts.th_libd_hnd) fd_lis (false, true);
    make_listen_call (the ts.th_libd_hnd) fd_lis 1;
    make_names_calls (the ts.th_libd_hnd) fd_lis;
    let fd_aux = get_socket (the ts.ah_libd_hnd) in
    make_connect_call (the ts.ah_libd_hnd) fd_aux (mk_ip id.test_host.test_ip_address, Some (mk_port portnum));
    let accept_call = (tid_of_int_private 0, ACCEPT(fd_lis)) in
    let libret = libd_call (the ts.th_libd_hnd) accept_call in
    match libret with
	    (_, OK_FD_IP_PORT(fd,_)) -> make_close_call (the ts.th_libd_hnd) fd
      | _ -> ();
    destroy_sockets id ts fd_lis fd_aux), (* should DTRT *)
  "network: bind a socket, then shut it down for " ^ desc ^ " before calling listen() and then attempting to connect to it",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let listen_test2 = function backlog -> (
  (function id -> function ts ->
    let fd_lis = get_socket (the ts.th_libd_hnd) in
    let portnum = get_next_port_for_host id.test_host in
    make_bind_call (the ts.th_libd_hnd) fd_lis (Some (mk_ip id.test_host.test_ip_address), Some (mk_port portnum));
    make_listen_call (the ts.th_libd_hnd) fd_lis backlog;
    (* now make ten sockets on aux host and have them all try to connect *)
    let fdlist =
      let rec makesocks n =
        if n = 0 then []
        else (get_socket (the ts.ah_libd_hnd)) :: (makesocks (n - 1))
      in makesocks (backlog + 2)
    in
    List.iter (function s -> make_setfileflags_call (the ts.ah_libd_hnd) s [O_NONBLOCK]) fdlist;
    List.iter (function s -> make_connect_call (the ts.ah_libd_hnd) s (mk_ip id.test_host.test_ip_address, Some (mk_port portnum))) fdlist;
    delay 1.0;
    List.iter (function s -> destroy_socket (the ts.ah_libd_hnd) s) fdlist;
    destroy_socket (the ts.th_libd_hnd) fd_lis),
  "network: make a listening socket with a backlog of " ^ (string_of_int backlog) ^ " and attempt to connect to it " ^ (string_of_int (backlog+2))^ " times",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let listen_test3 = function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    make_listen_call (the ts.th_libd_hnd) fd 1;
    make_names_calls (the ts.th_libd_hnd) fd;
    destroy_sockets id ts fd fd_aux),
  "network: for a socket in state " ^ (string_of_st st) ^ ", call listen() followed by getsockname() and getpeername()",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests = normal_tests @ [listen_test1 (true, false,"reading");
                                   listen_test1 (false, true, "writing");
                           listen_test1 (true, true, "reading and writing")]
                  @ (List.map listen_test2 [1;2;3;5;0])
                  @ (List.map listen_test3 all_interesting_network_states)

(* ---------------------------------------------------------------------- *)

let deliver_test1 = function (listening, waiting) -> (
  (function id -> function ts ->
    (* note that as we're not using drive_connection_to_state, SO_REUSEADDR
       will *not* be set (which is what we want) --amgb *)
    let srcip = mk_ip id.test_host.test_ip_address in
    let srcport = mk_port id.test_host.test_ephm_port in
    let dstip = mk_ip id.aux_host.test_ip_address in
    let dstport = mk_port (get_next_port_for_host id.aux_host) in
    let fd = get_socket (the ts.th_libd_hnd) in
    make_bind_call (the ts.th_libd_hnd) fd (Some srcip, Some srcport);
    let fd_lis = get_socket (the ts.ah_libd_hnd) in
    make_bind_call (the ts.ah_libd_hnd) fd_lis (Some dstip, Some dstport);
    make_listen_call (the ts.ah_libd_hnd) fd_lis 1;
    make_connect_call (the ts.th_libd_hnd) fd (dstip, Some dstport);
    let accept_call = (tid_of_int_private 0, ACCEPT(fd_lis)) in
    let libret = libd_call (the ts.ah_libd_hnd) accept_call in
    let fd_aux = match libret with
      (_, OK_FD_IP_PORT(fd,_)) -> fd
      | _ -> raise (Drive_Failure "accept() failed") in
    make_close_call (the ts.th_libd_hnd) fd;
    make_close_call (the ts.ah_libd_hnd) fd_lis;
    make_close_call (the ts.ah_libd_hnd) fd_aux;
    delay (if waiting then 125.0 else 0.0);
    let fd_new = get_socket (the ts.th_libd_hnd) in
    make_bind_call (the ts.th_libd_hnd) fd_new (Some srcip, Some srcport);
    let fd_new_lis = if listening then
      let fd = get_socket (the ts.ah_libd_hnd) in
      make_bind_call (the ts.ah_libd_hnd) fd (Some dstip, Some dstport);
      make_listen_call (the ts.ah_libd_hnd) fd 1;
      Some fd
    else
      None in
    make_connect_call (the ts.th_libd_hnd) fd_new (dstip, Some dstport);
    destroy_socket (the ts.th_libd_hnd) fd_new;
    if listening then
      destroy_socket (the ts.ah_libd_hnd) (the fd_new_lis)
    else
      ()),
  (let wait_str = if waiting then "wait two minutes and " else "" in
  let lis_str = if listening then "with" else "without" in
  "network: establish and destroy a connection from the test host to the auxiliary host, then " ^ wait_str ^ "try to establish the same connection again " ^ lis_str ^ " an appropriate listening socket in place"),
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let deliver_test2 = function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    destroy_socket (the ts.ah_libd_hnd) fd_aux;
    make_names_calls (the ts.th_libd_hnd) fd;
    destroy_socket (the ts.th_libd_hnd) fd),
  "network: for a socket in state " ^ (string_of_st st) ^ ", attempt to deliver a RST by performing an abortive close on the auxiliary host, then call getsockname() and getpeername() on the socket",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests = normal_tests @ List.map deliver_test1 [(false, false);
                              (false, true); (true, false); (true, true)]
                    @ List.map deliver_test2 all_interesting_network_states

(* ---------------------------------------------------------------------- *)

let disconnect_test = function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    make_disconnect_call (the ts.th_libd_hnd) fd;
    destroy_sockets id ts fd fd_aux),
  "network: for a socket in state " ^ (string_of_st st) ^ ", call disconnect()",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests = normal_tests @
                 List.map disconnect_test all_interesting_network_states

(* ---------------------------------------------------------------------- *)

let accept_test = function blocking -> function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    (if blocking then () else
      make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK]);
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore (libd_call (the ts.th_libd_hnd) accept_call);
    destroy_sockets id ts fd fd_aux),
  (let block_str = if blocking then "blocking" else "non-blocking" in
  "network: for a " ^ block_str ^ " socket in state " ^ (string_of_st st) ^ ", call accept()"),
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests =
let non_listen_states = List.filter (function x -> x <> ST_LISTEN)
                                        all_interesting_network_states in
    normal_tests  @ List.map (accept_test  true) non_listen_states
                  @ List.map (accept_test false) non_listen_states

(* ---------------------------------------------------------------------- *)

let getnames_test = function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    make_names_calls (the ts.th_libd_hnd) fd;
    destroy_sockets id ts fd fd_aux),
  "network: for a socket in state " ^ (string_of_st st) ^ ", call getsockname() and getpeername()",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests = normal_tests
                   @ List.map getnames_test all_interesting_network_states

(* ---------------------------------------------------------------------- *)

let pselect_test1 = function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    let fd_bad = fd_of_int_private 751 in
    make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK];
    let fds = [fd; fd_bad] in
    make_pselect_call (the ts.th_libd_hnd) (fds, fds, fds) (Some(3,0)) None;
    destroy_sockets id ts fd fd_aux),
  "network: for a non-blocking socket in state " ^ (string_of_st st) ^ ", call pselect() on that socket's fd and another, bad fd",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let pselect_test2 = function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK];
    make_pselect_call (the ts.th_libd_hnd) ([fd], [fd], [fd]) (Some(-1,0)) None;
    destroy_sockets id ts fd fd_aux),
  "network: for a non-blocking socket in state " ^ (string_of_st st) ^ ", call pselect() on that socket's fd with a negative timeout",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let pselect_test3 = function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    let t = Thread.create (function () ->
      delay 5.0;
      make_send_call (the ts.ah_libd_hnd) fd_aux "wake up!") ()
    in
    make_pselect_call (the ts.th_libd_hnd) ([fd], [], []) (Some(30,0)) None;
    Thread.join t;
    destroy_sockets id ts fd fd_aux),
  "network: for a socket in state " ^ (string_of_st st) ^ ", call pselect() on that socket's fd, then send data to the socket",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let pselect_test4 = function blocking -> function mkargs, psd ->
                                         function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    (if blocking then () else
       make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK]);
    make_pselect_call (the ts.th_libd_hnd) (mkargs fd) (Some(3,0)) None;
    destroy_sockets id ts fd fd_aux),
  (let bdesc = if blocking then "blocking" else "non-blocking" in
  "network: for a " ^ bdesc ^ " socket in state " ^ (string_of_st st) ^ ", call pselect() on that socket's fd for " ^ psd),
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let pselect_test4_modes =
  [(function x -> ([x],[],[])), "reading only";
   (function x -> ([],[x],[])), "writing only";
   (function x -> ([],[],[x])), "errors only";
   (function x -> ([x],[x],[])), "reading, writing and errors"]

let pselect_test5 = function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    make_shutdown_call (the ts.th_libd_hnd) fd (true, true);
    make_pselect_call (the ts.th_libd_hnd) ([fd],[fd],[fd]) (Some(3,0)) None;
    destroy_sockets id ts fd fd_aux),
  "network: for a socket in state " ^ (string_of_st st) ^ ", call shutdown(true, true) followed by pselect()",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests =
  let receptive_states = List.filter (function s ->
                          match s with ST_ESTABLISHED(_) -> true
                                     | ST_FIN_WAIT_2(_) -> true | _ -> false)
                         all_interesting_network_states in
  normal_tests @ List.map pselect_test1 all_interesting_network_states
               @ List.map pselect_test2 all_interesting_network_states
               @ List.map pselect_test3 receptive_states
               @ List.flatten (List.map (function x ->
                              List.map x all_interesting_network_states)
                     (List.map (pselect_test4 true) pselect_test4_modes))
               @ List.flatten (List.map (function x ->
                              List.map x all_interesting_network_states)
                     (List.map (pselect_test4 false) pselect_test4_modes))
               @ List.map pselect_test5 all_interesting_network_states

(* ---------------------------------------------------------------------- *)

let getsocklistening_test = function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    make_getsocklistening_call (the ts.th_libd_hnd) fd;
    destroy_sockets id ts fd fd_aux),
  "network: for a socket in state " ^ (string_of_st st) ^ ", call getsocklistening()",
  ((true,false),true,true,false),
  ((true,false),true,true,false))

let normal_tests = normal_tests @ List.map getsocklistening_test
                                               all_interesting_network_states

(* ---------------------------------------------------------------------- *)

type locality = LocalLoop | Local | NonLocal

let connect_test = function (is_nonblocking, is_listening, locality) ->
                   function st -> (
  (function id -> function ts ->
  (* the slurper started by default doesn't slurp on the loopback interface,
     so we need to manually start one that does here *)
  let slurper_log =
    if locality <> NonLocal && id.test_host.platform_type <> ARCH_WINXP
    then
      let log = create_fresh_log (string_ip id.tthee_host) in
      let _ = merger_register_log ts.th_merge_hnd log None in
      Some log
    else
      None
  in let (slurp_filter, slurp_hostip, slurp_iface) =
    match locality with
      LocalLoop ->
        (Some("tcp"), Some(hol_ip (127,0,0,1)), id.test_host.loopback_name)
    | Local ->
        (Some("tcp"), Some(hol_ip id.test_host.test_ip_address),
                                                id.test_host.loopback_name)
    | NonLocal ->
        (None, None, "")
  in let slurper_hnd =
    if locality <> NonLocal && id.test_host.platform_type <> ARCH_WINXP then
      Some(slurper_create id.test_host.ns_tools_exec_params (the slurper_log)
                                        slurp_iface slurp_filter slurp_hostip)
    else
      None
  in delay 5.0;
  (* slurper started *)
  let fd, fd_aux = drive_connection_to_state id ts st in
  (if is_nonblocking then
    (make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK])
  else
    ());
  let (rem_is_local, rem_libd_hnd, rem_ip_address, rem_ephm_port) =
    match locality with
      LocalLoop -> (true, ts.th_libd_hnd, mk_ip (127,0,0,1),
                                          mk_port id.test_host.test_ephm_port)
    | Local ->     (true, ts.th_libd_hnd, mk_ip id.test_host.test_ip_address,
                                          mk_port id.test_host.test_ephm_port)
    | NonLocal -> (false, ts.ah_libd_hnd, mk_ip id.aux_host.test_ip_address,
                                          mk_port id.aux_host.test_ephm_port) in
  (* create new listening socket if necessary *)
  let fd2opt = if is_listening then
    let fd2 = get_local_bound_socket
             (the rem_libd_hnd) (Some rem_ip_address) (Some rem_ephm_port) in
    make_listen_call (the rem_libd_hnd) fd2 1;
    Some fd2
  else
    None
  in
  (* now actually do the test *)
  make_connect_call (the ts.th_libd_hnd) fd (rem_ip_address,Some rem_ephm_port);
  (* now tidy up *)
  destroy_sockets id ts fd fd_aux;
  lift (destroy_socket (the rem_libd_hnd)) fd2opt;
  ignore (lift slurper_destroy slurper_hnd);
  ignore (lift destroy_log slurper_log)),
  (let blockstr = if is_nonblocking then "non-blocking" else "blocking" in
  let localstr = match locality with
      LocalLoop -> "local loopback"
    | Local ->     "local"
    | NonLocal ->  "non-local" in
  let listenstr = if is_listening then "listening" else "non-listening" in
  "network: for a " ^ blockstr ^ " socket in the " ^ (string_of_st st) ^ " state, attempt to connect to a " ^ localstr ^ ", " ^ listenstr ^ " socket"),
  ((true, true), true, true, false),
  ((true, false), true, true, false))

let connect_test_modes =
  [ (false, false, LocalLoop);  (false, true, LocalLoop);
    (true, false, LocalLoop);   (true, true, LocalLoop);
    (false, false, Local);      (false, true, Local);
    (true, false, Local);       (true, true, Local);
    (false, false, NonLocal);   (false, true, NonLocal);
    (true, false, NonLocal);    (true, true, NonLocal) ]

let normal_tests = normal_tests
    @ List.flatten (List.map
                (function x -> List.map x all_interesting_network_states)
                (List.map connect_test connect_test_modes))

(* ---------------------------------------------------------------------- *)

let linger_states = [ (None,       "no linger");
                      (Some(0, 0), "zero linger");
                      (Some(2, 2), "non-zero linger") ]

let close_test11 = function blocking -> function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    make_close_call (the ts.th_libd_hnd) fd;
    destroy_socket (the ts.ah_libd_hnd) fd_aux),
  ("network: for a " ^ (if blocking then "blocking" else "non-blocking") ^
   " socket in state " ^ (string_of_st st) ^ ", call close()"),
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let close_test12 = function blocking -> function st ->
                                        function linger, ldesc -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    (if (not blocking) then
      (make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK])
    else
      ());
    make_setsocktopt_call (the ts.th_libd_hnd) fd SO_LINGER linger;
    make_close_call (the ts.th_libd_hnd) fd;
    destroy_socket (the ts.ah_libd_hnd) fd_aux),
  ("network: for a " ^ (if blocking then "blocking" else "non-blocking") ^
   " socket in state " ^ (string_of_st st) ^ " and with " ^ ldesc ^
   ", call close()"),
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let close_test13 = function blocking -> (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    make_bind_call (the ts.th_libd_hnd) fd
                            (Some (mk_ip id.test_host.test_ip_address),
                             Some (mk_port id.test_host.test_ephm_port));
    make_listen_call (the ts.th_libd_hnd) fd 1;
    (if (not blocking) then
      (make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK])
    else
      ());
    make_close_call (the ts.th_libd_hnd) fd),
  ("network: for a " ^ (if blocking then "blocking" else "non-blocking") ^
   " socket in state LISTEN and with no connections waiting, call close()"),
  ((true, false), true, true, false),
  ((false, false), false, false, false))

let close_test14 = function blocking -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts ST_LISTEN in
    let t = Thread.create (function () ->
                        make_connect_call (the ts.ah_libd_hnd) fd_aux
                        (mk_ip id.test_host.test_ip_address,
                        Some(mk_port id.test_host.test_ephm_port))) () in
    delay 3.0;
    make_close_call (the ts.th_libd_hnd) fd;
    Thread.join t;
    destroy_socket (the ts.ah_libd_hnd) fd_aux),
  ("network: for a " ^ (if blocking then "blocking" else "non-blocking") ^
   " socket in state LISTEN and with a connection on the accept queue, call close()"),
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let close_test15 = function blocking -> function corig, cdup, cdesc -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts
                                      (ST_ESTABLISHED DATA_SENT_RCVD) in
    (if (not blocking) then
      make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK]
    else
      ());
    let fd_dup = dup_fd (the ts.th_libd_hnd) fd in
    (if cdup then make_close_call (the ts.th_libd_hnd) fd_dup else ());
    (if corig then make_close_call (the ts.th_libd_hnd) fd else ());
    destroy_socket (the ts.ah_libd_hnd) fd_aux),
  ("network: for a " ^ (if blocking then "blocking" else "non-blocking") ^
   " socket in state ESTABLISHED(data sent/rcvd), duplicate the file descriptor and then close " ^ cdesc),
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let close_test15_modes = [ (true, false, "the original descriptor");
                           (false, true, "the duplicate");
                           (true, true, "both descriptors") ]

let close_test12a = close_test12 true  (ST_ESTABLISHED DATA_SENT_RCVD)
let close_test12b = close_test12 false (ST_ESTABLISHED DATA_SENT_RCVD)
let close_test12c = close_test12 true  (ST_CLOSE_WAIT DATA_SENT_RCVD)
let close_test12d = close_test12 false (ST_CLOSE_WAIT DATA_SENT_RCVD)

let normal_tests = normal_tests
           @ List.map (close_test11 true) all_interesting_network_states
           @ List.map (close_test11 false) all_interesting_network_states
           @ List.map close_test12a linger_states
           @ List.map close_test12b linger_states
           @ List.map close_test12c linger_states
           @ List.map close_test12d linger_states
           @ List.map (close_test15 true) close_test15_modes
           @ List.map (close_test15 false) close_test15_modes
           @ [close_test13 true; close_test13 false; close_test14 true;
              close_test14 false]

(* ---------------------------------------------------------------------- *)

let dup_test1 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    let fd_dup = dup_fd (the ts.th_libd_hnd) fd in
    make_send_call (the ts.th_libd_hnd) fd "tweedledum";
    make_send_call (the ts.th_libd_hnd) fd_dup "tweedledee";
    make_recv_call (the ts.ah_libd_hnd) fd_aux 10;
    make_recv_call (the ts.ah_libd_hnd) fd_aux 10;
    destroy_socket (the ts.ah_libd_hnd) fd_aux;
    make_close_call (the ts.th_libd_hnd) fd;
    make_close_call (the ts.th_libd_hnd) fd_dup),
  "network: duplicate a file descriptor of an established connection, then send data on both descriptors",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let dup_test2 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    let fd_dup = dup_fd (the ts.th_libd_hnd) fd in
    make_close_call (the ts.th_libd_hnd) fd;
    make_send_call (the ts.th_libd_hnd) fd_dup "cabbages";
    make_recv_call (the ts.ah_libd_hnd) fd_aux 8;
    destroy_socket (the ts.ah_libd_hnd) fd_aux;
    make_close_call (the ts.th_libd_hnd) fd_dup),
  "network: duplicate a file descriptor of an established connection, then close the original descriptor and send data on the duplicate",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let normal_tests = normal_tests @ [dup_test1; dup_test2]

(* ---------------------------------------------------------------------- *)

let send_test1 = function block, zero -> function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    (if (not block) then
      (make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK])
    else
      ());
    let data_to_send = (if zero then "" else "here is the data!") in
    make_send_call (the ts.th_libd_hnd) fd data_to_send;
    destroy_sockets id ts fd fd_aux),
  ("network: for a " ^ (if block then "blocking" else "non-blocking") ^
   " socket in state " ^ (string_of_st st) ^ ", send " ^ (if zero then "no"
   else "some") ^ " bytes of data"),
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let send_test2 = function flags, flagsd -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_send_call_with_flags (the ts.th_libd_hnd) fd "hello!" flags;
    destroy_sockets id ts fd fd_aux),
  "network: for a blocking socket in state ESTABLISHED(no data), send some data with " ^ flagsd ^ " set",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let send_test3 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_shutdown_call (the ts.th_libd_hnd) fd (false, true);
    make_send_call (the ts.th_libd_hnd) fd "some data!";
    destroy_sockets id ts fd fd_aux),
  "network: for a blocking socket in state ESTABLISHED(no data), shut down for writing and then attempt to send more data",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let send_test4 = function str -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK];
    make_setsocknopt_call (the ts.th_libd_hnd) fd SO_SNDLOWAT 5;
    make_send_call (the ts.th_libd_hnd) fd str;
    destroy_sockets id ts fd fd_aux),
  ("network: for a non-blocking socket in state ESTABLISHED(no data), set SO_SNDLOWAT to 5 and then attempt to send " ^ (string_of_int (String.length str)) ^ " bytes of data"),
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let send_test5 = function zero -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts
                                              (ST_FIN_WAIT_2 DATA_SENT_RCVD) in
    make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK];
    make_shutdown_call (the ts.th_libd_hnd) fd (true, false);
    let data_to_send = if zero then "" else "data?" in
    make_send_call (the ts.th_libd_hnd) fd data_to_send;
    destroy_sockets id ts fd fd_aux),
  "network: for a non-blocking socket in state FIN_WAIT_2(data sent/rcvd), shutdown the connection for reading and then attempt to send() " ^ (if zero then "no" else "some") ^ " data",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let send_test6 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    destroy_socket (the ts.ah_libd_hnd) fd_aux;
    make_send_call (the ts.th_libd_hnd) fd "hello?";
    make_close_call (the ts.th_libd_hnd) fd),
  "network: for a blocking socket in state ESTABLISHED(no data), perform an abortive close on the other end of the connection and then attempt to send data",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let send_test7 = function blocking -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_setsocknopt_call (the ts.th_libd_hnd) fd SO_SNDBUF 3;
    (if (not blocking) then
      (make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK])
    else
      ());
    make_send_call (the ts.th_libd_hnd) fd "here is a moderately long string";
    destroy_sockets id ts fd fd_aux),
  (let blockstr = if blocking then "blocking" else "non-blocking" in
  "network: for a " ^ blockstr ^ " socket in state ESTABLISHED(no data), reduce the send buffer size to 3 and then send a long string"),
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let test1_states = all_interesting_network_states @ [ST_ESTABLISHED NO_DATA]

let normal_tests = normal_tests
  @ List.map (send_test1 (false,false)) test1_states
  @ List.map (send_test1 (false, true)) test1_states
  @ List.map (send_test1 (true, false)) test1_states
  @ List.map (send_test1 (true,  true)) test1_states
  @ [send_test2 ([MSG_PEEK], "MSG_PEEK");
     send_test2 ([MSG_WAITALL], "MSG_WAITALL");
     send_test2 ([MSG_DONTWAIT], "MSG_DONTWAIT"); send_test3; send_test5 true;
     send_test5 false; send_test6; send_test7 true; send_test7 false]
  @ List.map send_test4 ["hi"; "hello"; "good afternoon"]

(* ---------------------------------------------------------------------- *)

let recv_test1 = function blocking -> function (data_on_q, want_data) ->
                                                           function st -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts st in
    (if (not blocking) then
      (make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK])
    else
      ());
    (if data_on_q then
      (make_send_call (the ts.ah_libd_hnd) fd_aux "data here!")
    else
      ());
    let recv_arg = if want_data then 10 else 0 in
    let _ = Thread.create (function () ->
         make_recv_call (the ts.th_libd_hnd) fd recv_arg) () in
    delay 3.0;
    (* abortive close the aux socket first, to unblock the recv() call
       if necessary *)
    destroy_socket (the ts.ah_libd_hnd) fd_aux;
    make_close_call (the ts.th_libd_hnd) fd),
  ("network: for a " ^ (if blocking then "blocking" else "non-blocking") ^
   " socket in state " ^ (string_of_st st) ^ " with " ^ (if data_on_q then "10"
   else "no ") ^ "bytes of data on the receive queue, call recv(" ^ (if
   want_data then "10" else "0") ^ ")"),
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let recv_test2 = function blocking -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_send_call (the ts.ah_libd_hnd) fd_aux "123456";
    (if (not blocking) then
      (make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK])
    else
      ());
    make_recv_call (the ts.th_libd_hnd) fd 100;
    destroy_sockets id ts fd fd_aux),
  ("network: for a " ^ (if blocking then "blocking" else "non-blocking") ^
   " socket in state ESTABLISHED(no data), try to recv() more bytes of data than are available on the receive queue"),
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let recv_test3 = function data_on_q, recv_too_much -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    (if data_on_q then
      (make_send_call (the ts.ah_libd_hnd) fd_aux "test msg")
    else
      ());
    make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK];
    let recv_arg = if recv_too_much then 20 else 4 in
    make_recv_call_with_flags (the ts.th_libd_hnd) fd recv_arg [MSG_PEEK];
    make_recv_call (the ts.th_libd_hnd) fd recv_arg;
    destroy_sockets id ts fd fd_aux),
  "network: for a non-blocking socket in state ESTABLISHED(no data) and with "
    ^ (if data_on_q then "8 " else "no ") ^ "bytes of data on the receive queue, call recv(" ^ (if recv_too_much then "20" else "4") ^ ") twice, first with and then without MSG_PEEK set",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let recv_test4 = function send_more -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_send_call (the ts.ah_libd_hnd) fd_aux "tra la la";
    let t = Thread.create (function () ->
        make_recv_call_with_flags (the ts.th_libd_hnd) fd 15
                                                  [MSG_PEEK; MSG_WAITALL]) () in
    delay 2.5;
    (if send_more then
      make_send_call (the ts.ah_libd_hnd) fd_aux "la la la laaaaa"
    else
      ());
    delay 2.5;
    destroy_socket (the ts.ah_libd_hnd) fd_aux;
    make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK];
    make_recv_call (the ts.th_libd_hnd) fd 15;
    make_close_call (the ts.th_libd_hnd) fd),
  "network: from state ESTABLISHED, make a blocking call to recv() with MSG_PEEK and MSG_WAITALL set requesting more data than is available on the receive queue, " ^ (if send_more then "then send enough data that the call can return, " else "") ^ "then perform an abortive close on the other end and then make a non-blocking call to recv with no flags",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let recv_test5 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_send_call (the ts.ah_libd_hnd) fd_aux "12345678";
    make_recv_call_with_flags (the ts.th_libd_hnd) fd 8 [MSG_WAITALL];
    make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK];
    make_recv_call (the ts.th_libd_hnd) fd 8;
    destroy_sockets id ts fd fd_aux),
  "network: from state ESTABLISHED, make a blocking call to recv() with MSG_WAITALL set requesting exactly as much data as is on the receive queue, then make another, non-blocking call to recv() with no flags",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let recv_test6 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_send_call (the ts.ah_libd_hnd) fd_aux "kapow";
    let t = Thread.create (function () ->
      make_recv_call_with_flags (the ts.th_libd_hnd) fd 10 [MSG_WAITALL]) () in
    delay 5.0;
    destroy_socket (the ts.ah_libd_hnd) fd_aux;
    make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK];
    make_recv_call (the ts.th_libd_hnd) fd 10;
    make_close_call (the ts.th_libd_hnd) fd),
  "network: from state ESTABLISHED, make a blocking call to recv() with MSG_WAITALL set requesting more data than is on the receive queue, then perform an abortive close on the other end and make another, non-blocking call to recv() with no flags",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let recv_test7 = function lowat -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK];
    make_setsocknopt_call (the ts.th_libd_hnd) fd SO_RCVLOWAT lowat;
    make_send_call (the ts.ah_libd_hnd) fd_aux "banananana";
    make_recv_call (the ts.th_libd_hnd) fd 10;
    destroy_sockets id ts fd fd_aux),
  "network: for a non-blocking socket in state ESTABLISHED(no data), set SO_RCVLOWAT to " ^ (string_of_int lowat) ^ ", then send 10 bytes of data to the socket and attempt to recv() them (NB: this test may not function on WinXP)",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let recv_test8 = function timeout, tdesc, send_data -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_setsocktopt_call (the ts.th_libd_hnd) fd SO_RCVTIMEO timeout;
    let t = Thread.create (function () ->
                              make_recv_call (the ts.th_libd_hnd) fd 5) () in
    delay 3.0;
    (if send_data then
      make_send_call (the ts.ah_libd_hnd) fd_aux "hello"
    else
      ());
    delay 6.0;
    destroy_socket (the ts.ah_libd_hnd) fd_aux;
    make_close_call (the ts.th_libd_hnd) fd),
  "network: for a socket in state ESTABLISHED(no data) with an empty receive queue, set SO_RCVTIMEO=" ^ tdesc ^ " and call recv()" ^ (if send_data then ", then send data to the socket before the timeout occurs" else "") ^ " (NB. this test may not function on WinXP)",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let recv_test9 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_setsocktopt_call (the ts.th_libd_hnd) fd SO_RCVTIMEO (Some (5,0));
    make_send_call (the ts.ah_libd_hnd) fd "wowzers";
    let t = Thread.create (function () ->
      make_recv_call_with_flags (the ts.th_libd_hnd) fd 10 [MSG_WAITALL]) () in
    delay 10.0;
    destroy_socket (the ts.ah_libd_hnd) fd_aux;
    make_close_call (the ts.th_libd_hnd) fd),
  "network: for a socket in state ESTABLISHED(no data), set SO_RCVTIMEO=6 and then make a blocking call to recv() with MSG_WAITALL set requesting more data than is on the receive queue (NB. this test may not function on WinXP)",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let recv_test10 = function blocking, data_on_q -> (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    (if data_on_q then
      make_send_call (the ts.ah_libd_hnd) fd_aux "polly wanna cracker?"
    else
      ());
    (if (not blocking) then
      make_setfileflags_call (the ts.th_libd_hnd) fd [O_NONBLOCK]
    else
      ());
    make_shutdown_call (the ts.th_libd_hnd) fd (true, false);
    make_recv_call (the ts.th_libd_hnd) fd 5;
    destroy_sockets id ts fd fd_aux),
  "network: for a " ^ (if blocking then "blocking" else "non-blocking") ^
  " socket in state ESTABLISHED(no data) and with " ^ (if data_on_q then "" else
  "no ") ^ "data on the receive queue, call shutdown(T,F) followed by recv()",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let recv_ok_states, recv_not_ok_states = List.partition
  (function s -> match s with
      ST_ESTABLISHED(_) -> true | ST_FIN_WAIT_1(_) -> true
    | ST_FIN_WAIT_2(_) -> true | ST_CLOSING(_) -> true | _ -> false)
  all_interesting_network_states

let normal_tests = normal_tests
  @ List.map (recv_test1 true (false, true)) recv_not_ok_states
  @ List.map (recv_test1 false (false, true)) recv_not_ok_states
  @ List.map (recv_test1 true (true, true)) recv_ok_states
  @ List.map (recv_test1 false (true, true)) recv_ok_states
  @ List.map (recv_test1 true (true, false)) recv_ok_states
  @ List.map (recv_test1 false (true, false)) recv_ok_states
  @ List.map (recv_test1 true (false, true)) recv_ok_states
  @ List.map (recv_test1 false (false, true)) recv_ok_states
  @ [recv_test2 false; recv_test2 true]
  @ List.map recv_test3 [(false, false); (true, false); (true, true)]
  @ [recv_test4 false; recv_test4 true; recv_test5; recv_test6]
  @ List.map recv_test7 [8; 10; 12]
  @ List.map recv_test8 [(None, "0", false); (Some (6,0), "6", false);
                                             (Some (6,0), "6", true)]
  @ [recv_test9]
  @ List.map recv_test10 [(false,false);(false,true);(true,false);(true,true)]

(* ---------------------------------------------------------------------- *)

let timer_test1 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_TIME_WAIT NO_DATA) in
    inter_test_delay 300.0;
    destroy_sockets id ts fd fd_aux),
  "network: put the connection in the TIME_WAIT state and wait for the 2MSL timeout to expire",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let timer_test2 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_send_call (the ts.ah_libd_hnd) fd_aux "incoming!";
    delay 5.0;
    destroy_sockets id ts fd fd_aux),
  "network: in state ESTABLISHED, receive incoming data and wait for a delayed ACK to be emitted",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let timer_test3 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_send_call (the ts.ah_libd_hnd) fd_aux "incoming!";
    make_send_call (the ts.th_libd_hnd) fd "run away!";
    delay 5.0;
    destroy_sockets id ts fd fd_aux),
  "network: in state ESTABLISHED, receive incoming data but call send() to emit data before the delayed ACK timer can fire",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let timer_test4 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_FIN_WAIT_2 NO_DATA) in
    inter_test_delay 900.0;
    destroy_sockets id ts fd fd_aux),
  "network: move to state FIN_WAIT_2 then wait for fifteen minutes to see if the FIN_WAIT_2 timer fires",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let timer_test5 = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_FIN_WAIT_2 NO_DATA) in
    inter_test_delay 180.0;
    make_send_call (the ts.ah_libd_hnd) fd_aux "still alive!";
    inter_test_delay 900.0;
    destroy_sockets id ts fd fd_aux),
  "network: move to state FIN_WAIT_2, wait for three minutes then receive more data, then wait for the FIN_WAIT_2 timer to fire",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let very_last_test = (
  (function id -> function ts ->
    let fd, fd_aux = drive_connection_to_state id ts (ST_ESTABLISHED NO_DATA) in
    make_setsockbopt_call (the ts.th_libd_hnd) fd SO_KEEPALIVE true;
    inter_test_delay 7250.0;
    destroy_sockets id ts fd fd_aux),
  "network: for an established connection, set SO_KEEPALIVE and then leave the connection idle for two hours",
  ((true, false), true, true, false),
  ((true, false), true, true, false))

let normal_tests = normal_tests @ [timer_test1; timer_test2; timer_test3;
                                   timer_test4; timer_test5; very_last_test]

(* ---------------------------------------------------------------------- *)

let do_network_tests handle hosts_list test_type =
  begin_next_test_group handle "network tests";
  let done_a_test = ref false in
  let num_of_tests = ref 0 in

  let tests = match test_type with
    TCP_NORMAL -> []
  | UDP_NORMAL -> []
  | ALL_NORMAL -> []
  | TCP_EXHAUSTIVE -> []
  | UDP_EXHAUSTIVE -> []
  | ALL_EXHAUSTIVE -> []
  | STREAM_NORMAL -> normal_tests
  | STREAM_EXHAUSTIVE -> exhaustive_tests in

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
		    !tthee_baseport_2 (* !merger_delta *) 4000000 in
		let _ =
		  try

print_string ("[" ^ test_fname); flush stdout;

 test_thunk id ts;
print_string "] "; flush stdout;
		  with e -> report_test_failure handle descr e
		in
		num_of_tests := !num_of_tests + 1;
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
