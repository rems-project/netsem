(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: connect()                           *)
(* Steve Bishop - Created 20030627                                        *)
(* $Id: connect.ml,v 1.46 2006/06/28 16:24:15 amgb2 Exp $ *)
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
open Common
open Dual
open Dualdriven
open Testscommon

(* ---------------------------------------------------------------------- *)

type locality = LocalLoop | Local | NonLocal

let test_1234 = function (is_nonblocking,is_listening,locality,diff_port) ->
                function (bq, bqdescr) -> (
  (function id -> function ts ->
    (* ------ *)
    (* Start the slurper -- need to do this here because of loopbacks *)
    (* ------ *)
    let slurper_log =
      if locality <> NonLocal && id.test_host.platform_type != ARCH_WINXP then
	let log = create_fresh_log (string_ip id.tthee_host) in
	let _ = merger_register_log ts.th_merge_hnd log None in
	Some(log)
      else
	None in
    let (slurp_filter, slurp_hostip, slurp_iface) =
      if locality = LocalLoop then
	(Some("tcp"), Some(hol_ip (127,0,0,1)), id.test_host.loopback_name)
      else if locality = Local then
	(Some("tcp"), Some(hol_ip id.test_host.test_ip_address), id.test_host.loopback_name)
      else
        (None, None, "")
    in
    let slurper_hnd =
      if locality <> NonLocal && id.test_host.platform_type != ARCH_WINXP then
	Some(slurper_create id.test_host.ns_tools_exec_params
	       (the slurper_log) slurp_iface slurp_filter slurp_hostip)
      else
	None
    in

    delay 10.00;
    (* ----- *)
    let fd = the(fst(get_bound_socket id ts bq)) in
    let nonblock_call = (tid_of_int_private 0,
			 SETFILEFLAGS(fd,if is_nonblocking then [O_NONBLOCK] else [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let (rem_is_local,rem_libd_hnd,rem_ip_address,rem_ephm_port) =
      match locality with
         LocalLoop -> (true,
                       ts.th_libd_hnd,
                         mk_ip (127,0,0,1),
                           mk_port (if diff_port then id.test_host.test_listening_port_base else id.test_host.test_ephm_port))
       | Local     -> (true,
                       ts.th_libd_hnd,
                         mk_ip id.test_host.test_ip_address,
                           mk_port id.test_host.test_ephm_port)
       | NonLocal  -> (false,
                       ts.ah_libd_hnd,
                         mk_ip id.aux_host.test_ip_address,
                           mk_port id.aux_host.test_ephm_port) in
    (* ------ *)
    let fd2opt =
      (if is_listening then
         let fd2 = get_local_bound_socket (the rem_libd_hnd)
             (Some rem_ip_address)
             (Some rem_ephm_port) in
         let listen_call = (tid_of_int_private 0, LISTEN(fd2, 1)) in
         ignore(libd_call (the rem_libd_hnd) listen_call);
         Some fd2
       else
         None) in
    (* ------ *)
    let connect_call = (tid_of_int_private 0,
			CONNECT(fd, rem_ip_address, Some(rem_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) connect_call);
    delay 25.00;
    rst_driven_socket ts id fd NO_DATAGRAMS;
    if rem_is_local = false && fd2opt <> None then
      (let linger_call = (tid_of_int_private 0, SETSOCKTOPT((the fd2opt), SO_LINGER, Some(0,0))) in
      ignore(libd_call (the rem_libd_hnd) linger_call);
      let reset_call = (tid_of_int_private 0, CLOSE(the fd2opt)) in
      ignore(libd_call (the rem_libd_hnd) reset_call))
    else
      ();
    ignore(lift slurper_destroy slurper_hnd);
    ignore(lift destroy_log slurper_log)),
  (let blockness  = if is_nonblocking then "non-" else "" in
   let localness  = match locality with
                      LocalLoop -> "local loopback"
                    | Local     -> "local"
                    | NonLocal  -> "non-local" in
   let listenness = if is_listening then "" else "non-" in
   let selfconnectness = if locality=LocalLoop && is_listening && not diff_port then "itself over the loopback interface" else "a " ^ localness ^ " " ^ listenness ^ "listening socket" in
   "connect() -- for a fresh " ^ blockness ^ "blocking socket, in the CLOSED state and with binding quad " ^ bqdescr ^ ", attempt to connect() to " ^ selfconnectness),
  ((true, true), true (* start slurper manually *), true, false),
  if locality = NonLocal then  (* only need tools on aux host if it is used *)
    ((is_listening, false), true, true, false)
  else
    ((false, false), false, false, false)
 )


let test1  = test_1234 (false,true ,NonLocal,false)
let test2  = test_1234 (false,false,NonLocal,false)
let test3  = test_1234 (true ,true ,NonLocal,false)
let test4  = test_1234 (true ,false,NonLocal,false)
let test1a = test_1234 (false,true ,Local,false)
let test2a = test_1234 (false,false,Local,false)
let test3a = test_1234 (true ,true ,Local,false)
let test4a = test_1234 (true ,false,Local,false)
let test1b = test_1234 (false,true ,LocalLoop,false)
let test2b = test_1234 (false,false,LocalLoop,false)
let test3b = test_1234 (true ,true ,LocalLoop,false)
let test4b = test_1234 (true ,false,LocalLoop,false)
let test4c = test_1234 (false,true ,LocalLoop,true)



let test5 = function (bq, bqdescr) -> (
  (function id -> function ts ->
    let fd = the(fst(get_bound_socket id ts bq)) in
    let connect_call = (tid_of_int_private 0,
			CONNECT(fd, mk_ip id.virtual_host_ip,
				Some(mk_port id.virtual_host_port))) in
    ignore(libd_call (the ts.th_libd_hnd) connect_call);
    rst_driven_socket ts id fd NO_DATAGRAMS),
  "connect() -- for a fresh blocking socket, in the CLOSED state and with binding quad " ^ bqdescr ^ ", attempt to connect() to the socket of a non-existent host (a timeout is expected here)",
  ((true, false), true, true, false),
  ((false, false), false, false, false)
 )

let test_6789 = function (is_nonblocking, is_listening, locality) ->
               function (st, stdescr) -> (
  (function id -> function ts ->
    (* ------ *)
    (* Start the slurper -- need to do this here because of loopbacks *)
    (* ------ *)
    let slurper_log =
      if locality <> NonLocal && id.test_host.platform_type != ARCH_WINXP then
	let log = create_fresh_log (string_ip id.tthee_host) in
	let _ = merger_register_log ts.th_merge_hnd log None in
	Some(log)
      else
	None in
    let (slurp_filter, slurp_hostip, slurp_iface) =
      if locality = LocalLoop then
	(Some("tcp"), Some(hol_ip (127,0,0,1)), id.test_host.loopback_name)
      else if locality = Local then
	(Some("tcp"), Some(hol_ip id.test_host.test_ip_address), id.test_host.loopback_name)
      else
        (None, None, "")
    in
    let slurper_hnd =
      if locality <> NonLocal && id.test_host.platform_type != ARCH_WINXP then
	Some(slurper_create id.test_host.ns_tools_exec_params
	       (the slurper_log) slurp_iface slurp_filter slurp_hostip)
      else
	None
    in

    delay 10.00;
    (* ----- *)
    let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
    let nonblock_call = (tid_of_int_private 0,
			 SETFILEFLAGS(fd, if is_nonblocking then [O_NONBLOCK] else [])) in
    ignore(libd_call (the ts.th_libd_hnd) nonblock_call);
    let (rem_is_local,rem_libd_hnd,rem_ip_address,rem_ephm_port) =
      match locality with
         LocalLoop -> (true,
                       ts.th_libd_hnd,
                         mk_ip (127,0,0,1),
                           mk_port id.test_host.test_ephm_port)
       | Local     -> (true,
                       ts.th_libd_hnd,
                         mk_ip id.test_host.test_ip_address,
                           mk_port id.test_host.test_ephm_port)
       | NonLocal  -> (false,
                       ts.ah_libd_hnd,
                         mk_ip id.aux_host.test_ip_address,
                           mk_port id.aux_host.test_ephm_port) in
    (* ------ *)
    let fd2opt =
      (if is_listening then
        let fd2 = get_local_bound_socket (the rem_libd_hnd)
            (Some rem_ip_address)
            (Some rem_ephm_port) in
        let listen_call = (tid_of_int_private 0, LISTEN(fd2, 1)) in
        ignore(libd_call (the rem_libd_hnd) listen_call);
        Some fd2
       else
        None) in
    (* ------ *)
    let connect_call = (tid_of_int_private 0,
			CONNECT(fd, rem_ip_address, Some(rem_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) connect_call);
    delay 25.00;
    rst_driven_socket ts id fd last_dgram;
    if rem_is_local = false && fd2opt <> None then
      (let linger_call = (tid_of_int_private 0, SETSOCKTOPT((the fd2opt), SO_LINGER, Some(0,0))) in
      ignore(libd_call (the rem_libd_hnd) linger_call);
      let reset_call = (tid_of_int_private 0, CLOSE(the fd2opt)) in
      ignore(libd_call (the rem_libd_hnd) reset_call))
    else
      ();
    ignore(lift slurper_destroy slurper_hnd);
    ignore(lift destroy_log slurper_log)),
  (let blockness  = if is_nonblocking then "non-" else "" in
   let localness  = match locality with
                      LocalLoop -> "local loopback"
                    | Local     -> "local"
                    | NonLocal  -> "non-local" in
   let listenness = if is_listening then "" else "non-" in
   "connect() --  for a fresh " ^ blockness ^ "blocking socket in the " ^ stdescr ^ " state, attempt to connect() to a " ^ localness ^ " " ^ listenness ^ "listening socket"),
  ((true, true), true (* slurper started manually above due to loopbacks *), true, false),
  if locality = NonLocal then
    ((is_listening, false), false, false, true)
  else
    ((false, false), false, false, true)
 )

let test6  = test_6789 (false,true ,NonLocal)
let test7  = test_6789 (false,false,NonLocal)
let test8  = test_6789 (true ,true ,NonLocal)
let test9  = test_6789 (true ,false,NonLocal)
let test6a = test_6789 (false,true ,Local)
let test7a = test_6789 (false,false,Local)
let test8a = test_6789 (true ,true ,Local)
let test9a = test_6789 (true ,false,Local)
let test6b = test_6789 (false,true ,LocalLoop)
let test7b = test_6789 (false,false,LocalLoop)
let test8b = test_6789 (true ,true ,LocalLoop)
let test9b = test_6789 (true ,false,LocalLoop)

(* ---------------------------------------------------------------------- *)

let test10 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let connect_call = (tid_of_int_private 0,
			CONNECT(fd, mk_ip (200,200,200,10),
				Some(mk_port id.virtual_host_port))) in
    ignore(libd_call (the ts.th_libd_hnd) connect_call);
    rst_driven_socket ts id fd NO_DATAGRAMS),
  "connect() -- for a fresh blocking socket attempt to connect() to a non-local, listening socket for which there is no route to its host",
  ((true, false), true, true, false),
  ((false, false), false, false, false))
(* this test excluded because for some reason it was taking forever *)

let test11 = (
  (function id -> function ts ->
    (* Get a bound socket *)
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    let sockopt_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_REUSEADDR, true)) in
    ignore(libd_call (the ts.th_libd_hnd) sockopt_call);
    (* Start listening *)
    let listen_call = (tid_of_int_private 0, LISTEN(fd, 3)) in
    ignore(libd_call (the ts.th_libd_hnd) listen_call);

    (* Put a connection on the connection queue *)
    let aux_fd = get_socket (the ts.ah_libd_hnd) in
    let sockopt_call = (tid_of_int_private 0, SETSOCKBOPT(aux_fd, SO_REUSEADDR, true)) in
    ignore(libd_call (the ts.ah_libd_hnd) sockopt_call);
    let bind_call = (tid_of_int_private 0,
		     BIND(aux_fd,
			  Some (mk_ip id.aux_host.test_ip_address),
			  Some (mk_port id.aux_host.test_npoe_port))) in
    ignore(libd_call (the ts.ah_libd_hnd) bind_call);
    let sockopt_call = (tid_of_int_private 0, SETSOCKBOPT(aux_fd, SO_REUSEADDR, true)) in
    ignore(libd_call (the ts.ah_libd_hnd) sockopt_call);
    (* Start listening *)
    let thread_body = (function () ->
      let connect_call = (tid_of_int_private 0,
			  CONNECT(aux_fd, mk_ip id.test_host.test_ip_address,
			  Some(mk_port id.test_host.test_ephm_port))) in
      ignore(libd_call (the ts.ah_libd_hnd) connect_call)) in
    let thread = Thread.create thread_body () in
    delay 2.00;
    (* Accept the connection *)
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) accept_call);

    (* Now try and connect the listening socket back to the remote *)
    (* end of the connected socket *)
    let connect_call = (tid_of_int_private 0,
			CONNECT(fd, mk_ip id.aux_host.test_ip_address,
				Some(mk_port id.aux_host.test_npoe_port))) in
   ignore(libd_call (the ts.th_libd_hnd) connect_call);
    let close_call = (tid_of_int_private 0, CLOSE(aux_fd)) in
    ignore(libd_call (the ts.ah_libd_hnd) close_call);
    rst_driven_socket ts id fd NO_DATAGRAMS),
  "connect() -- for a blocking socket attempt to call connect() in such a way as to bind to an address that is already in use and results in the same binding quad as an existing connection",
  ((true, false), true, true, false),
  ((true, false), true, true, false))
(* this test is excluded because it's not quite working yet *)

let test12 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let nb_call = (tid_of_int_private 0, SETFILEFLAGS(fd,[O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) nb_call);
    let connect_call = (tid_of_int_private 0, CONNECT(fd, mk_ip (200,200,200,10), Some(mk_port id.virtual_host_port))) in
    ignore(libd_call (the ts.th_libd_hnd) connect_call);
    let connect_call = (tid_of_int_private 0, CONNECT(fd, mk_ip id.aux_host.test_ip_address, Some(mk_port id.aux_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) connect_call);
    delay 60.0;
    ignore(libd_call (the ts.th_libd_hnd) connect_call)),
  "connect() -- for a fresh non-blocking socket call connect() to non-local, socket for which there is no route to its host, then call connect() to the a non-listening socket on the aux-host, then delay and call connect() again",
  ((true,true),true,true,false),
  ((false,false),true,true,false))

let test13 = (
  (function id -> function ts ->
    let fd = get_socket (the ts.th_libd_hnd) in
    let conn_call = (tid_of_int_private 0, CONNECT(fd, mk_ip id.aux_host.test_ip_address, Some(mk_port id.aux_host.test_ephm_port))) in
    ignore(libd_call (the ts.th_libd_hnd) conn_call);
    let conn2_call = (tid_of_int_private 0, CONNECT(fd, mk_ip id.aux_host.test_ip_address, Some(mk_port id.aux_host.test_priv_port))) in
    ignore(libd_call (the ts.th_libd_hnd) conn2_call)),
  "connect() -- call connect() to a non-listening socket and then when that fails call connect() again to a different socket. Should fail on FreeBSD and succeed on others.",
  ((true,true),true,true,false),
  ((false,false),true,true,false))

let test14 = (
  function (shutrd, shutwr) -> (function id -> function ts ->
    let fd = get_local_bound_socket (the ts.th_libd_hnd)
	(Some (mk_ip id.test_host.test_ip_address))
	(Some (mk_port id.test_host.test_ephm_port)) in
    let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd,shutrd,shutwr)) in
    ignore(libd_call (the ts.th_libd_hnd) shutdown_call);
    let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) sn_call);
    let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
    ignore(libd_call (the ts.th_libd_hnd) pn_call);
    let setfflag_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call (the ts.th_libd_hnd) setfflag_call);
    let connect_call = (tid_of_int_private 0, CONNECT(fd, mk_ip id.aux_host.test_ip_address, Some(mk_port id.aux_host.test_priv_port))) in
    ignore(libd_call (the ts.th_libd_hnd) connect_call);
    rst_driven_socket ts id fd (NO_DATAGRAMS)),
  "connect() -- for a fresh bound socket, call shutdown(" ^ (if shutrd then "T" else "F") ^ "," ^ (if shutwr then "T" else "F") ^ ") followed by a call to connect(), to a remote non-listening socket.",
  ((true, false), true, true, false),
  ((false, false), true, true, false)

)

(* ---------------------------------------------------------------------- *)

let driven_states =
  let rec remove_listen_state driven_list =
    match driven_list with
      [] -> []
    | (ST_CLOSED, y)::xs -> remove_listen_state xs
    | (x, y)::xs -> (x, y)::(remove_listen_state xs) in
  remove_listen_state all_interesting_driven_states

(*let test_from_all_states =  List.map test8 driven_states*)

let bound_states =
  List.map (function (i1,p1) ->
    let quad = (i1,p1,UNSPECIFIED_IP,UNSPECIFIED_PORT) in
    (quad, string_of_bound_quad quad))
    local_bindings_list

let all_driven_tests =
  (List.map test6  driven_states) @
  (List.map test7  driven_states) @
  (List.map test8  driven_states) @
  (List.map test9  driven_states) @
  (List.map test6a driven_states) @
  (List.map test7a driven_states) @
  (List.map test8a driven_states) @
  (List.map test9a driven_states) @
  (List.map test6b driven_states) @
  (List.map test7b driven_states) @
  (List.map test8b driven_states) @
  (List.map test9b driven_states)

let all_bound_tests =
  (List.map test1  bound_states) @
  (List.map test2  bound_states) @
  (List.map test3  bound_states) @
  (List.map test4  bound_states) @
  (List.map test1a bound_states) @
  (List.map test2a bound_states) @
  (List.map test3a bound_states) @
  (List.map test4a bound_states) @
  (List.map test1b bound_states) @
  (List.map test2b bound_states) @
  (List.map test3b bound_states) @
  (List.map test4b bound_states) @
  (List.map test4c bound_states) @
  (List.map test5 bound_states)

let tcp_tests = [test10; test11; test12; test13] @ all_bound_tests @ all_driven_tests
                                                 @ (List.map test14 [(true,false);(false,true);(true,true)])

let udp_tests = []

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = [test10; test11; test12; test13]
                    @ (List.map test14 [(true,false);(false,true);(true,true)])
                    @ all_bound_tests
let stream_exhaustive_tests = []

(* ---------------------------------------------------------------------- *)

let do_connect_tests handle hosts_list test_type =
  begin_next_test_group handle "connect()";
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
		let ((l,priv),s,d,i) = thts in
		let thts = ((l,
			     if host.platform_type = ARCH_WINXP then true
			     else priv),
			    s,d,i) in
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

		delay 3.00;
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
