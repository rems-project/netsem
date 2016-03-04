(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: bind()                              *)
(* Steve Bishop - Created 20030503                                        *)
(* $Id: bind.ml,v 1.19 2006/06/19 11:57:44 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

open Thread;;

(* Our libraries *)
open Tthee;;
open Ttheehelper;;
open Ocamllib;;
open Libcalls;;
open Common;;
open Simple;;
open Testscommon;;

(* ---------------------------------------------------------------------- *)
(* Testing of bind() *)
(* ---------------------------------------------------------------------- *)

type bound_ip =
    UNSPECIFIED
  | AVAILABLE
  | UNAVAILABLE;;

type bound_port =
    UNBOUND of local_port_binding
  | BOUND of local_port_binding;;


let make_bind_descr bound_ip bound_port priv =
  let ip_str =
    match bound_ip with
      UNSPECIFIED -> "unspecified IP"
    | AVAILABLE -> "available IP"
    | UNAVAILABLE -> "unavailable IP" in
  let port_str, pb =
    match bound_port with
      UNBOUND(pb) -> "Unbound ", pb
    | BOUND(pb) -> "Bound ", pb in
  let port_str = port_str ^
    (match pb with
      PORT_UNSPEC -> "unspecified port"
    | PORT_PRIV -> "privileged port" ^
	(if priv then " with permission"
	else " without permission")
    | PORT_EPHEMERAL -> "ephemeral port"
    | PORT_NPOE -> "non-priv non-ephem port") in
  "bind() -- call bind() to test the result of binding to an " ^ ip_str ^ "address and " ^ port_str;;

let make_bind_ip host bound_ip =
  match bound_ip with
    UNSPECIFIED -> None
  | AVAILABLE -> Some(Ocamllib.ip_of_string (string_ip host.test_ip_address))
  | UNAVAILABLE -> Some(Ocamllib.ip_of_string (string_ip host.unavailable_ip_address))
;;

let make_bind_port host bound_port =
  let pb =
    match bound_port with
      UNBOUND (pb) -> pb
    | BOUND (pb) -> pb in
  match pb with    PORT_UNSPEC -> None
  | PORT_PRIV ->  Some(Ocamllib.port_of_int host.test_priv_port)
  | PORT_EPHEMERAL -> Some(Ocamllib.port_of_int host.test_ephm_port)
  | PORT_NPOE ->  Some(Ocamllib.port_of_int host.test_npoe_port);;

(* do_bind_tests handle host_pair_list test_type = bool                        *)
(* For each pair of hosts in host_pair_list perform a suite of tests designed  *)
(* to test the bind() system call.  For more information on the tests          *)
(* refer to the auto-testing documentation                                     *)
let do_bind_tests handle host_pair_list test_type =
  begin_next_test_group handle "bind()";
  let hosts = host_pair_list in

  match test_type with
    UDP_NORMAL -> false
  | UDP_EXHAUSTIVE -> false
  | STREAM_EXHAUSTIVE -> false
  (* I'm not convinced TCP_EXHAUSTIVE shouldn't be here also, if we want it
     to be the case that TCP_NORMAL and TCP_EXHAUSTIVE don't overlap, but it
     doesn't seem terribly important -- amgb *)
  | _ ->

  (* Generic function to create a bind test thunk *)
  (* bound_ip - type of ip binding to test *)
  (* bound_port - type of port binding to test *)
  (* priv - whether libd should run as root *)
  let create_test bound_ip bound_port priv =
    let test send recv fname =
      (* WinXP no privs hack *)
      let priv =
	if send.platform_type =  ARCH_WINXP then
	  true
	else
	  priv in
      (* Create a test_init record to return *)
      let binding_info =
	match bound_port with
	  UNBOUND(_) -> None
	| BOUND(pb) ->
	    (match pb with
	      PORT_UNSPEC -> None
	    | PORT_PRIV -> Some(send.test_priv_port)
	    | PORT_EPHEMERAL -> Some(send.test_ephm_port)
	    | PORT_NPOE -> Some(send.test_npoe_port)) in
      let already_bound =
	match binding_info with
	  None -> []
	| Some(p) ->
	    [((make_bind_ip send bound_ip), p)] in
      let ti = {
	tthee_host = handle.tthee_host_ip;
	send_host = send;
	recv_host = recv;
	seq_fname = fname;
	priv = priv;
	already_bound = already_bound;
	test_descr = make_bind_descr bound_ip bound_port priv
      } in

      (* The thunk that does the actual testing *)
      let f = function ts ->
	(* Create a socket *)
	let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
	let fd = match libd_call ts.libd_hnd socket_call with
	  (_, OK_FD(fd)) -> fd
	|	_ -> raise(Test_failed(ti.test_descr)) in

	(* Select ip and port *)
	let ips = make_bind_ip send bound_ip in
	let ps = make_bind_port send bound_port in

        (* If we are doing a test involving an already bound port number *)
	(* then create a second socket and bind to the port first *)
	let ts2 =
	  (match bound_port with
	    BOUND(_) -> (
              (* Initialise a temporary tthee *)
	      let ti2 = {ti with seq_fname = (ti.seq_fname^".tmp");
			 send_host = {ti.send_host with host_supports_holtcpcb = false};
			 recv_host = {ti.recv_host with host_supports_holtcpcb = false} } in
	      let ts2 = simple_pre_test_init ti2 !tthee_baseport_2 in
	      (* Create socket *)
	      let socket_call2 = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
	      let fd = match libd_call ts2.libd_hnd socket_call2 with
		(_, OK_FD(fd)) -> fd
	      |	_ -> raise(Test_failed(ti.test_descr)) in
	      (* Do the binding *)
	      let bind_call = (tid_of_int_private 0, BIND(fd, ips, ps)) in
	      let _ = libd_call ts2.libd_hnd bind_call in Some(ts2)
	     )
	  | _ -> None) in

        (* Finally, try and perform the bind we are interested in *)
	let bind_call = (tid_of_int_private 0, BIND(fd, ips, ps)) in
	let _ = libd_call ts.libd_hnd bind_call in

	(* Call getsockname() and getpeername() so we can see what happened *)
	let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
	let _ = libd_call ts.libd_hnd sn_call in
	let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
	let _ = libd_call ts.libd_hnd pn_call in

	(* ..and cleanup the temporary tthee *)
	match ts2 with
	  None -> ()
	| Some(state) -> simple_cleanup_tthee state in
      (ti, f) in
    test in

  (* Create the list of tests to be performed *)
  let test_thunk_list = [
    create_test UNSPECIFIED (UNBOUND(PORT_UNSPEC)) false;
    create_test UNSPECIFIED (UNBOUND(PORT_NPOE)) false;
    create_test UNSPECIFIED (UNBOUND(PORT_EPHEMERAL)) false;
    create_test UNSPECIFIED (UNBOUND(PORT_PRIV)) true;
    create_test UNSPECIFIED (UNBOUND(PORT_PRIV)) false;
    create_test UNSPECIFIED (BOUND(PORT_NPOE)) false;
    create_test UNSPECIFIED (BOUND(PORT_EPHEMERAL)) false;
    create_test UNSPECIFIED (BOUND(PORT_PRIV)) true;
    create_test UNSPECIFIED (BOUND(PORT_PRIV)) false;

    create_test AVAILABLE (UNBOUND(PORT_UNSPEC)) false;
    create_test AVAILABLE (UNBOUND(PORT_NPOE)) false;
    create_test AVAILABLE (UNBOUND(PORT_EPHEMERAL)) false;
    create_test AVAILABLE (UNBOUND(PORT_PRIV)) true;
    create_test AVAILABLE (UNBOUND(PORT_PRIV)) false;
    create_test AVAILABLE (BOUND(PORT_NPOE)) false;
    create_test AVAILABLE (BOUND(PORT_EPHEMERAL)) false;
    create_test AVAILABLE (BOUND(PORT_PRIV)) true;
    create_test AVAILABLE (BOUND(PORT_PRIV)) false;

    create_test UNAVAILABLE (UNBOUND(PORT_UNSPEC)) false;
    create_test UNAVAILABLE (UNBOUND(PORT_NPOE)) false;
    create_test UNAVAILABLE (UNBOUND(PORT_EPHEMERAL)) false;
    create_test UNAVAILABLE (UNBOUND(PORT_PRIV)) true;
    create_test UNAVAILABLE (UNBOUND(PORT_PRIV)) false;
    create_test UNAVAILABLE (BOUND(PORT_NPOE)) false;
    create_test UNAVAILABLE (BOUND(PORT_EPHEMERAL)) false;
    create_test UNAVAILABLE (BOUND(PORT_PRIV)) true;
    create_test UNAVAILABLE (BOUND(PORT_PRIV)) false;
  ] in


  let done_a_test = ref false in
  let num_of_tests = ref 0 in
  for_each_host_pair_and_test hosts test_thunk_list
    (function (send, recv) -> function test ->
      let _ =
	(if(!num_of_tests = 10) then
	  let _ =  num_of_tests := 0 in
	  ntp_update 60.0) in
      if not(skip_test handle) then
	let _ = done_a_test := true in
        (* Create the trace filename *)
	let test_fname = fmt_fname handle !trace_name_number_size in

        (* Get the test_init structure and thunk *)
	let ti, test_thunk = test send recv test_fname in

	let ti = {ti with test_descr = (test_type_str test_type) ^ " " ^ ti.test_descr} in

        (* Initialise tthee *)
	let test_specific_state = simple_pre_test_init ti !tthee_baseport_1 in

        (* Perform the test *)
	let testno = Int64.to_string !(handle.output_actual_seq_num) in
	let _ =
	  try test_thunk test_specific_state
	  with e -> report_test_failure handle ti.test_descr e
	in
        (* Tidy up *)
	num_of_tests := !num_of_tests + 1;
	simple_post_test_cleanup handle test_specific_state
      else ();
      next_test handle
    );
  !done_a_test
