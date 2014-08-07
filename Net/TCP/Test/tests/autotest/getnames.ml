(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code: getsockname(), getpeername()        *)
(* Steve Bishop - Created 20030626                                        *)
(* $Id: getnames.ml,v 1.16 2006/06/28 16:24:15 amgb2 Exp $ *)
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
open Dualdriven_udp
open Common_udp
open Testscommon
(* ---------------------------------------------------------------------- *)

let test1 = (
  function (binding, binding_str) ->
    let aux_libd_required =
      let i1,p1,i2,p2 = binding in
      if (i2 = FOREIGN_IP) && (p2 != UNSPECIFIED_PORT) then true else false
    in
    (function id -> function ts ->
      (* ------ *)
      (* Start the slurper -- need to do this here because of loopbacks *)
      (* ------ *)
      let slurper_log =
	  let log = create_fresh_log (string_ip id.tthee_host) in
	  let _ = merger_register_log ts.th_merge_hnd log None in
	  Some(log) in
      let (slurp_filter, slurp_hostip, slurp_iface) =
	(Some("tcp"), Some(hol_ip (127,0,0,1)), id.test_host.loopback_name)
      in
      let slurper_hnd =
	  Some(slurper_create id.test_host.ns_tools_exec_params
		 (the slurper_log) slurp_iface slurp_filter slurp_hostip)
      in

      delay 10.00;
      (* ----- *)

      let fd1,fd2 =  get_bound_socket id ts binding in
      rst_driven_socket ts id (the fd1) NO_DATAGRAMS;
      delay 5.00;
      ignore(lift slurper_destroy slurper_hnd);
      ignore(lift destroy_log slurper_log)),
      (* Don't need to call getsockname() or getpeername() as they are *)
      (* implicitly called everytime we do bind() or connect() *)
    "getsockname(), getpeername() -- for a fresh TCP socket with binding quad, " ^ binding_str ^", call getsockname() and getpeername()",
    ((true, true), true, true, false),
    ((aux_libd_required, true), aux_libd_required, aux_libd_required, false)
 )


let test2 = (
  function (st, stdescr) ->
    (function id -> function ts ->
      let fd, last_dgram, _ = tcp_state_diagram_driver id ts st false in
      get_bound_state (the ts.th_libd_hnd) fd;
      rst_driven_socket ts id fd last_dgram),
    "getsockname(), getpeername() -- for a TCP socket in state " ^ stdescr ^ ", call getsockname() and getpeername()",
    ((true, false), true, true, false),
    ((false,false), false, false, true)
 )

let test3 = (
  function (sf,sfdescr) ->
    (function id -> function ts ->
      let fd = get_bound_socket_udp id ts sf in
      get_bound_state_udp (the ts.th_libd_hnd) fd;
      rst_udp_socket id ts fd),
    "getsockname(),getpeername() -- for a UDP socket with binding quad, " ^ sfdescr ^ ", call getsockname() and getpeername()",
    ((true,false),true,false,false),
    ((false,false),false,false,true))

let bound_states =
  List.map (function x -> (x, string_of_bound_quad x))
    all_bindings_list

let tcp_tests =
  (List.map test1 bound_states) @
  (List.map test2 all_driven_states)

let udp_tests = (List.map test3 bound_udp_quads)

let normal_tests = tcp_tests @ udp_tests

let tcp_exhaustive_tests = []
let udp_exhaustive_tests = []
let exhaustive_tests = tcp_exhaustive_tests @ udp_exhaustive_tests

let stream_tests = List.map test1 bound_states
let stream_exhaustive_tests = []

(* ---------------------------------------------------------------------- *)

let do_getnames_tests handle hosts_list test_type =
  begin_next_test_group handle "getsockname()/getpeername()";
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
		let id = {
		  tthee_host = handle.tthee_host_ip;
		  virtual_host_ip = handle.vhost_ip;
		  virtual_host_port = handle.vhost_port;
		  seq_fname = test_fname;
		  test_descr =(test_type_str test_type) ^ " " ^ descr;

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
	  num_of_tests := !num_of_tests + 1;)
	tests
    )
    hosts_list;
  !done_a_test

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
