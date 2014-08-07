(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Code                                      *)
(* Adam Biltcliffe - Created 20060630                                     *)
(* $Id: loss.ml,v 1.1 2006/07/03 15:32:12 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread
open Printf

(* Our libraries *)
open Nettypes
open Tthee
open Ttheehelper
open Testscommon
open Ocamllib
open Libcalls
open Common
open Dual
open Dualdriven
open Common_udp
open Dualdriven_udp

type loss_test_config = host_info * Ttheehelper.ip (* first host *)
                      * host_info * Ttheehelper.ip (* second host *)
                      * host_info (* where to run mirror *)

let mirror_opt_list =
  [ (["-l"; "0.5"], "50% packet loss");
    (["-n"; "3"],   "up to 3 duplicates per packet") ]

(* ---------------------------------------------------------------------- *)

 let test1 = (
  (function id -> function ts -> function tfakeip, afakeip ->
print_endline "entering test thunk";
    let fd_lis = get_socket (the ts.ah_libd_hnd) in
print_endline "created socket";
    let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd_lis, SO_REUSEADDR, true)) in
    ignore (libd_call (the ts.ah_libd_hnd) reuse_call);
print_endline "set options";
    let bind_call = (tid_of_int_private 0, BIND(fd_lis, Some (mk_ip id.aux_host.test_ip_address), Some (mk_port id.aux_host.test_listening_port_base))) in
    ignore (libd_call (the ts.ah_libd_hnd) bind_call);
print_endline "bound socket";
    let listen_call = (tid_of_int_private 0, LISTEN(fd_lis, 1)) in
    ignore (libd_call (the ts.ah_libd_hnd) listen_call);
print_endline "started listening";
    let fd_con = get_socket (the ts.th_libd_hnd) in
print_endline "got other socket";
    let connect_call = (tid_of_int_private 0, CONNECT(fd_con, mk_ip afakeip, Some (mk_port id.aux_host.test_listening_port_base))) in
    ignore (libd_call (the ts.th_libd_hnd) connect_call);
print_endline "connected"),
  "network: try to establish a connection",
  ((true, false), true, true, false),
  ((true, false), true, true, false)
 )

let tests = [test1]

(* ---------------------------------------------------------------------- *)

let do_loss_tests handle cfg_list test_type =
  begin_next_test_group handle "lossy network";
  let done_a_test = ref false in
  let num_of_tests = ref 0 in

  let tests = match test_type with
    STREAM_NORMAL -> tests
  | _ -> [] in

  List.iter
    (function mirror_opts, mirror_opts_descr ->
  List.iter
    (function (thost, tfakeip, ahost, afakeip, mirrorhost) ->
      List.iter
	(function (test_thunk, descr, thts, ahts) ->
    let realdescr = descr ^ " (" ^ mirror_opts_descr ^ ")" in
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
		  test_descr = (test_type_str test_type) ^ " " ^ realdescr;

		  test_host = thost;
		  test_host_tools = thts;
		  test_host_bound = [];

		  aux_host = ahost;
		  aux_host_tools =  ahts;
		  aux_host_bound = [];
		} in

		let ts = dual_tthee_init id debug_OFF !tthee_baseport_1
		    !tthee_baseport_2 !merger_delta in
    let rewritelist = [string_ip (thost.test_ip_address);
                       string_ip tfakeip;
                       string_ip (ahost.test_ip_address);
                       string_ip afakeip ] in
    let mirror_log = create_fresh_log (string_ip id.tthee_host) in
    let _ = merger_register_log ts.th_merge_hnd mirror_log in
    let mirror_hnd = mirror_create mirrorhost.ns_tools_exec_params mirror_log
                       mirrorhost.iface_name rewritelist (Some mirror_opts) in
		let _ =
		  try test_thunk id ts (tfakeip, afakeip)
		  with e -> report_test_failure handle realdescr e
		in
    mirror_destroy mirror_hnd;
    destroy_log mirror_log;

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
    cfg_list
    )
    mirror_opt_list;
  !done_a_test;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
