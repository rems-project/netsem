(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Simple Test Helper Code                   *)
(* Steve Bishop - Created 20030503                                        *)
(* $Id: simple.ml,v 1.9 2005/12/13 10:12:46 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread;;
open Unix;;
open ThreadUnix;;
open Printf;;

(* Our libraries *)
open Nettypes;;
open Netconv;;
open Ocamllib;;
open Tthee;;
open Ttheehelper;;
open Libcalls;;
open Testscommon;;
open Common;;


(* ---------------------------------------------------------------------- *)
(* State of an individual test run *)
(* ---------------------------------------------------------------------- *)

type test_run_state_simple = {
    out_fd           : Unix.file_descr;
    out_ch           : out_channel;
    merge_hnd        : merger_handle;
    libd_hnd         : libd_handle;
    slurper_hnd      : slurper_handle;
    injector_hnd     : injector_handle;
    holtcpcb_hnd_opt : holtcpcb_handle option;

    libd_log         : log_handle;
    slurper_log      : log_handle;
    holtcpcb_log     : log_handle option
  } ;;


(* ---------------------------------------------------------------------- *)
(* Preinitialisation of test socket *)
(* ---------------------------------------------------------------------- *)

(* setup_preinit_state test_run_state_simple preinit_state local_host_info *)
(*                     foreign_host_ip_opt foreign_host_port_opt = file_descr *)
let setup_preinit_state ts preinit_state hi foreign_ips foreign_ps =
  (* Create a socket *)
  let sd =
    match libd_call ts.libd_hnd (tid_of_int_private 0, SOCKET(SOCK_STREAM)) with
      (_, OK_FD(fd)) -> fd
    | _ -> raise(Assertion_failed("setup_preinit_state SOCKET_ONLY")) in

  (* Perform a local binding *)
  let local_binding ip_bind port_bind =
    let ips =
      match ip_bind with
	IP_UNSPEC -> None
      |	IP_LOCAL -> Some(Ocamllib.ip_of_string(string_ip hi.test_ip_address)) in
    let ps =
      match port_bind with
	PORT_UNSPEC -> None
      |	PORT_PRIV -> Some(Ocamllib.port_of_int hi.test_priv_port)
      |	PORT_EPHEMERAL -> Some(Ocamllib.port_of_int hi.test_ephm_port)
      |	PORT_NPOE -> Some(Ocamllib.port_of_int hi.test_npoe_port) in
    ignore(libd_call ts.libd_hnd (tid_of_int_private 0, BIND(sd, ips, ps))) in

  (* Perform an optional local binding followed by an active connection attempt *)
  let connected_bound ip_bind port_bind =
    (match ip_bind, port_bind with
      IP_UNSPEC, PORT_UNSPEC -> ()
    | _ -> local_binding ip_bind port_bind);
    let conn_ip =
      match foreign_ips with
	None -> raise(Assertion_failed("No IP specified in call to setup_preinit_state"))
      |	Some(ip) -> Ocamllib.ip_of_string (string_ip ip) in
    let conn_port =
      match foreign_ps with
	None -> raise(Assertion_failed("No port specified in call to setup_preinit_state"))
      |	Some(p) -> Ocamllib.port_of_int p in
    ignore(libd_call ts.libd_hnd (tid_of_int_private 0, CONNECT(sd, conn_ip, Some(conn_port)))) in

  (* Select which type of binding should occur *)
  let bind_type_selector bt =
    match bt with
      LOCAL_BOUND(ip_bind, port_bind) ->
	local_binding ip_bind port_bind
    | CONNECTED_BOUND(ip_bind, port_bind, ipf_bind) ->
	connected_bound ip_bind port_bind in

  (* Call the requested binding function *)
  match preinit_state with
    SOCKET_ONLY -> sd
  | BOUND_SOCKET(bt) ->
      bind_type_selector bt; sd
  | BOUND_SOCKET_CUSTOM(bt, f) ->
      bind_type_selector bt; f (); sd;;


(* ---------------------------------------------------------------------- *)
(* TThee initialisation and shutdown functions (Simple mode)              *)
(* ---------------------------------------------------------------------- *)

type tthee_init_simple = {
    tthee_host: Ttheehelper.ip;     (* IP of tthee control host *)
    send_host: host_info;           (* Client test host (that will run libd) *)
    recv_host: host_info;           (* Server test host (that will inject) *)
    seq_fname: string;              (* Unique trace filename *)
    priv: bool;                     (* Run libd as root? *)
    already_bound: (Ocamllib.ip option * int) list;  (* Already bound port number *)
    test_descr: string              (* Description of test *)
  } ;;

(* This is a temporary hack in order to get quick-and-dirty multi-host traces *)
(* working. If it's still here come November or so, amgb2 has been very naughty. *)
let make_multipurpose_merger fname =
  let out_fd = Unix.openfile fname [O_WRONLY; O_CREAT; O_TRUNC] 432 in
  let out_ch = Unix.out_channel_of_descr out_fd in
  output_string out_ch "(* Multi-host merger output *)";
  merger_create out_ch RAW;;

(* simple_pre_test_init tthee_init_simple = test_run_state_simple *)
(* Initialise tthee and start test processes on the test hosts *)
(* libd, holtcpcb-v8, slurper run on send host and injector on recv host. *)
(* If send_host is WinXP, then the slurper runs on the recv host instead: this *)
(* is a fix to get better timestamps than is possible using winpcap *)
(* Used primarily by socket(), bind() and connect() tests *)
let simple_pre_test_init_with_merger ti base_port m =
  (* Set the tthee debug level *)
  let _ = set_debug_level debug_OFF in

  (* Pull out some testing host specific information *)
  let send_ip = ti.send_host.test_ip_address in
  let recv_ip = ti.recv_host.test_ip_address in
  let send_exec = ti.send_host.ns_tools_exec_params in
  let recv_exec = ti.recv_host.ns_tools_exec_params in

  (* Open a file for merge results *)
  let out_fd = Unix.openfile ti.seq_fname [O_WRONLY; O_CREAT; O_TRUNC] 432 in
  let out_ch = Unix.out_channel_of_descr out_fd in

  (* Write out host and test description to trace file *)
  let str = (platform_to_string ti.send_host.platform_type) ^ "(" ^ ti.send_host.host_name ^
    ") ---> " ^ (platform_to_string ti.recv_host.platform_type) ^ "(" ^
    ti.recv_host.host_name ^ ")" in
  output_string out_ch ("(* Test Host: " ^ str ^ " *)\n");
  output_string out_ch ("(* Test Description: " ^ ti.test_descr ^ " *)\n\n");

  let merge_hnd, log_name = (match m with
    Some(h) -> (h, Some ti.send_host.host_name)
  | None -> ((* Create merger *) merger_create out_ch RAW, None))
  in

  (* Setup an initial_host *)
  let initial_host = ti.send_host.hol_initial_host in

  (* Initialise libd *)
  let libd_log = create_fresh_log (string_ip ti.tthee_host) in
 (* let _ = merger_register_log merge_hnd libd_log None in *)
  let _ = merger_register_named_log merge_hnd libd_log None log_name in

  (* Initialise slurper *)
  let slurp_log = create_fresh_log (string_ip ti.tthee_host) in
  let slurp_filter = create_filter send_ip recv_ip in
  let slurp_hostip = Some(hol_ip (get_initial_host_ip initial_host)) in
  let slurp_iface =
    if (ti.send_host.platform_type != ARCH_WINXP) then
      ti.send_host.iface_name
    else
      ti.recv_host.iface_name
  in
 (* let _ = merger_register_log merge_hnd slurp_log None in *)
  let _ = merger_register_named_log merge_hnd slurp_log None log_name in

  (* Initialise holtcpcb *)
  let tcpcb_log =
    if ti.send_host.host_supports_holtcpcb then
      Some(create_fresh_log (string_ip ti.tthee_host))
    else
      None in
  let _ =
    match tcpcb_log with
      None -> ()
  (*  | Some(log) -> merger_register_log merge_hnd log None *)
    | Some(log) -> merger_register_named_log merge_hnd log None log_name
  in

  (* Start the merger *)
  let merger_hdr_msg = "" in
  merger_begin merge_hnd (Int64.of_int 1000000) merger_hdr_msg;

  (* Create test tool processes *)
  let libd_hnd = libd_create send_exec (cmd_tcp_create send_ip (base_port+1))
      libd_log ti.send_host.host_supports_holtcpcb ti.priv in

  (* Create the initial_host_header which depends upon the libd remote pid *)
  let bound_state = ti.already_bound in
  let merger_hdr_msg =
    (initial_host_to_string initial_host (libd_getpid libd_hnd) (ti.send_host.platform_type)
       ti.priv bound_state) ^
    "(* Injector: running on " ^ (print_initial_host_name ti.recv_host.hol_initial_host) ^ "*)" in

  (* Call merger_begin again to update the header message *)
  merger_begin merge_hnd (Int64.of_int 100000) merger_hdr_msg;

  (* Finish creating the test tool processes *)
  let inj_hnd = injector_create recv_exec (cmd_tcp_create recv_ip base_port) in
  let slurp_hnd =
    if (ti.send_host.platform_type != ARCH_WINXP) then
      slurper_create send_exec slurp_log slurp_iface slurp_filter slurp_hostip
    else
      slurper_create recv_exec slurp_log slurp_iface slurp_filter slurp_hostip in
  let tcpcb_hndopt =
    match tcpcb_log with
      Some(log) -> Some(holtcpcb_create send_exec log [AF_INPUT;AF_OUTPUT;AF_DROP;AF_USER])
    | None -> None
  in

  (* Return a test_run_state_simple record *)
  {
   out_fd = out_fd;
   out_ch = out_ch;
   merge_hnd = merge_hnd;
   libd_hnd = libd_hnd;
   slurper_hnd = slurp_hnd;
   injector_hnd = inj_hnd;
   holtcpcb_hnd_opt = tcpcb_hndopt;
   libd_log = libd_log;
   slurper_log = slurp_log;
   holtcpcb_log = tcpcb_log;
 } ;;

let simple_pre_test_init ti base_port = simple_pre_test_init_with_merger ti base_port None;;


(* simple_cleanup_tthee test_run_state_simple = unit *)
(* Clean-up function for simple test runs that were initialised by a *)
(* call to simple_pre_test_init() *)
(* Destroy all of the test tool processes by calling the relevant *)
(* tthee destroy function. *)
let simple_cleanup_tthee test_state =
  let _ = Thread.delay !test_quiet_period in
  (match test_state.holtcpcb_hnd_opt with
    None -> ()
  | Some(hnd) -> let _ = holtcpcb_destroy hnd in ());
  let _ = injector_destroy test_state.injector_hnd in
  let _ = libd_destroy test_state.libd_hnd in
  let _ = slurper_destroy test_state.slurper_hnd in
  let _ = merger_destroy test_state.merge_hnd in
  let _ = destroy_log test_state.libd_log in
  let _ = destroy_log test_state.slurper_log in
  let _ =
    match test_state.holtcpcb_log with
      None -> ()
    | Some(log) -> destroy_log log in
  ();;


(* simple_post_test_cleanup handle test_run_state_simple = unit *)
(* Clean_up the current tthee run, close the trace output file and *)
(* increment the test sequence number by 1 *)
(* Used for tidying up simple test runs that were initialised by a *)
(* call to simple_pre_test_init() *)
let simple_post_test_cleanup handle test_state =
  let _ = simple_cleanup_tthee test_state in
  Unix.close test_state.out_fd;;

(* ---------------------------------------------------------------------- *)

let for_each_host_pair_and_test hosts tests f =
  List.iter  (* for each host pair *)
    (function (send, recv) ->
      (List.iter (f (send,recv)) tests) (* for each test we wish to perform *)
    ) hosts;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
