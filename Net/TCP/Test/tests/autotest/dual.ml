(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Dual Tests Helper Code                          *)
(* Steve Bishop - Created 20030504                                        *)
(* $Id: dual.ml,v 1.25 2006/08/17 10:28:25 tjr22 Exp $                  *)
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
(* Dual-host Tthee initialisation and shutdown functions                  *)
(* ---------------------------------------------------------------------- *)

(* ((libd,libd is privileged),slurper,holtcpcb-v8,injector) *)
type tool_select = (bool * bool) * bool * bool * bool;;

type named_tool_select = { libd: bool; libd_is_p: bool; slurper: bool; holtcpcb: bool; injector: bool}

let nts_to_ts { libd= libd; libd_is_p= libd_is_p; slurper= slurper; holtcpcb= holtcpcb; injector= injector} =
  (libd, libd_is_p),slurper,holtcpcb,injector;;

type tthee_init_dual = {
    tthee_host: Ttheehelper.ip;        (* IP of tthee control host *)
    virtual_host_ip: Ttheehelper.ip;   (* IP of the test virtual host *)
    virtual_host_port: int;            (* Port to use for connections to virtual host *)
    seq_fname: string;                 (* Unique trace filename *)
    test_descr: string;                (* Description of test *)

    (* Test Host *)
    test_host: host_info;              (* Test host *)
    test_host_tools: tool_select;      (* Tools to run on test host *)
    test_host_bound:                   (* Existing bound ports on test host *)
      (Ocamllib.ip option * int) list;

    (* Auxillary host *)
    aux_host: host_info;               (* Auxillary host *)
    aux_host_tools: tool_select;       (* Tools to run on auxillary host *)
    aux_host_bound:                    (* Existing bound ports on auxillary host *)
      (Ocamllib.ip option * int) list;
  };;

type virtual_tcpcb = Nettypes.ip option * Nettypes.ip option * Nettypes.port option *
      Nettypes.port option * uint

type dual_test_state = {
    (* Test host tool handles *)
    th_libd_hnd     : libd_handle option;
    th_slurper_hnd  : slurper_handle option;
    th_injector_hnd : injector_handle option;
    th_holtcpcb_hnd : holtcpcb_handle option;

    (* Auxillary host tool handles *)
    ah_libd_hnd     : libd_handle option;
    ah_slurper_hnd  : slurper_handle option;
    ah_injector_hnd : injector_handle option;
    ah_holtcpcb_hnd : holtcpcb_handle option;

    (* Test host log and merger handles *)
    th_out_fd       : Unix.file_descr;
    th_out_ch       : out_channel;
    th_merge_hnd    : merger_handle;
    th_libd_log     : log_handle option;
    th_slurper_log  : log_handle option;
    th_holtcpcb_log : log_handle option;

    (* Auxillary host log and merger handles *)
    ah_out_fd_opt    : Unix.file_descr option;
    ah_out_ch_opt    : out_channel option;
    ah_merge_hnd_opt : merger_handle option;
    ah_libd_log      : log_handle option;
    ah_slurper_log   : log_handle option;
    ah_holtcpcb_log  : log_handle option;

    (* Virtual host *)
    tcpcb_list: virtual_tcpcb list ref;
  };;

(* ---------------------------------------------------------------------- *)

let tcpcb_update_win ts is1 is2 ps1 ps2 win =
  let found =
    try
      List.exists
	(function (i1,i2,p1,p2,w) ->
	if i1 = is1 && i2 = is2 && p1 = ps1 && p2 = ps2 then
	  true
	else
	  false
	) !(ts.tcpcb_list)
    with Not_found -> false in
  ts.tcpcb_list :=
    if found then
      List.map
	(function (i1,i2,p1,p2,w) ->
	  if i1 = is1 && i2 = is2 && p1 = ps1 && p2 = ps2 then
	    (i1,i2,p1,p2,win)
	  else
	    (i1,i2,p1,p2,w)
	) !(ts.tcpcb_list)
    else
      (is1,is2,ps1,ps2,win)::!(ts.tcpcb_list)

let tcpcb_get_win ts is1 is2 ps1 ps2 =
  let (_,_,_,_,win) =
    List.find
      (function (i1,i2,p1,p2,w) ->
	if i1 = is1 && i2 = is2 && p1 = ps1 && p2 = ps2 then
	  true
	else
	  false
      ) !(ts.tcpcb_list) in
  win

(* ---------------------------------------------------------------------- *)

(* True is one of libd, slurper or holtcpcb is set to run *)
let require_merger tool_select =
  match tool_select with
    ((l, _), s, h, i) -> l || s || h;;

let the a_opt =
  match a_opt with
    None -> raise (Assertion_failed("Should not get a None in `Dual.the` function"))
  | Some(x) -> x;;

(* The standard lift functor *)
let lift f opt_type =
  match opt_type with
    None -> ()
  | Some(x) -> f x;;

(* dual_thhee_init tthee_init_dual debug_level baseport_1 baseport_2 *)
(* merger_delta_value = dual_test_state                              *)
(* Startup tthee and test tools described by tthee_init_dual, with   *)
(* debug_level, merging delta set to merger_delta_value and using    *)
(* baseport_1 and baseport_2 as the lower values for command channel *)
(* port numbering *)
let dual_tthee_init id debug baseport_1 baseport_2 merger_delta =
  let _ = set_debug_level debug in
  let th_out_fd = Unix.openfile id.seq_fname [O_WRONLY; O_CREAT; O_TRUNC] 432 in
  let th_out_ch = Unix.out_channel_of_descr th_out_fd in
  let initial_host = id.test_host.hol_initial_host in
  let not_initial_host = id.aux_host.hol_initial_host in

  (* Write out host and test description to trace file *)
  let host1 = (platform_to_string id.test_host.platform_type) ^ "(" ^
    id.test_host.host_name ^ ")" in
  let host2 = (platform_to_string id.aux_host.platform_type) ^ "(" ^
    id.aux_host.host_name ^ ")" in
  output_string th_out_ch ("(* Test Host: " ^ host1 ^ "  Aux Host: " ^ host2 ^ " *)\n");
  output_string th_out_ch ("(* Test Description: " ^ id.test_descr ^ " *)\n\n");

  (* Create the mergers *)
  let th_merge_hnd = merger_create th_out_ch RAW in
  let (ah_out_fd_opt, ah_out_ch_opt, ah_merge_hnd_opt) =
    if (require_merger id.aux_host_tools) then
      let fd = Unix.openfile (id.seq_fname ^ ".aux") [O_WRONLY; O_CREAT; O_TRUNC] 432 in
      let ch = Unix.out_channel_of_descr fd in
      (Some fd, Some ch, Some(merger_create ch RAW))
    else
      None, None, None in

  (* Some useful values *)
  let th_exec = id.test_host.ns_tools_exec_params in
  let ah_exec = id.aux_host.ns_tools_exec_params in
  let th_test_ip = id.test_host.test_ip_address in
  let ah_test_ip = id.aux_host. test_ip_address in

  (* Tools we want to start on hosts *)
  let ((tl, tlp), ts, th, ti) = id.test_host_tools in
  let ((al, alp), auxs, ah, ai) = id.aux_host_tools in
  let tlp = if (id.test_host.platform_type = ARCH_WINXP) then true else tlp in

  (* --------------------------------------------------------- *)
  (* Create logs and start processes relating to the test host *)
  (* --------------------------------------------------------- *)
  let th_libd_log =
    if tl then
      let log = create_fresh_log (string_ip id.tthee_host) in
      let _ = merger_register_log th_merge_hnd log None in
      Some log
    else
      None in
  let th_slurper_log =
    if ts then
      let log = create_fresh_log (string_ip id.tthee_host) in
      let _ = merger_register_log th_merge_hnd log None in
      Some log
    else
      None in
  let th_holtcpcb_log =
    if th && id.test_host.host_supports_holtcpcb then
      let log = create_fresh_log (string_ip id.tthee_host) in
      let _ = merger_register_log th_merge_hnd log None in
      Some log
    else
      None in
  merger_begin th_merge_hnd (Int64.of_int merger_delta) "";

  (* Create libd *)
  let th_libd_hnd =
    if tl then
      Some(libd_create th_exec (cmd_tcp_create th_test_ip baseport_1)
	     (the th_libd_log) id.test_host.host_supports_holtcpcb tlp)
    else
      None in

  (* Create the initial_host_header which depends upon the libd remote pid *)
  let merger_hdr_msg =
    let libd_pid = match th_libd_hnd with
      None -> uint 0
      | Some h -> libd_getpid h in
    (initial_host_to_string initial_host libd_pid
       (id.test_host.platform_type) tlp id.test_host_bound) ^
    (if ai then
      "(* Injector: running on " ^ (print_initial_host_name id.aux_host.hol_initial_host) ^ " *)"
    else "(* Injector: not running *)") in

  (* Call merger_begin again to update the header message *)
  merger_begin th_merge_hnd (Int64.of_int merger_delta) merger_hdr_msg;

  (* Create slurper, injector and holtcpcb-v8 if required *)
  let th_slurper_hnd =
    if ts then
      let slurp_filter = create_virtual_filter th_test_ip ah_test_ip id.virtual_host_ip
	  broadcast_ip multicast_ip unused_ip in
      let slurp_hostip = Some(hol_ip (get_initial_host_ip initial_host)) in
      (*let slurp_iface = id.test_host.iface_name in
      Some(slurper_create th_exec (the th_slurper_log) slurp_iface slurp_filter slurp_hostip) *)
      (if (id.test_host.platform_type != ARCH_WINXP) then
	let slurp_iface = id.test_host.iface_name in
	Some(slurper_create th_exec (the th_slurper_log) slurp_iface slurp_filter slurp_hostip)
      else
	let slurp_iface = id.aux_host.iface_name in
	Some(slurper_create ah_exec (the th_slurper_log) slurp_iface slurp_filter slurp_hostip))
    else
      None in
  let th_injector_hnd =
    if ai then
      Some(injector_create ah_exec (cmd_tcp_create ah_test_ip (baseport_1 + 1)))
    else
      None in
  let th_holtcpcb_hnd =
    if th && id.test_host.host_supports_holtcpcb then
      Some(holtcpcb_create th_exec (the th_holtcpcb_log) [AF_INPUT;AF_OUTPUT;AF_DROP;AF_USER])
    else
      None in

  (* --------------------------------------------------------- *)
  (* Create logs and start processes relating to the aux host  *)
  (* --------------------------------------------------------- *)
  let ah_libd_log =
    if al then
      let log = create_fresh_log (string_ip id.tthee_host) in
      let _ = merger_register_log (the ah_merge_hnd_opt) log None in
      Some log
    else
      None in
  let ah_slurper_log =
    if auxs && not(ts && (id.test_host.platform_type = ARCH_WINXP)) then
      let log = create_fresh_log (string_ip id.tthee_host) in
      let _ = merger_register_log (the ah_merge_hnd_opt) log None in
      Some log
    else
      None in
  let ah_holtcpcb_log =
    if ah && id.aux_host.host_supports_holtcpcb then
      let log = create_fresh_log (string_ip id.tthee_host) in
      let _ = merger_register_log (the ah_merge_hnd_opt) log None in
      Some log
    else
      None in

  lift (function hnd -> merger_begin hnd (Int64.of_int merger_delta) "") ah_merge_hnd_opt;

  (* Create libd *)
  let ah_libd_hnd =
    if al then
      Some(libd_create ah_exec (cmd_tcp_create ah_test_ip baseport_2)
	     (the ah_libd_log) id.aux_host.host_supports_holtcpcb alp)
    else
      None in

  (* Create the initial_host_header which depends upon the libd remote pid *)
  let merger_hdr_msg =
    match ah_merge_hnd_opt with
      None -> ""
    | Some(_) ->
	(let libd_pid = match ah_libd_hnd with
    None -> uint 0
    | Some h -> libd_getpid h in
  initial_host_to_string not_initial_host libd_pid
	   (id.aux_host.platform_type) alp id.aux_host_bound) ^
	(if ti then
	  "(* Injector: running on " ^ (print_initial_host_name id.test_host.hol_initial_host) ^ "*)"
	else "(* Injector: not running *)") in

  (* Call merger_begin again to update the header message *)
  lift (function hnd -> merger_begin hnd (Int64.of_int merger_delta) merger_hdr_msg) ah_merge_hnd_opt;

  (* Create slurper, injector and holtcpcb-v8 if required *)
  let ah_slurper_hnd =
    if auxs && not(ts && (id.test_host.platform_type = ARCH_WINXP)) then
      let slurp_filter = create_filter ah_test_ip th_test_ip in
      let slurp_hostip = Some(hol_ip (get_initial_host_ip not_initial_host)) in
      let slurp_iface = id.aux_host.iface_name in
      Some(slurper_create ah_exec (the ah_slurper_log) slurp_iface slurp_filter slurp_hostip)
    else
      None in
  let ah_injector_hnd =
    if ti then
      Some(injector_create th_exec (cmd_tcp_create th_test_ip (baseport_2 + 1)))
    else
      None in
  let ah_holtcpcb_hnd =
    if ah  && id.aux_host.host_supports_holtcpcb then
      Some(holtcpcb_create ah_exec (the ah_holtcpcb_log) [AF_INPUT;AF_OUTPUT;AF_DROP;AF_USER])
    else
      None in

  (* -------------------------------------------- *)
  (* Create and return the dual_test_state record *)
  (* -------------------------------------------- *)
  {
   th_libd_hnd = th_libd_hnd;
   th_slurper_hnd = th_slurper_hnd;
   th_injector_hnd = th_injector_hnd;
   th_holtcpcb_hnd = th_holtcpcb_hnd;

   ah_libd_hnd = ah_libd_hnd;
   ah_slurper_hnd  = ah_slurper_hnd;
   ah_injector_hnd = ah_injector_hnd;
   ah_holtcpcb_hnd = ah_holtcpcb_hnd;

   th_out_fd = th_out_fd;
   th_out_ch = th_out_ch;
   th_merge_hnd = th_merge_hnd;
   th_libd_log = th_libd_log;
   th_slurper_log = th_slurper_log;
   th_holtcpcb_log = th_holtcpcb_log;

   ah_out_fd_opt = ah_out_fd_opt;
   ah_out_ch_opt = ah_out_ch_opt;
   ah_merge_hnd_opt = ah_merge_hnd_opt;
   ah_libd_log = ah_libd_log;
   ah_slurper_log = ah_slurper_log;
   ah_holtcpcb_log = ah_holtcpcb_log;

   tcpcb_list = ref []
  };;

(* ---------------------------------------------------------------------- *)

(* dual_tthee_cleanup dual_test_state = unit *)
(* Clean up the dual test run by killing all test processes, stopping Tthee, *)
(* deleting all log channels and closing open descriptors *)
let dual_tthee_cleanup ts =
  let _ = Thread.delay !test_quiet_period in
  ignore(lift holtcpcb_destroy ts.ah_holtcpcb_hnd);
  ignore(lift injector_destroy ts.th_injector_hnd);
  ignore(lift slurper_destroy ts.ah_slurper_hnd);
  ignore(lift libd_destroy ts.ah_libd_hnd);
  ignore(lift merger_destroy ts.ah_merge_hnd_opt);
  ignore(lift destroy_log ts.ah_libd_log);
  ignore(lift destroy_log ts.ah_slurper_log);
  ignore(lift destroy_log ts.ah_holtcpcb_log);

  ignore(lift holtcpcb_destroy ts.th_holtcpcb_hnd);
  ignore(lift injector_destroy ts.ah_injector_hnd);
  ignore(lift slurper_destroy ts.th_slurper_hnd);
  ignore(lift libd_destroy ts.th_libd_hnd);
  ignore(merger_destroy ts.th_merge_hnd);
  ignore(lift destroy_log ts.th_libd_log);
  ignore(lift destroy_log ts.th_slurper_log);
  ignore(lift destroy_log ts.th_holtcpcb_log);

  let _ = Thread.delay !test_quiet_period in
  ignore(Unix.close ts.th_out_fd);
  ignore(lift (Unix.close) ts.ah_out_fd_opt);;

(* ---------------------------------------------------------------------- *)

let dual_second_th_libd_create ts id baseport =
  let libd_log = create_fresh_log (string_ip id.tthee_host) in
  let _ = merger_register_log ts.th_merge_hnd libd_log None in
  let libd_hnd = libd_create id.test_host.ns_tools_exec_params
       (cmd_tcp_create id.test_host.test_ip_address baseport) libd_log false false in
  (libd_log, libd_hnd)

let dual_second_th_libd_kill libd_hnd libd_log =
  libd_destroy libd_hnd;
  destroy_log libd_log

let rec clearup_libd_list libd_list =
  match libd_list with
    [] -> ()
  | (logh, libdh)::xs ->
      libd_destroy libdh;
      destroy_log logh;
      clearup_libd_list xs

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)

