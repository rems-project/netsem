(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Dual Tests Helper Code                          *)
(* Steve Bishop - Created 20030504                                        *)
(* $Id: dual.mli,v 1.9 2006/08/17 10:28:25 tjr22 Exp $                  *)
(* ---------------------------------------------------------------------- *)

(* Our libraries *)
open Ocamllib;;
open Tthee;;
open Ttheehelper;;
open Testscommon;;
open Nettypes
open Common;;

(* ---------------------------------------------------------------------- *)
(* Dual-host Tthee initialisation and shutdown functions                  *)
(* ---------------------------------------------------------------------- *)

(* ((libd,libd is privileged),slurper,holtcpcb-v8,injector) *)
type tool_select = (bool * bool) * bool * bool * bool;;

type named_tool_select = { libd: bool; libd_is_p: bool; slurper: bool; holtcpcb: bool; injector: bool}

val nts_to_ts: named_tool_select -> tool_select


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

val tcpcb_update_win: dual_test_state -> Nettypes.ip option -> Nettypes.ip option ->
  Nettypes.port option -> Nettypes.port option -> uint -> unit

val tcpcb_get_win: dual_test_state -> Nettypes.ip option -> Nettypes.ip option ->
  Nettypes.port option -> Nettypes.port option -> uint

(* ---------------------------------------------------------------------- *)

(* dual_thhee_init tthee_init_dual debug_level baseport_1 baseport_2 *)
(* merger_delta_value = dual_test_state                              *)
(* Startup tthee and test tools described by tthee_init_dual, with   *)
(* debug_level, merging delta set to merger_delta_value and using    *)
(* baseport_1 and baseport_2 as the lower values for command channel *)
(* port numbering *)
val dual_tthee_init: tthee_init_dual -> int -> int -> int -> int ->
  dual_test_state;;

(* dual_tthee_cleanup dual_test_state = unit *)
(* Clean up the dual test run by killing all test processes, stopping Tthee, *)
(* deleting all log channels and closing open descriptors *)
val dual_tthee_cleanup: dual_test_state -> unit;;

(* ---------------------------------------------------------------------- *)

val the: 'a option -> 'a;;

val lift: ('a -> unit) -> 'a option -> unit;;

(* ---------------------------------------------------------------------- *)

val dual_second_th_libd_create: dual_test_state -> tthee_init_dual -> int ->
  log_handle * libd_handle

val dual_second_th_libd_kill: libd_handle -> log_handle -> unit

val clearup_libd_list: (log_handle * libd_handle) list -> unit

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)

