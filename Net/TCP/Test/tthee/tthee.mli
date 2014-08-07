(* Netsem TThee -- TCP Testing (host) Executive Engine  *)
(* Keith Wansbrough/Steve Bishop -- Created 20021210     *)
(* $Id: tthee.mli,v 1.27 2006/08/17 11:29:13 tjr22 Exp $ *)

open Nettypes;;
open Holtypes;;
open Parserlib;;
open Holparselib;;

(* ------------------------------------------------------- *)
(* HEALTH WARNING: This library's support for libd_call    *)
(* and libd_call_asyn is not thread-safe.  DO NOT          *)
(* use from multiple concurrent threads within the same    *)
(* process or be prepared to face the consequences!        *)
(* ------------------------------------------------------- *)

(* ---------- *)
(* Debugging  *)
(* ---------- *)
val set_debug_level: int -> unit;;
val debug_OFF: int;;
val debug_MSG: int;;
val debug_FUN: int;;
val debug_VER: int;;
val debug_MUT: int;;

(* ---------- *)
(* Common     *)
(* ---------- *)

type log_handle;;
type log_callback_handle;;

type sock_type =
    TCP of ip * port
  | UNIX of string;;

exception TThee_fatal of string;;
exception Invalid_log_callback_handle of string * log_callback_handle;;

val ip_of_ints: int -> int -> int -> int -> ip;;
val port_of_int: int -> uint;;

(* ---------- *)
(* Executor   *)
(* ---------- *)

(* These strings should be fully qualifed path names *)
(* e.g. /TCP/Test/slurp/slurp *)
type exec_paths = {
    libd_path : string;
    slurp_path : string;
    injector_path : string;
    holtcpcb_path : string;
    mirror_path : string;
  } ;;

type rsh_client =
    SSH of string          (* path of ssh client *)
  | CUSTOM_RSH of int      (* port of listening CUSTOM_RSH daemon *)
;;

type exec_params =
    LOCAL of exec_paths
  | REMOTE of string * rsh_client * exec_paths;;

type exec_program =
    EXEC_LIBD
  | EXEC_SLURP
  | EXEC_INJECTOR
  | EXEC_HOLTCPCB
  | EXEC_MIRROR
  | EXEC_TSCAL (* for WinXP only *);;


(* ---------- *)
(* Log mgmt   *)
(* ---------- *)

(* create_fresh_log bindip = handle *)
(* Create a fresh listening log (socket) and register with selector *)
val create_fresh_log: string -> log_handle;;

(* destroy_log handle = unit *)
(* Destroy a log channel once it is finished with *)
val destroy_log: log_handle -> unit;;

(* ---------- *)
(* Merger     *)
(* ---------- *)

type merger_handle;;

type merger_output_mode =
    RAW
  | HOLDEF;;

exception Merger_invalid_handle of string * merger_handle;;
exception Merger_deregister_failed of string;;
exception Merger_fatal of string;;
exception Merger_done;;
exception Merger_continue_loop;;

(* merger_create: out_channel = handle *)
(* Create a new merger thread outputting to out_channel *)
val merger_create: out_channel -> merger_output_mode -> merger_handle;;

(* merger_register_log handle log_handle out_channel_option = unit *)
(* Register a specific log with the merger referenced by handle *)
(* and  with optional echo to out_channel out_channel_option *)
val merger_register_log: merger_handle -> log_handle -> out_channel option -> unit;;
val merger_register_named_log: merger_handle -> log_handle -> out_channel option -> string option -> unit;;

(* merger_deregister_log handle log_handle = unit *)
(* Unregister log_handle from the merger referenced by handle *)
val merger_deregister_log: merger_handle -> log_handle -> unit;;

(* merger_begin handle delta hdr_string = unit *)
(* Starts the merger process once all logs have been registered *)
(* Delta is the per-thread merger delay *)
(* Hdr_string is any custom string that needs to be written *)
(* to the merger file header *)
val merger_begin: merger_handle -> uint -> string -> unit;;

(* merger_destroy handle = unit *)
(* Destroy the merger referenced by handle. This unregisters all *)
(* the callbacks registered with the referenced merger first to ensure *)
(* things terminate nicely *)
val merger_destroy: merger_handle -> unit;;

(* ---------- *)
(* Libd       *)
(* ---------- *)

type libd_handle;;

exception Libd_hard_fail of string;;
exception Libd_invalid_handle of string * libd_handle;;
exception Libd_kill_failed of string * int * exec_params;;

(* libd_create exec_params cmd_channel log_channel tcp_debug privileged = handle *)
(* Create a new libd daemon *)
val libd_create: exec_params -> sock_type -> log_handle -> bool -> bool -> libd_handle;;

(* libd_getpid handle = int *)
(* Get the remote-end pid of the remote libd process *)
val libd_getpid: libd_handle -> uint;;

(* #################################### *)
(* You must only call libd_call and     *)
(* libd_call_async from a single thread *)
(* (the same single thread) as they are *)
(* not thread-safe                      *)
(* #################################### *)
(* libd_call handle libcall = libreturn *)
(* Make a LIB call via the referenced libd daemon and wait for the return *)
val libd_call: libd_handle -> libcall -> libreturn;;

(* libd_call handle libcall = unit *)
(* Make a LIB call via the referenced libd daemon and don't wait *)
val libd_call_async: libd_handle -> libcall -> unit;;
(* #################################### *)


(* libd_destroy handle = unit *)
(* Destroy the referenced libd daemon *)
val libd_destroy: libd_handle -> unit;;

(* ---------- *)
(* Injector   *)
(* ---------- *)

type injector_handle;;

exception Injector_hard_fail of string;;
exception Injector_invalid_handle of string * injector_handle;;
exception Injector_kill_failed of string * int * exec_params;;

(* injector_create: exec_params cmd_channel = handle *)
(* Create a new injector daemon *)
val injector_create: exec_params -> sock_type -> injector_handle;;

(* injector_inject handle hol_datagram = unit *)
(* Inject a HOL record datagram via the referenced daemon *)
val injector_inject: injector_handle -> holmsg -> unit;;

(* injector_destroy handle = unit *)
(* Destroy the referenced injector daemon *)
val injector_destroy: injector_handle -> unit;;

(* ---------- *)
(* Slurper    *)
(* ---------- *)

type slurper_handle;;
type slurper_callback_handle;;

exception Slurper_invalid_handle of string * slurper_handle;;
exception Slurper_kill_failed of string * int * exec_params;;
exception Slurper_invalid_callback_handle of string * slurper_callback_handle;;
exception Slurper_callback_handle_mismatch of string * slurper_handle * slurper_callback_handle;;

(* slurper_create exec_params log_channel iface filter hostip = handle *)
(* Create a new slurper daemon *)
(*  iface is the interface to sniff on *)
(*  log_channel specifies the socket to output HOL labels to *)
(*  filter is an optional filter string *)
(*  hostip if set specifies the ip address of the sending host *)
val slurper_create: exec_params -> log_handle -> string -> string option -> ip option -> slurper_handle;;

(* slurper_register_callback handle callback = slurper_callback_handle *)
(* Register a new callback with log channel for the *)
(* slurper referenced by handle *)
val slurper_register_callback: slurper_handle -> (holmsg -> unit) -> slurper_callback_handle;;

(* slurper_deregister_callback handle callback_handle = unit *)
(* Unregister the given callback *)
val slurper_deregister_callback: slurper_handle -> slurper_callback_handle -> unit;;

(* slurper_destroy handle = unit *)
(* Destroy the referenced slurper daemon *)
val slurper_destroy: slurper_handle -> unit;;

(* ---------- *)
(* Holtcpcb   *)
(* ---------- *)

type holtcpcb_handle;;
type holtcpcb_callback_handle;;

type action_flag =
    AF_INPUT
  | AF_OUTPUT
  | AF_DROP
  | AF_USER;;

exception Holtcpcb_invalid_action_mask of string * int;;
exception Holtcpcb_invalid_handle of string * holtcpcb_handle;;
exception Holtcpcb_kill_failed of string * int * exec_params;;
exception Holtcpcb_invalid_callback_handle of string * holtcpcb_callback_handle;;
exception Holtcpcb_callback_handle_mismatch of string * holtcpcb_handle * holtcpcb_callback_handle;;

(* holtcpcb_create exec_params log_channel action_mask = handle *)
(* Create a new holtcpcb daemon *)
(*  log_channel is the channel to log HOL trace messages to *)
(*  action_mask is the set of events to trace *)
val holtcpcb_create: exec_params -> log_handle -> action_flag list -> holtcpcb_handle;;

(* holtcpcb_register_callback handle callback = holtcpcb_callback_handle *)
(* Register a new callback function with the holtcpcb instances log *)
val holtcpcb_register_callback: holtcpcb_handle -> (tcptrace -> unit) -> holtcpcb_callback_handle;;

(* holtcpcb_deregister_callback handle callback_handle = unit *)
(* Unregister a callback *)
val holtcpcb_deregister_callback: holtcpcb_handle -> holtcpcb_callback_handle -> unit;;

(* holtcpcb_destroy handle = unit *)
(* Destroy the referenced holtcpcb daemon *)
val holtcpcb_destroy: holtcpcb_handle -> unit;;

(* ------ *)
(* Mirror *)
(* ------ *)

type mirror_handle;;

(* mirror_create exec_params iface rewritelist = handle *)
(* Create a new magic mirror *)
(*  iface is the interface to reflect on *)
(*  rewritelist is a list of ip address strings (can't use Ttheehelper.ip because of dependencies) *)
(*  opts is an optional list of argument strings *)
val mirror_create: exec_params -> log_handle -> string -> string list -> string list option -> mirror_handle;;

(* mirror_destroy handle = unit *)
(* Break the magic mirror *)
val mirror_destroy: mirror_handle -> unit;;

(* re-calibrate time on WinXP *)
val tsccal_start: int -> int -> unit
(* ---------- *)
(* End        *)
(* ---------- *)
