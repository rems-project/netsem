(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Simple Test Helper Code                   *)
(* Steve Bishop - Created 20030503                                        *)
(* $Id: simple.mli,v 1.2 2005/09/27 10:32:41 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread;;
open Unix;;
open ThreadUnix;;

(* Our libraries *)
open Nettypes;;
open Netconv;;
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
(* Functions for creating and destroying simple test environments         *)
(* (libd, holtcpcb-v8 & slurper on send host and injector on recv host)   *)
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


(* simple_pre_test_init tthee_setup base_port = test_run_state_simple *)
(* Initialise tthee and start test processes on the test hosts using port base_port *)
val make_multipurpose_merger: string -> merger_handle
val simple_pre_test_init_with_merger: tthee_init_simple -> int -> merger_handle option -> test_run_state_simple
val simple_pre_test_init: tthee_init_simple -> int -> test_run_state_simple

val setup_preinit_state: test_run_state_simple -> preinit_state -> host_info ->
  Ttheehelper.ip option -> int option -> Ocamllib.fd;;

(* simple_cleanup_tthee test_run_state_simple = unit *)
(* Destroy all of the test tool processes by calling the relevant *)
(* tthee destroy function *)
val simple_cleanup_tthee: test_run_state_simple -> unit

(* simple_post_test_cleanup handle test_run_state_simple = unit *)
(* Clean_up the current tthee run, close the trace output file and *)
(* increment the test sequence number by 1 *)
val simple_post_test_cleanup: autotest_handle -> test_run_state_simple -> unit

(* ---------------------------------------------------------------------- *)

val for_each_host_pair_and_test:
    ('a * 'b) list -> 'c list -> ('a * 'b -> 'c -> unit) -> unit;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
