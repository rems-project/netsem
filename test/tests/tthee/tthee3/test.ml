open Tthee;;
open Ttheehelper;;
open Testscommon;;
open Libcalls;;
open Unix;;
open Platform;;
open Nettypes;;
open Holtypes;;
open Holparselib;;
open Ocamllib;;

exception Error_occured;;

let _ = set_debug_level debug_OFF in ();;

let my_priv_ip = thalamus_priv_ip in

(* Open a file for merge results *)
let out_fd = Unix.openfile "trace" [O_WRONLY; O_CREAT; O_TRUNC] 432 in
let out_ch = Unix.out_channel_of_descr out_fd in

(* Create merger *)
let merge_hnd = merger_create out_ch RAW in

(* Setup an initial_host *)
let initial_host = INITIAL_HOST_JOHN in

(* Initialise libd *)
let libd_log = create_fresh_log (string_ip my_priv_ip) in
let _ = merger_register_log merge_hnd libd_log None in

(* Initialise slurper *)
let slurp_log = create_fresh_log (string_ip my_priv_ip) in
let slurp_filter = create_filter john_priv_ip emil_priv_ip in
let slurp_hostip = Some(hol_ip (get_initial_host_ip initial_host)) in
let slurp_iface = "ep0" in
let _ = merger_register_log merge_hnd slurp_log None in

(* Initialise holtcpcb *)
let tcpcb_log = create_fresh_log (string_ip my_priv_ip) in
let _ = merger_register_log merge_hnd tcpcb_log None in

(* Start the merger *)
let merger_hdr_msg = "" in
merger_begin merge_hnd (Int64.of_int 1000000) merger_hdr_msg;

(* Create processes *)
let libd_hnd = libd_create john_remote (cmd_tcp_create john_priv_ip 5005) libd_log true true in
let merger_hdr_msg = (initial_host_to_string initial_host (uint 0) ARCH_BSD false []) ^
  "(* Injector: running on emil *)" in
merger_begin merge_hnd (Int64.of_int 1000000) merger_hdr_msg;
let slurp_hnd = slurper_create john_remote slurp_log slurp_iface slurp_filter slurp_hostip in
let tcpcb_hnd = holtcpcb_create john_remote tcpcb_log [AF_INPUT;AF_OUTPUT;AF_DROP;AF_USER] in

(* Make a libd call or two *)
let mylibcall = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
let ret1 = libd_call libd_hnd mylibcall in
let fd =
  match ret1 with
    (_, OK_FD(fd)) -> fd
  | _ -> raise Error_occured in
let mylibcall2 = (tid_of_int_private 0, CONNECT(fd, Ocamllib.ip_of_string (string_ip emil_priv_ip),
					  Some(Ocamllib.port_of_int 22))) in
let ret2 = libd_call libd_hnd mylibcall2 in


(* The spoofed connection has been accepted so lets send some data *)
(* let mylibcall = (tid_of_int_private 0, SEND(fd, None,"Hello sshd!", [])) in *)
(* let ret = libd_call libd_hnd mylibcall in *)

(* Make a close call *)
let mylibcall = (tid_of_int_private 0, CLOSE(fd)) in
let ret = libd_call libd_hnd mylibcall in


(* Delay until everything settles down *)
let _ = Thread.delay 10.00 in

(* Clear up before quiting *)
let _ = holtcpcb_destroy tcpcb_hnd in
let _ = slurper_destroy slurp_hnd in
let _ = libd_destroy libd_hnd in
let _ = merger_destroy merge_hnd in
();;
