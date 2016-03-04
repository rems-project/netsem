open Tthee;;
open Ttheehelper;;
open Testscommon;;
open Libcalls;;
open Unix;;
open Platform;;
open Nettypes;;
open Holtypes;;
open Holparselib;;

exception Error_occured;;

let _ = set_debug_level debug_MUT in ();;

let my_priv_ip = thalamus_priv_ip in

(* Open a file for merge results *)
let out_fd = Unix.openfile "test_output" [O_WRONLY; O_CREAT; O_TRUNC] 432 in
let out_ch = Unix.out_channel_of_descr out_fd in

(* Create merger *)
let merge_hnd = merger_create out_ch RAW in

(* Initialise libd *)
let libd_log = create_fresh_log (string_ip my_priv_ip) in
let _ = merger_register_log merge_hnd libd_log None in

(* Initialise slurper *)
let slurp_log = create_fresh_log (string_ip my_priv_ip) in
let slurp_filter = Some("port 1234") in
let slurp_hostip = Some(hol_ip thalamus_real_ip) in
let slurp_iface = "ep0" in
let _ = merger_register_log merge_hnd slurp_log None in

(* Start the merger *)
let _ = merger_begin merge_hnd (Int64.of_int 100000) in

(* Create processes *)
let libd_hnd = libd_create local_ep (cmd_tcp_create thalamus_priv_ip 5005) libd_log false in
let slurp_hnd = slurper_create john_remote slurp_log slurp_iface slurp_filter slurp_hostip in

(* -------------------------------------------------------------------- *)
(* Do some tests *)
(* -------------------------------------------------------------------- *)

(* Make a socket() call *)
let mylibcall = (Int64.of_int 0, SOCKET(SOCK_STREAM)) in
let ret = libd_call libd_hnd mylibcall in

(* Recover the sockets fd *)
let fd =
  match ret with
    (_,OK_FD(fd)) -> fd
  | _ -> raise Error_occured in

(* Bind the socket to an ip and port *)
let mylibcall = (Int64.of_int 0,
		 BIND(fd, Some(Ocamllib.ip_of_string (string_ip thalamus_real_ip )),
		      Some(Ocamllib.port_of_int 1234))) in
let ret = libd_call libd_hnd mylibcall in

let mylibcall = (Int64.of_int 0,
		 CONNECT(fd, Ocamllib.ip_of_string (string_ip john_priv_ip), Some(Ocamllib.port_of_int 1234))) in
let ret2 = libd_call libd_hnd mylibcall in

let mylibcall = (Int64.of_int 0, CLOSE(fd)) in
let ret = libd_call libd_hnd mylibcall in


(* -------------------------------------------------------------------- *)


(* Delay until everything settles down *)
let _ = Thread.delay 2.00 in

(* Clear up before quiting *)
let _ = slurper_destroy slurp_hnd in
let _ = libd_destroy libd_hnd in
let _ = merger_destroy merge_hnd in ();;
