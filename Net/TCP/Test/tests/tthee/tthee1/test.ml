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

(* Define a bogus TCP segment ready for injection later *)
let tcp_seg =
  TCPMSG( {
	  is1 = Some (hol_ip john_priv_ip);
	  is2 = Some (hol_ip emil_priv_ip);
	  ps1 = Some (uint 9000);
	  ps2 = Some (uint 9000);
	  seq = uint 1000;
	  ack = uint 2000;
	  uRG = false;
	  aCK = true;
	  pSH = true;
	  rST = false;
	  sYN = false;
	  fIN = false;
	  win = uint 4096;
	  urp = uint 0;
	  mss = Some(uint 4096);
	  scale = None;
	  ts = None;
	  data = []
	}) in

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
let inj_hnd = injector_create john_remote (cmd_tcp_create john_priv_ip 5004) in
let libd_hnd = libd_create john_remote (cmd_tcp_create john_priv_ip 5005) libd_log true true in
let merger_hdr_msg = (initial_host_to_string initial_host (libd_getpid libd_hnd) ARCH_BSD false []) ^
  "(* Injector: running on emil *)" in
merger_begin merge_hnd (Int64.of_int 1000000) merger_hdr_msg;
let slurp_hnd = slurper_create john_remote slurp_log slurp_iface slurp_filter slurp_hostip in
let tcpcb_hnd = holtcpcb_create john_remote tcpcb_log [AF_INPUT;AF_OUTPUT;AF_DROP;AF_USER] in

(* Inject some packets *)
let _ = injector_inject inj_hnd tcp_seg in
(*let _ = injector_inject inj_hnd tcp_seg in
let _ = injector_inject inj_hnd tcp_seg in*)


(* Make a libd call or two *)
let mylibcall = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
let ret1 = libd_call libd_hnd mylibcall in
let mylibcall2 =
  match ret1 with
    (_,OK_FD(fd)) -> (tid_of_int_private 0,
		      CONNECT(fd, Ocamllib.ip_of_string (string_ip emil_priv_ip), Some(Ocamllib.port_of_int 22)))
  | _ -> raise Error_occured in
let ret2 = libd_call libd_hnd mylibcall2 in

(* Delay until everything settles down *)
let _ = Thread.delay 10.00 in

(* Clear up before quiting *)
let _ = holtcpcb_destroy tcpcb_hnd in
let _ = injector_destroy inj_hnd in
let _ = slurper_destroy slurp_hnd in
let _ = libd_destroy libd_hnd in
let _ = merger_destroy merge_hnd in
();;
