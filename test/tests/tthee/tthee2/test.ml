open Tthee;;
open Ttheehelper;;
open Testscommon;;
open Libcalls;;
open Unix;;
open Platform;;
open Nettypes;;
open Holtypes;;
open Holparselib;;
open Ocamllib

exception Error_occured;;

let _ = set_debug_level debug_MUT;;

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
let slurp_filter = create_filter john_priv_ip psyche_priv_ip in
let slurp_hostip = Some(hol_ip (get_initial_host_ip initial_host)) in
let slurp_iface = "ep0" in
let _ = merger_register_log merge_hnd slurp_log None in

(* Initialise holtcpcb *)
let tcpcb_log = create_fresh_log (string_ip my_priv_ip) in
let _ = merger_register_log merge_hnd tcpcb_log None in

(* Start the merger *)
let merger_hdr_msg = "" in
merger_begin merge_hnd (Int64.of_int 100000) merger_hdr_msg;

(* Create processes *)
let inj_hnd = injector_create emil_remote (cmd_tcp_create emil_priv_ip 5004) in
let libd_hnd = libd_create john_remote (cmd_tcp_create john_priv_ip 5005) libd_log true true in
let merger_hdr_msg = (initial_host_to_string initial_host (uint 0) ARCH_BSD false []) ^
  "(* Injector: running on emil *)" in
merger_begin merge_hnd (Int64.of_int 100000) merger_hdr_msg;
let slurp_hnd = slurper_create john_remote slurp_log slurp_iface slurp_filter slurp_hostip in
let tcpcb_hnd = holtcpcb_create john_remote tcpcb_log [AF_INPUT;AF_OUTPUT;AF_DROP;AF_USER] in

(* -------------------------------------------------------------------- *)
(* Do some tests *)
(* -------------------------------------------------------------------- *)

(* Fake up a TCP segment to try and connect to the listening socket *)
let base_port = 8006 in

let fake_syn_datagram =
  TCPMSG( {
	  is1 = Some (hol_ip psyche_priv_ip);
	  is2 = Some (hol_ip john_priv_ip);
	  ps1 = Some (uint 9000);
	  ps2 = Some (uint base_port);
	  seq = uint 1000;
	  ack = uint 2000;
	  uRG = false;
	  aCK = false;
	  pSH = false;
	  rST = false;
	  sYN = true;
	  fIN = false;
	  win = uint 4096;
	  urp = uint 0;
	  mss = Some(uint 4096);
	  scale = None;
	  ts = None;
	  data = []
	}) in

let partial_fake_datagram =
  {
   is1 = Some (hol_ip psyche_priv_ip);
   is2 = Some (hol_ip john_priv_ip);
   ps1 = Some (uint 9000);
   ps2 = Some (uint base_port);
   seq = uint 0;
   ack = uint 0;
   uRG = false;
   aCK = false;
   pSH = false;
   rST = false;
   sYN = false;
   fIN = false;
   win = uint 4096;
   urp = uint 0;
   mss = Some(uint 4096);
   scale = None;
   ts = None;
   data = []
 } in

(* Register a callback function for the slurper *)
(* This will look for a syn,ack packet and ack it *)
let slurper_callback msg =
  match msg with
    TCPMSG(m) -> (
      if (m.is1 = Some(hol_ip john_priv_ip)) &&
	 (m.is2 = Some(hol_ip psyche_priv_ip)) &&
	 (m.ps2 = Some(uint 9000)) &&
	 (m.sYN = true) && (m.aCK = true) then
	let fake_ack_datagram =
	  TCPMSG ( {partial_fake_datagram with seq=m.ack; ack=m.seq+.(uint 1);
		    aCK=true} ) in
	injector_inject inj_hnd fake_ack_datagram
      else if (m.is1 = Some(hol_ip john_priv_ip)) &&
	(m.is2 = Some(hol_ip psyche_priv_ip)) &&
	(m.ps2 = Some(uint 9000)) &&
	(m.fIN = true) then
	let fake_ack_datagram =
	  TCPMSG ( {partial_fake_datagram with seq=m.ack; ack=m.seq+.(uint 1);
		    aCK=true; fIN=true } ) in
	injector_inject inj_hnd fake_ack_datagram
      else
	()
     )
  | _ -> () in
let slurper_cb_hnd = slurper_register_callback slurp_hnd slurper_callback in

(* Make a socket() call *)
let mylibcall = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
let ret = libd_call libd_hnd mylibcall in

(* Recover the sockets fd *)
let fd =
  match ret with
    (_,OK_FD(fd)) -> fd
  | _ -> raise Error_occured in

let mylibcall = (tid_of_int_private 0, SETSOCKBOPT(fd, Ocamllib.SO_REUSEADDR, true)) in
let _ = libd_call libd_hnd mylibcall in

(* Bind the socket to an ip and port *)
let mylibcall = (tid_of_int_private 0,
		 BIND(fd, Some(Ocamllib.ip_of_string (string_ip john_priv_ip)),
		      Some(Ocamllib.port_of_int base_port))) in
let ret = libd_call libd_hnd mylibcall in

(* Put the socket into listening mode *)
let mylibcall = (tid_of_int_private 0, LISTEN(fd, 1)) in
let ret = libd_call libd_hnd mylibcall in

(* Insert a fake SYN packet to try and connect to the listening socket *)
let _ = injector_inject inj_hnd fake_syn_datagram in

(* Let the socket accept the connection *)
let mylibcall = (tid_of_int_private 0, ACCEPT(fd)) in
let ret = libd_call libd_hnd mylibcall in
let connfd =
  match ret with
    (_,OK_FD_IP_PORT(fd,_)) -> fd
  | _ -> raise Error_occured in

(* The spoofed connection has been accepted so lets send some data *)
let mylibcall = (tid_of_int_private 0, SEND(connfd, None,"Hello evil psyche", [])) in
let ret = libd_call libd_hnd mylibcall in

(* The tcp stack on john will then reply with a SYN,ACK if all went well *)
(* The slurper registered callback function above will get this and send *)
(* out an ACK packet to set up the connection (hopefully!) *)

(* Make a close call *)
let mylibcall = (tid_of_int_private 0, CLOSE(connfd)) in
let ret = libd_call libd_hnd mylibcall in
let mylibcall = (tid_of_int_private 0, CLOSE(fd)) in
let ret = libd_call libd_hnd mylibcall in


(* -------------------------------------------------------------------- *)


(* Delay until everything settles down *)
let _ = Thread.delay 2.00 in

(* Clear up before quiting *)
let _ = holtcpcb_destroy tcpcb_hnd in
let _ = slurper_destroy slurp_hnd in
let _ = libd_destroy libd_hnd in
let _ = injector_destroy inj_hnd in
let _ = merger_destroy merge_hnd in ();;
