(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Dual Tests TCP State Driver Code                *)
(* Steve Bishop - Created 20030505                                        *)
(* $Id: dualdriven.ml,v 1.28 2006/06/16 11:45:47 amgb2 Exp $          *)
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
open Holtypes;;
open Holparselib;;
open Tthee;;
open Ttheehelper;;
open Libcalls;;
open Testscommon;;
open Common;;
open Dual;;

exception Drive_Failure of string;;

(* ---------------------------------------------------------------------- *)

let get_bound_state th_libd fd =
  let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
  ignore(libd_call th_libd sn_call);
  let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
  ignore(libd_call th_libd pn_call);;

(* ---------------------------------------------------------------------- *)

(* Get new socket on host *)
let get_socket libd_hnd =
  let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
  match libd_call libd_hnd socket_call with
    (_, OK_FD(fd)) -> fd
  | _ -> raise(Drive_Failure("get_socket() failed"));;

(* Get new bound socket on host *)
let get_local_bound_socket libd_hnd ips ps =
  let fd = get_socket libd_hnd in
  let bind_call = (tid_of_int_private 0, BIND(fd, ips, ps)) in
  ignore(libd_call libd_hnd bind_call);
  get_bound_state libd_hnd fd;
  fd;;

(* Get an autobound, connected socket on host *)
let get_autobound_connected_socket libd_hnd ip port =
  let fd = get_socket libd_hnd in
  let connect_call = (tid_of_int_private 0, CONNECT(fd, ip, Some(port))) in
  ignore(libd_call libd_hnd connect_call);
  get_bound_state libd_hnd fd;
  fd;;

(* Get a non-auto bound, connected socket on host *)
let get_local_bound_connected_socket libd_hnd ips ps ip port =
  let fd = get_local_bound_socket libd_hnd ips ps in
  let connect_call = (tid_of_int_private 0, CONNECT(fd, ip, Some(port))) in
  ignore(libd_call libd_hnd connect_call);
  get_bound_state libd_hnd fd;
  fd;;

(* ---------------------------------------------------------------------- *)
(* Create socket and drive to a TCP state transition diagram style state  *)
(* ---------------------------------------------------------------------- *)

(* The state of a TCP connection wrt whether it has sent *)
(* or received data or not *)
type tcp_data_status =
    NO_DATA
  | DATA_SENT
  | DATA_RCVD
  | DATA_SENT_RCVD;;

(* The last datagram seen on the wire (and whether it was sent or *)
(* received by the test host), if any *)
type last_datagram_seen =
    NO_DATAGRAMS
  | SENT_DATAGRAM of Holtypes.tcp_segment
  | RECV_DATAGRAM of Holtypes.tcp_segment;;

(* ---------------------------------------------------------------------- *)

let timestamp_update_swap ts incr =
  match ts with
    None -> None
  | Some(t1,t2) -> Some(t2 +. incr, t1)

let timestamp_update ts incr =
  match ts with
    None -> None
  | Some(t1,t2) -> Some(t1 +. incr, t2)

let ts_incr = uint 1

(* ---------------------------------------------------------------------- *)

let drive_tcp_data_sent id ts fd last_datagram =
  let th_libd = the ts.th_libd_hnd in
  let th_injector = the ts.th_injector_hnd in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let seen_ack = ref false in
  let last_datagram_seen = ref last_datagram in

  (* A slurper callback function that signals a condition when the *)
  (* required packet is actually seen on the wire *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if (List.length datagram.data > 0) &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  let ack_datagram = {datagram with
			      is1 = datagram.is2;
			      is2 = datagram.is1;
			      ps1 = datagram.ps2;
			      ps2 = datagram.ps1;
			      sYN = false; aCK = true;
			      seq = datagram.ack;
			      ack = datagram.seq +. (uint (List.length datagram.data));
			      win = tcpcb_get_win ts datagram.is2 datagram.is1
				datagram.ps2 datagram.ps1;
			      ts = timestamp_update_swap datagram.ts ts_incr;
			      data = []} in
	  injector_inject th_injector (TCPMSG(ack_datagram))
	else if datagram.aCK &&
	  (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.ps1 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   seen_ack := true;
	   last_datagram_seen := RECV_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  (* Try a send to the virtual host *)
  let send_call = (tid_of_int_private 0, SEND(fd, None, "foo", [])) in
  ignore(libd_call th_libd send_call);

  (* Block on condition variable here until we verify that the send *)
  (* occured and the ACK has been received back *)
  Mutex.lock lock;
  while !seen_ack = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
  (* Return the last datagram seen *)
  !last_datagram_seen;;


let drive_tcp_data_recv id ts fd last_datagram =
  let th_libd = the ts.th_libd_hnd in
  let th_injector = the ts.th_injector_hnd in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let seen_ack = ref false in
  let last_datagram_seen = ref last_datagram in

  (* A slurper callback function that signals a condition when the *)
  (* required ACK packet is actually seen on the wire *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if datagram.aCK &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   seen_ack := true;
	   last_datagram_seen := SENT_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  (* Inject the packet sent by psyche *)
  let packet_to_inject =
    match last_datagram with
      RECV_DATAGRAM(dg) ->
	{dg with seq = dg.seq +. (uint (List.length(dg.data)));
	 sYN = false; aCK = true; ts = timestamp_update dg.ts ts_incr;
	 win = tcpcb_get_win ts dg.is1 dg.is2 dg.ps1 dg.ps2;
	 data = [uint(Char.code 'b'); uint(Char.code 'a'); uint(Char.code 'r');]}
    | SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	 seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	 sYN = false; aCK = true; ts = timestamp_update_swap dg.ts ts_incr;
	 win = tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1;
	 data = [uint(Char.code 'b'); uint(Char.code 'a'); uint(Char.code 'r');]}
    | _ ->
	raise(Drive_Failure("In drive_tcp_data_recv() got a NO_DATAGRAMS!"))
  in
  injector_inject th_injector (TCPMSG(packet_to_inject));

  (* Try a send to the virtual host *)
  let recv_call = (tid_of_int_private 0, RECV(fd, 3, [])) in
  ignore(libd_call th_libd recv_call);

  (* Block on condition variable here until we verify that the send *)
  (* occured and the ACK has been received back *)
  Mutex.lock lock;
  while !seen_ack = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;
  (* Return the last datagram seen *)
  !last_datagram_seen;;


let drive_tcp_data_status id ts status fd last_datagram =
  match status with
    NO_DATA -> last_datagram
  | DATA_SENT -> drive_tcp_data_sent id ts fd last_datagram
  | DATA_RCVD -> drive_tcp_data_recv id ts fd last_datagram
  | DATA_SENT_RCVD -> drive_tcp_data_sent id ts fd
	(drive_tcp_data_recv id ts fd last_datagram);;

(* ---------------------------------------------------------------------- *)

let socket_CLOSED id ts dupb =
  let th_libd = the ts.th_libd_hnd in

  (* Make a socket call *)
  let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
  let fd, last_dgram =
    match libd_call th_libd socket_call with
      (_, OK_FD(fd)) -> (fd, NO_DATAGRAMS)
    | _ -> raise(Drive_Failure("socket_CLOSED() failed")) in

  let reuseaddr_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_REUSEADDR, true)) in
  ignore(libd_call th_libd reuseaddr_call);

  let fd2 =
    if dupb then
      let dup_call = (tid_of_int_private 0, DUP(fd)) in
      match libd_call th_libd dup_call with
	(_, OK_FD(fd)) -> Some(fd)
      | _ -> raise(Test_failed("dup() -- test failed due to dup failure"))
    else
      None in
  (fd, last_dgram, fd2)

(* ---------------------------------------------------------------------- *)

let socket_LISTEN id ts dupb =
  let th_libd = the ts.th_libd_hnd in

  (* Get a st=CLOSED socket *)
  let fd, _, fd2 = socket_CLOSED id ts dupb in

  (* Bind socket to the local interface and an ephemeral port *)
  let ips = Some(mk_ip id.test_host.test_ip_address) in
  let ps = Some(mk_port id.test_host.test_ephm_port) in
  let bind_call = (tid_of_int_private 0, BIND(fd, ips, ps)) in
  ignore(libd_call th_libd bind_call);

  get_bound_state th_libd fd;

  (* Call listen on the bound socket *)
  let listen_call = (tid_of_int_private 0, LISTEN(fd, 1)) in
  ignore(libd_call th_libd listen_call);

  get_bound_state th_libd fd;

  (* Return the file descriptor and last datagram seen on the wire *)
  (fd, NO_DATAGRAMS, fd2);;

(* ---------------------------------------------------------------------- *)

let socket_SYN_SENT id ts dupb =
  let th_libd = the ts.th_libd_hnd in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let syn_seen = ref false in
  let last_datagram_seen = ref NO_DATAGRAMS in

  (* A slurper callback function that signals a condition when the *)
  (* required SYN packet is actually seen on the wire *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if datagram.sYN && (datagram.aCK = false) &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   syn_seen := true;
	   last_datagram_seen := SENT_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  (* Get a st=CLOSED socket *)
  let fd, _, fd2 = socket_CLOSED id ts dupb in

  (* Put socket into non blocking mode *)
  let non_block_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
  ignore(libd_call th_libd non_block_call);

  (* Try an connect to a non-reponding virtual host *)
  let ip = mk_ip id.virtual_host_ip in
  let pt = mk_port id.virtual_host_port in
  let connect_call = (tid_of_int_private 0, CONNECT(fd, ip, Some(pt))) in
  ignore(libd_call th_libd connect_call);

  (* Block on condition variable here until we verify that the SYN *)
  (* packet has been sent onto the network *)
  Mutex.lock lock;
  while !syn_seen = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  get_bound_state th_libd fd;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  (* Return the file descriptor and last datagram seen on the wire *)
  (fd, !last_datagram_seen, fd2);;

(* ---------------------------------------------------------------------- *)

let socket_SYN_RCVD id ts dupb =
  let th_libd = the ts.th_libd_hnd in
  let th_injector = the ts.th_injector_hnd in

  (* Get into the SYN_SENT state *)
  let fd, last_message_seen, fd2 = socket_SYN_SENT id ts dupb in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let syn_ack_seen = ref false in
  let last_datagram_seen = ref last_message_seen in

  (* required SYN packet is actually seen on the wire *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if datagram.sYN && (datagram.aCK = true) &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   syn_ack_seen := true;
	   last_datagram_seen := SENT_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  (* Inject the simultaneous SYN packet *)
  let syn_datagram =
    match !last_datagram_seen with
      SENT_DATAGRAM(dg) ->
	{dg with
	 is1 = dg.is2;
	 is2 = dg.is1;
	 ps1 = dg.ps2;
	 ps2 = dg.ps1;
	 sYN = true; aCK = false;
	 seq = uint 1000000;
	 ack = uint 0;
	 win = uint 16384;
	 ts = Some(uint 100, uint 0);
	 data = []}
    | _ -> raise(Assertion_failed("socket_SYN_RCVD: expected a SENT_DATAGRAM here!"))
  in
  injector_inject th_injector (TCPMSG(syn_datagram));
  tcpcb_update_win ts syn_datagram.is1 syn_datagram.is2 syn_datagram.ps1
    syn_datagram.ps2 syn_datagram.win;

  (* Block on condition variable here until we verify that the SYN *)
  (* packet has been sent onto the network *)
  Mutex.lock lock;
  while !syn_ack_seen = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  get_bound_state th_libd fd;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  (* Return the file descriptor and last datagram seen on the wire *)
  (fd, !last_datagram_seen, fd2);;


(* ---------------------------------------------------------------------- *)

let socket_ESTABLISHED id ts status send_mss dupb=
  let th_libd = the ts.th_libd_hnd in
  let th_injector = the ts.th_injector_hnd in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let connect_successful = ref false in
  let last_datagram_seen = ref NO_DATAGRAMS in

  (* A slurper callback function that responds to the connect SYN packet  *)
  (* with a SYN,ACK packet and then waits for the final ACK packet before *)
  (* signalling a successful connection *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if datagram.sYN && (datagram.aCK = false) &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  (* Inject the syn/ack packet *)
	  let s_a_dg = {datagram with
				  is1 = datagram.is2;
				  is2 = datagram.is1;
				  ps1 = datagram.ps2;
				  ps2 = datagram.ps1;
				  sYN = true; aCK = true;
				  seq = datagram.ack;
				  ack = datagram.seq +. (uint 1);
				  win = uint 16384;
				  ts = timestamp_update_swap datagram.ts ts_incr;
                                  mss = if send_mss then datagram.mss else None;
				  data = []} in
	  tcpcb_update_win ts s_a_dg.is1 s_a_dg.is2 s_a_dg.ps1 s_a_dg.ps2 s_a_dg.win;
	  injector_inject th_injector (TCPMSG(s_a_dg))
	else if (datagram.sYN = false) && (datagram.aCK = true) &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   connect_successful := true;
	   last_datagram_seen := SENT_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  (* Get a st=CLOSED socket *)
  let fd, _, fd2 = socket_CLOSED id ts dupb in

  (* Try a connect to the virtual host *)
  let ip = mk_ip id.virtual_host_ip in
  let pt = mk_port id.virtual_host_port in
  let connect_call = (tid_of_int_private 0, CONNECT(fd, ip, Some(pt))) in
  ignore(libd_call th_libd connect_call);

  (* Block on condition variable here until we verify that the *)
  (* connect has succeeded *)
  Mutex.lock lock;
  while !connect_successful = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  get_bound_state th_libd fd;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  (* Drive the established socket into the request sent/recv'd data state *)
  (* and return the file descriptor and last datagram seen on the wire *)
  (fd, drive_tcp_data_status id ts status fd !last_datagram_seen, fd2);;

(* ---------------------------------------------------------------------- *)

let socket_CLOSE_WAIT id ts status dupb =
  let th_libd = the ts.th_libd_hnd in
  let th_injector = the ts.th_injector_hnd in

  (* Get into the ESTABLISHED state and send/recv any necessary data *)
  let fd, last_message_seen, fd2 = socket_ESTABLISHED id ts status true dupb in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let ack_seen = ref false in
  let last_datagram_seen = ref last_message_seen in

  (* A slurper callback function that waits to see the ACK packet *)
  (* sent by the test host in response to the FIN it received *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if (datagram.aCK = true) &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   ack_seen := true;
	   last_datagram_seen := SENT_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  (* Inject the FIN packet from the virtual host *)
  let fin_packet =
    match last_message_seen with
      RECV_DATAGRAM(dg) ->
	{dg with seq = dg.seq +. (uint (List.length dg.data));
	 ack = dg.ack; aCK = true; fIN = true;
	 ts = timestamp_update dg.ts ts_incr; data = []}
    | SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2;
	 ps2 = dg.ps1; seq = dg.ack; ack = dg.seq +. (uint (List.length dg.data));
	 aCK = true; fIN = true; ts = timestamp_update_swap dg.ts ts_incr; data = [];
	 win = tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1 }
    | _ -> raise(Drive_Failure("Assertion failed in socket_CLOSE_WAIT()"))
 in
  ignore(injector_inject th_injector (TCPMSG(fin_packet)));

  (* Block on condition variable here until we verify that the *)
  (* connect has succeeded *)
  Mutex.lock lock;
  while !ack_seen = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  (* Return the file descriptor and last datagram seen on the wire *)
  (fd, !last_datagram_seen, fd2);;

(* ---------------------------------------------------------------------- *)

let socket_LAST_ACK id ts status dupb =
  let th_libd = the ts.th_libd_hnd in
  let th_injector = the ts.th_injector_hnd in

  (* Get into the CLOSE_WAIT state *)
  let fd, last_message_seen, fd2 = socket_CLOSE_WAIT id ts status dupb in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let fin_seen = ref false in
  let last_datagram_seen = ref last_message_seen in

  (* A slurper callback function that waits to see the FIN packet *)
  (* sent by the test host *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if (datagram.fIN = true) &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   fin_seen := true;
	   last_datagram_seen := SENT_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  (* Call close() *)
  (*let close_call = (tid_of_int_private 0, CLOSE(fd)) in*)
  (*ignore(libd_call th_libd close_call);*)
  (*if dupb then
    let close_call2 = (tid_of_int_private 0, CLOSE(the fd2)) in
    ignore(libd_call th_libd close_call2)
  else
    ();*)

  (* Call shutdown() instead *)
  let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, true, true)) in
  ignore(libd_call th_libd shutdown_call);

  (* Block on condition variable here until we verify that the *)
  (* close has caused a FIN packet to be sent *)
  Mutex.lock lock;
  while !fin_seen = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  (* Return the file descriptor and last datagram seen on the wire *)
  (fd, !last_datagram_seen, fd2);;

(* ---------------------------------------------------------------------- *)

let socket_FIN_WAIT_1 id ts status dupb=
  let th_libd = the ts.th_libd_hnd in
  let th_injector = the ts.th_injector_hnd in

  (* Get into the ESTABLISHED state *)
  let fd, last_message_seen, fd2 = socket_ESTABLISHED id ts status true dupb in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let fin_seen = ref false in
  let last_datagram_seen = ref last_message_seen in

  (* A slurper callback function that waits to see the FIN packet *)
  (* sent by the test host *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if (datagram.fIN = true) &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   fin_seen := true;
	   last_datagram_seen := SENT_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  (* Call close() *)
  let shutdown_call = (tid_of_int_private 0, SHUTDOWN(fd, false, true)) in
  ignore(libd_call th_libd shutdown_call);

  if dupb then
    let shutdown_call2 = (tid_of_int_private 0, SHUTDOWN(the fd2, false, true)) in
    ignore(libd_call th_libd shutdown_call2)
  else
    ();

  (* Block on condition variable here until we verify that the *)
  (* close has caused a FIN packet to be sent *)
  Mutex.lock lock;
  while !fin_seen = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  (* Return the file descriptor and last datagram seen on the wire *)
  (fd, !last_datagram_seen, fd2);;


(* ---------------------------------------------------------------------- *)

let socket_CLOSING id ts status dupb =
  let th_libd = the ts.th_libd_hnd in
  let th_injector = the ts.th_injector_hnd in

  (* Get into the FIN_WAIT_1 state *)
  let fd, last_message_seen, fd2 = socket_FIN_WAIT_1 id ts status dupb in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let ack_seen = ref false in
  let last_datagram_seen = ref last_message_seen in

  (* A slurper ca llback function that waits to see the ACK packet *)
  (* sent by the test host *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if (datagram.aCK = true) &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   ack_seen := true;
	   last_datagram_seen := SENT_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  (* Inject the FIN packet from the virtual host *)
  let fin_packet =
    match last_message_seen with
     | SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2;
	 ps2 = dg.ps1; seq = dg.ack; ack = dg.seq; aCK = true;
	 fIN = true; ts = timestamp_update_swap dg.ts ts_incr; data = [];
	 win = tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1}
    | _ -> raise(Drive_Failure("Assertion failed in socket_CLOSING()"))
 in
  ignore(injector_inject th_injector (TCPMSG(fin_packet)));

  (* Block on condition variable here until we see the ACK generated *)
  (* by the test host for the recv'd FIN *)
  Mutex.lock lock;
  while !ack_seen = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  (* Return the file descriptor and last datagram seen on the wire *)
  (fd, !last_datagram_seen, fd2);;


(* ---------------------------------------------------------------------- *)

let socket_FIN_WAIT_2 id ts status dupb =
  let th_libd = the ts.th_libd_hnd in
  let th_injector = the ts.th_injector_hnd in

  (* Get into the FIN_WAIT_1 state *)
  let fd, last_message_seen, fd2 = socket_FIN_WAIT_1 id ts status dupb in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let remote_ack_seen = ref false in
  let last_datagram_seen = ref last_message_seen in

  (* A slurper ca llback function that waits to see the ACK packet *)
  (* sent by the VIRTUAL host *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if (datagram.fIN = false) && (datagram.aCK = true) &&
	  (datagram.is1 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.is2 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.ps1 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   remote_ack_seen := true;
	   last_datagram_seen := RECV_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

 (* Inject the ACK packet from the virtual host *)
  let fin_packet =
    match last_message_seen with
     | SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2;
	 ps2 = dg.ps1; seq = dg.ack; ack = dg.seq +. (uint 1) +. (uint (List.length dg.data));
	 aCK = true; fIN = false; ts = timestamp_update_swap dg.ts ts_incr; data = [];
	 win = tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1}
    | _ -> raise(Drive_Failure("Assertion failed in socket_CLOSE_WAIT()"))
 in
  ignore(injector_inject th_injector (TCPMSG(fin_packet)));

  (* Block on condition variable here until we see the ACK generated *)
  (* by the VIRTUAL host for the recv'd FIN *)
  Mutex.lock lock;
  while !remote_ack_seen = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  (* Return the file descriptor and last datagram seen on the wire *)
  (fd, !last_datagram_seen, fd2);;


(* ---------------------------------------------------------------------- *)

let socket_TIME_WAIT id ts status dupb =
  let th_libd = the ts.th_libd_hnd in
  let th_injector = the ts.th_injector_hnd in

  (* Get into the FIN_WAIT_1 state *)
  let fd, last_message_seen, fd2 = socket_FIN_WAIT_1 id ts status dupb in

  let lock = Mutex.create () in
  let cond = Condition.create () in
  let ack_seen = ref false in
  let last_datagram_seen = ref last_message_seen in

  (* A slurper ca llback function that waits to see the ACK packet *)
  (* generated by the test host *)
  let slurper_callback_fun holmsg =
    match holmsg with
      TCPMSG(datagram) ->
	if (datagram.fIN = false) && (datagram.aCK = true) &&
	  (datagram.is1 = Some(hol_ip id.test_host.test_ip_address)) &&
	  (datagram.is2 = Some(hol_ip id.virtual_host_ip)) &&
	  (datagram.ps2 = Some(uint id.virtual_host_port))
	then
	  (Mutex.lock lock;
	   ack_seen := true;
	   last_datagram_seen := SENT_DATAGRAM(datagram);
	   Condition.signal cond;
	   Mutex.unlock lock)
	else ()
    | _ -> ()
  in
  let slurper_callback_hnd = slurper_register_callback
      (the ts.th_slurper_hnd) slurper_callback_fun in

  (* Inject the FIN,ACK packet from the virtual host *)
  let fin_ack_packet =
    match last_message_seen with
     | SENT_DATAGRAM(dg) ->
	{dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2;
	 ps2 = dg.ps1; seq = dg.ack; ack = dg.seq +. (uint 1) +. (uint (List.length dg.data));
	 aCK = true; fIN = true; ts = timestamp_update_swap dg.ts ts_incr; data = [];
	 win = tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1}
    | _ -> raise(Drive_Failure("Assertion failed in socket_CLOSE_WAIT()"))
 in
  ignore(injector_inject th_injector (TCPMSG(fin_ack_packet)));

  (* Block on condition variable here until we see the ACK generated *)
  (* by the test host for the recv'd FIN,ACK *)
  Mutex.lock lock;
  while !ack_seen = false do
    Condition.wait cond lock;
  done;
  Mutex.unlock lock;

  (* Unregister the callback *)
  slurper_deregister_callback (the ts.th_slurper_hnd) slurper_callback_hnd;

  (* Return the file descriptor and last datagram seen on the wire *)
  (fd, !last_datagram_seen, fd2);;

(* ---------------------------------------------------------------------- *)
(* Get a socket in a tcp state-transition diagram state *)
(* ---------------------------------------------------------------------- *)

(* The TCP states you can be in a la TCP state transition diagram *)
type tcp_state_diagram_state =
    ST_CLOSED
  | ST_LISTEN
  | ST_SYN_RCVD
  | ST_SYN_SENT
  | ST_ESTABLISHED of tcp_data_status
  | ST_CLOSE_WAIT of tcp_data_status
  | ST_LAST_ACK of tcp_data_status
  | ST_FIN_WAIT_1 of tcp_data_status
  | ST_CLOSING of tcp_data_status
  | ST_FIN_WAIT_2 of tcp_data_status
  | ST_TIME_WAIT of tcp_data_status;;

(* Create a fresh socket forcing it into state tcp_state_diagram_state. *)
(* Returns the socket's fd and the last related datagram seen on the wire *)
let tcp_state_diagram_driver id ts st dupb =
  match st with
    ST_CLOSED ->
      socket_CLOSED id ts dupb
  | ST_LISTEN ->
      socket_LISTEN id ts dupb
  | ST_SYN_SENT ->
      socket_SYN_SENT id ts dupb
  | ST_SYN_RCVD ->
      socket_SYN_RCVD id ts dupb
  | ST_ESTABLISHED(status) ->
      socket_ESTABLISHED id ts status true dupb
  | ST_CLOSE_WAIT(status) ->
      socket_CLOSE_WAIT id ts status dupb
  | ST_LAST_ACK(status) ->
      socket_LAST_ACK id ts status dupb
  | ST_FIN_WAIT_1(status) ->
      socket_FIN_WAIT_1 id ts status dupb
  | ST_CLOSING(status) ->
      socket_CLOSING id ts status dupb
  | ST_FIN_WAIT_2(status) ->
      socket_FIN_WAIT_2 id ts status dupb
  | ST_TIME_WAIT(status) ->
      socket_TIME_WAIT id ts status dupb

let all_driven_states = [
  ST_CLOSED, "CLOSED";
  ST_LISTEN, "LISTEN";
  ST_SYN_SENT, "SYN_SENT";
  ST_SYN_RCVD, "SYN_RECEIVED";
  ST_ESTABLISHED(NO_DATA), "ESTABLISHED(no data)";
  ST_ESTABLISHED(DATA_SENT), "ESTABLISHED(data sent)";
  ST_ESTABLISHED(DATA_RCVD), "ESTABLISHED(data rcvd)";
  ST_ESTABLISHED(DATA_SENT_RCVD), "ESTABLISHED(data sent rcvd)";
  ST_CLOSE_WAIT(NO_DATA), "CLOSE_WAIT(no data)";
  ST_CLOSE_WAIT(DATA_SENT), "CLOSE_WAIT(data sent)";
  ST_CLOSE_WAIT(DATA_RCVD), "CLOSE_WAIT(data rcvd)";
  ST_CLOSE_WAIT(DATA_SENT_RCVD), "CLOSE_WAIT(data sent rcvd)";
  ST_LAST_ACK(NO_DATA), "LAST_ACK(no data)";
  ST_LAST_ACK(DATA_SENT), "LAST_ACK(data sent)";
  ST_LAST_ACK(DATA_RCVD), "LAST_ACK(data rcvd)";
  ST_LAST_ACK(DATA_SENT_RCVD), "LAST_ACK(data sent rcvd)";
  ST_FIN_WAIT_1(NO_DATA), "FIN_WAIT_1(no data)";
  ST_FIN_WAIT_1(DATA_SENT), "FIN_WAIT_1(data sent)";
  ST_FIN_WAIT_1(DATA_RCVD), "FIN_WAIT_1(data rcvd)";
  ST_FIN_WAIT_1(DATA_SENT_RCVD), "FIN_WAIT_1(data sent rcvd)";
  ST_CLOSING(NO_DATA), "CLOSING(no data)";
  ST_CLOSING(DATA_SENT), "CLOSING(data sent)";
  ST_CLOSING(DATA_RCVD), "CLOSING(data rcvd)";
  ST_CLOSING(DATA_SENT_RCVD), "CLOSING(data sent rcvd)";
  ST_FIN_WAIT_2(NO_DATA), "FIN_WAIT_2(no data)";
  ST_FIN_WAIT_2(DATA_SENT), "FIN_WAIT_2(data sent)";
  ST_FIN_WAIT_2(DATA_RCVD), "FIN_WAIT_2(data rcvd)";
  ST_FIN_WAIT_2(DATA_SENT_RCVD), "FIN_WAIT_2(data sent rcvd)";
  ST_TIME_WAIT(NO_DATA), "TIME_WAIT(no data)";
  ST_TIME_WAIT(DATA_SENT), "TIME_WAIT(data sent)";
  ST_TIME_WAIT(DATA_RCVD), "TIME_WAIT(data rcvd)";
  ST_TIME_WAIT(DATA_SENT_RCVD), "TIME_WAIT(data sent rcvd)";
]

let all_interesting_driven_states = [
  ST_CLOSED, "CLOSED";
  ST_LISTEN, "LISTEN";
  ST_SYN_SENT, "SYN_SENT";
  ST_SYN_RCVD, "SYN_RECEIVED";
  ST_ESTABLISHED(DATA_SENT_RCVD), "ESTABLISHED(data sent rcvd)";
  ST_CLOSE_WAIT(DATA_SENT_RCVD), "CLOSE_WAIT(data sent rcvd)";
  ST_LAST_ACK(DATA_SENT_RCVD), "LAST_ACK(data sent rcvd)";
  ST_FIN_WAIT_1(DATA_SENT_RCVD), "FIN_WAIT_1(data sent rcvd)";
  ST_CLOSING(DATA_SENT_RCVD), "CLOSING(data sent rcvd)";
  ST_FIN_WAIT_2(DATA_SENT_RCVD), "FIN_WAIT_2(data sent rcvd)";
  ST_TIME_WAIT(DATA_SENT_RCVD), "TIME_WAIT(data sent rcvd)";
]

let drive_socket_established_nomss id ts dupb =
    socket_ESTABLISHED id ts DATA_SENT_RCVD false dupb;;

let rst_driven_socket ts id fd last_datagram =
  match last_datagram with
    RECV_DATAGRAM(dg) ->
      let rst_datagram =
	{dg with sYN = false; aCK = false; fIN = false; rST = true; pSH = false;
	 ts = timestamp_update dg.ts ts_incr; data = []} in
      ignore(injector_inject (the ts.th_injector_hnd) (TCPMSG(rst_datagram)))
  | SENT_DATAGRAM(dg) ->
      let rst_datagram =
	{dg with is1 = dg.is2; is2 = dg.is1; ps1 = dg.ps2; ps2 = dg.ps1;
	 seq = dg.ack; ack= dg.seq +. (uint (List.length(dg.data)));
	 sYN = false; aCK = false; fIN = false; rST = true; pSH = false;
	 ts = timestamp_update_swap dg.ts ts_incr; data = [];
	 win = try tcpcb_get_win ts dg.is2 dg.is1 dg.ps2 dg.ps1 with
	   Not_found -> dg.win } in
      ignore(injector_inject (the ts.th_injector_hnd) (TCPMSG(rst_datagram)))
  | _ ->
      let linger_call = (tid_of_int_private 0, SETSOCKTOPT(fd, SO_LINGER, Some(0,0))) in
      ignore(libd_call (the ts.th_libd_hnd) linger_call);
      let reset_call = (tid_of_int_private 0, CLOSE(fd)) in
      ignore(libd_call (the ts.th_libd_hnd) reset_call)

(* ---------------------------------------------------------------------- *)
(* Exhausting file descriptors                                            *)
(* ---------------------------------------------------------------------- *)

let exhaust_proc_fds_helper libd_hnd num =
 let rec loop n =
    if(n<1) then ()
    else
      (let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
      (try ignore(libd_call libd_hnd socket_call) with _ -> ());
      loop (n-1))
  in
 loop num

let exhaust_proc_fds ts id =
  exhaust_proc_fds_helper (the ts.th_libd_hnd) id.test_host.max_proc_fds

let exhaust_sys_fds ts id =
  let num_libds_req = (id.test_host.max_sys_fds / id.test_host.max_proc_fds) + 1 in
  let rec outer_loop i libd_list =
    if(i<1) then libd_list
    else
      (let libd = dual_second_th_libd_create ts id (!tthee_baseport_2 + 5 + i) in
      exhaust_proc_fds_helper (snd libd) id.test_host.max_proc_fds;
      outer_loop (i-1) (libd::libd_list))
  in
  outer_loop num_libds_req []

(* ---------------------------------------------------------------------- *)
(* Getting bound and/or connected sockets                                 *)
(* ---------------------------------------------------------------------- *)

type bound_ip =
    LOCAL_IP
  | LOOPBACK_IP
  | FOREIGN_IP
  | UNSPECIFIED_IP

type bound_port =
    PRIV_PORT
  | EPHM_PORT
  | NPOE_PORT
  | UNSPECIFIED_PORT
  | SOME_PORT  (* used for connect() *)

type bound_pair = bound_ip * bound_port
type bound_quad = bound_ip * bound_port * bound_ip * bound_port

let local_bindings_list = [
  (UNSPECIFIED_IP, UNSPECIFIED_PORT);
  (UNSPECIFIED_IP, PRIV_PORT);
  (UNSPECIFIED_IP, EPHM_PORT);
  (UNSPECIFIED_IP, NPOE_PORT);
  (LOCAL_IP, UNSPECIFIED_PORT);
  (LOCAL_IP, PRIV_PORT);
  (LOCAL_IP, EPHM_PORT);
  (LOCAL_IP, NPOE_PORT);
  (LOOPBACK_IP, UNSPECIFIED_PORT);
  (LOOPBACK_IP, PRIV_PORT);
  (LOOPBACK_IP, EPHM_PORT);
  (LOOPBACK_IP, NPOE_PORT)
]

let foreign_bindings_list = [
  (UNSPECIFIED_IP, UNSPECIFIED_PORT);
  (FOREIGN_IP, SOME_PORT);
  (LOCAL_IP, SOME_PORT);
  (LOOPBACK_IP, SOME_PORT)
]

let all_bindings_list =
  List.flatten (
  List.map
    (function foreign ->
      List.map
	(function local ->
	  let a,b = local in
	  let c,d = foreign in
	  (a, b, c, d)
	) local_bindings_list
    ) foreign_bindings_list
 )

let string_of_bound_ip bound_ip =
  match bound_ip with
    LOCAL_IP -> "LOCAL_IP"
  | LOOPBACK_IP -> "LOOPBACK_IP"
  | FOREIGN_IP -> "FOREIGN_IP"
  | UNSPECIFIED_IP -> "UNSPECIFIED_IP"

let string_of_bound_port bound_port =
  match bound_port with
    PRIV_PORT -> "PRIV_PORT"
  | EPHM_PORT -> "EPHM_PORT"
  | NPOE_PORT -> "NPOE_PORT"
  | UNSPECIFIED_PORT -> "UNSPECIFIED_PORT"
  | SOME_PORT -> "SOME_PORT"

let string_of_bound_quad bound_quad =
  let a,b,c,d = bound_quad in
  "(" ^ (string_of_bound_ip a) ^ ", " ^
  (string_of_bound_port b) ^ ", " ^
  (string_of_bound_ip c) ^ ", " ^
  (string_of_bound_port d) ^ ")"

let get_bound_socket id ts binding =
  let th_libd = the ts.th_libd_hnd in
  let bi1,bp1,bi2,bp2 = binding in
  let is1 =
    match bi1 with
      LOCAL_IP -> Some(Ocamllib.ip_of_string (string_ip id.test_host.test_ip_address))
    | LOOPBACK_IP -> Some(Ocamllib.ip_of_string (string_ip (127,0,0,1)))
    | FOREIGN_IP -> Some(Ocamllib.ip_of_string (string_ip id.aux_host.test_ip_address))
    | UNSPECIFIED_IP -> None in
  let is2 =
    match bi2 with
      LOCAL_IP -> Some(Ocamllib.ip_of_string (string_ip id.test_host.test_ip_address))
    | LOOPBACK_IP -> Some(Ocamllib.ip_of_string (string_ip (127,0,0,1)))
    | FOREIGN_IP -> Some(Ocamllib.ip_of_string (string_ip id.aux_host.test_ip_address))
    | UNSPECIFIED_IP ->  None in
  let ps1 =
    match bp1 with
      PRIV_PORT -> Some(Ocamllib.port_of_int (id.test_host.test_priv_port))
    | EPHM_PORT -> Some(Ocamllib.port_of_int (id.test_host.test_ephm_port))
    | NPOE_PORT -> Some(Ocamllib.port_of_int (id.test_host.test_npoe_port))
    | SOME_PORT -> Some(Ocamllib.port_of_int (id.test_host.test_listening_port_base))
    | UNSPECIFIED_PORT -> None in
  let ps2 =
    match bp2 with
      PRIV_PORT -> Some(Ocamllib.port_of_int (id.aux_host.test_priv_port))
    | EPHM_PORT -> Some(Ocamllib.port_of_int (id.aux_host.test_ephm_port))
    | NPOE_PORT -> Some(Ocamllib.port_of_int (id.aux_host.test_npoe_port))
    | SOME_PORT -> Some(Ocamllib.port_of_int (id.aux_host.test_listening_port_base))
    | UNSPECIFIED_PORT -> None in

  if (is2 = None) || (ps2 = None) then (
    if (is1 = None) && (ps1 = None) then
      Some(get_socket th_libd), None
    else
      Some(get_local_bound_socket th_libd is1 ps1), None
   )
  else if bi2 = FOREIGN_IP then (
    let fd = get_local_bound_socket (the ts.ah_libd_hnd) is2 ps2 in
    let reuseaddr_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_REUSEADDR, true)) in
    ignore(libd_call (the ts.ah_libd_hnd) reuseaddr_call);
    let listen_call =  (tid_of_int_private 0, LISTEN(fd, 2)) in
    ignore(libd_call (the ts.ah_libd_hnd) listen_call);
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call_async (the ts.ah_libd_hnd) accept_call);
    Some(get_local_bound_connected_socket th_libd is1 ps1 (the is2) (the ps2)), Some(fd))
  else (
    let fd = get_local_bound_socket th_libd is2 ps2 in
    let listen_call =  (tid_of_int_private 0, LISTEN(fd, 2)) in
    ignore(libd_call th_libd listen_call);
    let reuseaddr_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_REUSEADDR, true)) in
    ignore(libd_call th_libd reuseaddr_call);
    let nonblock_call = (tid_of_int_private 0, SETFILEFLAGS(fd, [O_NONBLOCK])) in
    ignore(libd_call th_libd nonblock_call);
    let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
    ignore(libd_call th_libd accept_call);
    Some(get_local_bound_connected_socket th_libd is1 ps1 (the is2) (the ps2)), Some(fd)
   )

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)

