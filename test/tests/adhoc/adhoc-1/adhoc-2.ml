(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Adhoc Test 1                                              *)
(* Dual host client-server example                                        *)
(* Steve Bishop - Created 20030512          *)
(* $Id *)
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
open Ocamllib;;
open Libcalls;;
open Testscommon;;
open Common;;
open Ocamllib;;
open Simple;;
(*open Render;;*)

exception Incorrect_cmd_line_args of string;;


(* ---------------------------------------------------------------------- *)

let john_host_info = {
  platform_type = ARCH_BSD;
  host_name = "john";
  iface_name = "ep0";
  loopback_name = "lo0";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = john_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 2000;
  test_listening_port_range = 100;
  max_proc_fds = 957;
  max_sys_fds = 1064;
  so_max_conns = 5;
  ns_tools_exec_params = john_remote;
  host_supports_holtcpcb = true;
  hol_initial_host = INITIAL_HOST_JOHN
} ;;

let emil_host_info = {
  platform_type = ARCH_BSD;
  host_name = "emil";
  iface_name = "ep0";
  loopback_name = "lo0";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = emil_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 2000;
  test_listening_port_range = 100;
  max_proc_fds = 957;
  max_sys_fds = 1064;
  so_max_conns = 5;
  ns_tools_exec_params = emil_remote;
  host_supports_holtcpcb = true;
  hol_initial_host = INITIAL_HOST_EMIL
} ;;

let kurt_host_info = {
  platform_type = ARCH_LINUX;
  host_name = "kurt";
  iface_name = "eth0";
   loopback_name = "lo";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = kurt_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 2000;
  test_listening_port_range = 100;
  max_proc_fds = 1024;
  max_sys_fds = 8192;
  so_max_conns = 5;
  ns_tools_exec_params = kurt_remote;
  host_supports_holtcpcb = false;
  hol_initial_host = INITIAL_HOST_KURT
} ;;

let alan_host_info = {
  platform_type = ARCH_LINUX;
  host_name = "alan";
  iface_name = "eth0";
  loopback_name = "lo";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = alan_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 2000;
  test_listening_port_range = 100;
  max_proc_fds = 1024;
  max_sys_fds = 8192;
  so_max_conns = 5;
  ns_tools_exec_params = alan_remote;
  host_supports_holtcpcb = false;
  hol_initial_host = INITIAL_HOST_ALAN
} ;;

let glia_host_info = {
  platform_type = ARCH_WINXP;
  host_name = "glia";
  iface_name = "\\Device\\NPF_{E156046C-C2F7-44FC-B502-9FBAB66E211C}";
 loopback_name = "\\Device\\NPF_{E156046C-C2F7-44FC-B502-9FBAB66E211C}";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = glia_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 2000;
  test_listening_port_range = 100;
  max_proc_fds = 1025;
  max_sys_fds = 1025;
  so_max_conns = 5;
  ns_tools_exec_params = glia_remote;
  host_supports_holtcpcb = false;
  hol_initial_host = INITIAL_HOST_GLIA
} ;;

let ken_host_info = {
  platform_type = ARCH_BSD;
  host_name = "ken";
  iface_name = "xl0";
  loopback_name = "lo0";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = ken_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 957;
  max_sys_fds = 1064;
  so_max_conns = 5;
  ns_tools_exec_params = ken_remote;
  host_supports_holtcpcb = true;
  hol_initial_host = INITIAL_HOST_KEN
} ;;

let jan_host_info = {
  platform_type = ARCH_LINUX;
  host_name = "jan";
  iface_name = "eth0";
  loopback_name = "lo";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = jan_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 8192;
  max_sys_fds = 1024;
  so_max_conns = 5;
  ns_tools_exec_params = jan_remote;
  host_supports_holtcpcb = false;
  hol_initial_host = INITIAL_HOST_JAN
} ;;

let ada_host_info = {
  platform_type = ARCH_LINUX;
  host_name = "ada";
  iface_name = "eth0";
  loopback_name = "lo";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = ada_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 8192;
  max_sys_fds = 1024;
  so_max_conns = 5;
  ns_tools_exec_params = ada_remote;
  host_supports_holtcpcb = false;
  hol_initial_host = INITIAL_HOST_ADA
} ;;

(*let all_test_hosts = [john_host_info; emil_host_info;
		      (*glia_host_info;*) kurt_host_info;
		      alan_host_info;];;*)

let all_test_hosts = [ada_host_info; ken_host_info; jan_host_info;];;

(* ---------------------------------------------------------------------- *)

let cmd_line_args = "autotest trace_filename_prefix";;

let check_cmdline_args argv =
  let len = Array.length argv in
  if(len > 1) then
   Array.get argv 1
  else
    raise (Incorrect_cmd_line_args(cmd_line_args));;

let fname = check_cmdline_args Sys.argv in

(* ---------------------------------------------------------------------- *)

let fake_server_host = {
  tthee_host = fornix_priv_ip;
  send_host = john_host_info;
  recv_host = kurt_host_info;  (* so the slurper knows where to snarf between *)
  seq_fname = fname ^ "/server";
  priv = false;
  already_bound = [];
  test_descr = "Simple client-server test: server_host"
}  in

let fake_client_host = {
  tthee_host = fornix_priv_ip;
  send_host = kurt_host_info;
  recv_host = john_host_info;  (* so the slurper knows where to snarf between *)
  seq_fname = fname ^ "/client";
  priv = false;
  already_bound = [];
  test_descr = "Simple client-server test: client_host"
}  in

(*let host_pairs_list = create_host_pairs [john_host_info; alan_host_info(*;
					 glia_host_info*)] in*)

let host_pairs_list = create_host_pairs all_test_hosts in

(* Define the server's operation *)
let server_thread_body (ts, hi) =
  (* Get a fresh socket *)
  let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
  let fd = match libd_call ts.libd_hnd socket_call with
    (_, OK_FD(fd)) -> fd
  |	_ -> raise(Test_failed(hi.test_descr ^ " @ socket() call")) in
  (* Set the socket option SO_REUSEADDR *)
  let sockopt_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_REUSEADDR, true)) in
  ignore(libd_call ts.libd_hnd sockopt_call);
  (* Bind the socket *)
  let ips = Some(Ocamllib.ip_of_string(string_ip hi.send_host.test_ip_address)) in
  let ps = Some(Ocamllib.port_of_int hi.send_host.test_npoe_port) in
  (*(prerr_string ((string_of_ip (match ips with Some x -> x)) ^ " " ^ (string_of_int (int_of_port (match ps with Some x -> x)))));*)
  let bind_call = (tid_of_int_private 0, BIND(fd, ips, ps)) in
  ignore(libd_call ts.libd_hnd bind_call);
  (* Put socket in listening state *)
  let listen_call = (tid_of_int_private 0, LISTEN(fd, 0)) in
  ignore(libd_call ts.libd_hnd listen_call);
  (* Accept a new client connection *)
  let accept_call = (tid_of_int_private 0, ACCEPT(fd)) in
  let returned_val = libd_call ts.libd_hnd accept_call in
  let connfd =
    match returned_val with
      (_, OK_FD_IP_PORT(connected_fd, _)) -> connected_fd
    | _ -> raise(Test_failed("Didn't get a connected fd from server_thread accept()")) in
  (* Receive some data *)
  let recv_call = (tid_of_int_private 0, RECV(connfd, 50, [])) in
  let returned_val = libd_call ts.libd_hnd recv_call in
  (* Send a response to the client *)
  let send_call = (tid_of_int_private 0, SEND(connfd,None, "Hi?", [])) in
  let returned_val = libd_call ts.libd_hnd send_call in
  (* Close the sockets *)
  let close_call = (tid_of_int_private 0, CLOSE(fd)) in
  ignore(libd_call ts.libd_hnd close_call);
  let close_call = (tid_of_int_private 0, CLOSE(connfd)) in
  ignore(libd_call ts.libd_hnd close_call) in


(* Define the client's operation *)
let client_thread_body (ts, hi, server_hi) =
  (* Get a fresh socket *)
  let socket_call = (tid_of_int_private 0, SOCKET(SOCK_STREAM)) in
  let fd = match libd_call ts.libd_hnd socket_call with
    (_, OK_FD(fd)) -> fd
  |	_ -> raise(Test_failed(server_hi.test_descr ^ " @ socket() call")) in
  (* Set the socket option SO_REUSEADDR *)
  let sockopt_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_REUSEADDR, true)) in
  ignore(libd_call ts.libd_hnd sockopt_call);
  (* Connect to the server *)
  let ip = Ocamllib.ip_of_string (string_ip server_hi.send_host.test_ip_address) in
  let port = Ocamllib.port_of_int server_hi.send_host.test_npoe_port in
  let connect_call = (tid_of_int_private 0, CONNECT(fd, ip, Some(port))) in
  ignore(libd_call ts.libd_hnd connect_call);
  (* Send some data *)
  let send_call = (tid_of_int_private 0, SEND(fd,None, "Hi!", [])) in
  let returned_val = libd_call ts.libd_hnd send_call in
  (* Receive the server's reponse *)
  let recv_call = (tid_of_int_private 0, RECV(fd, 50, [])) in
  let returned_val = libd_call ts.libd_hnd recv_call in
  (* Close the socket *)
  let close_call = (tid_of_int_private 0, CLOSE(fd)) in
  ignore(libd_call ts.libd_hnd close_call) in


(* For each host_pair combination do... *)
let rec loop host_pairs_list n =
  match host_pairs_list with
    [] -> ()
  | ((server, client)::xs) -> (
      let server_host = { fake_server_host with
			  send_host = server;
			  recv_host = client;
			  seq_fname = fname ^ "/server" ^ (string_of_int n) } in
      let client_host = { fake_client_host with
			  send_host = client;
			  recv_host = server;
			  seq_fname = fname ^ "/client" ^ (string_of_int n) } in

      (prerr_endline ("running: " ^ server_host.send_host.host_name ^ ", " ^
            client_host.send_host.host_name));

      (* let mh = make_multipurpose_merger (fname ^ "/both" ^ (string_of_int n)) in *)

      (prerr_endline "initialising server ...");
      (* Start-up the tthee bits 'n' pieces *)
      let server_test_state = simple_pre_test_init(*_with_merger*) server_host !tthee_baseport_1 (*(Some(mh))*) in
      (prerr_endline "initialising client ...");
      let client_test_state = simple_pre_test_init(*_with_merger*) client_host !tthee_baseport_2 (*(Some(mh))*) in

      (prerr_endline "starting threads ...");

      (* Start the client and server running *)
      let server_thread = Thread.create server_thread_body (server_test_state, server_host) in
      delay 2.00;   (* wait for the server to start up the nasty way *)
      let client_thread = Thread.create client_thread_body (client_test_state, client_host, server_host) in

      (prerr_endline "waiting on threads ...");

      (* Wait for the threads to die (and hence the tests to complete) *)
      Thread.join client_thread;
      Thread.join server_thread;

      delay 5.00;   (* delay: hope all the fin/ack'ing will happen sometime soon *)

      (* Tidy up *)
      simple_cleanup_tthee client_test_state;
      simple_cleanup_tthee server_test_state;
      loop xs (n+1)
     )

in (prerr_endline "go!"); loop host_pairs_list 0;;

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*-                                                    *)
(* ---------------------------------------------------------------------- *)
