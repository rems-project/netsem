(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Dual Tests UDP State Driver Code                *)
(* Matthew Fairbairn - Created 20040109                                   *)
(* $Id: dualdriven_udp.ml,v 1.4 2004/04/19 16:42:38 mf266 Exp $          *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread
open Unix
open ThreadUnix
open Printf

(* Our libraries *)
open Nettypes
open Netconv
open Ocamllib
open Holtypes
open Holparselib
open Tthee
open Ttheehelper
open Libcalls
open Testscommon
open Common
open Dual
open Dualdriven
open Common_udp

exception Drive_Failure of string

(* ---------------------------------------------------------------------- *)

let get_bound_state_udp th_libd fd =
  let sn_call = (tid_of_int_private 0, GETSOCKNAME(fd)) in
  ignore(libd_call th_libd sn_call);
  let pn_call = (tid_of_int_private 0, GETPEERNAME(fd)) in
  ignore(libd_call th_libd pn_call)

(* ---------------------------------------------------------------------- *)

(* Get new socket on host *)
let get_socket_udp libd_hnd =
  let socket_call = (tid_of_int_private 0, SOCKET(SOCK_DGRAM)) in
  match libd_call libd_hnd socket_call with
    (_, OK_FD(fd)) -> fd
  | _ -> raise(Drive_Failure("get_socket() failed"));;

(* Get new bound socket on host *)
let get_local_bound_socket_udp libd_hnd ips ps =
  let fd = get_socket_udp libd_hnd in
  let bind_call = (tid_of_int_private 0, BIND(fd, ips, ps)) in
  ignore(libd_call libd_hnd bind_call);
  get_bound_state_udp libd_hnd fd;
  fd;;

(* Get an autobound, connected socket on host *)
let get_autobound_connected_socket_udp libd_hnd ip port =
  let fd = get_socket_udp libd_hnd in
  let connect_call = (tid_of_int_private 0, CONNECT(fd, ip, Some(port))) in
  ignore(libd_call libd_hnd connect_call);
  get_bound_state_udp libd_hnd fd;
  fd;;

(* Get a non-auto bound, connected socket on host *)
let get_local_bound_connected_socket_udp libd_hnd ips ps ip port =
  let fd = get_local_bound_socket_udp libd_hnd ips ps in
  let connect_call = (tid_of_int_private 0, CONNECT(fd, ip, Some(port))) in
  ignore(libd_call libd_hnd connect_call);
  get_bound_state_udp libd_hnd fd;
  fd;;


let bound_udp_quads =
  List.map (function x -> (x,string_of_bound_udp_quad x))
    all_sock_flavours

let rst_udp_socket id ts fd =
  let close_call = (tid_of_int_private 0, CLOSE(fd)) in
  ignore(libd_call (the ts.th_libd_hnd) close_call)


(* ---------------------------------------------------------------------- *)
(* Exhausting file descriptors                                            *)
(* ---------------------------------------------------------------------- *)

let exhaust_proc_fds_helper_udp libd_hnd num =
 let rec loop n =
    if(n<1) then ()
    else
      (let socket_call = (tid_of_int_private 0, SOCKET(SOCK_DGRAM)) in
      (try ignore(libd_call libd_hnd socket_call) with _ -> ());
      loop (n-1))
  in
 loop num

let exhaust_proc_fds_udp ts id =
  exhaust_proc_fds_helper_udp (the ts.th_libd_hnd) id.test_host.max_proc_fds

let exhaust_sys_fds_udp ts id =
  let num_libds_req = (id.test_host.max_sys_fds / id.test_host.max_proc_fds) + 1 in
  let rec outer_loop i libd_list =
    if(i<1) then libd_list
    else
      (let libd = dual_second_th_libd_create ts id (!tthee_baseport_2 + 5 + i) in
      exhaust_proc_fds_helper_udp (snd libd) id.test_host.max_proc_fds;
      outer_loop (i-1) (libd::libd_list))
  in
  outer_loop num_libds_req []

(* ---------------------------------------------------------------------- *)
(* Getting bound and/or connected sockets                                 *)
(* ---------------------------------------------------------------------- *)

(* Get a socket matching the quadruple sf (sock flavour) *)
let get_bound_socket_udp id ts sf =
  let sockcall = (tid_of_int_private 0, SOCKET(SOCK_DGRAM)) in
  let fd =
    match libd_call (the ts.th_libd_hnd) sockcall with
      (_,OK_FD(fd)) -> fd
    | _ -> raise(Drive_Failure("get_sock_udp() failed")) in
  let is1,ps1,is2,ps2 = sf in
  let i1 =
    match is1 with
      SF_IP_UNSPEC -> get_ip_udp WILDCARD_IP id ts
    | SF_IP_SPEC -> get_ip_udp LOCAL_IP id ts in
  let p1 =
    match ps1 with
      SF_PORT_UNSPEC -> get_port_udp WILDCARD_PORT id ts
    | SF_PORT_SPEC -> get_port_udp KNOWN_PORT id ts
    | SF_PORT_ERROR -> get_port_udp KNOWN_PORT id ts in
  let i2 =
    match is2 with
      SF_IP_UNSPEC -> get_ip_udp WILDCARD_IP id ts
    | SF_IP_SPEC -> get_ip_udp REMOTE_IP id ts in
  let p2 =
    match ps2 with
      SF_PORT_UNSPEC -> get_port_udp WILDCARD_PORT id ts
    | SF_PORT_SPEC -> get_port_udp KNOWN_PORT id ts
    | SF_PORT_ERROR -> raise(Drive_Failure("get_sock_udp() failed: ps2 = ERROR")) in
  let bindcall = (tid_of_int_private 0, BIND(fd,i1,p1)) in
  let _ =
    match i1,p1 with
      None,None -> ()
    | _ -> ignore(libd_call (the ts.th_libd_hnd) bindcall) in
  match ps1 with
    SF_PORT_ERROR ->
      (match i2 with
	None -> get_bound_state_udp (the ts.th_libd_hnd) fd; fd
      | Some(i2') ->
	  let connectcall = (tid_of_int_private 0, CONNECT(fd,i2',p2)) in
	  let _ = ignore(libd_call (the ts.th_libd_hnd) connectcall) in
	  get_bound_state_udp (the ts.th_libd_hnd) fd;
	  match p2 with
	    None -> fd
	  | Some(p2') ->
	      let sendto_call = (tid_of_int_private 0, SEND(fd, None, "Generate ICMP", [])) in
	      ignore(libd_call (the ts.th_libd_hnd) sendto_call);
	      delay 5.0; fd)
  | _ ->
      match i2 with
	None -> get_bound_state_udp (the ts.th_libd_hnd) fd; fd
      | Some(i2') ->
	  let connectcall = (tid_of_int_private 0, CONNECT(fd,i2',p2)) in
	  let _ = ignore(libd_call (the ts.th_libd_hnd) connectcall) in
	  get_bound_state_udp (the ts.th_libd_hnd) fd; fd

(* Get a socket matching the quadruple sf (sock flavour) *)
let get_bound_socket_reuse_udp id ts sf =
  let sockcall = (tid_of_int_private 0, SOCKET(SOCK_DGRAM)) in
  let fd =
    match libd_call (the ts.th_libd_hnd) sockcall with
      (_,OK_FD(fd)) -> fd
    | _ -> raise(Drive_Failure("get_sock_udp() failed")) in
  let reuse_call = (tid_of_int_private 0, SETSOCKBOPT(fd, SO_REUSEADDR, true)) in
  ignore(libd_call (the ts.th_libd_hnd) reuse_call);
  let is1,ps1,is2,ps2 = sf in
  let i1 =
    match is1 with
      SF_IP_UNSPEC -> get_ip_udp WILDCARD_IP id ts
    | SF_IP_SPEC -> get_ip_udp LOCAL_IP id ts in
  let p1 =
    match ps1 with
      SF_PORT_UNSPEC -> get_port_udp WILDCARD_PORT id ts
    | SF_PORT_SPEC -> get_port_udp KNOWN_PORT id ts
    | SF_PORT_ERROR -> get_port_udp KNOWN_PORT id ts in
  let i2 =
    match is2 with
      SF_IP_UNSPEC -> get_ip_udp WILDCARD_IP id ts
    | SF_IP_SPEC -> get_ip_udp REMOTE_IP id ts in
  let p2 =
    match ps2 with
      SF_PORT_UNSPEC -> get_port_udp WILDCARD_PORT id ts
    | SF_PORT_SPEC -> get_port_udp KNOWN_PORT id ts
    | SF_PORT_ERROR -> raise(Drive_Failure("get_sock_udp() failed: ps2 = ERROR")) in
  let bindcall = (tid_of_int_private 0, BIND(fd,i1,p1)) in
  let _ =
    match i1,p1 with
      None,None -> ()
    | _ -> ignore(libd_call (the ts.th_libd_hnd) bindcall) in
  match ps1 with
    SF_PORT_ERROR ->
      (match i2 with
	None -> get_bound_state_udp (the ts.th_libd_hnd) fd; fd
      | Some(i2') ->
	  let connectcall = (tid_of_int_private 0, CONNECT(fd,i2',p2)) in
	  let _ = ignore(libd_call (the ts.th_libd_hnd) connectcall) in
	  get_bound_state_udp (the ts.th_libd_hnd) fd;
	  match p2 with
	    None -> fd
	  | Some(p2') ->
	      let sendto_call = (tid_of_int_private 0, SEND(fd, None, "Generate ICMP", [])) in
	      ignore(libd_call (the ts.th_libd_hnd) sendto_call);
	      delay 5.0; fd)
  | _ ->
      match i2 with
	None -> get_bound_state_udp (the ts.th_libd_hnd) fd; fd
      | Some(i2') ->
	  let connectcall = (tid_of_int_private 0, CONNECT(fd,i2',p2)) in
	  let _ = ignore(libd_call (the ts.th_libd_hnd) connectcall) in
	  get_bound_state_udp (the ts.th_libd_hnd) fd; fd

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)

