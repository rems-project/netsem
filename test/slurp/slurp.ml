(* slurp.ml - slurps in a lib_pcap (tcpdump) dump file / stream *)
(* 2002-07-29.. *)
(* Time-stamp: <2002-08-07 12:03:48 kw217@astrocyte.cl.cam.ac.uk> *)
(* Direct libpcap support and HOL label output added by smb50 *)

open Nettypes;;
open Netconv;;
open Net2hol;;
open Netipreass;;
open Pcapfile;;
open Pcapinterface;;
open Holtypes;;
open Debugrenderer;;
open Holrender;;
open Printf;;
open Unix;;
open Platform;;
open Sock;;

exception Fatal of string * unit;;

let cmdlineargs = "
Usage: slurp [-h hostip] iface TCP ip port [filter]
       slurp [-h hostip] iface UNIX socket [filter]
where iface is the interface to sniff on
      ip and port specify the socket to output HOL labels to
      sockets specifies the UNIX domain socket to output HOL labels to
      filter is an option filter string (enclosed in double quotes)
      TCP selects output to TCP socket mode
      UNIX selects output to UNIX domain socket mode\n";;

let check_cmdline_args argv =
  let len = Array.length argv in
  if(len < 4 || len > 8) then
    raise(Fatal("Incorrect arguments: ", print_endline (cmdlineargs)))
  else
    if((Array.get argv 1) = "-h") then
      let hostip = Some (Array.get argv 2) in
      let iface = Array.get argv 3 in
      let ty = Array.get argv 4 in
      let ip = Array.get argv 5 in
      let(port, filter) =
	if(ty = "TCP") then
	  (Array.get argv 6,
	   if(len = 8) then Array.get argv 7 else "")
	else
	  ("",
	   if(len = 7) then Array.get argv 6 else "")
      in
      (hostip, iface, ty, ip, port, filter)
    else
      let hostip = None in
      let iface = Array.get argv 1 in
      let ty = Array.get argv 2 in
      let ip = Array.get argv 3 in
      let (port, filter) =
	if(ty = "TCP") then
	  (Array.get argv 4,
	   if(len=6) then Array.get argv 5 else "")
	else
	  ("",
	   if(len=5) then Array.get argv 4 else "")
      in
      (hostip, iface, ty, ip, port, filter)

let render_number = ref (uint 0);;

(* this function was previously in holrender.ml *)
let render_tcp_to_socket sd (tcps: tcp_segment) tstamp hostip iface =
  let sendrecv =
    match iface with
      OTHERIFACE ->
	(match hostip with
          None -> RECVDGRAM
         | Some x ->
             match check_host_ip tcps.is1 x with
	       true -> SENDDGRAM
             | false -> RECVDGRAM)
    | _ -> LOOPDGRAM in
  let time = sprintf "(** %s.%s \"slurp%s\" **)\n"
			(Int64.to_string tstamp.t_sec)
      (lpad_numeric_string (Int64.to_string tstamp.t_usec) 6)
      (Int64.to_string (!render_number)) in
  let _ = render_number := !render_number +. (uint 1) in
  let _ = Sock.write sd time in
  let s = render_tcp_inner tcps sendrecv in
  let _ = Sock.write sd s in
    ();;


let render_icmp_to_socket sd icmp tstamp hostip iface =
  let sendrecv = match iface with
       OTHERIFACE -> (match hostip with
               None -> RECVDGRAM
             | Some x ->
                   match check_host_ip icmp.icmp_hol_is1 x with
	              true -> SENDDGRAM
                    | false -> RECVDGRAM)
      | _ -> LOOPDGRAM in
  let time = sprintf "(** %s.%s \"slurp%s\" **)\n"
      (Int64.to_string tstamp.t_sec)
      (lpad_numeric_string (Int64.to_string tstamp.t_usec) 6)
      (Int64.to_string (!render_number)) in
  let _ = render_number := (!render_number) +. (uint 1) in
  let _ = Sock.write sd time in
  let s = render_icmp_inner icmp sendrecv in
  let _ = Sock.write sd s in
    ();;

let render_udp_to_socket sd udp tstamp hostip iface =
  let sendrecv =
    match iface with
      OTHERIFACE ->
	(match hostip with
	  None -> RECVDGRAM
	| Some x ->
	    match check_host_ip udp.udp_hol_is1 x with
	    true -> SENDDGRAM
	    | false -> RECVDGRAM)
    | _ -> LOOPDGRAM in
  let time = sprintf "(** %s.%s \"slurp%s\" **)\n"
      (Int64.to_string tstamp.t_sec)
      (lpad_numeric_string (Int64.to_string tstamp.t_usec) 6)
      (Int64.to_string (!render_number)) in
  let _ = render_number := (!render_number) +. (uint 1) in
  let _ = Sock.write sd time in
  let s = render_udp_inner udp sendrecv in
  let _ = Sock.write sd s in
    ();;

let connect_socket socktype ip port =
  if(socktype = "TCP") then
    let sd = socket PF_INET SOCK_STREAM 6 in
    let _ = setsockopt sd SO_REUSEADDR true in
    let _ = connect sd (ADDR_INET(inet_addr_of_string ip, int_of_string port)) in
    sd
  else
    let sd = socket PF_UNIX SOCK_STREAM 0 in
    let _ = setsockopt sd SO_REUSEADDR true in
    let _ = connect sd (ADDR_UNIX(ip)) in
    sd;;


(* pull an IP PCAP packet off the stream and parse it *)
let parse_pcaplive_ip_packet c iface =
  match iface with OTHERIFACE ->
                      let cap = skip_ip_eth_header c in
                      let ip = parse_ip_packet cap in
                      ip,c
                 | _ ->
                      let cap = skip_loopback_header c iface in
                      let ip = parse_ip_packet cap in
                      ip, c;;

let render_h h =
  match h with
    None -> "None"
  | Some x -> sprintf "Some %s" x;;

let _ =
  let (hostip, iface, socktype, ip, port, filter) = check_cmdline_args Sys.argv in
  let ph = pcap_open_live iface 65535 true 5 in
  let (net, mask) = pcap_lookupnet iface in
  let whichiface = match iface with "lo0" -> LOOPIFACE_BSD
                                  | "lo"  -> LOOPIFACE_LINUX
                                  | "winloop" -> LOOPIFACE_WIN
                                  | _ -> OTHERIFACE in
  let pcap_prog = pcap_compile ph filter true mask in
  let _ = pcap_setfilter ph pcap_prog in
  let sdconn = connect_socket socktype ip port in

  let out_header = sprintf "(* Netsem Slurper - Initialised on host: %s *)\n"
      (Platform.gethostname ()) in
  let out_header2 = sprintf "(* Date: %s Source Host Option (-h): %s *)\n"
      (Platform.gettimeofday ()) (render_h hostip) in
  let out_header3 = sprintf "(* NTP STATUS:\n" in
  let out_header3a = sprintf " *)\n" in
  let out_header4 =  sprintf "(* -------------------------------------------------------------------------- *)\n" in
  let out_header5 = "(* BEGIN *)\n" in
  let _ = (Sock.write sdconn out_header; Sock.write sdconn out_header2;
	  Sock.write sdconn out_header3) in
  if(Platform.check_platform () != WIN32) then
    let ntp_args = Array.of_list ["/usr/bin/ntpq" ; "-c"; "readvar 0 offset"] in
    let ntp_pid = create_process "/usr/bin/ntpq" ntp_args stdin sdconn stdout in
    let _ = waitpid [] ntp_pid in ()
  else ();
  let _ = (Sock.write sdconn out_header3a; Sock.write sdconn out_header4; Sock.write sdconn out_header5) in

  let rec loop st =
    let (hdr, pkt) =
      let rec loop2 x = try pcap_next ph with Pcap_error(_,"returned no data") -> loop2 x
      in loop2 ()
    in
    let (ip, _) = parse_pcaplive_ip_packet pkt whichiface in
    match ip_input st hdr.tstamp ip with
      (st,Some ip) ->
	(if (ip.ip_h.ip_p ==. ip_proto_tcp) then
	  let tcp = parse_tcp_datagram ip in
	  let holtcp = tcp_segment_of_tcp_packet tcp in
          (*let _ = print_endline "----TCP datagram:----" in*)
	  let _ = render_tcp_to_socket sdconn holtcp hdr.tstamp hostip whichiface in
          loop st;
	else
	  if(ip.ip_h.ip_p ==. ip_proto_icmp) then
	    let icmp = parse_icmp_message ip in
	    let holicmp = hol_icmp_of_icmp_datagram icmp in
	    (*let _ = print_endline "----ICMP packet----" in*)
	    let _ = render_icmp_to_socket sdconn holicmp hdr.tstamp hostip whichiface in
	    loop st;
	  else
	    if(ip.ip_h.ip_p ==. ip_proto_udp) then
	      let udp = parse_udp_datagram ip in
	      let holudp = hol_udp_of_udp_datagram udp in
	      (* let _ = print_endline "----UDP datagram----" in *)
	      let _ = render_udp_to_socket sdconn holudp hdr.tstamp hostip whichiface in
	      loop st;
	    else (* not a protocol we're interested in *) ())
    | (st,None) ->
        let _ = print_endline "----fragment----" in
        loop st
  in
  loop init_ip_input_state;;







