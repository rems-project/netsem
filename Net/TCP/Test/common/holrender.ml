open Nettypes;;
(*open Netconv;;*)
open Holtypes;;
(*open Holparselib;;*)
open Printf;;
open Unix;;
(* open ThreadUnix;; *)
(*open Sock;;*)
(*open Render;;*)

exception Fatal of string

let render_bool x =
  match x with
    false -> "  F"
  | true -> "T  ";;

let render_icmp_proto p =
  match p with
    PROTO_TCP -> "PROTO_TCP"
  | PROTO_UDP -> "PROTO_UDP"

let render_icmp_unreach y =
  match y with
    NET -> "NET"
  | HOST -> "HOST"
  | PROTOCOL -> "PROTOCOL"
  | PORT -> "PORT"
  | SRCFAIL -> "SRCFAIL"
  | NEEDFRAG x  -> "NEEDFRAG " ^ (render_word16_option x)
  | NET_UNKNOWN -> "NET_UNKNOWN"
  | HOST_UNKNOWN -> "HOST_UNKNOWN"
  | ISOLATED -> "ISOLATED"
  | NET_PROHIB -> "NET_PROHIB"
  | HOST_PROHIB -> "HOST_PROHIB"
  | TOSNET -> "TOSNET"
  | TOSHOST -> "TOSHOST"
  | FILTER_PROHIB -> "FILTER_PROHIB"
  | PREC_VIOLATION -> "PREC_VIOLATION"
  | PREC_CUTOFF -> "PREC_CUTOFF"

let render_icmp_source_quench y =
  match y with
    QUENCH -> "QUENCH"
  | SQ_OTHER(x,z) -> "OTHER " ^ (Int64.to_string x) ^ " " ^ (Int64.to_string z)

let render_icmp_redirect y =
  match y with
    RD_NET -> "NET"
  | RD_HOST -> "HOST"
  | RD_TOSNET -> "TOSNET"
  | RD_TOSHOST -> "TOSHOST"
  | RD_OTHER(x,z) -> "OTHER " ^ (Int64.to_string x) ^ " " ^ (Int64.to_string z)

let render_icmp_time_exceeded y =
  match y with
    INTRANS -> "INTRANS"
  | REASS -> "REASS"
  | TX_OTHER(x,z) -> "OTHER " ^ (Int64.to_string x) ^ " " ^ (Int64.to_string z)

let render_icmp_paramprob y =
  match y with
    BADHDR -> "BADHDR"
  | NEEDOPT -> "NEEDOPT"
  | PP_OTHER(x,z) -> "OTHER " ^ (Int64.to_string x) ^ " " ^ (Int64.to_string z)

let render_icmp_type x =
  match x with
    ICMP_UNREACH y -> "ICMP_UNREACH " ^ (render_icmp_unreach y)
  | ICMP_SOURCE_QUENCH y -> "ICMP_SOURCE_QUENCH " ^ (render_icmp_source_quench y)
  | ICMP_REDIRECT y -> "ICMP_REDIRECT " ^ (render_icmp_redirect y)
  | ICMP_TIME_EXCEEDED y -> "ICMP_TIME_EXCEEDED " ^ (render_icmp_time_exceeded y)
  | ICMP_PARAMPROB y -> "ICMP_PARAMPROB " ^ (render_icmp_paramprob y)
  | ICMP_NONE -> "ICMP_OTHER";;  (*unknown case*)

let render_data x =
  let rec renderer y res=
    match y with
      [] -> res ^ "]"
    | [y] -> renderer [] (res ^ (sprintf "CHR %s " (Int64.to_string (y &: 0xff))))
    | y::ys -> renderer ys (res ^ (sprintf "CHR %s; " (Int64.to_string (y &: 0xff))))
  in
  renderer x "[";;

let is_printable x =
  (x >=. uint 32) && (x <=. uint 127) && (!=. x (uint 34))
                                         (* double quote not safe in strings *)

let make_pretty x str n =
  if is_printable x then String.set str n (Char.chr (Int64.to_int x))
  else
   (let fmtstr = sprintf "\\x%3.3x" (Int64.to_int x) in
    String.blit fmtstr 0 str n 5
   );;

let render_datastr d =
  let len =
    let rec countlen x =
      match x with
	[] -> 0
      |	x::xs -> (if is_printable x then 1 else 5) + countlen xs in
    countlen d in
  let str = String.create len in
  let rec makeString l n =
    match l with
      [] -> str
    | x::xs -> (make_pretty x str n;
		makeString xs (if is_printable x then n+1 else n+5)) in
  makeString d 0

let check_host_ip ipaddr hostip =
  match ipaddr with
    None -> false
  | Some x ->
      let a = Int64.to_string ((x >> 24) &: 0xff) in
      let b = Int64.to_string ((x >> 16) &: 0xff) in
      let c = Int64.to_string ((x >> 8) &: 0xff) in
      let d = Int64.to_string (x &: 0xff) in
      let pktip = a^"."^b^"."^c^"."^d in
      (pktip = hostip);;

let is_loopback_tcp (tcps: tcp_segment) =
  let src = tcps.is1 in
  let dst = tcps.is2 in
    if src=dst then true else
         let adr = (match dst with None -> (uint 0x7f000001) | Some(u) -> u) in
         let adr2 = Int64.logand adr ((*uint*) 0xff000000L) in
         let lb = (uint 0x7f000000) in
           if adr2=lb then true else false;;


let is_loopback_icmp (icmps: icmp_message_hol) =
  let src = icmps.icmp_hol_is1 in
  let dst = icmps.icmp_hol_is2 in
    if src=dst then true else
         let adr = (match dst with None -> (uint 0x7f000001) | Some(u) -> u) in
         let adr2 = Int64.logand adr ((*uint*) 0xff000000L) in
         let lb = (uint 0x7f000000) in
           if adr2=lb then true else false;;

let is_loopback_udp (udps: udp_datagram_hol) =
  let src = udps.udp_hol_is1 in
  let dst = udps.udp_hol_is2 in
  if src=dst then true else
  let adr = (match dst with None -> (uint 0x7f000001) | Some(u) -> u) in
  let adr2 = (Int64.logand adr ((*uint*) 0xff000000L)) in
  let lb = (uint 0x7f000000) in
  if adr2=lb then true else false;;

let tcp_segment_to_string (tcps:tcp_segment) =
  let ss = [ "<|\n"
	   ; sprintf "    is1 := %s;\n" (render_ip_option tcps.is1)
	   ; sprintf "    is2 := %s;\n" (render_ip_option tcps.is2)
	   ; sprintf "    ps1 := %s;\n" (render_port_option tcps.ps1)
	   ; sprintf "    ps2 := %s;\n" (render_port_option tcps.ps2)
	   ; sprintf "    seq := tcp_seq_local(n2w %s);\n" (Int64.to_string tcps.seq)
	   ; sprintf "    ack := tcp_seq_foreign(n2w %s);\n" (Int64.to_string tcps.ack)
	   ; sprintf "    URG := %s;\n" (render_bool tcps.uRG)
	   ; sprintf "    ACK := %s;\n" (render_bool tcps.aCK)
	   ; sprintf "    PSH := %s;\n" (render_bool tcps.pSH)
	   ; sprintf "    RST := %s;\n" (render_bool tcps.rST)
	   ; sprintf "    SYN := %s;\n" (render_bool tcps.sYN)
	   ; sprintf "    FIN := %s;\n" (render_bool tcps.fIN)
	   ; sprintf "    win := n2w %s;\n" (Int64.to_string tcps.win)
	   ; sprintf "    ws := %s;\n" (render_byte_option tcps.scale)
	   ; sprintf "    urp := n2w %s;\n" (Int64.to_string tcps.urp)
	   ; sprintf "    mss := %s;\n" (render_word16_option tcps.mss)
	   ; sprintf "    ts := %s;\n" (render_timestamp_option tcps.ts)
	   ; sprintf "    data := %s   (*\"%s\"*)\n" (render_data tcps.data) (render_datastr tcps.data)
	   ; "|>"
	   ] in
  let s = List.fold_right (fun a acc -> a^acc) ss "" in
    s
;;

let udp_datagram_hol_to_string udp =
  let ss =  "<|\n"
	    ^ sprintf "    is1 := %s;\n" (render_ip_option udp.udp_hol_is1)
	    ^ sprintf "    is2 := %s;\n" (render_ip_option udp.udp_hol_is2)
	    ^ sprintf "    ps1 := %s;\n" (render_port_option udp.udp_hol_ps1)
	    ^ sprintf "    ps2 := %s;\n" (render_port_option udp.udp_hol_ps2)
	    ^ sprintf "    data := %s   (*\"%s\"*)\n" (render_data udp.udp_hol_data) (render_datastr udp.udp_hol_data)
	    ^ "|>" in
    ss;;

let icmp_message_hol_to_string icmp =
  let ss = "<|\n"
	   ^ sprintf "    is1 := %s;\n" (render_ip_option icmp.icmp_hol_is1)
	   ^ sprintf "    is2 := %s;\n" (render_ip_option icmp.icmp_hol_is2)
	   ^ sprintf "    is3 := %s;\n" (render_ip_option icmp.icmp_hol_is3)
	   ^ sprintf "    is4 := %s;\n" (render_ip_option icmp.icmp_hol_is4)
	   ^ sprintf "    ps3 := %s;\n" (render_port_option icmp.icmp_hol_ps3)
	   ^ sprintf "    ps4 := %s;\n" (render_port_option icmp.icmp_hol_ps4)
	   ^ sprintf "    proto := %s;\n" (render_icmp_proto icmp.icmp_hol_proto)
	   ^ sprintf "    seq := NONE;\n"
	   ^ sprintf "    t := %s\n" (render_icmp_type icmp.icmp_hol_type)
	   ^ "|>" in
    ss;;

let holmsg_to_string msg = match msg with
  | TCPMSG tcps -> "TCP(" ^ (tcp_segment_to_string tcps) ^ ")"
  | UDPMSG udp_dg_hol -> "UDP(" ^ (udp_datagram_hol_to_string udp_dg_hol) ^ ")"
  | ICMPMSG icmp_msg_hol -> "ICMP(" ^ (icmp_message_hol_to_string icmp_msg_hol) ^ ")";;

let render_tcp_inner_no_semicolon (tcps:tcp_segment) b = match b with
  (* FIXME tjr checking loopback at this point is madness *)
    | SENDDGRAM ->
	if is_loopback_tcp tcps
	then "Lh_loopdatagram(" ^ (holmsg_to_string (TCPMSG tcps)) ^ ")"
	else "Lh_senddatagram(" ^ (holmsg_to_string (TCPMSG tcps)) ^ ")"
    | LOOPDGRAM -> "Lh_loopdatagram(" ^ (holmsg_to_string (TCPMSG tcps)) ^ ")"
    | RECVDGRAM -> "Lh_recvdatagram(" ^ (holmsg_to_string (TCPMSG tcps)) ^ ")";;

let render_tcp_inner (tcps:tcp_segment) b =
  render_tcp_inner_no_semicolon tcps b ^ " ;\n";;

(* FIXME the rest of the printing functions should be similarly
   refactored. In fact, I think this whole directory is pretty much
   beyond the pale. *)

let render_icmp_inner_no_semicolon icmp b = match b with
  | SENDDGRAM ->
      if is_loopback_icmp icmp
      then "Lh_loopdatagram(" ^ (holmsg_to_string (ICMPMSG icmp)) ^ ")"
      else "Lh_senddatagram(" ^ (holmsg_to_string (ICMPMSG icmp)) ^ ")"
  | LOOPDGRAM -> "Lh_loopdatagram(" ^ (holmsg_to_string (ICMPMSG icmp)) ^ ")"
  | RECVDGRAM -> "Lh_recvdatagram(" ^ (holmsg_to_string (ICMPMSG icmp)) ^ ")";;

let render_icmp_inner icmp b =
  render_icmp_inner_no_semicolon icmp b ^ ";\n";;

let render_udp_inner_no_semicolon udp b = match b with
  | SENDDGRAM ->
      if is_loopback_udp udp
      then "Lh_loopdatagram(" ^ (holmsg_to_string (UDPMSG udp)) ^ ")"
      else "Lh_senddatagram(" ^ (holmsg_to_string (UDPMSG udp)) ^ ")"
  | LOOPDGRAM -> "Lh_loopdatagram(" ^ (holmsg_to_string (UDPMSG udp)) ^ ")"
  | RECVDGRAM -> "Lh_recvdatagram(" ^ (holmsg_to_string (UDPMSG udp)) ^ ")";;

let render_udp_inner udp b =
  render_udp_inner_no_semicolon udp b ^ ";\n";;

