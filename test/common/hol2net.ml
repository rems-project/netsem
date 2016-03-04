open Nettypes;;
open Netconv;;
open Holtypes;;
open Holparselib;;
open Printf;;
open Platform;;

(* This fabricates some fields due to the lossy
   representation of HOL tcp segments *)

let tcp_segment_to_tcp s =
  let is1 = match s.is1 with
    None -> uint 0
  | Some x -> x in
  let is2 = match s.is2 with
    None -> uint 0
  | Some x -> x in
  let (sz1, scaleopt) = match s.scale with
    None -> (0, [])
  | Some x -> (1, [(TCPOPT_WINDOW x)]) in
  let (sz2, tops) = match s.ts with
    None -> (sz1, scaleopt)
  | Some(x,y) -> (sz1+3, (TCPOPT_TIMESTAMP (x, y))::scaleopt) in
  let (sz3, opts) = match s.mss with
    None -> (sz2, tops)
  | Some x -> (sz2+1, (TCPOPT_MAXSEG x)::tops) in
  let tcpdata = s.data in
  let tcpheader =
    {
     tcp_sport = (match s.ps1 with
       None -> uint 0
     | Some x -> x);
     tcp_dport = (match s.ps2 with
       None -> uint 0
     | Some x -> x);
     tcp_seq = s.seq;
     tcp_ack = s.ack;
     tcp_off = uint 5 +. uint sz3;  (* Add option size -- factoring in for any padding required *)
     tcp_x2 = uint 0;    (* Fabricated -- but assumed MBZ *)
     tcp_URG = s.uRG;
     tcp_ACK = s.aCK;
     tcp_PSH = s.pSH;
     tcp_RST = s.rST;
     tcp_SYN = s.sYN;
     tcp_FIN = s.fIN;
     tcp_win = s.win;
     tcp_sum = uint 0;
     tcp_urp = s.urp;
     tcp_opts = opts;
   } in
  (is1, is2, tcpheader, tcpdata);;


let rec calc_csum l sum =
  match l with
    [] ->
      (let rec loop s =
	if((s>>16) >=. uint 1) then
	  loop ((s &. (Int64.of_string "0xffff")) +. (s>>16))
	else
	  s
      in
      loop sum)
  | (a::b::ls) -> calc_csum ls (sum +. ((a<<8) |. b))
  | (a::ls) -> calc_csum ls (sum +. ((a<<8) |. uint 0))


(* Adds in any necessary padding *)
let rec add_tcp_header_opts opts d =
  match opts with
    [] -> d
  | (TCPOPT_MAXSEG(x)::xs) -> (uint 2)::(uint 4)::(output_uint16_net x
						     (add_tcp_header_opts xs d))
  | (TCPOPT_WINDOW(x)::xs) -> (uint 1)::(uint 3)::(uint 3)::x::(add_tcp_header_opts xs d)
  | (TCPOPT_TIMESTAMP(x,y)::xs) -> (uint 1)::(uint 1)::(uint 8)::(uint 10)::(output_uint32_net x
							  (output_uint32_net y
							     (add_tcp_header_opts xs d)))
  | _ -> d;;   (* To make pattern matching exhaustive (as not all of the TCPOPTs are used
		  in the HOL model yet) *)


let tcp_flatten s =
  let (is1, is2, tcpheader, tcpdata) =
    tcp_segment_to_tcp s in
  let calc_pseudo_header_csum i1 i2 h d =
    let tcplen = uint (List.length d) +. (h.tcp_off *. uint 4) in
    let p1 = output_uint16_net tcplen [] in
    let p2 = uint 0 :: uint 6 :: p1 in    (* MBZ and protocol *)
    let p3 = output_uint32_net i2 p2 in
    let p4 = output_uint32_net i1 p3 in
    let sum = calc_csum p4 (uint 0) in
    sum in
  let pseudo_header_csum = calc_pseudo_header_csum is1 is2 tcpheader tcpdata in
  let h1 = add_tcp_header_opts tcpheader.tcp_opts tcpdata in
  let h2 = output_uint16_net tcpheader.tcp_urp h1 in
  let h3 = (uint 0)::(uint 0)::h2 in
  let h4 = output_uint16_net tcpheader.tcp_win h3 in
  let moveflags f shl =
    match f with
      true -> (uint 1) << shl
    | false -> uint 0 in
  let mapflags th =
    (moveflags th.tcp_URG 5) |. (moveflags th.tcp_ACK 4) |.
    (moveflags th.tcp_PSH 3) |. (moveflags th.tcp_RST 2) |.
    (moveflags th.tcp_SYN 1) |. (moveflags th.tcp_FIN 0) in
  let h5 = output_uint16_net ((tcpheader.tcp_off << 12) |. (tcpheader.tcp_x2 << 6) |.
                              (mapflags tcpheader)) h4 in
  let h6 = output_uint32_net tcpheader.tcp_ack h5 in
  let h7 = output_uint32_net tcpheader.tcp_seq h6 in
  let h8 = output_uint16_net tcpheader.tcp_dport h7 in
  let h9 = output_uint16_net tcpheader.tcp_sport h8 in
  let checksum = calc_csum h9 pseudo_header_csum in
  let inverted_csum = (Int64.lognot checksum) &. (Int64.of_string "0xFFFF") in
  let write_checksum_to_segment segment checksum =
    let rec loop l cs n =
      match l with
	[] -> []
      | (a::b::xs) ->
	  if n=16 then
	    output_uint16_net checksum xs
	  else
	    a::b::(loop xs cs (n+2))
      | (x::xs) -> x::(loop xs cs (n+1))
    in
    loop segment checksum 0 in
  let tcp_segment = write_checksum_to_segment h9 inverted_csum in
  (is1, is2, tcp_segment);;

let udp_flatten u =
  let calc_pseudo_header_csum is1 is2 ps1 ps2 l d =
    let p1 = output_uint16_net (uint 0) d in
    let p2 = output_uint16_net l p1 in
    let p3 = output_uint16_net ps2 p2 in
    let p4 = output_uint16_net ps1 p3 in
    let p5 = output_uint16_net l p4 in
    let p6 = uint 0 :: uint 17 :: p5 in
    let p7 = output_uint32_net is2 p6 in
    let p8 = output_uint32_net is1 p7 in
    let sum = calc_csum p4 (uint 0) in
    sum in
  let i1 =
    (match u.udp_hol_is1 with
      None -> uint 0
    | Some(x) -> x) in
  let i2 =
    (match u.udp_hol_is2 with
      None -> uint 0
    | Some(x) -> x) in
  let p1 =
    (match u.udp_hol_ps2 with
      None -> uint 0
    | Some(x) -> x) in
  let p2 =
    (match u.udp_hol_ps2 with
      None -> uint 0
    | Some(x) -> x) in
  let len = uint (8 + (List.length u.udp_hol_data)) in
  let cs = uint 0 in (* calc_pseudo_header_csum i1 i2 p1 p2 len u.udp_hol_data in *)
  let h1 = output_uint16_net cs u.udp_hol_data in
  let h2 = output_uint16_net len h1 in
  let h3 = output_uint16_net p2 h2 in
  let h4 = output_uint16_net p1 h3 in
  (i1, i2, h4);;

(* Follow the standard Berkley implementation and base the
   initial IP identification value on timeofday *)
let ip_idno = ref (Int64.of_float (Unix.time ()));;

let ip_encapsulate i1 i2 proto pkt =
  let ip_v = uint 4 in
  let ip_hl = uint 5 in
  let ip_tos = uint 0  in
  let ip_len = (ip_hl *. uint 4) +. (uint (List.length pkt)) in
  let ip_id = !ip_idno in
  let _ = ip_idno := !ip_idno +. uint 1 in
  let ip_off = Int64.of_string "0x4000" in  (* set the df flag only *)
  let ip_ttl = Int64.of_string "0x40" in
  let ip_p = proto in
  let ip_sum = uint 0 in
  let ip_src = i1 in
  let ip_dst = i2 in
  let ip_data = pkt in
  let p1 = [] in (* don't put data on the end until we calc the csum *)
  let p2 = output_uint32_net ip_dst p1 in
  let p3 = output_uint32_net ip_src p2 in
  let p4 = output_uint16_net ip_sum p3 in
  let p5 = ip_p::p4 in
  let p6 = ip_ttl::p5 in
  let p7 = match (check_platform ()) with
    BSD -> output_uint16 Little ip_off p6
  | _ -> output_uint16_net ip_off p6 in
  let p8 = output_uint16_net ip_id p7 in
  let p9 = match (check_platform ()) with
    BSD -> output_uint16 Little ip_len p8
  | LINUX -> output_uint16_net (uint 0) p8
  | _ -> output_uint16_net ip_len p8 in
  (*let p9 = output_uint16_net ip_len p8 in*)
  let p10 = ip_tos::p9 in
  let p11 = ((ip_v<<4) |. ip_hl)::p10 in
  let csum = calc_csum p11 (uint 0) in
  let p =
    let write_checksum_to_packet hdr checksum =
    let rec loop l cs n =
      match l with
	[] -> []
      | (a::b::xs) ->
	  if n=10 then
	    output_uint16_net checksum xs
	  else
	    a::b::(loop xs cs (n+2))
      | (x::xs) -> x::(loop xs cs (n+1))
    in
    loop hdr checksum 0
    in
    match (check_platform ()) with
      BSD -> p11
    | LINUX -> p11
    | _ -> write_checksum_to_packet p11 csum in
  let packet = p @ ip_data in
  packet;;


let uint_list_to_string l =
  let newl =
    let rec loop1 l =
      match l with
	[] -> []
      |	x::xs -> (char_of_int (Int64.to_int x))::(loop1 xs)
    in loop1 l in
  let len = List.length newl in
  let str1 = String.create len in
  let _ =
    let rec loop2 l c =
      match l with
	[] -> ()
      |	x::xs -> (String.set str1 c x); loop2 xs (c+1) in
    loop2 newl 0 in
  str1;;


let icmp_flatten m =
  let (ty, cd) =
    match m.icmp_hol_type with
      ICMP_UNREACH NET -> iCMP_UNREACH_NET
    | ICMP_UNREACH HOST -> iCMP_UNREACH_HOST
    | ICMP_UNREACH PROTOCOL -> iCMP_UNREACH_PROTOCOL
    | ICMP_UNREACH PORT -> iCMP_UNREACH_PORT
    | ICMP_UNREACH NEEDFRAG(x) -> iCMP_UNREACH_NEEDFRAG
    | ICMP_UNREACH SRCFAIL -> iCMP_UNREACH_SRCFAIL
    | ICMP_UNREACH NET_UNKNOWN -> iCMP_UNREACH_NET_UNKNOWN
    | ICMP_UNREACH HOST_UNKNOWN -> iCMP_UNREACH_HOST_UNKNOWN
    | ICMP_UNREACH ISOLATED -> iCMP_UNREACH_ISOLATED
    | ICMP_UNREACH NET_PROHIB -> iCMP_UNREACH_NET_PROHIB
    | ICMP_UNREACH HOST_PROHIB -> iCMP_UNREACH_HOST_PROHIB
    | ICMP_UNREACH TOSNET -> iCMP_UNREACH_TOSNET
    | ICMP_UNREACH TOSHOST -> iCMP_UNREACH_TOSHOST
    | ICMP_UNREACH FILTER_PROHIB -> iCMP_UNREACH_FILTER_PROHIB
    | ICMP_UNREACH PREC_VIOLATION -> iCMP_UNREACH_PREC_VIOLATION
    | ICMP_UNREACH PREC_CUTOFF -> iCMP_UNREACH_PREC_CUTOFF
    | ICMP_SOURCE_QUENCH QUENCH -> iCMP_SOURCE_QUENCH
    | ICMP_SOURCE_QUENCH SQ_OTHER(_,_) -> iCMP_SOURCE_QUENCH_OTHER
    | ICMP_TIME_EXCEEDED INTRANS -> iCMP_TIME_EXCEEDED_INTRANS
    | ICMP_TIME_EXCEEDED REASS -> iCMP_TIME_EXCEEDED_REASS
    | ICMP_TIME_EXCEEDED TX_OTHER (_,_) -> iCMP_TIME_EXCEEDED_OTHER
    | ICMP_PARAMPROB BADHDR -> iCMP_PARAMPROB_BADHDR
    | ICMP_PARAMPROB NEEDOPT -> iCMP_PARAMPROB_NEEDOPT
    | ICMP_PARAMPROB PP_OTHER (_,_) -> iCMP_PARAMPROB_OTHER
    | ICMP_REDIRECT RD_NET -> iCMP_REDIRECT_NET
    | ICMP_REDIRECT RD_HOST -> iCMP_REDIRECT_HOST
    | ICMP_REDIRECT RD_TOSNET -> iCMP_REDIRECT_TOSNET
    | ICMP_REDIRECT RD_TOSHOST -> iCMP_REDIRECT_TOSHOST
    | ICMP_REDIRECT RD_OTHER (_,_) -> iCMP_REDIRECT_OTHER
    | ICMP_NONE -> raise(ParseError("ICMP_NONE: don't understand the ICMP type"));
	(uint 0, uint 0) in
  let i1 =
    match m.icmp_hol_is1 with
      None -> uint 0
    | Some x -> x in
  let i2 =
    match m.icmp_hol_is2 with
      None -> uint 0
    | Some x -> x in
  let i3 =
    match m.icmp_hol_is3 with
      None -> uint 0
    | Some x -> x in
  let i4 =
    match m.icmp_hol_is4 with
      None -> uint 0
    | Some x -> x in
  let p3 =
    match m.icmp_hol_ps3 with
      None -> uint 0
    | Some x -> x in
  let p4 =
    match m.icmp_hol_ps4 with
      None -> uint 0
    | Some x -> x in
  let pr =
    match m.icmp_hol_proto with
      PROTO_TCP -> (uint 6)
    | PROTO_UDP -> (uint 17) in
  let a1 = output_uint32_net (uint 0) [] in (* last 4 bytes of data *)
  let a2 = output_uint16_net p4 a1 in (* dest port *)
  let a3 = output_uint16_net p3 a2 in (* src port *)
  let a4 = ip_encapsulate i3 i4 pr a3 in
  let a5 = output_uint32_net (uint 0) a4 in (* 4 unused bytes *)
  let a6 = output_uint16_net (uint 0) a5 in (* temp csum *)
  let a7 = cd::a6 in (* code *)
  let a8 = ty::a7 in (* type *)
  let csum = calc_csum a8 (uint 0) in
  let pkt =
    let write_checksum_to_packet hdr checksum =
      let rec loop l cs n =
	match l with
	  [] -> []
	| (a::b::xs) ->
	    if n=2 then
	      output_uint16_net checksum xs
	    else
	      a::b::(loop xs cs (n+2))
	| (x::xs) -> x::(loop xs cs (n+1))
      in
      loop hdr checksum 0
    in
    write_checksum_to_packet a8 csum in
  (i1, i2, pkt)

