(* ***************************** *)
(* types for idealised HOL model *)
(* ***************************** *)

open Nettypes;;
open Netconv;;

(* tcp segments as used by our HOL model (isomorphic to the HOL record
type, perhaps modulo the word16-ness ).  We expect to have a
(slightly) lossy and partial map from tcp_packet into tcp_segment. *)

(* HOL-model TCP segment *)
type tcp_segment = {
    is1 : ip option ;
    is2 : ip option ;
    ps1 : port option;
    ps2 : port option;
    seq : word32;         (* sequence_number       *)
    ack : word32;         (* acknowledgment_number *)
    uRG : bool;
    aCK : bool;
    pSH : bool;
    rST : bool;
    sYN : bool;
    fIN : bool;
    win : word16;         (* window size *)
    urp : word16;

    (* and TCP options, which we pull out as follows.  We need to find
       out the correct names *)

    mss : word16 option;            (* maximum segment size TCPv2p865 *)
    scale : byte option;            (* window scaling; probably 0..14? *)
    ts : (word32 * word32) option;  (* _val and _ecr TCPv2p867: RFC1323, value and echo-reply *)

    data : byte list;
}


(* ***************************************** *)
(* lossy and asserty conversion to HOL model *)
(* ***************************************** *)

let tcp_segment_of_tcp_packet p =
  (* this is now lossy and asserty (before, we were not lossy and we were only slightly asserty - but (PS) should be*)
  { is1 = ip_option_of_uint p.tcp_iph.ip_src;
    is2 = ip_option_of_uint p.tcp_iph.ip_dst;
    ps1 = port_option_of_uint p.tcp_h.tcp_sport;
    ps2 = port_option_of_uint p.tcp_h.tcp_dport;
    seq = p.tcp_h.tcp_seq;
    ack = p.tcp_h.tcp_ack;
    uRG = p.tcp_h.tcp_URG;
    aCK = p.tcp_h.tcp_ACK;
    pSH = p.tcp_h.tcp_PSH;
    rST = p.tcp_h.tcp_RST;
    sYN = p.tcp_h.tcp_SYN;
    fIN = p.tcp_h.tcp_FIN;
    win = p.tcp_h.tcp_win;
    urp = p.tcp_h.tcp_urp;
    mss   = (match (List.filter
                      (fun opt -> match opt with TCPOPT_MAXSEG(_) -> true | _ -> false)
                      p.tcp_h.tcp_opts) with
               [] ->
                 None
             | [TCPOPT_MAXSEG(mss)] ->
                 Some(mss)
             | _ ->
                 assert_packet_wf "TCPOPT_MAXSEG repeated" false;
                 None (*notreached*));
    scale = (match (List.filter
                      (fun opt -> match opt with TCPOPT_WINDOW(_) -> true | _ -> false)
                      p.tcp_h.tcp_opts) with
               [] ->
                 None
             | [TCPOPT_WINDOW(scale)] ->
                 (* RFC1323 page 11 says log and clip if out of range *)

		 (* SMB 20030805: We probably don't want to check this -- we like broken segments! *)
		 (* assert_packet_wf "TCPOPT_WINDOW out of range" (int scale <= 14); *)
                 Some(scale)
             | _ ->
                 assert_packet_wf "TCPOPT_WINDOW repeated" false;
                 None (*notreached*));
    ts    = (match (List.filter
                      (fun opt -> match opt with TCPOPT_TIMESTAMP(_) -> true | _ -> false)
                      p.tcp_h.tcp_opts) with
               [] ->
                 None
             | [TCPOPT_TIMESTAMP(ts_val,ts_ecr)] ->
                 Some(ts_val,ts_ecr)
             | _ ->
                 assert_packet_wf "TCPOPT_TIMESTAMP repeated" false;
                 None (*notreached*));
    data = p.tcp_data;
  }

type protocol =
    PROTO_UDP
  | PROTO_TCP

type icmp_unreach_code =
    NET
  | HOST
  | PROTOCOL
  | PORT
  | SRCFAIL
  | NEEDFRAG of word16 option
  | NET_UNKNOWN
  | HOST_UNKNOWN
  | ISOLATED
  | NET_PROHIB
  | HOST_PROHIB
  | TOSNET
  | TOSHOST
  | FILTER_PROHIB
  | PREC_VIOLATION
  | PREC_CUTOFF

type icmp_source_quench_code =
    QUENCH
  | SQ_OTHER of byte * word32

type icmp_redirect_code =
    RD_NET
  | RD_HOST
  | RD_TOSNET
  | RD_TOSHOST
  | RD_OTHER of byte * word32

type icmp_time_exceeded_code =
    INTRANS
  | REASS
  | TX_OTHER of byte * word32

type icmp_paramprob_code =
    BADHDR
  | NEEDOPT
  | PP_OTHER of byte * word32

type icmp_type =
    ICMP_UNREACH of icmp_unreach_code
  | ICMP_SOURCE_QUENCH of icmp_source_quench_code
  | ICMP_REDIRECT of icmp_redirect_code
  | ICMP_TIME_EXCEEDED of icmp_time_exceeded_code
  | ICMP_PARAMPROB of icmp_paramprob_code
  | ICMP_NONE

type icmp_message_hol = {
    icmp_hol_is1 : ip option;
    icmp_hol_is2 : ip option;
    icmp_hol_is3 : ip option;
    icmp_hol_is4 : ip option;
    icmp_hol_ps3 : port option;
    icmp_hol_ps4 : port option;
    icmp_hol_proto : protocol;
    icmp_hol_seq : word32 option;
    icmp_hol_type : icmp_type;
  }


type lh_dgram_render = SENDDGRAM | LOOPDGRAM | RECVDGRAM;;


let hol_icmp_of_icmp_datagram dgram =
  let (is1, is2, is3, is4, ps3, ps4, seq, itype,pr) =
    match dgram.icmp_msg.icmp_body with
(*    | ICMP_QUERY(c) ->
        (None, None, None, None, None, None, None, ICMP_NONE)
    | ICMP_ECHO_REQUEST(ident, seq, c) ->
	(Some dgram.icmp_iph.ip_src, Some dgram.icmp_iph.ip_dst,
	 None, None, None, None, None, ICMP_NONE)
    | ICMP_ECHO_REPLY(ident, seq, c) ->
	(Some dgram.icmp_iph.ip_src, Some dgram.icmp_iph.ip_dst,
	 None, None, None, None, None, ICMP_NONE)
*)
      ICMP_ERROR(ty, cd, mtu, header, src, dest) ->
	let htype =
	  if (ty,cd) = iCMP_UNREACH_NET  then ICMP_UNREACH NET
	  else if (ty,cd) = iCMP_UNREACH_HOST then ICMP_UNREACH HOST
	  else if (ty,cd) = iCMP_UNREACH_PROTOCOL then ICMP_UNREACH PROTOCOL
	  else if (ty,cd) = iCMP_UNREACH_PORT then ICMP_UNREACH PORT
	  else if (ty,cd) = iCMP_UNREACH_NEEDFRAG then ICMP_UNREACH (NEEDFRAG mtu)
	  else if (ty,cd) = iCMP_UNREACH_SRCFAIL then ICMP_UNREACH SRCFAIL
	  else if (ty,cd) = iCMP_UNREACH_NET_UNKNOWN then ICMP_UNREACH NET_UNKNOWN
	  else if (ty,cd) = iCMP_UNREACH_HOST_UNKNOWN then ICMP_UNREACH HOST_UNKNOWN
	  else if (ty,cd) = iCMP_UNREACH_ISOLATED then ICMP_UNREACH ISOLATED
	  else if (ty,cd) = iCMP_UNREACH_NET_PROHIB then ICMP_UNREACH NET_PROHIB
	  else if (ty,cd) = iCMP_UNREACH_HOST_PROHIB then ICMP_UNREACH HOST_PROHIB
	  else if (ty,cd) = iCMP_UNREACH_TOSNET then ICMP_UNREACH TOSNET
	  else if (ty,cd) = iCMP_UNREACH_TOSHOST then ICMP_UNREACH TOSHOST
	  else if (ty,cd) = iCMP_UNREACH_FILTER_PROHIB then ICMP_UNREACH FILTER_PROHIB
	  else if (ty,cd) = iCMP_UNREACH_PREC_VIOLATION then ICMP_UNREACH PREC_VIOLATION
	  else if (ty,cd) = iCMP_UNREACH_PREC_CUTOFF then ICMP_UNREACH PREC_CUTOFF
	  else if (ty,cd) = iCMP_SOURCE_QUENCH then ICMP_SOURCE_QUENCH QUENCH
	  else if (ty,cd) = iCMP_TIME_EXCEEDED_INTRANS then ICMP_TIME_EXCEEDED INTRANS
	  else if (ty,cd) = iCMP_TIME_EXCEEDED_REASS then ICMP_TIME_EXCEEDED REASS
	  else if (ty,cd) = iCMP_PARAMPROB_BADHDR then ICMP_PARAMPROB BADHDR
	  else if (ty,cd) = iCMP_PARAMPROB_NEEDOPT then ICMP_PARAMPROB NEEDOPT
	  else ICMP_NONE in
	let pr = if header.ip_p = (uint 17) then PROTO_UDP else PROTO_TCP in
	(Some dgram.icmp_iph.ip_src, Some dgram.icmp_iph.ip_dst,
	 Some header.ip_src, Some header.ip_dst, Some src, Some dest,
	 None, htype,pr) in
  { icmp_hol_is1 = is1;
    icmp_hol_is2 = is2;
    icmp_hol_is3 = is3;
    icmp_hol_is4 = is4;
    icmp_hol_ps3 = ps3;
    icmp_hol_ps4 = ps4;
    icmp_hol_proto = pr;
    icmp_hol_seq = seq;
    icmp_hol_type = itype;
  }

(* UDP datagram *)
type udp_datagram_hol = {
    udp_hol_is1 : ip option ;
    udp_hol_is2 : ip option ;
    udp_hol_ps1 : port option ;
    udp_hol_ps2 : port option ;
    udp_hol_data : byte list
  }

let hol_udp_of_udp_datagram dgram =
  {
   udp_hol_is1 = ip_option_of_uint dgram.udp_iph.ip_src;
   udp_hol_is2 = ip_option_of_uint dgram.udp_iph.ip_dst;
   udp_hol_ps1 = ip_option_of_uint dgram.udp_h.udp_sport;
   udp_hol_ps2 = ip_option_of_uint dgram.udp_h.udp_dport;
   udp_hol_data = dgram.udp_data;
 }

let data_of_string str =
  let len = String.length str in
  let rec build_list i =
    if i < len then
      (uint (Char.code (String.get str i)))::build_list (i+1)
    else
      []
  in build_list 0

type holmsg =
    TCPMSG of tcp_segment
  | UDPMSG of udp_datagram_hol
  | ICMPMSG of icmp_message_hol;;
