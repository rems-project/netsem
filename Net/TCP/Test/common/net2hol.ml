(* ********************)
(* IP and TCP parsing *)
(* ********************)

open Nettypes;;
open Netconv;;

(* we do purely-functional parsing *)

(* WUPS!!  We should check the checksum too... see RFC1071,1624,1936,1145,1146,1141 *)

let skip_ip_eth_header c =
  let _,c = input_bytes 6 c in  (* eth_dst; TCPv1p23 *)
  let _,c = input_bytes 6 c in  (* eth_src; TCPv1p23 *)
  let eth_type,c = input_uint16 Big c in
  assert_packet_wf "Ethernet type not IP" (eth_type = uint 0x0800);
  c

let skip_loopback_header c iface =
     match iface with LOOPIFACE_BSD ->
                        let _, c = input_bytes 4 c in (* take away first four bytes on BSD: 2 0 0 0 this is the address family for the BPF pseudo header *)
                        c
                    | LOOPIFACE_LINUX ->
                        let _,c = input_bytes 6 c in (* eth_dst; should be 0...0 *)
                        let _,c = input_bytes 6 c in (* eth_src; should be 0...0 *)
                        let _,c = input_bytes 2 c in (* should be 8 0 *)
                        c
                    | LOOPIFACE_WIN ->
                        (* for now we do nothing *)
                        c
                    | OTHERIFACE ->
                        skip_ip_eth_header c;;


let parse_ip_packet c =
  (* names from TCPv2p211 *)
  let (ip_v,ip_hl),c =
    mapfst (bits 0xF0 4 <|> bits 0x0F 0)
      (input_byte c) in
  assert_packet_wf "parse_ip_packet: not IPv4" (ip_v = uint 4);
  let ip_tos,c = input_byte c in
  let ip_len,c = input_uint16_net c in
  let ip_id,c = input_uint16_net c in
  let (ip_zf,(ip_df,(ip_mf,ip_off))),c =
    mapfst (bit 0x8000 <|> (bit 0x4000 <|> (bit 0x2000 <|> bits 0x1FFF 0)))
      (input_uint16_net c) in
  let ip_ttl,c = input_byte c in
  let ip_p,c = input_byte c in
  let ip_sum,c = input_uint16_net c in
  let ip_src,c = input_uint32_net c in
  let ip_dst,c = input_uint32_net c in
  (* and now the options *)
  (* RFC 1122 states that every IP option other than end of options
     and no op specifies its own length *)
  let rec loop os nb c =
    assert_packet_wf "Bad IP option length" (nb >= 0);
    if nb = 0 then
      os,c
    else
      let opt,c = input_byte c in
      let (ip_opt_copied,(ip_opt_class,ip_opt_num)) =
          (bit 0x80 <|> (bits 0x60 5 <|> bits 0x1F 0)) opt in
      if ip_opt_num = uint 0 then
        let bytes,c = input_bytes (nb - 1) c in
        (List.rev (bytes :: [opt] :: os)),c
      else if ip_opt_num = uint 1 then
        loop ([opt] :: os) (nb - 1) c
      else
        let opt_len,c = input_byte c in
        let bytes,c = input_bytes (int opt_len - 2) c in
        loop ((opt :: opt_len :: bytes)::os)  (nb - int opt_len) c in
  let ip_opts,c = loop [] (int ip_hl * 4 - 20) c in
  let ip_data,c  = splitat ((Int64.to_int ip_len) - ((Int64.to_int ip_hl) * 4)) c in
  { ip_h =
    {
     ip_v    = ip_v    ;
     ip_hl   = ip_hl   ;
     ip_tos  = ip_tos  ;
     ip_len  = ip_len  ;
     ip_id   = ip_id   ;
     ip_zf   = ip_zf   ;
     ip_df   = ip_df   ;
     ip_mf   = ip_mf   ;
     ip_off  = ip_off  ;
     ip_ttl  = ip_ttl  ;
     ip_p    = ip_p    ;
     ip_sum  = ip_sum  ;
     ip_src  = ip_src  ;
     ip_dst  = ip_dst  ;
     ip_opts = ip_opts ;
   };
    ip_data = ip_data ;}


(* let check_ip_packet_wf ip = ... check the length matches, the protocol is IPv4, ... *)

(* should be the case that this always holds for the results of parse_ip_packet *)



(* now let's get the TCP header *)

let parse_tcp_datagram ip =
  let c = ip.ip_data in
  let tcp_sport,c = input_uint16_net c in
  let tcp_dport,c = input_uint16_net c in
  let tcp_seq,c = input_uint32_net c in
  let tcp_ack,c = input_uint32_net c in
  let (tcp_off,(tcp_x2,
      (tcp_URG,(tcp_ACK,(tcp_PSH,
      (tcp_RST,(tcp_SYN,tcp_FIN))))))),c =
    mapfst
      (bits 0xF000 12 <|> (bits 0x0FC0 6 <|>
      (bit 0x0020 <|> (bit 0x0010 <|> (bit 0x0008 <|>
      (bit 0x0004 <|> (bit 0x0002 <|> bit 0x0001)))))))
      (input_uint16_net c) in
  let tcp_win,c = input_uint16_net c in
  let tcp_sum,c = input_uint16_net c in
  let tcp_urp,c = input_uint16_net c in
  (* now the TCP options *)
  let rec loop os nb c =
    assert_packet_wf "Bad TCP option length" (nb >= 0);
    if nb = 0 then
      os,c
    else
      let n,c = input_byte c in
      if n = uint 0 then
        if nb > 1 then
          let bytes,c = input_bytes (nb - 1) c in
          (List.rev ((TCPOPT_tail bytes) :: TCPOPT_EOL :: os)),c
        else
          (List.rev (TCPOPT_EOL :: os)),c
      else if n = uint 1 then
        loop (TCPOPT_NOP :: os) (nb - 1) c
      else let tcp_opt_len,c = input_byte c in
      (* there are lots of other TCP options; see http://www.iana.org/assignments/tcp-parameters *)
      let tcp_opt,c =
        if n = uint 2 then
          (assert_packet_wf "TCPOPT_MAXSEG len" (int tcp_opt_len = 4);
           let v,c = input_uint16_net c in
           TCPOPT_MAXSEG(v),c )
        else if n = uint 3 then
          (assert_packet_wf "TCPOPT_WINDOW len" (int tcp_opt_len = 3);
           let v,c = input_byte c in
           TCPOPT_WINDOW(v),c )
        else if n = uint 8 then
          (assert_packet_wf "TCPOPT_TIMESTAMP len" (int tcp_opt_len = 10);
           let ts_val,c = input_uint32_net c in
           let ts_ecr,c = input_uint32_net c in
           TCPOPT_TIMESTAMP(ts_val,ts_ecr) ,c)
        else
          let bytes,c = input_bytes (int tcp_opt_len - 2) c in
          TCPOPT_unknown(n,bytes),c in
      loop (tcp_opt :: os) (nb - int tcp_opt_len) c in
  let tcp_opts,c = loop [] (int tcp_off * 4 - 20) c in

  (* and finally, the data *)
  let tcp_data,c = input_bytes (int ip.ip_h.ip_len - int ip.ip_h.ip_hl * 4 - int tcp_off * 4) c in
  assert_packet_wf "TCP extra data" (c=[]) ;

  (* now fill in the record *)
  { tcp_iph = ip.ip_h;
    tcp_h =
    {
     tcp_sport = tcp_sport ;
     tcp_dport = tcp_dport ;
     tcp_seq   = tcp_seq   ;
     tcp_ack   = tcp_ack   ;
     tcp_off   = tcp_off   ;
     tcp_x2    = tcp_x2    ;
     tcp_URG   = tcp_URG   ;
     tcp_ACK   = tcp_ACK   ;
     tcp_PSH   = tcp_PSH   ;
     tcp_RST   = tcp_RST   ;
     tcp_SYN   = tcp_SYN   ;
     tcp_FIN   = tcp_FIN   ;
     tcp_win   = tcp_win   ;
     tcp_sum   = tcp_sum   ;
     tcp_urp   = tcp_urp   ;
     tcp_opts  = tcp_opts  ;
   } ;
    tcp_data = tcp_data ;
  }


let parse_icmp_unreachable_contents c =
  (* names from TCPv2p211 *)
  let (ip_v,ip_hl),c =
    mapfst (bits 0xF0 4 <|> bits 0x0F 0)
      (input_byte c) in
  assert_packet_wf "parse_icmp_unreachable_contents: not IPv4" (ip_v = uint 4);
  let ip_tos,c = input_byte c in
  let ip_len,c = input_uint16_net c in
  let ip_id,c = input_uint16_net c in
  let (ip_zf,(ip_df,(ip_mf,ip_off))),c =
    mapfst (bit 0x8000 <|> (bit 0x4000 <|> (bit 0x2000 <|> bits 0x1FFF 0)))
      (input_uint16_net c) in
  let ip_ttl,c = input_byte c in
  let ip_p,c = input_byte c in
  let ip_sum,c = input_uint16_net c in
  let ip_src,c = input_uint32_net c in
  let ip_dst,c = input_uint32_net c in
  (* and now the options *)
  (* RFC 1122 states that every IP option other than end of options
     and no op specifies its own length *)
  let rec loop os nb c =
    assert_packet_wf "Bad IP option length" (nb >= 0);
    if nb = 0 then
      os,c
    else
      let opt,c = input_byte c in
      let (ip_opt_copied,(ip_opt_class,ip_opt_num)) =
          (bit 0x80 <|> (bits 0x60 5 <|> bits 0x1F 0)) opt in
      if ip_opt_num = uint 0 then
        let bytes,c = input_bytes (nb - 1) c in
        (List.rev (bytes :: [opt] :: os)),c
      else if ip_opt_num = uint 1 then
        loop ([opt] :: os) (nb - 1) c
      else
        let opt_len,c = input_byte c in
        let bytes,c = input_bytes (int opt_len - 2) c in
        loop ((opt :: opt_len :: bytes)::os)  (nb - int opt_len) c in
  let ip_opts,c = loop [] (int ip_hl * 4 - 20) c in
  assert_packet_wf "parse_icmp_unreachable_contents: more than 8 bytes IP data" (List.length c >= 8);
  let ip_data,c  = splitat 8 c in (* ICMP unreachable only has at least 8 bytes data *)
  { ip_h =
    {
     ip_v    = ip_v    ;
     ip_hl   = ip_hl   ;
     ip_tos  = ip_tos  ;
     ip_len  = ip_len  ;
     ip_id   = ip_id   ;
     ip_zf   = ip_zf   ;
     ip_df   = ip_df   ;
     ip_mf   = ip_mf   ;
     ip_off  = ip_off  ;
     ip_ttl  = ip_ttl  ;
     ip_p    = ip_p    ;
     ip_sum  = ip_sum  ;
     ip_src  = ip_src  ;
     ip_dst  = ip_dst  ;
     ip_opts = ip_opts ;
   };
    ip_data = ip_data ;}


let parse_icmp_message ip =
  assert_packet_wf "parse_icmp_message: `datagram' fragmented"
    (ip.ip_h.ip_mf = false && ip.ip_h.ip_off = uint 0);
  assert_packet_wf "parse_icmp_message: not ICMP"
    (ip.ip_h.ip_p = uint 1);
  let c = ip.ip_data in
  let itype,c = input_byte c in
  let icode,c = input_byte c in
  let isum,c = input_uint16_net c in
  let idata =
    if(itype ==. icmp_echo_reply) then
      (let ident,c = input_uint16_net c in
      let seqno,c = input_uint16_net c in
      ICMP_ECHO_REQUEST(ident, seqno, c))
    else if(itype ==. icmp_echo_request) then
      (let ident,c = input_uint16_net c in
      let seqno,c = input_uint16_net c in
      ICMP_ECHO_REPLY(ident, seqno, c))
    else if((itype ==. icmp_destination_unreachable) or (itype ==. icmp_time_exceeded) or (itype ==. icmp_source_quench) or (itype ==. icmp_parameter_problem)) then
      if(icode ==. (uint 4) (* NEEDFRAG *)) then
	let _,c = input_bytes 2 c in
	let mtu,c = input_uint16_net c in
	let ippacket = parse_icmp_unreachable_contents c in
	let srcport,c = input_uint16_net ippacket.ip_data in
	let destport,c = input_uint16_net c in
	ICMP_ERROR(itype,icode,Some mtu,ippacket.ip_h,srcport,destport)
      else
      let _,c = input_bytes 4 c in
      let ippacket = parse_icmp_unreachable_contents c in
      let srcport,c = input_uint16_net ippacket.ip_data in
      let destport,c = input_uint16_net c in
      ICMP_ERROR(itype, icode, None,ippacket.ip_h, srcport, destport)
    else
      ICMP_QUERY(c) in
  { icmp_iph = ip.ip_h;
    icmp_msg =
    {
     icmp_type = itype;
     icmp_code = icode;
     icmp_sum = isum;
     icmp_body = idata;
    }
  }

let parse_udp_datagram ip =
  assert_packet_wf "parse_udp_datagram: not UDP" (ip.ip_h.ip_p = ip_proto_udp);
  let c = ip.ip_data in
  let udp_sport, c = input_uint16_net c in
  let udp_dport, c = input_uint16_net c in
  let udp_len, c = input_uint16_net c in
  let udp_sum, c = input_uint16_net c in
  let udp_data, c = input_bytes (int ip.ip_h.ip_len - int ip.ip_h.ip_hl * 4 - 8) c in
  assert_packet_wf "UDP extra data" (c=[]) ;
  { udp_iph = ip.ip_h;
    udp_h =
    {
     udp_sport = udp_sport ;
     udp_dport = udp_dport ;
     udp_len = udp_len ;
     udp_sum = udp_sum ;
   } ;
    udp_data = udp_data;
  };;



(* let check_tcp_body_wf body = ... check the length matches, no duplicate options, ... ? *)
(* should be the case that this always holds for the results of parse_tcp_body *)





