open Nettypes;;
open Netconv;;
open Net2hol;;
open Netipreass;;
open Pcapfile;;
open Holtypes;;
open Printf

let bstr b = if b then "true" else "false"

let rflag st sf b = if b then st else sf

let render_ip_header iph =
  printf "  Version:           %6d\n"      (int iph.ip_v);
  printf "  Header length:     %6d\n"      (int iph.ip_hl);
  printf "  TOS:                 0x%02x\n" (int iph.ip_tos);
  printf "  Total length:      %6d\n"      (int iph.ip_len);
  printf "  ID:                0x%04x\n"   (int iph.ip_id);
  printf "  Flags:           %s %s %s\n" (rflag "ZF" "--" iph.ip_zf)
                                         (rflag "DF" "--" iph.ip_df)
                                         (rflag "MF" "--" iph.ip_mf);
  printf "  Offset:            %6d\n"      (int iph.ip_off);
  printf "  Time to live:      %6d\n"      (int iph.ip_ttl);
  printf "  Protocol:          %6d\n"      (int iph.ip_p);
  printf "  Checksum:          0x%04x\n"   (int iph.ip_sum);
  printf "  Source IP:     0x%08x\n"       (int iph.ip_src);
  printf "  Dest IP:       0x%08x\n"       (int iph.ip_dst);
  printf "  Options:       [";
  let rec go opts =
    let rec go2 xs = match xs with
      (x::y::xs) ->
        printf "%02x " (int x);
        go2 (y::xs)
    | [x] ->
        printf "%02x" (int x)
    | [] ->
        () in
    match opts with
      (opt::opt'::opts) ->
        go2 opt;
        printf ", ";
        go (opt'::opts)
    | [opt] ->
        go2 opt
    | [] ->
        () in
  go iph.ip_opts;
  printf "]\n"

let render_nlist ns =
  printf "[";
  let rec loop ns = match ns with
    (n::n'::ns) -> printf "%d," n; loop (n'::ns)
  | [n] -> printf "%d]" n
  | [] -> printf "]" in
  loop ns

let render_tcp_header tcph =
  printf "  Source port:       %6d\n"      (int tcph.tcp_sport);
  printf "  Dest port:         %6d\n"      (int tcph.tcp_dport);
  printf "  Seq number:    %10u\n"         (int tcph.tcp_seq);
  printf "  Ack number:    %10u\n"         (int tcph.tcp_ack);
  printf "  Offset (hdrlen):   %6d\n"      (int tcph.tcp_off);
  printf "  Reserved:           0x%03x\n"  (int (tcph.tcp_x2 << 6));
  printf "  Flags:        %s %s %s\n" (rflag "URG" "---" tcph.tcp_URG)
                                      (rflag "ACK" "---" tcph.tcp_ACK)
                                      (rflag "PSH" "---" tcph.tcp_PSH);
  printf "                %s %s %s\n" (rflag "RST" "---" tcph.tcp_RST)
                                      (rflag "SYN" "---" tcph.tcp_SYN)
                                      (rflag "FIN" "---" tcph.tcp_FIN);
  printf "  Window size:       %6d\n"      (int tcph.tcp_win);
  printf "  Checksum:          0x%04x\n"   (int tcph.tcp_sum);
  printf "  Urgent pointer:    %6d\n"      (int tcph.tcp_urp);
  printf "  Options:           [";
  let go opt = match opt with
    TCPOPT_EOL -> printf "EOL"
  | TCPOPT_NOP -> printf "NOP"
  | TCPOPT_MAXSEG(n) -> printf "MSS=%d" (int n)
  | TCPOPT_WINDOW(n) -> printf "WS=%d" (int n)
  | TCPOPT_TIMESTAMP(m,n) -> printf "TS=(%u,%u)" (int m) (int n)
  | TCPOPT_unknown(n,ns) ->
      printf "?%d=" (int n);
      render_nlist (List.map int ns);
  | TCPOPT_tail(ns) ->
      printf "tail=";
      render_nlist (List.map int ns) in
  let rec loop opts = match opts with
    (opt::opt'::opts) ->
      go opt;
      printf ",\n                      ";
      loop (opt'::opts)
  | [opt] ->
      go opt;
      printf "]\n";
  | [] ->
      printf "]\n" in
  loop tcph.tcp_opts

let render_ip_packet ip =
  printf "IP header:\n";
  render_ip_header ip.ip_h;
  printf "IP data:\n";
  printf "  (%d bytes)" (List.length ip.ip_data)

let render_tcp_datagram tcp =
  printf "IP header:\n";
  render_ip_header tcp.tcp_iph;
  printf "TCP header:\n";
  render_tcp_header tcp.tcp_h;
  printf "TCP data:\n";
  printf "  (%d bytes)" (List.length tcp.tcp_data)
