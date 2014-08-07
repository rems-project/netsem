open Nettypes;;
open Netconv;;

val skip_ip_eth_header: char list -> char list

val skip_loopback_header: char list -> iface -> char list

val parse_ip_packet: char list -> ip_packet

val parse_tcp_datagram: ip_packet -> tcp_datagram

val parse_icmp_message: ip_packet -> icmp_datagram

val parse_udp_datagram: ip_packet -> udp_datagram
