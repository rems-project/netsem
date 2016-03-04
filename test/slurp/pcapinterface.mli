open Nettypes;;
open Pcapfile;;

(* Base types *)
type pcap_handle
type pcap_bpf_program

type pcap_net = ip
type pcap_netmask = uint

(* Error handling *)
exception Pcap_error of string * string

(* Useful conversions *)
val net_of_ip: ip -> pcap_net
val ip_of_net: pcap_net -> ip

val netmask_of_uint: uint -> pcap_netmask
val uint_of_netmask: pcap_netmask -> uint

(* libpcap functions *)

val pcap_lookupdev: unit -> string
(* Returns the name of a device (e.g. eth0) suitable for *)
(* use with libpcap. Raises pcap_error on an error *)

val pcap_lookupnet: string -> (pcap_net * pcap_netmask)
(* Returns the ip address and network mask associated with the *)
(* device specified (e.g. eth0). Raises pcap_error on an error *)

val pcap_open_live: string -> int -> bool -> int -> pcap_handle
(* Returns a new pcap_handle for a given device. *)
(* pcap_open_live devname snaplength promiscuous readouttime *)
(* Raises pcap_error on an error *)

val pcap_compile: pcap_handle -> string -> bool -> pcap_netmask -> pcap_bpf_program

val pcap_setfilter: pcap_handle -> pcap_bpf_program -> unit

val pcap_next: pcap_handle -> (pcap_pkthdr * char list)

val pcap_close: pcap_handle -> unit
