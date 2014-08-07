open Nettypes;;
open Pcapfile;;

(* Base types*)
type pcap_handle
type pcap_bpf_program

type pcap_net = ip
type pcap_netmask = uint

(* Error handling *)
exception Pcap_error of string * string

let _ = Callback.register_exception "Pcapinterface.Pcap_error"
                                    (Pcap_error("", ""))


(* Useful conversions *)
let net_of_ip (n : ip) = (n : pcap_net)
let ip_of_net (n : pcap_net) = (n : ip)

let netmask_of_uint (n : uint) = (n : pcap_netmask)
let uint_of_netmask (n : pcap_netmask) = (n : uint)


(* libpcap functions *)

external pcap_lookupdev: unit -> string = "ns_pcap_lookupdev"
(* Returns the name of a device (e.g. eth0) suitable for *)
(* use with libpcap. Raises pcap_error on an error *)

external pcap_lookupnet: string -> (pcap_net * pcap_netmask) = "ns_pcap_lookupnet"
(* Returns the ip address and network mask associated with the *)
(* device specified (e.g. eth0). Raises pcap_error on an error *)

external pcap_open_live: string -> int -> bool -> int -> pcap_handle = "ns_pcap_open_live"
(* Returns a new pcap_handle for a given device. *)
(* pcap_open_live devname snaplength promiscuous readouttime *)
(* Raises pcap_error on an error *)

external pcap_compile: pcap_handle -> string -> bool -> pcap_netmask -> pcap_bpf_program = "ns_pcap_compile"
(* Returns a compiled pcap filter for the given pcap_handle and filter string *)
(* pcap_compile pcap_handle filterstr optimise netmask *)
(* Does NOT raise any errors *)

external pcap_setfilter: pcap_handle -> pcap_bpf_program -> unit = "ns_pcap_setfilter"
(* Sets the current pcap filter to be the provided compiled pcap filter *)
(* pcap_setfilter pcap_handle compiledfilter *)
(* Raises pcap_error on an error *)

external pcap_next: pcap_handle -> (pcap_pkthdr * char list) = "ns_pcap_next"
(* Gets the next packet for the given pcap_handle *)
(* Raises pcap_error on an error *)

external pcap_close: pcap_handle -> unit = "ns_pcap_close"
(* Closes the pcap_handle and frees all resources *)





