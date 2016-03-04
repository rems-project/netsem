open Nettypes;;
open Netconv;;
open Net2hol;;
open Netipreass;;
open Holtypes;;

type pcap_file_header = {
    magic         : uint;        (* uint32: magic number *)
    endian        : endianness;  (* --      endianness *)
    version_major : uint;        (* uint16: major version number *)
    version_minor : uint;        (* uint16: minor version number *)
    thiszone      : sint;        (*  int32: GMT to local correction *)
    sigfigs       : uint;        (* uint32: accuracy of timestamps *)
    snaplen       : uint; (* uint32: max length of saved portion of each packet *)
    linktype      : uint;        (* uint32: data link type LINKTYPE_* *)
}

type pcap_pkthdr = {
    tstamp     : timestamp;
    caplen    : uint;
    len       : uint;
  }

val parse_pcap_file_header: char list -> pcap_file_header * char list

val parse_pcapfile_ip_packet: pcap_file_header -> char list -> (timestamp * ip_packet) * char list















