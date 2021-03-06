(* *********************************)
(* types for dealing with lib_pcap *)
(* *********************************)

open Nettypes;;
open Netconv;;
open Net2hol;;
open Netipreass;;
open Holtypes;;

(* see tcpdump sources: pcap.h, pcap-int.h, savefile.c *)

(* uses the file format generated by lib_pcap's pcap_dump.
   See:

    http://cvs.tcpdump.org/cgi-bin/cvsweb/libpcap/pcap-int.h
    and ditto savefile.c

   The structure is called pcap_pkthdr or pcap_patched_pkthdr, and the
   magic number is 0xa1b2c3d4 or 0xa1b2cd34.  We must also recognised
   a byte-reordered magic number, and do that reordering on the dump
   headers (but the packet is always in network order).

*)

type pcap_file_header = {
    magic         : uint;        (* uint32: magic number *)
    endian        : endianness;  (* --      endianness *)
    version_major : uint;        (* uint16: major version number *)
    version_minor : uint;        (* uint16: minor version number *)
    thiszone      : sint;        (*  int32: GMT to local correction *)
    sigfigs       : uint;        (* uint32: accuracy of timestamps *)
    snaplen       : uint;        (* uint32: max length of saved portion of each packet *)
    linktype      : uint;        (* uint32: data link type LINKTYPE_* *)
}

type pcap_pkthdr = {
    tstamp    : timestamp;
    caplen    : uint;
    len       : uint;
  }

let pcap_magic = (uint 0xa1b2 << 16) |. uint 0xc3d4
let patched_pcap_magic = (uint 0xa1b2 << 16) |. uint 0xcd34

let parse_pcap_file_header c0 =
  let magic,c = input_uint32 Little c0 in
  let magic,endian,c =
    if magic = pcap_magic || magic = patched_pcap_magic then
      magic,Little,c
    else
      let magic,c = input_uint32 Big c0 in
      if magic = pcap_magic || magic = patched_pcap_magic then
        magic,Big,c
      else
        (assert_packet_wf "Bad PCAP magic number" false;
         magic,Little,c) in
  let version_major,c = input_uint16 endian c in
  let version_minor,c = input_uint16 endian c in
  let thiszone,c = input_sint32 endian c in
  let sigfigs,c = input_uint32 endian c in
  let snaplen,c = input_uint32 endian c in
  let linktype,c = input_uint32 endian c in
  { magic         = magic         ;
    endian        = endian        ;
    version_major = version_major ;
    version_minor = version_minor ;
    thiszone      = thiszone      ;
    sigfigs       = sigfigs       ;
    snaplen       = snaplen       ;
    linktype      = linktype      ;
  },c

(* pull a PCAP packet off the stream; don't parse the packet *)
let parse_pcapfile_packet fh c =
  let ts_sec,c = input_uint32 fh.endian c in
  let ts_usec,c = input_uint32 fh.endian c in
  let caplen,c = input_uint32 fh.endian c in
  let len,c = input_uint32 fh.endian c in
  assert_packet_wf "Packet truncated by PCAP" (len = caplen);
  let extra,c =
    if fh.magic = patched_pcap_magic then
      let index,c = input_sint32 fh.endian c in
      let protocol,c = input_uint16 fh.endian c in
      let pkt_type,c = input_byte c in
      let _,c = input_byte c in (* garbage for alignment purposes *)
      Some (index,protocol,pkt_type),c
    else
      None,c in
  let cap,c = splitat (int caplen) c in
  ({t_sec = ts_sec; t_usec = ts_usec;}, extra, cap),c

(* pull an IP PCAP packet off the stream and parse it *)
let parse_pcapfile_ip_packet fh c =
  let (ts,_,cap),c = parse_pcapfile_packet fh c in
  let cap = skip_ip_eth_header cap in
  let ip = parse_ip_packet cap in
  (ts,ip),c

















