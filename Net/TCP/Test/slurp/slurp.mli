(* slurp.mli - slurps in a lib_pcap (tcpdump) dump file / stream *)
(* 2002-07-29.. *)
(* Time-stamp: <2002-07-29 17:07:05 kw217@astrocyte.cl.cam.ac.uk> *)
open Nettypes;;
open Netconv;;




(* read in the file header off the input channel *)
(*val slurp_header : in_channel -> pcap_file_header*)

(* read the next segment off the input channel *)
(*val slurp : pcap_file_header -> in_channel -> (timestamp * tcp_segment)*)

(* build an IP packet from a tcp_segment datum *)
(*val build : tcp_segment -> string*)


