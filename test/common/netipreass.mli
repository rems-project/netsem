open Nettypes;;
open Netconv;;

type fragment = {
    f_p   : ip_packet;
    f_ts  : timestamp;
  }

(* unique datagram identifier *)
type ip_uniq = {
    ipu_id  : uint;
    ipu_src : uint;
    ipu_dst : uint;
    ipu_p   : uint;
  }

type defrag_chain = {
    dfc_uniq : ip_uniq;        (* unique identifier of all fragments in chain *)
    dfc_ts   : timestamp;      (* invariant: earliest timestamp in dfc_data *)
    dfc_data : fragment list;  (* invariant: in reverse order of arrival; nonempty *)
  }

type reass_frag = {
    rf_off  : int;
    rf_dlen : int;
    rf_mf   : bool;
    rf_data : char list;
  }

type defrag_state = defrag_chain list  (* set of defrag chains *)

val ip_input: defrag_state -> timestamp -> ip_packet -> defrag_state * ip_packet option

(* FIXME tjr surely this should be defrag_chain list? *)
val init_ip_input_state: 'a list




