(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Common Code UDP                           *)
(* Matthew Fairbairn - Created 20040119                                   *)
(* $Id: common_udp.ml,v 1.8 2006/06/16 11:45:47 amgb2 Exp $              *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread;;
open Unix;;
open ThreadUnix;;
open Printf;;

(* Our libraries *)
open Nettypes;;
open Netconv;;
open Ocamllib;;
open Tthee;;
open Ttheehelper;;
open Libcalls;;
open Testscommon;;
open Common;;
open Dual;;
open Dualdriven;;

type port_flavour =
    WILDCARD_PORT
  | ICMP_PORT
  | PRIVILEGED_PORT
  | UNAVAILABLE_PORT
  | AVAILABLE_PORT
  | KNOWN_PORT

type ip_flavour =
    BOGUS_IP
  | ICMP_IP
  | REMOTE_IP
  | WILDCARD_IP
  | LOCAL_IP

type sock_flavour_ip =
    SF_IP_UNSPEC
  | SF_IP_SPEC

type sock_flavour_port =
    SF_PORT_UNSPEC
  | SF_PORT_SPEC
  | SF_PORT_ERROR

type sock_flavour = sock_flavour_ip * sock_flavour_port * sock_flavour_ip * sock_flavour_port

let sock_flavours = [
  (SF_IP_SPEC,SF_PORT_ERROR,SF_IP_SPEC,SF_PORT_SPEC);
  (SF_IP_UNSPEC,SF_PORT_UNSPEC,SF_IP_UNSPEC,SF_PORT_UNSPEC);
  (SF_IP_UNSPEC,SF_PORT_SPEC,SF_IP_UNSPEC,SF_PORT_UNSPEC);
  (SF_IP_SPEC,SF_PORT_SPEC,SF_IP_UNSPEC,SF_PORT_UNSPEC);
  (SF_IP_SPEC,SF_PORT_SPEC,SF_IP_SPEC,SF_PORT_UNSPEC);
  (SF_IP_SPEC,SF_PORT_SPEC,SF_IP_SPEC,SF_PORT_SPEC);
  (SF_IP_UNSPEC,SF_PORT_ERROR,SF_IP_UNSPEC,SF_PORT_UNSPEC);
  (SF_IP_SPEC,SF_PORT_ERROR,SF_IP_UNSPEC,SF_PORT_UNSPEC);
  (SF_IP_SPEC,SF_PORT_ERROR,SF_IP_SPEC,SF_PORT_UNSPEC);
]

let sf_UUUU = SF_IP_UNSPEC, SF_PORT_UNSPEC, SF_IP_UNSPEC, SF_PORT_UNSPEC

let sf_UPUU = SF_IP_UNSPEC, SF_PORT_SPEC, SF_IP_UNSPEC, SF_PORT_UNSPEC

let sf_IPUU = SF_IP_SPEC, SF_PORT_SPEC, SF_IP_UNSPEC, SF_PORT_UNSPEC

let sf_IPIU = SF_IP_SPEC, SF_PORT_SPEC, SF_IP_SPEC, SF_PORT_UNSPEC

let sf_IPIP = SF_IP_SPEC, SF_PORT_SPEC, SF_IP_SPEC, SF_PORT_SPEC

let sf_UEUU = SF_IP_UNSPEC, SF_PORT_ERROR, SF_IP_UNSPEC, SF_PORT_UNSPEC

let sf_IEUU = SF_IP_SPEC, SF_PORT_ERROR, SF_IP_UNSPEC, SF_PORT_UNSPEC

let sf_IEIU = SF_IP_SPEC, SF_PORT_ERROR, SF_IP_SPEC, SF_PORT_UNSPEC

let sf_IEIP = SF_IP_SPEC, SF_PORT_ERROR, SF_IP_SPEC, SF_PORT_SPEC

let all_sock_flavours = sock_flavours

let all_address_flavours = [BOGUS_IP; REMOTE_IP; WILDCARD_IP; LOCAL_IP]

let all_port_flavours = [WILDCARD_PORT; PRIVILEGED_PORT; UNAVAILABLE_PORT; AVAILABLE_PORT; KNOWN_PORT]

let get_ip_udp ip id ts =
  match ip with
    BOGUS_IP -> Some(Ocamllib.ip_of_string (string_ip (200,200,200,10)))
  | ICMP_IP -> Some(Ocamllib.ip_of_string (string_ip john_priv_ip))
  | REMOTE_IP -> Some(Ocamllib.ip_of_string (string_ip id.aux_host.test_ip_address))
  | WILDCARD_IP -> None
  | LOCAL_IP -> Some(Ocamllib.ip_of_string (string_ip id.test_host.test_ip_address));;

let get_port_udp port id ts =
  match port with
    WILDCARD_PORT -> None
  | ICMP_PORT -> Some(Ocamllib.port_of_int 60000)
  | PRIVILEGED_PORT -> Some(Ocamllib.port_of_int id.test_host.test_priv_port)
  | UNAVAILABLE_PORT -> Some(Ocamllib.port_of_int id.test_host.test_ephm_port)
  | AVAILABLE_PORT -> Some(Ocamllib.port_of_int id.test_host.test_listening_port_base)
  | KNOWN_PORT -> Some(Ocamllib.port_of_int id.test_host.test_ephm_port);;

let get_port_udp_inject p =
  match p with
    None -> None
  | Some(p') -> Some(uint (Ocamllib.int_of_port p'))

(* String representation of a sock flavour port *)
let string_of_udp_port port =
  match port with
    SF_PORT_UNSPEC -> "WILDCARD_PORT"
  | SF_PORT_SPEC ->  "KNOWN_PORT"
  | SF_PORT_ERROR -> "KNOWN_PORT_ERR"

(* string representation of a sock flavour ip *)
let string_of_udp_ip ip local =
  match ip,local with
    SF_IP_UNSPEC,local -> "WILDCARD_IP"
  | SF_IP_SPEC,true -> "LOCAL_IP"
  | SF_IP_SPEC,false -> "REMOTE_IP"

(* string represtenation of a binding quad *)
let string_of_bound_udp_quad (i1,p1,i2,p2) =
  (string_of_udp_ip i1 true) ^ "," ^ (string_of_udp_port p1) ^ "," ^ (string_of_udp_ip i2 false) ^ "," ^ (string_of_udp_port p2)

(* string representation of a port flavour *)
let string_of_port_flavour port =
  match port with
    WILDCARD_PORT -> "WILDCARD_PORT"
  | ICMP_PORT -> "ICMP_PORT"
  | PRIVILEGED_PORT -> "PRIVILEGED_PORT"
  | UNAVAILABLE_PORT -> "UNAVAILABLE_PORT"
  | AVAILABLE_PORT -> "AVAILABLE_PORT"
  | KNOWN_PORT -> "KNOWN_PORT"

(* string representation of an ip address flavour *)
let string_of_ip_flavour ip =
  match ip with
    BOGUS_IP -> "BOGUS_IP"
  | ICMP_IP -> "ICMP_IP"
  | REMOTE_IP -> "REMOTE_IP"
  | WILDCARD_IP -> "WILDCARD_IP"
  | LOCAL_IP -> "LOCAL_IP"

let all_sf_af_pf f sf af pf =
  let fsf = List.map f sf in
  let rec iter xs ys =
    match xs with
      [] -> []
    | (x::xs) -> (List.map x ys) @ (iter xs ys) in
  let fsf' = iter fsf af in
  iter fsf' pf


let get_real_port id ts sf =
  let _,p,_,_ = sf in
  match p with
    SF_PORT_UNSPEC -> None
  | SF_PORT_SPEC -> Some(uint id.test_host.test_ephm_port)
  | SF_PORT_ERROR -> Some(uint id.test_host.test_ephm_port)

let get_foreign_ip id ts sf =
  let _,_,i,_ = sf in
  match i with
    SF_IP_UNSPEC -> Some(hol_ip id.aux_host.test_ip_address) (* None *)
  | SF_IP_SPEC -> Some(hol_ip id.aux_host.test_ip_address)

let get_foreign_port id ts sf =
  let _,_,_,p = sf in
  match p with
    SF_PORT_UNSPEC -> Some(hol_ip id.aux_host.test_ip_address) (* None *)
  | SF_PORT_SPEC -> Some(uint id.aux_host.test_ephm_port)
  | SF_PORT_ERROR -> Some(uint id.aux_host.test_ephm_port)
