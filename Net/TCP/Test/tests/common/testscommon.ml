open Tthee;;
open Nettypes;;
open Netconv;;
open Printf;;

(* Program paths *)
let unix_execpaths = {
  libd_path = "/home/Net/TCP/Test/libd/libd";
  slurp_path = "/home/Net/TCP/Test/slurp/slurp";
  injector_path = "/home/Net/TCP/Test/injector/injector";
  holtcpcb_path = "/home/Net/TCP/Test/utils/holtcpcb-v8/holtcpcb-v8";
  mirror_path = "/home/Net/TCP/Test/mirror/mirror";
} ;;

(* I can't imagine that this is used for anything, given that the reference
   to Steve's filespace hasn't caused problems yet --amgb2 *)
let local_execpaths = {
  libd_path = "/homes/smb50/Net/TCP/Test/libd/libd";
  slurp_path = "/homes/smb50/Net/TCP/Test/slurp/slurp";
  injector_path = "/homes/smb50/Net/TCP/Test/injector/injector";
  holtcpcb_path = "/homes/smb50/Net/TCP/Test/utils/holtcpcb-v8/holtcpcb-v8";
  mirror_path = "/homes/smb50/Net/TCP/Test/utils/mirror/mirror"
} ;;

let no_execpaths = {
  libd_path = "NOT REQUIRED";
  slurp_path = "NOT REQUIRED";
  injector_path = "NOT REQUIRED";
  holtcpcb_path = "NOT REQUIRED";
  mirror_path = "NOT REQUIRED"
} ;;

let john_execpaths = unix_execpaths ;;
let emil_execpaths = unix_execpaths ;;
let alan_execpaths = unix_execpaths ;;
let kurt_execpaths = unix_execpaths ;;
let glia_execpaths = no_execpaths ;;

let alf_execpaths = unix_execpaths ;;
let ken_execpaths = unix_execpaths ;;
let jan_execpaths = unix_execpaths ;;
let ada_execpaths = unix_execpaths ;;
let dag_execpaths = unix_execpaths ;;
let tom_execpaths = unix_execpaths ;;

(* ------------------------------------------------------------ *)

(* Initial host choices *)
type initial_host =
    INITIAL_HOST_JOHN
  | INITIAL_HOST_EMIL
  | INITIAL_HOST_KURT
  | INITIAL_HOST_ALAN
  | INITIAL_HOST_GLIA
  | INITIAL_HOST_THALAMUS
(*  | INITIAL_HOST_FORNIX *)
  | INITIAL_HOST_ALF
  | INITIAL_HOST_KEN
  | INITIAL_HOST_JAN
  | INITIAL_HOST_ADA
  | INITIAL_HOST_DAG
  | INITIAL_HOST_TOM
;;

let tthee_ip_to_string ip =
  match ip with
    (a,b,c,d) ->
      (string_of_int a) ^ " " ^ (string_of_int b) ^ " " ^
      (string_of_int c) ^ " " ^ (string_of_int d);;

let tthee_ip_to_string_dots ip =
  match ip with
    (a,b,c,d) ->
      (string_of_int a) ^ "." ^ (string_of_int b) ^ "." ^
      (string_of_int c) ^ "." ^ (string_of_int d);;

(* ------------------------------------------------------------ *)

(* Private IP addresses *)
(* netsem *)
let astrocyte_priv_ip = (192,168,0,1)
let thalamus_priv_ip = (192,168,0,2)
let glia_priv_ip = (192,168,0,3)
let kurt_priv_ip = (192,168,0,11)
let john_priv_ip = (192,168,0,12)
let emil_priv_ip = (192,168,1,13)
let alan_priv_ip = (192,168,0,14)
let alan_priv_ip2 = (192,168,1,14)
let psyche_priv_ip = (192,168,0,99)
let thalamus_real_ip = (128,232,8,182)

(* netsem2 *)
let alf_priv_ip = (192,168,13,101)
let ken_priv_ip = (192,168,13,102)
let jan_priv_ip = (192,168,13,103)
let ada_priv_ip = (192,168,13,104)
let dag_priv_ip = (192,168,13,105)
let tom_priv_ip = (192,168,13,106)
let fornix_priv_ip = (192,168,13,200)
let zonule_priv_ip = (192,168,13,201)

let unused_ip = (192,168,13,88) (* note these are particular to the network netsem or netsem2 *)
let broadcast_ip = (192,168,13,255)
let multicast_ip = (224,1,2,3)
let subnet_mask = (255,255,255,0)

(* Interface and routing table configurations *)
let john_ifaces =
  let eth0 = "(ETH 0, <| ipset := {IP 192 168 0 12}; primary := IP 192 168 0 12; netmask := NETMASK 24; up := T |>)" in
  let lo = "(LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 8; up := T |>)" in
  "[" ^ eth0 ^"; " ^ lo ^ "]"

let john_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 8; ifid := LO |>" in
  let route_2 = "<| destination_ip := IP 192 168 0 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  let route_3 = "<| destination_ip := IP 192 168 1 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  "[" ^ route_1 ^ ";" ^ route_2 ^ "; " ^ route_3 ^ "]"

let kurt_ifaces =
  let eth0 = "(ETH 0, <| ipset := {IP 192 168 0 11}; primary := IP 192 168 0 11; netmask := NETMASK 24; up := T |>)" in
  let lo = "(LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 8; up := T |>)" in
  "[" ^ eth0 ^"; " ^ lo ^ "]"

let kurt_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 8; ifid := LO |>" in
  let route_2 = "<| destination_ip := IP 192 168 0 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  let route_3 = "<| destination_ip := IP 192 168 1 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  "[" ^ route_1 ^ "; " ^ route_2 ^ "; " ^ route_3 ^ "]"

let emil_ifaces =
  let eth0 = "(ETH 0, <| ipset := {IP 192 168 1 13}; primary := IP 192 168 1 13; netmask := NETMASK 24; up := T |>)" in
  let lo = "(LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 8; up := T |>)" in
  "[" ^ eth0 ^"; " ^ lo ^ "]"

let emil_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 8; ifid := LO |>" in
  let route_2 = "<| destination_ip := IP 192 168 0 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  let route_3 = "<| destination_ip := IP 192 168 1 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  "[" ^ route_1 ^ "; " ^ route_2 ^ "; " ^ route_3 ^ "]"

let alan_ifaces =
  let eth0 = "(ETH 0, <| ipset := {IP 192 168 0 14}; primary := IP 192 168 0 14; netmask := NETMASK 24; up := T |>)" in
  let eth1 = "(ETH 1, <| ipset := {IP 192 168 1 14}; primary := IP 192 168 1 14; netmask := NETMASK 24; up := T |>)" in
  let lo = "(LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 8; up := T |>)" in
  "[" ^ eth0 ^"; " ^ eth1 ^ "; " ^ lo ^ "]"

let alan_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 8; ifid := LO |>" in
  let route_2 = "<| destination_ip := IP 192 168 0 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  let route_3 = "<| destination_ip := IP 192 168 1 0; destination_netmask := NETMASK 24; ifid := ETH 1 |>" in
  "[" ^ route_1 ^ "; " ^ route_2 ^ "; " ^ route_3 ^ "]"

let glia_ifaces =
  let eth0 = "(ETH 0, <| ipset := {IP 192 168 0 3}; primary := IP 192 168 0 3; netmask := NETMASK 24; up := T |>)" in
  let eth1 = "(ETH 1, <| ipset := {IP 128 232 13 142}; primary := IP 128 232 13 142;  netmask := NETMASK 20; up := T |>)" in
  let lo = "(LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 8; up := T |>)" in
  "[" ^ eth0 ^"; " ^ lo ^ "]"

let glia_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 8; ifid := LO |>" in
  let route_2 = "<| destination_ip := IP 192 168 0 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  let route_3 = "<| destination_ip := IP 192 168 1 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  let route_4 = "<| destination_ip := IP 128 232 13 142; destination_netmask := NETMASK 20; ifid := ETH 1 |>" in
  "[" ^ route_1 ^ "; " ^ route_2 ^ "; " ^ route_3 ^ "; " ^ route_4 ^ "]"

(* FIXME netsem2 info copied mindlessly from previous entries- these previous entries don't seem directly related to the actual routing info *)

let alf_ifaces =
  let xl0 = "(XL 0, <| ipset := {IP 192 168 13 101}; primary := IP 192 168 13 101; netmask := NETMASK 8; up := T |>)" in
  let lo0 = "(LO 0, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 24; up := T |>)" in
  "[" ^ xl0 ^"; " ^ lo0 ^ "]"

let alf_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 24; ifid := LO 0 |>" in
  let route_2 = "<| destination_ip := IP 192 168 13 0; destination_netmask := NETMASK 24; ifid := XL 0 |>" in
  "[" ^ route_1 ^ "; " ^ route_2 ^ "]"

let ken_ifaces =
  let xl0 = "(ETH 0, <| ipset := {IP 192 168 13 102}; primary := IP 192 168 13 102; netmask := NETMASK 8; up := T |>)" in
  let lo0 = "(LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 24; up := T |>)" in
  "[" ^ xl0 ^"; " ^ lo0 ^ "]"

let ken_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 24; ifid := LO |>" in
  let route_2 = "<| destination_ip := IP 192 168 13 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  "[" ^ route_1 ^ "; " ^ route_2 ^ "]"

let jan_ifaces =
  let eth0 = "(ETH 0, <| ipset := {IP 192 168 13 103}; primary := IP 192 168 13 103; netmask := NETMASK 8; up := T |>)" in
  let lo = "(LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 24; up := T |>)" in
  "[" ^ eth0 ^"; " ^ lo ^ "]"

let jan_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 24; ifid := LO |>" in
  let route_2 = "<| destination_ip := IP 192 168 13 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  "[" ^ route_1 ^ "; " ^ route_2 ^ "]"

let ada_ifaces =
  let eth0 = "(ETH 0, <| ipset := {IP 192 168 13 104}; primary := IP 192 168 13 104; netmask := NETMASK 8; up := T |>)" in
  let lo = "(LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 24; up := T |>)" in
  "[" ^ eth0 ^"; " ^ lo ^ "]"

let ada_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 24; ifid := LO |>" in
  let route_2 = "<| destination_ip := IP 192 168 13 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  "[" ^ route_1 ^ "; " ^ route_2 ^ "]"

let dag_ifaces =
  let xl0 = "(ETH 0, <| ipset := {IP 192 168 13 105}; primary := IP 192 168 13 105; netmask := NETMASK 8; up := T |>)" in
  let lo0 = "(LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 24; up := T |>)" in
  "[" ^ xl0 ^"; " ^ lo0 ^ "]"

let dag_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 24; ifid := LO |>" in
  let route_2 = "<| destination_ip := IP 192 168 13 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  "[" ^ route_1 ^ "; " ^ route_2 ^ "]"

let tom_ifaces =
  let eth0 = "(ETH 0, <| ipset := {IP 192 168 13 106}; primary := IP 192 168 13 106; netmask := NETMASK 8; up := T |>)" in
  let lo = "(LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 24; up := T |>)" in
  "[" ^ eth0 ^"; " ^ lo ^ "]"

let tom_rttab =
  let route_1 = "<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 24; ifid := LO |>" in
  let route_2 = "<| destination_ip := IP 192 168 13 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>" in
  "[" ^ route_1 ^ "; " ^ route_2 ^ "]"


let get_ifaces host =
   match host with
    INITIAL_HOST_JOHN -> john_ifaces
  | INITIAL_HOST_EMIL -> emil_ifaces
  | INITIAL_HOST_KURT -> kurt_ifaces
  | INITIAL_HOST_ALAN -> alan_ifaces
  | INITIAL_HOST_GLIA -> glia_ifaces
  | INITIAL_HOST_THALAMUS -> "[]"
  | INITIAL_HOST_ALF  -> alf_ifaces
  | INITIAL_HOST_KEN  -> ken_ifaces
  | INITIAL_HOST_JAN  -> jan_ifaces
  | INITIAL_HOST_ADA  -> ada_ifaces
  | INITIAL_HOST_DAG  -> dag_ifaces
  | INITIAL_HOST_TOM  -> tom_ifaces

let get_rttab host =
   match host with
    INITIAL_HOST_JOHN -> john_rttab
  | INITIAL_HOST_EMIL -> emil_rttab
  | INITIAL_HOST_KURT -> kurt_rttab
  | INITIAL_HOST_ALAN -> alan_rttab
  | INITIAL_HOST_GLIA -> glia_rttab
  | INITIAL_HOST_THALAMUS -> "[]"
  | INITIAL_HOST_ALF  -> alf_rttab
  | INITIAL_HOST_KEN  -> ken_rttab
  | INITIAL_HOST_JAN  -> jan_rttab
  | INITIAL_HOST_ADA  -> ada_rttab
  | INITIAL_HOST_DAG  -> dag_rttab
  | INITIAL_HOST_TOM  -> tom_rttab

(* ------------------------------------------------------------ *)

(* Remote execution parameters *)
let john_remote = REMOTE("john.netsem", SSH("/usr/bin/ssh"), john_execpaths);;
let emil_remote = REMOTE("emil.netsem", SSH("/usr/bin/ssh"), emil_execpaths);;
let kurt_remote = REMOTE("kurt.netsem", SSH("/usr/bin/ssh"), kurt_execpaths);;
let alan_remote = REMOTE("alan.netsem", SSH("/usr/bin/ssh"), alan_execpaths);;
let glia_remote = REMOTE(tthee_ip_to_string_dots glia_priv_ip, CUSTOM_RSH(60000), glia_execpaths);;
let alf_remote = REMOTE("alf.netsem2", SSH("/usr/bin/ssh"), alf_execpaths);;
let ken_remote = REMOTE("ken.netsem2", SSH("/usr/bin/ssh"), ken_execpaths);;
let jan_remote = REMOTE("jan.netsem2", SSH("/usr/bin/ssh"), jan_execpaths);;
let ada_remote = REMOTE("ada.netsem2", SSH("/usr/bin/ssh"), ada_execpaths);;
let dag_remote = REMOTE("dag.netsem2", SSH("/usr/bin/ssh"), dag_execpaths);;
let tom_remote = REMOTE("tom.netsem2", SSH("/usr/bin/ssh"), tom_execpaths);;

(* Local execution parameters *)
let local_ep = LOCAL(local_execpaths);;

type platform_types =
    ARCH_BSD
  | ARCH_LINUX
  | ARCH_WINXP
;;

let print_initial_host_ip host =
  match host with
    INITIAL_HOST_JOHN -> tthee_ip_to_string john_priv_ip
  | INITIAL_HOST_EMIL -> tthee_ip_to_string emil_priv_ip
  | INITIAL_HOST_KURT -> tthee_ip_to_string kurt_priv_ip
  | INITIAL_HOST_ALAN -> tthee_ip_to_string alan_priv_ip
  | INITIAL_HOST_GLIA -> tthee_ip_to_string glia_priv_ip
  | INITIAL_HOST_THALAMUS -> tthee_ip_to_string thalamus_priv_ip
  | INITIAL_HOST_ALF  -> tthee_ip_to_string alf_priv_ip
  | INITIAL_HOST_KEN  -> tthee_ip_to_string ken_priv_ip
  | INITIAL_HOST_JAN  -> tthee_ip_to_string jan_priv_ip
  | INITIAL_HOST_ADA  -> tthee_ip_to_string ada_priv_ip
  | INITIAL_HOST_DAG  -> tthee_ip_to_string dag_priv_ip
  | INITIAL_HOST_TOM  -> tthee_ip_to_string tom_priv_ip
;;

let print_initial_host_name host =
  match host with
    INITIAL_HOST_JOHN -> "john"
  | INITIAL_HOST_EMIL -> "emil"
  | INITIAL_HOST_KURT -> "kurt"
  | INITIAL_HOST_ALAN -> "alan"
  | INITIAL_HOST_GLIA -> "glia"
  | INITIAL_HOST_THALAMUS -> "thalamus"
  | INITIAL_HOST_ALF  -> "alf"
  | INITIAL_HOST_KEN  -> "ken"
  | INITIAL_HOST_JAN  -> "jan"
  | INITIAL_HOST_ADA  -> "ada"
  | INITIAL_HOST_DAG  -> "dag"
  | INITIAL_HOST_TOM  -> "tom"
;;

let get_initial_host_ip host =
  match host with
    INITIAL_HOST_JOHN -> john_priv_ip
  | INITIAL_HOST_EMIL -> emil_priv_ip
  | INITIAL_HOST_KURT -> kurt_priv_ip
  | INITIAL_HOST_ALAN -> alan_priv_ip
  | INITIAL_HOST_GLIA -> glia_priv_ip
  | INITIAL_HOST_THALAMUS -> thalamus_priv_ip
  | INITIAL_HOST_ALF  -> alf_priv_ip
  | INITIAL_HOST_KEN  -> ken_priv_ip
  | INITIAL_HOST_JAN  -> jan_priv_ip
  | INITIAL_HOST_ADA  -> ada_priv_ip
  | INITIAL_HOST_DAG  -> dag_priv_ip
  | INITIAL_HOST_TOM  -> tom_priv_ip
;;

let get_prealloc_fds host =
  match host with
    INITIAL_HOST_JOHN -> "[0;1;2;3;4;5;6;7]"
  | INITIAL_HOST_EMIL -> "[0;1;2;3;4;5;6;7]"
  | INITIAL_HOST_KURT -> "[0;1;2;3;4;5;6;1000]"
  | INITIAL_HOST_ALAN -> "[0;1;2;3;4;5;6;1000]"
  | INITIAL_HOST_GLIA -> "[]"
  | INITIAL_HOST_THALAMUS -> "[0;1;2;3;4;5;6;1000]" (* a guess *)
  | INITIAL_HOST_ALF  -> "[0;1;2;3;4;5]" (* totally made up *)
  | INITIAL_HOST_KEN  -> "[0;1;2;3;4;5]" (* confirmed *)
  | INITIAL_HOST_JAN  -> "[0;1;2;3;4;5;6;1000]" (* confirmed *)
  | INITIAL_HOST_ADA  -> "[0;1;2;3;4;5;6;1000]" (* confirmed *)
  | INITIAL_HOST_DAG  -> "[0;1;2;3;4;5;6;7]" (* not yet confirmed *)
  | INITIAL_HOST_TOM  -> "[0;1;2;3;4;5;6;7]" (* not yet confirmed *)
;;

let print_initial_host_params host =
  let bsd_low_port_range = "<| min_eph_port := 1024; max_eph_port := 4999 |>" in
  let bsd_high_port_range = "<| min_eph_port := 49152; max_eph_port := 65535 |> " in
  let linux_bonus_high_port_range = "<| min_eph_port := 32768; max_eph_port := 61000 |>" in
  match host with
    | INITIAL_HOST_JOHN -> bsd_low_port_range
    | INITIAL_HOST_EMIL -> bsd_low_port_range
    | INITIAL_HOST_KURT -> bsd_low_port_range
    | INITIAL_HOST_ALAN -> bsd_low_port_range
    | INITIAL_HOST_GLIA -> bsd_low_port_range (* unchecked *)
    | INITIAL_HOST_THALAMUS -> linux_bonus_high_port_range
    | INITIAL_HOST_ALF -> bsd_high_port_range (* unchecked *)
    | INITIAL_HOST_KEN -> bsd_high_port_range
    | INITIAL_HOST_JAN -> linux_bonus_high_port_range
    | INITIAL_HOST_ADA -> bsd_low_port_range
    | INITIAL_HOST_DAG -> bsd_low_port_range
    | INITIAL_HOST_TOM -> bsd_low_port_range
;;

let platform_type_to_string p =
  match p with
    ARCH_BSD -> "FreeBSD_4_6_RELEASE"  (* really: +TCP_DEBUG, +kernel time accuracy: (smb50:NEW KERNEL) *)
  | ARCH_LINUX -> "Linux_2_4_20_8"
  | ARCH_WINXP -> "WinXP_Prof_SP1";;


let string_of_ip_no_dots ip =
  let ip_str = Ocamllib.string_of_ip ip in
  let rec loop i =
    if i < 0 then ip_str
    else if (String.get ip_str i) = '.' then
      (String.set ip_str i ' ';
       loop (i-1))
    else
      loop (i-1)
  in loop ((String.length ip_str) - 1);;


let initial_host_to_string host tid arch ispriv bound_ip_port_list =
  let ip_str = " (IP " ^ (print_initial_host_ip host) ^")" in
  let tid_str = " (TID " ^ (Int64.to_string tid) ^ ")" in
  let arch_str = " (" ^ (platform_type_to_string arch) ^ ")" in
  let priv_str = if ispriv then " T" else " F" in
  let bound_ip_ports_str = (* Construct the list of bound ips/ports *)
    match bound_ip_port_list with
      [] -> " []"
    | _ ->
	let mk_pair s (is, p) =
	  let ip =
	    match is with
	      None -> "NONE"
	    | Some(ip) -> sprintf "SOME(IP %s)" (string_of_ip_no_dots ip) in
	  (s ^ "( " ^ ip ^ ", Port " ^ (string_of_int p) ^ ");") in
	List.fold_left mk_pair " [" bound_ip_port_list in
  (* and change the trailing semi-colon to a closing square bracket *)
  String.set bound_ip_ports_str ((String.length bound_ip_ports_str) - 1) ']';
  let ifaces = (get_ifaces host) ^ " " in
  let rttab = (get_rttab host) ^ " " in
  let fds = (get_prealloc_fds host) ^ " " in
  let param_str = (print_initial_host_params host) in
  let host_test =
    "(* HOST *)\n" ^
    "initial_host"^ip_str^tid_str^arch_str^priv_str^bound_ip_ports_str^" " ^ifaces^rttab^fds^"initial_ticker_count initial_ticker_remdr "^param_str^"\n"^
    "(* TSOH *)\n" in
  host_test;;


(* ---------------------------------------------------------------------- *)

(* Fake IP addresses for use with the magic mirror *)

let dag_fake_ip = (192,168,14,105)
let tom_fake_ip = (192,168,14,106)

(* ---------------------------------------------------------------------- *)
(* Description of test hosts *)
(* ---------------------------------------------------------------------- *)

type host_info = {
    platform_type           : platform_types;      (* host platform type *)
    host_name               : string;              (* host name *)
    iface_name              : string;              (* name of test interface, e.g. eth0 *)
    loopback_name           : string;              (* name of loopback interface, e.g. lo *)

    (* [(1,1024), (2048-3000)] represents 1-1024, 2048-3000 inclusive *)
    priv_port_range         : (int * int) list;  (* privileged port range on host *)
    ephm_port_range         : (int * int) list;  (* ephemeral port range on host *)
    npoe_port_range         : (int * int) list;  (* all other valid port ranges on host *)

    test_ip_address         : Ttheehelper.ip;   (* local ip address to use for tests *)
    test_subnet_mask        : Ttheehelper.ip;   (* subnet mask *)
    unavailable_ip_address  : Ttheehelper.ip;   (* not assigned to a local interface *)
    test_priv_port          : int;              (* priv port to use in tests *)
    test_ephm_port          : int;              (* ephemeral port to use in *SOME* tests *)
    test_npoe_port          : int;              (* non-priv non-ephem port to use in tests *)
    test_listening_port_base: int;              (* lowest port to select for listening *)
    test_listening_port_range:int;              (* select from [base,base+range-1] *)

    max_proc_fds            : int;              (* Max number of per-process file descriptors *)
    max_sys_fds             : int;              (* Max number of system file descriptors *)
    so_max_conns            : int;              (* Max number of connected sockets *)

    ns_tools_exec_params    : Tthee.exec_params;   (* exec parameters for our test tools on host *)
    host_supports_holtcpcb  : bool;                      (* host supports TCP_DEBUG and holtcpcb *)
    hol_initial_host        : (* Testscommon. *)initial_host;  (* HOL specific initial host type *)
  } ;;

let john_host_info = {
  platform_type = ARCH_BSD;
  host_name = "john";
  iface_name = "ep0";
  loopback_name = "lo0";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = john_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 957;
  max_sys_fds = 1064;
  so_max_conns = 5;
  ns_tools_exec_params = john_remote;
  host_supports_holtcpcb = true;
  hol_initial_host = INITIAL_HOST_JOHN
}

let emil_host_info = {
  platform_type = ARCH_BSD;
  host_name = "emil";
  iface_name = "ep0";
  loopback_name = "lo0";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = emil_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 957;
  max_sys_fds = 1064;
  so_max_conns = 5;
  ns_tools_exec_params = emil_remote;
  host_supports_holtcpcb = true;
  hol_initial_host = INITIAL_HOST_EMIL
}

let kurt_host_info = {
  platform_type = ARCH_LINUX;
  host_name = "kurt";
  iface_name = "eth0";
  loopback_name = "lo";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = kurt_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 8192;
  max_sys_fds = 1024;
  so_max_conns = 5;
  ns_tools_exec_params = kurt_remote;
  host_supports_holtcpcb = false;
  hol_initial_host = INITIAL_HOST_KURT
}

let alan_host_info = {
  platform_type = ARCH_LINUX;
  host_name = "alan";
  iface_name = "eth0";
  loopback_name = "lo";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = alan_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 8192;
  max_sys_fds = 1024;
  so_max_conns = 5;
  ns_tools_exec_params = alan_remote;
  host_supports_holtcpcb = false;
  hol_initial_host = INITIAL_HOST_ALAN
}

let glia_host_info = {
  platform_type = ARCH_WINXP;
  host_name = "glia";
  iface_name = "\\Device\\NPF_{E156046C-C2F7-44FC-B502-9FBAB66E211C}";
  (* Loopback name is wrong; fix later *)
  loopback_name = "\\Device\\NPF_{E156046C-C2F7-44FC-B502-9FBAB66E211C}";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = glia_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 1025;
  max_sys_fds = 1025;
  so_max_conns = 5;
  ns_tools_exec_params = glia_remote;
  host_supports_holtcpcb = false;
  hol_initial_host = INITIAL_HOST_GLIA
}

let alf_host_info = {
  platform_type = ARCH_BSD;
  host_name = "alf";
  iface_name = "xl0";
  loopback_name = "lo0";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(49152, 65535);];
  npoe_port_range = [(1025, 49151);];
  test_ip_address = alf_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 55555;
  test_npoe_port = 4444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 957;
  max_sys_fds = 1064;
  so_max_conns = 5;
  ns_tools_exec_params = alf_remote;
  host_supports_holtcpcb = true;
  hol_initial_host = INITIAL_HOST_ALF
}

let ken_host_info = {
  platform_type = ARCH_BSD;
  host_name = "ken";
  iface_name = "xl0";
  loopback_name = "lo0";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = ken_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 957;
  max_sys_fds = 1064;
  so_max_conns = 5;
  ns_tools_exec_params = ken_remote;
  host_supports_holtcpcb = true;
  hol_initial_host = INITIAL_HOST_KEN
}

let jan_host_info = {
  platform_type = ARCH_LINUX;
  host_name = "jan";
  iface_name = "eth0";
  loopback_name = "lo";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = jan_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 8192;
  max_sys_fds = 1024;
  so_max_conns = 5;
  ns_tools_exec_params = jan_remote;
  host_supports_holtcpcb = false;
  hol_initial_host = INITIAL_HOST_JAN
}

let ada_host_info = {
  platform_type = ARCH_LINUX;
  host_name = "ada";
  iface_name = "eth0";
  loopback_name = "lo";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = ada_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 8192;
  max_sys_fds = 1024;
  so_max_conns = 5;
  ns_tools_exec_params = ada_remote;
  host_supports_holtcpcb = false;
  hol_initial_host = INITIAL_HOST_ADA
}

let dag_host_info = {
  platform_type = ARCH_BSD;
  host_name = "dag";
  iface_name = "xl0";
  loopback_name = "lo0";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = dag_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 957;
  max_sys_fds = 1064;
  so_max_conns = 5;
  ns_tools_exec_params = dag_remote;
  host_supports_holtcpcb = true;
  hol_initial_host = INITIAL_HOST_DAG
}

let tom_host_info = {
  platform_type = ARCH_BSD;
  host_name = "tom";
  iface_name = "xl0";
  loopback_name = "lo0";
  priv_port_range = [(1, 1024);];
  ephm_port_range = [(1025, 8192);];
  npoe_port_range = [(8193, 65535);];
  test_ip_address = tom_priv_ip;
  test_subnet_mask = subnet_mask;
  unavailable_ip_address = unused_ip;
  test_priv_port = 222;
  test_ephm_port = 3333;
  test_npoe_port = 44444;
  test_listening_port_base = 20000;
  test_listening_port_range = 100;
  max_proc_fds = 957;
  max_sys_fds = 1064;
  so_max_conns = 5;
  ns_tools_exec_params = tom_remote;
  host_supports_holtcpcb = true;
  hol_initial_host = INITIAL_HOST_TOM
}
