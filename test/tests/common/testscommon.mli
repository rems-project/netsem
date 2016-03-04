open Tthee;;
open Nettypes;;

(* Program paths *)
val john_execpaths: exec_paths;;
val emil_execpaths: exec_paths;;
val alan_execpaths: exec_paths;;
val kurt_execpaths: exec_paths;;
val local_execpaths: exec_paths;;
val glia_execpaths: exec_paths;;
val alf_execpaths: exec_paths;;
val ken_execpaths: exec_paths;;
val jan_execpaths: exec_paths;;
val ada_execpaths: exec_paths;;
val dag_execpaths: exec_paths;;
val tom_execpaths: exec_paths;;

(* Private IP addresses *)
val astrocyte_priv_ip: Ttheehelper.ip;;
val thalamus_priv_ip: Ttheehelper.ip;;
val glia_priv_ip: Ttheehelper.ip;;
val kurt_priv_ip: Ttheehelper.ip;;
val john_priv_ip: Ttheehelper.ip;;
val emil_priv_ip: Ttheehelper.ip;;
val alan_priv_ip: Ttheehelper.ip;;
val psyche_priv_ip: Ttheehelper.ip;;
val thalamus_real_ip: Ttheehelper.ip;;
val unused_ip: Ttheehelper.ip;;
val broadcast_ip: Ttheehelper.ip;;
val multicast_ip: Ttheehelper.ip;;
val subnet_mask: Ttheehelper.ip;;

val alf_priv_ip: Ttheehelper.ip;;
val ken_priv_ip: Ttheehelper.ip;;
val jan_priv_ip: Ttheehelper.ip;;
val ada_priv_ip: Ttheehelper.ip;;
val dag_priv_ip: Ttheehelper.ip;;
val tom_priv_ip: Ttheehelper.ip;;
val fornix_priv_ip: Ttheehelper.ip;;
val zonule_priv_ip: Ttheehelper.ip;;

(* Remote execution parameters *)
val john_remote: exec_params;;
val emil_remote: exec_params;;
val kurt_remote: exec_params;;
val alan_remote: exec_params;;
val glia_remote: exec_params;;
val alf_remote: exec_params;;
val ken_remote: exec_params;;
val jan_remote: exec_params;;
val ada_remote: exec_params;;
val dag_remote: exec_params;;
val tom_remote: exec_params;;

(* Local execution parameters *)
val local_ep: exec_params;;

type platform_types =
    ARCH_BSD
  | ARCH_LINUX
  | ARCH_WINXP
;;

(* Initial host choices *)
type initial_host =
    INITIAL_HOST_JOHN
  | INITIAL_HOST_EMIL
  | INITIAL_HOST_KURT
  | INITIAL_HOST_ALAN
  | INITIAL_HOST_GLIA
  | INITIAL_HOST_THALAMUS
  | INITIAL_HOST_ALF
  | INITIAL_HOST_KEN
  | INITIAL_HOST_JAN
  | INITIAL_HOST_ADA
  | INITIAL_HOST_DAG
  | INITIAL_HOST_TOM
;;

val print_initial_host_ip: initial_host -> string;;
val print_initial_host_name: initial_host -> string;;
val get_initial_host_ip: initial_host -> Ttheehelper.ip;;

val initial_host_to_string: initial_host -> uint -> platform_types -> bool -> (Ocamllib.ip option * int) list -> string;;

val dag_fake_ip: Ttheehelper.ip;;
val tom_fake_ip: Ttheehelper.ip;;

type host_info = {
    platform_type          : platform_types;      (* host platform type *)
    host_name              : string;              (* host name *)
    iface_name             : string;              (* name of test interface, e.g. eth0 *)
    loopback_name          : string;              (* name of loopback interface, e.g. lo *)

    (* [(1,1024), (2048-3000)] represents 1-1024, 2048-3000 inclusive *)
    priv_port_range        : (int * int) list;  (* privileged port range on host *)
    ephm_port_range        : (int * int) list;  (* ephemeral port range on host *)
    npoe_port_range        : (int * int) list;  (* all other valid port ranges on host *)

    test_ip_address        : Ttheehelper.ip;   (* local ip address to use for tests *)
    test_subnet_mask        : Ttheehelper.ip;  (* subnet mask *)
    unavailable_ip_address : Ttheehelper.ip;   (* not assigned to a local interface *)
    test_priv_port         : int;              (* priv port to use in tests *)
    test_ephm_port         : int;              (* ephemeral port to use in *SOME* tests *)
    test_npoe_port         : int;              (* non-priv non-ephem port to use in tests *)
    test_listening_port_base:int;              (* port to listen for incoming connections on *)
    test_listening_port_range:int;             (* may add up to this much to base *)

    max_proc_fds           : int;              (* Max number of per-process file descriptors *)
    max_sys_fds            : int;              (* Max number of system file descriptors *)
    so_max_conns           : int;              (* Max number of connected sockets *)

    ns_tools_exec_params   : Tthee.exec_params;         (* exec parameters for our test tools on host *)
    host_supports_holtcpcb : bool;                      (* host supports TCP_DEBUG and holtcpcb *)
    hol_initial_host       : (*Testscommon.*)initial_host;  (* HOL specific initial host type *)
  } ;;

val john_host_info : host_info;;
val emil_host_info : host_info;;
val kurt_host_info : host_info;;
val alan_host_info : host_info;;
val glia_host_info : host_info;;
val alf_host_info : host_info;;
val ken_host_info : host_info;;
val jan_host_info : host_info;;
val ada_host_info : host_info;;
val tom_host_info : host_info;;
val dag_host_info : host_info;;
