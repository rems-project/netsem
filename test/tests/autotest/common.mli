(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Common Code *)
(* Steve Bishop - Created 20030314          *)
(* $Id: common.mli,v 1.31 2006/06/14 12:01:08 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread;;
open Unix;;
open ThreadUnix;;

(* Our libraries *)
open Nettypes;;
open Netconv;;
open Tthee;;
open Ttheehelper;;
open Libcalls;;
open Testscommon;;

exception Test_failed of string;;
exception Assertion_failed of string;;

(* Number of digits used to display trace sequence numbers *)
val trace_name_number_size: int ref;;

(* Time to wait following a test before shutting down. Allow the *)
(* network time to reach a peaceful state *)
val test_quiet_period: float ref;;

(* Port bases used for tthee command and control channels *)
val tthee_baseport_1: int ref;;
val tthee_baseport_2: int ref;;

(* Tthee merger delta value *)
val merger_delta: int ref;;

(* ---------------------------------------------------------------------- *)
(* Description of test hosts *)
(* ---------------------------------------------------------------------- *)

type host_info = Testscommon.host_info;;
(* moved to testscommon
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
    test_listening_port    : int;              (* port to listen for incoming connections on *)

    max_proc_fds           : int;              (* Max number of per-process file descriptors *)
    max_sys_fds            : int;              (* Max number of system file descriptors *)
    so_max_conns           : int;              (* Max number of connected sockets *)

    ns_tools_exec_params   : Tthee.exec_params;         (* exec parameters for our test tools on host *)
    host_supports_holtcpcb : bool;                      (* host supports TCP_DEBUG and holtcpcb *)
    hol_initial_host       : Testscommon.initial_host;  (* HOL specific initial host type *)
  } ;;
*)

(* Returns a string representation of a platform_type *)
val platform_to_string: platform_types -> string;;

(* ---------------------------------------------------------------------- *)
(* Bound socket state manipulation *)
(* ---------------------------------------------------------------------- *)

type local_port_binding =
    PORT_UNSPEC
  | PORT_PRIV
  | PORT_EPHEMERAL
  | PORT_NPOE;;

type local_ip_binding =
    IP_UNSPEC
  | IP_LOCAL;;

type foreign_ip_binding =
    IP_FOREIGN;;

type binding_type =                         (* is1 ps1 is2 ps2 *)
  | LOCAL_BOUND of                          (*  xs  ys  -   -  *)
      local_ip_binding * local_port_binding
  | CONNECTED_BOUND of                      (*  xs  ys  w   z  *)
      local_ip_binding * local_port_binding * foreign_ip_binding;;

(* All types of non-privileged, locally bound sockets *)
val local_bindings_list_non_priv: binding_type list;;

(* All types of privileged, locally bound sockets *)
val local_bindings_list_priv: binding_type list;;

(* All types of locally bound sockets *)
val local_bindings_list: binding_type list;;

(* All types of non-privileged, connected sockets *)
val connected_bindings_list_non_priv: binding_type list;;

(* All types of privileged, connected sockets *)
val connected_bindings_list_priv: binding_type list;;

(* All types of connected sockets *)
val connected_bindings_list: binding_type list;;

(* All types of bound and/or connected sockets *)
val all_bindings_list: binding_type list;;

(* binding_type_to_string binding_type = string *)
(* Returns a string explaining the binding for a provided binding type *)
val binding_type_to_string: binding_type -> string;;


(* ---------------------------------------------------------------------- *)
(* Preinitialisation of test socket *)
(* ---------------------------------------------------------------------- *)

type preinit_state =
    SOCKET_ONLY
  | BOUND_SOCKET of binding_type
  | BOUND_SOCKET_CUSTOM of binding_type * (unit -> unit);;

type test_type =
    TCP_NORMAL
  | UDP_NORMAL
  | ALL_NORMAL
  | TCP_EXHAUSTIVE
  | UDP_EXHAUSTIVE
  | ALL_EXHAUSTIVE
  | STREAM_NORMAL
  | STREAM_EXHAUSTIVE;;

val get_test_type: string -> test_type

val test_type_str: test_type -> string

(* ---------------------------------------------------------------------- *)
(* The useful functions *)
(* ---------------------------------------------------------------------- *)

(* Abstract type of test handles *)
type autotest_handle = {
    tthee_host_ip : Ttheehelper.ip;    (* IP address of host running tthee *)
    output_filename : string;          (* incl full path *)
    output_start_seq_num  : uint;      (* starting sequence number *)
    output_actual_seq_num : uint ref;  (* current test sequence number *)
    output_seq_min : uint;             (* minimum sequence number to actually output *)
    output_seq_max : uint;             (* maximum sequence number to actually output *)
    logging_fd : Unix.file_descr;      (* file descriptor for logging *)
    logging_ch : out_channel;          (* output channel for logging *)
    vhost_ip : Ttheehelper.ip;  (* IP address of the virtual test host *)
    vhost_port : int;           (* Port to connect to on virtual test host *)
  } ;;

(* init_tests tthee_host_ip output_name output_seq_no minseq maxseq logfname vhost_ip vhost_port = handle *)
(* Test output is merged to the filename output_name^(output_seq_no+x) *)
(* where x is the current test number. Tests start at minseq and continue *)
(* until maxseq if minseq != 0 and maxseq != 0. output_name should contain a *)
(* fully-qualified path. tthee_host_ip is the IP address of the host *)
(* running the test harness code. logfname is the fully qualified path *)
(* to where the overall success of autotesting should be recorded *)
(* vhost_ip is the ip address of the virtual test host to use during tests *)
(* and vhost_port is the imaginary port to connect to *)
val initialise_tests: Ttheehelper.ip -> string ->  uint -> uint -> uint -> string -> Ttheehelper.ip ->
  int ->  autotest_handle;;

(* clearup_tests autotest_handle = unit *)
(* Clean up after all the tests have been completed *)
val clearup_tests: autotest_handle -> unit;;

(* skip_test handle = bool *)
(* Skip the next test based upon whether its sequence number is in range *)
val skip_test: autotest_handle -> bool;;

(* ---------------------------------------------------------------------- *)
(* Logging and reporting functions                                        *)
(* ---------------------------------------------------------------------- *)

(* begin_next_test_group autotest_handle test_description = unit *)
(* Log the start of each new test group to stderr and the log *)
val begin_next_test_group: autotest_handle -> string -> unit;;

(* next_test autotest_handle = unit *)
(* Called after each test within a test group to increment the current test *)
(* number and show progress is being made on stderr *)
val next_test: autotest_handle -> unit;;

(* report_test_failure autotest_handle failure_message exception = unit *)
(* Report a test failure to stderr and the log *)
val report_test_failure: autotest_handle -> string -> exn -> unit;;

(* inter_test_delay delay_in_seconds = unit *)
(* Prints a delay warning message to stderr, delays execution of the test for *)
(* delay_in_seconds seconds and then continues *)
val inter_test_delay: float -> unit;;

(* ---------------------------------------------------------------------- *)
(* Some useful definitions                                                *)
(* ---------------------------------------------------------------------- *)

(* create_host_pairs host_list = host_pair_list *)
(* Create all pairs of platforms from the host list *)
(* i.e. for a list of length n, all nP2 pairs *)
val create_host_pairs: host_info list -> (host_info * host_info) list;;

val pick_any_other_host: host_info list -> host_info -> host_info;;

(* fmt_fname autotest_handle seq_no_precision = string *)
(* Create the unique filename for a test run by appending *)
(* the test's sequence number displayed to seq_no_precision *)
(* number of digits to the base filename *)
val fmt_fname: autotest_handle -> int -> string;;

val mk_ip: Ttheehelper.ip -> Ocamllib.ip;;
val mk_port: int -> Ocamllib.port;;

(* ---------------------------------------------------------------------- *)

(* List containing 500 bytes of data *)
val data_500_bytes: uint list

(* List containing n bytes of data *)
val data_n_bytes: int -> uint list

val all_but_last: 'a list -> 'a list

(* ntp update *)
val ntp_update: float -> unit

(* string more than 1460 bytes long *)
val very_long_string: string

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
