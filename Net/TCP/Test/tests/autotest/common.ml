(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Common Code                               *)
(* Steve Bishop - Created 20030314                                        *)
(* $Id: common.ml,v 1.45 2006/06/14 12:01:08 amgb2 Exp $                  *)
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

(* ---------------------------------------------------------------------- *)
(* Global values                                                          *)
(* ---------------------------------------------------------------------- *)

let autotest_version = "$Id: common.ml,v 1.45 2006/06/14 12:01:08 amgb2 Exp $";;

exception Test_failed of string;;
exception Assertion_failed of string;;

(* Number of digits used to display trace sequence numbers *)
let trace_name_number_size = ref 4;;

(* Time to wait following a test before shutting down. Allow the *)
(* network time to reach a peaceful state *)
let test_quiet_period = ref 1.50;;

(* Port bases used for tthee command and control channels *)
let tthee_baseport_1 = ref 45000;;
let tthee_baseport_2 = ref 46000;;

(* Tthee merger delta value *)
let merger_delta = ref 100000;

type autotest_handle = {
    tthee_host_ip : Ttheehelper.ip;    (* IP address of host running tthee *)
    output_filename : string;          (* incl full path *)
    output_start_seq_num  : uint;      (* starting sequence number *)
    output_actual_seq_num : uint ref;  (* current test sequence number *)
    output_seq_min : uint;             (* minimum sequence number to actually output *)
    output_seq_max : uint;             (* maximum sequence number to actually output *)
    logging_fd : Unix.file_descr;      (* file descriptor for logging *)
    logging_ch : out_channel;          (* output channel for logging *)
    vhost_ip : Ttheehelper.ip;         (* IP address of the virtual test host *)
    vhost_port : int;                  (* Port to connect to on virtual test host *)
  } ;;

type host_info = Testscommon.host_info;;

let platform_to_string p =
  match p with
    ARCH_BSD -> "BSD"
  | ARCH_LINUX -> "LINUX"
  | ARCH_WINXP -> "WINXP";;


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
let local_bindings_list_non_priv = [
  LOCAL_BOUND(IP_UNSPEC, PORT_UNSPEC);
  LOCAL_BOUND(IP_UNSPEC, PORT_EPHEMERAL);
  LOCAL_BOUND(IP_UNSPEC, PORT_NPOE);
  LOCAL_BOUND(IP_LOCAL, PORT_UNSPEC);
  LOCAL_BOUND(IP_LOCAL, PORT_EPHEMERAL);
  LOCAL_BOUND(IP_LOCAL, PORT_NPOE)
] ;;

(* All types of privileged, locally bound sockets *)
let local_bindings_list_priv = [
  LOCAL_BOUND(IP_UNSPEC, PORT_PRIV);
  LOCAL_BOUND(IP_LOCAL, PORT_PRIV)
] ;;

(* All types of locally bound sockets *)
let local_bindings_list = local_bindings_list_non_priv @ local_bindings_list_priv;;

(* All types of non-privileged, connected sockets *)
let connected_bindings_list_non_priv = [
  CONNECTED_BOUND(IP_UNSPEC, PORT_UNSPEC, IP_FOREIGN);
  CONNECTED_BOUND(IP_UNSPEC, PORT_PRIV, IP_FOREIGN);
  CONNECTED_BOUND(IP_UNSPEC, PORT_EPHEMERAL, IP_FOREIGN);
  CONNECTED_BOUND(IP_UNSPEC, PORT_NPOE, IP_FOREIGN);
  CONNECTED_BOUND(IP_LOCAL, PORT_UNSPEC, IP_FOREIGN);
  CONNECTED_BOUND(IP_LOCAL, PORT_PRIV, IP_FOREIGN);
  CONNECTED_BOUND(IP_LOCAL, PORT_EPHEMERAL, IP_FOREIGN);
  CONNECTED_BOUND(IP_LOCAL, PORT_NPOE, IP_FOREIGN)
] ;;

(* All types of privileged, connected sockets *)
let connected_bindings_list_priv = [
  CONNECTED_BOUND(IP_UNSPEC, PORT_PRIV, IP_FOREIGN);
  CONNECTED_BOUND(IP_LOCAL, PORT_PRIV, IP_FOREIGN)
] ;;

(* All types of connected sockets *)
let connected_bindings_list = connected_bindings_list_non_priv @ connected_bindings_list_priv;;

(* List of all possible types of bound socket *)
let all_bindings_list = local_bindings_list @ local_bindings_list @ connected_bindings_list;;

(* binding_type_to_string binding_type = string *)
(* Returns a string explaining the binding for a provided binding type *)
let binding_type_to_string bt =
  match bt with
    LOCAL_BOUND(IP_UNSPEC, PORT_UNSPEC) -> "local_bound(ip_unspec, port_unspec)"
  | LOCAL_BOUND(IP_UNSPEC, PORT_PRIV) -> "local_bound(ip_unspec, port_priv)"
  | LOCAL_BOUND(IP_UNSPEC, PORT_EPHEMERAL) -> "local_bound(ip_unspec, port_ephemeral)"
  | LOCAL_BOUND(IP_UNSPEC, PORT_NPOE) -> "local_bound(ip_unspec, port_npoe)"
  | LOCAL_BOUND(IP_LOCAL, PORT_UNSPEC) -> "local_bound(ip_local, port_unspec)"
  | LOCAL_BOUND(IP_LOCAL, PORT_PRIV) -> "local_bound(ip_local, port_priv)"
  | LOCAL_BOUND(IP_LOCAL, PORT_EPHEMERAL) -> "local_bound(ip_local, port_ephemeral)"
  | LOCAL_BOUND(IP_LOCAL, PORT_NPOE) -> "local_bound(ip_local, port_npoe)"
  | CONNECTED_BOUND(IP_UNSPEC, PORT_UNSPEC, IP_FOREIGN) ->
      "connected(ip_unspec, port_unspec, ip_foreign)"
  | CONNECTED_BOUND(IP_UNSPEC, PORT_PRIV, IP_FOREIGN) ->
      "connected(ip_unspec, port_priv, ip_foreign)"
  | CONNECTED_BOUND(IP_UNSPEC, PORT_EPHEMERAL, IP_FOREIGN) ->
      "connected(ip_unspec, port_ephemeral, ip_foreign)"
  | CONNECTED_BOUND(IP_UNSPEC, PORT_NPOE, IP_FOREIGN) ->
      "connected(ip_unspec, port_npoe, ip_foreign)"
  | CONNECTED_BOUND(IP_LOCAL, PORT_UNSPEC, IP_FOREIGN) ->
      "connected(ip_local, port_unspec, ip_foreign)"
  | CONNECTED_BOUND(IP_LOCAL, PORT_PRIV, IP_FOREIGN) ->
      "connected(ip_local, port_priv, ip_foreign)"
  | CONNECTED_BOUND(IP_LOCAL, PORT_EPHEMERAL, IP_FOREIGN) ->
      "connected(ip_local, port_ephemeral, ip_foreign"
  | CONNECTED_BOUND(IP_LOCAL, PORT_NPOE, IP_FOREIGN) ->
      "connected(ip_local, port_npoe, ip_foreign";;

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

let get_test_type tt =
  match tt with
    "TCP_NORMAL" -> TCP_NORMAL
  | "UDP_NORMAL" -> UDP_NORMAL
  | "ALL_NORMAL" -> ALL_NORMAL
  | "TCP_EXHAUSTIVE" -> TCP_EXHAUSTIVE
  | "UDP_EXHAUSTIVE" -> UDP_EXHAUSTIVE
  | "ALL_EXHAUSTIVE" -> ALL_EXHAUSTIVE
  | "STREAM_NORMAL" -> STREAM_NORMAL
  | "STREAM_EXHAUSTIVE" -> STREAM_EXHAUSTIVE

let test_type_str tt =
  match tt with
    TCP_NORMAL -> "[TCP normal]"
  | UDP_NORMAL -> "[UDP normal]"
  | ALL_NORMAL -> "[ALL normal]"
  | TCP_EXHAUSTIVE -> "[TCP exhaustive]"
  | UDP_EXHAUSTIVE -> "[UDP exhaustive]"
  | ALL_EXHAUSTIVE -> "[ALL exhaustive]"
  | STREAM_NORMAL -> "[STREAM normal]"
  | STREAM_EXHAUSTIVE -> "[STREAM exhaustive]"

(* ---------------------------------------------------------------------- *)

(* Print a message to stderr and flush the channel *)
let print_message str =
  prerr_string str;
  (* Two flushes are often required.... don't know why! *)
  flush Pervasives.stderr;
  flush Pervasives.stderr;;

(* Return the current local time as a string *)
let get_localtime_string () =
  let tm = Unix.localtime (Unix.time ()) in
  sprintf "%4d%2.2d%2.2d %2.2d:%2.2d:%2.2d UTC" (tm.tm_year+1900) tm.tm_mon tm.tm_mday
    tm.tm_hour tm.tm_min tm.tm_sec;;

(* Print the startup banner to stderr and to a logging channel *)
let autotesting_startup_message ch =
  let banner_1 = "\n----------------------------------------------------------------------\n" in
  let banner_2 = "Netsem automatic testing tool --- " ^ (get_localtime_string ()) ^ "\n" in
  let banner_3 = "Version: " ^ autotest_version ^ "\n" in
  let banner_4 = "----------------------------------------------------------------------" in
  let banner = (banner_1 ^ banner_2 ^ banner_3 ^ banner_4) in
  print_message banner;
  output_string ch (banner ^ "\n");
  flush ch;;

(* begin_next_test_group autotest_handle test_description = unit *)
(* Log the start of each new test group to stderr and the log *)
let begin_next_test_group handle testname =
  print_message ("\n\n" ^ testname ^ ": ");
  output_string handle.logging_ch ("\n\nStarting test: " ^ testname ^ "");
  flush handle.logging_ch;;

(* next_test autotest_handle = unit *)
(* Called after each test within a test group to increment the current test *)
(* number and show progress is being made on stderr *)
let next_test handle =
  if (handle.output_seq_min = uint 0) && (handle.output_seq_max = uint 0) then
    print_message "."
  else if (!(handle.output_actual_seq_num) >= handle.output_seq_min) &&
    (!(handle.output_actual_seq_num) <= handle.output_seq_max) then
    print_message "."
  else
    ();
  handle.output_actual_seq_num := !(handle.output_actual_seq_num) +. (uint 1);;

(* report_test_failure autotest_handle failure_message = unit *)
(* Report a test failure to stderr and the log *)
let report_test_failure handle msg e =
  let realmsg = "Test #" ^ (Int64.to_string !(handle.output_actual_seq_num)) ^
    " failed: \n" ^ msg ^ "\nOriginal exception:" ^ Printexc.to_string e ^ "\n\n"in
  print_message ("\n" ^ realmsg);
  output_string handle.logging_ch ("\n****"^realmsg);
  flush handle.logging_ch;;

(* inter_test_delay delay_in_seconds = unit *)
(* Prints a delay warning message to stderr, delays execution of the test for *)
(* delay_in_seconds seconds and then continues *)
let inter_test_delay t =
  print_message ("[Pausing for " ^ (string_of_float t) ^ "0s...");
  delay t;
  print_message "continuing] ";;

(* ---------------------------------------------------------------------- *)
(* Some useful per-test specific definitions *)
(* ---------------------------------------------------------------------- *)

(* init_tests tthee_host_ip output_name output_seq_no minseq maxseq logfname vhost_ip vhost_port = handle *)
(* Test output is merged to the filename output_name^(output_seq_no+x) *)
(* where x is the current test number. Tests start at minseq and continue *)
(* until maxseq if minseq != 0 and maxseq != 0. output_name should contain a *)
(* fully-qualified path. tthee_host_ip is the IP address of the host *)
(* running the test harness code. logfname is the fully qualified path *)
(* to where the overall success of autotesting should be recorded *)
(* vhost_ip is the ip address of the virtual test host to use during tests *)
(* and vhost_port is the imaginary port to connect to *)
let initialise_tests tthee_host_ip fname seqno minseq maxseq logfname vhost_ip vhost_port =
  let logging_fd = Unix.openfile logfname [O_WRONLY; O_CREAT; O_TRUNC] 432 in
  let logging_ch = out_channel_of_descr logging_fd in
  autotesting_startup_message logging_ch;
  { tthee_host_ip = tthee_host_ip;
    output_filename =  fname;
    output_start_seq_num = seqno;
    output_actual_seq_num = ref seqno;
    output_seq_min = minseq;
    output_seq_max = maxseq;
    logging_fd = logging_fd;
    logging_ch = logging_ch;
    vhost_ip = vhost_ip;
    vhost_port = vhost_port;
  } ;;

(* clearup_tests autotest_handle = unit *)
(* Clean up after all the tests have been completed *)
let clearup_tests handle =
  print_message "\n";
  Unix.close handle.logging_fd

(* skip_test handle = bool *)
(* Skip the next test based upon whether its sequence number is in range *)
let skip_test hnd =
  if hnd.output_seq_min = uint 0 && hnd.output_seq_max = uint 0 then
    false
  else if !(hnd.output_actual_seq_num) >= hnd.output_seq_min &&
    !(hnd.output_actual_seq_num) <= hnd.output_seq_max then
    false
  else
    true

(* ---------------------------------------------------------------------- *)

(* create_host_pairs host_list = host_pair_list *)
(* Create all pairs of platforms from the host list *)
(* i.e. for a list of length n, all nP2 pairs *)
let create_host_pairs host_list =
  let pairs x y = List.map (function z -> (x,z)) y in
  let list =
    let rec loop l r =
      match l with
	[] -> []
      | x::xs -> (pairs x (r@xs))::loop xs (x::r)
    in loop host_list []
  in List.flatten list;;

let rec pick_any_other_host host_list host =
  match host_list with
    [] -> raise(Test_failed("failed to pick_any_other_host"))
  | x::xs ->
      if (x = host) then pick_any_other_host xs host
      else x;;

(* fmt_fname autotest_handle seq_no_precision = string *)
(* Create the unique filename for a test run by appending *)
(* the test's sequence number displayed to seq_no_precision *)
(* number of digits to the base filename *)
let fmt_fname handle size =
  let numstr = Int64.to_string !(handle.output_actual_seq_num) in
  let padstr str n =
    let len = String.length str in
    if(len < size) then
      (String.make (size-len) '0')^numstr
    else
      numstr in
  handle.output_filename ^ (padstr numstr size);;

let mk_ip tthee_ip = Ocamllib.ip_of_string (string_ip tthee_ip);;

let mk_port tthee_port = Ocamllib.port_of_int tthee_port;;

(* ---------------------------------------------------------------------- *)

(* List containing 500 bytes of data *)
let data_500_bytes =
  let rec loop x acc =
    if x = 0 then acc
    else loop (x-1) (uint (Char.code 'b')::acc)
  in loop 500 []

(* List containing n bytes of data *)
let data_n_bytes n =
  let rec loop x acc =
    if x = 0 then acc
    else loop (x-1) (uint (Char.code 'n')::acc)
  in loop n []

let rec all_but_last l =
  match l with
    [] -> []
  | x::[] -> []
  | x::xs -> x::(all_but_last xs)

(* Function to enable then disable NTP time updates *)
(* let ntp_update x =
  let s = Unix.system "ntp_update ENABLE" in
  let _ =
    match s with
      Unix.WEXITED n ->
	if n = 0 then () else raise (Assertion_failed "ntp_update ENABLE exited but failed")
    | _ ->
	raise (Assertion_failed "ntp_update ENABLE failed") in
  let _ = delay 120.0 in
  let _ = tsccal_start 10 10000 in
  let _ = delay 60.0 in
  let s = Unix.system "ntp_update DISABLE" in
  match s with Unix.WEXITED n ->
    if n = 0 then () else raise (Assertion_failed "ntp_update DISABLE exited but failed")
  | _ ->
      raise (Assertion_failed "ntp_update DISABLE failed")*)

(* Disabling and re-enabling NTP updates don't really help with timestamping; disable for now *)
let ntp_update x = ()

(* A piece of text larger than 1460 bytes *)
let very_long_string =

"Four score and seven years ago our fathers brought forth on this continent, a new nation, conceived in Liberty, and dedicated to the proposition that all men are created equal. \n \
Now we are engaged in a great civil war, testing whether that nation, or any nation so conceived and so dedicated, can long endure. We are met on a great battle-field of that war. We have come to dedicate a portion of that field, as a final resting place for those who here gave their lives that that nation might live. It is altogether fitting and proper that we should do this. \n \
But, in a larger sense, we can not dedicate -- we can not consecrate -- we can not hallow -- this ground. The brave men, living and dead, who struggled here, have consecrated it, far above our poor power to add or detract. The world will little note, nor long remember what we say here, but it can never forget what they did here. It is for us the living, rather, to be dedicated here to the unfinished work which they who fought here have thus far so nobly advanced. It is rather for us to be here dedicated to the great task remaining before us -- that from these honored dead we take increased devotion to that cause for which they gave the last full measure of devotion -- that we here highly resolve that these dead shall not have died in vain -- that this nation, under God, shall have a new birth of freedom -- and that government of the people, by the people, for the people, shall not perish from the earth."

(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*- *)
(* ---------------------------------------------------------------------- *)
