(* ---------------------------------------------------------------------- *)
(* Netsem Tthee Automated Tests Common Code *)
(* Steve Bishop - Created 20030314          *)
(* $Id: autotest.ml,v 1.77 2006/07/03 15:32:12 amgb2 Exp $ *)
(* ---------------------------------------------------------------------- *)

(* Ocaml libraries *)
open Thread
open Printf

(* Our libraries *)
open Nettypes
open Testscommon
open Common
open Tthee

open Socket
open Bind
open Bind_2
open Bind_udp
open Connect
open Connect_udp
open Disconnect
open Listen
open Accept
open Dup
open Dupfd
open Drivetest
open Close
open Getifaddrs
open Getsocklistening
open Getnames
open Sockatmark_udp
open Sockbopt
open Socknopt
open Socktopt
open Shutdown
open Send
open Recv
open Send_to
open Recv_from
open Fileflags
open Getsockerr
open Deliver_in
open Timers
open Deliver_in_3
open Deliver_icmp
open Loopback
open Pselect
open Demo
open Network
open Loss

exception Incorrect_cmd_line_args of string

(* ---------------------------------------------------------------------- *)

let all_test_hosts = [dag_host_info; tom_host_info]

let all_test_platforms = [dag_host_info; tom_host_info]
let all_unix_platforms = [dag_host_info; tom_host_info]

(* A sensible design would have it so that if you're only testing on one
platform, there should only be one entry in all_test_platforms, but turns
out it picks the auxiliary host from there too, so you'll get an error *)

let all_test_platform_pairs = [(dag_host_info, tom_host_info)]

let all_loss_test_configs =
  [(dag_host_info, dag_fake_ip, tom_host_info, tom_fake_ip, alf_host_info);
   (tom_host_info, tom_fake_ip, dag_host_info, dag_fake_ip, alf_host_info)]

(* ---------------------------------------------------------------------- *)

let cmd_line_args = "autotest (TCP_NORMAL | UDP_NORMAL | ALL_NORMAL | TCP_EXHAUSTIVE | UDP_EXHAUSTIVE | ALL_EXHAUSTIVE | STREAM_NORMAL | STREAM_EXHAUSTIVE) trace_filename_prefix logging_filename [min_seq_no max_seq_no]";;

let check_cmdline_args argv =
  let len = Array.length argv in
  if(len = 4) then
   (Array.get argv 1, Array.get argv 2, Array.get argv 3, "0", "0")
  else if(len > 5) then
   (Array.get argv 1, Array.get argv 2, Array.get argv 3, Array.get argv 4, Array.get argv 5)
  else
    raise (Incorrect_cmd_line_args(cmd_line_args));;

let (tt, fname, lname, min, max) = check_cmdline_args Sys.argv in
let test_type =
  try get_test_type tt
  with _ -> raise (Incorrect_cmd_line_args(cmd_line_args)) in
let sseq, smin,smax = uint 0, Int64.of_string min, Int64.of_string max in
let test_hnd = initialise_tests zonule_priv_ip fname sseq smin smax lname (*psyche_priv_ip*)(192,168,13,199) 200 in

(* Test function, inter-test delay *)
let tests = [

   do_socket_tests test_hnd all_test_platforms, 1.00;
   do_driver_tests test_hnd all_test_platforms, 1.00;
   do_loopback_tests test_hnd all_test_platforms, 1.00;
   do_bind_tests test_hnd  all_test_platform_pairs, 700.00;
   do_bind_2_tests test_hnd all_test_platforms, 1.00;
   do_bind_udp_tests test_hnd all_test_platforms, 1.00;
   do_connect_tests test_hnd all_test_platforms, 1.00;
   do_connect_udp_tests test_hnd all_test_platforms, 1.00;
   do_listen_tests test_hnd all_test_platforms, 1.00;
   do_accept_tests test_hnd all_test_platforms, 1.00;
   do_disconnect_tests test_hnd all_test_platforms, 1.00;
   do_dup_tests test_hnd all_test_platforms, 1.00;
   do_dupfd_tests test_hnd all_test_platforms, 1.00;
   do_close_tests test_hnd all_test_platforms, 1.00;

   do_getifaddrs_tests test_hnd all_unix_platforms, 1.00;  (* don't run these tests on xp as there is no getifaddrs() call *)
   do_getsocklistening_tests test_hnd all_test_platforms, 1.00;
   do_getnames_tests test_hnd all_test_platforms, 1.00;
   do_sockatmark_udp_tests test_hnd all_test_platforms, 1.00;
   do_sockbopt_tests test_hnd all_test_platforms, 1.00;
   do_socknopt_tests test_hnd all_test_platforms, 1.00;
   do_socktopt_tests test_hnd all_test_platforms, 1.00;
   do_shutdown_tests test_hnd all_test_platforms, 1.00;

   do_send_tests test_hnd all_test_platforms, 1.00;
   do_recv_tests test_hnd all_test_platforms, 1.00;
   do_send_to_tests test_hnd all_test_platforms, 1.00;

   do_fileflags_tests test_hnd all_test_platforms, 1.00;
   do_getsockerr_tests test_hnd all_test_platforms, 1.00;
   do_recv_from_tests test_hnd all_test_platforms, 1.00;

   do_deliver_in_tests test_hnd all_test_platforms, 1.00;

   do_deliver_in_3_tests test_hnd all_test_platforms, 1.00;
   do_deliver_icmp_tests test_hnd all_test_platforms, 1.00;
   do_timer_tests test_hnd all_test_platforms, 1.00;
   do_pselect_tests test_hnd all_test_platforms, 1.00;
   do_demo_tests test_hnd all_test_platforms, 1.00;
   do_network_tests test_hnd all_test_platforms, 125.00;
   (*do_loss_tests test_hnd all_loss_test_configs, 1.00*)

] in

(* Perform the requested tests (TCP, UDP, all NORMAL, or EXHAUSTIVE) *)
List.iter (
function (f, d) ->
  if f test_type then inter_test_delay d else ()
) tests;

clearup_tests test_hnd



(* ---------------------------------------------------------------------- *)
(* -*-*- THE END -*-*-                                                    *)
(* ---------------------------------------------------------------------- *)
