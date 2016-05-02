(* A HOL98 specification of TCP *)

(* Rule names for the host specification LTS *)

(*[ RCSID "$Id: TCP1_ruleidsScript.sml,v 1.22 2009/02/17 11:56:46 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

val _ = new_theory "TCP1_ruleids";

(*: @chapter [[TCP1_ruleids]] Rule names

This file defines the names of transition rules in the specification.

:*)

(* -------------------------------------------------- *)
(*               RULE IDS                             *)
(* -------------------------------------------------- *)

(*: @section [[ruleids_ruleids]] Rule names

We list here the names of all rules in the host LTS.

:*)

val _ =
    Hol_datatype
      `rule_ids = return_1
                | socket_1 | socket_2
                | accept_1 | accept_2 | accept_3 | accept_4 | accept_5 | accept_6 | accept_7
                | bind_1 | bind_2 | bind_3 | bind_5 | bind_7 | bind_9
                | close_1 | close_2 | close_3 | close_4 | close_5
                | close_6 | close_7 | close_8 | close_10
                | connect_1 |connect_1a | connect_2 | connect_3 | connect_4 | connect_4a | connect_5
                | connect_5a | connect_5b | connect_5c | connect_5d | connect_6
                | connect_7 | connect_8 | connect_9 | connect_10
		| disconnect_1 | disconnect_2 | disconnect_3 | disconnect_4 | disconnect_5
                | dup_1 | dup_2
                | dupfd_1 | dupfd_3 | dupfd_4
                | listen_1 | listen_1b | listen_1c | listen_2 | listen_3 | listen_4 | listen_5 | listen_7
                | getfileflags_1
                | setfileflags_1
		| getifaddrs_1
                | getsockbopt_1 | getsockbopt_2
                | setsockbopt_1 | setsockbopt_2
                | getsocknopt_1 | getsocknopt_4
                | setsocknopt_1 | setsocknopt_4 | setsocknopt_2
                | getsocktopt_1 | getsocktopt_4
                | setsocktopt_1 | setsocktopt_4 | setsocktopt_5
                | getsockerr_1 | getsockerr_2
                | getsocklistening_1 | getsocklistening_2 | getsocklistening_3
                | shutdown_1 | shutdown_2 | shutdown_3 | shutdown_4
                | recv_1 | recv_2 | recv_3 | recv_4 | recv_5 | recv_6 | recv_7 | recv_8 | recv_8a | recv_9
                | recv_11 | recv_12 | recv_13 | recv_14 | recv_15 | recv_16 | recv_17 | recv_20 | recv_21 | recv_22
                | recv_23 | recv_24
                | send_1 | send_2 | send_3 | send_3a | send_4 | send_5 | send_5a
                | send_6 | send_7 | send_8 | send_9 | send_10
                | send_11 | send_12 | send_13 | send_14 | send_15
                | send_16 | send_17 | send_18 | send_19 | send_21 | send_22 | send_23
                | sockatmark_1 | sockatmark_2
                | pselect_1 | pselect_2 | pselect_3 | pselect_4 | pselect_5
                | pselect_6
                | getsockname_1 | getsockname_2 | getsockname_3
                | getpeername_1 | getpeername_2
                | badf_1
                | notsock_1
                | intr_1
                | resourcefail_1 | resourcefail_2
                | deliver_in_1 | deliver_in_1b | deliver_in_2 | deliver_in_2a
                | deliver_in_3 | deliver_in_3a | deliver_in_3b | deliver_in_3c
                | deliver_in_4 | deliver_in_5 | deliver_in_6
                | deliver_in_7 | deliver_in_7a | deliver_in_7b | deliver_in_7c
                | deliver_in_7d | deliver_in_8 | deliver_in_9
                | deliver_in_icmp_1 | deliver_in_icmp_2 | deliver_in_icmp_3
                | deliver_in_icmp_4 | deliver_in_icmp_5 | deliver_in_icmp_6
                | deliver_in_icmp_7
                | deliver_in_udp_1 | deliver_in_udp_2 | deliver_in_udp_3
                | deliver_in_99 | deliver_in_99a
                | timer_tt_rexmt_1
                | timer_tt_rexmtsyn_1
                | timer_tt_persist_1
                | timer_tt_2msl_1
                | timer_tt_delack_1
                | timer_tt_conn_est_1
                | timer_tt_keep_1
                | timer_tt_fin_wait_2_1
                | deliver_out_1
                | deliver_out_99
                | deliver_loop_99
                | trace_1 | trace_2
                | interface_1
                | epsilon_1
		| epsilon_2
`;
(* REMARK connect_1a is Spec3 only *)
(* -------------------------------------------------- *)

val _ = export_theory();
