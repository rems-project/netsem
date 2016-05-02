(* A HOL98 specification of TCP *)

(* Definitions of constants used in typical traces, particularly
   defining a sensible initial host *)

(*[ RCSID "$Id: TCP1_evalSupportScript.sml,v 1.33 2005/12/14 12:38:16 amgb2 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib containerTheory

open HolDoc

local open TCP1_baseTypesTheory
           TCP1_timersTheory
           TCP1_hostTypesTheory
           TCP1_hostLTSTheory
in end;

val Term = Parse.Term;

val _ = new_theory "TCP1_evalSupport";

(*: @chapter [[TCP1_evalSupport]] Initial state

This file defines a function to construct certain initial host states for use in automated trace checking, along with other
constants used in typical traces.
The interfaces, routing table and some host fields are taken from the |initial_host| line at the
  start of a valid trace.
:*)

(*: @section [[evals_foo]] ALL Initial state

The initial state of a host.

:*)

val _ = Phase.phase 0 Define `
    (*: simple ethernet interface :*)
    simple_ifd_eth i = (ETH 0, <| ipset := {i}; primary := i; netmask := NETMASK 24; up := T |>)`;

val _ = Phase.phase 0 Define `
    (*: simple loopback interface :*)
    simple_ifd_lo = (LO, <| ipset := LOOPBACK_ADDRS; primary := ip_localhost;
                            netmask:= NETMASK 8; up := T |>)`;

val _ = Phase.phase 1 Define `
    (*: simple routing table :*)
    simple_rttab = [<| destination_ip := ip_localhost;
                       destination_netmask := NETMASK 8;
                       ifid := LO |>;
                    <| destination_ip := IP 0 0 0 0;
                       destination_netmask := NETMASK 0;
                       ifid := ETH 0 |>]`;

val _ = Phase.phase 0 Define `
    (*: initial thread id :*)
    tid_initial = TID 0`;

val _ = Phase.phase 0 Define `
    (*: simple host state :*)
    simple_host i tick0 remdr0 =
        <| arch  := FreeBSD_4_6_RELEASE ;
           privs := F;
           ifds  := FEMPTY |++ [simple_ifd_lo; simple_ifd_eth i] ;
           rttab := simple_rttab;
           ts    := FUPDATE FEMPTY (tid_initial, Timed(Run,never_timer)) ;
           files := FEMPTY ;
           socks := FEMPTY ;
           listen := [] ;
           bound := [] ;
           iq    := Timed([],never_timer) ;
           oq    := Timed([],never_timer) ;
           bndlm := bandlim_state_init ;
           ticks := Ticker(tick0, remdr0, tickintvlmin, tickintvlmax) ;
           fds   := FEMPTY;
           params:= <| min_eph_port := 1024; max_eph_port := 5000 |>
        |> `;



val dummy_cb_def = Phase.phase 0 Define`
  dummy_cb = <| tt_rexmt := NONE;
                tt_2msl := NONE;
                tt_conn_est := NONE;
                tt_delack := NONE;
                tt_keep := NONE;
                tt_fin_wait_2 := NONE;
                t_idletime := Stopwatch(0, 1, 1);
                t_badrxtwin := TimeWindowClosed;
                ts_recent := TimeWindowClosed |>
`;

val dummy_socket_def = Phase.phase 0 Define`
  (*: minimal socket :*)
  dummy_socket (is,p) =
		   <| fid := NONE;
                      sf  := <| b := \x.F; n := \x.0; t := \x.time_infty |>;
                      is1 := is;
                      ps1 := SOME p;
                      is2 := NONE;
                      ps2 := NONE;
                      pr  := TCP_PROTO(<| st  := LISTEN;
                                          cb  := dummy_cb;
                                          lis := SOME <| q0 := []; q := []; qlimit := 10 |>
                                       |>)
                   |>
`(*: @description
This is a pretty minimally-defined socket, just enough to say
   "this port is bound". :*)
;

val _ = Phase.phase 1 Define`
  dummy_sockets n     []  = [] /\
  dummy_sockets n (p::ps) = (SID n,dummy_socket p) :: dummy_sockets (n+1) ps
`;

val _ = Phase.phase 0 Define`
  (*: function to construct an initial host for trace checking :*)
  initial_host (i:ip) (t:tid) (arch:arch) (ispriv:bool)
               (heldports:(ip option # port) list) (ifaces: (ifid # ifd) list)
               (rt: routing_table)
               (prealloc_fds: num list)
               (init_tick : ts_seq)
               (init_tick_remdr : duration)
               (params : hostParams)
    = simple_host i init_tick init_tick_remdr with <|
        arch := arch;
        privs := ispriv;
	ifds := FEMPTY |++ ifaces;
	rttab := rt;
        ts := FUPDATE FEMPTY (t, Timed(Run,never_timer));
  (* list of prealloacated fds is passed in as a list of ints, build the
     appropriate thing here *)
  fds := FEMPTY |++ (MAP (\x. (FD x, FID 0)) prealloc_fds);
        (*
        fds := case arch of
                  (* per architecture, note down FDs preallocated for
                     internal use by OCaml or the test harness *)
                  Linux_2_4_20_8 ->
                    FEMPTY |++ [(FD 0, FID 0);
                                         (FD 1, FID 0);
                                         (FD 2, FID 0);
					 (FD 3, FID 0);
					 (FD 4, FID 0);
                                         (FD 5, FID 0);
                                         (FD 6, FID 0);
                                         (FD 1000, FID 0)
                                        ]
               || FreeBSD_4_6_RELEASE ->
                    FEMPTY |++ [(FD 0, FID 0);
                                         (FD 1, FID 0);
                                         (FD 2, FID 0);
                                         (FD 3, FID 0);
                                         (FD 4, FID 0);
                                         (FD 5, FID 0);
                                         (FD 6, FID 0);
                                         (FD 7, FID 0)
                                        ]
               || WinXP_Prof_SP1 ->
                    FEMPTY;  (*: Windows FDs are not allocated in order, so
                                there's no need to specify anything here. :*)
        *)
        files := FEMPTY |+ (FID 0,
                            File(FT_Console, <| b := \x. F |>));
        socks := FEMPTY |++ (dummy_sockets 0 heldports);
        params := params
                        |>
`;
(* -------------------------------------------------- *)








val _ = export_theory();

(* End: *)
