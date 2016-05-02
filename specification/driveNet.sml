(* drive a sample network trace through the net transitions *)

open HolKernel boolLib Parse bossLib

open HolDoc

local open
	   TCP1_net1_to_netTheory (* FIXME temporary dependency to allow sharing of host and net types, which should probably be put in a shared file *)
	   TCP1_evalSupportTheory (* FIXME temp to get initial hosts *)
in end;

val Term = Parse.Term;

val _ = new_theory "driveNet";

(*
val dep_tokens = fn s =>
		    let
		       val delim = fn c => c = #" "
		   in
			String.tokens delim s
		    end;

val loadDeps = fn s => app (load o (implode o rev o tl o tl o tl o rev o explode)) (tl (dep_tokens s));

loadDeps "driveNet.uo: /local/scratch/tjr22/hol98/sigobj/bossLib.ui Version.ui TCP1_net1_to_netTheory.ui HolDoc.ui /local/scratch/tjr22/hol98/sigobj/Parse.ui /local/scratch/tjr22/hol98/sigobj/HolKernel.ui /local/scratch/tjr22/hol98/sigobj/boolLib.ui TCP1_evalSupportTheory.ui";

*)

(* hosts *)

(*

val _  = new_constant("bill",``:hostid``);
val _  = new_constant("ben",``:hostid``);

(* bill's lbls *)

val bill_lbls = [
    ``
	     Lh_call(TID 27715, socket(SOCK_STREAM))
``,

``Lh_epsilon(duration 0 099265)``,

(* Conflate Index: 1 *)
(** 1137153826.834713 "ns1" **)
(* Merge Index: 2 *)
``
Lh_return(TID 27715, OK(FD 7))
``,

``Lh_epsilon(duration 0 001314)``,

(* Conflate Index: 2 *)
(** 1137153826.836027 "ns2" **)
(* Merge Index: 4 *)
``
Lh_call(TID 27715, setsockbopt(FD 7, SO_REUSEADDR, T))
``

];

val blbl = fn n => List.nth(bill_lbls,n);


(* initial host, hosts *)

val b0 =   ``
initial_host (IP 192 168 13 104) (TID 27715) (Linux_2_4_20_8) F [] [(ETH 0, <| ipset := {IP 192 168 13 104}; primary := IP 192 168 13 104; netmask := NETMASK 8; up := T |>); (LO, <| ipset := {IP 127 0 0 1}; primary := IP 127 0 0 1; netmask:= NETMASK 24; up := T |>)] [<| destination_ip := IP 127 0 0 1; destination_netmask := NETMASK 24; ifid := LO |>; <| destination_ip := IP 192 168 13 0; destination_netmask := NETMASK 24; ifid := ETH 0 |>] [0;1;2;3;4;5;6;1000] initial_ticker_count initial_ticker_remdr <| min_eph_port := 1024; max_eph_port := 4999 |>
``;

val bs = [
    b0,
    b0 (* FIXME *)
];

val b = fn n => List.nth(bs,n);

(* host transitions *)

g `host_redn0 socket_1 rp_tcp rc ^(b 0) ^(blbl 0) ^(b 1)`;



(* net lbls *)

val lbls = [
    ``Ln1_host (bill,
	     Lh_call(TID 27715, socket(SOCK_STREAM))
)``,

``Ln1_epsilon(duration 0 099265)``,

(* Conflate Index: 1 *)
(** 1137153826.834713 "ns1" **)
(* Merge Index: 2 *)
``Ln1_host (bill,
Lh_return(TID 27715, OK(FD 7))
)``,

``Ln1_epsilon(duration 0 001314)``,

(* Conflate Index: 2 *)
(** 1137153826.836027 "ns2" **)
(* Merge Index: 4 *)
``Ln1_host (bill,
Lh_call(TID 27715, setsockbopt(FD 7, SO_REUSEADDR, T))
)``

];

val t = fn n => List.nth(lbls,n);

*)

val _ = export_theory();
