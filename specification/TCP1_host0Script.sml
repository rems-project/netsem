(* A HOL98 specification of TCP *)

(* Transition labels, rule names, rule categories, and other support
   for the host specification LTS *)

(*[ RCSID "$Id: TCP1_host0Script.sml,v 1.98 2006/10/04 10:23:17 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

local open TCP1_baseTypesTheory
           TCP1_utilsTheory
           TCP1_LIBinterfaceTheory
           TCP1_netTypesTheory
           TCP1_hostTypesTheory  (* needed for trace labels, annoyingly *)
in end;

val _ = new_theory "TCP1_host0";

val _ = Version.registerTheory "$RCSfile: TCP1_host0Script.sml,v $" "$Revision: 1.98 $" "$Date: 2006/10/04 10:23:17 $";

(*: @chapter [[TCP1_host0]] Host LTS labels and rule categories

This file defines the labels for the host labelled transition system,
characterising the possible interactions between a host and its environment.
It also defines various categories for the host LTS rules.

:*)


(* -------------------------------------------------- *)
(*               OPERATION CLASSES                    *)
(* -------------------------------------------------- *)

(* commented out for now...

val OP_def =
  Define`OP fd opn =
           (?is ps. opn = bind(fd, is, ps)) \/
           (?i ps. opn = connect(fd, i, ps)) \/
           (opn = disconnect fd) \/
           (opn = getsockname fd) \/
           (opn = getpeername fd) \/
           (opn = geterr fd) \/
           (?opt. opn = getsockopt(fd, opt)) \/
           (?opt b. opn = setsockopt(fd, opt, b)) \/
           (?v data nb. opn = sendto(fd, v, data, nb)) \/
           (?nb. opn = recvfrom(fd, nb)) \/
           (opn = close fd)`;

val OP2_def =
  Define`OP2 fd ts =
           (?junk. ts = Sendto2(fd, junk)) \/
           (ts = Recvfrom2 fd)`;

...end commented out section *)


(* -------------------------------------------------- *)
(*               TRANSITION LABELS                    *)
(* -------------------------------------------------- *)

(*: @section [[host0_labels]] ALL Transition labels

Host transition labels.
:*)

(*[ NEWMODE straightLH ]*)
(*[ HOL_CURRIED_ALIST
  (* disable these curried identifiers *)
  Lh_call "" 99 false false
  Lh_return "" 99 false false
  Lh_senddatagram "" 99 false false
  Lh_recvdatagram "" 99 false false
  Lh_loopdatagram "" 99 false false
  Lh_interface "" 99 false false
  Lh_epsilon "" 99 false false
  Lh_trace "" 99 false false
]*)
val _ = Hol_datatype
  `
(*: Host transition labels :*)
        Lhost0 =
         (* library interface *)
           Lh_call of tid # LIB_interface                      (*[ MODE 0 ]*)  (*: invocation of LIB call, written e.g.~[[Lh_call (tid,(socket (socktype)))]] :*) (*[ MODE straightLH ]*)
         | Lh_return of tid # TLang                            (*[ MODE 0 ]*)  (*: return result of LIB call, written [[Lh_return (tid,v) ]] :*) (*[ MODE straightLH ]*)

         (* message transmission and receipt *)
         | Lh_senddatagram of msg                              (*[ MODE 0 ]*) (*: output of message to the network, written [[Lh_senddatagram msg]] :*) (*[ MODE straightLH ]*)
         | Lh_recvdatagram of msg                              (*[ MODE 0 ]*)(*: input of message from the network, written [[Lh_recvdatagram msg]]  :*) (*[ MODE straightLH ]*)
         | Lh_loopdatagram of msg                              (*[ MODE 0 ]*) (*: loopback output/input, written [[Lh_loopdatagram msg]] :*) (*[ MODE straightLH ]*)

         (* connectivity changes *)
         | Lh_interface of ifid # bool                         (*[ MODE 0 ]*)(*: set interface status to boolean [[up]], written [[Lh_interface (ifid,up)]] :*) (*[ MODE straightLH ]*)

         (* miscellaneous *)
         | Lh_tau                                              (*[ MODE 0 ]*)(*: internal transition, written [[Lh_tau]] :*) (*[ MODE straightLH ]*)
         | Lh_epsilon of duration                              (*[ MODE 0 ]*)(*: time passage, written [[Lh_epsilon dur]] :*) (*[ MODE straightLH ]*)
         | Lh_trace of tracerecord                             (*[ MODE 0 ]*)(*: TCP trace record, written [[Lh_trace tr]] :*) (*[ MODE straightLH ]*)
`
;

(*
         | Lh_exit                                            (* out *)
         | Lh_console of string                               (* out *)
*)

(*[ MODE 0 ]*)


(* -------------------------------------------------- *)
(*               RULE CATEGORIES                      *)
(* -------------------------------------------------- *)

(* moved to TCP1_preHostTypes *)

(* -------------------------------------------------- *)

val _ = export_theory();

