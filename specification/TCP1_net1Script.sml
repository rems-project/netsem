(* standard prefix *)
open HolKernel boolLib Parse bossLib

open HolDoc

local open bagTheory

           TCP1_baseTypesTheory
           TCP1_timersTheory
           TCP1_hostTypesTheory
           TCP1_hostLTSTheory
	   TCP1_netTheory
in end;

val Term = Parse.Term;

val _ = new_theory "TCP1_net1";

(* Network LTS *)

(*: @chapter [[net_LTS]] Detailed network LTS

  This file describes a straightforward embedding of the host LTS into a network. The relation
  defined in this file is refined in TCP1\_net.

:*)

(*: @section [[net_LTS]] TCP Detailed network LTS

  Network transition labels are defined, which are essentially located host transition labels. Then
  the network transition relation is defined.

:*)

(*[ NEWMODE straightLH ]*)
(*[ HOL_CURRIED_ALIST
  (* disable these curried identifiers *)
  Ln_host "" 99 false false
  Ln_epsilon "" 99 false false
]*)

val _ = Hol_datatype  `
(*: Net1 transition labels :*)
        Lnet1 =
         (*: host transition labels lifted to the network :*)

         (* INVARIANT expect that Lhost0 is not [[Lh_epsilon]]: time passes for all hosts, not just
         a particular host *)

           Ln1_host of hostid # Lhost0                          (*[ MODE 0 ]*)  (*: invocation of call on host, written e.g.~[[Ln1_host (hid,c)]] :*) (*[ MODE straightLH ]*)

         (* miscellaneous *)
         | Ln1_epsilon of duration                              (*[ MODE 0 ]*)(*: time passage, written [[Ln1_epsilon dur]] :*) (*[ MODE straightLH ]*)
`
;

val _ = set_trace "inddef strict" 1;


(* REMARK in the following, @description multiline tags didn't work,
hance comments are embedded in rule *)

val _ = Hol_reln `

     (! hs hid h h' lbl msgs
        rn rp rc.

     hid NOTIN FDOM hs /\

     (*: Only handle labels [[lbl]] that do not affect the messages in the network. :*)
     (~ ? m. lbl = (Lh_senddatagram m)) /\
     (~ ? m. lbl = (Lh_recvdatagram m)) /\

     (*: Do not allow [[Lh_epsilon]] transitions for hosts. :*)
     ( ~ ? dur. lbl = (Lh_epsilon dur)) /\

     (rn /* rp, rc */ h -- lbl --=> h')

     ==>

     net1_redn
     ((hs |+ (hid,h),msgs):net)
     (Ln1_host(hid,lbl))
     (hs |+ (hid,h'),msgs)


     (*: A host [[h]] executes a non [[Lh_epsilon]] transition that does not affect the messages on
     the network. :*)

     )

/\

     (! hs hid h h' lbl msgs msg new_msgs
        rn rp rc.

     hid NOTIN FDOM hs /\

     (lbl = (Lh_senddatagram msg)) /\

     (rn /* rp, rc */ h -- lbl --=> h') /\

     (*: Zero, one, or many messages, with different lifetimes [[dur]], may be added to the network. :*)
     (! new_msg. BAG_IN new_msg new_msgs ==> ? dur. new_msg = (Timed(msg,sharp_timer dur)))

     ==>

     net1_redn
     ((hs |+ (hid,h),msgs):net)
     (Ln1_host(hid,lbl))
     (hs |+ (hid,h'),BAG_UNION msgs new_msgs)


     (*: A host sends a message to the network. The message may be lost or finitely duplicated. :*)

     )

/\

     (! hs hid h h' lbl msgs msg dur
        rn rp rc.

     hid NOTIN FDOM hs /\

     timer_expires (sharp_timer dur) /\

     (lbl = (Lh_recvdatagram msg)) /\

     (rn /* rp, rc */ h -- lbl --=> h')

     ==>

     net1_redn
     ((hs |+ (hid,h),BAG_INSERT (Timed(msg,sharp_timer dur)) msgs):net)
     (Ln1_host(hid,lbl))
     (hs |+ (hid,h'),msgs)


     (*: A host [[h]] receives a message [[m]] from the network :*)

     )

/\

     (! rn rp rc hs hs' msgs msgs' dur msgs''.

     (*: Time passes for the hosts. :*)
     FDOM hs' = FDOM hs /\
     (! h. h IN FDOM hs ==> (rn /* rp, rc */ hs ' h -- (Lh_epsilon dur) --=> hs' ' h)) /\

     (*: Time passes for the messages. :*)
     msgs'' = BAG_IMAGE (Time_Pass_timed dur) msgs /\
     ~ (BAG_IN NONE msgs'') /\
     msgs' = BAG_IMAGE THE msgs''

     ==>

     net1_redn
     ((hs,msgs):net)
     (Ln1_epsilon dur)
     (hs',msgs')


     (*: Allow time to pass for hosts and messages :*)

     )

`;

(* REMARK currently this relation does not include message loss or interface changes *)


(* REMARK the following definitions are an attempt to define what a trace of the system consists of;
they should be ignored *)

val _ = Define `
     is_initial_net (net:net) =
       (* REMARK mn pull initial hosts into hostLTS from evalSupportScript, then use defn of initialhost in the following *)
       ? initial_hosts. initial_hosts IN ARB /\
       let initial_msgs = EMPTY_BAG in
         net = (initial_hosts, initial_msgs)
`;

val _ = Define `
     (*: A trace of the system is a sequence of transitions, where the initial, i.e. [[0]], state is drawn from a set of start states. :*)
     is_net1_path (states:num->net,labels:num->Lnet1) =
       (is_initial_net (states 0) /\
       (! n. net1_redn (states n) (labels n) (states (SUC n))))
`;

val Lnet1_to_Lnet0_def = Define `
     Lnet1_to_Lnet0 (lbl1:Lnet1) = (case lbl1 of
         Ln1_host (hid,lbl0) => (case lbl0 of
              Lh_senddatagram msg => Ln0_tau
           | Lh_recvdatagram msg => Ln0_tau
           | Lh_call (tid,lib) => Ln0_call (hid,tid,lib)
           | Lh_return (tid,tlang) => Ln0_return (hid,tid,tlang)
           | Lh_loopdatagram msg => Ln0_tau
           | Lh_interface (ifid,b) => Ln0_interface (hid,ifid,b)
           | Lh_tau => Ln0_tau
           | Lh_trace tr => Ln0_trace tr
           | Lh_epsilon dur => ARB "Lnet1_to_Lnet0:1"(* Ln0_epsilon dur *)
           | _1 => ARB "Lnet1_to_Lnet0:2")
       | Ln1_epsilon dur => Ln0_epsilon dur)
`;

val _ = export_theory();

(* Local Variables: *)
(* fill-column: 100 *)
(* End: *)
