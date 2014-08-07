(* standard prefix *)
open HolKernel boolLib Parse

open bossLib containerTheory

open HolDoc

local open
           bagTheory
	   TCP1_baseTypesTheory
           TCP1_timersTheory
           TCP1_hostTypesTheory
           TCP1_hostLTSTheory
in end;

val Term = Parse.Term;

val _ = new_theory "TCP1_net";

val _ = Version.registerTheory "$RCSfile: TCP1_netScript.sml,v $" "$Revision: 1.12 $" "$Date: 2009/02/17 11:56:46 $";


(* Network LTS *)

(*: @chapter [[net_LTS]] Network labelled transition system

  This file defines a transition system for the network.

:*)

(*: @section [[net_LTS]] TCP Network labelled transition system

  The following definitions include a type of transition labels for
  the network, and the network transition relation.

:*)

val _ = type_abbrev("msgs", ``:msg timed multiset``);

val _ = type_abbrev("hosts", ``:hostid |-> host``);

val _ = type_abbrev("net",``:hosts # msgs``);

val _ = Define `
    hosts_to_net (h1:host,h2:host) = (FEMPTY |++ [(Test,h1);(Aux,h2)])
`;



(* embed individual host thread transitions and host transitions in the network *)

(* question of what kind of visibility we want for e.g. host emitting a msg- presumably this isn't seen at the thread level, so should be invisible *)

val _ = Hol_datatype  `
(*: Net transition labels :*)
        Lnet0 =
         (* library interface *)
           Ln0_call of hostid # tid # LIB_interface                      (*[ MODE 0 ]*)  (*: invocation of LIB call, written e.g.~[[Lh_call (tid,(socket (socktype)))]] :*)
         | Ln0_return of hostid # tid # TLang                            (*[ MODE 0 ]*)  (*: return result of LIB call, written [[Lh_return (tid,v) ]] :*)

         (* connectivity changes *)
         (* REMARK interface changes are not currently incorporated into the network model *)
         | Ln0_interface of hostid # ifid # bool                         (*[ MODE 0 ]*)(*: set interface status to boolean [[up]], written [[Lh_interface (ifid,up)]] :*)

         (* miscellaneous *)
         | Ln0_tau                                              (*[ MODE 0 ]*)(*: internal transition, written [[Lh_tau]] :*)
         | Ln0_epsilon of duration                              (*[ MODE 0 ]*)(*: time passage, written [[Lh_epsilon dur]] :*)
         | Ln0_trace of tracerecord                             (*[ MODE 0 ]*)(*: TCP trace record, written [[Lh_trace tr]] :*)
`
;

(* REMARK trace records are not included in the network model *)

(* val _ = set_trace "inddef strict" 1; *)


(* REMARK in the following, @description multiline tags didn't work,
hance comments are embedded in rule *)

val _ = Hol_reln `

     (! hs hid h h' tid c msgs
        rn rp rc.

     hid NOTIN FDOM hs /\

     (rn /* rp, rc */ h -- (Lh_call(tid,c)) --=> h')

     ==>

     net_redn
     ((hs |+ (hid,h),msgs):net)
     (Ln0_call(hid,tid,c))
     (hs |+ (hid,h'),msgs)


     (*: A thread [[tid]] on host [[h]] executes a sockets call [[c]] :*)

     )

/\

     (! hs hid h h' tid msgs v
        rn rp rc.

     hid NOTIN FDOM hs /\

     (rn /* rp, rc */ h -- (Lh_return(tid,v)) --=> h')

     ==>

     net_redn
     ((hs |+ (hid,h),msgs):net)
     (Ln0_return(hid,tid,v))
     (hs |+ (hid,h'),msgs)


     (*: A thread [[tid]] on host [[h]] returns from a sockets call :*)

     )

/\

     (! hid rn rp rc h hs h' msgs msg new_msgs.

     hid NOTIN FDOM hs /\

     (rn /* rp, rc */ h -- (Lh_senddatagram msg) --=> h') /\

     (*: Zero, one, or many messages, with different lifetimes [[dur]], may be added to the network. :*)
     (! new_msg. BAG_IN new_msg new_msgs ==> ? dur. new_msg = (Timed(msg,sharp_timer dur)))

     ==>

     net_redn
     ((hs |+ (hid,h),msgs):net)
     Ln0_tau
     (hs |+ (hid,h'),BAG_UNION msgs new_msgs)


     (*: A host sends a message to the network. The message may be lost or finitely duplicated. :*)

     )

/\

     (! (hid:hostid) rn rp rc h hs d h' msgs msg.

     hid NOTIN FDOM hs /\

     timer_expires (sharp_timer d) /\

     (rn /* rp, rc */ h -- (Lh_recvdatagram msg) --=> h')

     ==>

     net_redn
     ((hs |+ (hid,h),BAG_INSERT (Timed(msg,sharp_timer d)) msgs))
     Ln0_tau
     (hs |+ (hid,h'),msgs)


     (*: A host [[h]] receives a message [[m]] from the network :*)

     )

/\

     (! hid rn rp rc h hs h' msgs msg.

     hid NOTIN FDOM hs /\

     (rn /* rp, rc */ h -- (Lh_loopdatagram msg) --=> h')

     ==>

     net_redn
     ((hs |+ (hid,h),msgs):net)
     Ln0_tau
     (hs |+ (hid,h'),msgs)


     (*: A host [[h]] receives a message [[m]] on loopback.:*)

     (* REMARK timing consideration for loopback are not taken into
     account here or elsewhere *)

     )

/\

     (! hid rn rp rc h hs h' msgs
       ifid up.

     hid NOTIN FDOM hs /\

     (rn /* rp, rc */ h -- (Lh_interface (ifid,up)) --=> h')

     ==>

     net_redn
     ((hs |+ (hid,h),msgs):net)
     (Ln0_interface (hid,ifid,up))
     (hs |+ (hid,h'),msgs)


     (*: Network interface change :*)

     )

/\

     (! hid rn rp rc h hs h' msgs.

     hid NOTIN FDOM hs /\

     (rn /* rp, rc */ h -- Lh_tau --=> h')

     ==>

     net_redn
     ((hs |+ (hid,h),msgs):net)
     Ln0_tau
     (hs |+ (hid,h'),msgs)


     (*: Allow a host to do a [[Lh_tau]] transition :*)

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

     net_redn
     ((hs,msgs):net)
     (Ln0_epsilon dur)
     (hs',msgs')


     (*: Allow time to pass for hosts and messages :*)

     )

/\

     (! hid rn rp rc h hs h' msgs tr.

     hid NOTIN FDOM hs /\

     (rn /* rp, rc */ h -- (Lh_trace tr) --=> h')

     ==>

     net_redn
     ((hs |+ (hid,h),msgs):net)
     (Ln0_trace tr)
     (hs |+ (hid,h'),msgs)


     (*: Trace records :*)

     )

`;

(* REMARK the above transitions do not include message loss *)


val _ = export_theory();

