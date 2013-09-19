(* standard prefix *)
open HolKernel boolLib Parse

open bossLib containerTheory

open HolDoc

local open TCP3_hostLTSTheory
in end;

val Term = Parse.Term;

val _ = new_theory "TCP3_net";

val _ = Version.registerTheory "$RCSfile: TCP3_netScript.sml,v $" "$Revision: 1.20 $" "$Date: 2009/02/17 17:22:20 $";



(* Network LTS *)

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[net_LTS]] Network labelled transition system

This file defines the network model, using the host LTS defined previously.

:*)

(*: @section [[net_types]] ALL Basic network types

Basic network types, and transition labels.

:*)

(* Spec3 net is similar to Spec1, with the addition of network gizmos *)

val _ = type_abbrev("hosts", ``:hostid |-> host``);

val _ = type_abbrev("streams", ``:streamid |-> tcpStreams``);

val _ = type_abbrev("msgs", ``:msg multiset``);

val _ = type_abbrev("net",``:hosts # streams # msgs``);

val _ = Hol_datatype  `
    (*: net transition labels :*)
        Lnet0 =
         (* library interface *)
           Ln_call of hostid # tid # LIB_interface                      (*[ MODE 0 ]*)
         | Ln_return of hostid # tid # TLang                            (*[ MODE 0 ]*)

         (* connectivity changes *)
         | Ln_interface of hostid # ifid # bool                         (*[ MODE 0 ]*)

         (* miscellaneous *)
         | Ln_tau                                              (*[ MODE 0 ]*)
         | Ln_epsilon of duration                              (*[ MODE 0 ]*)
`
;

val _ = Hol_datatype  `
    (*: net transition rule names :*)
    rn = call | return | tau | interface | host_tau | time_pass | trace
`;



(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[net_LTS]] ALL Network labelled transition system

:*)

val _ = add_rule { block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   fixity = Infix(NONASSOC, 420),
                   pp_elements = [HardSpace 1, TOK "/**/", HardSpace 1,
                                  TM (* host0 *), HardSpace 1,
				  TOK "--", HardSpace 1,
                                  TM (* label *), HardSpace 1,
				  TOK "--->", HardSpace 1],
                   term_name = "net_redn1"
                   };


val Net_reln = let open Net_Hol_reln in Net_Hol_reln end;

val _ = Net_reln `

(! hs hid h h' tid c
    rn rp rc
    S S' M M'.

    call /**/ ((hs |+ (hid,h),S,M):net)
    -- (Ln_call(hid,tid,c)) --->
    (hs |+ (hid,h'),S',M')

    <==

    (rn /* rp, rc */ (h,S,M) -- (Lh_call(tid,c)) --> (h',S',M'))


    (*: @description

    A thread [[tid]] on host [[h]] executes a sockets call [[c]] which
    does not sync with the streams.

    :*)

)

/\

(! hs hid h h' tid v
    rn rp rc
    S S' M M'.

    return /**/ ((hs |+ (hid,h),S,M):net)
    -- (Ln_return(hid,tid,v)) --->
    (hs |+ (hid,h'),S',M')

    <==

    (rn /* rp, rc */ (h,S,M) -- (Lh_return(tid,v)) --> (h',S',M'))


    (*: @description

    A thread [[tid]] on host [[h]] returns from a sockets call.

    :*)

)

/\

(! hs S M.

    tau /**/ ((hs,S,M):net)
    -- (Ln_tau) --->
    (hs,S,M)

    <==

    T


    (*: @description

    This tau action at the network level corresponds to the hosts
    doing a [[Lh_senddatagram msg]] or a [[Lh_recvdatagram msg]] transition.

    :*)


)

/\

(! hid rn rp rc h hs h'
    ifid up
    S S' M M'.

    interface /**/ ((hs |+ (hid,h),S,M):net)
    -- (Ln_interface (hid,ifid,up)) --->
    (hs |+ (hid,h'),S',M')

    <==

    (rn /* rp, rc */ (h,S,M) -- (Lh_interface(ifid,up)) --> (h',S',M'))


    (*: @description

    Network interface change.

    :*)

)

/\

(! hid rn rp rc h hs h'
    S S' M M'.

    host_tau /**/ ((hs |+ (hid,h),S,M):net)
    -- Ln_tau --->
    (hs |+ (hid,h'),S',M')

    <==

    (rn /* rp, rc */ (h,S,M) -- Lh_tau --> (h',S',M'))


    (*: @description

    Allow a host to do a [[Lh_tau]] transition.

    :*)

)

/\

(! hs hs' hs'' dur
    S M.

    time_pass /**/ ((hs,S,M):net)
    -- (Ln_epsilon dur) --->
    (hs'',S,M)

    <==

    (! h. h IN FRANGE hs ==> ~(?rn rp rc lbl h' S' M'.
            (rn /* rp, rc */ (h,S,M) -- lbl --> (h',S',M')) /\ is_urgent rc)) /\

    (*: Time passes for the hosts. :*)
    hs' = (Time_Pass_host dur) o_f hs /\
    ~ (NONE IN FRANGE hs') /\

    FDOM hs'' = FDOM hs /\
    (! hid. hid IN FDOM hs ==> hs'' ' hid IN (THE (hs' ' hid)))


    (*: @description

    Allow time to pass for hosts. The check [[~ (NONE IN FRANGE hs')]]
    ensures that time actually can pass for a host, i.e. that there
    are no urgent events that need to happen.

    :*)

)

/\

(! hid rn rp rc h hs h' tr S M S' M'.

     trace /**/ ((hs |+ (hid,h),S,M):net)
     -- (Ln_tau) --->
     (hs |+ (hid,h'),S',M')

     <==

     hid NOTIN FDOM hs /\

     (rn /* rp, rc */ (h,S,M) -- (Lh_trace tr) --> (h',S',M'))



     (*: @description

     Trace records give [[Ln_tau]] transitions at the network level.

     :*)

)

`;

(* tjr 2009-02-16 the following is a direct copy of the above, with
rule names ommitted; the slight exception is the <== T clause which is
commented below; I believe the following is the version of the
relation used by the checker, but am not sure (look at changes
committed today to check-sketch.sml)

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[net_LTS]] ALL Network labelled transition system

The same as above, but this time we omit the rule names, because the
check-sketch has not been updated to handle transitions with
names. Also alter the Ln_tau rule so no T precondition so that
check-sketch can find it. This all needs to be done properly-
absfun needs to output named transitions, and so Spec1 network
transitions need to be named.

@norender

:*)

val _ = add_rule { block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   fixity = Infix(NONASSOC, 420),
                   pp_elements = [HardSpace 1,
				  TOK "--", HardSpace 1,
                                  TM (* label *), HardSpace 1,
				  TOK "--->", HardSpace 1],
                   term_name = "net_redn"
                   };


val Net_reln = let open Net_Hol_reln in Net_Hol_reln end;

val _ = Net_reln `

(! hs hid h h' tid c
    rn rp rc
    S S' M M'.

    ((hs |+ (hid,h),S,M):net)
    -- (Ln_call(hid,tid,c)) --->
    (hs |+ (hid,h'),S',M')

    <==

    (rn /* rp, rc */ (h,S,M) -- (Lh_call(tid,c)) --> (h',S',M'))


    (*: @description

    A thread [[tid]] on host [[h]] executes a sockets call [[c]] which
    does not sync with the streams.

    :*)

)

/\

(! hs hid h h' tid v
    rn rp rc
    S S' M M'.

    ((hs |+ (hid,h),S,M):net)
    -- (Ln_return(hid,tid,v)) --->
    (hs |+ (hid,h'),S',M')

    <==

    (rn /* rp, rc */ (h,S,M) -- (Lh_return(tid,v)) --> (h',S',M'))


    (*: @description

    A thread [[tid]] on host [[h]] returns from a sockets call.

    :*)

)

/\

(! hs S M.

    ((hs,S,M):net)
    -- (Ln_tau) --->
    (hs,S,M)

(*    <==

    T *)


    (*: @description

    This tau action at the network level corresponds to the hosts
    doing a [[Lh_senddatagram msg]] or a [[Lh_recvdatagram msg]] transition.

    :*)


)

/\

(! hid rn rp rc h hs h'
    ifid up
    S S' M M'.

    ((hs |+ (hid,h),S,M):net)
    -- (Ln_interface (hid,ifid,up)) --->
    (hs |+ (hid,h'),S',M')

    <==

    (rn /* rp, rc */ (h,S,M) -- (Lh_interface(ifid,up)) --> (h',S',M'))


    (*: @description

    Network interface change.

    :*)

)

/\

(! hid rn rp rc h hs h'
    S S' M M'.

    ((hs |+ (hid,h),S,M):net)
    -- Ln_tau --->
    (hs |+ (hid,h'),S',M')

    <==

    (rn /* rp, rc */ (h,S,M) -- Lh_tau --> (h',S',M'))


    (*: @description

    Allow a host to do a [[Lh_tau]] transition.

    :*)

)

/\

(! hs hs' hs'' dur
    S M.

    ((hs,S,M):net)
    -- (Ln_epsilon dur) --->
    (hs'',S,M)

    <==

    (! h. h IN FRANGE hs ==> ~(?rn rp rc lbl h' S' M'.
            (rn /* rp, rc */ (h,S,M) -- lbl --> (h',S',M')) /\ is_urgent rc)) /\

    (*: Time passes for the hosts. :*)
    hs' = (Time_Pass_host dur) o_f hs /\
    ~ (NONE IN FRANGE hs') /\

    FDOM hs'' = FDOM hs /\
    (! hid. hid IN FDOM hs ==> hs'' ' hid IN (THE (hs' ' hid)))


    (*: @description

    Allow time to pass for hosts. The check [[~ (NONE IN FRANGE hs')]]
    ensures that time actually can pass for a host, i.e. that there
    are no urgent events that need to happen.

    :*)

)

/\

(! hid rn rp rc h hs h' tr S M S' M'.

     ((hs |+ (hid,h),S,M):net)
     -- (Ln_tau) --->
     (hs |+ (hid,h'),S',M')

     <==

     hid NOTIN FDOM hs /\

     (rn /* rp, rc */ (h,S,M) -- (Lh_trace tr) --> (h',S',M'))



     (*: @description

     Trace records give [[Ln_tau]] transitions at the network level.

     :*)

)

`;

*)

val _ = export_theory();

(* Local Variables: *)
(* fill-column: 100 *)
(* End: *)
