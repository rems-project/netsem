(* standard prefix *)

open HolKernel boolLib Parse bossLib

open HolDoc

local open
        listTheory
	TCP1_net1Theory
	TCP1_netTheory
in end;

val Term = Parse.Term;

val _ = new_theory "TCP1_net1_to_net";

(*: @chapter [[net_LTS]] Net LTS: detailed network semantics for Spec1

  This file no longer used. It contained some preliminary proofs about the network transition
  relation.

:*)

(*: @section [[net_LTS]] TCP Net LTS

  This file no longer used.

:*)


(* fn to take 2 (or n?) host traces to 1 detailed net trace *)

(* idea: take a host and a net trace and combine into a net trace


*)

(* need concept of finite trace- a list *)

(* a finite trace that starts in a given state *)
val is_fin_trace'_def = Define `
     is_fin_trace' s0 [] = T
     /\ is_fin_trace' s0 (CONS x xs) =
       let (s,lbl,s') = x in
         (s = s0)
         /\ is_fin_trace' s' xs
`;

val is_fin_trace_def = Define `
     is_fin_trace t = case t of
          [] -> T
       || CONS x xs -> let (s,lbl,s') = x in is_fin_trace' s t
`;
(*
val is_fin_host_trace_def = Define `
     is_fin_host_trace t =
       (is_fin_trace t
       /\ (EVERY (\(s,lbl,s'). ? rn rp rc. rn /* rp, rc */ s -- lbl --=> s') t))
`;

val _ = type_abbrev("fin_host_trace", ``:(host # Lhost0 # host) list``);

val host_traces_to_net1_trace'_def = Define `
     host_traces_to_net1_trace' (t1:real) (tr1:fin_host_trace) (t2:real) (tr2:fin_host_trace) 0 = []
     /\ host_traces_to_net1_trace' (t1:real) (tr1:fin_host_trace) (t2:real) (tr2:fin_host_trace) (SUC n) = (
       let (h1,lbl1) = tr1 in
       let (h2,lbl2) = tr2 in
         case lbl1 0 of
              Lh_epsilon dur -> ( let t1 = t1+dur in
                                  let tr1 = trace_tail tr1 in
                                    host_traces_to_net1_trace' t1 tr1 t2 tr2 n)
           || _ -> case lbl2 0 of
                Lh_epsilon dur -> ( let t2 = t2+dur in
                                    let tr2 = trace_tail tr2 in
                                     host_traces_to_net1_trace t1 tr1 t2 tr2)
             || _ -> if t1 < t2 then let (n,lbl) = host_traces_to_net1_trace t1 (trace_tail tr1) t2 tr2 in
                               trace_cons (host_to_net1 (h1 (0:num)), host_lbl_to_net1_lbl (lbl1 0)) (n,lbl)
                             else let (n,lbl) = host_traces_to_net1_trace t1 tr1 t2 (trace_tail tr2) in
                               trace_cons (host_to_net1 (h2 0), host_lbl_to_net1_lbl (lbl2 0)) (n,lbl))
`;




(* ******************************************************************************** *)
(* infinite trace stuff here *)

val is_host_trace_def = Define `
     is_host_trace t = let (h,lbl) = t in ! n. ? rn rp rc. rn /* rp, rc */ (h n) -- (lbl n) --=> (h (SUC n))
`;

(* fn to take 2 host traces and combine into 1 net1 trace *)

val trace_tail_def = Define `
     trace_tail (h,lbl) =
       let h = \n. h (SUC n) in
       let lbl = \n. lbl(SUC n) in
         (h,lbl)
`;

val _ = Define `
     trace_cons (n0,lbl0) (n,lbl) =
       let n = \x. case x of 0 -> n0 || SUC x -> n x in
       let lbl = \ x. case x of 0 -> lbl0 || SUC x -> lbl x in
         (n,lbl)
`;

val _ = type_abbrev("host_trace", ``:(num -> host) # (num -> Lhost0)``);
val _ = type_abbrev("net1_trace", ``:(num -> net) # (num -> Lnet1)``); (* FIXME move to net1 *)

val _ = Define `
     host_to_net1 (h:host) = (ARB:net)
`;

val _ = Define `
     host_lbl_to_net1_lbl (lbl:Lhost0) = (ARB:Lnet1)
`;

val _ = Define `
     host_traces_to_net1_trace (t1:real) (tr1:host_trace) (t2:real) (tr2:host_trace) = ARB:net1_trace
`;
*)
(*
g `
     ! t1 tr1 t2 tr2. (host_traces_to_net1_trace (t1:real) (tr1:host_trace) (t2:real) (tr2:host_trace)):net1_trace = (
       let (h1,lbl1) = tr1 in
       let (h2,lbl2) = tr2 in
         case lbl1 0 of
              Lh_epsilon dur -> (let t1 = t1+dur in
                                let tr1 = trace_tail tr1 in
                                  host_traces_to_net1_trace t1 tr1 t2 tr2)
           || _ -> case lbl2 0 of
                Lh_epsilon dur -> (let t2 = t2+dur in
                                  let tr2 = trace_tail tr2 in
                                     host_traces_to_net1_trace t1 tr1 t2 tr2)
             || _ -> if t1 < t2 then let (n,lbl) = host_traces_to_net1_trace t1 (trace_tail tr1) t2 tr2 in
                               trace_cons (host_to_net1 (h1 (0:num)), host_lbl_to_net1_lbl (lbl1 0)) (n,lbl)
                             else let (n,lbl) = host_traces_to_net1_trace t1 tr1 t2 (trace_tail tr2) in
                               trace_cons (host_to_net1 (h2 0), host_lbl_to_net1_lbl (lbl2 0)) (n,lbl))
`;
e(FV_TAC);
e(CHEAT_TAC);
val host_traces_to_net1_trace_def = pg_top_thm_and_drop();

host_traces_to_net1_trace_def;

(* stripping an epsilon preserves is_host_trace *)

g `
! h lbl. is_host_trace (h,lbl)
==> (? dur. lbl 0 = Lh_epsilon dur)
==> is_host_trace (trace_tail (h,lbl))
`;
e(FV_TAC);
e(intros);
e(elims);
e(FULL_SIMP_TAC std_ss [is_host_trace_def, LET_THM]);
e(FULL_SIMP_TAC std_ss [trace_tail_def, LET_THM]);
val drop_epsilon_from_host_trace = pg_top_thm_and_drop();

g `
is_host_trace (h1,lbl1)
==> is_host_trace (h2,lbl2)
==> msg_assumption t1 (h1,lbl1) t2 (h2,lbl2)
==> is_net1_path (host_traces_to_net1_trace t1 (h1,lbl1) t2 (h2,lbl2)) (* FIXME is_net1_trace *)
`;
e(FV_TAC);
e(intros);
e(QCUT_TAC `(? dur. lbl1 0 = Lh_epsilon dur) \/ ~ (? dur. lbl1 0 = Lh_epsilon dur) `);
e(mesonLib.ASM_MESON_TAC[]);
dl();

(* ? dur. lbl1 0 = epsilon dur *)
e(elims);
e(Cases_on `lbl1 0`);

(* lbl1 0 = Lh_call *)
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_distinct"]);

(* Lh_return *)
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_distinct"]);

(* ... *)
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_distinct"]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_distinct"]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_distinct"]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_distinct"]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_distinct"]);

(* the real goal *)
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_11"]);
e(ASSUME_TAC host_traces_to_net1_trace_def);
al ``t1:real``;
al ``(h1,lbl1):host_trace``;
al ``t2:real``;
al ``(h2,lbl2):host_trace``;
e(ASM_SIMP_TAC std_ss []); (* FIXME surely simp takes quantified formulae? *)
e(ASM_SIMP_TAC std_ss [LET_THM]); (* FIXME surely simp takes quantified formulae? *)
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_case_def"]);
(* part of the induction? need that stripping an epsilon and increasing the time results in a good host trace *)











(* ******************************************************************************** *)

(* net1 to net projection stuff here *)

FIXME definition net1_to_net_Lnet1_def moved (and probably renamed) to TCP1_net1Script.

g `
! hs msgs netlbl1 hs' msgs'.
(net1_redn (hs,msgs) netlbl1 (hs',msgs'))
==> (net_redn (hs,msgs) (net1_to_net_Lnet1 netlbl1) (hs',msgs'))
`;
(* check freevars of goal *)
e(FV_TAC);
e(intros);

(* case Ln1_host *)
(* use TCP1_net1.net1_redn_cases *)
e(ASSUME_TAC (fetch "TCP1_net1" "net1_redn_cases"));
al ``(hs,msgs):net``;
al ``netlbl1:Lnet1``;
al ``(hs',msgs'):net``;
eql();
e(THIN_TAC ``
 (?hs'' hid h h' lbl msgs'' rn rp rc.
             (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ netlbl1 = Ln1_host (hid,lbl) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
             ~(?m. lbl = Lh_senddatagram m) /\ ~(?m. lbl = Lh_recvdatagram m) /\ ~(?dur. lbl = Lh_epsilon dur) /\ rn /* rp, rc */ h -- lbl --=> h') \/
          (?hs'' hid h h' lbl msgs'' msg new_msgs rn rp rc.
             (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ netlbl1 = Ln1_host (hid,lbl) /\ (hs',msgs') = (hs'' |+ (hid,h'),BAG_UNION msgs'' new_msgs) /\
             hid NOTIN FDOM hs'' /\ lbl = Lh_senddatagram msg /\ rn /* rp, rc */ h -- lbl --=> h' /\
             !new_msg. BAG_IN new_msg new_msgs ==> ?dur. new_msg = Timed (msg,sharp_timer dur)) \/
          (?hs'' hid h h' lbl msgs'' msg dur rn rp rc.
             (hs,msgs) = (hs'' |+ (hid,h),BAG_INSERT (Timed (msg,sharp_timer dur)) msgs'') /\ netlbl1 = Ln1_host (hid,lbl) /\
             (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\ timer_expires (sharp_timer dur) /\ lbl = Lh_recvdatagram msg /\
             rn /* rp, rc */ h -- lbl --=> h') \/
          (?rn rp rc hs'' hs''' msgs'' msgs''' dur msgs''''.
             (hs,msgs) = (hs'',msgs'') /\ netlbl1 = Ln1_epsilon dur /\ (hs',msgs') = (hs''',msgs''') /\ FDOM hs''' = FDOM hs'' /\
             (!h. h IN FDOM hs'' ==> rn /* rp, rc */ hs'' ' h -- Lh_epsilon dur --=> hs''' ' h) /\ msgs'''' = BAG_IMAGE (Time_Pass_timed dur) msgs'' /\
             ~BAG_IN NONE msgs'''' /\ msgs''' = BAG_IMAGE THE msgs'''') ==>
          net1_redn (hs,msgs) netlbl1 (hs',msgs')
``);
il 1; ii();
dl();

(* clause 1 of net1_redn, not send or receive *)
e(elims);
(* case split on lbl *)
e(Cases_on `lbl`);

(* Lh_call *)
e(SIMP_TAC std_ss [net1_to_net_Lnet1_def]);
e(FULL_SIMP_TAC std_ss []);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_net1" "Lnet1_case_def"]);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_case_def"]);
e(QCUT_TAC `? tid lib. p = (tid,lib)`); e(Q.EXISTS_TAC `FST p`); e(Q.EXISTS_TAC `SND p`); e(FULL_SIMP_TAC std_ss []);
e(elims);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
(* use clause 1 of net_redn *)
e(ASSUME_TAC (fetch "TCP1_net" "net_redn_cases"));
al ``(hs,msgs):net``;
al ``Ln0_call (hid,tid,lib)``;
al ``(hs',msgs'):net``;
eql();
e(THIN_TAC ``
 net_redn (hs,msgs) (Ln0_call (hid,tid,lib)) (hs',msgs') ==>
           (?hs'' hid' h h' tid' c msgs'' rn rp rc.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_call (hid,tid,lib) = Ln0_call (hid',tid',c) /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_call (tid',c) --=> h') \/
           (?hs'' hid' h h' tid' msgs'' v rn rp rc.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_call (hid,tid,lib) = Ln0_return (hid',tid',v) /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_return (tid',v) --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs'' msg new_msgs.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_call (hid,tid,lib) = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid',h'),BAG_UNION msgs'' new_msgs) /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_senddatagram msg --=> h' /\
              !new_msg. BAG_IN new_msg new_msgs ==> ?dur. new_msg = Timed (msg,sharp_timer dur)) \/
           (?hid' rn rp rc h hs'' d h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid',h),BAG_INSERT (Timed (msg,sharp_timer d)) msgs'') /\ Ln0_call (hid,tid,lib) = Ln0_tau /\
              (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\ hid' NOTIN FDOM hs'' /\ timer_expires (sharp_timer d) /\
              rn /* rp, rc */ h -- Lh_recvdatagram msg --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_call (hid,tid,lib) = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\ hid' NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_loopdatagram msg --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs'' ifid up.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_call (hid,tid,lib) = Ln0_interface (hid',ifid,up) /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_interface (ifid,up) --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs''.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_call (hid,tid,lib) = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\ hid' NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_tau --=> h') \/
           (?rn rp rc hs'' hs''' msgs'' msgs''' dur msgs''''.
              (hs,msgs) = (hs'',msgs'') /\ Ln0_call (hid,tid,lib) = Ln0_epsilon dur /\ (hs',msgs') = (hs''',msgs''') /\ FDOM hs''' = FDOM hs'' /\
              (!h. h IN FDOM hs'' ==> rn /* rp, rc */ hs'' ' h -- Lh_epsilon dur --=> hs''' ' h) /\ msgs'''' = BAG_IMAGE (Time_Pass_timed dur) msgs'' /\
              ~BAG_IN NONE msgs'''' /\ msgs''' = BAG_IMAGE THE msgs'''') \/
           ?hid' rn rp rc h hs'' h' msgs'' tr.
             (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_call (hid,tid,lib) = Ln0_trace tr /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\ hid' NOTIN FDOM hs'' /\
             rn /* rp, rc */ h -- Lh_trace tr --=> h'
``);
il 12;
e(FULL_SIMP_TAC std_ss []);
(* to avoid repeated dr2 *)
e(QCUT_TAC `
    (?hs''' hid' h'' h''' tid' c rn' rp' rc'.
       hs'' |+ (hid,h) = hs''' |+ (hid',h'') /\ Ln0_call (hid,tid,lib) = Ln0_call (hid',tid',c) /\ hs'' |+ (hid,h') = hs''' |+ (hid',h''') /\
       hid' NOTIN FDOM hs''' /\ rn' /* rp', rc' */ h'' -- Lh_call (tid',c) --=> h''')
`);
e(Q.EXISTS_TAC `hs''`);
e(Q.EXISTS_TAC `hid`);
e(Q.EXISTS_TAC `h`);
e(Q.EXISTS_TAC `h'`);
e(Q.EXISTS_TAC `tid`);
e(Q.EXISTS_TAC `lib`);
e(Q.EXISTS_TAC `rn`);
e(Q.EXISTS_TAC `rp`);
e(Q.EXISTS_TAC `rc`);
e((REPEAT CONJR_TAC) THEN (FULL_SIMP_TAC std_ss []));

e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);

(* Lh_return *)
e(SIMP_TAC std_ss [net1_to_net_Lnet1_def]);
e(FULL_SIMP_TAC std_ss []);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_net1" "Lnet1_case_def"]);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_case_def"]);
e(QCUT_TAC `? tid tlang. p = (tid,tlang)`); e(Q.EXISTS_TAC `FST p`); e(Q.EXISTS_TAC `SND p`); e(FULL_SIMP_TAC std_ss []);
e(elims);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
(* use clause 1 of net_redn *)
e(ASSUME_TAC (fetch "TCP1_net" "net_redn_cases"));
al ``(hs,msgs):net``;
al ``Ln0_return (hid,tid,tlang)``;
al ``(hs',msgs'):net``;
eql();
e(THIN_TAC ``
  net_redn (hs,msgs) (Ln0_return (hid,tid,tlang)) (hs',msgs') ==>
           (?hs'' hid' h h' tid' c msgs'' rn rp rc.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_return (hid,tid,tlang) = Ln0_call (hid',tid',c) /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_call (tid',c) --=> h') \/
           (?hs'' hid' h h' tid' msgs'' v rn rp rc.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_return (hid,tid,tlang) = Ln0_return (hid',tid',v) /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_return (tid',v) --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs'' msg new_msgs.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_return (hid,tid,tlang) = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid',h'),BAG_UNION msgs'' new_msgs) /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_senddatagram msg --=> h' /\
              !new_msg. BAG_IN new_msg new_msgs ==> ?dur. new_msg = Timed (msg,sharp_timer dur)) \/
           (?hid' rn rp rc h hs'' d h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid',h),BAG_INSERT (Timed (msg,sharp_timer d)) msgs'') /\ Ln0_return (hid,tid,tlang) = Ln0_tau /\
              (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\ hid' NOTIN FDOM hs'' /\ timer_expires (sharp_timer d) /\
              rn /* rp, rc */ h -- Lh_recvdatagram msg --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_return (hid,tid,tlang) = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\ hid' NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_loopdatagram msg --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs'' ifid up.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_return (hid,tid,tlang) = Ln0_interface (hid',ifid,up) /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_interface (ifid,up) --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs''.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_return (hid,tid,tlang) = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\ hid' NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_tau --=> h') \/
           (?rn rp rc hs'' hs''' msgs'' msgs''' dur msgs''''.
              (hs,msgs) = (hs'',msgs'') /\ Ln0_return (hid,tid,tlang) = Ln0_epsilon dur /\ (hs',msgs') = (hs''',msgs''') /\ FDOM hs''' = FDOM hs'' /\
              (!h. h IN FDOM hs'' ==> rn /* rp, rc */ hs'' ' h -- Lh_epsilon dur --=> hs''' ' h) /\ msgs'''' = BAG_IMAGE (Time_Pass_timed dur) msgs'' /\
              ~BAG_IN NONE msgs'''' /\ msgs''' = BAG_IMAGE THE msgs'''') \/
           ?hid' rn rp rc h hs'' h' msgs'' tr.
             (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_return (hid,tid,tlang) = Ln0_trace tr /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
             hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_trace tr --=> h'
``);
il 12;
e(FULL_SIMP_TAC std_ss []);
(* to avoid repeated dr2 *)
e(QCUT_TAC `
    (?hs''' hid' h'' h''' tid' v rn' rp' rc'.
       hs'' |+ (hid,h) = hs''' |+ (hid',h'') /\ Ln0_return (hid,tid,tlang) = Ln0_return (hid',tid',v) /\ hs'' |+ (hid,h') = hs''' |+ (hid',h''') /\
       hid' NOTIN FDOM hs''' /\ rn' /* rp', rc' */ h'' -- Lh_return (tid',v) --=> h''')
`);
e(Q.EXISTS_TAC `hs''`);
e(Q.EXISTS_TAC `hid`);
e(Q.EXISTS_TAC `h`);
e(Q.EXISTS_TAC `h'`);
e(Q.EXISTS_TAC `tid`);
e(Q.EXISTS_TAC `tlang`);
e(Q.EXISTS_TAC `rn`);
e(Q.EXISTS_TAC `rp`);
e(Q.EXISTS_TAC `rc`);
e((REPEAT CONJR_TAC) THEN (FULL_SIMP_TAC std_ss []));

e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);

(* Lh_senddatagram *)
e(mesonLib.ASM_MESON_TAC[]);

(* Lh_recvdatagram *)
e(mesonLib.ASM_MESON_TAC[]);

(* Lh_loopdatagram *)
e(SIMP_TAC std_ss [net1_to_net_Lnet1_def]);
e(FULL_SIMP_TAC std_ss []);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_net1" "Lnet1_case_def"]);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_case_def"]);
(* use clause 1 of net_redn *)
e(ASSUME_TAC (fetch "TCP1_net" "net_redn_cases"));
al ``(hs,msgs):net``;
al ``Ln0_tau``;
al ``(hs',msgs'):net``;
eql();
e(THIN_TAC ``
 net_redn (hs,msgs) Ln0_tau (hs',msgs') ==>
           (?hs'' hid h h' tid c msgs'' rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_call (hid,tid,c) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_call (tid,c) --=> h') \/
           (?hs'' hid h h' tid msgs'' v rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_return (hid,tid,v) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_return (tid,v) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg new_msgs.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),BAG_UNION msgs'' new_msgs) /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_senddatagram msg --=> h' /\ !new_msg. BAG_IN new_msg new_msgs ==> ?dur. new_msg = Timed (msg,sharp_timer dur)) \/
           (?hid rn rp rc h hs'' d h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),BAG_INSERT (Timed (msg,sharp_timer d)) msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\
              hid NOTIN FDOM hs'' /\ timer_expires (sharp_timer d) /\ rn /* rp, rc */ h -- Lh_recvdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_loopdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' ifid up.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_interface (hid,ifid,up) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_interface (ifid,up) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs''.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_tau --=> h') \/
           (?rn rp rc hs'' hs''' msgs'' msgs''' dur msgs''''.
              (hs,msgs) = (hs'',msgs'') /\ Ln0_tau = Ln0_epsilon dur /\ (hs',msgs') = (hs''',msgs''') /\ FDOM hs''' = FDOM hs'' /\
              (!h. h IN FDOM hs'' ==> rn /* rp, rc */ hs'' ' h -- Lh_epsilon dur --=> hs''' ' h) /\ msgs'''' = BAG_IMAGE (Time_Pass_timed dur) msgs'' /\
              ~BAG_IN NONE msgs'''' /\ msgs''' = BAG_IMAGE THE msgs'''') \/
           ?hid rn rp rc h hs'' h' msgs'' tr.
             (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_trace tr /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
             rn /* rp, rc */ h -- Lh_trace tr --=> h'
``);
il 11;
e(FULL_SIMP_TAC std_ss []);
(* to avoid repeated dr2 *)
e(QCUT_TAC `
    (?hid' rn' rp' rc' h'' hs''' h''' msg.
       hs'' |+ (hid,h) = hs''' |+ (hid',h'') /\ hs'' |+ (hid,h') = hs''' |+ (hid',h''') /\ hid' NOTIN FDOM hs''' /\
       rn' /* rp', rc' */ h'' -- Lh_loopdatagram msg --=> h''')
`);
e(Q.EXISTS_TAC `hid`);
e(Q.EXISTS_TAC `rn`);
e(Q.EXISTS_TAC `rp`);
e(Q.EXISTS_TAC `rc`);
e(Q.EXISTS_TAC `h`);
e(Q.EXISTS_TAC `hs''`);
e(Q.EXISTS_TAC `h'`);
e(Q.EXISTS_TAC `m`);
e((REPEAT CONJR_TAC) THEN (FULL_SIMP_TAC std_ss []));

e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);

(* Lh_interface *)
e(SIMP_TAC std_ss [net1_to_net_Lnet1_def]);
e(FULL_SIMP_TAC std_ss []);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_net1" "Lnet1_case_def"]);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_case_def"]);
e(QCUT_TAC `? ifid b. p = (ifid,b)`); e(Q.EXISTS_TAC `FST p`); e(Q.EXISTS_TAC `SND p`); e(FULL_SIMP_TAC std_ss []);
e(elims);
(* use clause 1 of net_redn *)
e(ASSUME_TAC (fetch "TCP1_net" "net_redn_cases"));
al ``(hs,msgs):net``;
al ``Ln0_interface (hid,ifid,b)``;
al ``(hs',msgs'):net``;
eql();
e(THIN_TAC ``
 net_redn (hs,msgs) (Ln0_interface (hid,ifid,b)) (hs',msgs') ==>
           (?hs'' hid' h h' tid c msgs'' rn rp rc.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_interface (hid,ifid,b) = Ln0_call (hid',tid,c) /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_call (tid,c) --=> h') \/
           (?hs'' hid' h h' tid msgs'' v rn rp rc.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_interface (hid,ifid,b) = Ln0_return (hid',tid,v) /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_return (tid,v) --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs'' msg new_msgs.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_interface (hid,ifid,b) = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid',h'),BAG_UNION msgs'' new_msgs) /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_senddatagram msg --=> h' /\
              !new_msg. BAG_IN new_msg new_msgs ==> ?dur. new_msg = Timed (msg,sharp_timer dur)) \/
           (?hid' rn rp rc h hs'' d h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid',h),BAG_INSERT (Timed (msg,sharp_timer d)) msgs'') /\ Ln0_interface (hid,ifid,b) = Ln0_tau /\
              (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\ hid' NOTIN FDOM hs'' /\ timer_expires (sharp_timer d) /\
              rn /* rp, rc */ h -- Lh_recvdatagram msg --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_interface (hid,ifid,b) = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\ hid' NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_loopdatagram msg --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs'' ifid' up.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_interface (hid,ifid,b) = Ln0_interface (hid',ifid',up) /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
              hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_interface (ifid',up) --=> h') \/
           (?hid' rn rp rc h hs'' h' msgs''.
              (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_interface (hid,ifid,b) = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\ hid' NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_tau --=> h') \/
           (?rn rp rc hs'' hs''' msgs'' msgs''' dur msgs''''.
              (hs,msgs) = (hs'',msgs'') /\ Ln0_interface (hid,ifid,b) = Ln0_epsilon dur /\ (hs',msgs') = (hs''',msgs''') /\ FDOM hs''' = FDOM hs'' /\
              (!h. h IN FDOM hs'' ==> rn /* rp, rc */ hs'' ' h -- Lh_epsilon dur --=> hs''' ' h) /\ msgs'''' = BAG_IMAGE (Time_Pass_timed dur) msgs'' /\
              ~BAG_IN NONE msgs'''' /\ msgs''' = BAG_IMAGE THE msgs'''') \/
           ?hid' rn rp rc h hs'' h' msgs'' tr.
             (hs,msgs) = (hs'' |+ (hid',h),msgs'') /\ Ln0_interface (hid,ifid,b) = Ln0_trace tr /\ (hs',msgs') = (hs'' |+ (hid',h'),msgs'') /\
             hid' NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_trace tr --=> h'

``);
il 12;
e(FULL_SIMP_TAC std_ss []);
(* to avoid repeated dr2 *)
e(QCUT_TAC `
    (?hid' rn' rp' rc' h'' hs''' h''' ifid' up.
       hs'' |+ (hid,h) = hs''' |+ (hid',h'') /\ Ln0_interface (hid,ifid,b) = Ln0_interface (hid',ifid',up) /\ hs'' |+ (hid,h') = hs''' |+ (hid',h''') /\
       hid' NOTIN FDOM hs''' /\ rn' /* rp', rc' */ h'' -- Lh_interface (ifid',up) --=> h''')
`);
e(Q.EXISTS_TAC `hid`);
e(Q.EXISTS_TAC `rn`);
e(Q.EXISTS_TAC `rp`);
e(Q.EXISTS_TAC `rc`);
e(Q.EXISTS_TAC `h`);
e(Q.EXISTS_TAC `hs''`);
e(Q.EXISTS_TAC `h'`);
e(Q.EXISTS_TAC `ifid`);
e(Q.EXISTS_TAC `b`);

e((REPEAT CONJR_TAC) THEN (FULL_SIMP_TAC std_ss []));

e(mesonLib.ASM_MESON_TAC[]);

e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]); e(mesonLib.ASM_MESON_TAC[]); (* FIXME *)

(* Lh_tau *)
e(SIMP_TAC std_ss [net1_to_net_Lnet1_def]);
e(FULL_SIMP_TAC std_ss []);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_net1" "Lnet1_case_def"]);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_case_def"]);
(* use clause of net_redn *)
e(ASSUME_TAC (fetch "TCP1_net" "net_redn_cases"));
al ``(hs,msgs):net``;
al ``Ln0_tau``;
al ``(hs',msgs'):net``;
eql();
e(THIN_TAC ``
 net_redn (hs,msgs) Ln0_tau (hs',msgs') ==>
           (?hs'' hid h h' tid c msgs'' rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_call (hid,tid,c) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_call (tid,c) --=> h') \/
           (?hs'' hid h h' tid msgs'' v rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_return (hid,tid,v) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_return (tid,v) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg new_msgs.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),BAG_UNION msgs'' new_msgs) /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_senddatagram msg --=> h' /\ !new_msg. BAG_IN new_msg new_msgs ==> ?dur. new_msg = Timed (msg,sharp_timer dur)) \/
           (?hid rn rp rc h hs'' d h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),BAG_INSERT (Timed (msg,sharp_timer d)) msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\
              hid NOTIN FDOM hs'' /\ timer_expires (sharp_timer d) /\ rn /* rp, rc */ h -- Lh_recvdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_loopdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' ifid up.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_interface (hid,ifid,up) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_interface (ifid,up) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs''.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_tau --=> h') \/
           (?rn rp rc hs'' hs''' msgs'' msgs''' dur msgs''''.
              (hs,msgs) = (hs'',msgs'') /\ Ln0_tau = Ln0_epsilon dur /\ (hs',msgs') = (hs''',msgs''') /\ FDOM hs''' = FDOM hs'' /\
              (!h. h IN FDOM hs'' ==> rn /* rp, rc */ hs'' ' h -- Lh_epsilon dur --=> hs''' ' h) /\ msgs'''' = BAG_IMAGE (Time_Pass_timed dur) msgs'' /\
              ~BAG_IN NONE msgs'''' /\ msgs''' = BAG_IMAGE THE msgs'''') \/
           ?hid rn rp rc h hs'' h' msgs'' tr.
             (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_trace tr /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
             rn /* rp, rc */ h -- Lh_trace tr --=> h'
``);
il 11;
e(FULL_SIMP_TAC std_ss []);
(* to avoid repeated dr2 *)
e(QCUT_TAC `
    (?hid' rn' rp' rc' h'' hs''' h'''.
       hs'' |+ (hid,h) = hs''' |+ (hid',h'') /\ hs'' |+ (hid,h') = hs''' |+ (hid',h''') /\ hid' NOTIN FDOM hs''' /\ rn' /* rp', rc' */ h'' -- Lh_tau --=> h''')
`);
e(Q.EXISTS_TAC `hid`);
e(Q.EXISTS_TAC `rn`);
e(Q.EXISTS_TAC `rp`);
e(Q.EXISTS_TAC `rc`);
e(Q.EXISTS_TAC `h`);
e(Q.EXISTS_TAC `hs''`);
e(Q.EXISTS_TAC `h'`);

e((REPEAT CONJR_TAC) THEN (FULL_SIMP_TAC std_ss []));

e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);

(* Lh_epsilon *)
e(mesonLib.ASM_MESON_TAC[]);

(* Lh_trace *)
e(SIMP_TAC std_ss [net1_to_net_Lnet1_def]);
e(FULL_SIMP_TAC std_ss []);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_net1" "Lnet1_case_def"]);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_case_def"]);
(* use clause of net_redn *)
e(ASSUME_TAC (fetch "TCP1_net" "net_redn_cases"));
al ``(hs,msgs):net``;
al ``Ln0_trace p``;
al ``(hs',msgs'):net``;
eql();
e(THIN_TAC ``
  net_redn (hs,msgs) (Ln0_trace p) (hs',msgs') ==>
           (?hs'' hid h h' tid c msgs'' rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_trace p = Ln0_call (hid,tid,c) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_call (tid,c) --=> h') \/
           (?hs'' hid h h' tid msgs'' v rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_trace p = Ln0_return (hid,tid,v) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_return (tid,v) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg new_msgs.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_trace p = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),BAG_UNION msgs'' new_msgs) /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_senddatagram msg --=> h' /\ !new_msg. BAG_IN new_msg new_msgs ==> ?dur. new_msg = Timed (msg,sharp_timer dur)) \/
           (?hid rn rp rc h hs'' d h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),BAG_INSERT (Timed (msg,sharp_timer d)) msgs'') /\ Ln0_trace p = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\
              hid NOTIN FDOM hs'' /\ timer_expires (sharp_timer d) /\ rn /* rp, rc */ h -- Lh_recvdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_trace p = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_loopdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' ifid up.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_trace p = Ln0_interface (hid,ifid,up) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_interface (ifid,up) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs''.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_trace p = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_tau --=> h') \/
           (?rn rp rc hs'' hs''' msgs'' msgs''' dur msgs''''.
              (hs,msgs) = (hs'',msgs'') /\ Ln0_trace p = Ln0_epsilon dur /\ (hs',msgs') = (hs''',msgs''') /\ FDOM hs''' = FDOM hs'' /\
              (!h. h IN FDOM hs'' ==> rn /* rp, rc */ hs'' ' h -- Lh_epsilon dur --=> hs''' ' h) /\ msgs'''' = BAG_IMAGE (Time_Pass_timed dur) msgs'' /\
              ~BAG_IN NONE msgs'''' /\ msgs''' = BAG_IMAGE THE msgs'''') \/
           ?hid rn rp rc h hs'' h' msgs'' tr.
             (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_trace p = Ln0_trace tr /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
             rn /* rp, rc */ h -- Lh_trace tr --=> h'
``);
il 11;
e(FULL_SIMP_TAC std_ss []);
(* to avoid repeated dr2 *)
e(QCUT_TAC `
    ?hid' rn' rp' rc' h'' hs''' h''' tr.
      hs'' |+ (hid,h) = hs''' |+ (hid',h'') /\ Ln0_trace p = Ln0_trace tr /\ hs'' |+ (hid,h') = hs''' |+ (hid',h''') /\ hid' NOTIN FDOM hs''' /\
      rn' /* rp', rc' */ h'' -- Lh_trace tr --=> h'''
`);
e(Q.EXISTS_TAC `hid`);
e(Q.EXISTS_TAC `rn`);
e(Q.EXISTS_TAC `rp`);
e(Q.EXISTS_TAC `rc`);
e(Q.EXISTS_TAC `h`);
e(Q.EXISTS_TAC `hs''`);
e(Q.EXISTS_TAC `h'`);
e(Q.EXISTS_TAC `p`);

e((REPEAT CONJR_TAC) THEN (FULL_SIMP_TAC std_ss []));

e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);
(* end of these Lh cases *)

dl();

(* clause 2 of net1_redn, Lh_senddatagram *)
e(elims);
e(SIMP_TAC std_ss [net1_to_net_Lnet1_def]);
e(FULL_SIMP_TAC std_ss []);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_net1" "Lnet1_case_def"]);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_case_def"]);
(* use clause 3 of net_redn *)
e(ASSUME_TAC (fetch "TCP1_net" "net_redn_cases"));
al ``(hs,msgs):net``;
al ``Ln0_tau``;
al ``(hs',msgs'):net``;
eql();
e(THIN_TAC ``
 net_redn (hs,msgs) Ln0_tau (hs',msgs') ==>
           (?hs'' hid h h' tid c msgs'' rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_call (hid,tid,c) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_call (tid,c) --=> h') \/
           (?hs'' hid h h' tid msgs'' v rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_return (hid,tid,v) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_return (tid,v) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg new_msgs.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),BAG_UNION msgs'' new_msgs) /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_senddatagram msg --=> h' /\ !new_msg. BAG_IN new_msg new_msgs ==> ?dur. new_msg = Timed (msg,sharp_timer dur)) \/
           (?hid rn rp rc h hs'' d h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),BAG_INSERT (Timed (msg,sharp_timer d)) msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\
              hid NOTIN FDOM hs'' /\ timer_expires (sharp_timer d) /\ rn /* rp, rc */ h -- Lh_recvdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_loopdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' ifid up.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_interface (hid,ifid,up) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_interface (ifid,up) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs''.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_tau --=> h') \/
           (?rn rp rc hs'' hs''' msgs'' msgs''' dur msgs''''.
              (hs,msgs) = (hs'',msgs'') /\ Ln0_tau = Ln0_epsilon dur /\ (hs',msgs') = (hs''',msgs''') /\ FDOM hs''' = FDOM hs'' /\
              (!h. h IN FDOM hs'' ==> rn /* rp, rc */ hs'' ' h -- Lh_epsilon dur --=> hs''' ' h) /\ msgs'''' = BAG_IMAGE (Time_Pass_timed dur) msgs'' /\
              ~BAG_IN NONE msgs'''' /\ msgs''' = BAG_IMAGE THE msgs'''') \/
           ?hid rn rp rc h hs'' h' msgs'' tr.
             (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_trace tr /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
             rn /* rp, rc */ h -- Lh_trace tr --=> h'
``);
il 10;
e(FULL_SIMP_TAC std_ss []);
(* to avoid repeated dr2 *)
e(QCUT_TAC `
    (?hid' rn' rp' rc' h'' hs''' h''' msg' new_msgs'.
       hs'' |+ (hid,h) = hs''' |+ (hid',h'') /\ hs'' |+ (hid,h') = hs''' |+ (hid',h''') /\ BAG_UNION msgs'' new_msgs = BAG_UNION msgs'' new_msgs' /\
       hid' NOTIN FDOM hs''' /\ rn' /* rp', rc' */ h'' -- Lh_senddatagram msg' --=> h''' /\
       !new_msg. BAG_IN new_msg new_msgs' ==> ?dur. new_msg = Timed (msg',sharp_timer dur))
`);
er ``hid:hostid``;
e(Q.EXISTS_TAC `rn`);
e(Q.EXISTS_TAC `rp`);
e(Q.EXISTS_TAC `rc`);
e(Q.EXISTS_TAC `h`);
e(Q.EXISTS_TAC `hs''`);
e(Q.EXISTS_TAC `h'`);
e(Q.EXISTS_TAC `msg`);
e(Q.EXISTS_TAC `new_msgs`);
e((REPEAT CONJR_TAC) THEN (FULL_SIMP_TAC std_ss []));
e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);

dl();

(* clause 3 of net1_redn, Lh_recvdatagram *)
e(elims);
e(SIMP_TAC std_ss [net1_to_net_Lnet1_def]);
e(FULL_SIMP_TAC std_ss []);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_net1" "Lnet1_case_def"]);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_case_def"]);
(* use clause 4 of net_redn *)
e(ASSUME_TAC (fetch "TCP1_net" "net_redn_cases"));
al ``(hs,msgs):net``;
al ``Ln0_tau``;
al ``(hs',msgs'):net``;
eql();
e(THIN_TAC ``
 net_redn (hs,msgs) Ln0_tau (hs',msgs') ==>
           (?hs'' hid h h' tid c msgs'' rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_call (hid,tid,c) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_call (tid,c) --=> h') \/
           (?hs'' hid h h' tid msgs'' v rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_return (hid,tid,v) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_return (tid,v) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg new_msgs.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),BAG_UNION msgs'' new_msgs) /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_senddatagram msg --=> h' /\ !new_msg. BAG_IN new_msg new_msgs ==> ?dur. new_msg = Timed (msg,sharp_timer dur)) \/
           (?hid rn rp rc h hs'' d h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),BAG_INSERT (Timed (msg,sharp_timer d)) msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\
              hid NOTIN FDOM hs'' /\ timer_expires (sharp_timer d) /\ rn /* rp, rc */ h -- Lh_recvdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_loopdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' ifid up.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_interface (hid,ifid,up) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_interface (ifid,up) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs''.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_tau --=> h') \/
           (?rn rp rc hs'' hs''' msgs'' msgs''' dur msgs''''.
              (hs,msgs) = (hs'',msgs'') /\ Ln0_tau = Ln0_epsilon dur /\ (hs',msgs') = (hs''',msgs''') /\ FDOM hs''' = FDOM hs'' /\
              (!h. h IN FDOM hs'' ==> rn /* rp, rc */ hs'' ' h -- Lh_epsilon dur --=> hs''' ' h) /\ msgs'''' = BAG_IMAGE (Time_Pass_timed dur) msgs'' /\
              ~BAG_IN NONE msgs'''' /\ msgs''' = BAG_IMAGE THE msgs'''') \/
           ?hid rn rp rc h hs'' h' msgs'' tr.
             (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln0_tau = Ln0_trace tr /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
             rn /* rp, rc */ h -- Lh_trace tr --=> h'
``);
il 10;
e(FULL_SIMP_TAC std_ss []);
(* to avoid repeated dr2 *)
e(QCUT_TAC `
    (?hid' rn' rp' rc' h'' hs''' d h''' msg'.
       hs'' |+ (hid,h) = hs''' |+ (hid',h'') /\ BAG_INSERT (Timed (msg,sharp_timer dur)) msgs'' = BAG_INSERT (Timed (msg',sharp_timer d)) msgs'' /\
       hs'' |+ (hid,h') = hs''' |+ (hid',h''') /\ hid' NOTIN FDOM hs''' /\ timer_expires (sharp_timer d) /\
       rn' /* rp', rc' */ h'' -- Lh_recvdatagram msg' --=> h''')
`);
er ``hid:hostid``;
e(Q.EXISTS_TAC `rn`);
e(Q.EXISTS_TAC `rp`);
e(Q.EXISTS_TAC `rc`);
e(Q.EXISTS_TAC `h`);
e(Q.EXISTS_TAC `hs''`);
e(Q.EXISTS_TAC `dur`);
e(Q.EXISTS_TAC `h'`);
e(Q.EXISTS_TAC `msg`);
e((REPEAT CONJR_TAC) THEN (FULL_SIMP_TAC std_ss []));
e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);

(* clause 4 of net1_redn, Lh_epsilon *)
e(elims);
e(SIMP_TAC std_ss [net1_to_net_Lnet1_def]);
e(FULL_SIMP_TAC std_ss []);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_net1" "Lnet1_case_def"]);
e(FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);
e(FULL_SIMP_TAC std_ss [fetch "TCP1_host0" "Lhost0_case_def"]);
(* use clause 5 of net_redn *)
e(ASSUME_TAC (fetch "TCP1_net" "net_redn_cases"));
al ``(hs,msgs):net``;
al ``Ln0_epsilon dur``;
al ``(hs',msgs'):net``;
eql();
e(THIN_TAC ``
 net_redn (hs,msgs) (Ln_epsilon dur) (hs',msgs') ==>
           (?hs'' hid h h' tid c msgs'' rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln_epsilon dur = Ln_call (hid,tid,c) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_call (tid,c) --=> h') \/
           (?hs'' hid h h' tid msgs'' v rn rp rc.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln_epsilon dur = Ln_return (hid,tid,v) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_return (tid,v) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg new_msgs.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln_epsilon dur = Ln_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),BAG_UNION msgs'' new_msgs) /\
              hid NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_senddatagram msg --=> h' /\
              !new_msg. BAG_IN new_msg new_msgs ==> ?dur. new_msg = Timed (msg,sharp_timer dur)) \/
           (?hid rn rp rc h hs'' d h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),BAG_INSERT (Timed (msg,sharp_timer d)) msgs'') /\ Ln_epsilon dur = Ln_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\
              hid NOTIN FDOM hs'' /\ timer_expires (sharp_timer d) /\ rn /* rp, rc */ h -- Lh_recvdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' msg.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln_epsilon dur = Ln_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_loopdatagram msg --=> h') \/
           (?hid rn rp rc h hs'' h' msgs'' ifid up.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln_epsilon dur = Ln_interface (hid,ifid,up) /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\
              hid NOTIN FDOM hs'' /\ rn /* rp, rc */ h -- Lh_interface (ifid,up) --=> h') \/
           (?hid rn rp rc h hs'' h' msgs''.
              (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln_epsilon dur = Ln_tau /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
              rn /* rp, rc */ h -- Lh_tau --=> h') \/
           (?rn rp rc hs'' hs''' msgs'' msgs''' dur' msgs''''.
              (hs,msgs) = (hs'',msgs'') /\ Ln_epsilon dur = Ln_epsilon dur' /\ (hs',msgs') = (hs''',msgs''') /\ FDOM hs''' = FDOM hs'' /\
              (!h. h IN FDOM hs'' ==> rn /* rp, rc */ hs'' ' h -- Lh_epsilon dur' --=> hs''' ' h) /\ msgs'''' = BAG_IMAGE (Time_Pass_timed dur') msgs'' /\
              ~BAG_IN NONE msgs'''' /\ msgs''' = BAG_IMAGE THE msgs'''') \/
           ?hid rn rp rc h hs'' h' msgs'' tr.
             (hs,msgs) = (hs'' |+ (hid,h),msgs'') /\ Ln_epsilon dur = Ln_trace tr /\ (hs',msgs') = (hs'' |+ (hid,h'),msgs'') /\ hid NOTIN FDOM hs'' /\
             rn /* rp, rc */ h -- Lh_trace tr --=> h'
``);
il 11;
e(FULL_SIMP_TAC std_ss []);
(* to avoid repeated dr2 *)
e(QCUT_TAC `
    (?rn' rp' rc' dur'.
       Ln0_epsilon dur = Ln0_epsilon dur' /\ BAG_IMAGE THE (BAG_IMAGE (Time_Pass_timed dur) msgs'') = BAG_IMAGE THE (BAG_IMAGE (Time_Pass_timed dur') msgs'') /\
       (!h. h IN FDOM hs'' ==> rn' /* rp', rc' */ hs'' ' h -- Lh_epsilon dur' --=> hs''' ' h) /\ ~BAG_IN NONE (BAG_IMAGE (Time_Pass_timed dur') msgs''))
`);
e(Q.EXISTS_TAC `rn`);
e(Q.EXISTS_TAC `rp`);
e(Q.EXISTS_TAC `rc`);
e(Q.EXISTS_TAC `dur`);
e((REPEAT CONJR_TAC) THEN (FULL_SIMP_TAC std_ss []));
e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);

e(mesonLib.ASM_MESON_TAC[]);
val _ = pg_top_thm_and_drop();

*)

val _ = export_theory();


(* Local Variables: *)
(* fill-column: 100 *)
(* End: *)
