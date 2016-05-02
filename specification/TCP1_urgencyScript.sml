(* A HOL98 specification of TCP *)

(* An approximate characterisation of urgency *)

(*[ RCSID "$Id: TCP1_urgencyScript.sml,v 1.16 2006/10/04 10:23:17 tjr22 Exp $" ]*)

open HolKernel boolLib Parse

val _ = new_theory "TCP1_urgency";

open BasicProvers bossLib

val _ = augment_srw_ss [boolSimps.LET_ss]


local open TCP1_evalSupportTheory in end;

open TCP1_paramsTheory TCP1_auxFnsTheory TCP1_hostLTSTheory
open finite_mapTheory pred_setTheory

open HolDoc

(* ----------------------------------------------------------------------
    abbreviation for formula that occurs in host_redn_rules
   ---------------------------------------------------------------------- *)

val nonurgent_host_def = Define`
  nonurgent_host h =
    ~?rn rp rc lbl h'. rn /* rp, rc */ h -- lbl --> h' /\ is_urgent rc
`;

(* now prove a characterisation of when a host is nonurgent.  Because it's
   not an equivalence, it may be too strong. *)
  fun pull_neghost_eq (asl, g) = let
    val ds = strip_disj g
    fun is_hosteq t = let
      val (l,r,ty) = dest_eq_ty (dest_neg t)
    in
      ty = ``:host``
    end handle HOL_ERR _ => false
    val hosteq = valOf (List.find is_hosteq ds)
  in
    ASM_CASES_TAC (dest_neg hosteq) THENL [
      POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [],
      POP_ASSUM (fn th => REWRITE_TAC [th])]
  end (asl, g)

  val pull_neg_eq = let
    fun pullable t = is_var (lhs (dest_neg t)) handle HOL_ERR _ => false
  in
    CONV_TAC (markerLib.move_disj_left pullable) THEN
    CONV_TAC (REWR_CONV (GSYM IMP_DISJ_THM)) THEN
    DISCH_THEN ASSUME_TAC THEN VAR_EQ_TAC
  end

  val _ = augment_srw_ss [rewrites [finite_mapTheory.FUPDATE_LIST_THM,
                                    TCP1_hostTypesTheory.Sock_def]]

  val urgent_rules = store_thm(
    "urgent_rules",
    ``is_urgent rc /\ rn /* rp, rc */ h0 -- lab --> h ==>
      rn IN {accept_1; accept_4; accept_5; close_5; connect_2;
             connect_3; connect_4; recv_8a; recv_15; recv_20;
             recv_23; send_5a; send_7; send_15; send_16; send_17}``,
    Cases_on `rc` THEN
    REWRITE_TAC [TCP1_preHostTypesTheory.is_urgent_def] THEN
    Cases_on `b` THEN REWRITE_TAC [] THEN
    REWRITE_TAC [TCP1_hostLTSTheory.host_redn0_cases,
                 TypeBase.distinct_of ``:rule_cat``,
                 GSYM (TypeBase.distinct_of ``:rule_cat``),
                 TypeBase.one_one_of ``:rule_cat``,
                 TCP1_preHostTypesTheory.urgent_def,
                 TCP1_preHostTypesTheory.nonurgent_def,
                 TCP1_utilsTheory.ASSERTION_FAILURE_def] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [pred_setTheory.IN_INSERT] THEN
    FULL_SIMP_TAC bool_ss []);
    (* copes with connect_1, getsocklistening_2, sockat_mark_2 and recv_17 *)


  val nonurgent_approx_def = Define`
    nonurgent_approx a2 =
      let ts = a2.ts in
        let socks = a2.socks in
        !tid.
          tid IN FDOM ts ==>
          let tstid = ts ' tid
          in
           (!sid d lis.
               tstid = Timed (Accept2 sid, d) ==>
               let sockssid = socks ' sid
               in
                 ?tcp_sock.
                    sockssid.pr = TCP_PROTO tcp_sock /\
                    tcp_sock.st = LISTEN /\           (* for accept_5 *)
                    sockssid.cantrcvmore = F /\       (* for accept_4 *)
                    (tcp_sock.lis = SOME lis /\ ~(lis.q = []) ==>
                     let sid' = LAST lis.q in
                     let ssid' = socks ' sid' in
                     ?tcp_sock'.
                        ssid'.pr = TCP_PROTO tcp_sock' /\
                        let s'st = tcp_sock'.st in
                        let s'es = ssid'.es in
                          (s'st = ESTABLISHED ==>  (* for accept_1 *)
                           s'es = SOME ECONNABORTED))) /\
           (!sid d. ts ' tid = Timed(Close2 sid, d) ==> (* for close_5 *)
                  let sock = socks ' sid
                  in
                      ?tcp_sock.
                         sock.pr = TCP_PROTO tcp_sock /\
                         let st = tcp_sock.st in
                           ~(st = FIN_WAIT_2) /\ ~(st = TIME_WAIT) /\
                           ~(st = CLOSED)) /\
         (!sid d. ts ' tid = Timed(Connect2 sid, d) ==>
                  let sock = socks ' sid
                  in
                     ?tcp_sock.
                        sock.pr = TCP_PROTO tcp_sock /\
                        let st = tcp_sock.st in
                          ~(st IN
                              {ESTABLISHED; CLOSE_WAIT; (* for connect_2 *)
                               CLOSED}) /\              (* for connect_3 *)
                          (st = SYN_SENT ==>
                           sock.es = NONE)) /\          (* for connect_4 *)
         (!sid n opts d.
             ts ' tid = Timed(Recv2(sid, n, opts), d) ==>
             let s = socks ' sid in
               s.es = NONE /\ (* for recv_8a *)
               !udp_sock.
                  s.pr = UDP_PROTO udp_sock ==>
                  udp_sock.rcvq = []) (* for recv_15, recv_20 and recv_23 *) /\
         (!sid str opts d ipas.
             ts ' tid = Timed(Send2(sid, ipas, str, opts), d) ==>
             let s = socks ' sid
             in
               ~s.cantsndmore /\          (* for send_7 *)
               s.es = NONE /\             (* for send_16 and send_5a *)
               (proto_of s.pr = PROTO_UDP ==>
                s.cantsndmore = T /\      (* for send_15 *)
                (!ips addrs. (ipas = SOME (ips, addrs)) ==> (* for send_17 *)
                            ~(ips = NONE /\ s.is2 = NONE)) /\
                STRLEN (IMPLODE str) <= UDPpayloadMax a2.arch /\
                (bsd_arch a2.arch ==>
                 STRLEN (IMPLODE str) <= s.sf.n(SO_SNDBUF))))
`;

val LAST_APPEND_1 = store_thm(
  "LAST_APPEND_1",
  ``!l x. LAST (APPEND l [x]) = x``,
  Induct THEN SRW_TAC [][listTheory.LAST_DEF]);
val _ = export_rewrites ["LAST_APPEND_1"]

val brwt1 = SIMP_CONV (srw_ss()) [] ``F /\ p``
val brwt2 = SIMP_CONV (srw_ss()) [] ``p \/ F``

val approx_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [TCP1_hostLTSTheory.host_redn0_cases] THEN
  CONV_TAC
    (RAND_CONV
       (EVERY_DISJ_CONV
          (STRIP_QUANT_CONV (LAND_CONV (SIMP_CONV (srw_ss()) []))))) THEN
  PURE_REWRITE_TAC [brwt1, brwt2, EXISTS_SIMP] THEN
  STRIP_TAC THEN
  Q.PAT_ASSUM `rc = y` SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [TCP1_preHostTypesTheory.is_urgent_def]) THEN
  TRY (FIRST_X_ASSUM CONTR_TAC) THEN
  Q.PAT_ASSUM `nonurgent_approx x` MP_TAC THEN
  SRW_TAC [][nonurgent_approx_def] THEN
  Q.EXISTS_TAC `tid` THEN
  ASM_SIMP_TAC (srw_ss()) [finite_mapTheory.NOT_EQ_FAPPLY,
                           TCP1_hostTypesTheory.TCP_Sock_def,
                           TCP1_hostTypesTheory.UDP_Sock_def,
                           TCP1_hostTypesTheory.TCP_Sock0_def,
                           TCP1_hostTypesTheory.UDP_Sock0_def]

val accept_1_approx = store_thm(
  "accept_1_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(accept_1 /* rp, rc */ h -- lbl --> h')``,
 approx_tac THEN SRW_TAC [][EXISTS_OR_THM]);

val accept_4_approx = store_thm(
  "accept_4_approx",
  ``nonurgent_approx a2 /\ is_urgent rc ==>
    ~(accept_4 /* rp, rc */ a2 -- lbl --> h)``,
  approx_tac);

val accept_5_approx = store_thm(
  "accept_5_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(accept_5 /* rp, rc */ h -- lbl --> h')``,
  approx_tac THEN
  Q.PAT_ASSUM `TCP_PROTO y = x` (MP_TAC o SYM) THEN
  FULL_SIMP_TAC (srw_ss()) []);

val close_5_approx = store_thm(
  "close_5_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(close_5 /* rp, rc */ h -- lbl --> h')``,
  approx_tac);

val connect_2_approx = store_thm(
  "connect_2_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(connect_2 /* rp, rc */ h -- lbl --> h')``,
  approx_tac THEN
  Q.PAT_ASSUM `TCP_PROTO y = x` (MP_TAC o SYM) THEN
  ASM_SIMP_TAC (srw_ss()) []);

val connect_3_approx = store_thm(
  "connect_3_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(connect_3 /* rp, rc */ h -- lbl --> h')``,
  approx_tac THEN
  Q.PAT_ASSUM `TCP_PROTO y = x` (MP_TAC o SYM) THEN
  ASM_SIMP_TAC (srw_ss()) []);

val connect_4_approx = store_thm(
  "connect_4_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(connect_4 /* rp, rc */ h -- lbl --> h')``,
  approx_tac);

val recv_8a_approx = store_thm(
  "recv_8a_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(recv_8a /* rp, rc */ h -- lbl --> h')``,
  approx_tac)

val recv_15_approx = store_thm(
  "recv_15_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(recv_15 /* rp, rc */ h -- lbl --> h')``,
  approx_tac);

val recv_20_approx = store_thm(
  "recv_20_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(recv_20 /* rp, rc */ h -- lbl --> h')``,
  approx_tac);

val recv_23_approx = store_thm(
  "recv_23_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(recv_23 /* rp, rc */ h -- lbl --> h')``,
  approx_tac);

val send_5a_approx = store_thm(
  "send_5a_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(send_5a /* rp, rc */ h -- lbl --> h')``,
  approx_tac);

val send_7_approx = store_thm(
  "send_7_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(send_7 /* rp, rc */ h -- lbl --> h')``,
  approx_tac);

val send_15_approx = store_thm(
  "send_15_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(send_15 /* rp, rc */ h -- lbl --> h')``,
  approx_tac THEN
  SIMP_TAC (srw_ss()) [TCP1_hostTypesTheory.proto_of_def]);

val send_16_approx = store_thm(
  "send_16_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(send_16 /* rp, rc */ h -- lbl --> h')``,
  approx_tac THEN Cases_on `str` THEN SRW_TAC [][]);

val send_17_approx = store_thm(
  "send_17_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(send_17 /* rp, rc */ h -- lbl --> h')``,
  approx_tac THEN
  SRW_TAC [numSimps.ARITH_ss][TCP1_hostTypesTheory.proto_of_def])

val nonurgent_characterisation = store_thm(
  "nonurgent_characterisation",
  ``!h. nonurgent_approx h ==> nonurgent_host h``,
  SIMP_TAC bool_ss [nonurgent_host_def, GSYM IMP_DISJ_THM] THEN
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC urgent_rules THEN
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) THEN
  PROVE_TAC [accept_1_approx, accept_4_approx, accept_5_approx,
             close_5_approx,
             connect_2_approx, connect_3_approx, connect_4_approx,
             recv_8a_approx, recv_15_approx, recv_20_approx, recv_23_approx,
             send_5a_approx, send_7_approx, send_15_approx, send_16_approx,
             send_17_approx]);

(* ----------------------------------------------------------------------
    reworking of time passage constants to be relational, and thus
    easy to rewrite with.
   ---------------------------------------------------------------------- *)

val relify_def = Define`
  (* turns a function to options into a relation *)
  relify f x y = (f x = SOME y)
`;

val Time_Pass_tcpcb_rel_def = Define`
  Time_Pass_tcpcb_rel dur cb0 cb =
    ?ts_recent' t_badrxtwin' t_idletime' tt_rexmt' tt_keep'
     tt_2msl' tt_delack' tt_conn_est' tt_fin_wait_2'.
        (* deterministic, but still partial, fields *)
        relify (Time_Pass_timedoption dur) cb0.tt_rexmt tt_rexmt' /\
        relify (Time_Pass_timedoption dur) cb0.tt_keep tt_keep' /\
        relify (Time_Pass_timedoption dur) cb0.tt_2msl tt_2msl' /\
        relify (Time_Pass_timedoption dur) cb0.tt_delack tt_delack' /\
        relify (Time_Pass_timedoption dur) cb0.tt_conn_est tt_conn_est' /\
        relify (Time_Pass_timedoption dur) cb0.tt_fin_wait_2 tt_fin_wait_2' /\
        (* non-deterministic *)
        Time_Pass_timewindow dur cb0.ts_recent ts_recent' /\
        Time_Pass_timewindow dur cb0.t_badrxtwin t_badrxtwin' /\
        Time_Pass_stopwatch dur cb0.t_idletime t_idletime' /\
        cb = cb0 with <| tt_rexmt := tt_rexmt';
                         tt_keep := tt_keep';
                         tt_2msl := tt_2msl';
                         tt_delack := tt_delack';
                         tt_conn_est := tt_conn_est';
                         tt_fin_wait_2 := tt_fin_wait_2';
                         ts_recent := ts_recent';
                         t_badrxtwin := t_badrxtwin';
                         t_idletime := t_idletime' |>
`;


val IS_SOME_EXISTS = prove(
  ``IS_SOME x = ?y. x = SOME y``,
  Cases_on `x` THEN SRW_TAC [][]);

val Time_Pass_tcpcb_relationally = prove(
  ``(?cbset. Time_Pass_tcpcb dur cb = SOME cbset /\ cb' IN cbset) =
    Time_Pass_tcpcb_rel dur cb cb'``,
  SRW_TAC [][TCP1_hostLTSTheory.Time_Pass_tcpcb_def,
             Time_Pass_tcpcb_rel_def, pred_setTheory.SPECIFICATION,
             relify_def, RES_EXISTS_THM] THEN
  SRW_TAC[][IS_SOME_EXISTS, PULL_EXISTS, GSYM RIGHT_EXISTS_AND_THM] THEN
  SRW_TAC[][EQ_IMP_THM] THEN SRW_TAC[][] THEN METIS_TAC[]);

val Time_Pass_socket_rel_def = Define`
  Time_Pass_socket_rel dur s0 s =
     case s0.pr of
        TCP_PROTO v =>
          (let cb0 = v.cb in
             ?cb. Time_Pass_tcpcb_rel dur cb0 cb /\
                  (s = s0 with pr := TCP_PROTO (v with cb := cb)))
      | UDP_PROTO  _ => (s = s0)
`;

val Time_Pass_socket_relationally = prove(
  ``(?sockset. Time_Pass_socket dur s = SOME sockset /\ s' IN sockset) =
    Time_Pass_socket_rel dur s s'``,
  SRW_TAC [][TCP1_hostLTSTheory.Time_Pass_socket_def,
             SYM Time_Pass_tcpcb_relationally, Time_Pass_socket_rel_def,
             RES_EXISTS_THM] THEN
  Cases_on `s.pr` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `Time_Pass_tcpcb dur t.cb` THEN
  FULL_SIMP_TAC (srw_ss()) [pred_setTheory.SPECIFICATION]);

(* ----------------------------------------------------------------------
    fm_range_relates will be used instead of fmap_every_pred
   ---------------------------------------------------------------------- *)

val fm_range_relates_def = Define`
  fm_range_relates R fm1 fm2 = (FDOM fm1 = FDOM fm2 /\
                                !k. k IN FDOM fm1 ==> R (fm1 ' k) (fm2 ' k))
`;

val fm_range_relates_FEMPTY = store_thm(
  "fm_range_relates_FEMPTY",
  ``fm_range_relates R FEMPTY fm = (fm = FEMPTY)``,
  SRW_TAC [][fm_range_relates_def, GSYM finite_mapTheory.fmap_EQ_THM,
             pred_setTheory.EXTENSION] THEN
  EQ_TAC THEN SRW_TAC [][]);

val fm_range_relates_FUPDATE = store_thm(
  "fm_range_relates_FUPDATE",
  ``fm_range_relates R (fm0 |+ (k,v)) fm =
       ?fm0' v'. R v v' /\ fm_range_relates R (fm0 \\ k) fm0' /\
                 fm = fm0' |+ (k, v')``,
  SRW_TAC [][fm_range_relates_def, DISJ_IMP_THM, FORALL_AND_THM] THEN
  EQ_TAC THENL [
    SRW_TAC [][] THEN
    MAP_EVERY Q.EXISTS_TAC [`fm \\ k`, `fm ' k`] THEN
    SRW_TAC [][] THENL [
      FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
      SRW_TAC [][pred_setTheory.EXTENSION] THEN PROVE_TAC [],
      FIRST_X_ASSUM (Q.SPEC_THEN `k'` MP_TAC) THEN
      SRW_TAC [][finite_mapTheory.DOMSUB_FAPPLY_NEQ,
                 finite_mapTheory.NOT_EQ_FAPPLY],
      SRW_TAC [][GSYM finite_mapTheory.fmap_EQ_THM] THENL [
        FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
        SRW_TAC [][pred_setTheory.EXTENSION] THEN PROVE_TAC [],
        Cases_on `x = k` THEN1 SRW_TAC [][] THEN
        SRW_TAC [][finite_mapTheory.DOMSUB_FAPPLY_NEQ,
                   finite_mapTheory.NOT_EQ_FAPPLY]
      ]
    ],
    SRW_TAC [][] THENL [
      SRW_TAC [][] THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
      SRW_TAC [][pred_setTheory.EXTENSION]THEN PROVE_TAC [],
      SRW_TAC [][],
      FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.FAPPLY_FUPDATE_THM,
                                finite_mapTheory.DOMSUB_FAPPLY_NEQ] THEN
      SRW_TAC [][]
    ]
  ]);

val NOT_IN_DOM_DOMSUB = prove(
  ``~(k IN FDOM fm) ==> fm \\ k = fm``,
  SRW_TAC [][GSYM finite_mapTheory.fmap_EQ_THM,
             finite_mapTheory.DOMSUB_FAPPLY_NEQ] THEN
  SRW_TAC [][pred_setTheory.EXTENSION] THEN PROVE_TAC []);

val IN_FRANGE_KEY_IN_DOM = prove(
  ``!fm v k. (v IN FRANGE fm) = ?k. k IN FDOM fm /\ fm ' k = v``,
  HO_MATCH_MP_TAC finite_mapTheory.fmap_INDUCT THEN
  SRW_TAC [][] THEN EQ_TAC THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `x` THEN SRW_TAC [][],
    `v IN FRANGE fm` by PROVE_TAC [NOT_IN_DOM_DOMSUB] THEN
    `?k. k IN FDOM fm /\ fm ' k = v` by PROVE_TAC [] THEN
    `~(x = k)` by PROVE_TAC [] THEN
    PROVE_TAC[finite_mapTheory.NOT_EQ_FAPPLY],
    SRW_TAC [][],
    `~(x = k)` by PROVE_TAC [] THEN
    `fm \\ x = fm` by PROVE_TAC [NOT_IN_DOM_DOMSUB] THEN
    SRW_TAC [][finite_mapTheory.NOT_EQ_FAPPLY] THEN PROVE_TAC []
  ]);

val NOT_EQ_NONE = prove(
  ``~(x = NONE) = ?y. x = SOME y``,
  Cases_on `x` THEN SRW_TAC [][]);

open lcsymtacs
val fmap_every_pred_relationally = prove(
  ``(?x. fmap_every_pred (Time_Pass_socket dur) fm = SOME x /\ y IN x) =
    fm_range_relates (Time_Pass_socket_rel dur) fm y``,
  SRW_TAC [][TCP1_hostLTSTheory.fmap_every_pred_def, EQ_IMP_THM,
             NOT_EQ_NONE,
             fm_range_relates_def, SYM Time_Pass_socket_relationally]
  THENL [
    `fm ' k ∈ FRANGE fm` by PROVE_TAC [IN_FRANGE_KEY_IN_DOM] THEN
    metis_tac[optionTheory.THE_DEF],
    qcase_tac `e ∈ FRANGE fm` >> Cases_on `e ∈ FRANGE fm` >> simp[] >>
    metis_tac[IN_FRANGE_KEY_IN_DOM],
    metis_tac[optionTheory.THE_DEF]
  ]);

val Time_Pass_host_rel_def = Define`
  Time_Pass_host_rel dur h h' =
    ?ts' iq' oq' ticks' socks'.
       relify (fmap_every (Time_Pass_timed dur)) h.ts ts' /\
       relify (Time_Pass_timed dur) h.iq iq' /\
       relify (Time_Pass_timed dur) h.oq oq' /\
       Time_Pass_ticker dur h.ticks ticks'/\
       fm_range_relates (Time_Pass_socket_rel dur) h.socks socks' /\
       h' = h with <| ts := ts' ; iq := iq'; oq := oq'; ticks := ticks';
                      socks := socks' |>
`;

val Time_Pass_host_relationally = prove(
  ``(?hostset. Time_Pass_host dur h = SOME hostset /\ h' IN hostset) =
    Time_Pass_host_rel dur h h'``,
  SRW_TAC [][TCP1_hostLTSTheory.Time_Pass_host_def,
             relify_def, pred_setTheory.SPECIFICATION,
             SYM fmap_every_pred_relationally, Time_Pass_host_rel_def,
             RES_EXISTS_THM, IS_SOME_EXISTS, PULL_EXISTS] >>
  csimp[] >> metis_tac[]);

val epsilon_rule = CONJUNCT1 TCP1_hostLTSTheory.host_redn_rules

(* don't understand how the -- --=> relation is supposed to work without
   having made a TCP1_net theory an ancestor *)
val better_epsilon_rule = store_thm(
  "better_epsilon_rule",
  ``!h dur h'.
       Time_Pass_host_rel dur h h' /\ nonurgent_host h ==>
       epsilon_1 /* rp_all, misc nonurgent */ h -- Lh_epsilon dur --=> h'``,
  SRW_TAC [][nonurgent_host_def, GSYM Time_Pass_host_relationally] THEN
  MATCH_MP_TAC epsilon_rule THEN SRW_TAC [][]);

val _ = export_theory()
