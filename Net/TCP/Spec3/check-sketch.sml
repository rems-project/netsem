(* magic code to make SIGINT appear as an Interrupt exception *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

open HolKernel boolLib Parse simpLib BasicProvers

open testEval_utils
open finite_mapTheory

val _ = Globals.priming := SOME ""
val _ = Globals.linewidth := 180

(*
loadPath := "../Spec1" :: !loadPath
*)

(* ancestors *)
local
  open TCP1_bettersTheory TCP1_net1Theory
  open TCP3_bettersTheory fastRulesTheory
in end

(* ensure srw_ss() gets real calculation routines *)
local open realLib in end

fun LABEL_CONV l ss t = SIMP_CONV ss [] t before print l
fun PRINT_CONV s t = (print s; ALL_CONV t)

fun die s = if !Globals.interactive then raise Fail s
            else (TextIO.output(TextIO.stdErr, s ^ "\n");
                  OS.Process.exit OS.Process.failure)

fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")


(* important types and terms from ancestor theories *)
val hostid_ty = ``:TCP1_preHostTypes$hostid``
val streamid_ty = ``:streamid`` (* type abbreviation so can't use $ syntax *)
val host_ty = ``:TCP3_hostTypes$host``
val msg_ty = ``:TCP1_netTypes$msg``
val stream_ty = ``:TCP3_streamTypes$tcpStreams``
val Test_t = ``TCP1_preHostTypes$Test``
val Aux_t = ``TCP1_preHostTypes$Aux``
val Ln_epsilon_t = ``TCP3_net$Ln_epsilon``
val Ln_tau_t = ``TCP3_net$Ln_tau``
val host3_redn_t = ``TCP3_hostLTS$host_redn0``

val empty_hostmap = finite_mapSyntax.mk_fempty (hostid_ty, host_ty)
val empty_streammap = finite_mapSyntax.mk_fempty (streamid_ty, stream_ty)
val empty_msgbag = bagSyntax.mk_bag ([], msg_ty)
val net_redn_t = ``TCP3_net$net_redn``

fun extract_transition th = let
  val t = lhs (concl th)
  val (s1, lab_s2) = pairSyntax.dest_pair t
  val (lab, s2) = pairSyntax.dest_pair lab_s2
in
  (s1, lab, s2)
end

fun extract_streamid t = let
  (* assume streams terms always look like <| streams := ... |> *)
  val streamset = rand (rand (rator t))
  val (s1, rest) = pred_setSyntax.dest_insert streamset
  val (s2, _) = pred_setSyntax.dest_insert rest
  fun stream_to_ip_pair s = let
    val i = rhs (concl (SIMP_CONV (srw_ss()) [] ``(^s).i``))
    val p = rhs (concl (SIMP_CONV (srw_ss()) [] ``(^s).p``))
  in
    pairSyntax.mk_pair(i,p)
  end
  val s1pair = stream_to_ip_pair s1
  val s2pair = stream_to_ip_pair s2
in
  pred_setSyntax.mk_set [s1pair,s2pair]
end

fun state_to_netstate s = let
  open finite_mapSyntax pairSyntax
  val (h1, streamopt_h2) = dest_pair s
  val (streamopt, h2) = dest_pair streamopt_h2
  val hostmap =
      mk_fupdate (mk_fupdate(empty_hostmap, mk_pair(Test_t, h1)),
                  mk_pair(Aux_t, h2))
  val streammap =
      if same_const optionSyntax.none_tm streamopt then
        empty_streammap
      else let
          val strm = optionSyntax.dest_some streamopt
        in
          mk_fupdate(empty_streammap, mk_pair(extract_streamid strm, strm))
        end
in
  list_mk_pair[hostmap,streammap,empty_msgbag]
end



fun congs ths = SSFRAG { ac = [], congs = ths,
                         convs = [], dprocs = [], filter = NONE,
                         rewrs = []}

val cond_cong1 = prove(
  ``(p = p') ==> ((if p then q else r) = (if p' then q else r))``,
  SIMP_TAC boolSimps.bool_ss []);

val option_cong = prove(
  ``(p = p') ==> (option_case x y p = option_case x y p')``,
  SIMP_TAC boolSimps.bool_ss []);

val two_insert_eq = prove(
  ``({p;q} = {x;y}) = (p = x /\ q = y \/ p = y /\ q = x \/
                       p = q /\ q = x /\ x = y)``,
  SRW_TAC [][pred_setTheory.EXTENSION] THEN bossLib.METIS_TAC []);

val dnf_cond = prove(
  ``(if p then q else r) = (p /\ q \/ ~p /\ r)``,
  bossLib.METIS_TAC []);

val elim_bool_case = prove(
  ``bool_case p q r = if r then p else q``,
  bossLib.Cases_on `r` THEN SRW_TAC [][])

val sing_abstraction = prove(
  ``(\s. s = v) = {v}``,
  SRW_TAC [][pred_setTheory.EXTENSION, IN_DEF]);

val GSPEC_applied = SIMP_RULE bool_ss [IN_DEF] pred_setTheory.GSPECIFICATION

val INSERT_applied = prove(
  ``((e1:'a) INSERT s) e2 = (e1 = e2 \/ e2 IN s)``,
  SRW_TAC [][GSPEC_applied, pred_setTheory.INSERT_DEF] THEN PROVE_TAC[])

val EMPTY_applied = prove(
  ``{} x = F``,
  SRW_TAC [][pred_setTheory.EMPTY_DEF]);

val DIFF_applied = prove(
  ``(s1 DIFF s2) x = (x IN s1 /\ ~(x IN s2))``,
  SRW_TAC [][pred_setTheory.DIFF_DEF, GSPEC_applied])

val IN_THM = prove(``(x IN (P : 'a -> bool)) = P x``, SRW_TAC [][IN_DEF])
fun mk_INth q = let
  val test = Parse.Term (QUOTE "( (" :: (q @ [QUOTE ") _foo):bool"]))
  val t = rator test
  val (dty,_) = dom_rng (type_of t)
  val P = mk_var("P", type_of t)
in
  (INST [P |-> t] o
   INST_TYPE [alpha |-> #1 (dom_rng (type_of t))]) IN_THM
end

val streams_sets2_1 = prove(
  ``~(r2.i = r3.i) ==>
   ({r1;r2} = {r3;r4}) = (r1 = r3 /\ r2 = r4)``,
  SRW_TAC [][EQ_IMP_THM, pred_setTheory.EXTENSION, DISJ_IMP_THM,
             FORALL_AND_THM]);

val streams_sets2_2 = prove(
  ``~(r2.i = r4.i) ==>
    ({r1;r2} = {r3;r4}) = (r1 = r4 /\ r2 = r3)``,
  SRW_TAC [][EQ_IMP_THM, pred_setTheory.EXTENSION, DISJ_IMP_THM,
             FORALL_AND_THM]);

val streams_sets2_3 = prove(
  ``~(r1.i = r3.i) ==>
    (({r1;r2} = {r3;r4}) = (r1 = r4 /\ r2 = r3))``,
  SRW_TAC [][EQ_IMP_THM, pred_setTheory.EXTENSION, DISJ_IMP_THM,
             FORALL_AND_THM]);
val streams_sets2_4 = prove(
  ``~(r1.i = r4.i) ==>
    (({r1;r2} = {r3;r4}) = (r1 = r3 /\ r2 = r4))``,
  SRW_TAC [][EQ_IMP_THM, pred_setTheory.EXTENSION, DISJ_IMP_THM,
             FORALL_AND_THM]);

val fm_SAME_KEY = prove(
  ``(fm1 |+ (k,v1) = fm2 |+ (k,v2)) =
    (fm1 \\ k = fm2 \\ k /\ v1 = v2)``,
  SRW_TAC [][fmap_EXT, pred_setTheory.EXTENSION, DOMSUB_FAPPLY_THM,
             FAPPLY_FUPDATE_THM, EQ_IMP_THM, DISJ_IMP_THM,
             FORALL_AND_THM] THEN
  METIS_TAC []);

val fmsize_def = new_definition("fmsize_def",
  ``fmsize (fm : 'a |-> 'b) = CARD (FDOM fm)``);

val card_lemma = prove(
  ``!fm k. k IN FDOM fm ==> 0 < CARD (FDOM fm)``,
  HO_MATCH_MP_TAC fmap_INDUCT THEN SRW_TAC [][]);

val fmsize_thm = prove(
  ``(fmsize FEMPTY = 0) /\
    (fmsize (fm |+ (k,v)) = fmsize (fm \\ k) + 1)``,
  SRW_TAC [][fmsize_def] THENL [
    `0 < CARD (FDOM fm)` by METIS_TAC [card_lemma] THEN
    DECIDE_TAC,
    DECIDE_TAC
  ]);

(* val FEMPTY_FUPDATE_EQ = prove(
  ``(FEMPTY |+ (k1,v1) = fm |+ (k2,v2)) =
    (fm \\ k2 = FEMPTY /\ k1 = k2 /\ v1 = v2)``,
  SRW_TAC [][fmap_EXT, EQ_IMP_THM, DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN
  bossLib.METIS_TAC []);
*)

(* from testEval.sml *)
val fd_sockop_concrete = let
  open simpLib BasicProvers
  val opns = TypeBase.constructors_of ``:LIB_interface``
  val li_ty = ``:LIB_interface``
  fun fill_out t = let
    val (d, _) = dom_rng (type_of t)
    fun make_gen_t ty = let
      val (ty1, ty2) = pairSyntax.dest_prod ty
    in
      pairSyntax.mk_pair(make_gen_t ty1, make_gen_t ty2)
    end handle HOL_ERR _ => genvar ty
    val d_t = make_gen_t d
  in
    fill_out (mk_comb(t, d_t))
  end handle HOL_ERR _ => t
  val filled_opns = map fill_out opns
  val fd_sockop_specced = SPEC_ALL TCP1_LIBinterfaceTheory.fd_sockop_def
  val fd_op_specced = SPEC_ALL TCP1_LIBinterfaceTheory.fd_op_def
  val opnv = mk_var("opn", li_ty)
  fun mk_concrete_thms t =
      [SIMP_RULE (srw_ss()) [] (INST [opnv |-> t] fd_sockop_specced),
       SIMP_RULE (srw_ss()) [] (INST [opnv |-> t] fd_op_specced)]
in
  List.concat (map mk_concrete_thms filled_opns)
end

val funupd_alt = Phase.phase_imm 1 (prove(
  (* ensures that the rewrite, generating an if, only happens if a funupd
     function is applied.  Because rewriting won't proceed underneath the
     if, there won't be a big chain of these generated.  Instead, the guard
     will stop work underneath it until it rewrites to T or F *)
  ``funupd f x y z = if x = z then y else f z``,
  SRW_TAC [][TCP1_utilsTheory.funupd_def]));

val base_ss =
    srw_ss() ++ rewrites (Phase.get_phase_list 1) ++
    rewrites [whileTheory.LEAST_DEF, whileTheory.WHILE,
              sing_abstraction, INSERT_applied, EMPTY_applied,
              GSPEC_applied, elim_bool_case,
              TCP3_auxFnsTheory.initial_cb_def,
              TCP3_auxFnsTheory.bound_port_allowed_def,
              TCP3_auxFnsTheory.tcp_output_required_def,
              TCP1_timersTheory.never_timer_def,
              mk_INth `drop_from_q0 lis`,
              mk_INth `TCP3_auxFns$update_idle y`,
              mk_INth `make_syn_flgs_data`,
              mk_INth `accept_incoming_q y`,
              mk_INth `tcp_output_required`,
              mk_INth `sf_default_b`,
              mk_INth `TCP3_stream$null_flgs_data`,
              BETA_RULE (mk_INth `(\y:'a. P y)`),
              pred_setTheory.INSERT_COMM,
              pred_setTheory.INSERT_INTER,
              pred_setTheory.INSERT_UNION_EQ,
              FUPDATE_LIST_THM,
              RES_EXISTS_THM, RES_FORALL_THM,
              arithmeticTheory.GREATER_EQ,
              arithmeticTheory.GREATER_DEF,
              integerTheory.int_ge,
              integerTheory.int_gt,
              realTheory.real_ge,
              realTheory.real_gt] ++
    rewrites fd_sockop_concrete

local
  val s = SIMP_CONV base_ss
  fun fmc thl t = Net_fmap_analyse.fm_onestep thl s t
  val fempty_update11 = prove(
    ``(FEMPTY |+ (k1:'a,v1:'b) = FEMPTY |+ (k2,v2)) = (k1 = k2 /\ v1 = v2)``,
    SRW_TAC [][fmap_EXT, EQ_IMP_THM, FAPPLY_FUPDATE_THM] THEN
    SRW_TAC [][pred_setTheory.EXTENSION] THEN DISJ1_TAC THEN
    Q.EXISTS_TAC `k1` THEN SRW_TAC [][])
  fun outervarkey_elim0 t = let
    val ove = Net_fmap_analyse.outermost_varkey_elim
    val set = HOLset.empty Term.compare
  in
    ove set (s []) t
    handle HOL_ERR { message = "outermost key not a var", ... } =>
             (REWR_CONV EQ_SYM_EQ THENC ove set (s [])) t
  end
  fun conjeq_elim t = let
    val (p,q) = dest_conj t
    val q0 = hd (CONJUNCTS (ASSUME q))
    val p'_th0 = REWRITE_CONV [q0] p
    val p'_th = DISCH_ALL p'_th0
    val q'_th = DISCH (rhs (concl p'_th0)) (REFL q)
  in
    MATCH_MP AND_CONG (CONJ p'_th q'_th)
  end
  val fmsizes_must_match = prove(
    ``~(fmsize fm1 = fmsize fm2) ==> ~(fm1 = fm2)``,
    METIS_TAC [])
  val FDOM_EQ_EMPTY' = prove(``({} = FDOM fm) = (fm = FEMPTY)``,
                             METIS_TAC [FDOM_EQ_EMPTY])
  val fdom_eq_th = prove(
    ``!fm e s.
          ((FDOM fm = e INSERT s) =
          ?v fm'. (fm = fm' |+ (e,v)) /\ (FDOM fm' = s))``,
    SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [EQ_IMP_THM] THEN
    HO_MATCH_MP_TAC fmap_INDUCT THEN SRW_TAC [][] THEN
    Cases_on `x = e` THENL [
      SRW_TAC [][] THEN Cases_on `e IN s` THENL [
        MAP_EVERY Q.EXISTS_TAC [`y`,`fm |+ (e,ARB)`] THEN
        SRW_TAC [][] THEN SRW_TAC [][GSYM pred_setTheory.ABSORPTION],
        MAP_EVERY Q.EXISTS_TAC [`y`, `fm`] THEN SRW_TAC [][] THEN
        METIS_TAC [pred_setTheory.IN_INSERT, pred_setTheory.EXTENSION]
      ],
      `FDOM fm = e INSERT (s DELETE x)`
         by (SRW_TAC [][pred_setTheory.EXTENSION] THEN
             METIS_TAC [pred_setTheory.EXTENSION, pred_setTheory.IN_INSERT,
                        pred_setTheory.IN_DELETE]) THEN
      RES_TAC THEN SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`v`, `fm' |+ (x,y)`] THEN
      SRW_TAC [][FUPDATE_COMMUTES] THEN
      MATCH_MP_TAC pred_setTheory.INSERT_DELETE THEN
      METIS_TAC [pred_setTheory.IN_INSERT]
    ]);
in
  val fm_SS =
      SSFRAG { ac = [], congs = [], dprocs = [], filter = NONE,
               rewrs = [FUPD11_SAME_KEY_AND_BASE, fempty_update11,
                        DOMSUB_FUPDATE_THM,
                        FAPPLY_FUPDATE_THM],
               convs = [{conv = K fmc, key = SOME ([], ``(?) P``),
                         name = "fmc", trace = 2}] }
  val fm2_SS =
      SSFRAG { ac = [], congs = [], dprocs = [], filter = NONE,
               rewrs = [FUPDATE_COMMUTES, fm_SAME_KEY, fmsizes_must_match,
                        fmsize_thm, FDOM_EQ_EMPTY, FDOM_EQ_EMPTY', fdom_eq_th],
               convs = [{conv = K (K (outervarkey_elim0 THENC conjeq_elim)),
                         key = SOME ([], ``fm1 |+ (k1,v1) = fm2 |+ (k2,v2)``),
                         name = "fm.outervarkey", trace = 2}] }
end

val tcp1_ss =
    base_ss ++ congs [cond_cong1, option_cong] ++ fm_SS



val pair_sets = prove(
  ``({a;b} = {c;d}) = (if a = c then b = d else (a = d) /\ (b = c))``,
  SRW_TAC [][EQ_IMP_THM, pred_setTheory.EXTENSION] THEN METIS_TAC []);

val better_both_streams_destroyed = prove(
  ``both_streams_destroyed <| streams := {s1;s2} |> =
      (s1.destroyed /\ s2.destroyed)``,
  SRW_TAC [][TCP3_streamTheory.both_streams_destroyed_def, EQ_IMP_THM,
             pair_sets] THEN
  METIS_TAC []);

val p2_rwts =
    rewrites (Phase.get_phase_list 2 @
              [LET_THM, GSYM LEFT_EXISTS_AND_THM,
               GSYM RIGHT_EXISTS_AND_THM, pair_sets,
               TCP3_auxFnsTheory.stream_rollback_tcp_output_def,
               TCP3_auxFnsTheory.stream_test_outroute_def,
               TCP3_streamTheory.write_def,
               TCP3_streamTheory.read_def,
               TCP3_auxFnsTheory.update_idle_def,
               (* streams_sets2_1, streams_sets2_2,
               streams_sets2_3, streams_sets2_4, *)

               TCP3_streamTheory.sync_streams_def,
               TCP3_streamTheory.remove_destroyed_streams_def,
               TCP3_streamTheory.destroy_quads_def,
               better_both_streams_destroyed,
               TCP3_hostTypesTheory.EXISTS_socket,
               TCP3_hostTypesTheory.EXISTS_tcp_socket,
               TCP3_streamTypesTheory.EXISTS_streamFlags,
               TCP3_streamTypesTheory.EXISTS_tcpStreams,
               TCP3_streamTypesTheory.EXISTS_tcpStream,
               TCP1_preHostTypesTheory.EXISTS_socket_listen,
               TCP3_hostLTSTheory.di3_ackstuff_def])

val tcp2_ss =
    tcp1_ss ++ p2_rwts ++ fm_SS ++ fm2_SS ++ congs [cond_cong1, option_cong]

val tcp3_ss = base_ss ++ p2_rwts ++ fm_SS ++ fm2_SS

val tcp4_ss =
    tcp3_ss ++ boolSimps.DNF_ss ++ fm_SS ++ fm2_SS ++
    rewrites [two_insert_eq, dnf_cond]


val net_redn_rules = CONJUNCTS TCP3_netTheory.net_redn_rules
val net_redn_cases = TCP3_netTheory.net_redn_cases

fun myfind f [] = NONE
  | myfind f (h::t) = case f h of NONE => myfind f t | x => x

fun fmkey_match simp fmpat concmap = let
  open finite_mapSyntax pairSyntax
  val (fmpat0, kv) = dest_fupdate fmpat
  val (conckey, vpat) = dest_pair kv
  fun extract fmap = let
    val (cmap, kv) = dest_fupdate fmap
    val (k,v) = dest_pair kv
  in
    if Term.aconv conckey k then
      (v, cmap, REFL fmap)
    else let
        val (v, cmap0, th0) = extract cmap
        val th1 = RATOR_CONV (RAND_CONV (K th0)) fmap
        val noteq_th = EQT_ELIM (simp (mk_neg(mk_eq(conckey, k))))
        val comm_th = PART_MATCH (lhs o rand) FUPDATE_COMMUTES
                                 (rhs (concl th1))
      in
        (v,mk_fupdate(cmap0,kv),MP comm_th noteq_th)
      end
  end
  val (v_inst, map_inst, eqth) = extract concmap
  val fm_inst = if is_var fmpat0 then [fmpat0 |-> map_inst]
                else #1 (match_term fmpat0 map_inst)
  val v_inst = if is_var vpat then [vpat |-> v_inst]
               else #1 (match_term vpat v_inst)
  (* hope two insts are compatible *)
in
  (fm_inst @ v_inst, eqth)
end

val epsilon_rule =
    valOf (List.find (free_in Ln_epsilon_t o concl) net_redn_rules)
    handle Option => die "Couldn't find epsilon rule for net_redn"

fun net_redn_epsilon t = PART_MATCH rand epsilon_rule t

val tau_rule_id_rule = let
  fun is_id t = let
    val (_, args) = strip_comb t
  in
    aconv (hd args) (List.nth(args, 2))
  end
  fun is_id_rule th =
      free_in Ln_tau_t (concl th) andalso
      is_id (#2 (strip_forall (concl th)))
in
  valOf (List.find is_id_rule net_redn_rules)
  handle Option => die "Couldn't find identity-tau rule for net_redn"
end

val changing_tau_rule = let
  fun changep th = free_in Ln_tau_t (concl th) andalso
                   is_imp (#2 (strip_forall (concl th)))
in
  valOf (List.find changep net_redn_rules)
  handle Option => die "Couldn't find changing-tau rule for net_redn"
end

fun fmap_finish fmap_pat simp concpat1 concpat2 t th = let
  open pairSyntax
  val (fm_inst1,fm_match1) = fmkey_match simp fmap_pat concpat1
  val th1 =
      CONV_RULE (RAND_CONV
                   (RATOR_CONV
                      (RATOR_CONV
                         (RAND_CONV
                            (ONCE_REWRITE_CONV [SYM fm_match1])))))
                (INST fm_inst1 th)

  val host_fmap2 = (hd o strip_pair o rand o rand o concl) th1
  val (fm_inst2, fm_match2) =
      fmkey_match simp host_fmap2 concpat2
  val th2_0 = INST fm_inst2 th1
  val th2 =
      CONV_RULE (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [SYM fm_match2])))
                th2_0
in
  PART_MATCH rand th2 t
end


fun net_redn_tau t = let
  open pairSyntax finite_mapSyntax
  val (_, [state1, _, state2]) = strip_comb t
  val map1 = hd (strip_pair state1)
  val map2 = hd (strip_pair state2)
  datatype result = BM of (term,term)Binarymap.dict | CLASH of term
  fun build_mlmap mlm t = let
    val (fm, kv) = dest_fupdate t
    val (k, v) = dest_pair kv
  in
    case Binarymap.peek (mlm, k) of
      NONE => build_mlmap (Binarymap.insert(mlm, k, v)) fm
    | SOME v' => if aconv v v' then build_mlmap mlm fm
                 else CLASH k
  end handle HOL_ERR _ => BM mlm
  val mlm1 = case build_mlmap (Binarymap.mkDict Term.compare) map1 of
               BM m => m
             | CLASH t => die "Found clashing hosts within state1 map"
in
  case build_mlmap mlm1 map2 of
    BM _ => let
      (* no changed host - can use the stuttering tau at net_redn level *)
    in
      REWRITE_CONV [tau_rule_id_rule] t
    end
  | CLASH k => let
      val simp = SIMP_CONV base_ss []
      val rules_hid = let
        val con = concl changing_tau_rule
        val c = #2 (dest_imp (#2 (strip_forall con)))
        val triple1 = hd (#2 (strip_comb c))
        val hmap = hd (strip_pair triple1)
      in
        hd (strip_pair (#2 (dest_fupdate hmap)))
      end
      val inst0 = INST [rules_hid |-> k] (SPEC_ALL changing_tau_rule)
      val hmap_pat =
          hd (strip_pair (hd (#2 (strip_comb (#2 (dest_imp (concl inst0)))))))
    in
      fmap_finish hmap_pat simp map1 map2 t inst0
    end
end


fun net_redn_match t = let
  (* doesn't work for tau transitions *)
  open finite_mapSyntax pairSyntax
  val (_, args) = strip_comb t
  val label = List.nth (args, 1)
in
  if same_const label Ln_tau_t then net_redn_tau t
  else if same_const (rator label) Ln_epsilon_t handle HOL_ERR _ => false then
    net_redn_epsilon t
  else let
      val state1 = hd args
      val state2 = last args
      val th0 =
          myfind (fn th => SOME (PART_MATCH (rand o rator o rand) th label)
                     handle HOL_ERR _ => NONE)
                 net_redn_rules
      val th0 = valOf th0
      val simp = SIMP_CONV tcp1_ss []

      (* the non-tau, non-epsilon rules record the id of the changing
         host in the label of the transition, so the PART_MATCH above
         will have instantiated the hid in the first component of the
         rule's state1. This partially instantiated pattern, something
         of the form
                hmap |+ (k,v)
         with k ground, is what we extract here. *)
      val host_fmap1 =
          (hd o strip_pair o hd o #2 o strip_comb o rand o concl) th0
    in
      fmap_finish host_fmap1
                  simp
                  (hd (strip_pair state1))
                  (hd (strip_pair state2))
                  t
                  th0
    end
end

fun mapi f l = let
  fun recurse acc l =
      case l of [] => []
              | h :: t =>
                ((acc, SOME (f h)) handle _ => (acc, NONE)) ::
                recurse (acc + 1) t
in
  recurse 0 l
end


fun find_rule_by_id id = let
  val name = #Name (dest_thy_const id)
in
  DB.fetch "fastRules" ("fast_"^name)
end


val HOST3_LABEL_POS = 4
val HOST3_IDS = 3

fun down_to_args n t = let
  fun count_args t =
      1 + (count_args (rator t)) handle HOL_ERR _ => 0
  val c = count_args t
  fun drop_n n t = if n <= 0 then t else drop_n (n - 1) (rator t)
in
  drop_n (c - n) t
end

fun PROVE_NONURGENT_CONV t = let
  open TCP3_urgencyTheory
  val h = rand t
  val prove_ant =
      PART_MATCH rand (GEN_ALL nonurgent_characterisation) t
  val rewritten =
      CONV_RULE (LAND_CONV (SIMP_CONV tcp1_ss [nonurgent_approx_def, LET_THM]))
                prove_ant
in
  EQT_INTRO (MP rewritten TRUTH)
end

val IN_Time_Pass_ticker = prove(
  ``(x IN Time_Pass_ticker a b) = Time_Pass_ticker a b x``,
  SRW_TAC [][IN_DEF]);

val urgent_ss = tcp1_ss ++ rewrites (Phase.get_phase_list 3) ++
                rewrites [RES_EXISTS_THM, pairTheory.EXISTS_PROD,
                          IN_Time_Pass_ticker,
                          TCP3_hostLTSTheory.Time_Pass_host_def,
                          TCP3_hostLTSTheory.Time_Pass_socket_def,
                          TCP3_hostLTSTheory.Time_Pass_tcpcb_def]

fun validate_eps1_transition th = let
  open TCP3_urgencyTheory
  val _ = print "(hs-non-urgent "
  val th1 =
      CONV_RULE
        (LAND_CONV
           (LAND_CONV (SIMP_CONV tcp1_ss
                                 [DISJ_IMP_THM, FORALL_AND_THM,
                                  DOMSUB_FUPDATE_THM,
                                  GSYM nonurgent_host_def] THENC
                       EVERY_CONJ_CONV PROVE_NONURGENT_CONV)))
        th
  val th2 =
      CONV_RULE
        (LAND_CONV
           (SIMP_CONV urgent_ss [o_f_FUPDATE, o_f_FEMPTY,
                                 DOMSUB_FUPDATE_THM, LET_THM])) th1
  val _ = print "done) "
  (* hypothesis now looks like
       (hs = ...) /\ ~(NONE IN FRANGE hs) /\ (!hid. ... ) ==> transition
     so eliminate the hs variable *)
  val (hyp,con) = dest_imp (concl th2)
  val hyp_conjs = strip_conj hyp
  val hs_var = lhs (hd hyp_conjs)
  val th3 = Unwind.UNWIND_FORALL_RULE (GEN hs_var th2)

  (* simplify the ~(NONE IN ..) hypothesis *)
  val th4 =
      CONV_RULE (LAND_CONV
                   (LAND_CONV (SIMP_CONV urgent_ss [DOMSUB_FUPDATE_THM]) THENC
                    REWRITE_CONV []))
                th3

  val _ = print "(t-pass "
  (* simplify the !hid. conjunct *)
  val th5 = CONV_RULE
              (LAND_CONV
                 (SIMP_CONV urgent_ss [DISJ_IMP_THM, FORALL_AND_THM,
                                       FAPPLY_FUPDATE_THM]))
              th4
  (* all that remains is a conjunction of (ground) Time_Pass_ticker calls *)
  val two_32i = let
    fun sqr t = Arbint.*(t,t)
  in
    funpow 5 sqr Arbint.two
  end
  fun SOLVE_TICKER_DELTA_CONV t = let
    val (var, body) = dest_exists t
    val conjs = strip_conj body
    (* form of first conjunct is
          rat1 - &delta * coeff <= rat2
    *)
    fun dest_ratlit t =
        if realSyntax.is_div t then
          Arbrat./ (dest_ratlit (lhand t), dest_ratlit (rand t))
        else
          Arbrat.fromAInt (realSyntax.int_of_term t)
    val (l, r) = realSyntax.dest_leq (hd (strip_conj body))
    val rat2 = dest_ratlit r
    val (r1, dc) = realSyntax.dest_minus l
    val rat1 = dest_ratlit r1
    val c = dest_ratlit (#2 (realSyntax.dest_mult dc))
    val witness1 = Arbrat.ceil (Arbrat./(Arbrat.-(rat1,rat2), c))

    val eq_t = last conjs
    val (l,r) = dest_eq eq_t
    val li = Arbint.fromNat (numSyntax.dest_numeral (rand l))
    val ri = Arbint.fromNat (numSyntax.dest_numeral (rand (lhand r)))
    val diff = Arbint.mod(Arbint.-(li,ri), two_32i)
    fun inc_diff d = if Arbint.<(d, witness1) then
                       inc_diff (Arbint.+(d,two_32i))
                     else d
    val witness = numSyntax.mk_numeral (Arbint.toNat (inc_diff diff))
    val shown = EQT_ELIM ((SIMP_CONV urgent_ss [] THENC
                           word32Lib.WORD_CONV) (subst [var |-> witness] body))

  in
    EQT_INTRO (EXISTS(t, witness) shown)
  end

  val th6 =
      CONV_RULE
        (LAND_CONV
           (SIMP_CONV urgent_ss [TCP1_timersTheory.Time_Pass_ticker_def,
                                 LET_THM] THENC
            PRINT_CONV "deltas" THENC
            EVERY_CONJ_CONV SOLVE_TICKER_DELTA_CONV))
        th5
  val _ = print ") "
in
  ONCE_REWRITE_RULE [] th6
end


val ELIMINATE_HOST3_REDN_HYP =
    LABEL_CONV "(p1" tcp1_ss THENC
    LABEL_CONV " p2" tcp2_ss THENC
    PRINT_CONV ") "

exception Restart of thm
exception FalseContext
val p_eq_p_eq_T = SYM (List.nth(CONJUNCTS (SPEC_ALL EQ_CLAUSES), 1))
val np_eq_p_eq_F = SYM (last (CONJUNCTS (SPEC_ALL EQ_CLAUSES)))
fun remove_imp th =
    if is_imp (concl th) then let
        val (ant,con) = dest_imp (concl th)
      in
        if is_conj ant then
          remove_imp (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) th)
        else if is_exists ant then
          remove_imp (CONV_RULE LEFT_IMP_EXISTS_CONV th)
        else if is_eq ant then let
            val (l0,r0) = dest_eq ant
            val (l,r) = if is_var l0 then (l0,r0) else (r0,l0)
          in
            if is_eliminable_equality ant then
              remove_imp (MP (INST [l |-> r] th) (REFL r))
            else if null (free_vars l0) then
              remove_imp
                (UNDISCH (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ)) th))
            else
              remove_imp (UNDISCH th)
          end
        else if same_const ant boolSyntax.T then
          remove_imp (MP th TRUTH)
        else if same_const ant boolSyntax.F then
          raise FalseContext
        else if is_var ant then
          remove_imp (CONV_RULE (LAND_CONV (REWR_CONV p_eq_p_eq_T)) th)
        else if is_neg  ant andalso is_var (dest_neg ant) then
          remove_imp (CONV_RULE (LAND_CONV (REWR_CONV np_eq_p_eq_F)) th)
        else
          remove_imp (UNDISCH th)
      end
    else if is_forall (concl th) then
      remove_imp (SPEC_ALL th)
    else th

val shyps_ss = tcp2_ss ++ numSimps.ARITH_ss ++ realSimps.REAL_ARITH_ss ++
               rewrites [DECIDE ``~(x:num = y) = (x < y \/ y < x)``,
                         PROVE [integerTheory.INT_LE_ANTISYM,
                                integerTheory.INT_NOT_LE]
                               ``~(x:int = y) = (x < y \/ y < x)``]

fun simp_hyps th = let
  val hs = hypset th
  fun foldthis (h, th) = let
    val th' = DISCH h th
    val asms = map ASSUME (hyp th')
    val h'_th = SIMP_CONV shyps_ss asms h
    val th'' = EQ_MP (AP_THM (AP_TERM implication h'_th) (concl th)) th'
  in
    raise Restart (remove_imp th'')
  end handle UNCHANGED => th
in
  SOME(HOLset.foldl foldthis th hs)
  handle FalseContext => NONE
       | Restart th' => simp_hyps th'
end

fun PURE_REWRITE_HYPS thl th = let
  fun foldthis (h, th) = let
    val th' = DISCH h th
  in
    UNDISCH (CONV_RULE (LAND_CONV (PURE_REWRITE_CONV thl)) th')
  end
in
  HOLset.foldl foldthis th (hypset th)
end

fun case_split_and_simp (d,th) = let
  fun remove g th = let
    val _ = print "\\"
    val _ = print (StringCvt.padLeft #" " 2 (Int.toString d))
    val _ = print (" Case splitting on "^term_to_string g^"\\\n")
    val th1 = remove_imp (DISCH g (PURE_REWRITE_HYPS [ASSUME (mk_eq(g,T))] th))
    val neg_g = mk_eq(g,F)
    val th2 = remove_imp (DISCH neg_g (PURE_REWRITE_HYPS [ASSUME neg_g] th))
    fun s (d,th) = case simp_hyps th of NONE => NONE | SOME th' => SOME (d,th')
    val simped = seq.mapPartial s (seq.fromList [(d+1,th1), (d+1,th2)])
  in
    seq.bind simped case_split_and_simp
  end
  val cond_splits = find_free_conds [] [] (map Check (hyp th))
  val eqconds = List.mapPartial (fn c => let val cnd = #1 (dest_cond c)
                                         in
                                           if is_eq cnd then SOME cnd
                                           else NONE
                                         end)
                                cond_splits
  val disj_splits =
      List.mapPartial (fn t => if is_disj t orelse is_imp t andalso not (is_neg t)
                               then SOME (lhand t) else NONE)
                      (hyp th)
  val bool_splits = List.filter (fn t => type_of t = bool)
                                (HOLset.listItems (hyp_frees th))
  fun condsz c = let val (g,t,e) = dest_cond c
                 in
                   HOLset.numItems (FVL [t,e] empty_tmset)
                 end
in
  case eqconds of
    [] => let
    in
      case List.find is_eq disj_splits of
        NONE => let
        in
          case Listsort.sort (measure_cmp condsz) cond_splits of
            [] => let
            in
              case disj_splits @ bool_splits of
                [] => seq.result th
              | h :: _ => seq.delay (fn () => remove h th)
            end
          | c :: _ => seq.delay (fn () => remove (#1 (dest_cond c)) th)
        end
      | SOME d => seq.delay (fn () => remove d th)
    end
  | h :: _ => seq.delay (fn () => remove h th)
end

fun discharge_hypothesis net1_info0 th = let
  val net1_info = lhs (concl net1_info0)
  val _ :: _ :: rule_id :: _ =
      List.rev (pairSyntax.strip_pair net1_info)
in
  if rule_id = ``epsilon_1`` then let
      val dur = rand (List.nth(#2 (strip_comb (rand (concl th))), 1))
      val _ = print (StringCvt.padRight #" " 25 ("ep1 "^term_to_string dur))
    in
      validate_eps1_transition th before print "done\n"
    end
  else if is_imp (concl th) then let
      (* calculate which host is moving and print it out with rule_id *)
      val ant_h = lhand (List.nth(#2 (strip_comb (lhand (concl th))), 3))
      val con_fm = lhand (hd (#2 (strip_comb (rand (concl th)))))
      val moving_host = let
        fun check fm_t = let
          val (fm', kv) = finite_mapSyntax.dest_fupdate fm_t
        in
          if aconv (rand kv) ant_h then lhand kv
          else check fm'
        end
      in
        check con_fm
      end
      val _ = print (StringCvt.padRight #" " 25
                                        (#Name (dest_thy_const rule_id) ^
                                         " " ^term_to_string moving_host))

      val (ant, con) = dest_imp (concl th)
      val hypargs = #2 (strip_comb ant)
      val r = SPEC_ALL (find_rule_by_id rule_id)
              (* r is an equality giving the cases clause for the given rule *)

      val label = List.nth (hypargs, HOST3_LABEL_POS)
       (* at this point, our hyp will have free variables corresponding to the
          as yet unknown information about which rule fired at the host1
          level.  The id is assumed to be the first parameter of the
          host_redn relation *)
      val h_ids = down_to_args 1 ant
      val (id_inst, _) = match_term h_ids
                                    (down_to_args 1 (lhs (concl r)))
      val th = Thm.INST id_inst th

      (* there should be rp (protocol) and rc (category) variables free in
         the hypothesis - we existentially quantify these *)
      val th0 = SIMP_RULE bool_ss [LEFT_FORALL_IMP_THM] (GEN_ALL th)

      val th1 =
          CONV_RULE (LAND_CONV (STRIP_QUANT_CONV (REWR_CONV r) THENC
                                ELIMINATE_HOST3_REDN_HYP))
                          th0
      val ant = #1 (dest_imp (concl th1))
    in
      if same_const ant boolSyntax.T then
        MATCH_MP th1 TRUTH before print "done\n"
      else if same_const ant boolSyntax.F then
        (print "**FALSE HYPOTHESIS\n"; th1)
      else let
          val _ = print "search\\\n"
          val witness_opt =
              Lib.total seq.hd (case_split_and_simp (0, remove_imp th1))
        in
          case witness_opt of
            NONE => (print "** search FAILS (hyps false)\n"; th1)
          | SOME wth => let
              val _ = print "\\numinst"
              val intinst = find_int_inst.find_int_inst (hyp wth)
            in
              case simp_hyps (INST intinst wth) of
                NONE => (print " **numinst FAILS\n"; wth)
              | SOME th => if not (null (hyp th)) then
                             (print " **hyps remain\n"; DISCH_ALL th)
                           else (print " done\n"; th)
            end
        end
    end
  else let
      val _ = print (StringCvt.padRight #" " 25
                                        (#Name (dest_thy_const rule_id)))
    in
      th before print "done\n"
    end
end handle Interrupt => (if !Globals.interactive then raise Interrupt
                         else print "INTERRUPTED\n"; th)

fun testsome n concs abs =
    case (concs, abs) of
      ([], []) => (print "ALLDONE\n"; [])
    | (c::cs, a::ass) => let
        val _ = print ("Step "^
                       StringCvt.padLeft #" " 3 (Int.toString n)^"  ")
      in
        (n, discharge_hypothesis c a) :: testsome (n + 1) cs ass
      end
    | ([], _) => (print "URK! Ran out of Spec1 information\n"; [])
    | (_, []) => (print "URK! Ran out of Spec3 information\n"; [])

fun test_nth n net_ths netredn_eliminated = let
  val net1_info0 = List.nth (net_ths, n)
  val th = List.nth (netredn_eliminated, n)
in
  discharge_hypothesis net1_info0 th
end

(* ----------------------------------------------------------------------
    main loop
   ---------------------------------------------------------------------- *)

(* get our "command-line argument" *)
val fnames =
    if !Globals.interactive then let
        val sample_str = TextIO.openIn "sample-check"
        val inp = TextIO.inputLine sample_str
      in
        [substring(inp, 0, size inp - 1)] before
        TextIO.closeIn sample_str
      end
    else CommandLine.arguments()
val _ = if not (!Globals.interactive) andalso fnames = [] then
          Process.exit Process.success
        else ()
val fname = hd fnames

fun pp_thms fname thlist = let
  val os = TextIO.openOut fname
  val pps = PP.mk_ppstream { consumer = (fn s => TextIO.output(os,s)),
                                linewidth = 150,
                                flush = (fn () => TextIO.flushOut os) }
  fun pp_el (n,th) =
      (PP.add_string pps (Int.toString n);
       PP.add_newline pps;
       pp_thm pps th;
       PP.add_newline pps;
       PP.add_newline pps)
in
  PP.begin_block pps PP.CONSISTENT 0;
  app pp_el thlist;
  PP.end_block pps;
  PP.flush_ppstream pps;
  TextIO.closeOut os
end


fun do_one_file fname = let
  (* If evaluating the following interactively, use quietdec!
       (The netredn_eliminated list will likely take ages to print otherwise)
  *)
  val net3_fname = Path.joinBaseExt {base = fname, ext = SOME "net3.thydata"}
  val net_fname = Path.joinBaseExt {base = fname, ext = SOME "net.thydata"}
  val _ = print ("Checking trace: "^net3_fname^" (reading ")

  (* read input *)
  val (_, net3_ths) = ListPair.unzip (DiskThms.read_file net3_fname)
  val (_, net_ths) = ListPair.unzip (DiskThms.read_file net_fname)
  val _ = print "munge1 "
  val transitions = map extract_transition net3_ths
  val netstate_transitions =
      map (fn (s0,lab,s) =>
              list_mk_comb(net_redn_t, [state_to_netstate s0,
                                        lab,
                                        state_to_netstate s]))
          transitions
   (* to check the trace at the Spec3 level, each term of netstates_transitions
      needs to be shown a theorem. *)

  (* first turn each net3 transition into an implication with an appropriate
     host3 transition as hypothesis, except for the epsilon rules, which
     have a more complicated hypothesis. *)
  val _ = print "munge2"
  val netredn_eliminated = map net_redn_match netstate_transitions
  val _ = print ")\n"
  val results = testsome 0 net_ths netredn_eliminated
  val output_base = Path.joinBaseExt {base = fname, ext = SOME "net3.checked"}
  val output_file1 =
      Path.joinBaseExt {base = output_base, ext = SOME "thydata"}
  val output_file2 =
      Path.joinBaseExt {base = output_base, ext = SOME "ppthms"}
  val _ = print ("Printing results to "^output_base^".{thydata,ppthms}\n\n")
in
  DiskThms.write_file output_file1 (map (fn (n,th) => (Int.toString n, th))
                                    results);
  pp_thms output_file2 results
end

val _ = app do_one_file fnames

