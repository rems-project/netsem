(* A HOL98 specification of TCP *)

(* Support for the symbolic evaluation of expressions involving finite maps *)

structure Net_fmap_analyse :> Net_fmap_analyse =
struct

open HolKernel Parse boolLib

val _ = Version.register "$RCSfile: Net_fmap_analyse.sml,v $" "$Revision: 1.19 $" "$Date: 2007/06/19 07:41:04 $";

val entry_grammars = (type_grammar(), term_grammar())
val _ = Parse.temp_set_grammars finite_mapTheory.finite_map_grammars

val ERR = mk_HOL_ERR "Net_fmap_analyse"
val WARN = HOL_WARNING "Net_fmap_analyse"

val tracing = ref false
val _ = register_btrace ("fmap_analyse", tracing)

val conjl_cong = prove(
  ``!p q q'. (p ==> (q = q')) ==> (p /\ q <=> p /\ q')``,
  REPEAT GEN_TAC THEN Q.ASM_CASES_TAC `p` THEN ASM_REWRITE_TAC []);
val conjr_cong = prove(
  ``!p q q'. (p ==> (q = q')) ==> (q /\ p <=> q' /\ p)``,
  REPEAT GEN_TAC THEN Q.ASM_CASES_TAC `p` THEN ASM_REWRITE_TAC []);

open finite_mapSyntax finite_mapTheory

fun is_ground lcs t = HOLset.isEmpty (FVL [t] empty_varset) orelse
                      HOLset.member(lcs, t)

fun compare_from_reduce red k1 k2 = let
  val th = red [] (mk_eq(k1, k2))
in
  EQT_ELIM th handle HOL_ERR _ => EQF_ELIM th
end;

fun try_all_unwinds t =
    if is_exists t then
      ((Unwind.UNWIND_EXISTS_CONV THENC try_all_unwinds) ORELSEC
       BINDER_CONV try_all_unwinds) t
    else ALL_CONV t


fun numeq_reduce thl = numLib.REDUCE_CONV
val num_compare = compare_from_reduce numeq_reduce

fun dest_fupdate_kv t = let
  val (fm, kv) = dest_fupdate t
in
  (fm, pairSyntax.dest_pair kv)
end

fun grounded_fm lconsts t =
    if is_fupdate t then let
        val (fm, kv) = dest_fupdate t
        val (k, _) = pairSyntax.dest_pair kv
      in
        is_ground lconsts k andalso grounded_fm lconsts fm
      end
    else not(is_var t)


fun check_fmeq0 lconsts t = let
  (* requires that one side or the other of a fm-equality has a ground base,
     and that this side also have ground keys in all of its fupdates.
     Flips the equality (if necessary) to make the fm with the ground base
     appear on the right *)
  val (l, r) = dest_eq t
in
  if grounded_fm lconsts l then REWR_CONV EQ_SYM_EQ t
  else if grounded_fm lconsts r then ALL_CONV t
  else raise ERR "check_fmeq" "neither side ground"
end

val fm_forall_eq = let
  open BasicProvers simpLib
in
  prove(Parse.Term`(!v. fm1 |+ (k:'a,v:'b) = fm2 |+ (k,v)) =
                   (fm1 |+ (k,v) = fm2 |+ (k,v))`,
        SIMP_TAC (srw_ss()) [EQ_IMP_THM] THEN
        SRW_TAC [][GSYM fmap_EQ_THM] THEN SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN
        Cases_on `x = k` THEN
        FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM] THEN
        PROVE_TAC [])
end

fun check_fmeq lcs t =
    if is_forall t then (REWR_CONV fm_forall_eq THENC check_fmeq0 lcs) t
    else check_fmeq0 lcs t

fun update_base t =
    update_base (#1 (dest_fupdate t)) handle HOL_ERR _ => t

fun update_keys t = let
  fun recurse acc t =
      case Lib.total dest_fupdate t of
        NONE => acc
      | SOME (fm, kv) =>
          recurse (#1 (pairSyntax.dest_pair kv)::acc) fm
          handle HOL_ERR _ => raise ERR "update_keys"
                                        "key-value pair not a pair"
in
  recurse [] t
end

(* for both of these, t is a term of the form fm FUPDATE_LIST kvs, and
   kvs is a list of pairs *)
fun list_update_base t = rand (rator t)
fun list_update_keys t = map (#1 o pairSyntax.dest_pair)
                             (#1 (listSyntax.dest_list (rand t)))

fun pull_out_key kcmp k fm = let
  (* fm is a finite map update sequence, and k is one of the keys;
     this pulls key k out so that it is the outermost update *)
  val fmkeys = update_keys fm
  val _ = mem k fmkeys orelse raise ERR "pull_out_key" "key not in update keys"
  fun recurse t = let
    val (fm, (candidate_k, _)) = dest_fupdate_kv t
  in
    if k = candidate_k then ALL_CONV t
    else let
        val k_ne_candidate = kcmp k candidate_k
      in
        LAND_CONV recurse THENC
        REWR_CONV (MATCH_MP FUPDATE_COMMUTES k_ne_candidate)
      end t
  end
in
  recurse fm
end

fun eval_apply eqreduce t = let
  (* t is an application of a finite map composed of key-updates to a value *)
in
  REWR_CONV FAPPLY_FUPDATE_THM THENC
  RATOR_CONV (LAND_CONV eqreduce) THENC
  PURE_REWRITE_CONV [COND_CLAUSES] THENC
  TRY_CONV (eval_apply eqreduce)
end t

val dnfCOND_EXPAND = prove(
  ``!p t e. (if p then t else e) <=> p /\ t \/ ~p /\ e``,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC []);

fun push_varkeys_inwards lconsts (simpn : conv) t = let
  (* t is an oriented equality.  On the left, there is a sequence of
     key-value updates, some of which may have unground keys.  If there
     are any keys on the left that are ground, pull them out.  This
     relies on being able to distinguish values.  Returns an equality (so
     this is a genuine conversion), and the new rhs will include the
     inferred key inequality information *)
  val (l, r) = dest_eq t
  val fm_ty = type_of l
  val (k_ty, v_ty) = dest_fmap_ty fm_ty
  val is_ground = is_ground lconsts
  fun ground_under_var acc t = let
    (* acc is true if we've seen an unground key so far *)
    val (f, (k, v)) = dest_fupdate_kv t
  in
    if is_ground k then if acc then SOME k else ground_under_var acc f
    else ground_under_var true f
  end handle HOL_ERR _ => NONE
  val k =
      valOf (ground_under_var false (lhs t))
      handle Option => raise ERR "push_varkeys_inwards" "No change required"
  val eq_th = ASSUME t
  val fapp_t = Term.inst [alpha |-> k_ty, beta |-> v_ty] fapply_t
  val applied_to_k0 = AP_THM (AP_TERM fapp_t eq_th) k
  val applied_to_k1 =
      CONV_RULE (RAND_CONV (eval_apply simpn)) applied_to_k0
  fun work_to_var acc th = let
    val (l,r) = dest_eq (concl th)
    val (fm, _) = dest_fapply l
  in
    if isSome (ground_under_var false fm) then let
        val c =
            LAND_CONV (eval_apply simpn) THENC
            RATOR_CONV (REWR_CONV COND_RAND) THENC
            REWR_CONV COND_RATOR THENC
            REWR_CONV dnfCOND_EXPAND THENC
            LAND_CONV (RAND_CONV simpn) THENC
            REWRITE_CONV []
        val (th1, cth) = CONJ_PAIR (CONV_RULE c th)
      in
        work_to_var (th1::acc) cth
      end
    else let
        val th1 = CONV_RULE (LAND_CONV (eval_apply simpn) THENC simpn) th
      in
        th1 :: acc
      end
  end
  val eq_thms =  work_to_var [] applied_to_k1
  val base_data = hd eq_thms
  val ineq_thms = tl eq_thms
  val key_inequalities = map (ASSUME o concl) (List.rev ineq_thms)
  fun move_ckey_out thms t = let
    val (f, (k, v)) = dest_fupdate_kv t
  in
    if is_ground k then LAND_CONV (move_ckey_out thms) t
    else let
        fun doswap th =
            REWR_CONV (MATCH_MP FUPDATE_COMMUTES th)
        fun ensure_ground thms t = let
          val (f0, (k0, v0)) = dest_fupdate_kv t
        in
          if is_ground k0 then ALL_CONV
          else LAND_CONV (ensure_ground (tl thms)) THENC
               doswap (hd thms)
        end t
      in
        ensure_ground thms t
      end
  end
  val reformed_lhs = move_ckey_out key_inequalities l
  val old_imp_new = let
    val others = LIST_CONJ eq_thms
    val eqn = TRANS (SYM (List.foldl (uncurry PROVE_HYP) reformed_lhs eq_thms))
                    eq_th
  in
    DISCH t (CONJ eqn others)
  end
  val new_imp_old = let
    val new_eq_base = mk_eq(rhs (concl reformed_lhs), r)
    val assumption_t = mk_conj(new_eq_base, concl (LIST_CONJ eq_thms))
    val asm_th = ASSUME assumption_t
    val conjs = CONJUNCTS asm_th
    val eq_c = hd conjs
    val base_conjs = tl conjs
    val eqn = List.foldl (uncurry PROVE_HYP) reformed_lhs base_conjs
    val base_th = TRANS reformed_lhs (ASSUME new_eq_base)
    fun foldthis (t, th) = DISCH t th
  in
    DISCH_ALL (TRANS eqn eq_c)
  end
in
  IMP_ANTISYM_RULE  old_imp_new new_imp_old
end;




fun make_outers_common lcs kcmp t = let
  (* t is an oriented equality, with a ground-base fm on the right and
     something else on the left.  This conversion munges the right-hand
     side so that it has the same outermost keys as the LHS *)
  val (l, r) = dest_eq t
  val lkeys = List.rev (update_keys l)
  fun recurse klist =
      case klist of
        [] => ALL_CONV
      | (k::ks) => if not (is_ground lcs k) then ALL_CONV
                   else pull_out_key kcmp k THENC LAND_CONV (recurse ks)
in
  RAND_CONV (recurse lkeys) t
end

val (FUPDATE_LIST_NIL, FUPDATE_LIST_CONS) = let
  val base = SPEC_ALL FUPDATE_LIST_THM
in
  (GEN_ALL (CONJUNCT1 base), GEN_ALL (CONJUNCT2 base))
end

fun to_updlist_by_length n = let
  (* argument is a finite-map term with updates.  Take the n outermost updates
     and put them into an update list *)
  fun recurse n = if n = 0 then ALL_CONV
                  else REWR_CONV (GSYM FUPDATE_LIST_CONS) THENC
                       recurse (n - 1)
  val start = REWR_CONV (GSYM FUPDATE_LIST_NIL)
in
  start THENC recurse n
end

fun transform_to_updlist lcs t = let
  (* t is an oriented equality.  Turns the LHS into ``var FUPDATE_LIST list``
     and RHS into ``x FUPDATE_LIST list'``, where list and list' have the
     same keys in the same order (and thus, the same length) *)
  val (l, r) = dest_eq t
  val (lkeys,_) = List.partition (is_ground lcs) (update_keys l)
  val nlkeys = length lkeys
in
  BINOP_CONV (to_updlist_by_length nlkeys) t
end

fun apply_unwind_thm simp_ th = let
  (* th is of form   |- var FUPDATE_LIST list = x FUPDATE_LIST list' *)
  open listSyntax listTheory
  val (l,r) = dest_eq (concl th)
  val llist = rand l
  val rlist = rand r
  val (a_ty, b_ty) =
      pairSyntax.dest_prod (dest_list_type (type_of llist))
  val fst_t = Term.inst [alpha |-> a_ty, beta |-> b_ty] pairSyntax.fst_tm
  val lmap = mk_map(fst_t, llist)
  val rmap = mk_map(fst_t, rlist)
  val maps_eq = mk_eq(lmap, rmap)
  val distinct_t = mk_thy_const { Thy = "list",
                                  Ty = mk_list_type a_ty --> bool,
                                  Name = "ALL_DISTINCT" }
  val distinct = mk_comb(distinct_t, lmap)
  val map_prover = EQT_ELIM o REWRITE_CONV [MAP, pairTheory.FST]
  val dist_prover = EQT_ELIM o
                    (REWRITE_CONV [ALL_DISTINCT, MAP, MEM, DE_MORGAN_THM,
                                   pairTheory.FST] THENC
                     EVERY_CONJ_CONV (simp_ []) THENC
                     REWRITE_CONV [])
  val side_conds = LIST_CONJ [th, map_prover maps_eq, dist_prover distinct]
in
  CONJ_PAIR (MATCH_MP FUPDATE_LIST_SAME_KEYS_UNWIND side_conds)
end

val add_extras_cong = prove(
  ``!p q. (p ==> q) ==> (p <=> p /\ q)``,
  REPEAT GEN_TAC THEN Q.ASM_CASES_TAC `p` THEN ASM_REWRITE_TAC []);

fun do_list_unwind simp t = let
  (* t of standard form: c1 /\ c2 /\ .. cn
     with c1 a directed fmap equality with update lists *)
  val cs = strip_conj t
  val eq_t = hd cs
  val (newth0, _) = apply_unwind_thm simp (ASSUME eq_t)
  val newth = DISCH_ALL (CONV_RULE (REWRITE_CONV [listTheory.CONS_11,
                                                  pairTheory.PAIR_EQ] THENC
                                    simp [])
                                   newth0)
in
  MATCH_MP add_extras_cong newth
end

fun keys_down_to_base base t = let
  fun recurse acc t =
      if t = base then acc
      else let
          val (fmap, kv) = dest_fupdate t
        in
          recurse (#1 (pairSyntax.dest_pair kv)::acc) fmap
        end
in
  recurse [] t
end

fun arrange_varkeys kcmp base keyseq t = let
  val _ = is_fmap_ty (type_of t) orelse raise ERR "arrange_varkeys" "not a fm"
  val fmkeys = keys_down_to_base base t
               handle HOL_ERR _ =>
                      raise ERR "arrange_varkeys" "base not present"
  val (keyseq', strangers) = partition (fn t => mem t keyseq) fmkeys
  val _ = Lib.set_eq keyseq' keyseq orelse
          raise ERR "arrange_varkeys"
                    "Term doesn't have full complement of keys"
  fun pull_out_strangers c slist t =
      case slist of
        [] => c t
      | (s::ss) => (pull_out_key kcmp s THENC
                    LAND_CONV (pull_out_strangers c ss)) t
  fun pull_out_friends flist t =
      case flist of
        [] => ALL_CONV t
      | (f::fs) => (pull_out_key kcmp f THENC
                    LAND_CONV (pull_out_friends fs)) t
in
  pull_out_strangers (pull_out_friends (List.rev keyseq)) strangers t
end

fun check_for_other_eliminations lcs simp_ t = let
  (* t of usual form, with first conjunct being equality with update lists.
     Check to see if other expressions of type fmap among the conjuncts can
     be made to have a sub-term of the same general shape, and thus
     eliminated.
  *)
  val _ = if (!tracing) then print "FMTrace: check_for_other_eliminations\n"
          else ()
  val (eq_c, others) = dest_conj t
  val kcompare = compare_from_reduce simp_
  val (l, r) = dest_eq eq_c
  val keyseq = list_update_keys l
  val base = list_update_base l
  fun could_be_eliminated subterm = let
    fun check_keys seq = let
      val (friends, strangers) = partition (C mem keyseq) seq
    in
      set_eq friends keyseq andalso
      List.all (is_ground lcs) strangers
    end
  in
    is_fmap_ty (type_of subterm) andalso
    check_keys (keys_down_to_base base subterm)
  end handle HOL_ERR _ => false
  fun elim_CONV st =
      if could_be_eliminated st then let
          val (_, elim_thm) = apply_unwind_thm simp_ (ASSUME eq_c)
          fun final_elim t = let
            val updlist = rand t
          in
            CONV_RULE
              (LAND_CONV (REWRITE_CONV [listTheory.MAP, pairTheory.FST]) THENC
               REWRITE_CONV [])
              (SPEC updlist elim_thm)
          end
        in
          arrange_varkeys kcompare base keyseq THENC
          to_updlist_by_length (length keyseq) THENC
          final_elim
        end st
      else NO_CONV st
  val others_rewritten = DEPTH_CONV elim_CONV others
in
  MATCH_MP conjl_cong (DISCH_ALL others_rewritten)
  handle HOL_ERR _ => ALL_CONV t
end



fun is_an_uninclusion fm c = let
  (* fm is a finite map term (probably a variable)
     c is a term.
     This function returns true if c is of the form ~(k IN FDOM fm)
  *)
  val c0 = dest_neg c
  val (f, args) = strip_comb c0
  val _ = length args = 2 andalso same_const f pred_setSyntax.in_tm orelse
          raise ERR "" ""
  val fm' = dest_fdom (hd (tl args))
in
  Term.compare(fm,fm') = EQUAL
end handle HOL_ERR _ => false

val assume_right_conj_congruence = let
  val p = mk_var("p", bool)
  val p' = mk_var("p'", bool)
  val q = mk_var("q", bool)
in
  REWRITE_RULE [](SPECL [p,p',q,q] AND_CONG)
  (* |- (q ==> (p = p')) ==> (p /\ q = p' /\ q) *)
end

fun outermost_varkey_elim lcs simp_ t = let
  (* t is of the form
        fmv |+ (vk, vv) = FEMPTY |+ (ck1, cv1) |+ ... |+ (ckn, cvn)
     from this we can conclude that
        vk IN {ck1, ... ckn}
     and candidate equations for vv as well, i.e.,
        vv = cv1 \/ vv = cv2 \/ ... vv = cvn

     If all but one of these lead to false consequences (because vv
     will be some sort of structured value not necessarily compatible
     with the various cvi), then we know an exact value for vk.

     Assume that simp_ on equations will between the different cki will
     prove them inequal. *)
  open simpLib boolSimps
  val fmeq_t = t
  val (lfm, rfm) = dest_eq fmeq_t
  val rfm_base = update_base rfm
  val _ = same_const rfm_base fempty_t orelse
          raise ERR "outermost_varkey_elim" "update base on right not {}"
  val lfm_keys = update_keys lfm
  val vk = last lfm_keys
  val _ = (is_var vk andalso not (HOLset.member(lcs, vk))) orelse
          raise ERR "outermost_varkey_elim" "outermost key not a var"
  val _ = if !tracing then print "FM: outermost_varkey_elim" else ()
  val eq_assumed = ASSUME fmeq_t
  val tyi = match_type (#1 (dom_rng (type_of fdom_t))) (type_of lfm)
  val fdom_t' = Term.inst tyi fdom_t
  val doms_eq = SYM (AP_TERM fdom_t' eq_assumed)
  val in_t' = Term.inst [alpha |-> type_of vk] pred_setSyntax.in_tm
  val vk_in_eq0 = AP_TERM (mk_comb(in_t', vk)) doms_eq
  val vk_in_eq = SIMP_RULE bool_ss [pred_setTheory.IN_INSERT,
                                    pred_setTheory.NOT_IN_EMPTY,
                                    FDOM_FUPDATE, FDOM_FEMPTY] vk_in_eq0
in
  if not (is_disj (concl vk_in_eq)) then
    MATCH_MP add_extras_cong (DISCH fmeq_t vk_in_eq)
  else let
      val tyi2 = match_type (#1 (dom_rng (type_of fapply_t))) (type_of lfm)
      val fapply_t' = Term.inst tyi2 fapply_t
      fun conseq eqn = let
        (* eqn is an equation th  vk = ck *)
        val th0 = MK_COMB (AP_TERM fapply_t' eq_assumed, eqn)
        val th1 = SIMP_RULE bool_ss [FAPPLY_FUPDATE_THM] th0
      in
        CONV_RULE simp_ th1
      end
      val results =
          map (fn d => (d, conseq (ASSUME d))) (strip_disj (concl vk_in_eq))
      fun recurse disjt (list : ('a * thm) list)  =
          if is_disj disjt then let
              val (d1, d2) = dest_disj disjt
              val th2 = recurse d2 (tl list)
            in
              DISJ_CASES (ASSUME disjt) (#2 (hd list)) th2
            end
          else
            #2 (hd list)
    in
      case List.filter (not o equal boolSyntax.F o concl o #2) results of
        [] => let
          val final_result =  (* = F *)
              PROVE_HYP vk_in_eq (recurse (concl vk_in_eq) results)
          val not_eqn = NEG_DISCH t final_result
        in
          EQF_INTRO not_eqn
        end
      | [(eqn, th)] => let
          fun transform (eqn', th') =
              if concl th' = boolSyntax.F then
                (eqn', CONTR (mk_conj(eqn, concl th)) th')
              else (eqn, CONJ (ASSUME eqn) th)
          val identical_concls = map transform results
          val final_result =
              PROVE_HYP vk_in_eq (recurse (concl vk_in_eq) identical_concls)
        in
          MATCH_MP add_extras_cong (DISCH fmeq_t final_result)
        end
      | _ => raise ERR "outermost_varkey_elim" "Too many possibilities"
    end
end

fun same_newkey_elim lcs simp_ t = let
  (* t is a term of the form c1 /\ c2 /\ .. cn
     where c1 is an oriented finite map equality.  If there's enough
     information in the other conjuncts to allow the application of
     FUPD11_SAME_NEW_KEY, then make this elimination.  Otherwise raise
     a HOL_ERR *)
  val _ = if !tracing then print "FM: same_newkey_elim\n" else ()
  val cs = strip_conj t
  val fmeq_t = hd cs
  val other_cs = tl cs
  val (lfm, _) = dest_eq fmeq_t
  val lfm_base = update_base lfm
  val uninclusions = filter (is_an_uninclusion lfm_base) other_cs
  fun key_of_unincl uninc = rand (rator (dest_neg uninc))
  val lfm_keys = update_keys lfm
  val lfm_varkeys = filter (not o is_ground lcs) lfm_keys
  val possible_keys =
      Lib.intersect lfm_keys (map key_of_unincl uninclusions)
  fun is_ineq t1 t2 t = t = mk_neg(mk_eq(t1, t2)) orelse
                        t = mk_neg(mk_eq(t2, t1))
  fun has_ineq_with k k' = List.exists (is_ineq k k') other_cs
  fun check_key k =
    List.all (has_ineq_with k) (Lib.set_diff lfm_varkeys [k])
in
  case List.find check_key possible_keys of
    NONE => raise ERR "same_newkey_elim" "Not enough constraints to eliminate"
  | SOME k => let
      (* perform elimination *)
      val other_keys = Lib.set_diff lfm_varkeys [k]
      fun is_relevant c = (is_an_uninclusion lfm_base c andalso
                           key_of_unincl c = k) orelse
                          (exists (fn vk => is_ineq k vk c) other_keys)
      fun accumulate P t =
          TRY_CONV (RAND_CONV (markerLib.move_conj_left P) THENC
                    REWR_CONV CONJ_ASSOC THENC accumulate P) t
      fun aug_kcompare ths t1 t2 =
            case List.find (fn th => concl th = mk_neg(mk_eq(t1,t2))) ths of
              NONE => compare_from_reduce simp_ t1 t2
            | SOME th => th
      fun bring_key_out t = let
        (* t is of the form c1 /\ c2 /\ .. cn, where c1 is a
           directed fmap equality, and the remaining conjuncts are relevant
           inequalities and an uninclusion.
           Use these to make the finite maps both have the same key on
           their outermost updates *)
        val (eq_t, others_t) = dest_conj t
        val others_th = ASSUME others_t
        val other_ths0 = CONJUNCTS others_th
        val other_ths = other_ths0 @ map GSYM other_ths0
        val pullout = BINOP_CONV (pull_out_key (aug_kcompare other_ths) k) eq_t
      in
        if HOLset.isEmpty (hypset pullout) then
          AP_THM (AP_TERM conjunction pullout) others_t
        else MATCH_MP conjr_cong (DISCH_ALL pullout)
      end

      fun perform_elimination t = let
        (* t is of same shape as before, but now the outermost keys are the
           same *)
        val (eq_t, others) = dest_conj t handle HOL_ERR _ => (t, boolSyntax.T)
        val other_ths0 = CONJUNCTS (ASSUME others)
        val other_ths = other_ths0 @ map GSYM other_ths0
        val (f1upd_t, f2upd_t) = dest_eq eq_t
        val (k_ty, v_ty) = dest_fmap_ty (type_of f1upd_t)
        val (f1_t, f1_kv) = dest_fupdate f1upd_t
        val (f2_t, f2_kv) = dest_fupdate f2upd_t
        val v1 = #2 (pairSyntax.dest_pair f1_kv)
        val v2 = #2 (pairSyntax.dest_pair f2_kv)
        val f1dom = mk_fdom f1_t
        val f2dom = mk_fdom f2_t
        val ab_inst = Term.inst [alpha |-> k_ty, beta |-> v_ty]
        val in_t = ab_inst pred_setSyntax.in_tm
        val k_in_f1dom = list_mk_comb(in_t, [k, f1dom])
        val k_in_f2dom = list_mk_comb(in_t, [k, f2dom])
        fun dom_rwt_conv ths =
            REWRITE_CONV (FDOM_FUPDATE::FDOM_FEMPTY::
                          pred_setTheory.IN_INSERT::
                          pred_setTheory.NOT_IN_EMPTY::ths)
        val in_fdom_prover = dom_rwt_conv other_ths THENC
                             EVERY_DISJ_CONV (simp_ [])
        val k_notin_f1dom = EQF_ELIM (in_fdom_prover k_in_f1dom)
        val k_notin_f2dom = EQF_ELIM (in_fdom_prover k_in_f2dom)
        val notins = CONJ k_notin_f1dom k_notin_f2dom
        val thm11 = MATCH_MP finite_mapTheory.FUPD11_SAME_NEW_KEY notins
        val eqn0 = DISCH others (REWR_CONV thm11 eq_t)
      in
        MATCH_MP assume_right_conj_congruence eqn0
      end
      fun maybeLAND_CONV c t = let
        val (l, r) = dest_conj t
      in
        if not (is_conj r) andalso is_relevant r then c t
        else LAND_CONV c t
      end
    in
      accumulate is_relevant THENC
      maybeLAND_CONV (REWRITE_CONV [GSYM CONJ_ASSOC] THENC
                      bring_key_out THENC perform_elimination) THENC
      TRY_CONV (REWR_CONV (GSYM CONJ_ASSOC))
    end t
end;

val T_and = GEN_ALL (hd (CONJUNCTS (SPEC_ALL boolTheory.AND_CLAUSES)))

local
  open bossLib
in
val mappair_eq_lemma = prove(
  ``!l1 (l2:('a#'b) list).
      (MAP FST l1 = MAP FST l2) /\ (MAP SND l1 = MAP SND l2) ==> (l1 = l2)``,
  Induct THEN SRW_TAC [][] THEN Cases_on `l2` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN Cases_on `h`  THEN
  FULL_SIMP_TAC (srw_ss()) []);

val last_elim_th = prove(
  ``!kvl1 kvl2 (fm':'a |-> 'b).
       (MAP FST kvl1 = MAP FST kvl2) /\ ALL_DISTINCT (MAP FST kvl1) ==>
       ((?fm. fm |++ kvl1 = fm' |++ kvl2) = (MAP SND kvl1 = MAP SND kvl2))``,
  Induct THEN1 SRW_TAC [][FUPDATE_LIST_THM] THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][] THEN Cases_on `kvl2` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN EQ_TAC THENL [
    SRW_TAC [][FUPDATE_LIST_THM] THENL [
      POP_ASSUM (MP_TAC o Q.AP_TERM `FAPPLY`) THEN
      DISCH_THEN (MP_TAC o C Q.AP_THM `FST h`) THEN
      Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `~(MEM q (MAP FST t))` by METIS_TAC [] THEN
      SRW_TAC [][FUPDATE_LIST_APPLY_NOT_MEM],
      METIS_TAC []
    ],
    STRIP_TAC THEN Q.EXISTS_TAC `fm'` THEN SRW_TAC [][FUPDATE_LIST_THM] THEN
    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
    SRW_TAC [][mappair_eq_lemma]
  ]);
end


fun check_for_final_elimination s lcs t = let
  (* t is of form ?v1 .. vn. (fm1 = fm2) /\ ...
     If fm1's only variable is of fmap type at the bottom of a chain of
     updates that matches up with those in fm2, and that variable doesn't
     occur anywhere else, eliminate it. *)
  val (vs, body) = strip_exists t
  val (fm_eq, others) = dest_conj body
  val lvars = HOLset.difference (FVL [lhs fm_eq] empty_tmset,  lcs)
  val fv = valOf (List.find (fn v => finite_mapSyntax.is_fmap_ty (type_of v))
                            (HOLset.listItems lvars))
  val other_fvs = FVL [others] empty_tmset
  val _ = if !tracing then print "FM: check_for_final_elimination ..." else ()
  val TRY_CONV =
      if !tracing then
        (fn c => fn t => c t before print "done!\n"
                    handle e as HOL_ERR _ => (print "failed!\n"; raise e)
                         | e as Conv.UNCHANGED =>
                           (print "no change!\n"; raise e))
      else TRY_CONV
  val ALL_CONV = if !tracing then (fn t => (print "no change!\n"; ALL_CONV t))
                 else ALL_CONV
in
  if mem fv vs andalso not (HOLset.member(other_fvs, fv)) then let
      fun push_down t = let
        val (v, bod) = dest_exists t
      in
        if v = fv then
          if is_exists bod then
            (SWAP_VARS_CONV THENC BINDER_CONV push_down) t
          else ALL_CONV t
        else
          BINDER_CONV push_down t
      end
    in
      TRY_CONV (push_down THENC
                LAST_EXISTS_CONV (EXISTS_AND_CONV THENC
                                  LAND_CONV (s [last_elim_th])))
    end
  else
    ALL_CONV
end t

fun MOVE_EXISTS_RIGHT_CONV tm = let
  val (vs, body) = strip_exists tm
in
  case vs of
    [] => failwith "MOVE_EXISTS_RIGHT_CONV"
  | [_] => ALL_CONV tm
  | v::others => let
      val new_order_vs = others @ [v]
      val new_rhs  = list_mk_exists(new_order_vs, body)
    in
      prove(mk_eq(tm, new_rhs),
            EQ_TAC THENL [
              DISCH_THEN (EVERY_TCL (map X_CHOOSE_THEN vs) ASSUME_TAC) THEN
              MAP_EVERY EXISTS_TAC new_order_vs THEN POP_ASSUM ACCEPT_TAC,
              DISCH_THEN (EVERY_TCL (map X_CHOOSE_THEN new_order_vs)
                                    ASSUME_TAC) THEN
              MAP_EVERY EXISTS_TAC vs THEN POP_ASSUM ACCEPT_TAC
            ])
    end
end

fun single_simple t = let
  open finite_mapSyntax
  val _ = if !tracing then print "FM: single_simple\n" else ()
  val (v, _) = dest_exists t
  val (k_ty, v_ty) = dest_fmap_ty (type_of v)
      handle HOL_ERR _ => raise ERR "single_simple" "Not looking at ?fm. ..."
  val (_, body) = strip_exists t
  val hdc = hd (strip_conj body)
  val e = ERR "single_simple" "first conjunct not of right form"
  val (l, r) = dest_eq hdc handle HOL_ERR _ => raise e
  val (fm, kvp) = dest_fupdate l
  val _ = fm = v orelse raise e
  val (key, value) = pairSyntax.dest_pair kvp
  val _ = same_const (#1 (dest_fupdate r)) fempty_t orelse raise e
  fun push_in_then c = MOVE_EXISTS_RIGHT_CONV THENC LAST_EXISTS_CONV c
  fun finish_off t = let
    fun findthis t = let
      val (fm', kvp) = dest_fupdate t
      val (key',_) = pairSyntax.dest_pair kvp
    in
      fm' = fm andalso (key' = key orelse
                        (WARN "single_simple"
                              "new finite map updates with different key";
                         false))
    end handle HOL_ERR _ => false
    val to_elim_l = find_terms findthis (rand body)
    val to_elim_s = HOLset.addList(empty_tmset, to_elim_l)
    val to_elim =
        case HOLset.numItems to_elim_s of
          0 => mk_fupdate(v, pairSyntax.mk_pair(key, genvar v_ty))
        | 1 => hd (HOLset.listItems to_elim_s)
        | _ => raise ERR "single_simple" "More than one update pattern"
    val strategy1 =
        BINDER_CONV (RAND_CONV (UNBETA_CONV to_elim)) THENC
        REWR_CONV FMEQ_SINGLE_SIMPLE_ELIM THENC
        RAND_CONV (RAND_CONV BETA_CONV)
    val strategy2 =
        BINDER_CONV
          (LAND_CONV (REWR_CONV FMEQ_SINGLE_SIMPLE_DISJ_ELIM THENC
                      RAND_CONV (REWR_CONV LEFT_AND_OVER_OR THENC
                                 RAND_CONV RIGHT_AND_EXISTS_CONV) THENC
                      REWR_CONV LEFT_AND_OVER_OR THENC
                      RAND_CONV RIGHT_AND_EXISTS_CONV) THENC
                     REWR_CONV RIGHT_AND_OVER_OR THENC
                     RAND_CONV LEFT_AND_EXISTS_CONV) THENC
        EXISTS_OR_CONV THENC
        BINOP_CONV Unwind.UNWIND_EXISTS_CONV
    (* strategy1 is preferable because it doesn't introduce a case split.
       However, it will fail if there are stray references to the
       finite map hanging around, as can happen if there are additional
       constraints on it.  In this case, strategy2 comes into play.  This
       involves taking a deep breath and introducing a known case split. *)
  in
    strategy1 ORELSEC strategy2
  end t
in
  push_in_then finish_off t
end





(* ----------------------------------------------------------------------

   Basic strategy:

   1.  Pull fmap-equality to front of body.
   2.  Orient fmap-equality so that ground term is on right.
   2a  Try to catch simple case early and rewrite with
         FMEQ_SINGLE_SIMPLE_ELIM
       this requires a little work to set up the higher order match by
       hand, and to move the fmap quantifier into just over the constraints.

   3a. Some of the LHS's keys may still be unground, try to esnure that
       the updates on the LHS are ordered such that all of the updates
       with ground keys are outermost.

       This process may generate extra inequalities between unground and
       ground keys.  For example, if we have

          fm |+ (2, 4) |+ (k, 3) = FEMPTY |+ (3,3) |+ (2, 4)

       then we can conclude that ~(k = 2) (the two maps wouldn't agree on
       what to map 2 to), and that we can therefore swap (k, 3) and (2, 4)
       on the LHS.

   3b. If after this, the finite map on the left still has a variable key
       as its outermost key, then try to find a concrete value for it
       by considering the values on the right.  E.g., in

          fm |+ (k, SOME x) = FEMPTY |+ (3, NONE) |+ (4, SOME 5)

       it's easy to conclude that k = 4 /\ x = 5.  It's even possible
       that this analysis will turn the whole conjunct into false
       (e.g., if the binding for four above was also to NONE)

   4.  a. If constraints in the body imply that a ground key from the
          LHS can not be elsewhere in the fmap, then use
          FUPD11_SAME_NEW_KEY to eliminate the update entirely.

       b. Otherwise, arrange the lists of ground key-value pairs on the
          LHS in some order, and arrange a matching list on the right.
          Derive equalities using FUPDATE_LIST_SAME_KEYS_UNWIND.  If the
          keys on the LHS are all ground, then also use the second
          consequence of the above, to eliminate other finite-map
          expressions involving the same base.  If this is possible, then
          the presumably quantified variable can be eliminated by
          pushing the exists in and providing the ground base as a witness.

   5.  Eliminate any new equalities, and then repeat 'til done.

   ----------------------------------------------------------------------

   These steps are implemented by the following bits of code:

   1.  Using markerLib.move_conj_left
   2.  check_fmeq
   2a. single_simple
   3a.    push_varkeys_inwards
   3b.    outermost_varkey_elim
   4a.    same_newkey_elim
   4b.    make_outers_common
          transform_to_updlist         -  fms now have common outer lists
          do_list_unwind               -  equates update lists

       If other fmaps are being eliminated, then
          check_for_other_eliminations -  to normalise other fmap expressions
          check_for_final_elimination  -  to get rid of lone equality

   All of the above is done (once) in fm_onestep.

   ---------------------------------------------------------------------- *)

fun is_fmap_eq lconsts v t = let
  val (l, r, ty) = dest_eq_ty t
in
  (is_fmap_ty ty andalso
   (grounded_fm lconsts l andalso free_in v r orelse
    grounded_fm lconsts r andalso free_in v l))
end handle HOL_ERR _ => is_fmap_eq lconsts v (#2 (dest_forall t))
    handle HOL_ERR _ => false

fun move_fmconj_left lconsts v body = let
  val conjs = strip_conj body
in
  if is_fmap_eq lconsts v (hd conjs) then ALL_CONV
  else markerLib.move_conj_left (is_fmap_eq lconsts v)
end body

val last_call = ref (concl TRUTH)
fun fm_onestep ctxt (simp_ : thm list -> conv) t = let
  val _ = last_call := t
  val (vs, _) = strip_exists t
  val v = hd vs
          handle Empty => raise ERR "fn_onestep" "Term not of form ?fm. ..."
  val _ = finite_mapSyntax.is_fmap_ty (type_of v) orelse
          raise ERR "fm_onestep" "Term not of form ?fm. ..."
  val kcompare = compare_from_reduce simp_
  val lconsts = HOLset.difference(FVL ctxt empty_varset,
                                  HOLset.fromList Term.compare vs)
  fun complicated_case t = let
    val c =
      TRY_CONV (STRIP_QUANT_CONV
                    (LAND_CONV (outermost_varkey_elim lconsts (simp_ []))) THENC
                try_all_unwinds) THENC
      REPEATC
        (STRIP_QUANT_CONV
           (LAND_CONV (push_varkeys_inwards lconsts (simp_ [])) THENC
            REWR_CONV (GSYM CONJ_ASSOC)) THENC
           try_all_unwinds) THENC
      TRY_CONV (STRIP_QUANT_CONV
                    (LAND_CONV (outermost_varkey_elim lconsts (simp_ []))) THENC
                try_all_unwinds) THENC
      ((STRIP_QUANT_CONV (same_newkey_elim lconsts simp_) THENC
        try_all_unwinds) ORELSEC
       (STRIP_QUANT_CONV (LAND_CONV (make_outers_common lconsts kcompare THENC
                                     transform_to_updlist lconsts THENC
                                     do_list_unwind simp_) THENC
                          TRY_CONV (REWR_CONV (GSYM CONJ_ASSOC))) THENC
        CHANGED_CONV (try_all_unwinds THENC
                      STRIP_QUANT_CONV
                          (check_for_other_eliminations lconsts simp_) THENC
                          check_for_final_elimination simp_ lconsts))) THENC
      numLib.REDUCE_CONV THENC
      REWRITE_CONV [FUPDATE_LIST_THM]
    val _ = if !tracing then
              print "FM: Having to do complicated analysis of finite map\n"
            else ()
  in
    CHANGED_CONV c t
  end
in
  STRIP_QUANT_CONV (move_fmconj_left lconsts v THENC
                    LAND_CONV (check_fmeq lconsts)) THENC
  (single_simple ORELSEC complicated_case)
end t

val _ = Parse.temp_set_grammars entry_grammars
(* test applications of fm_onestep

    open simpLib BasicProvers Net_fmap_analyse
    val simp_ = SIMP_CONV (srw_ss())
    val fm1 = time (fm_onestep [] simp_);


    fm1 ``?fm k x.
            P x /\ Q y /\
            (FEMPTY |+ (3, 2, 1) |+ (2, 2, 1) |+ (1, 1, 1) =
             fm |+ (2, u, w) |+ (3, 2, k) |+ (k, 1, x))``;

    fm1 ``?fm k x w.
             ~(3 IN FDOM fm) /\
             (fm |+ (3, x) |+ (k, 6) =
              FEMPTY |+ (1,2) |+ (2,2) |+ (3,4))``;

    fm1 ``?fm z v x.
            (fm |+ (3, z) |+ (2,1) |+ (v, 4) |+ (x, 5) =
             FEMPTY |+ (1,1) |+ (2,2) |+ (3,4) |+ (4,5) |+ (5,6)) /\
            P x y z /\
            ~(3 IN FDOM fm) /\ ~(2 IN FDOM fm) /\ ~(3 = v) /\ ~(x = 3)``;

    fm1 ``?fm v z x.
            (fm |+ (3, z) |+ (2,1) |+ (v, 4) |+ (x, 5) =
             FEMPTY |+ (1,1) |+ (2,2) |+ (3,4) |+ (4,5) |+ (5,6)) /\
            P x y z /\ ~(3 IN FDOM fm) /\ ~(2 IN FDOM fm) /\
            ~(3 = v)`` handle e => Raise e;

    fm1 ``?fm v x.
            (fm |+ (3, v) |+ (4, x) =
             FEMPTY |+ (1,2) |+ (3,4) |+ (2,2) |+ (4, 7)) /\
            P v x 5 /\
            Q (fm |+ (4, 9) |+ (3, x + 1))``;

   fm1 ``?fm. P k v fm /\ (FEMPTY |+ (2, 4) = fm |+ (k,v))``



*)


end (* struct *)
