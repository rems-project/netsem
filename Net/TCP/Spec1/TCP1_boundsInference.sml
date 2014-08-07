structure TCP1_boundsInference =
struct

(* code to perform bounds inference on arithmetic expressions that are not
   ground *)

open HolKernel boolLib bossLib
open TCP1_timersTheory TCP1_timerPropsTheory TCP1_rangeAnalysisTheory


fun myfind f [] = NONE
  | myfind f (h::t) = (case f h of NONE => myfind f t
                                 | x => x)

val ok_preserved = ticker_ok_preserved
val real_ss = realSimps.real_ss

val ticks_of_t = ``TCP1_timers$ticks_of``
val ticker_t = ``TCP1_timers$Ticker``
val tick_imin_t = ``TCP1_timers$tick_imin``
val tick_imax_t = ``TCP1_timers$tick_imax``
val ticker_ok_t = ``TCP1_timers$ticker_ok``
val srange_t = prim_mk_const {Thy = "TCP1_rangeAnalysis", Name = "srange"}
val rrange_t = ``TCP1_rangeAnalysis$rrange``
val irange_t = ``TCP1_rangeAnalysis$irange``
val nrange_t = ``TCP1_rangeAnalysis$nrange``

fun is_srange t = let
  val (f, args) = strip_comb t
in
  same_const f srange_t andalso length args = 3
end

fun is_range t = let
  val (f, args) = strip_comb t
in
  (same_const f srange_t orelse mem f [rrange_t, irange_t]) andalso
  length args = 3
end

fun infer_ticker_ok ths t = let
  (* ths is a list of theorems, including Time_Pass_ticker and
     ticker_ok terms; t is the desired argument to ticker_ok *)
  fun recurse t =
      case List.find (aconv t o concl) ths of
        NONE =>
        if is_var (rand t) then let
            val ok_preserved' = PART_MATCH (#2 o dest_imp) ok_preserved t
            val ok_froze = ADD_ASSUM (mk_eq (rand t, rand t)) ok_preserved'
            val selector = last o strip_conj o #1 o dest_imp
            fun finder th = Lib.total (PART_MATCH selector ok_froze) (concl th)
          in
            case myfind finder ths of
              NONE => raise Fail "Couldn't chain backwards"
            | SOME th' => let
                val new_objective = hd (strip_conj (#1 (dest_imp (concl th'))))
                val objective_th = recurse new_objective
              in
                PROVE_HYP (REFL (rand t))
                          (SIMP_RULE real_ss (objective_th :: ths) th')
              end
          end
        else
          EQT_ELIM (SIMP_CONV real_ss (ticker_ok_def::ths) t)
      | SOME th => th
in
  recurse (mk_comb(ticker_ok_t, t))
end

fun prove_zero_le t =
    EQT_ELIM (SIMP_CONV real_ss [] (realSyntax.mk_leq(realSyntax.zero_tm, t)))

val tpass_t = ``Time_Pass_ticker``

fun infer_one_big_ticker_passage ths start finish = let
  fun recurse start_ok start finish = let
    fun successor t = let
      val (f, args) = strip_comb (concl t)
    in
      same_const f tpass_t andalso
      aconv (List.nth(args, 1)) start
    end
    val start_successor_th = valOf (List.find successor ths)
    val tpass_start = concl start_successor_th
    val next = rand tpass_start
    val d = hd (#2 (strip_comb tpass_start))
    val zero_le_d = prove_zero_le d
  in
    if aconv next finish then
      (start_successor_th, zero_le_d)
    else let
        val next_ok =
            MATCH_MP ok_preserved
                     (LIST_CONJ [start_ok, zero_le_d, start_successor_th])
        val (next_to_finish, zero_le_d2) = recurse next_ok next finish
        val ex_concl =
            let val gv = genvar (type_of next)
            in
              mk_exists(gv, subst [next |-> gv]
                                  (mk_conj(tpass_start, concl next_to_finish)))
            end
        val ex_thm =
            EXISTS (ex_concl, next) (CONJ start_successor_th next_to_finish)
        val exist_preconds = LIST_CONJ [zero_le_d, zero_le_d2, start_ok]
        val eqn = MATCH_MP (INST [``t:ticker`` |-> rand (concl next_to_finish)]
                                 time_pass_exists_eliminate) exist_preconds
        val conclude_rhs = EQ_MP eqn ex_thm
        val d_d2 =
            SIMP_CONV real_ss []
                      (realSyntax.mk_plus(d, rand (concl zero_le_d2)))
        val zero_le_d_d2 = prove_zero_le (rand (concl d_d2))
      in
        (SIMP_RULE bool_ss [d_d2] conclude_rhs, zero_le_d_d2)
      end
  end
in
  #1 (recurse (infer_ticker_ok ths start) start finish)
end

fun look_back_for_passage ths t = let
  (* t is of type :ticker, find a theorem in ths that links forward to it *)
  fun finder th = let
    val (f, args) = strip_comb (concl th)
  in
    same_const f tpass_t andalso aconv (rand (concl th)) t
  end
in
  List.find finder ths
end

fun infer_iminmax ths t = let
  (* t is a term of type :ticker, for which constraints of the form
       tick_imin t = v1
     and
       tick_imax t = v2
     are desired *)
  fun recurse t =
      if same_const (rator t) ticker_t handle HOL_ERR _ => false then
        (REWR_CONV tick_imin_def (mk_comb(tick_imin_t, t)),
         REWR_CONV tick_imax_def (mk_comb(tick_imax_t, t)))
      else let
          fun finder f th =
              is_eq (concl th) andalso
              aconv (lhs (concl th)) (mk_comb(f, t))
        in
          case (List.find (finder tick_imin_t) ths,
                List.find (finder tick_imax_t) ths)
           of
            (SOME th1, SOME th2) => (th1, th2)
          | (NONE, NONE) => let
              val passage = valOf (look_back_for_passage ths t)
                            handle Option => raise Fail "No backward chain"
              val prev = rand (rator (concl passage))
              val (prev_min, prev_max) = recurse prev
              val (pres_min, pres_max) =
                  CONJ_PAIR (MATCH_MP tick_imin_imax_preserved passage)
            in
              (TRANS pres_min prev_min, TRANS pres_max prev_max)
            end
          | _ => raise Fail "infer_iminmax: huh?"
        end
in
  recurse t
end

fun infer_ticks_of_constraint ths t = let
  (* t is a term of type :ticker, for which a constraint of the form
       srange (ticks_of t) s n
     is desired.  If n = 0, this can then be turned into ticks_of t = s
  *)
  fun lookfor_eq ths t = let
    (* look for an equality of the form
         ticks_of t = value
       as "near" as possible to t in the sequence of Time_Pass_ticker links *)
    val ticks_of_term = mk_comb(ticks_of_t, t)
    fun finder th = let
      val c = concl th
    in
      is_eq c andalso aconv ticks_of_term (lhs c)
    end
  in
    case List.find finder ths of
      SOME th => th
    | NONE => let
      in
        case look_back_for_passage ths t of
          NONE => raise Fail "Couldn't chain backwards"
        | SOME th => lookfor_eq ths (rand (rator (concl th)))
      end
  end
  val base_eqn = lookfor_eq ths t
  val base_tick = rand (lhs (concl base_eqn))
  val base_ok = infer_ticker_ok ths base_tick
  val passage = infer_one_big_ticker_passage (base_ok::ths) base_tick t
  val (imin_eqn, imax_eqn) = infer_iminmax ths base_tick
  val bounds0 = MATCH_MP infer_ticker_bounds (CONJ passage base_ok)
  val bounds =
      SIMP_RULE real_ss [base_eqn, imin_eqn, imax_eqn] bounds0
  val simp = SIMP_CONV real_ss [num_floor_eqns]
  (* the ORELSEC in lower_bound and the TRY_CONV in upper_bound are necessary
     because of the possibility that the divisions in bounds0 will simplify
     in bounds to natural numbers giving rise initially to expressions of the
     form
        real-numeral < (&)var
     and thus to
        nat-numeral < var
     In neither case (upper or lower) will a num_floor expression be
     applicable.  In the lower bound case the < needs turning into a <= *)
  val lower_bound =
      (REWR_CONV num_floor_lower_bound THENC LAND_CONV simp) ORELSEC
      (REWR_CONV arithmeticTheory.LESS_EQ THENC
       LAND_CONV numLib.REDUCE_CONV)
  val upper_bound =
      TRY_CONV (REWR_CONV num_floor_upper_bound THENC RAND_CONV simp)
  val bounds =
      CONV_RULE
        (BINDER_CONV (RAND_CONV (FORK_CONV(lower_bound, upper_bound))))
        bounds
  val bounds = SIMP_RULE real_ss [into_srange] bounds
in
  SIMP_RULE std_ss [TCP1_baseTypesTheory.seq32_plus_def,
                    word32Theory.ADD_EVAL] bounds
end

val ticker_ty = mk_thy_type {Thy = "TCP1_timers", Tyop = "ticker", Args = []}

fun intersectP tmset P =
    HOLset.foldl (fn (e,acc) => if P e then HOLset.add(acc, e) else acc)
                 empty_tmset tmset

fun augment_theorem th = let
  (* augment a transition theorem with a ticks_of constraint for those
     tickers that don't already have them. *)
  val hypfvs = hyp_frees th
  val free_tickers = intersectP hypfvs (fn v => type_of v = ticker_ty)
  fun is_tick_of_eqn t =
      (* is t either of the form  ticks_of t = v
         or srange (ticks_of t) v sz *)
      (is_eq t andalso same_const ticks_of_t (rator (lhs t))) orelse
      (let val (f, args) = strip_comb t in
         same_const srange_t f andalso
         same_const (rator (hd args)) ticks_of_t
       end) handle HOL_ERR _ => false

  val ticks_of_equalities = intersectP (hypset th) is_tick_of_eqn
  fun constraint_to_var t =
      if is_eq t then rand (lhs t)       (* ticks_of t = v *)
      else rand (hd (#2 (strip_comb t))) (* srange (ticks_of t) b sz *)
  fun foldthis (eqn, acc) = HOLset.add(acc, constraint_to_var eqn)
  val ticks_with_eqns = HOLset.foldl foldthis empty_tmset ticks_of_equalities
  val ticks_to_do = HOLset.difference (free_tickers, ticks_with_eqns)
  fun do_one(t,(newths, ths)) = let
    val newth = infer_ticks_of_constraint ths t
  in
    (newth :: newths, newth :: ths)
  end handle Fail _ => (newths, ths)
  val newths = if HOLset.isEmpty ticks_of_equalities then
                 []
               else
                 #1 (HOLset.foldl do_one ([], map ASSUME (hyp th)) ticks_to_do)
in
  List.foldl (uncurry ADD_ASSUM) th (map concl newths)
end

(* like find_term but doesn't look for matching sub-terms inside terms that
   have already satisfied the predicate, also only looks into the guards
   of conditional expressions  *)
fun find_maximal_terms P t = let
  fun recurse acc t =
      if P t then HOLset.add(acc, t)
      else if is_cond t then recurse acc (hd (#2 (strip_comb t)))
      else
        case dest_term t of
          COMB(t1, t2) => recurse (recurse acc t2) t1
        | LAMB(t1, t2) => recurse acc t2
        | _ => acc
in
  HOLset.listItems (recurse empty_tmset t)
end


(* ----------------------------------------------------------------------
    a simple prolog-style engine that proceeds by iterative deepening
     * no cut
   ---------------------------------------------------------------------- *)

fun myinst i t =
    repeat (fn t => let val t' = Term.subst i t
                    in
                      if aconv t t' then failwith "foo" else t'
                    end)
    t

fun myINST i th =
    repeat (fn th => let val th' = Thm.INST i th
                     in
                       if aconv (concl th') (concl th) then failwith "foo"
                       else th'
                     end)
    th

fun gSPEC_ALL th =
    if is_forall (concl th) then
      gSPEC_ALL (SPEC (genvar (type_of (#1 (dest_forall (concl th))))) th)
    else th

fun unify consts t1 t2 env success fail =
    (* assumes t1 and t2 have same type *)
    case Lib.total (Unify.simp_unify_terms_in_env consts t1 t2) env of
      SOME i => success i
    | NONE => fail ()

type env = (term, term)subst

fun prolog db c max t = let

  fun try_simp t (success : thm -> 'a) (fail : unit -> 'a) =
      case Lib.total EQT_ELIM (QCONV c t) of
        SOME th => success th
      | NONE => fail ()



  fun find_match (cs, dbths) env t success fail = let
    fun filterthis th =
        can (Unify.simp_unify_terms [] (#2 (strip_imp (concl (SPEC_ALL th)))))
            t
    val possibles = List.filter filterthis dbths
    fun scan [] = try_simp t (fn th => success (env, th) fail) fail
      | scan (th::ths) = let
          val base = gSPEC_ALL th
          fun failc () = scan ths
          fun succ i = let
            val ith = myINST i base
          in
            success (i,ith) failc
          end
        in
          unify cs t (#2 (strip_imp (concl base))) env succ failc
        end
  in
    if null possibles then try_simp t (fn th => success (env, th) fail) fail
    else scan possibles
  end

  fun solve_hyps db n (pthm as (env, th)) (success : env * thm -> 'a) fail =
      if is_imp (concl th) then
        if 0 < n then let
            val goals = strip_conj (#1 (dest_imp (concl th)))
            fun succ (e, thl) = success (e, MP (myINST e th) (LIST_CONJ thl))
          in
            prolog_andl db (n - 1) env goals succ fail
          end
        else fail ()
      else success pthm
  and prolog_andl db n env goals (success : env * thm list -> 'a) fail =
      case goals of
        [] => success (env, [])
      | g::gs => let
          fun succ (e0, matched_th) fail = let
            fun after_hyps_solved (e1, th) =
                prolog_andl db n e1 (map (myinst e1) gs)
                            (fn (e2, ths) => success (e2, th::ths))
                            fail
          in
            solve_hyps db n (e0, matched_th) after_hyps_solved fail
          end
        in
          find_match db env g succ fail
        end

  fun search n = if n < max then
                   prolog_andl db n [] [t] (hd o #2) (fn () => search (n + 1))
                 else failwith "Search depth exceeded"
in
  search 0
end

(* ----------------------------------------------------------------------
    use prolog engine to derive new constraints on "interesting" terms
    within the goal.
   ---------------------------------------------------------------------- *)

val irange_th = prove(
  ``srange v b sz /\
    sz < 2147483648 /\ ABS (b - w) < 1073741824 /\
    ABS (b + sz - w) < 1073741824 ==>
    irange (v:tstamp seq32 - w) (b - w) sz``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ranged_seq32_sub THEN
  ASM_REWRITE_TAC []);

val base_db_ths =
    map GEN_ALL [irange_th, irange_real_of_int,

                 rrange_posdiv, rrange_plus,
                 rrange_sub, rrange_negate, rrange_min, rrange_max,
                 rrange_abs1, rrange_abs2, rrange_abs3,
                 rrange_lmult, rrange_rmult,

                 nrange_intro, nrange_plus, nrange_sub, nrange_max,
                 nrange_min, nrange_rounddown, nrange_cond] @
    map GEN_ALL (CONJUNCTS rrange_literals) @
    map GEN_ALL (CONJUNCTS nrange_literals);

fun vreal n = mk_var(n, realSyntax.real_ty)
fun vint n = mk_var(n, intSyntax.int_ty)
fun vnum n = mk_var(n, numSyntax.num)
fun give_range t =
    if type_of t = intSyntax.int_ty then
      list_mk_comb(irange_t, [t, vint "x", vnum "n"])
    else if type_of t = realSyntax.real_ty then
      list_mk_comb(rrange_t, [t, vreal "x", vreal "y"])
    else if type_of t = numSyntax.num then
      list_mk_comb(nrange_t, [t, vnum "x", vnum "y"])
    else raise mk_HOL_ERR "TCP1_boundsInference" "give_range" "Unexpected type"

fun good_asm t = is_range t orelse numSyntax.is_leq t

fun infer_other_constraints simp th = let
  open HOLset
  val hyps = hypset th
  val c = concl th
  val interesting_asms = intersectP hyps good_asm
  val asm_vars =
      foldl (fn (t,acc) => FVL [t] acc) empty_tmset interesting_asms
  fun not_letcomp_value t =
      not (is_comb t andalso same_const (rator t) LetComputeLib.value_t)
  fun interesting_term_in_concl t = (* just boolean test *)
      not_letcomp_value t andalso
      ((mem (type_of t) [intSyntax.int_ty, realSyntax.real_ty] andalso
        not (isEmpty (intersection(asm_vars, FVL [t] empty_tmset))))
       orelse
       (type_of t = numSyntax.num andalso not (null (free_vars t))))
  fun collect_interesting_terms_in_asm(t, acc) =
      if LetComputeLib.is_pending t andalso
         mem (type_of (rhs (rand t))) [numSyntax.num, realSyntax.real_ty]
      then HOLset.add(acc, rhs (rand t))
      else acc

  fun cmp(t1, t2) = Int.compare(term_size t1, term_size t2)
  val interesting_terms =
      Listsort.sort cmp (find_maximal_terms interesting_term_in_concl c @
                         listItems (foldl collect_interesting_terms_in_asm
                                          empty_tmset hyps))

  val hypfvs = HOLset.listItems asm_vars
  fun infer_one (t, (news, all)) = let
    val new_asm_form = give_range t
    val new_asm0 = prolog (free_vars t @ hypfvs, all) simp 10 new_asm_form
    val new_asm = CONV_RULE simp new_asm0
    val other_news =
        if mem (#1 (dest_const (#1 (strip_comb new_asm_form))))
               ["rrange", "nrange"]
        then
          CONJUNCTS (CONV_RULE
                       (REWRITE_CONV [rrange_def, nrange_def] THENC
                        simp) new_asm)
        else []
    val new_asms = new_asm :: other_news
  in
    (new_asms @ news, new_asms @ all)
  end handle HOL_ERR _ => (news, all)
  val (new_asms, _) =
      List.foldl infer_one
                 ([], map ASSUME (listItems interesting_asms) @ base_db_ths)
                 interesting_terms
in
  List.foldl (fn (newth, baseth) => ADD_ASSUM (concl newth) baseth)
             th new_asms
end



(*

val ths = map ASSUME [
  ``Time_Pass_ticker (18219 / 500000)
                     (Ticker (t0,remdr0,1/105,21 / 2000)) ticks'``,
  ``remdr0:real < 21/2000``, ``0r <= remdr0:real``,
  ``Time_Pass_ticker (9987 / 1000000) ticks' ticks'1``,
  ``Time_Pass_ticker (369 / 1000000) ticks'1 ticks'2``,
  ``Time_Pass_ticker (283 / 100000) ticks'2 ticks'3``,
  ``Time_Pass_ticker (303 / 1000000) ticks'3 ticks'4``,
  ``Time_Pass_ticker (117 / 1000000) ticks'4 ticks'5``,
  ``ticks_of ticks'3 = SEQ32 Tstamp 395833474w``,
  ``Time_Pass_ticker (9 / 500000) ticks'5 ticks'6``,
  ``Time_Pass_ticker (325913 / 1000000) ticks'6 ticks'7``,
  ``Time_Pass_ticker (59 / 500000) ticks'7 ticks'8``,
  ``Time_Pass_ticker (33 / 1000000) ticks'8 ticks'9``,
  ``Time_Pass_ticker (81 / 1000000) ticks'9 ticks'10``,
  ``ticks_of ticks'8 = SEQ32 Tstamp 395833507w``,
  ``Time_Pass_ticker (1747 / 250000) ticks'10 ticks'11``,
  ``Time_Pass_ticker (31103 / 1000000) ticks'11 ticks'12``,
  ``Time_Pass_ticker (171 / 250000) ticks'12 ticks'13``,
  ``Time_Pass_ticker (511 / 200000) ticks'13 ticks'14``,
  ``Time_Pass_ticker (449 / 1000000) ticks'14 ticks'15``,
  ``Time_Pass_ticker (2573 / 1000000) ticks'15 ticks'16``,
  ``Time_Pass_ticker (81 / 100000) ticks'16 ticks'17``,
  ``Time_Pass_ticker (89 / 1000000) ticks'17 ticks'18``,
  ``ticks_of ticks'18 = SEQ32 Tstamp 395833511w``,
  ``Time_Pass_ticker (83 / 1000000) ticks'18 ticks'19``,
  ``Time_Pass_ticker (163 / 1000000) ticks'19 ticks'20``,
  ``Time_Pass_ticker (43137 / 250000) ticks'20 ticks'21``,
  ``Time_Pass_ticker (87 / 1000000) ticks'21 ticks'22``]
val t = ``ticks'22 : ticker``

*)


end; (* struct *)
