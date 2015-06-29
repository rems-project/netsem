(* A HOL98 specification of TCP *)

(* The symbolic evaluator itself *)

(* see README.testing for usage instructions *)

(* Expansion phases are as follows:

   0: Initial simplification of host and labels

   1: Abbreviations that don't expand into things that are too large;
      e.g., auto_outroute OK but make_ack_segment not.  Hopefully this
      gets rid of lots of irrelevant stuff, and doesn't blow up very
      much.

   2: Expands bigger things, hoping that by this time we are down to
      only one or two rules.

   3: Time-passage rewrites.

   Note that phase 2 includes all of phase 1, and phase 3 includes all
   of phase 2 and phase 1.  Phase 0 stands on its own.

*)

open HolKernel Parse boolLib

open TCP1_evalSupportTheory NetEvalTheory TCP1_bettersTheory
open LetComputeLib

open BasicProvers simpLib

local open numLib pred_setLib pairLib realSimps intLib in end

open TextIO

val _ = Version.register "$RCSfile: testEval.sml,v $" "$Revision: 1.230 $" "$Date: 2007/06/18 03:41:20 $";

val _ = Globals.priming := SOME ""

(* ----------------------------------------------------------------------
    Output routines
   ---------------------------------------------------------------------- *)

val outputtingTiming = ref false

val toStdOut = ref false  (* should output just go to stdout, rather than file? *)

val output = (fn (hnd, s) => (output(hnd, s); flushOut hnd))
val print = (fn s => (print s; flushOut TextIO.stdOut))

fun output_and_print (hnd,s) =
  if !toStdOut then
      print s
  else
      (output (hnd,s); print s)

fun mytrace(hnd, s) = if !outputtingTiming then output(hnd, s) else ()

val outputtingHtml = ref (not (!Globals.interactive))
fun htmlOutput hnd s = if !outputtingHtml then output (hnd,s) else ()
fun textOutput hnd s = if !outputtingHtml then () else output (hnd,s)
fun altOutput hnd shtml stxt = output (hnd,if !outputtingHtml then shtml else stxt)

(* the classic control construct *)
fun try_finally f1 f2 =
  let val r = f1 () handle exn => (f2 (); raise exn)
  in
    f2 (); r
  end

(* given a theorem, find the string of its rule_id *)
fun rule_name th =
    #1 (dest_const (find_term (fn t => type_of t = ``:rule_ids`` andalso
                                       is_const t) (concl th)))
    handle HOL_ERR _ => "(rule with no name??)"


(* ----------------------------------------------------------------------
    backtracking control

    If btrack_control is set to SOME x, then the start of a trace will
    set btrack_node_count_limit to some positive number.

    Each time spec_n_simp or do_epsilon is called (representing
    entering a node in the "trace tree") the reference is reduced.  If
    it gets to zero then the two functions mentioned above will raise
    ExcessiveBackTracking.

   ---------------------------------------------------------------------- *)

datatype btrack_control = PercentExtra of int | AbsExtra of int

val btrack_control = ref (NONE : btrack_control option)

val btrack_node_count_limit = ref ~1

exception ExcessiveBackTracking

fun check_btrack hnd =
  case !btrack_node_count_limit of
    0 => (output(hnd, "== Excessive Backtracking!!\n");
          raise ExcessiveBackTracking)
  | ~1 => ()
  | _ => (btrack_node_count_limit := !btrack_node_count_limit - 1;
          output(hnd, "== Backtrack limit counts down to "^
                      Int.toString (!btrack_node_count_limit)^"\n"))

val eliminable_cond_size = 20
val eliminable_disj_size = 50

(* ----------------------------------------------------------------------
    Useful bits and pieces :

    Trivial but important rewrites (probably should be proved elsewhere,
    and imported).
   ---------------------------------------------------------------------- *)

val setify_rwt =
    (* turns a rewrite of the form
         |- !x1..xn. f x y z = <rhs>
       into
         |- z IN f x y = <rhs>
       (drops all universal quantification)
    *)
    CONV_RULE (LAND_CONV (REWR_CONV (GSYM pred_setTheory.SPECIFICATION))) o
    SPEC_ALL

(* boolean tautologies *)
val F_and_l = tautLib.TAUT_PROVE ``(F /\ t) = F``
val F_and_r = tautLib.TAUT_PROVE ``(t /\ F) = F``
val T_and_l = tautLib.TAUT_PROVE ``(T /\ t) = t``
val T_and_r = tautLib.TAUT_PROVE ``(t /\ T) = t``
val T_or_l = tautLib.TAUT_PROVE ``(T \/ t) = T``
val F_or_l = tautLib.TAUT_PROVE ``(F \/ t) = t``

(* stuff about sets *)
val IN_ABS = Phase.phase_imm 1 (prove(
  ``(x IN (\y. P y)) = P x``,
  SIMP_TAC bool_ss [IN_DEF]))

val gspec_empty = Phase.phase_imm 1 (prove(
  ``(GSPEC f = {}) = (!x. ~(x IN GSPEC f))``,
  REWRITE_TAC [pred_setTheory.EXTENSION, pred_setTheory.NOT_IN_EMPTY]));
val gspec_empty' = Phase.phase_imm 1 (CONV_RULE (LAND_CONV SYM_CONV) gspec_empty)

val ho_gspec_F = Phase.phase_imm 1 (prove(
  ``GSPEC (\x. (f x, F)) = {}``,
  SRW_TAC [][pred_setTheory.EXTENSION]));
val list_to_set_eq_empty = Phase.phase_imm 1 (prove(
  ``(LIST_TO_SET s = {}) = (s = [])``,
  Q.ISPEC_THEN `s` STRUCT_CASES_TAC listTheory.list_CASES  THEN
  SRW_TAC [][]));

val insert_inter_eq_empty = Phase.phase_imm 1 (prove(
  ``((x INSERT P) INTER Q = {}) = (~(x IN Q) /\ (P INTER Q = {}))``,
  REWRITE_TAC [pred_setTheory.EXTENSION, EQ_IMP_THM,
               pred_setTheory.IN_INSERT, pred_setTheory.IN_INTER,
               pred_setTheory.NOT_IN_EMPTY] THEN
  BasicProvers.PROVE_TAC []));

fun gspec_eq_empty t = let
  val (gs, f) = dest_comb t
  val _ = assert (same_const pred_setSyntax.gspec_tm) gs
  val (bvar_t, body_t) = pairSyntax.strip_pabs f
  val (img, condition) = pairSyntax.dest_pair body_t
in
  if condition = boolSyntax.F then let
      val goal = mk_eq(t, inst [alpha |-> #1 (dom_rng (type_of t))]
                               pred_setSyntax.empty_tm)
    in
      prove(goal, REWRITE_TAC [pred_setTheory.EXTENSION,
                               pred_setTheory.NOT_IN_EMPTY] THEN
                  GEN_TAC THEN
                  CONV_TAC (RAND_CONV pred_setLib.SET_SPEC_CONV) THEN
                  REWRITE_TAC [])
    end
  else
    raise mk_HOL_ERR "testEval" "gspec_eq_empty" "Set not (obviously) empty"
end

val GSPEC_ss = SSFRAG {ac = [], congs = [],
                        convs = [{conv = K (K gspec_eq_empty),
                                  key = SOME ([], ``pred_set$GSPEC f``),
                                  trace = 2, name = "gspec_eq_empty"}],
                        dprocs = [], filter = NONE, rewrs = [],
                        name = SOME "testEval.GSPEC_ss" }


(* options *)
val option_cond_thms = prove(
  ``!P x y z. (NONE = if P then NONE else SOME x) = P /\
              (NONE = if P then SOME x else NONE) = ~P /\
              (NONE = if P then SOME x else SOME y) = F /\
              (SOME x = if P then SOME y else SOME z) =
                (x = if P then y else z) /\
              (SOME x = if P then SOME y else NONE) = (P /\ x = y) /\
              (SOME x = if P then NONE else SOME y) = (~P /\ x = y)``,
  REPEAT GEN_TAC THEN Q.ASM_CASES_TAC `P` THEN
  ASM_REWRITE_TAC [optionTheory.option_CLAUSES]);

val IS_SOME_IMP_ELIM = prove(
  ``!P v. (IS_SOME v ==> P v) = (!n. (v = SOME n) ==> P (SOME n))``,
  REPEAT GEN_TAC THEN Cases_on `v` THEN
  SRW_TAC [][]);

val option_case_equalities = prove(
  ``((NONE = option_CASE v NONE (\v. SOME (f v))) = (v = NONE)) /\
    ((option_CASE v NONE (\v. SOME (f v)) = NONE) = (v = NONE)) /\
    ((option_CASE v NONE (\v. SOME (f v)) = SOME u) =
        ?x. (v = SOME x) /\ (u = f x)) /\
    ((NONE = option_CASE v (SOME x) (\v. NONE)) = ?x. (v = SOME x)) /\
    ((SOME u = option_CASE v (SOME x) (\v. NONE)) =
        ((v = NONE) /\ (u = x)))``,
  Cases_on `v` THEN SRW_TAC [][] THEN PROVE_TAC []);
val _ = Phase.phase_imm 1 option_case_equalities

(* lists *)
val existential_append_idiom0 = prove(
  (* this appears in deliver_in_3 *)
  ``!l1 conc. (conc = APPEND l1 (k :: l2)) =
              case conc of
                [] => F
              | h::t => (k = h) /\ (t = l2) /\ (l1 = []) \/
                        (?l1'. (l1 = h::l1') /\ (t = APPEND l1' (k :: l2)))``,
  Induct THEN SRW_TAC [][] THEN Cases_on `conc` THEN
  SRW_TAC [][] THEN PROVE_TAC [])

val existential_append_idiom = let
  val base = SPEC_ALL existential_append_idiom0
  (* only provide one specialisation, because the nil case
        [] = APPEND l1 (k :: l2)
     is already handled by the built-in rewrites, which know that
        ([] = APPEND l1 l2) = (l1 = []) /\ (l2 = [])
     and so rewrite the former to false without any extra help *)
in
  Phase.phase_imm 1
                  (SIMP_RULE (srw_ss()) [] (Q.INST [`conc` |-> `h::t`] base))
end

val _ = Phase.phase_imm 1 listTheory.LENGTH_NIL
val _ = Phase.phase_imm 1 (CONV_RULE (BINDER_CONV (LAND_CONV
                                                     (REWR_CONV EQ_SYM_EQ)))
                                     listTheory.LENGTH_NIL)

(* these right and lift shift operators should be replaced with those
   already provided by word<n>Theory *)
val right_shift_zero = Phase.phase_imm 1 (prove(
  ``(n >> 0) : num = n``,
  SRW_TAC [][TCP1_utilsTheory.right_shift_num_def]));
val left_shift_zero = Phase.phase_imm 1 (prove(
  ``(n << 0) : num = n``,
  SRW_TAC [][TCP1_utilsTheory.left_shift_num_def]));

(* onlywhen combinator *)
val onlywhen_rwts = Phase.phase_imm 1 (prove(
  ``(x onlywhen T = K x) /\ (x onlywhen F = I)``,
  REWRITE_TAC [TCP1_utilsTheory.onlywhen_def]));

(* words *)

(* this rewrite is an efficiency disaster; not sure why it was
   included
val word32_mod = Phase.phase_imm 1 (prove(
  ``4294967296 <= n ==> n2w n:word32 = n2w (n MOD 4294967296)``,
  SIMP_TAC (srw_ss()) [word32Theory.n2w_11, word32Theory.MOD_WL_def,
                       word32Theory.WL_def, word32Theory.HB_def]));
*)

(* dummies *)
val _ = Phase.phase_imm
          0
          (SIMP_RULE (srw_ss()) []
                             TCP1_evalSupportTheory.dummy_cb_def);


(* TAKE *)
val TAKE_EQ_THM = Phase.phase_imm 1 (prove(
  ``!n l m. (TAKE n l = m) = (LENGTH m < LENGTH l /\ (n = LENGTH m) /\
                              (?l0. (l = APPEND m l0)) \/
                             (l = m) /\ LENGTH m <= n)``,
  Induct THENL [
    SIMP_TAC (srw_ss()) [TCP1_utilPropsTheory.TAKE_THM] THEN
    REPEAT GEN_TAC THEN Cases_on `m` THEN
    SIMP_TAC (srw_ss()) [] THEN Cases_on `l` THEN
    SIMP_TAC (srw_ss()) [],
    REPEAT GEN_TAC THEN Cases_on `m` THEN
    Cases_on `l` THEN
    ASM_SIMP_TAC (srw_ss()) [TCP1_utilPropsTheory.TAKE_THM] THEN
    mesonLib.MESON_TAC []
  ]))





(* arithmetic *)
val DIV_LESS_EQ' = Phase.phase_imm 1 let
  open simpLib BasicProvers arithmeticTheory
  val rwt =
      CONV_RULE
        (LAND_CONV
           (SIMP_CONV bool_ss [NUMERAL_DEF, BIT1, BIT2,
                               ADD_CLAUSES, prim_recTheory.LESS_0]) THENC
         REWRITE_CONV [])
in
  CONJ (rwt (Q.SPEC `NUMERAL (BIT1 n)` DIV_LESS_EQ))
       (rwt (Q.SPEC `NUMERAL (BIT2 n)` DIV_LESS_EQ))
end

val LT_DIV = Phase.phase_imm 1 (REWRITE_RULE [GSYM arithmeticTheory.NOT_LESS] DIV_LESS_EQ')

(*
val min_eq = prove(
  ``(a = MIN b c : num) = if a = b then b <= c else a = c /\ c <= b``,
  REWRITE_TAC [arithmeticTheory.MIN_DEF] THEN numLib.ARITH_TAC);

val max_eq = prove(
  ``(a = MAX b c : num) = if a = b then c <= b else a = c /\ b <= c``,
  REWRITE_TAC [arithmeticTheory.MAX_DEF] THEN numLib.ARITH_TAC);

val MIN_EQ = Phase.phase_imm 1 (
             CONJ (REWR_CONV min_eq ``NUMERAL n = MIN (NUMERAL m) c``)
                  ((RAND_CONV (REWR_CONV arithmeticTheory.MIN_COMM) THENC
                    REWR_CONV min_eq) ``NUMERAL n = MIN b (NUMERAL m)``))
val MAX_EQ = Phase.phase_imm 1 (
             CONJ (REWR_CONV max_eq ``NUMERAL n = MAX (NUMERAL m) c``)
                  ((RAND_CONV (REWR_CONV arithmeticTheory.MAX_COMM) THENC
                    REWR_CONV max_eq) ``NUMERAL n = MAX b (NUMERAL m)``))
*)
val _ = Phase.phase_imm 1 arithmeticTheory.MAX_DEF
val _ = Phase.phase_imm 1 arithmeticTheory.MIN_DEF

val clip_int_to_num_injection = Phase.phase_imm 1 (prove(
  ``clip_int_to_num ((&) n) = n``,
  REWRITE_TAC [TCP1_utilsTheory.clip_int_to_num_def, integerTheory.NUM_OF_INT,
               integerTheory.INT_LT_CALCULATE, prim_recTheory.NOT_LESS_0]))

(* this is a very inefficient rewrite; but also useful.  Plan to replace
   it with tailored search for anti-symmetry pairs in context normalisation
val num_leq_antisym = Phase.phase_imm 1 (prove(
  ``x:num <= y ==> ((y <= x) = (x = y))``,
  numLib.ARITH_TAC));
*)

(* normalise < to <= *)
val lt_to_le = Phase.phase_imm 1 (prove(
  ``((x:num) < (y:num)) = (x + 1 <= y)``,
  numLib.ARITH_TAC));

val MAX_MIN_MAX = Phase.phase_imm 1 (prove(
  (* this pattern often seems to appear *)
  ``x <= y ==> (MAX (x:real) (MIN y (MAX x z)) = MIN y (MAX x z))``,
  SIMP_TAC (srw_ss()) [realTheory.max_def, realTheory.min_def] THEN
  Cases_on `x <= z` THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
    Cases_on `y <= z` THEN ASM_SIMP_TAC (srw_ss()) [],
    Cases_on `y <= x` THEN ASM_SIMP_TAC (srw_ss()) []
  ]));


val tcp_seq_flip = prove(
  ``tcp_seq_foreign_to_local (SEQ32 TcpForeign w) = SEQ32 TcpLocal w /\
    tcp_seq_local_to_foreign (SEQ32 TcpLocal w) = SEQ32 TcpForeign w``,
  SRW_TAC [][TCP1_baseTypesTheory.tcp_seq_foreign_to_local_def,
             TCP1_baseTypesTheory.tcp_seq_local_to_foreign_def,
             TCP1_baseTypesTheory.seq32_coerce_def, tcp_ARB]);


(* ----------------------------------------------------------------------
    conversion for calculating tcp_reass_q_ok quickly
   ---------------------------------------------------------------------- *)

local
  val qok_t = ``TCP1_betters$tcp_reass_q_ok``
  val seq_fld = ``TCP1_hostTypes$tcpReassSegment_seq_fupd``
  val data_fld = ``TCP1_hostTypes$tcpReassSegment_data_fupd``
  fun get_fld fld t = let
    val (f, args) = strip_comb t
  in
    if same_const f fld then rand (hd args)
    else get_fld fld (hd (tl args))
  end
  fun sq2num s = numSyntax.dest_numeral (rand (rand s))

  val s32_cons = ``TCP1_baseTypes$SEQ32 TcpForeign``
  fun mk_seq n =
      mk_comb(s32_cons, mk_comb(``word32$n2w``, numSyntax.mk_numeral n))

  val defn = TCP1_bettersTheory.tcp_reass_q_ok_def
in

fun calc_tcp_reass_q_ok_CONV simp t = let
  fun cmp (n1, n2) = if Arbnum.<(n1, n2) then LESS
                     else if n1 = n2 then EQUAL
                     else GREATER
  val (f, q) = dest_comb t
  val _ = assert (same_const qok_t) f
  val (elements, _) = listSyntax.dest_list q
  fun calculate_hits(e, acc) = let
    open Arbnum
    val sq = sq2num (get_fld seq_fld e)
    val data = get_fld data_fld e
    val dlen = fromInt (length (#1 (listSyntax.dest_list data)))
    val stop = sq + dlen
    fun insert_em n acc = if n = stop then acc
                          else insert_em (n + one) (HOLset.add(acc, n))
  in
    insert_em sq acc
  end
  val hits = List.foldl calculate_hits (HOLset.empty cmp) elements
  fun find_gap n = if HOLset.member(hits, n) then
                     find_gap (Arbnum.+(n, Arbnum.one))
                   else n
  val gap = find_gap Arbnum.zero
  val gap_s = mk_seq gap
  fun prove_exists witness t = let
    val (v, bod) = dest_exists t
  in
    EQT_INTRO (EXISTS(t, witness) (EQT_ELIM (simp (subst [v|->witness] bod))))
  end
in
  REWR_CONV defn THENC prove_exists gap_s
end t

end (* local *)



(* ----------------------------------------------------------------------
    sf_default_b (and descendents) as a set

     needed because the bound_ports_protocol and
     bound_ipports_protocol use a sockbflag as a set (with IN) rather
     than as a characteristic function, which is the way it is
     defined.  This code gives us a version of the definition that
     uses the IN notation.  The sockflags are updated by use of the
     funupd constant, so that terms such as

         FOO IN funupd_thm f x v

     will also arise.  These need to be rewritten to

         funupd_thm f x v FOO

   ---------------------------------------------------------------------- *)

val sf_default_b_as_set =
    Phase.phase_imm 1 (
    CONV_RULE
      (EVERY_CONJ_CONV
         (LAND_CONV (REWR_CONV (GSYM pred_setTheory.SPECIFICATION))))
      TCP1_paramsTheory.sf_default_b_def)

val funupd_as_set = Phase.phase_imm 1 (prove(
  ``(b IN funupd f k v) = funupd f k v b``,
  REWRITE_TAC [pred_setTheory.SPECIFICATION]));

(* stopwatch normalisation *)
local open realTheory simpLib BasicProvers
in
val elim_stopwatch_var = prove(
  ``0 < c1 /\ 0 < c2 ==>
    ((!r1 r2. l <= r1 /\ r1 <= m /\ l <= r2 /\ r2 <= m ==>
             P (c1 * r1 + c2 * r2)) =
     (!r. l <= r /\ r <= m ==> P((c1 + c2) * r)))``,
  STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    FIRST_X_ASSUM (Q.SPECL_THEN [`r`,`r`] MP_TAC) THEN
    ASM_REWRITE_TAC [REAL_ADD_RDISTRIB],
    `0 < c1 + c2` by (Q.UNDISCH_THEN `0 < c1` MP_TAC THEN
                      Q.UNDISCH_THEN `0 < c2` MP_TAC THEN
                      RealArith.REAL_ARITH_TAC) THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `(c1 * r1 + c2 * r2) / (c1 + c2)` MP_TAC) THEN
    `~(c1 + c2 = 0)` by PROVE_TAC [REAL_LT_REFL] THEN
    ASM_SIMP_TAC (srw_ss()) [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ, REAL_LDISTRIB,
                             REAL_MUL_COMM, REAL_LE_ADD2, REAL_LE_LMUL,
                             REAL_DIV_LMUL]
  ]);

val tickintvls_ok = prove(
  ``0 < tickintvlmin /\ tickintvlmin <= tickintvlmax``,
  SIMP_TAC (srw_ss()) [TCP1_paramsTheory.tickintvlmin_def,
                       TCP1_paramsTheory.tickintvlmax_def,
                       TCP1_paramsTheory.HZ_def]);

val zero_le_tickmax = MATCH_MP realTheory.REAL_LT_IMP_LE
                               (MATCH_MP realTheory.REAL_LTE_TRANS
                                         tickintvls_ok)
end; (* local *)




val ticker_t = ``TCP1_timers$Time_Pass_ticker``
val ticker_ok_t = ``TCP1_timers$ticker_ok``
val EXISTS_REFL' = EQT_INTRO (SPEC_ALL EXISTS_REFL)
fun find_mentions v hyps = let
  fun foldthis (t, acc) = if free_in v t then t::acc else acc
in
  HOLset.foldl foldthis [] hyps
end

fun sort_tpass_terms chained terms = let
  fun recurse chained acc =
      case chained of
        (x::y::rest) => recurse (y::rest) (assoc (x,y) terms :: acc)
      | _ => List.rev acc
in
  recurse chained []
end

val elimth = GEN_ALL TCP1_timerPropsTheory.time_pass_exists_eliminate
val elim_ss = srw_ss()
fun eliminate_redundant_tickers th = let
  fun foldthis (t, acc) = let
    val (f, args) = strip_comb t
  in
    if same_const ticker_t f then let
        val pair = case args of [dur, t1, t2] => ((t1, t2), t)
                              | _ => raise Fail "Urk"
      in
       pair::acc
      end
    else acc
  end
  val hyps = hypset th
  val ticker_terms = HOLset.foldl foldthis [] hyps
  (* the ticker_terms are an unordered list of
        ((tick_i, tick_i+1), tpass_t)
     tuples, where the tpass_t term is a Time_Pass_ticker term involving
     tick_i and tick_i+1, but we want to be able to stitch these together
     into a chained list of the form
       [(t_0, t_1), (t_1, t_2), (t_2, t_3)...].  *)
  val chained_ticker_terms =
      Chaining.norman_hardy Term.compare (map #1 ticker_terms)
  (* now that they've been chained, each three elements in the list
     is a spot where we might be able to eliminate the middle guy *)
  val _ = assert (not o null) chained_ticker_terms
  val sorted_tpass_terms = sort_tpass_terms chained_ticker_terms ticker_terms
  val t0 = hd chained_ticker_terms
  val d0 = hd (#2 (strip_comb (hd sorted_tpass_terms)))
  fun zero_le d =
      EQT_ELIM (SIMP_CONV elim_ss []
                          (realSyntax.mk_leq(realSyntax.zero_tm, d)))
  val zero_le_d0 = zero_le d0
  val t0_ticker_ok_t = mk_comb(ticker_ok_t, t0)
  val t0_ticker_ok_th =
      EQT_ELIM (SIMP_CONV elim_ss
                                  [TCP1_timersTheory.ticker_ok_def,
                                   tickintvls_ok, zero_le_tickmax,
                                   realTheory.REAL_LE_REFL,
                                   TCP1_paramsTheory.tickintvlmin_def,
                                   TCP1_paramsTheory.HZ_def]
                                  t0_ticker_ok_t)

  fun do_eliminables changed chain tpass_ts okth d1ok th =
      case chain of
        (x::y::z::rest) => let
          val x2y = hd tpass_ts
          val y2z = hd (tl tpass_ts)
          val d2 = hd (#2 (strip_comb y2z))
          val zero_le_d2 = zero_le d2
        in
          if free_in y (concl th) then let
              val y_ok = MATCH_MP TCP1_timerPropsTheory.ticker_ok_preserved
                                  (LIST_CONJ [okth, d1ok, ASSUME x2y])
            in
              do_eliminables changed (tl chain) (tl tpass_ts) y_ok zero_le_d2
                             th
            end
          else let
              val lc = mk_var("lc", type_of y)
              val lc_ex = mk_exists(lc, mk_eq(lc, y))
              val th = DISCH lc_ex th
              val th = MATCH_MP (CONV_RULE (LAND_CONV
                                              (REWR_CONV EXISTS_REFL')) th)
                                TRUTH
              val th = DISCH y2z th
              val th = DISCH x2y th
              val th = CONV_RULE (REWR_CONV AND_IMP_INTRO) th
              val th = GEN y th
              val th = CONV_RULE FORALL_IMP_CONV th
              val elimth' =
                  MATCH_MP elimth (LIST_CONJ [d1ok, zero_le_d2, okth])
              val th = CONV_RULE (LAND_CONV (REWR_CONV elimth')) th
              val th = CONV_RULE (LAND_CONV (SIMP_CONV elim_ss [])) th
              val x2z = #1 (dest_imp (concl th))
              val d2 = hd (#2 (strip_comb x2z))
              val d2ok = zero_le d2
            in
              do_eliminables true (x::z::rest) (x2z::tl (tl tpass_ts))
                             okth d2ok (UNDISCH th)
            end handle HOL_ERR _ => let
                         val y_ok = MATCH_MP TCP1_timerPropsTheory.ticker_ok_preserved
                                             (LIST_CONJ [okth, d1ok,
                                                         ASSUME x2y])
                       in
                         do_eliminables changed (tl chain) (tl tpass_ts) y_ok
                                        zero_le_d2 th
                       end
        end
      | _ => if changed then th else raise Conv.UNCHANGED
in
  do_eliminables false chained_ticker_terms sorted_tpass_terms t0_ticker_ok_th
                 zero_le_d0 th
end

(* ----------------------------------------------------------------------
    host_rule s

    returns the rule given the rule_id s.
    Useful for interactive debugging.
   ---------------------------------------------------------------------- *)

val host_rule = let
  val rules = strip_disj
                (rhs (#2 (strip_forall (concl NetEvalTheory.host_redn0_eval))))
in
  fn s => let
       val id = mk_const(s, ``:rule_ids``)
     in
       List.find (free_in id) rules
     end
end


(* ----------------------------------------------------------------------
    Code to control trace-checking's analysis of constraints.

    In particular, ctxt_abort_now is a predicate used to decide when
    to abort because constraint sets are getting too horrendous.

   ---------------------------------------------------------------------- *)

fun ctxt_abort_now constraints = let
  (* pending terms are OK simply because we're happy to have them be
     pending further simplification.
     Disjunctions and terms including conditionals are deemed OK because
     if they are too large, then the case-splitting technology will rip
     them apart anyway. *)
  fun deemed_ok t = is_pending t orelse is_disj t orelse
                    can (find_term is_cond) t
  val constraints = filter (not o deemed_ok) constraints
in
  List.length constraints > 20 orelse
  List.exists (fn t => term_size t > 200) constraints
end


(* rewrites used to eliminate rules with the wrong label *)
val label_rwts = let
  open TCP1_host0Theory TCP1_LIBinterfaceTheory
in
  [pairTheory.PAIR_EQ, Lhost0_11, Lhost0_distinct,
   GSYM Lhost0_distinct, LIB_interface_11, LIB_interface_distinct,
   GSYM LIB_interface_distinct]
end

val quick_label_CONV = REWRITE_CONV label_rwts

(* possible to prove that host_redn0 never allows time passage *)
val redn0_time_passage_impossible = prove(
  ``!rn rp rc h dur h'.
        ~(rn /* rp, rc */ h -- Lh_epsilon dur --> h')``,
  ONCE_REWRITE_TAC [TCP1_hostLTSTheory.host_redn0_cases] THEN
  REWRITE_TAC label_rwts THEN
  SRW_TAC [][NOT_EXISTS_THM] THEN
  SRW_TAC [][]);


open BasicProvers simpLib

local open word32Theory open bossLib
in
val THE_WL = SIMP_RULE arith_ss [HB_def,arithmeticTheory.ADD1] WL_def;
val MSB_EVAL2 = GEN_ALL (REWRITE_RULE [MSBn_def,HB_def] MSB_EVAL);
val TWO_COMP_EVAL2 = GEN_ALL (SIMP_RULE arith_ss [TWO_COMP_def,THE_WL]
                                        TWO_COMP_EVAL);
end


val word_abbrevs =
    [wordsTheory.n2w_11, wordsTheory.dimword_def, wordsTheory.dimindex_32,
     wordsTheory.dimindex_16, wordsTheory.INT_MIN_def,
     CONJ (SIMP_RULE (srw_ss()) []
                     (Q.SPEC `(&)n` integer_wordTheory.i2w_def))
          (SIMP_RULE (srw_ss()) []
                     (Q.SPEC `~(&)n` integer_wordTheory.i2w_def)),
     Q.SPEC `NUMERAL x` integer_wordTheory.w2i_n2w_pos,
     integer_wordTheory.word_0_w2i,
     Q.SPEC `NUMERAL x` integer_wordTheory.w2i_n2w_neg,
     TCP1_seq32PropsTheory.WORD_SUB_EQN]

val funupd_alt = Phase.phase_imm 1 (prove(
  (* ensures that the rewrite, generating an if, only happens if a funupd
     function is applied.  Because rewriting won't proceed underneath the
     if, there won't be a big chain of these generated.  Instead, the guard
     will stop work underneath it until it rewrites to T or F *)
  ``funupd f x y z = if x = z then y else f z``,
  SRW_TAC [][TCP1_utilsTheory.funupd_def]));

fun concrete_marker_for_bigrecs tyname =
    hd (Term.decls
        (tyname ^ "_" ^ GrammarSpecials.bigrec_subdivider_string ^ "sf0_fupd"))


val better_rounddown =
    Phase.phase_imm 1 (
    LIST_CONJ (map (fn f => SIMP_RULE (srw_ss()) []
                            (f TCP1_utilsTheory.rounddown_def))
               [Q.SPECL [`0`,`0`], Q.SPECL [`0`, `NUMERAL n`],
                Q.SPECL [`NUMERAL n`, `0`],
                Q.SPECL [`NUMERAL n`, `NUMERAL m`]]))

val better_roundup =
    Phase.phase_imm 1 (
    LIST_CONJ (map (fn f => SIMP_RULE (srw_ss()) []
                            (f TCP1_utilsTheory.roundup_def))
               [Q.SPECL [`0`,`0`], Q.SPECL [`0`, `NUMERAL n`],
                Q.SPECL [`NUMERAL n`, `0`],
                Q.SPECL [`NUMERAL n`, `NUMERAL m`]]))

(* ----------------------------------------------------------------------
    Setting up LetComputeLib's structure_reduction_CONV
   ---------------------------------------------------------------------- *)

(* first set up the map which identifies "structural constants", things
   like comma (the tupling operator), record update functions, and
   the constructors for standard datatypes *)
fun constcompare(t1, t2) = if same_const t1 t2 then EQUAL
                           else Term.compare(t1, t2)
val structure_map = let
  val base = ref (HOLset.empty constcompare)
  val base_consts =
      [boolSyntax.arb, combinSyntax.K_tm, combinSyntax.o_tm,
       numSyntax.numeral_tm, numSyntax.zero_tm,
       numSyntax.bit1_tm, numSyntax.bit2_tm,
       numSyntax.alt_zero_tm, pairSyntax.comma_tm,
       pred_setSyntax.insert_tm,
       optionSyntax.some_tm, optionSyntax.none_tm,
       realSyntax.real_injection, intSyntax.int_injection,
       finite_mapSyntax.fempty_t, finite_mapSyntax.fupdate_t,
       ``word16$n2w``, ``word32$n2w``,
       ``TCP1_preHostTypes$IP``,
       ``string$CHR``, ``TCP1_timers$ticks_of``,
       ``TCP1_utils$funupd : ('a -> 'b) -> 'a -> 'b -> 'a -> 'b``,
       ``TCP1_baseTypes$time``, ``TCP1_baseTypes$OK``,
       ``TCP1_params$sf_default_n``, ``(+): real -> real -> real``,
       ``( * ) : real -> real -> real``, ``(/) : real -> real -> real`` ]
  fun add_stdty tyname = let
    fun prim_mk_type (r as {Thy,Tyop}) = let
      val a = Type.op_arity r
    in
      mk_thy_type {Thy = Thy, Tyop = Tyop,
                   Args = List.tabulate(valOf a, fn i => alpha)}
    end
    val ty =
        case Type.decls tyname of
          [] => raise mk_HOL_ERR "testEval" "structure_map"
                                 ("No such type: "^tyname)
        | [x] => prim_mk_type x
        | x::xs => (HOL_WARNING "testEval" "structure_map"
                                ("Multiple types of name "^tyname);
                    prim_mk_type x)
  in
    case Lib.total TypeBase.constructors_of ty of
      NONE => ()
    | SOME cs => base := HOLset.addList(!base, cs)
  end
  fun add_recordty tyname =
      base := HOLset.addList (!base, record_update_fns tyname)
  val _ = base := HOLset.addList(!base, base_consts)
  val _ = app add_stdty [
                         "TLang",
                         "fd",
                         "fid",
                         "hostThreadState",
                         "ifid",
                         "ip",
                         "list",
                         "msg",
                         "netmask",
                         "port",
                         "protocol_info",
                         "seq32",
                         "sid",
                         "stopwatch",
                         "tcpstate",
                         "tid",
                         "timed",
                         "timer",
                         "timewindow"
                         ]
  val _ = app add_recordty  ["fileflags", "host", "rttinf", "socket",
                             "socket_listen", "sockflags", "tcpcb",
                             "tcp_socket", "tcpReassSegment",
                             "tcpSegment", "udp_socket"]
in
  !base
end


val strCONV = structure_reduction_CONV structure_map
val strCONV_ss = SSFRAG {ac = [], congs = [],
                          convs = [{conv = K (K strCONV),
                                    key = SOME([], ``CLET f (value x)``),
                                    name = "structure_reduction_CONV",
                                    trace = 2}],
                          dprocs = [], filter = NONE, rewrs = [],
                          name = SOME "testEval.strCONV_ss"}

(* ----------------------------------------------------------------------
    (updated record) equality conversion
   ---------------------------------------------------------------------- *)

fun isSuffix suf s = (* this is part of the next version of Basis Library *)
    size suf <= size s andalso
    suf = String.extract(s, size s - size suf, NONE)

fun updrec_EQ_CONV info t = let
  val (l,r,ty) = dest_eq_ty t
  val _ = assert (not o is_var) l
  val _ = assert (not o is_var) r
  val (tyop, tyargs) = dest_type ty
  val rwt = case Binarymap.peek (info, tyop) of
              NONE => raise mk_HOL_ERR "testEval" "updrec_EQ_CONV"
                                       "Type not in record table"
            | SOME th => th
  fun strip acc t = let
    val (f, args) = strip_comb t
  in
    if length args <> 2 then (List.rev acc, t)
    else strip (f :: acc) (last args)
  end
  val (lfs, lbase) = strip [] l
  val (rfs, rbase) = strip [] r
  val _ = assert (not o null) lfs
  val _ = assert (not o null) rfs
  val _ = assert (List.all (isSuffix "_fupd" o #1 o dest_const)) lfs
  val _ = assert (List.all (isSuffix "_fupd" o #1 o dest_const)) rfs
in
  REWR_CONV rwt t
end

val updrec_info = let
  open simpLib BasicProvers
  fun getthm s = let
    val basename = s^"_component_equality"
    val base =
        case filter (fn ((_, n), _) => n = basename) (DB.find basename) of
          [(_, (th, _))] => th
        | [] => raise mk_HOL_ERR "testEval" "updrec_info"
                                 ("No component equality theorem of name "^s)
        | ((_, (th, _))::_) =>
          (Feedback.HOL_WARNING "testEval" "updrec_info"
                                ("Multiple component equality theorems with\
                                 \ name "^s);
           th)
  in
    SIMP_RULE (srw_ss()) [] base
  end
in
    List.foldl (fn (k,a) => Binarymap.insert(a,k,getthm k))
               (Binarymap.mkDict String.compare)
               ["tcpcb", "socket", "tcp_socket", "udp_socket"]
end

val updeq_CONV_ss =
    SSFRAG {ac = [], congs = [],
                     convs = [{conv = K (K (updrec_EQ_CONV updrec_info)),
                               key = SOME ([], ``x:'a = y``),
                               name = "updrec_EQ_CONV", trace = 2}],
                     dprocs = [], filter = NONE, rewrs = [],
                     name = SOME "testEval.updeq_CONV_ss"}


val better_do_tcp_options =
    Phase.phase_imm 1 (prove(
      ``do_tcp_options cb_tf_doing_tstmp cb_ts_recent cb_ts_val =
          if cb_tf_doing_tstmp then
            SOME (cb_ts_val, case timewindow_val_of cb_ts_recent of
                                NONE -> ts_seq 0w
                             || SOME x -> x)
          else NONE``,
      SIMP_TAC bool_ss [TCP1_auxFnsTheory.do_tcp_options_def, LET_THM,
                        prove(``I = \x. x``,
                              SIMP_TAC bool_ss [FUN_EQ_THM,
                                                combinTheory.I_THM])]))


val gcd' = prove(
  ``gcd a b = bool$LET (\a'. bool$LET (\b'. if a' = 0 then b'
                                            else gcd (b' MOD a') a') b) a``,
  CONV_TAC (LAND_CONV (REWR_CONV gcdTheory.GCD_EFFICIENTLY)) THEN
  REWRITE_TAC [LET_THM] THEN BETA_TAC THEN REWRITE_TAC [])


val better_real_add_rat = prove(
  ``(x:real) / real_of_num(y:num) + (u:real) / real_of_num(v:num) =
      if y = 0 then unint(x/real_of_num y) + u/real_of_num v
      else if v = 0 then x/real_of_num y + unint(u/real_of_num v)
      else if v = y then (x + u) / real_of_num v
      else bool$LET (\g.
             bool$LET (\l.
               bool$LET (\ly.
                 bool$LET (\lv.
                      (x * ly + u * lv) / l)
                 (l / real_of_num v))
               (l / real_of_num y))
             (real_of_num(y * v) / real_of_num g))
               (gcd y v)``,
  SRW_TAC [][markerTheory.unint_def, LET_THM] THENL [
    SRW_TAC [][realTheory.add_rat],
    Q.ABBREV_TAC `l = real_of_num (y * v) / real_of_num (gcd y v)` THEN
    ASM_SIMP_TAC (srw_ss())
                 [realTheory.mult_ratr, GSYM realTheory.REAL_DIV_ADD] THEN
    ONCE_REWRITE_TAC [realTheory.div_ratl] THEN
    ASM_SIMP_TAC bool_ss [] THEN
    Q.SUBGOAL_THEN `~(l = 0)` ASSUME_TAC THENL [
      SRW_TAC [][Abbr`l`] THEN
      Q.SUBGOAL_THEN `0 < real_of_num (gcd y v)` ASSUME_TAC THENL [
        SRW_TAC [][GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
                   gcdTheory.GCD_EQ_0],
        SRW_TAC [][realTheory.REAL_EQ_LDIV_EQ]
      ],
      ALL_TAC
    ] THEN
    ASM_SIMP_TAC bool_ss [GSYM realTheory.REAL_MUL, realTheory.REAL_INJ,
                          realTheory.REAL_DIV_RMUL_CANCEL]
  ]);

val (cond_T, cond_F) = CONJ_PAIR (SPEC_ALL COND_CLAUSES)
fun cond_guard_conv c = RATOR_CONV (RATOR_CONV (RAND_CONV c))

val gcdreduce_conv = let
  val num_compset = reduceLib.num_compset()
  val _ = computeLib.add_thms [gcdTheory.GCD_EFFICIENTLY] num_compset
in
  fn t => computeLib.CBV_CONV num_compset t
end

fun norm_add_rat t = let
  open realSyntax
  val rs = realSimps.real_ss
  val simpr = SIMP_CONV rs []
  val rmul_ac = AC realTheory.REAL_MUL_ASSOC realTheory.REAL_MUL_COMM
  val let_rarg = RAND_CONV simpr THENC REWR_CONV LET_THM THENC BETA_CONV
in
  REWR_CONV better_real_add_rat THENC
  cond_guard_conv simpr THENC REWR_CONV cond_F THENC
  cond_guard_conv simpr THENC REWR_CONV cond_F THENC
  cond_guard_conv simpr THENC
  (REWR_CONV cond_T ORELSEC (* denominators equal *)
   (REWR_CONV cond_F THENC (* denominators differ *)
    RAND_CONV gcdreduce_conv THENC REWR_CONV LET_THM THENC BETA_CONV THENC
    let_rarg THENC let_rarg THENC let_rarg THENC
    LAND_CONV (BINOP_CONV (SIMP_CONV rs [rmul_ac, realTheory.REAL_LDISTRIB])))
   )
end t

val nb12_eq_0 = prove(
  ``~(NUMERAL (BIT1 n) = 0) /\ ~(NUMERAL (BIT2 n) = 0)``,
  REWRITE_TAC [arithmeticTheory.NUMERAL_DEF, arithmeticTheory.BIT1,
               arithmeticTheory.BIT2, arithmeticTheory.ADD_CLAUSES,
               GSYM arithmeticTheory.SUC_NOT]);

val leq_rat =
    LIST_CONJ
    (map (SIMP_RULE realSimps.real_ss [nb12_eq_0] o C Q.INST realTheory.le_rat)
         [[`n` |-> `NUMERAL (BIT1 n)`, `m` |-> `NUMERAL (BIT1 m)`],
          [`n` |-> `NUMERAL (BIT1 n)`, `m` |-> `NUMERAL (BIT2 m)`],
          [`n` |-> `NUMERAL (BIT2 n)`, `m` |-> `NUMERAL (BIT1 m)`],
          [`n` |-> `NUMERAL (BIT2 n)`, `m` |-> `NUMERAL (BIT2 m)`]])

val leq_ratl =
    LIST_CONJ
    (map (SIMP_RULE realSimps.real_ss [nb12_eq_0] o
          C Q.INST realTheory.le_ratl)
         [[`n` |-> `NUMERAL (BIT1 n)`], [`n` |-> `NUMERAL (BIT2 n)`]])

val leq_ratr =
    LIST_CONJ
    (map (SIMP_RULE realSimps.real_ss [nb12_eq_0] o
          C Q.INST realTheory.le_ratr)
         [[`m` |-> `NUMERAL (BIT1 n)`], [`m` |-> `NUMERAL (BIT2 n)`]])





val rathandler_SS =
    SSFRAG {ac = [], congs = [],
             convs = [{conv = K (K norm_add_rat),
                       key = SOME ([], ``(x:real / y:real) + (u:real / v)``),
                       name = "rathandler", trace = 2}],
             dprocs = [], filter = NONE,
             rewrs =
             map (SIMP_RULE realSimps.real_ss [nb12_eq_0])
                 [Q.INST [`y` |-> `real_of_num (NUMERAL (BIT1 n))`]
                         realTheory.mult_ratl,
                  Q.INST [`y` |-> `real_of_num (NUMERAL (BIT2 n))`]
                         realTheory.mult_ratl,
                  Q.INST [`z` |-> `real_of_num (NUMERAL (BIT1 n))`]
                         realTheory.mult_ratr,
                  Q.INST [`z` |-> `real_of_num (NUMERAL (BIT2 n))`]
                         realTheory.mult_ratr],
             name = SOME "testEval.rathandler_SS"}

val better_EL =
    LIST_CONJ
    (map (SIMP_RULE bool_ss [nb12_eq_0])
         (map (fn f => f listTheory.EL_compute)
              [Q.SPEC `0`, Q.SPEC `NUMERAL (BIT1 n)`,
                      Q.SPEC `NUMERAL (BIT2 n)`]))

val accept_incoming_q' =
    Phase.phase_imm 1 (setify_rwt TCP1_preHostTypesTheory.accept_incoming_q_def)

val drop_from_q0' =
    Phase.phase_imm 1 (setify_rwt TCP1_preHostTypesTheory.drop_from_q0_def)

val better_while = Phase.phase_imm 1 (prove(
  ``WHILE P f x = if P x then bool$LET (\s. WHILE P f s) (f x) else x``,
  CONV_TAC (LAND_CONV (REWR_CONV whileTheory.WHILE)) THEN
  REWRITE_TAC [LET_THM] THEN BETA_TAC THEN REWRITE_TAC []))

(* abbreviations that don't expand into things that are too large *)
   (* e.g., auto_outroute OK but make_ack_segment not *)
val phase1_abbreviations =
    Phase.get_phase_list 1 @
    [
     (* the following block of definition references should probably be
        "phased" in their respective theories *)
     TCP1_auxFnsTheory.andThen_def,
     TCP1_auxFnsTheory.assert_def,
     TCP1_auxFnsTheory.chooseM_def,
     TCP1_auxFnsTheory.cont_def,
     TCP1_auxFnsTheory.bandlim_state_init_def,
     TCP1_auxFnsTheory.get_cb_def,
     TCP1_auxFnsTheory.get_sock_def,
     TCP1_auxFnsTheory.modify_cb_def,
     TCP1_auxFnsTheory.modify_sock_def,
     TCP1_auxFnsTheory.shift_of_def,
     TCP1_paramsTheory.TCPTV_DELACK_def,

     TCP1_auxFnsTheory.update_idle_def,
     TCP1_auxFnsTheory.tcp_drop_and_close_def,
     TCP1_auxFnsTheory.tcp_close_def,

     arithmeticTheory.ADD1,
     arithmeticTheory.GREATER_DEF,
     arithmeticTheory.GREATER_EQ,
     arithmeticTheory.NOT_LESS_EQUAL,
     GSYM stringTheory.ORD_CHR,
     RES_EXISTS_THM,
     time_lt_refl, time_le_refl,
     arithmeticTheory.EXP_EQ_0,
     arithmeticTheory.GREATER_DEF,
     integerTheory.int_ge,
     integerTheory.int_gt,
     integer_word32Theory.w2i_n2w_eq_num,
     arithmeticTheory.X_MOD_Y_EQ_X,
     better_EL,
     better_fmscan,
     better_sock_has_quad,
     better_sock_wants_to_rexmtX,
     better_sockcbfld_expires,
     better_sock_might_deliver,
     integerTheory.Num,
     leq_rat, leq_ratl, leq_ratr,
     realTheory.real_ge,
     tcp_seq_flip_sense_eq,
     CONV_RULE
       (BINOP_CONV (LAND_CONV (REWR_CONV EQ_SYM_EQ)))
       tcp_seq_flip_sense_eq,
     tcp_seq_flip,
     SIMP_RULE (srw_ss()) [] TCP1_auxFnsTheory.initial_cb_def,
     finite_mapTheory.FDOM_FEMPTY,
     finite_mapTheory.FDOM_FUPDATE,
     finite_mapTheory.FUPDATE_LIST_THM,
     finite_mapTheory.FAPPLY_FUPDATE_THM,
     pred_setTheory.INSERT_INSERT,
     pred_setTheory.INSERT_INTER,
     pred_setTheory.INSERT_UNION_EQ,
     pred_setTheory.INSERT_COMM,
     whileTheory.LEAST_DEF,

     stringTheory.CHR_11,
     SPEC ``TCP (^(concrete_marker_for_bigrecs "tcpSegment") f x)``
          TCP1_preHostTypesTheory.test_outroute_def,
     SPEC ``ICMP (icmpDatagram_is1_fupd f x)``
          TCP1_preHostTypesTheory.test_outroute_def,
     CONV_RULE (STRIP_QUANT_CONV
                  (RAND_CONV (SIMP_CONV
                                (srw_ss()) [])))
               TCP1_hostTypesTheory.Sock_def]

val phase1_abbreviations = phase1_abbreviations @ word_abbrevs

(* fd_sockop isn't very nice by itself; here we specialise it for each
operation, generating one theorem for each operation.  Useful since we
go from label to fd, not the other way. *)
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

(* stick them in too *)
val phase1_abbreviations = phase1_abbreviations @ fd_sockop_concrete

(* Phase 1 hopefully gets rid of lots of irrelevant stuff, and doesn't
blow up very much.  Phase 2 expands bigger things, hoping that by this
time we are down to only one or two rules *)



(* a version of better_make_syn_segment that expresses things in terms of
     seg IN make_syn_segment cb quad tstmp
   rather than
     make_syn_segment cb quad tstmp seg
   Generally don't want to simply write away x IN Y, but we do need to
   simplify this particular instance *)

val better_make_syn_segment' =
    Phase.phase_imm 2 (setify_rwt better_make_syn_segment)

val better_make_ack_segment' =
    Phase.phase_imm 2 (setify_rwt better_make_ack_segment)

val better_bsd_make_phantom_segment' =
    Phase.phase_imm 2 (setify_rwt better_bsd_make_phantom_segment)

val make_syn_ack_segment' =
    Phase.phase_imm 2 (setify_rwt TCP1_auxFnsTheory.make_syn_ack_segment_def)

val make_rst_segment_from_cb' =
    Phase.phase_imm
      2
      (setify_rwt TCP1_auxFnsTheory.make_rst_segment_from_cb_def)

val make_rst_segment_from_seg' =
    Phase.phase_imm
      2
      (setify_rwt TCP1_auxFnsTheory.make_rst_segment_from_seg_def)

val premunged_rollback_tcp_output =
    Phase.phase_imm 2 (
    CONV_RULE ((STRIP_QUANT_CONV o RAND_CONV o RAND_CONV o ABS_CONV o
                RATOR_CONV o RAND_CONV)
                 (SIMP_CONV (srw_ss()) []))
              TCP1_auxFnsTheory.rollback_tcp_output_def)




(* bigger things; will ultimately need some of the things that appear
in the body of deliver_in_3.  Would be much easier if we factored
deliver_in_3 into several definitions, that could be put in here. *)

val better_calculate_buf_sizes_1 =
    Phase.phase_imm 2 (
    SIMP_RULE bool_ss [optionTheory.option_case_def, combinTheory.I_THM]
              (Q.INST [`bw_delay_product_for_rt` |-> `SOME bwdp`]
                      (SPEC_ALL TCP1_auxFnsTheory.calculate_buf_sizes_def)))
val better_calculate_buf_sizes_2 =
    Phase.phase_imm 2 (
    SIMP_RULE bool_ss [optionTheory.option_case_def, combinTheory.I_THM]
              (Q.INST [`bw_delay_product_for_rt` |-> `NONE`]
                      (SPEC_ALL TCP1_auxFnsTheory.calculate_buf_sizes_def)))





val better_computed_rxtcur =
    Phase.phase_imm 2 (
    CONV_RULE (STRIP_QUANT_CONV
                 (RAND_CONV (UNBETA_CONV ``ri:rttinf`` THENC
                             REWR_CONV (GSYM LetComputeTheory.CLET_THM))))
              TCP1_auxFnsTheory.computed_rxtcur_def);


val phase2_abbreviations =
    Phase.get_phase_list 2 @
    [better_make_ack_segment,
     better_bsd_make_phantom_segment,
     better_make_syn_segment,
     better_enqueue,
     better_dequeue,
     better_tcp_reass,
     tcp_reass_build_def,
     calculate_buf_sizes_EQ,
     calculate_buf_sizes_EQ2,
     TCP1_auxFnsTheory.tcp_reass_prune_def,
     TCP1_hostLTSTheory.di3_ststuff_def,
     TCP1_auxFnsTheory.make_rst_segment_from_cb_def]



(* very useful FM theorem *)
val fempty_fupdate_eq_ss = let
  open finite_mapTheory simpLib BasicProvers
  val ps_lemma = prove(
     ``({x} = y INSERT Y) = (x = y /\ (Y = {} \/ Y = {x}))``,
     SIMP_TAC (srw_ss())[EQ_IMP_THM, pred_setTheory.EXTENSION] THEN
     PROVE_TAC []);
  val fempty_fupdate_eq =
      (* ck, cv stand for "concrete key", "concrete value" *)
      prove(``(FEMPTY |+ (ck, cv) = fm |+ (k, v)) =
              (k = ck /\ v = cv /\ !v. fm |+ (k,v) = FEMPTY |+ (k, v))``,
            SIMP_TAC (srw_ss())[GSYM fmap_EQ_THM, EQ_IMP_THM] THEN
            REWRITE_TAC [ps_lemma] THEN SRW_TAC [][] THEN
            FIRST_X_ASSUM SUBST_ALL_TAC THEN
            FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE])
  val c = REWR_CONV REFL_CLAUSE ORELSEC REWR_CONV fempty_fupdate_eq
in
  SSFRAG {ac = [], congs = [],
          convs = [{conv = K (K c), name = "fempty_fupdate_eq", trace = 2,
                    key = SOME([], ``FEMPTY |+ (ck,cv) = fm |+ (k,v)``)}],
          dprocs = [], filter = NONE, rewrs = [],
          name = SOME "testEval.fempty_fupdate_eq_ss" }
end

val base_ss =
    srw_ss() ++ rewrites [realTheory.REAL_INJ,
                                  realTheory.REAL_OF_NUM_MUL,
                                  realTheory.REAL_OF_NUM_ADD,
                                  finite_mapTheory.DOMSUB_FUPDATE_THM,
                                  option_cond_thms, IS_SOME_IMP_ELIM]

fun is_eliminable_equality t = let
  val (l, r) = dest_eq t
in
  is_var l andalso not (free_in l r) orelse
  is_var r andalso not (free_in r l)
end handle HOL_ERR _ => false

fun orient_eq t = let
  val (l, r) = dest_eq t
in
  if is_var l then t else mk_eq(r, l)
end

fun orient_eq_to_th t = let
  val (l, r) = dest_eq t
  val th = ASSUME t
in
  if is_var l then th
  else SYM th
end



val _ = overload_on ("LET", ``LetCompute$CLET``)
val _ = remove_ovl_mapping "LET" {Name = "LET", Thy = "bool"}

val lconj_congruence =
    tautLib.TAUT_PROVE ``(p = p') ==> (p' ==> (q = q')) ==>
                         ((p /\ q) = (p' /\ q'))``

(* A strategy for dealing with conds: don't ever look at the branches. *)
val cond_cong1 = prove(
  ``(p = p') ==> ((if p then q else r) = (if p' then q else r))``,
  SIMP_TAC boolSimps.bool_ss []);

val cond_ss = SSFRAG {ac = [], congs = [cond_cong1], convs = [],
                      filter = NONE, dprocs = [], rewrs = [],
                      name = SOME "testEval.cond_ss" }

val option_cong = prove(
  ``(p = p') ==> (option_CASE (p:'a option) (x:'b) y = option_CASE p' x y)``,
  SIMP_TAC boolSimps.bool_ss []);

val option_cong_ss = SSFRAG {ac = [], congs = [option_cong], convs = [],
                             filter = NONE, dprocs = [], rewrs = [],
                             name = SOME "testEval.option_cong_ss" }
val lconj_cong_ss = SSFRAG {ac = [], congs = [NetEvalTheory.lconj_cong],
                            convs = [], filter = NONE, dprocs = [],
                            rewrs = [], name = SOME "testEval.lconj_cong_ss" }
fun pending_filter (th0,c) = let
  val th = EQT_ELIM th0
  val (f, x) = dest_comb (concl th)
in
  if same_const f LetComputeLib.pending_t then
    if is_eq x then [(SYM (EQ_MP (SPEC x LetComputeTheory.pending_def) th), c)]
    else [(th0,c)]
  else [(th0,c)]
end handle HOL_ERR _ => [(th0,c)]
val pending_SS = SSFRAG {ac = [], congs = [], convs = [], dprocs = [],
                         filter = SOME pending_filter, rewrs = [],
                         name = SOME "testEval.pending_SS" }


fun STRIP_IMP_CONV c t =
    if is_imp t then RAND_CONV (STRIP_IMP_CONV c) t
    else c t
fun safe_rewrite_filter (th0,c) = let
  val (l,r) = dest_eq (#2 (strip_imp (concl th0)))
in
  if null (free_vars l) andalso not (null (free_vars r)) then
    [(CONV_RULE (STRIP_IMP_CONV (REWR_CONV EQ_SYM_EQ)) th0, c)]
  else [(th0,c)]
end
val safe_rewrite_SS = SSFRAG {ac = [], congs = [], convs = [], dprocs = [],
                              filter = SOME safe_rewrite_filter, rewrs = [],
                              name = SOME "testEval.safe_rewrite_SS" }

(* stops the simplifier looking inside string or number literals *)
val noliterals_SS = SSFRAG {ac = [],
                            congs = [REFL ``NUMERAL x``, REFL ``STRING x y``],
                            convs = [], dprocs = [], filter = NONE,
                            rewrs = [], name = SOME "testEval.noliterals_SS"}

(* vrecords - records of variables, making sure that the last theorem
   in a trace will know about all of the variables that have appeared in
   the course of the trace *)
val vrecord_t =
    mk_thy_const{Thy = "bool", Name = "DATATYPE", Ty = alpha --> bool}
val _ = overload_on ("vrecord", vrecord_t)
fun dest_vrecord t = let
  val (f,x) = dest_comb t
  val _ = same_const f vrecord_t orelse
          raise mk_HOL_ERR "testEval" "dest_vrecord" "Not a vrecord"
in
  x
end
val is_vrecord = can dest_vrecord

fun mk_vrecord t = let
  val ty = type_of t
in
  mk_comb(mk_thy_const{Thy = "bool", Name = "DATATYPE", Ty = ty --> bool}, t)
end
fun elim_bad_vrecords t = let
  val arg = rand t
in
  if is_var arg orelse is_eq arg andalso is_var (lhs arg) then raise UNCHANGED
  else REWR_CONV boolTheory.DATATYPE_TAG_THM t
end
val elim_bad_vrecords_SS =
    SSFRAG {ac = [], congs = [], dprocs = [], filter = NONE, rewrs = [],
            convs = [{conv = K (K elim_bad_vrecords),
                      key = SOME([], ``bool$DATATYPE (x:'a)``),
                      name = "elim_bad_vrecords", trace = 2}],
            name = SOME "testEval.elim_bad_vrecords_SS"}
(* call on a theorem when a variable v is about to be eliminated *)
fun eliminating_vrecord v th = let
  val cutth = EQT_ELIM (ISPEC v boolTheory.DATATYPE_TAG_THM)
in
  PROVE_HYP cutth th
end

fun record_elimination v r th = ADD_ASSUM (mk_vrecord (mk_eq(v,r))) th

(* ----------------------------------------------------------------------
    Definition of phase1 and 2 simpsets:

      phase2 is phase1 + phase2 rewrites

    In phase2 of spec_n_simp, the clever finite map elimination code
    is called too, but this is a function of the way REWRn_CONV is
    called rather than the simpset.
   ---------------------------------------------------------------------- *)
val phase1_ss = base_ss ++ CLET_ss ++ strCONV_ss ++ updeq_CONV_ss ++
                        option_cong_ss ++ cond_ss ++ lconj_cong_ss ++
                        rathandler_SS ++ safe_rewrite_SS ++ pending_SS ++
                        GSPEC_ss ++ boolSimps.CONJ_ss ++
                        numrelnorm.CANON_ss ++ noliterals_SS ++
                        rewrites phase1_abbreviations
val q_ok_SS =
    SSFRAG {ac = [], congs = [],
             convs = [{conv = K (K (calc_tcp_reass_q_ok_CONV
                                      (SIMP_CONV phase1_ss []))),
                       key = SOME([], ``tcp_reass_q_ok x``),
                       name = "calc_tcp_reass_q_ok_CONV", trace = 2}],
             dprocs = [], filter = NONE, rewrs = [],
             name = SOME "testEval.q_ok_SS"}

val phase2_ss = phase1_ss ++ rewrites phase2_abbreviations ++
                realSimps.REAL_ARITH_ss ++ q_ok_SS

(* moves head variable of existential chain to the end; slow because
   of deBruijn *)
fun MOVE_EXISTS_RIGHT_CONV tm = let
  val (vs, body) = strip_exists tm
in
  case vs of
    [] => failwith "MOVE_EXISTS_RIGHT_CONV"
  | [_] => ALL_CONV tm
  | (v::others) => let
      val reordered_vars = others @ [v]
      val asm = ASSUME body
      fun one_direction old new = let
        val thm =
            foldr (fn (v, th) => EXISTS (mk_exists(v, concl th),v) th) asm new
        fun foldthis (v, th) = let
          val hyp_t = hd (hyp th)
        in
          CHOOSE (v, ASSUME (mk_exists(v, hyp_t))) th
        end
      in
        DISCH_ALL (List.foldr foldthis thm old)
      end
    in
      IMP_ANTISYM_RULE (one_direction vs reordered_vars)
                       (one_direction reordered_vars vs)

    end
end

(* eliminate existential last ref to a FM by assuming FEMPTY *)
fun prove_ex_with_fempty t = let
  val (v, body) = dest_exists t
  val kvty = finite_mapSyntax.dest_fmap_ty (type_of v)
  val fempty = finite_mapSyntax.mk_fempty kvty
in
  EQT_INTRO
  (EXISTS (t, fempty)
          (EQT_ELIM (REWRITE_CONV [] (Term.subst [v |-> fempty] body))))
end

(* do the above inside a term: push existential inwards, then apply above *)
fun simplest_fm_elim t = let
  open finite_mapSyntax
  val (vs, body) = strip_exists t
  val v = hd vs
  val cs = strip_conj body
in
  case List.filter (free_in v) cs of
    [c] => if is_forall c then
             STRIP_QUANT_CONV (markerLib.move_conj_left (free_in v)) THENC
             MOVE_EXISTS_RIGHT_CONV THENC
             LAST_EXISTS_CONV (EXISTS_AND_CONV THENC
                               LAND_CONV prove_ex_with_fempty THENC
                               REWR_CONV T_and_l)
           else NO_CONV
  | _ => NO_CONV
end t

val unwind = Profile.profile "UNWIND" Unwind.UNWIND_EXISTS_CONV
fun all_unwinds tm =
    (if is_exists tm then (unwind THENC all_unwinds) ORELSEC
                          BINDER_CONV all_unwinds
     else ALL_CONV) tm

val check_unwinds = REPEATC CLET_UNWIND

fun check_unwinds_and_fmaps ctxt = let
  (* sitting atop a term with a bunch of existential quantifiers below;
     try and eliminate as many as possible, using both normal unwinding
     and finite_map magic *)
  open boolSimps simpLib BasicProvers Net_fmap_analyse
  fun kreduce thl = SIMP_CONV phase2_ss (ctxt @ thl)
  val fmctxt = HOLset.listItems (FVL (map concl ctxt) empty_tmset)
  fun fm t = if finite_mapSyntax.is_fmap_ty (type_of (#1 (dest_exists t))) then
               (Trace.trace(2,
                            Trace.LZ_TEXT
                              (fn () => "FM elimination attempt on variable "^
                                        #1 (dest_var (#1 (dest_exists t)))));
                (simplest_fm_elim ORELSEC fm_onestep fmctxt kreduce) t)
             else raise mk_HOL_ERR "foo" "foo" "Bad type"
  fun recurse tm = let
    val (v, body) = dest_exists tm
  in
    if is_exists body then
      BINDER_CONV recurse THENC TRY_CONV fm
    else TRY_CONV fm
  end tm handle HOL_ERR _ => ALL_CONV tm
in
  STRIP_QUANT_CONV draw_out_fmaps THENC
  REPEATC CLET_UNWIND THENC
  recurse
end

val CLET_EXISTS = prove(
  ``CLET (\v. ?x. P x v) e = ?x. CLET (P x) e``,
  SRW_TAC [][LetComputeTheory.CLET_THM]);

fun move_and_exists_up t = let
  (* move existential quantifiers up in a term, over conjunctions and let
     expressions *)
  val conj_resolve =
      REPEATC (STRIP_QUANT_CONV LEFT_AND_EXISTS_CONV) THENC
      REPEATC (STRIP_QUANT_CONV RIGHT_AND_EXISTS_CONV)
  fun clet_resolve t =
      TRY_CONV (HO_REWR_CONV CLET_EXISTS THENC BINDER_CONV clet_resolve) t
in
  if is_exists t then BINDER_CONV move_and_exists_up
  else if is_conj t then BINOP_CONV move_and_exists_up THENC conj_resolve
  else if is_clet t then LAND_CONV (ABS_CONV move_and_exists_up) THENC
                         clet_resolve
  else ALL_CONV
end t

val conj_assoc' = GSYM CONJ_ASSOC
val gen_lconj_congruence = GEN_ALL lconj_congruence

val lconj_t = ``NetEval$lconj``
fun is_lconj t = let
  val (f, args) = strip_comb t
in
  length args = 2 andalso same_const f lconj_t
end

(* rewrite from L to R across conjuncts; as soon as it rewrites to an
   equality that's been ex. quant. it stops and unwinds; never goes
   deeper than n conjuncts *)
fun REWRn fmaps ctxt n c t = let
  fun recursor env ctxt n t = let
    fun possible_left_ctxt t = let
      val (c1, c2) = dest_conj t
      val newctxt = if is_forall c1 andalso is_eq (#2 (strip_forall c1)) then
                      ASSUME c1 :: ctxt
                    else if is_eliminable_equality c1 andalso
                            not (finite_mapSyntax.is_fmap_ty
                                   (type_of (rand c1)))
                    then
                      orient_eq_to_th c1 :: ctxt
                    else ctxt
      val c2_th = DISCH c1 (recursor env newctxt (n - 1) c2)
    in
      MATCH_MP (MATCH_MP gen_lconj_congruence (REFL c1)) c2_th
    end
    fun STOP_ON P t = if P t then ALL_CONV t else NO_CONV t
    fun unwindable_eq_or_exists t = let
      val (c1, c2) = dest_conj t
    in
      is_eq c1 andalso let
        val (l, r) = dest_eq c1
      in
        HOLset.member(env, l) andalso not (free_in l r) orelse
        HOLset.member(env, r) andalso not (free_in r l)
      end orelse is_exists c1
    end
  in
    if n = 0 then ALL_CONV t
    else if is_exists t then let
        val (vs, _) = strip_exists t
      in
        (if fmaps then check_unwinds_and_fmaps ctxt else check_unwinds) THENC
        STRIP_QUANT_CONV (recursor (HOLset.addList(env, vs)) ctxt n) THENC
        PURE_REWRITE_CONV [EXISTS_SIMP]
      end t
    else if is_conj t then
      if is_lconj (rand (rator t)) then
        (LAND_CONV (REWR_CONV lconj_def) THENC recursor env ctxt n) t
      else
        (LAND_CONV (c ctxt) THENC
         REPEATC (REWR_CONV conj_assoc') THENC
         (REWR_CONV F_and_l ORELSEC
          STOP_ON unwindable_eq_or_exists ORELSEC
          (possible_left_ctxt THENC
           TRY_CONV (REWR_CONV F_and_r) THENC
           TRY_CONV (REWR_CONV T_and_l)))) t
    else if is_clet t then let
        open LetComputeTheory
        val value_arg = rand t
        val arg_eval =
            if is_comb value_arg andalso same_const (rator value_arg) value_t
            then
              RAND_CONV (c ctxt)
            else c ctxt THENC REWR_CONV (GSYM value_def)
        val deal_to_a_clet =
            strCONV ORELSEC CLET_CONV ORELSEC REWR_CONV CLET_SIMP ORELSEC
            grounded_let_CONV
      in
        RAND_CONV arg_eval THENC
        ((deal_to_a_clet THENC recursor env ctxt n) ORELSEC
         LAND_CONV (ABS_CONV (recursor env ctxt n)))
      end t
    else if is_lconj t then
      (REWR_CONV lconj_def THENC recursor env ctxt n) t
    else c ctxt t
  end
in
  (move_and_exists_up THENC recursor empty_tmset ctxt n) t
end

fun p1c0 ctxt n = let
  open simpLib
in
  REWRn false ctxt n
        (SIMP_CONV (phase1_ss ++ cond_ss ++ fempty_fupdate_eq_ss))
end

(* think about fm elimination conversions;
   add unwinding over foralls (doesn't happen often) *)
fun p1c n = REPEATC o CHANGED_CONV o p1c0 n

fun p2c ctxt =
    REPEATC (CHANGED_CONV (REWRn true ctxt ~1 (SIMP_CONV phase2_ss)))

fun disj_imp_conv t =
    TRY_CONV (REWR_CONV DISJ_IMP_THM THENC
              BINOP_CONV disj_imp_conv) t

fun pre_simp_disjunctify th = let
  (* th of form x --> y  = (?x...) \/ (?y...) \/ ... \/ (?z...) *)
  val (_, th0) = EQ_IMP_RULE th
in
  map GEN_ALL (CONJUNCTS (CONV_RULE disj_imp_conv th0))
end handle HOL_ERR _ => []

(* "database" of label given theorems *)
fun find_rule label = let
  val (trace_con, args)  = strip_comb label
  val trace_s = #1 (dest_const trace_con)
  val thm_name =
      if trace_s = "Lh_call" then let
          val libfncall_t = #2 (pairSyntax.dest_pair (hd args))
          val libfn_s = #1 (dest_const (#1 (strip_comb libfncall_t)))
        in
          trace_s ^ "_" ^ libfn_s
        end
      else
        trace_s
  fun find_arg posn eqn = let
    val (l, _) = dest_eq eqn
    val (_, args) = strip_comb l
  in
    List.nth(args, posn)
  end
  val base_label_thm = DB.fetch "NetEval" ("quick_redn_" ^ thm_name ^ "_thm")
  val instantiated = PART_MATCH (find_arg 4) base_label_thm label
      (* 4 is the number of the label position in the reduction relation:
              0label /* 1proto 2cat */ 3host0 -- 4label --> 5host
      *)
in
  instantiated
end

val lh_tau_t = ``TCP1_host0$Lh_tau``
val lh_send_t = ``TCP1_host0$Lh_senddatagram``
val deliver_out_1_t = ``TCP1_ruleids$deliver_out_1``
val lheps_t = ``TCP1_host0$Lh_epsilon``


val hiq_test_term = ``\h: host. timed_val_of h.iq = []``
val hsocks_term = ``\h: host. h.socks``
val timer_expires_t = ``TCP1_timers$timer_expires``
fun sort_for_output_next host label rest ths = let
  (* if
        label is Lh_tau  and
     then
        if
           the hd of the rest of the labels is a send_datagram
        then
           if
              the host's input queue is empty
           then
              if
                 there are no relevant timers in the host that can expire
              then
                 pull the deliver_out_1 rule to the head of the list ths
              else
                 pull the timer_* rules to the head of the list
           else
              pull the deliver_in_* rules to the head of the list
              (* could just do nothing, as the deliver_in_* rules come before
                 deliver_out_1 and the timer_tt rules, but this might save
                 time *)
        else if
           the hd of the rest of the labels is an Lh_epsilon
        then
           pull all urgent rules to the front of the list
        else
           return ths unchanged
     else
        return ths unchanged
  *)
  val simp = SIMP_CONV phase1_ss []
  fun hiq_empty() =
      rhs (concl (simp (mk_comb(hiq_test_term, host)))) = boolSyntax.T
  fun name_pfx s t = let
    val id = find_term (fn t => type_of t = ``:rule_ids``) t
    val name = #Name (dest_thy_const id)
  in
    String.isPrefix s name
  end handle HOL_ERR _ => false
  fun prefer_rules P ths = let
    val (preferred, rest) = List.partition (P o concl) ths
  in
    preferred @ rest
  end
  fun no_expiring_timers () = let
    (* just consider the host's socks value, in order to get timers that are
       in a tcpcb, but not those attached to input/output queues or thread
       state info *)
    val socks_t = rhs (concl (simp (mk_comb(hsocks_term, host))))
    val timer_vals = find_terms (fn t => type_of t = ``:timer``) socks_t
    fun timer_expires t =
        rhs (concl (simp (mk_comb(timer_expires_t, t)))) = boolSyntax.T
  in
    not (List.exists timer_expires timer_vals)
  end
  fun label_name t = #Name (dest_thy_const t) handle HOL_ERR _ => ""
in
  if same_const lh_tau_t label andalso not (null rest) then
    case label_name (#1 (strip_comb (hd rest))) of
      "Lh_senddatagram" => if hiq_empty () then
                             if no_expiring_timers() then
                               prefer_rules (free_in deliver_out_1_t) ths
                             else (* pull timer rules forward *)
                               prefer_rules (name_pfx "timer_tt") ths
                           else (* pull deliver_in rules forward *)
                             prefer_rules (name_pfx "deliver_in") ths
    | "Lh_epsilon" => if same_const lheps_t (rator (hd rest)) then
                        prefer_rules (free_in ``urgent``) ths
                      else
                        ths
    | _ => ths
  else ths
end

exception SendDatagramMismatch
val sdm_check_enabled = ref true
val sdm_fail_exception = ref true
val sdm_test_term = ``\h:host m:msg. HD (timed_val_of h.oq) = m``
fun check_for_senddatagram_mismatch host label = let
  val (f, args) = strip_comb label
in
  if !sdm_check_enabled andalso same_const f lh_send_t then let
      val msg = hd args
      val test_term = list_mk_comb(sdm_test_term, [host, msg])
      val simped = SIMP_CONV phase1_ss [] test_term
    in
      if rhs (concl simped) = boolSyntax.F then
        raise SendDatagramMismatch
      else ()
    end
  else ()
end

exception OutputQueueTooLong
val oq_test_term = ``\h:host. LENGTH (timed_val_of h.oq) > 2``
fun check_for_output_queue_too_long host = let
  val test_term = mk_comb(oq_test_term, host)
  val simped = SIMP_CONV phase1_ss [] test_term
in
  if rhs (concl simped) = boolSyntax.T then
    raise OutputQueueTooLong
  else ()
end

val assfailed_t = ``TCP1_utils$ASSERTION_FAILURE``
val assfailed_exn = mk_HOL_ERR "testEval" "dest_assfailed"
                               "Term not an assertion failure"
fun dest_assfailed t = let
  val (f, x) = dest_comb t handle HOL_ERR _ => raise assfailed_exn
  val _ = same_const f assfailed_t orelse raise assfailed_exn
in
  x
end
fun is_assfailed t = can dest_assfailed t


(* initial simplification given a context, host, a label and the labels
   that are to follow the current label (i.e., a possibly empty list).
   A context is the list of contraints we've accumulated so far
   (initially, an empty list). *)
fun spec_n_simp hnd ctxt host label rest = let
  open  simpLib BasicProvers
  fun identify_rule th = (output (hnd, "==Attempting "^rule_name th); th)
  val _ = check_btrack hnd
  fun phase s th = (output (hnd, " -- "^s); th)
  val timer = Timer.startCPUTimer()
  val _ = mytrace(hnd,"I1:")
  val _ = check_for_senddatagram_mismatch host label
  val _ = mytrace(hnd,"I2:")
  val _ = check_for_output_queue_too_long host
  val _ = mytrace(hnd,"I3:")
  val label_simped = find_rule label
  val _ = mytrace(hnd,"I4:")
  val label_ths = let
    val label_ths = pre_simp_disjunctify label_simped
    (* sort these to put the failing rules last ; helps us to look at what we
       think are more likely branches earlier.  Usually rules are ordered OK
       for non-taus, but for the tau label, fails can come before succeeds *)
    val _ = mytrace(hnd,"I5:")
    fun failing r = free_in ``fail`` r orelse free_in ``badfail`` r
    val (oks, fails) = partition (not o failing o concl) label_ths
    val _ = mytrace(hnd,"I6:")
  in
    sort_for_output_next host label rest (oks @ fails)
  end
  val _ = mytrace(hnd,"I7:")
  val label_simped_seq = seq.fromList label_ths
  val _ = mytrace(hnd,"I8.\n")
  val init_time_taken = #usr (Timer.checkCPUTimer timer)
  val _ = output (hnd,
                 "initial: "^Time.toString init_time_taken^
                 "s (#poss: "^Int.toString (length label_ths)^")\n")

  val ctxt_ths = map ASSUME ctxt
  val _ = mytrace(hnd,"M1:")

  fun do_pre_host_simp n th = let
    val new_th = CONV_RULE (STRIP_QUANT_CONV (LAND_CONV (p1c ctxt_ths n))) th
    val t = rand (rator (#2 (strip_forall (concl new_th))))
  in
    if t = boolSyntax.F then
      (output (hnd," -- REJECTED \n"); NONE)
    else case total dest_assfailed t of
           SOME s => (output(hnd, " -- REJECTED through assertion failure: "^
                                  stringSyntax.fromHOLstring s ^ "\n");
                      NONE)
         | NONE => SOME new_th
  end
  fun do_host_match th = let
    fun selector t = List.nth(#2 (strip_comb (rand t)), 3)
                     (* 3 above is the position of the initial host parameter
                        in the reduction relation,
                        0label /* 1proto 2cat */ 3host0 -- 4label --> 5host *)
  in
    PART_MATCH selector th host
  end
  val hostlabel_simped_seq =
      seq.mapPartial (Option.map do_host_match o do_pre_host_simp 5 o
                      itlist ADD_ASSUM ctxt o
                      phase "pre_host" o identify_rule)
                     label_simped_seq
  val _ = mytrace(hnd,"M2:")
  val simp_once_more =
      seq.mapPartial (do_pre_host_simp 11 o phase "post_host")
                     hostlabel_simped_seq
  val _ = mytrace(hnd,"M3:")
  fun simplify_base th = let
    val new = CONV_RULE (LAND_CONV (p2c ctxt_ths THENC
                                    cse_elim_CONV THENC
                                    p2c ctxt_ths)) th
    val new = TCP1_boundsInference.infer_other_constraints
                (SIMP_CONV phase1_ss [])
                new
    val hypothesis = rand (rator (concl new))
  in
    if hypothesis = boolSyntax.F then
      (output (hnd, " -- REJECTED\n"); NONE)
    else
      case total dest_assfailed hypothesis of
        SOME s => (output(hnd, " -- REJECTED through assertion failure: "^
                               stringSyntax.fromHOLstring s ^ "\n");
                   NONE)
      | NONE => SOME new
  end
in
  (* finish by doing phase2 simplification and least-evaluation on each
     antecedent, throwing away those that simplify to F *)
  let val ret = seq.mapPartial (simplify_base o phase "phase2") simp_once_more in
      mytrace(hnd,"M4.\n"); ret
  end
end handle e as SendDatagramMismatch =>
           if !sdm_fail_exception then raise e
           else (output(hnd, " -- REJECTED through SDM failure\n");
                 seq.empty)

(* called to turn (?x. P x) ==> Q into !x. P x ==> Q, and to do this
   recursively as long as such a pattern exists at the top level *)
fun repeated_limp_ex_conv t =
    TRY_CONV (LEFT_IMP_EXISTS_CONV THENC
              BINDER_CONV repeated_limp_ex_conv) t


exception CtxtTooComplicated of term list
fun eliminate_equalities th = let
  (* th "morally" of form |- c1 /\ c2 /\ .. /\ cn ==> P ..
     where some of the ci are equalities.  Eliminate those that are, and
     move the others into the hypotheses, returning the resulting theorem
     and a list of those conjuncts that moved into the hypotheses.

     In fact, there may be various let-expression littered through the
     hypotheses.  If any are of boolean type at the top level, use the
     CLET_pending theorem

       |- (CLET f (value e) ==> P) = !v. pending (v = e) ==> f v ==> P)

     to turn the let binding into an equational hypothesis, but one
     that isn't eliminated.  The pending tag prevents the equality
     from being messed with prematurely.  Subsequently, eliminate
     occurrences of e everywhere, replacing them with v *)

  fun recurse acc th =
    if is_imp (concl th) then let
        val (ant, con) = dest_imp (concl th)
        open LetComputeTheory
      in
        if is_clet ant then
          recurse acc (CONV_RULE (HO_REWR_CONV CLET_pending) th)
        else if is_pending ant then let
            val th' = SIMP_RULE (bool_ss ++ pending_SS) [] th
          in
            recurse acc (UNDISCH th')
          end
        else if is_conj ant then
          recurse acc (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) th)
        else if is_eq ant then let
            val (l0,r0) = dest_eq ant
            val (l,r) = if is_var l0 then (l0,r0) else (r0,l0)
          in
            if is_eliminable_equality ant then let
                fun doit th = MP (INST [l |-> r] th) (REFL r)
                val newth =
                    if HOLset.member(hypset th, mk_vrecord l) then
                      record_elimination l r (doit (eliminating_vrecord l th))
                    else doit th
              in
                recurse acc newth
              end
            else if null (free_vars l0) then
              recurse (mk_eq(r0,l0) :: acc)
                (UNDISCH (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ)) th))
            else
              recurse (ant :: acc) (UNDISCH th)
          end
        else recurse (ant :: acc) (UNDISCH th)
      end
    else if is_forall (concl th) then
      recurse acc (SPEC_ALL th)
    else (acc, th)
  val (cstrts, newth) = recurse [] th
in
  if ctxt_abort_now cstrts then raise CtxtTooComplicated cstrts
  else newth
end


fun superset_disj_rule ds t = let
  (* ds is a list of terms; t is a disjunction of a superset of ds *)
  (* return the theorem d1 \/ d2 \/ .. \/ dn |- t *)
  fun build_disj d t = let
    (* d is one of the disjuncts of t, returns the theorem d |- t *)
    val (t1, t2) = dest_disj t
  in
    if not (mem d (strip_disj t1)) then DISJ2 t1 (build_disj d t2)
    else DISJ1 (build_disj d t1) t2
  end handle HOL_ERR _ => ASSUME d
in
  case ds of
    [] => CCONTR t (ASSUME boolSyntax.F)
  | [d] => build_disj d t
  | (d::ds0) => DISJ_CASES (ASSUME (list_mk_disj ds)) (build_disj d t)
                           (superset_disj_rule ds0 t)
end

fun disch_conjuncts th = let
  (* th of form p /\ q /\ .. /\ r ==> s, returns a theorem
        [p,q,..,r] |- s
  *)
  val (ant, c) = dest_imp (concl th)
  val cs = strip_conj ant
in
  MATCH_MP (CONV_RULE (LAND_CONV (REWRITE_CONV (map ASSUME cs))) th) TRUTH
end

datatype lc_status = Good | Broken

fun lc_status t = let
  val (v, body) = dest_exists t
  val (l, r) = dest_eq body
in
  if l = v then if is_var r then SOME Good else SOME Broken
  else NONE
end handle HOL_ERR _ => NONE

val exists_refl = EQT_INTRO (SPEC_ALL EXISTS_REFL)

fun clean_and_undisch_equality th = let
  (* th is of the form |- (l = r) ==> c, and the equality is not eliminable,
     as per the elim_equality function below.  Cleanup the equality and
     then "undisch" it into the hypotheses.

     cleanups include
       * making sure that l is not a ground term
     and that's it for the moment
  *)
  val (l, r) = dest_eq (#1 (dest_imp (concl th)))
  val th' =
      if null (free_vars l) then CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ)) th
      else th
in
  UNDISCH th'
end

fun elim_equality hnd t th = let
  val (l, r) = dest_eq t
  val (var, value) = if is_var l andalso not (free_in l r) then (l, r)
                     else if is_var r andalso not (free_in r l) then (r, l)
                     else failwith "equality no good"
  val was_recorded = HOLset.member(hypset th, mk_vrecord var)
  val th0 = CONV_RULE (LAND_CONV (REWRITE_CONV []))
                      (INST [var |-> value] (eliminating_vrecord var th))
  val message = if was_recorded then "==Eliminated local variable: "
                else "==Eliminated (transient) local variable: "
  val _ = output (hnd, message ^ term_to_string var ^ " = "^
                       term_to_string value ^ "\n")
in
  if was_recorded then record_elimination var value (MP th0 TRUTH)
  else MP th0 TRUTH
end
fun eliminate_hyp_equalities hnd th = let
  val hyps = hypset th
in
  case HOLset.find is_eliminable_equality hyps of
    NONE => th
  | SOME t => eliminate_hyp_equalities hnd (elim_equality hnd t (DISCH t th))
end

exception Problem of term * thm
val working_thm = ref TRUTH

(* cleanup_ctxts can get into loops if the hypotheses include terms of the
   form x = y and y = x.  For this reason, eliminate_hyp_equalities is called
   on the input theorem before cleanup_ctxts gets a go at it. *)
fun cleanup_ctxts hnd th = let
  val _ = mytrace(hnd,"K1:")
  exception BogusContext
  exception Restart of thm
  val hs = hypset th
  open BasicProvers simpLib

  fun do_disj_hyp th = let
    (* Called when th is of the form
         [...] |- (d1 \/ d2 \/ ... \/ dn) ==> t
       and when the disjunctive antecedent was originally a hypothesis along
       with the [...], but has been singled out for examination.

       Removes those di that would cause any of the hypotheses to become
       false, as long as the di is a simple equality.  You could try assuming
       each disjunct in turn and doing a general simplification but my
       instinct is that this would be too much work.  It seems that we do
       get series of equalities as disjuncts sufficiently often that this
       is worth doing.

       This is a specialised form of disjunctive case-splitting and may lead
       to duplicated work. *)
    val (ant, c) = dest_imp (concl th)
    val ds = strip_disj ant
    val (eqs, noneqs) = List.partition is_eq ds
    fun testeq t = let
      (* equality t can be kept *)
      val simp = QCONV (SIMP_CONV phase2_ss [ASSUME (orient_eq t)])
    in
      not (is_eliminable_equality t) orelse
      List.all (fn h => rhs (concl (simp h)) <> boolSyntax.F) (hyp th)
    end
    val (keep, lose) = List.partition testeq eqs
    val new = list_mk_disj (keep @ noneqs) handle HOL_ERR _ => F
  in
    if null lose then th
    else if null keep andalso null noneqs then
      (* this happens if all disjunctions causes an assumption to rewrite
         to false *)
      (output(hnd, "==All arms of " ^ term_to_string ant ^ " lead to F\n");
       raise BogusContext)
    else let
        val new_entail_old = superset_disj_rule (keep @ noneqs) ant
      in
        DISCH new (MP th new_entail_old)
      end
  end

  fun process_hyp0 th1 = let
    val result_t = #1 (dest_imp (concl th1))
  in
    if result_t = boolSyntax.T then MP th1 TRUTH
    else if result_t = boolSyntax.F then raise BogusContext
    else if is_assfailed result_t then
      (output(hnd, "==ASSERTION FAILURE: " ^
                   stringSyntax.fromHOLstring (dest_assfailed result_t) ^
                   "\n");
       raise BogusContext)
    else if is_eq result_t then
      (raise Restart (elim_equality hnd result_t th1))
      handle HOL_ERR _ => clean_and_undisch_equality th1
    else if is_var result_t then
      raise Restart (elim_equality hnd (mk_eq(result_t, boolSyntax.T)) th1)
    else if is_neg result_t andalso is_var (dest_neg result_t) then
      raise Restart
              (elim_equality hnd (mk_eq(dest_neg result_t, boolSyntax.F)) th1)
    else if is_conj result_t then raise Restart (disch_conjuncts th1)
    else if is_exists result_t then
      process_hyp (SPEC_ALL (CONV_RULE LEFT_IMP_EXISTS_CONV th1))
    else if is_clet result_t then
      process_hyp
        (process_hyp (SPEC_ALL
                        (CONV_RULE
                           (HO_REWR_CONV
                              LetComputeTheory.CLET_pending) th1)))
    else if is_pending result_t then
      process_hyp
        (CONV_RULE (LAND_CONV
                      (pending_structure_reduction_CONV structure_map))
                   th1)
        handle HOL_ERR _ => UNDISCH th1
    else UNDISCH th1
  end
  and process_hyp th = let
    val result_t = #1 (dest_imp (concl th))
  in
    if is_disj result_t then process_hyp0 (do_disj_hyp th)
    else process_hyp0 th
  end

(* the code below works over the theorem's hypotheses.
    - foldhyps pulls each hypothesis out (using DISCH) and makes it the
      antecedent of an assumption.

    - it next calls transform_hyp (passed in as parameter f) on this
      antecedent.
        * transform_hyp applies the simplifier
    - then process_hyp is called on the whole theorem (hyp' ==> concl)
      to do something appropriate with hyp'.  process_hyp always gets
      rid of the hypothesis, whether by throwing it away in the case
      of hyp' = T, or by moving it (or a transformed version of it)
      into the assumptions.

    - if the simplifier modified the hypothesis, or if the process_hyp
      function modifies the hypothesis in a "significant" way, then the
      Restart exception will be raised, and the whole process will begin
      again.
 *)
  fun foldhyps f s th = let
    fun do_hyp (h, th) = let
      val _ = mytrace(hnd,"K1a:")
      val th' = DISCH h th
    in
      let val _ = mytrace(hnd,"K2:")
          val asms = map ASSUME (hyp th')
          val _ = mytrace(hnd,"K3:")
          val h' = f asms h (* simplifier will often raise UNCHANGED here *)
          val _ = mytrace(hnd,"K4:")
          val th'' = EQ_MP (AP_THM (AP_TERM implication h') (concl th)) th'
          val _ = mytrace(hnd,"K5:")
      in
        raise Restart (process_hyp th'')
      end handle HOL_ERR _ => (mytrace(hnd,"K3a:"); raise Problem(h,th))
               | UNCHANGED => (mytrace(hnd,"K3b:"); process_hyp th')
    end
  in
    HOLset.foldl do_hyp th s
  end
  val stdsimp = SIMP_CONV (phase2_ss ++ numSimps.ARITH_ss)
  fun transform_hyp asms t = let
    val _ = mytrace(hnd,"K3k:")
    val _ = not (is_vrecord t) orelse raise UNCHANGED
    val newt = stdsimp asms t
  in
    output(hnd, "== Assumption "^term_to_string t^" transformed to: "^
                term_to_string (rhs (concl newt))^"\n");
    mytrace(hnd,"K3l:");
    newt
  end
in
  SOME (foldhyps transform_hyp hs th)
  handle BogusContext => NONE
       | Restart th' => cleanup_ctxts hnd th'
end handle Interrupt => (working_thm := th ; raise Interrupt)

fun ctxt_then_body hnd =
    Option.map (ASM_SIMP_RULE (phase2_ss ++ numSimps.ARITH_ss) []) o
    cleanup_ctxts hnd o eliminate_hyp_equalities hnd


fun cleanup_simped_implication hnd th = let
  val _ = mytrace(hnd,"S1:")
  (* remove ex. quantifications: turn into universals, and then 'SPEC'. *)
  val exes_removed = SPEC_ALL (CONV_RULE repeated_limp_ex_conv th)
  (* move lhs of implication into hypotheses, (lets turn into pendings) *)
  val _ = mytrace(hnd,"S2:")
  val de_imped = eliminate_equalities exes_removed
  (* look for more interesting terms to infer facts about *)
  val _ = mytrace(hnd,"S3:")
  val extra_constraints =
      TCP1_boundsInference.infer_other_constraints
        (SIMP_CONV phase1_ss []) de_imped
  val _ = mytrace(hnd,"S4:")
  val ret = ctxt_then_body hnd extra_constraints
  val _ = mytrace(hnd,"S5.")
in
  ret
end


(* ----------------------------------------------------------------------
    Case splitting

    On both the guards of conditional expressions and disjunctions that
    appear in theorem contexts.
   ---------------------------------------------------------------------- *)

(* find_free_conds: find conditional expressions in the term list
     given, such that the guard is not contaminated by reference to a
     bound variable, and doesn't itself include any conditionals.
     Don't bother returning conditional expressions that are in the
     branches of conditionals with valid guards, as we will always
     prefer the containing conditional. *)

datatype ffc_act = Check of term | LoseBvar
fun find_free_conds bvars acc tlist =
    case tlist of
      [] => acc
    | Check t::ts => let
      in
        if is_cond t then let
            val (g, _, _) = dest_cond t
            val ok_guard = not (List.exists (C free_in g) bvars) andalso
                           not (can (find_term is_cond) g)
          in
            if ok_guard then
              find_free_conds bvars (t::acc) ts
            else find_free_conds bvars acc (Check g :: ts)
          end
        else
          case dest_term t of
            COMB(t1, t2) => find_free_conds bvars acc (Check t1::Check t2::ts)
          | LAMB(v, bod) => find_free_conds (v::bvars) acc
                                            (Check bod::LoseBvar::ts)
          | _ => find_free_conds bvars acc ts
      end
    | LoseBvar :: ts => find_free_conds (tl bvars) acc ts

fun best_eliminable_condguard tlist = let
  val conds = find_free_conds [] [] (map Check tlist)
  fun numfvs t = HOLset.numItems (FVL [t] empty_tmset)
  fun order(t1,t2) = Int.compare(numfvs t1, numfvs t2)

(*  fun order(t1, t2) =
      Int.compare(term_size t2, term_size t1) (* want bigger terms earlier *) *)
in
  case List.find (fn t => term_size t > eliminable_cond_size)
                 (Listsort.sort order conds)
   of NONE => NONE
    | SOME c => SOME (#1 (dest_cond c))
end

(* does case-splitting on conditional expression guards *)
fun lookfor_and_remove_big_conds hnd th = let
  val output_host = rand (concl th)
  fun remove g th = let
    val _ = output(hnd, "==Case splitting on condition guard: " ^
                        term_to_string g ^ "\n")
    val th1 = ADD_ASSUM g th
    val th2 = ADD_ASSUM (mk_neg g) th
    val simped = seq.mapPartial (ctxt_then_body hnd) (seq.fromList [th1, th2])
  in
    seq.bind simped (lookfor_and_remove_big_conds hnd)
  end
in
  case best_eliminable_condguard (output_host :: hyp th) of
    NONE => seq.result th
  | SOME g => seq.delay (fn () => remove g th)
end

(* disjunctive case-splitting *)
fun lookfor_and_remove_big_disjs hnd th = let
  val ctxt = hypset th
  fun foldthis (c, acc) = if is_disj c then c :: acc else acc
  fun order(t1, t2) =
      Int.compare(term_size t2, term_size t1) (* want bigger terms earlier *)
  val disj_asms = Listsort.sort order (HOLset.foldl foldthis [] ctxt)
  val d = case disj_asms of
            [] => NONE
          | d :: _ => if term_size d > eliminable_disj_size then SOME d
                      else NONE
  fun disj_split d th = let
    val (d1, _) = dest_disj d
    val _ = output(hnd, "==Case splitting on 1st arg. of disjunction: "^
                        term_to_string d1 ^ "\n")
    val dT = EQT_INTRO (ASSUME d1)
    val dF = EQF_INTRO (ASSUME (mk_neg d1))
    val th' = DISCH d th
    fun rwt th1 th2 = CONV_RULE (LAND_CONV (LAND_CONV (REWR_CONV th1) THENC
                                            REWR_CONV th2)) th'
    val thT = MP (rwt dT T_or_l) TRUTH
    val thF = UNDISCH (rwt dF F_or_l)
    val simped = seq.mapPartial (ctxt_then_body hnd) (seq.fromList [thT, thF])
  in
    seq.bind simped (lookfor_and_remove_big_disjs hnd)
  end
in
  case d of
    NONE => seq.result th
  | SOME d => seq.delay (fn () => disj_split d th)
end



fun next_state ths = let
  val th = hd ths
in
  (rand (concl th), hyp th)
end

val trace_list = ref [] : thm list ref
val show_possibilities = ref 1;

fun appi f lst = let
  fun recurse n [] = ()
    | recurse n (h::t) = (f n h; recurse (n + 1) t)
in
  recurse 0 lst
end

fun announce_possibilities hnd ctxt th = let
  fun is_newlc t = let
    val (v, body) = dest_exists t
    val (l, r) = dest_eq body
  in
    l = v
  end handle HOL_ERR _ => false
  fun analyse_ctxt c0 c = let
    val s0 = HOLset.addList(empty_tmset, c0)
    val s = HOLset.addList(empty_tmset, c)
    val new_ctxt = HOLset.listItems (HOLset.difference(s, s0))
    val vars0 = FVL c0 empty_tmset
    val vars = FVL c empty_tmset
    val newvars = HOLset.listItems (HOLset.difference(vars, vars0))
    fun print_cst t = let
      val fvs = free_vars t
    in
      if is_vrecord t then ()
      else
        (if null fvs then output(hnd, " *** Grounded constraint!! ***\n")
         else ();
         output(hnd, term_to_string t ^ "\n");
         if null fvs then output(hnd, " *** Grounded constraint ends. ***\n")
         else ())
    end
  in
    if null new_ctxt then ()
    else let
        val _ = mytrace(hnd,"P3:")
        val new_var_strs = map (trace("types", 1) term_to_string) newvars
        val _ = mytrace(hnd,"P4.\n")
        val _ = htmlOutput hnd "<div class=\"newvars\"><pre>\n"
        val _ = app (fn s => output (hnd,s)) ("==New variables: " :: Lib.commafy new_var_strs)
        val _ = output (hnd,"\n")
        val _ = htmlOutput hnd "</pre></div><div class=\"newcons\"><pre>\n"
        val _ = output (hnd,"==New constraints:\n")
        val _ = app print_cst new_ctxt
        val _ = htmlOutput hnd "</pre></div>\n"
      in
        ()
      end
  end
  fun do_one_transition transition = let
    val _ = output(hnd,"==Successful transition of "^rule_name transition^"\n")
    val _ = htmlOutput hnd "<div class=\"poss\"><pre>\n"
    val _ = try_finally (fn () => let
      val _ = output (hnd,"==Possibility #1:\n")
      val _ = output (hnd, thm_to_string transition)
    in
      ()
    end) (fn () => altOutput hnd "\n</pre></div>\n" "\n")
    val _ = analyse_ctxt ctxt (hyp transition)
    val _ = textOutput hnd "\n*****\n"
  in
    ()
  end
  fun do_no_transitions () = let
    val _ = htmlOutput hnd "<div class=\"noposs\"><pre>\n"
    val _ = output (hnd,"==No possibilities -- about to backtrack\n")
    val _ = altOutput hnd "</pre></div>\n" "\n"
  in
    ()
  end
in
  case th of
    SOME th => do_one_transition th
  | NONE => do_no_transitions ()
end

fun mtimestamp () =
    let val t = Time.now () in
        "<" ^
        Date.fmt "%Y-%m-%d T %H:%M:%S Z (%a)" (Date.fromTimeUniv t) ^
        "> " ^
        Time.fmt 0 t
    end


fun record_new_variables ctxt th = let
  val c0 = FVL ctxt empty_tmset
  val c = FVL [concl th] (hyp_frees th)
  val diff = HOLset.difference (c, c0)
  fun addassum (v, th) = ADD_ASSUM (mk_vrecord v) th
in
  HOLset.foldl addassum th diff
end

(* THE DRIVER *)
(* n is step number, lab is label, h is host, ctxt is context *)
fun do_mstep hnd label rest (n, host, ctxt) = let
  val _ = htmlOutput hnd "<div>\n"
  val (ths,cputimer,th,cpu_time_elapsed,unwind_time) =
    try_finally (fn () => let
      val (ths,cputimer,th,cpu_time_elapsed,unwind_time) =
        (htmlOutput hnd "<div><pre>\n";
         try_finally (fn () => let
           val _ = output_and_print (hnd,"==Step "^Int.toString n^" at "^mtimestamp()^":\n")
           val _ = output (hnd," "^term_to_string label^"\n")
           fun phase s th = (output (hnd, " -- "^s); th)
           val ths =
               seq.mapPartial
                 (cleanup_simped_implication hnd o phase "ctxtclean\n")
                 (seq.delay (fn () => spec_n_simp hnd ctxt host label rest))
           val ths = seq.bind ths (lookfor_and_remove_big_conds hnd)
           val ths = seq.bind ths (lookfor_and_remove_big_disjs hnd)
           val ths = seq.map (record_new_variables ctxt) ths
           (* force evaluation of head *)
           val cputimer = Timer.startCPUTimer ()
           val _ = Profile.reset_all()
           val th = SOME (seq.hd ths) handle Fail _ => NONE (* force *)
           val cpu_time_elapsed = #usr (Timer.checkCPUTimer cputimer)
           val unwind_time = #usr (Lib.assoc "UNWIND" (Profile.results()))
                             handle HOL_ERR _ => Time.zeroTime
           val _ = output (hnd,"CPU time elapsed : "^
                               Time.toString cpu_time_elapsed^ " seconds ")
           val _ = output (hnd,"(unwind: "^Time.toString unwind_time^")\n")
           val _ = Profile.output_profile_results hnd (Profile.results())
         in
           (ths,cputimer,th,cpu_time_elapsed,unwind_time)
         end
         ) (fn () => htmlOutput hnd "</pre></div>"))
      val _ = announce_possibilities hnd ctxt th (* print out one possibility *)
    in
      (ths,cputimer,th,cpu_time_elapsed,unwind_time)
    end
    ) (fn () => (htmlOutput hnd "</div>\n"; TextIO.flushOut hnd))
  fun mk_next th = let
    val h = rand (concl th)
    val c = hyp th
  in
    ((if label = ``Lh_tau`` then n else n + 1, h, c),
     (th, n, Time.toMilliseconds cpu_time_elapsed,
      Time.toMilliseconds unwind_time))
  end
in
  seq.map mk_next ths (* ...but iterate on *all* possibilities; some of
                         them may die later; this is backtracking *)
end

fun mmap f list x = seq.delay (fn () => seqmonad.mmap f list x)

(* do taus if necessary *)
fun poss_taustep hnd lab rest = let
  open seqmonad
  infix ++ >-
in
  (do_mstep hnd lab rest >- (fn x => return [x])) ++
  (do_mstep hnd ``Lh_tau`` (lab::rest) >-
    (fn x => poss_taustep hnd lab rest >- (fn y => return (x :: y))))
end

local open BasicProvers simpLib bossLib
in

val antisymmetric_bounds = Phase.phase_imm 3 (prove(
  ``(c <= x:real /\ x <= c /\ p) = (c = x /\ p)``,
  SRW_TAC [][realTheory.REAL_LE_REFL, EQ_IMP_THM] THEN
  PROVE_TAC [realTheory.REAL_LE_ANTISYM]));

end

local
  open TCP1_urgencyTheory
  val eps_rule = better_epsilon_rule
  val timepass_rwts = Phase.get_phase_list 3 @
                      [Time_Pass_host_rel_def, Time_Pass_socket_rel_def,
                       Time_Pass_tcpcb_rel_def,
                       relify_def, fm_range_relates_FUPDATE,
                       fm_range_relates_FEMPTY,
                       finite_mapTheory.o_f_FUPDATE,
                       finite_mapTheory.o_f_FEMPTY,
                       realTheory.REAL_ADD_LID,
                       realTheory.REAL_MUL_RID]
  val timepass_ss = phase2_ss ++ rewrites timepass_rwts

  exception NotUrgent of (Time.time * Time.time) * term
  val urgent_rwts = [DISJ_IMP_THM,
                     TCP1_evalSupportTheory.dummy_socket_def,
                     nonurgent_approx_def]

in
fun do_epsilon hnd label rest (n, host, ctxt) = let

  open simpLib BasicProvers
  val _ = check_btrack hnd
  val dur = rand label
  val cputimer = Timer.startCPUTimer()
  val _ = Profile.reset_all()
  val (cpu_time_elapsed, unwind_time, ths) =
    (htmlOutput hnd "<div>\n";
     try_finally (fn () => let
       val (cpu_time_elapsed, unwind_time, thopt) =
         (htmlOutput hnd "<div><pre>\n";
          try_finally (fn () => let
            val _ = output_and_print (hnd,"==Step "^Int.toString n^" at "^mtimestamp()^":\n")
            val _ = output (hnd," attempting time passage with duration "^term_to_string dur^"\n")
            fun times () = (#usr (Timer.checkCPUTimer cputimer),
                            #usr (Lib.assoc "UNWIND" (Profile.results()))
                            handle HOL_ERR _ => Time.zeroTime)
            val _ = mytrace(hnd,"T1:")
            val nonurgent = SPEC host nonurgent_characterisation
            val _ = mytrace(hnd,"T2:")
            val nonurgent =
                CONV_RULE (LAND_CONV
                             (SIMP_CONV phase2_ss (urgent_rwts @ map ASSUME ctxt)))
                          nonurgent
            val _ = mytrace(hnd,"T3:")
            val nonurgent =
                EQT_INTRO (MP nonurgent TRUTH)
                handle HOL_ERR err =>
                       raise NotUrgent(times(),#1 (dest_imp (concl nonurgent)))
            val _ = mytrace(hnd,"T4:")


            val rule = REWRITE_RULE [nonurgent]
                                    (SPEC_ALL (SPECL [host, dur] eps_rule))
            val _ = mytrace(hnd,"T5:")
            val simp_conv  = SIMP_CONV timepass_ss
            val _ = mytrace(hnd,"T6:")
            val conv = REPEATC (CHANGED_CONV (REWRn true (map ASSUME ctxt) 10 simp_conv))
            val _ = mytrace(hnd,"T7:")
            val rule = CONV_RULE (LAND_CONV conv) rule
            val _ = mytrace(hnd,"T8:")
            val (cpu_time_elapsed, unwind_time) = times()
            val _ = output (hnd,"CPU time elapsed : "^Time.toString cpu_time_elapsed^
                                " seconds")
            val _ = output (hnd,"(unwind: "^Time.toString unwind_time^")\n")
            fun try_ticker_elim th = let
              val newth = eliminate_redundant_tickers th
            in
              output(hnd, "Eliminated redundant ticker time passages\n");
              newth
            end handle Conv.UNCHANGED => th
                     | HOL_ERR _ => th
            val _ = mytrace(hnd,"T8a:") (* redundant, I think *)
            val thopt =
                if #1 (dest_imp (concl rule)) = boolSyntax.F then
                  (output (hnd,"Couldn't prove time passage\n"); NONE)
                else
                   let val _ = mytrace(hnd,"T9:")
                       val ctxt_rule0 = itlist ADD_ASSUM ctxt rule
                       val _ = mytrace(hnd,"T9a:")
                       val ctxt_rule1 = cleanup_simped_implication hnd ctxt_rule0
                       val _ = mytrace(hnd,"T9b:")
                       val ctxt_rule2 = Option.map try_ticker_elim ctxt_rule1
                       val _ = mytrace(hnd,"T9c:")
                       val ctxt_rule3 = Option.map TCP1_boundsInference.augment_theorem ctxt_rule2
                   in
                       ctxt_rule3
                   end
            val _ = mytrace(hnd,"T10.\n")
          in
            (cpu_time_elapsed, unwind_time, thopt)
          end
          ) (fn () => htmlOutput hnd "</pre></div>\n"))
       val _ = announce_possibilities hnd ctxt thopt
     in
       (cpu_time_elapsed, unwind_time, case thopt of NONE => seq.empty | SOME th => seq.result th)
     end
     ) (fn () => (htmlOutput hnd "</div>\n"; TextIO.flushOut hnd)))
  fun mk_next th = let
    val h = rand (concl th)
    val c = hyp th
  in
    ((n + 1, h, c), [(th, n, Time.toMilliseconds cpu_time_elapsed,
                      Time.toMilliseconds unwind_time)])
  end
in
  seq.map (mk_next o record_new_variables ctxt) ths
end handle NotUrgent (_,err) => (output (hnd,"Couldn't prove non-urgency\n");
                                 htmlOutput hnd "<pre>\n";
                                 output (hnd,term_to_string err);
                                 output (hnd, "\n");
                                 htmlOutput hnd "</pre>\n";
                                 seq.empty)

(* do taus if necessary *)
fun tauepsilon_step hnd lab rest = let
  open seqmonad
  infix ++ >-
in
  do_epsilon hnd lab rest ++
  (do_mstep hnd ``Lh_tau`` (lab :: rest) >-
    (fn x => tauepsilon_step hnd lab rest >- (fn y => return (x :: y))))
end



fun timed_step hnd lab rest = let
  open seqmonad
  infix >-
  val (hdop, _) = strip_comb lab
  val redn0_rule = last (CONJUNCTS TCP1_hostLTSTheory.host_redn_rules)
in
  if same_const hdop lheps_t then
    tauepsilon_step hnd lab rest
  else
    poss_taustep hnd lab rest >-
    (fn transitions =>
        return (map (fn (th,n,t1,t2) =>
                        (MATCH_MP redn0_rule th, n, t1, t2))
                    transitions))
end

end (* local *)



open TraceFiles

fun simp_hostlabels_from_file hnd fname = let
  val _ = mytrace(hnd, "L0")
  val (host0, labels) = host_and_labels_from_file fname
  open simpLib BasicProvers
  val _ = output (hnd,"==Simplifying host and labels from disk ... ")
  val simps = Phase.get_phase_list 0

  fun simpit t = rhs (concl (QCONV (SIMP_CONV phase2_ss simps) t))
in
  (simpit host0, map simpit labels) before output (hnd,"done\n")
end

local open seqmonad infix >-
in
(* mymmap maps a function over a list in monadic sequence, and passes not
   just each element to f, but also the remainder of the list at that point. *)
fun mymmap f [] = return []
  | mymmap f (h::t)  =
      f h t >- (fn r => mymmap f t >- (fn rl => return (r::rl)))
end

fun calculate_initial_context host = let
  (* the initial host will contain an unconstrained ticker value that needs
     to be assumed to be well-formed. *)
  val ticker_val = find_term (fn t => type_of t = ``:ticker``) host
  val components = pairSyntax.strip_pair (rand ticker_val)
  val remdr = List.nth(components, 1)
  val tick_imax = last components
in
  [realSyntax.mk_leq(realSyntax.zero_tm, remdr),
   realSyntax.mk_less(remdr, tick_imax),
   mk_vrecord remdr]
end

fun do_timed_trace hnd (host, labels) = let
  open seqmonad
  infix >-
  val tracelength = length labels
  val _ = (* set up limit *)
      btrack_node_count_limit :=
      (case !btrack_control of
        NONE => ~1
      | SOME (AbsExtra n) => tracelength + n
      | SOME (PercentExtra n) =>
        trunc (real tracelength * real (100 + n) / 100.0))
in
  (mymmap (timed_step hnd) labels >- (return  o List.concat))
    (0, host, calculate_initial_context host)
end

fun continue_trace hnd s1 more_labels = let
  open seqmonad
  infix >-
  fun cont (state as (n,h,c), ths) =
      (mymmap (timed_step hnd) more_labels >- (return o List.concat)) state
in
  seq.delay (fn () => seq.flatten (seq.map cont s1))
end

fun do_pfx_trace_from_file hnd n fname = let
  val (host, labels0) = simp_hostlabels_from_file hnd fname
  val s = do_timed_trace hnd (host, List.take(labels0, n))
  val (state, thmll) = seq.hd s
  (* thmll above is a list of theorems.  Each list is one trace;
     each theorem in the trace is a theorem stating that
        h_i -- lab --> h_(i+1)
  *)
  fun is_lv t = #1 (dest_var (#1 (dest_exists t))) = "is_lc"
                handle HOL_ERR _ => false
  val (constraints, lvs0) = partition (not o is_lv) (#3 state)
  val lvs = map (fn t => rhs (#2 (dest_exists t))) lvs0
in
  {final_state = #2 state, final_constraints = constraints,
   new_local_constants = lvs, thm_trace = thmll}
  (* local constants being existentially quantified variables from a rule that
     can't be deduced as having a specific value, most will be constrained
     by the constraints *)
end

(*
fun condprinter sysprint gravs depth pps t =
    if depth = 0 then PP.add_string pps "..."
    else if is_cond t then let
        val (g,th,el) = dest_cond t
        open term_pp_types
      in
        PP.add_string pps "(";
        PP.begin_block pps PP.CONSISTENT 0;
        PP.add_string pps "if";
        PP.add_break pps (1,2);

        sysprint (Top,Top,Top) depth g;
        PP.add_break pps (1,~2);

        PP.add_string pps "then";
        PP.add_break pps (1,2);

        sysprint (Top,Top,Top) 2 th;
        PP.add_break pps (1,~2);

        PP.add_string pps "else";
        PP.add_break pps (1,2);

        sysprint (Top,Top,Top) 2 el;
        PP.end_block pps;
        PP.add_string pps ")"
      end
    else raise term_pp_types.UserPP_Failed

val _ = temp_add_user_printer ({Tyop="", Thy = ""},condprinter)
*)
val _ = Globals.linewidth := 160;
