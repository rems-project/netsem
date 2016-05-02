(* A HOL98 specification of TCP *)

(* Proofs of properties of timers *)

(*[ RCSID "$Id: TCP1_timerPropsScript.sml,v 1.5 2006/02/20 23:03:47 mn200 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse

open BasicProvers bossLib

open HolDoc

local open TCP1_baseTypesTheory TCP1_utilsTheory TCP1_utilPropsTheory in end

local open arithmeticTheory realTheory wordsTheory in end;

val _ = BasicProvers.augment_srw_ss [rewrites [LET_THM]]

val _ = new_theory "TCP1_timerProps";

open TCP1_timersTheory

(* -------------------------------------------------------------------- *)
(*   PROOFS                                                             *)
(* -------------------------------------------------------------------- *)


val FORALL_ticker = prove(
  ``(!t. P t) = (!t r i1 i2. P (Ticker (t,r,i1,i2)))``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM] THEN STRIP_TAC THEN Cases THEN
  Q.ID_SPEC_TAC `p` THEN
  ASM_SIMP_TAC bool_ss [pairTheory.FORALL_PROD]);

val ticker_ok_preserved = store_thm(
  "ticker_ok_preserved",
  ``!t0 t d. ticker_ok t0 /\ 0 <= d /\ Time_Pass_ticker d t0 t ==>
             ticker_ok t``,
  SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss ++ realSimps.REAL_ARITH_ss)
           [FORALL_ticker, LET_THM, Time_Pass_ticker_def,
            ticker_ok_def]);


val Time_Pass_ticker_additive = store_thm(
  "Time_Pass_ticker_additive",
  ``time_pass_additive Time_Pass_ticker``,
  SIMP_TAC (srw_ss()) [time_pass_additive_def, FORALL_ticker,
                       Time_Pass_ticker_def] THEN REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `delta + delta'` THEN
  SRW_TAC [][] THEN
  SIMP_TAC bool_ss [GSYM realTheory.REAL_ADD,
                    realTheory.REAL_ADD_RDISTRIB]
  THENL [
    POP_ASSUM_LIST (MAP_EVERY MP_TAC) THEN RealArith.REAL_ARITH_TAC,
    POP_ASSUM_LIST (MAP_EVERY MP_TAC) THEN RealArith.REAL_ARITH_TAC,
    Cases_on `s0` THEN
    SRW_TAC [][TCP1_baseTypesTheory.seq32_plus_def,
               GSYM wordsTheory.WORD_ADD_ASSOC,
               wordsTheory.word_add_n2w]
  ]);

val seq32_add_rid = prove(
  ``(x : 'a seq32) + 0n = x``,
  Cases_on `x` THEN
  simpLib.SIMP_TAC (srw_ss())
                   [TCP1_baseTypesTheory.seq32_plus_def,
                    REWRITE_RULE [wordsTheory.word_0] wordsTheory.WORD_ADD_0]);


val ARITH_TAC = POP_ASSUM_LIST (MAP_EVERY MP_TAC) THEN
                RealArith.REAL_ARITH_TAC

(* Going back to the original Lynch and Vaandrager paper, I see that
   they require two properties of time, S1 and S2 (see above).

   They also mention a weaker form, S2', which says that for any step
   and any time point within the step, an intermediate state can be
   found such that the step can be broken into two steps.  This is
   what I was reaching towards above I think.

*)



(* I believe Time_Pass_ticker_trajectory holds because you can compute the number of ticks
   between s0 and s1, and the time consumed (dur+r0-r1), and divide
   the latter by the former.  This gives an interval in
   [intvlmin,intvlmax], which can then be assumed to be a fixed rate
   during [0,dur], and used to compute w(t) states in the obvious
   way.

   ---

   In fact, it doesn't hold as stated because you need some invariants
   on the state of the ticker, those that appear in the ticker_ok
   definition above are probably sufficient.

   Below, I prove the weaker S2' property, and need some of these
   preconditions.  I could probably prove a time_pass_trajectory like
   result of the following form:

    time_pass_trajectory (\d t1 t2. ticker_ok t1 /\ 0 <= d /\
                                    Time_Pass_ticker d t1 t2)

   encoding the pre-condition into the relation.
*)

(* Proof of property S2', which will allow elimination of redundant
   intermediate ticker values (apply this from left to right) *)

(* first some factoids about num_floor *)
val add1_gt_exists = prove(
  ``!y : real. ?n. (&) (n + 1) > y``,
  GEN_TAC THEN Q.SPEC_THEN `1` MP_TAC realTheory.REAL_ARCH THEN
  SIMP_TAC (srw_ss()) [] THEN
  DISCH_THEN (Q.SPEC_THEN `y` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `n` THEN
  SIMP_TAC bool_ss [GSYM realTheory.REAL_ADD] THEN ARITH_TAC);

val lt_add1_exists = prove(
  ``!y: real. ?n. y < (&)(n + 1)``,
  GEN_TAC THEN Q.SPEC_THEN `1` MP_TAC realTheory.REAL_ARCH THEN
  SIMP_TAC (srw_ss()) [] THEN
  DISCH_THEN (Q.SPEC_THEN `y` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `n` THEN
  SIMP_TAC bool_ss [GSYM realTheory.REAL_ADD] THEN ARITH_TAC);


val floor_x_le_x = prove(
  ``0 <= x ==> (&)(num_floor x) <= x``,
  SRW_TAC [][TCP1_utilsTheory.num_floor_def] THEN
  CONV_TAC (UNBETA_CONV ``LEAST n. (&)(n + 1) > x:real``) THEN
  MATCH_MP_TAC whileTheory.LEAST_ELIM THEN
  SRW_TAC [][add1_gt_exists] THEN
  Cases_on `n` THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
  SRW_TAC [numSimps.ARITH_ss][realTheory.real_gt, realTheory.REAL_NOT_LT,
                              arithmeticTheory.ADD1]);

val x_le_num_floor = prove(
  ``0 <= y ==> (x <= num_floor y) = ((&)x <= y)``,
  SRW_TAC [][TCP1_utilsTheory.num_floor_def] THEN
  CONV_TAC (UNBETA_CONV ``LEAST n. (&)(n + 1) > y:real``) THEN
  MATCH_MP_TAC whileTheory.LEAST_ELIM THEN
  SRW_TAC [][lt_add1_exists, realTheory.real_gt,
             realTheory.REAL_NOT_LT, EQ_IMP_THM]
  THENL [
    Cases_on `n` THENL [
      FULL_SIMP_TAC (srw_ss()) [],
      FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
      FULL_SIMP_TAC (bool_ss ++ numSimps.ARITH_ss)
                    [arithmeticTheory.ADD1, GSYM realTheory.REAL_ADD,
                     GSYM realTheory.REAL_LE] THEN
      ARITH_TAC
    ],
    `(&)x < (&)(n + 1):real` by PROVE_TAC [realTheory.REAL_LET_TRANS] THEN
    FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) []
  ]);

val num_floor_le_x = prove(
  ``(num_floor x <= y) <=> x < (&)y + 1``,
  SRW_TAC [][TCP1_utilsTheory.num_floor_def] THEN
  CONV_TAC (UNBETA_CONV ``LEAST n. (&)(n + 1) > x:real``) THEN
  MATCH_MP_TAC whileTheory.LEAST_ELIM THEN
  SRW_TAC [][lt_add1_exists, realTheory.real_gt,
             realTheory.REAL_NOT_LT, EQ_IMP_THM]
  THENL [
    FULL_SIMP_TAC bool_ss [GSYM realTheory.REAL_LE,
                           GSYM realTheory.REAL_ADD] THEN
    MATCH_MP_TAC realTheory.REAL_LTE_TRANS THEN
    Q.EXISTS_TAC `(&)n + 1` THEN
    SRW_TAC [][],
    Cases_on `n` THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
    FULL_SIMP_TAC (bool_ss ++ numSimps.ARITH_ss)
                  [arithmeticTheory.ADD1] THEN STRIP_TAC THEN
    `(&)(n' + 1) < (&)(y + 1):real` by ARITH_TAC THEN
    FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) []
  ]);

val num_floor_div = prove(
  ``0 <= x /\ 0 < y ==> (&)(num_floor (x / y)) * y <= x``,
  SRW_TAC [][TCP1_utilsTheory.num_floor_def] THEN
  CONV_TAC (UNBETA_CONV ``LEAST n. (&)(n + 1) > x / y:real``) THEN
  MATCH_MP_TAC whileTheory.LEAST_ELIM THEN
  SRW_TAC [][add1_gt_exists] THEN Cases_on `n` THEN1 SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
  SRW_TAC [numSimps.ARITH_ss]
          [realTheory.real_gt, realTheory.REAL_NOT_LT,
           arithmeticTheory.ADD1, realTheory.REAL_LE_RDIV_EQ]);

val num_floor_div_lowerbound = prove(
  ``0 <= x:real /\ 0 < y:real ==> x < (&)(num_floor (x/y) + 1) * y ``,
  SRW_TAC [][TCP1_utilsTheory.num_floor_def] THEN
  CONV_TAC (UNBETA_CONV ``LEAST n. (&)(n + 1) > x / y:real``) THEN
  MATCH_MP_TAC whileTheory.LEAST_ELIM THEN
  SRW_TAC [][add1_gt_exists] THEN Cases_on `n` THEN
  POP_ASSUM MP_TAC THEN
  SRW_TAC [][realTheory.real_gt, realTheory.REAL_LT_LDIV_EQ]);

val num_floor_eqns = store_thm(
  "num_floor_eqns",
  ``(num_floor (real_of_num n) = n) /\
    (0 < m ==> (num_floor (real_of_num n / real_of_num m) = n DIV m))``,
  SRW_TAC [][TCP1_utilsTheory.num_floor_def] THENL [
    numLib.LEAST_ELIM_TAC THEN
    SIMP_TAC (srw_ss()) [realTheory.real_gt, realTheory.REAL_LT] THEN
    intLib.ARITH_TAC,
    numLib.LEAST_ELIM_TAC THEN
    ASM_SIMP_TAC (srw_ss())
                 [realTheory.real_gt, realTheory.REAL_LT_LDIV_EQ] THEN
    CONJ_TAC THENL [
      Q.EXISTS_TAC `n` THEN
      Cases_on `m` THEN
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [arithmeticTheory.MULT_CLAUSES],

      Q.HO_MATCH_ABBREV_TAC `!p. (!i. i < p ==> ~(n < (i + 1) * m)) /\
                                 n < (p + 1) * m ==>
                                 p = n DIV m` THEN
      REPEAT STRIP_TAC THEN
      CONV_TAC (REWR_CONV EQ_SYM_EQ) THEN
      MATCH_MP_TAC arithmeticTheory.DIV_UNIQUE THEN
      `(p = 0) \/ (?p0. p = SUC p0)`
         by PROVE_TAC [arithmeticTheory.num_CASES] THEN
      FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                    [arithmeticTheory.ADD1,
                     arithmeticTheory.LEFT_ADD_DISTRIB] THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `p0` MP_TAC) THEN
      SRW_TAC [numSimps.ARITH_ss][arithmeticTheory.NOT_LESS] THEN
      Q.EXISTS_TAC `n - (m + p0 * m)` THEN
      SRW_TAC [numSimps.ARITH_ss][]
    ]
  ]);
val _ = Phase.add_to_phase 1 "num_floor_eqns"

val num_floor_lower_bound = store_thm(
  "num_floor_lower_bound",
  ``(x:real < (&)n) = (num_floor(x+1) <= n)``,
  MP_TAC (Q.INST [`x` |-> `x + 1`, `y` |-> `n`] num_floor_le_x) THEN
  SIMP_TAC (srw_ss()) []);

val num_floor_upper_bound = store_thm(
  "num_floor_upper_bound",
  ``((&)n <= x:real) = (n < num_floor(x + 1))``,
  MP_TAC (AP_TERM negation num_floor_lower_bound) THEN
  PURE_REWRITE_TAC [realTheory.REAL_NOT_LT, arithmeticTheory.NOT_LESS_EQUAL,
                    IMP_CLAUSES]);

open metisLib

val ticker_alternative = prove(
  ``0 < imin /\ imin <= imax ==>
    (Time_Pass_ticker d (Ticker(t0, r0, imin, imax)) t =
      ?i delta.
         (&)delta * i <= r0 + d /\ r0 + d < (&)delta * i + imax /\
         imin <= i /\ i <= imax /\
         t = Ticker(t0 + delta, r0 + d - (&)delta * i, imin, imax))``,
  SRW_TAC [][Time_Pass_ticker_def] THEN EQ_TAC THEN SRW_TAC [][] THENL[
    Cases_on `delta = 0` THENL [
      FULL_SIMP_TAC (srw_ss()) [realTheory.REAL_SUB_RZERO] THEN
      `remdr' = r0 + d` by PROVE_TAC [realTheory.REAL_LE_ANTISYM] THEN
      MAP_EVERY Q.EXISTS_TAC [`imin`, `0`] THEN
      SRW_TAC [][realTheory.REAL_SUB_RZERO] THEN ARITH_TAC,
      `0 < delta` by PROVE_TAC [arithmeticTheory.NOT_ZERO_LT_ZERO] THEN
      MAP_EVERY Q.EXISTS_TAC [`(r0 + d - remdr') / (&)delta`, `delta`] THEN
      SRW_TAC [][realTheory.REAL_DIV_LMUL, realTheory.REAL_LE_LDIV_EQ,
                 realTheory.REAL_LE_RDIV_EQ] THEN ARITH_TAC
    ],
    Q.EXISTS_TAC `delta` THEN
    SRW_TAC [][prove(``(x:real - y:real <= x - z) = (z <= y)``, ARITH_TAC),
               realTheory.REAL_LE_LMUL_IMP] THEN ARITH_TAC
  ]);

val real_sub' = prove(``x <= y ==> (&)(y - x):real = (&)y - (&)x``,
                      SRW_TAC [][realTheory.REAL_SUB] THEN
                      IMP_RES_TAC arithmeticTheory.LESS_EQUAL_ANTISYM THEN
                      SRW_TAC [][]);

val seq32_add_assoc = prove(
  ``((x : 'a seq32) + y:num) + z = x + (y + z)``,
  Cases_on `x` THEN
  SRW_TAC [][TCP1_baseTypesTheory.seq32_plus_def,
             GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w]);

(* Finally, the result we've all been waiting for... *)
val time_pass_exists_eliminate = store_thm(
  "time_pass_exists_eliminate",
  ``0 <= dur1 /\ 0 <= dur2 /\ ticker_ok t0 ==>
       (?t'. Time_Pass_ticker dur1 t0 t' /\ Time_Pass_ticker dur2 t' t) =
       Time_Pass_ticker (dur1 + dur2) t0 t``,
  STRIP_TAC THEN EQ_TAC THENL [
    METIS_TAC [time_pass_additive_def, Time_Pass_ticker_additive],
    Q.UNDISCH_THEN `ticker_ok t0` MP_TAC THEN
    MAP_EVERY Q.ID_SPEC_TAC [`t0`,`t`] THEN
    SIMP_TAC (srw_ss()) [FORALL_ticker, ticker_alternative, ticker_ok_def,
                         GSYM LEFT_FORALL_IMP_THM,
                         GSYM LEFT_EXISTS_AND_THM,
                         GSYM RIGHT_EXISTS_AND_THM] THEN
    SRW_TAC [][] THEN
    `0 < i` by IMP_RES_TAC realTheory.REAL_LTE_TRANS THEN
    Q.ABBREV_TAC `delta1 = MIN (num_floor ((r' + dur1) / i)) delta` THEN
    `0 <= (r' + dur1) / i` by SRW_TAC [][realTheory.REAL_LE_RDIV_EQ,
                                         realTheory.REAL_LE_ADD] THEN
    `(&)delta1 * i <= r' + dur1`
       by (Q.UNABBREV_TAC `delta1` THEN
           SRW_TAC [][arithmeticTheory.MIN_DEF] THENL [
             MATCH_MP_TAC num_floor_div THEN ARITH_TAC,
             POP_ASSUM MP_TAC THEN
             SRW_TAC [][arithmeticTheory.NOT_LESS, x_le_num_floor,
                        realTheory.REAL_LE_RDIV_EQ]
           ]) THEN
    `r' + dur1 < (&)delta1 * i + i2`
       by (SRW_TAC [][arithmeticTheory.MIN_DEF, Abbr`delta1`] THENL [
             MATCH_MP_TAC realTheory.REAL_LTE_TRANS THEN
             Q.EXISTS_TAC `(&)(num_floor ((r' + dur1) / i) + 1) * i` THEN
             CONJ_TAC THENL [
               MATCH_MP_TAC num_floor_div_lowerbound THEN
               SRW_TAC [][realTheory.REAL_LE_ADD],
               REWRITE_TAC [GSYM realTheory.REAL_ADD,
                            realTheory.REAL_RDISTRIB] THEN
               SRW_TAC [][]
             ],
             MATCH_MP_TAC realTheory.REAL_LET_TRANS THEN
             Q.EXISTS_TAC `r' + (dur1 + dur2)` THEN
             SRW_TAC [][realTheory.REAL_LE_ADDR]
           ]) THEN
    `delta1 <= delta` by SRW_TAC [][Abbr`delta1`] THEN
    MAP_EVERY Q.EXISTS_TAC [`i`, `delta1`, `i`, `delta - delta1`] THEN
    ASM_SIMP_TAC (srw_ss()) [real_sub', realTheory.REAL_SUB_RDISTRIB] THEN
    REPEAT CONJ_TAC THENL [
      ARITH_TAC,
      ARITH_TAC,
      ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)[seq32_add_assoc],
      ARITH_TAC
    ]
  ]);

val another_thing_we_want_to_be_true = store_thm(
  "another_thing_we_want_to_be_true",
  ``!d intvlmax intvlmin delta remdr'.
      d - real_of_num delta * intvlmax <= remdr' /\
      remdr' <= d - real_of_num delta * intvlmin /\
      0 <= remdr' /\ remdr' < intvlmax /\ 0 < intvlmin
     ==>
      (num_floor (d / intvlmax) <= delta /\ delta <= num_floor (d / intvlmin))
  ``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC (srw_ss()) [num_floor_le_x] THEN
  `(&)delta * intvlmin <= (&)delta * intvlmax`
     by (POP_ASSUM_LIST (MAP_EVERY MP_TAC) THEN
         RealArith.REAL_ARITH_TAC) THEN
  `0 <= (&)delta * intvlmax`
     by (MATCH_MP_TAC realTheory.REAL_LE_MUL THEN SRW_TAC [][] THEN
         PROVE_TAC [realTheory.REAL_LET_TRANS, realTheory.REAL_LT_IMP_LE]) THEN
  `0 <= (&)delta * intvlmin`
     by (MATCH_MP_TAC realTheory.REAL_LE_MUL THEN SRW_TAC [][] THEN
         ARITH_TAC) THEN
  `remdr' <= d` by ARITH_TAC THEN
  `0 <= d /\ 0 < intvlmax /\ 0 <= intvlmin` by ARITH_TAC THEN
  `0 <= d / intvlmin` by SRW_TAC [][realTheory.REAL_LE_DIV] THEN
  ASM_SIMP_TAC (srw_ss()) [x_le_num_floor] THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC `d / intvlmax * intvlmax < (&)(delta + 1) * intvlmax` THEN1
      SRW_TAC [][realTheory.REAL_LT_RMUL] THEN
    `~(intvlmax = 0)` by ARITH_TAC THEN
    ASM_SIMP_TAC bool_ss [realTheory.REAL_DIV_RMUL,
                          realTheory.REAL_ADD_RDISTRIB,
                          GSYM realTheory.REAL_ADD] THEN
    SRW_TAC [][] THEN ARITH_TAC,
    Q_TAC SUFF_TAC `(&)delta * intvlmin <= d / intvlmin * intvlmin` THEN1
      SRW_TAC [][realTheory.REAL_LE_RMUL] THEN
    `~(intvlmin = 0)` by ARITH_TAC THEN
    SRW_TAC [][realTheory.REAL_DIV_RMUL] THEN ARITH_TAC
  ]);

val tick_imin_imax_preserved = store_thm(
  "tick_imin_imax_preserved",
  ``Time_Pass_ticker d t0 t ==> (tick_imin t = tick_imin t0 /\
                                 tick_imax t = tick_imax t0)``,
  Q.ID_SPEC_TAC `t0` THEN
  SIMP_TAC (srw_ss()) [FORALL_ticker, Time_Pass_ticker_def] THEN
  SRW_TAC [][tick_imin_def, tick_imax_def] THEN
  SRW_TAC [][tick_imin_def, tick_imax_def]);

val infer_ticker_bounds = store_thm(
  "infer_ticker_bounds",
  ``Time_Pass_ticker d t0 t /\ ticker_ok t0 ==>
    ?delta.
       (ticks_of t = ticks_of t0 + delta) /\
       d/tick_imax t0 - 1 < real_of_num(delta) /\
       real_of_num(delta) <= (d + tick_imax t0) / tick_imin t0``,
  Q.ID_SPEC_TAC `t0` THEN
  SIMP_TAC (srw_ss()) [FORALL_ticker, ticker_ok_def] THEN
  CONV_TAC (RENAME_VARS_CONV ["t0", "r0", "imin", "imax"]) THEN
  Q.ID_SPEC_TAC `t` THEN
  SIMP_TAC (srw_ss()) [FORALL_ticker] THEN
  SRW_TAC [boolSimps.CONJ_ss][ticker_alternative,ticks_of_def,
                              tick_imin_def, tick_imax_def] THEN
  Q.EXISTS_TAC `delta` THEN
  SRW_TAC [realSimps.REAL_ARITH_ss]
          [realTheory.REAL_LT_SUB_RADD, realTheory.REAL_LE_RDIV_EQ,
           realTheory.REAL_LT_LDIV_EQ]
  THENL [
    MATCH_MP_TAC realTheory.REAL_LET_TRANS THEN
    Q.EXISTS_TAC `r0 + d` THEN
    SRW_TAC [realSimps.REAL_ARITH_ss][] THEN
    REWRITE_TAC [GSYM realTheory.REAL_ADD, realTheory.REAL_ADD_RDISTRIB] THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC realTheory.REAL_LTE_TRANS THEN
    Q.EXISTS_TAC `real_of_num delta * i + i2` THEN
    SRW_TAC [][realTheory.REAL_LE_RADD, realTheory.REAL_LE_LMUL_IMP],
    MATCH_MP_TAC realTheory.REAL_LE_TRANS THEN
    Q.EXISTS_TAC `real_of_num delta * i` THEN
    SRW_TAC [realSimps.REAL_ARITH_ss][realTheory.REAL_LE_LMUL_IMP]
  ]);


(* -------------------------------------------------- *)

val _ = export_theory();
