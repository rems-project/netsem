(* Definitions and theorems to support arithmetic range analyses *)

(*[ RCSID "$Id: TCP1_rangeAnalysisScript.sml,v 1.7 2006/02/20 23:03:47 mn200 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse

open BasicProvers bossLib

open HolDoc

local open TCP1_baseTypesTheory TCP1_utilsTheory TCP1_utilPropsTheory in end

local open arithmeticTheory realTheory wordsTheory in end;

val _ = new_theory "TCP1_rangeAnalysis";

open lcsymtacs

val srange_def = Define`
  srange (x:'a seq32) (base:'a seq32) (size:num) =
     ?n:num. n <= size /\ x = base + n
`;

val _ = augment_srw_ss [rewrites [wordsTheory.dimword_32,
                                  wordsTheory.dimindex_32,
                                  wordsTheory.INT_MIN_def,
                                  wordsTheory.INT_MAX_def]]

val TOP_BOT = prove(
  ``4294967296w : word32 = 0w``,
  SRW_TAC [][wordsTheory.n2w_11]);

val word32_nchotomy = prove(
  ``!w : word32. ?n. (w = n2w n) /\ n < 4294967296``,
  GEN_TAC THEN Q.ISPEC_THEN `w` STRUCT_CASES_TAC wordsTheory.word_nchotomy THEN
  SRW_TAC [][wordsTheory.n2w_11] THEN
  Q.EXISTS_TAC `n MOD 4294967296` THEN
  SRW_TAC [][arithmeticTheory.DIVISION]);

open integerTheory

val WORD_SUB_EQN = TCP1_seq32PropsTheory.WORD_SUB_EQN

val srange_alt = store_thm(
  "srange_alt",
  ``sz < 2147483648 ==>
    srange (v:tstamp seq32) b sz = (b <= v /\ b + sz >= v)``,
  Cases_on `v` THEN Cases_on `b` THEN STRIP_TAC THEN
  Q.MATCH_ABBREV_TAC `srange (SEQ32 x1 v1) (SEQ32 x2 v2) sz =
                      (SEQ32 x2 v2 <= SEQ32 x1 v1 /\
                       SEQ32 x2 v2 + sz >= SEQ32 x1 v1)` THEN
  markerLib.RM_ALL_ABBREVS_TAC THEN
  SRW_TAC [][srange_def, TCP1_baseTypesTheory.seq32_leq_def, EQ_IMP_THM,
             TCP1_baseTypesTheory.seq32_diff_def,
             TCP1_baseTypesTheory.seq32_plus_def,
             TCP1_baseTypesTheory.seq32_geq_def]
  THENL [
    SRW_TAC [][wordsTheory.WORD_ADD_SUB3, wordsTheory.word_2comp_def] THEN
    Cases_on `n = 0` THENL [
      SRW_TAC [][TOP_BOT, integer_wordTheory.w2i_n2w_pos],
      SRW_TAC [numSimps.ARITH_ss][integer_wordTheory.w2i_n2w_neg]
    ],
    Q.ISPEC_THEN `v2` STRIP_ASSUME_TAC word32_nchotomy THEN
    SRW_TAC [numSimps.ARITH_ss][WORD_SUB_EQN, wordsTheory.word_add_n2w] THEN
    SRW_TAC [numSimps.ARITH_ss][integer_wordTheory.w2i_n2w_pos, int_ge],
    Cases_on `x1` THEN Cases_on `x2` THEN ASM_REWRITE_TAC [] THEN
    `(?n1. v1 = n2w n1 /\ n1 < 4294967296) /\
     (?n2. v2 = n2w n2 /\ n2 < 4294967296)` by PROVE_TAC [word32_nchotomy] THEN
    Q.EXISTS_TAC `Num(w2i(v1 - v2))` THEN
    STRIP_ASSUME_TAC (DECIDE ``n1:num = n2 \/ n1 < n2 \/ n2 < n1``) THENL [
      FULL_SIMP_TAC (srw_ss()) [wordsTheory.WORD_SUB_REFL,
                                wordsTheory.word_0,
                                integer_wordTheory.w2i_n2w_pos,
                                wordsTheory.word_add_n2w],
      ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [WORD_SUB_EQN] THEN
      `~(n2 - n1 < 2147483648)`
         by (STRIP_TAC THEN
             FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                           [integer_wordTheory.w2i_n2w_pos,
                            WORD_SUB_EQN]) THEN
      `2147483648 <= n2 - n1` by DECIDE_TAC THEN
      `n1 + 2147483648 < n2`
          by (FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                            [integer_wordTheory.w2i_n2w_pos,
                             wordsTheory.word_add_n2w,
                             integer_wordTheory.w2i_n2w_neg,
                             WORD_SUB_EQN] THEN
              Q_TAC SUFF_TAC `~(n2 = n1 + 2147483648)` THEN1 DECIDE_TAC THEN
              STRIP_TAC THEN SRW_TAC [][] THEN
              Q.UNDISCH_THEN `sz < 2147483648` ASSUME_TAC THEN
              FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                            [integer_wordTheory.w2i_n2w_neg] THEN
              FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                            [int_ge, INT_LE_SUB_LADD]) THEN
      `n1 + 4294967296 - n2 < 2147483648` by DECIDE_TAC THEN
      ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                   [integer_wordTheory.w2i_n2w_pos, wordsTheory.word_add_n2w,
                    wordsTheory.n2w_11] THEN
      FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                    [WORD_SUB_EQN, wordsTheory.word_add_n2w] THEN
      SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
      `n2 + sz < n1 + 4294967296` by DECIDE_TAC THEN
      `2147483648 <= n2 + sz - n1 /\ n2 + sz - n1 < 4294967296`
         by DECIDE_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [integer_wordTheory.w2i_n2w_neg] THEN
      FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                    [int_ge, INT_LE_SUB_LADD],

      ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [WORD_SUB_EQN] THEN
      Q_TAC SUFF_TAC `n1 - n2 <= sz` THEN1
            ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                          [integer_wordTheory.w2i_n2w_pos,
                           wordsTheory.word_add_n2w] THEN
      SPOSE_NOT_THEN ASSUME_TAC THEN
      FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                    [WORD_SUB_EQN, wordsTheory.word_add_n2w] THEN
      `n2 + 4294967296 - n1 < 4294967296` by DECIDE_TAC THEN
      `2147483648 <= n2 + 4294967296 - n1`
         by (SPOSE_NOT_THEN ASSUME_TAC THEN
             FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                           [integer_wordTheory.w2i_n2w_pos]) THEN
      `n1 <= n2 + 2147483648` by DECIDE_TAC THEN
      `n2 + (sz + 4294967296) - n1 < 4294967296` by DECIDE_TAC THEN
      `2147483648 <= n2 + (sz + 4294967296) - n1` by DECIDE_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [integer_wordTheory.w2i_n2w_neg] THEN
      FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                    [int_ge, INT_LE_SUB_LADD]
    ]
  ]);

val srange_concrete = store_thm(
  "srange_concrete",
  ``sz < 2147483648 ==>
    (srange (SEQ32 Tstamp (n2w (NUMERAL n)))
            (SEQ32 Tstamp (n2w (NUMERAL m)))
            sz
    =
     (w2i (n2w (NUMERAL m) - n2w (NUMERAL n) : word32) <= 0 /\
      w2i (n2w (NUMERAL m + sz) - n2w (NUMERAL n) : word32) >= 0))``,
  SRW_TAC [][srange_alt, TCP1_baseTypesTheory.seq32_geq_def,
             TCP1_baseTypesTheory.seq32_leq_def,
             TCP1_baseTypesTheory.seq32_diff_def,
             TCP1_baseTypesTheory.seq32_plus_def,
             wordsTheory.word_add_n2w]);
val _ = Phase.add_to_phase 1 "srange_concrete"

val tstamp_arb = prove(
  ``!x: tstamp. x = ARB``,
  GEN_TAC THEN MAP_EVERY Cases_on [`x`, `ARB : tstamp`] THEN
  SRW_TAC [][]);

val srange_0 = store_thm(
  "srange_0",
  ``srange (v:tstamp seq32) b 0 = (v = b)``,
  Cases_on `b` THEN Cases_on `v` THEN
  SRW_TAC [][srange_def, TCP1_baseTypesTheory.seq32_plus_def,
             tstamp_arb, wordsTheory.WORD_ADD_0]);
val _ = Phase.add_to_phase 1 "srange_0"

val into_srange = store_thm(
  "into_srange",
  ``lo < hi ==>
      (?d. v = SEQ32 Tstamp w + d /\ lo <= d /\ d < hi) =
      srange v (SEQ32 Tstamp w + lo) (hi - lo - 1)``,
  SRW_TAC [][srange_def, EQ_IMP_THM, TCP1_baseTypesTheory.seq32_plus_def,
             wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.word_add_n2w,
             GSYM wordsTheory.WORD_ADD_ASSOC] THENL [
    Q.EXISTS_TAC `d - lo` THEN
    ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [],
    Q.EXISTS_TAC `lo + n` THEN
    ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) []
  ]);

val irange_def = Define`
  irange (v:int) (b:int) (sz:num) = ?n. n <= sz /\ v = b + (&)n
`;


val WORD_SUB_EQN' =
    SIMP_RULE bool_ss []
              (DISCH_ALL (ADD_ASSUM ``x:num <= y`` (GSYM WORD_SUB_EQN)))

val WORD_SUB_0 = wordsTheory.WORD_SUB_RZERO

val ranged_seq32_sub = store_thm(
  "ranged_seq32_sub",
  ``ABS (b - w) < 1073741824 /\
    ABS (b + sz - w) < 1073741824 /\
    sz < 2147483648 /\
    srange v b sz ==> irange (v - w) (b - w) sz``,
  SRW_TAC [][srange_def, irange_def] THEN
  Q.EXISTS_TAC `n` THEN SRW_TAC [][] THEN
  `(?bw bx. b = SEQ32 bx bw) /\ (?ww wx. w = SEQ32 wx ww)`
      by PROVE_TAC [TypeBase.nchotomy_of ``:'a seq32``] THEN
  `(?bn. bw = n2w bn /\ bn < 4294967296) /\
   (?wn. ww = n2w wn /\ wn < 4294967296)`
      by PROVE_TAC [word32_nchotomy] THEN
  FULL_SIMP_TAC (srw_ss()) [TCP1_baseTypesTheory.seq32_plus_def,
                            TCP1_baseTypesTheory.seq32_diff_def,
                            wordsTheory.word_add_n2w] THEN
  Cases_on `wn <= bn` THENL [
    FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [WORD_SUB_EQN] THEN
    Cases_on `bn - wn < 2147483648` THENL [
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                    [integer_wordTheory.w2i_n2w_pos, INT_ABS_NUM] THEN
      Cases_on `bn + n - wn < 2147483648` THENL [
        FULL_SIMP_TAC (srw_ss()) [integer_wordTheory.w2i_n2w_pos,
                                  INT_ABS_NUM] THEN
        REWRITE_TAC [INT_ADD, INT_INJ] THEN
        DECIDE_TAC,

        `bn + n - wn < 4294967296 /\ bn + sz - wn < 4294967296 /\
         2147483648 <= bn + sz - wn`
          by DECIDE_TAC THEN
        FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                      [integer_wordTheory.w2i_n2w_neg,
                       arithmeticTheory.NOT_LESS,
                       INT_ABS, INT_LT_SUB_RADD] THEN
        FULL_SIMP_TAC bool_ss [INT_ADD, INT_LT] THEN
        FULL_SIMP_TAC arith_ss []
      ],
      `bn - wn < 4294967296` by DECIDE_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.NOT_LESS,
                                integer_wordTheory.w2i_n2w_neg] THEN
      `2147483648 <= bn + n - wn` by DECIDE_TAC THEN
      Cases_on `bn + n - wn < 4294967296` THENL [
        simp[integer_wordTheory.w2i_n2w_neg] THEN
        ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [GSYM INT_SUB] THEN
        REWRITE_TAC [GSYM INT_ADD] THEN
        ASM_SIMP_TAC bool_ss [int_sub, AC INT_ADD_ASSOC INT_ADD_COMM],
        `bn + n - wn < 4294967296 + 2147483648` by DECIDE_TAC THEN
        `n2w (bn + n - wn) = n2w ((bn + n - wn) - 4294967296) : word32`
            by ASM_SIMP_TAC (bool_ss ++ numSimps.ARITH_ss)
                            [WORD_SUB_EQN', WORD_SUB_0, TOP_BOT] THEN
        `bn + n - wn - 4294967296 < 2147483648` by DECIDE_TAC THEN
        simp[integer_wordTheory.w2i_n2w_pos] THEN
        ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                     [GSYM INT_SUB, GSYM INT_ADD, int_sub,
                      INT_NEG_ADD, AC INT_ADD_ASSOC INT_ADD_COMM]
      ]
    ],
    ASM_SIMP_TAC (srw_ss()) [WORD_SUB_EQN] THEN Cases_on `wn <= bn + n` THENL [
      ASM_SIMP_TAC (srw_ss()) [] THEN
      `wn <= bn + sz` by DECIDE_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [WORD_SUB_EQN] THEN
      Cases_on `bn + 4294967296 - wn < 2147483648` THENL [
        FULL_SIMP_TAC (srw_ss()) [integer_wordTheory.w2i_n2w_pos] THEN
        ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [GSYM INT_SUB] THEN
        `bn + n - wn < 2147483648 /\ bn + sz - wn < 2147483648`
          by DECIDE_TAC THEN
        FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                      [integer_wordTheory.w2i_n2w_pos,
                       INT_ABS, GSYM INT_SUB, INT_LT_SUB_RADD],
        `bn + 4294967296 - wn < 4294967296` by DECIDE_TAC THEN
        FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.NOT_LESS,
                                  integer_wordTheory.w2i_n2w_neg] THEN
        `bn + n - wn < 2147483648` by DECIDE_TAC THEN
        ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                     [GSYM INT_SUB, integer_wordTheory.w2i_n2w_pos,
                      int_sub, AC INT_ADD_ASSOC INT_ADD_COMM, GSYM INT_ADD] THEN
        intLib.ARITH_TAC
      ],
      ASM_SIMP_TAC (srw_ss()) [] THEN
      `bn + n < 4294967296` by DECIDE_TAC THEN
      ASM_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `bn + 4294967296 - wn < 2147483648` THENL [
        FULL_SIMP_TAC (srw_ss()) [integer_wordTheory.w2i_n2w_pos,
                                  WORD_SUB_EQN, INT_ABS_NUM] THEN
        `~(wn <=  bn + sz)` by DECIDE_TAC THEN
        `bn + sz < 4294967296` by DECIDE_TAC THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN
        Cases_on `bn + sz + 4294967296 - wn < 2147483648` THENL [
          `bn + n + 4294967296 - wn < 2147483648` by DECIDE_TAC THEN
          FULL_SIMP_TAC (srw_ss()) [integer_wordTheory.w2i_n2w_pos,
                                    INT_ADD] THEN
          DECIDE_TAC,
          `bn + sz + 4294967296 - wn < 4294967296 /\
           bn + n + 4294967296 - wn < 4294967296` by DECIDE_TAC THEN
          FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.NOT_LESS,
                                    integer_wordTheory.w2i_n2w_neg] THEN
          FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                        [INT_ABS, INT_LT_SUB_RADD, INT_ADD]
        ],
        `bn + 4294967296 - wn < 4294967296` by DECIDE_TAC THEN
        FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
          [arithmeticTheory.NOT_LESS, WORD_SUB_EQN,
           integer_wordTheory.w2i_n2w_neg] THEN
        `2147483648 <= bn + n + 4294967296 - wn` by DECIDE_TAC THEN
        `bn + n + 4294967296 - wn < 4294967296` by DECIDE_TAC THEN
        ASM_SIMP_TAC (srw_ss()) [integer_wordTheory.w2i_n2w_neg] THEN
        ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [GSYM INT_SUB,
                                                      GSYM INT_ADD] THEN
        SIMP_TAC (srw_ss()) [AC INT_ADD_ASSOC INT_ADD_COMM, int_sub]
      ]
    ]
  ]);

val rrange_def = Define`
  rrange (v:real) (b:real) (sz:real) = (b <= v /\ v <= b + sz)
`;

val rrange_0 = store_thm(
  "rrange_0",
  ``rrange x y 0 = (x = y)``,
  SRW_TAC [realSimps.REAL_ARITH_ss][rrange_def]);
val _ = Phase.add_to_phase 1 "rrange_0"

val real_of_int_num = store_thm(
  "real_of_int_num",
  ``real_of_int ((&) n) = (&)n /\ real_of_int (~(&)n) = ~(&)n``,
  SRW_TAC [][TCP1_utilsTheory.real_of_int_def]);
val _ = augment_srw_ss [rewrites [real_of_int_num]]

val REAL_SUB' = prove(
  ``m <= n ==> ((&)(n - m) : real = (&)n - (&)m)``,
  SRW_TAC [][realTheory.REAL_SUB,
             DECIDE ``(m:num - n:num = 0) = (m <= n)``]);

val real_of_int_plus = store_thm(
  "real_of_int_plus",
  ``real_of_int (x + y) = real_of_int x + real_of_int y``,
  Cases_on `0 <= x + y` THENL [
    IMP_RES_TAC NUM_POSINT_EXISTS THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    MAP_EVERY (fn q => Q.SPEC_THEN q STRIP_ASSUME_TAC INT_NUM_CASES)
              [`x`, `y`] THEN
    FULL_SIMP_TAC (srw_ss() ++ boolSimps.COND_elim_ss)
                  [TCP1_utilsTheory.real_of_int_def, INT_NEG_ADD,
                   INT_ADD, INT_ADD_CALCULATE] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [REAL_SUB', realTheory.real_sub,
                              realTheory.REAL_ADD_COMM] THEN
    `n' = n''` by PROVE_TAC [arithmeticTheory.LESS_EQUAL_ANTISYM] THEN
    SRW_TAC [][],
    FULL_SIMP_TAC (srw_ss()) [INT_NOT_LE] THEN
    IMP_RES_TAC INT_LT_IMP_LE THEN
    IMP_RES_TAC NUM_NEGINT_EXISTS THEN
    MAP_EVERY (fn q => Q.SPEC_THEN q STRIP_ASSUME_TAC INT_NUM_CASES)
              [`x`, `y`] THEN
    FULL_SIMP_TAC (srw_ss() ++ boolSimps.COND_elim_ss)
                  [TCP1_utilsTheory.real_of_int_def, INT_NEG_ADD,
                   INT_ADD, INT_ADD_CALCULATE] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.NOT_LESS_EQUAL,
                              arithmeticTheory.LESS_IMP_LESS_OR_EQ,
                              REAL_SUB', realTheory.real_sub,
                              realTheory.REAL_NEG_ADD,
                              realTheory.REAL_ADD_COMM]
    THENL [
      PROVE_TAC [arithmeticTheory.LESS_LESS_EQ_TRANS,
                 prim_recTheory.LESS_REFL],
      PROVE_TAC [arithmeticTheory.LESS_LESS_EQ_TRANS,
                 prim_recTheory.LESS_REFL],
      PROVE_TAC [arithmeticTheory.LESS_LESS_EQ_TRANS,
                 prim_recTheory.LESS_REFL],
      PROVE_TAC [arithmeticTheory.LESS_LESS_EQ_TRANS,
                 prim_recTheory.LESS_REFL],
      REWRITE_TAC [GSYM realTheory.REAL_ADD, realTheory.REAL_NEG_ADD]
    ]
  ]);

val irange_real_of_int = store_thm(
  "irange_real_of_int",
  ``irange v b sz ==>
    rrange (real_of_int v) (real_of_int b) (real_of_num sz)``,
  SRW_TAC [][irange_def, rrange_def] THEN
  SRW_TAC [realSimps.REAL_ARITH_ss][real_of_int_plus,
                                    realTheory.REAL_LE_ADDR]);

val rrange_posdiv = store_thm(
  "rrange_posdiv",
  ``rrange v b sz /\ 0 < d ==> rrange (v / d) (b / d) (sz / d)``,
  SRW_TAC [realSimps.REAL_ARITH_ss][rrange_def, realTheory.add_rat,
                                    realTheory.REAL_LE_LDIV_EQ,
                                    realTheory.REAL_DIV_RMUL]);

val rrange_plus = store_thm(
  "rrange_plus",
  ``rrange v1 b1 sz1 /\ rrange v2 b2 sz2 ==>
    rrange (v1 + v2) (b1 + b2) (sz1 + sz2)``,
  SRW_TAC [realSimps.REAL_ARITH_ss][rrange_def]);

val rrange_negate = store_thm(
  "rrange_negate",
  ``rrange v b sz ==> rrange (~v) (~(b + sz)) sz``,
  SRW_TAC [realSimps.REAL_ARITH_ss][rrange_def]);

val rrange_sub = store_thm(
  "rrange_sub",
  ``rrange v1 b1 sz1 /\ rrange v2 b2 sz2 ==>
    rrange (v1 - v2) (b1 + ~(b2 + sz2)) (sz1 + sz2)``,
  SRW_TAC [realSimps.REAL_ARITH_ss][rrange_def, realTheory.real_sub,
                                    rrange_negate]);

val rrange_rmult = store_thm(
  "rrange_rmult",
  ``0 < c /\ rrange v b sz ==> rrange (v * c) (b * c) (sz * c)``,
  SRW_TAC [][rrange_def, realTheory.REAL_LE_RMUL,
             GSYM realTheory.REAL_RDISTRIB]);
val rrange_lmult = store_thm(
  "rrange_lmult",
  ``0 < c /\ rrange v b sz ==> rrange (c * v) (c * b) (c * sz)``,
  SRW_TAC [][rrange_def, realTheory.REAL_LE_LMUL,
             GSYM realTheory.REAL_LDISTRIB]);

val rrange_rmult = store_thm(
  "rrange_rmult",
  ``0 < c /\ rrange v b sz ==> rrange (v * c) (b * c) (sz * c)``,
  SRW_TAC [][rrange_def, realTheory.REAL_LE_RMUL,
             GSYM realTheory.REAL_RDISTRIB]);

val rrange_max = store_thm(
  "rrange_max",
  ``rrange v1 b1 sz1 /\ rrange v2 b2 sz2 ==>
    rrange (MAX v1 v2) (MAX b1 b2)
           (let lomax = MAX b1 b2 in
            let himax = MAX (b1 + sz1) (b2 + sz2) in
              himax - lomax)``,
  SRW_TAC [realSimps.REAL_ARITH_ss][rrange_def, realTheory.max_def, LET_THM]);

val rrange_min = store_thm(
  "rrange_min",
  ``rrange v1 b1 sz1 /\ rrange v2 b2 sz2 ==>
    rrange (MIN v1 v2) (MIN b1 b2)
           (let lomin = MIN b1 b2 in
            let himin = MIN (b1 + sz1) (b2 + sz2) in
              himin - lomin)``,
  SRW_TAC [realSimps.REAL_ARITH_ss][rrange_def, realTheory.min_def, LET_THM]);

val rrange_abs1 = store_thm(
  "rrange_abs1",
  ``rrange v b sz /\ 0 <= b ==> rrange (abs v) b sz``,
  SRW_TAC [realSimps.REAL_ARITH_ss][rrange_def]);

val rrange_abs2 = store_thm(
  "rrange_abs2",
  ``rrange v b sz /\ b + sz < 0 ==> rrange (abs v) (~(b + sz)) ~b``,
  SRW_TAC [realSimps.REAL_ARITH_ss][rrange_def]);

val rrange_abs3 = store_thm(
  "rrange_abs3",
  ``rrange v b sz /\ b < 0 /\ 0 <= b + sz ==>
    rrange (abs v) 0 (MAX (~b) (b + sz))``,
  SRW_TAC [realSimps.REAL_ARITH_ss][rrange_def, realTheory.max_def]);

val literals = [``0r``, ``(&)(NUMERAL n) : real``, ``~(&)(NUMERAL n) : real``,
                ``(&)(NUMERAL n) / (&)(NUMERAL m) : real``,
                ``~(&)(NUMERAL n) / (&)(NUMERAL m) : real``]

val rrange_concrete = save_thm(
  "rrange_concrete",
  LIST_CONJ (map (GEN_ALL o C SPEC rrange_def) literals))
val _ = Phase.add_to_phase 1 "rrange_concrete"

val rrange_literals = let
  val base = prove(``!x. rrange x x 0``, SRW_TAC [][rrange_0])
in
  save_thm("rrange_literals", LIST_CONJ (map (C SPEC base) literals))
end

val nrange_def = Define`
  nrange (v:num) (b:num) (sz :num) = (b <= v /\ v <= b + sz)
`;

val nrange_0 = store_thm(
  "nrange_0",
  ``nrange v b 0 = (v = b)``,
  SRW_TAC [numSimps.ARITH_ss][nrange_def]);
val _ = Phase.add_to_phase 1 "nrange_0"

val nrange_sub = store_thm(
  "nrange_sub",
  ``nrange v1 b1 sz1 /\ nrange v2 b2 sz2 ==>
    nrange (v1 - v2) (b1 - (b2 + sz2)) (sz1 + sz2)``,
  SRW_TAC [numSimps.ARITH_ss][nrange_def]);

val nrange_plus = store_thm(
  "nrange_plus",
  ``nrange v1 b1 sz1 /\ nrange v2 b2 sz2 ==>
    nrange (v1 + v2) (b1 + b2) (sz1 + sz2)``,
  SRW_TAC [numSimps.ARITH_ss][nrange_def]);

val nrange_literals = store_thm(
  "nrange_literals",
  ``nrange 0 0 0 /\ nrange (NUMERAL n) (NUMERAL n) 0``,
  SRW_TAC [][nrange_0]);

val nrange_concrete = store_thm(
  "nrange_concrete",
  ``nrange 0 b sz = (b = 0) /\
    nrange (NUMERAL n) b sz = (b <= NUMERAL n /\ NUMERAL n <= b + sz)``,
  SRW_TAC [numSimps.ARITH_ss][nrange_def])
val _ = Phase.add_to_phase 1 "nrange_concrete"

val rounddown_def = TCP1_utilsTheory.rounddown_def
val DIV_EQ_0 = store_thm(
  "DIV_EQ_0",
  ``0 < n ==> ((r DIV n = 0) <=> r < n)``,
  STRIP_TAC THEN
  Q.SPEC_THEN `n` MP_TAC arithmeticTheory.DIVISION THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (Q.SPEC_THEN `r` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `p = r DIV n` THEN
  Q.ABBREV_TAC `q = r MOD n` THEN
  markerLib.RM_ALL_ABBREVS_TAC THEN
  SRW_TAC [][EQ_IMP_THM] THEN
  Cases_on `p` THEN
  FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                [arithmeticTheory.MULT_CLAUSES]);

val nrange_rounddown = store_thm(
  "nrange_rounddown",
  ``0 < c /\ nrange v b sz ==>
    nrange (rounddown c v) (rounddown c b)
           (rounddown c (b + sz) - rounddown c b)``,
  SRW_TAC [][rounddown_def, nrange_def] THENL [
    Q_TAC SUFF_TAC `c <= (b + sz) DIV c * c` THEN1 DECIDE_TAC THEN
    CONV_TAC (LAND_CONV (REWR_CONV (GSYM arithmeticTheory.MULT_LEFT_1))) THEN
    REWRITE_TAC [arithmeticTheory.LE_MULT_RCANCEL] THEN
    ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [] THEN
    Q_TAC SUFF_TAC `~((b + sz) DIV c = 0)` THEN1 DECIDE_TAC THEN
    ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [DIV_EQ_0],
    PROVE_TAC [arithmeticTheory.LESS_EQ_LESS_TRANS],
    PROVE_TAC [arithmeticTheory.LESS_EQ_LESS_TRANS],
    FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.NOT_LESS] THEN
    Q_TAC SUFF_TAC `c <= v DIV c * c` THEN1 DECIDE_TAC THEN
    CONV_TAC (LAND_CONV (REWR_CONV (GSYM arithmeticTheory.MULT_LEFT_1))) THEN
    REWRITE_TAC [arithmeticTheory.LE_MULT_RCANCEL] THEN
    ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [] THEN
    Q_TAC SUFF_TAC `~(v DIV c = 0)` THEN1 DECIDE_TAC THEN
    ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [DIV_EQ_0],
    `b <= (b + sz) DIV c * c`
       by (Q_TAC SUFF_TAC `c <= (b + sz) DIV c * c` THEN1 DECIDE_TAC THEN
           CONV_TAC (LAND_CONV
                       (REWR_CONV (GSYM arithmeticTheory.MULT_LEFT_1))) THEN
           REWRITE_TAC [arithmeticTheory.LE_MULT_RCANCEL] THEN
           ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [] THEN
           Q_TAC SUFF_TAC `~((b + sz) DIV c = 0)` THEN1 DECIDE_TAC THEN
           ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [DIV_EQ_0]) THEN
    ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                 [arithmeticTheory.DIV_LE_MONOTONE],
    ASM_SIMP_TAC bool_ss [GSYM arithmeticTheory.X_LE_DIV,
                          arithmeticTheory.DIV_LE_MONOTONE],
    Q_TAC SUFF_TAC `b DIV c * c <= b + sz` THEN1
          ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [] THEN
    ASM_SIMP_TAC (bool_ss ++ numSimps.ARITH_ss)
                 [GSYM arithmeticTheory.X_LE_DIV,
                  arithmeticTheory.DIV_LE_MONOTONE],
    ASM_SIMP_TAC bool_ss [GSYM arithmeticTheory.X_LE_DIV,
                          arithmeticTheory.DIV_LE_MONOTONE],
    Q_TAC SUFF_TAC `b DIV c * c <= (b + sz) DIV c * c` THEN1
          ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [] THEN
    ASM_SIMP_TAC (bool_ss ++ numSimps.ARITH_ss)
                 [arithmeticTheory.DIV_LE_MONOTONE,
                  arithmeticTheory.LE_MULT_RCANCEL],
    ASM_SIMP_TAC bool_ss [arithmeticTheory.DIV_LE_MONOTONE],
    PROVE_TAC [arithmeticTheory.LESS_EQ_LESS_TRANS],
    ASM_SIMP_TAC bool_ss [arithmeticTheory.DIV_LE_MONOTONE],
    Q_TAC SUFF_TAC `b DIV c * c <= (b + sz) DIV c * c` THEN1
          (ASM_SIMP_TAC bool_ss
                        [DECIDE ``x <= y ==> (x + (y - x:num) = y)``] THEN
           ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                        [arithmeticTheory.DIV_LE_MONOTONE]) THEN
    ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                 [arithmeticTheory.DIV_LE_MONOTONE]
  ]);

val nrange_intro = store_thm(
  "nrange_intro",
  ``c1 <= v /\ v <= c2 ==> nrange v c1 (c2 - c1)``,
  SRW_TAC [numSimps.ARITH_ss][nrange_def]);

val nrange_min = store_thm(
  "nrange_min",
  ``nrange v1 b1 sz1 /\ nrange v2 b2 sz2 ==>
    nrange (MIN v1 v2) (MIN b1 b2)
           (let lomin = MIN b1 b2 in
            let himin = MIN (b1 + sz1) (b2 + sz2) in
                himin - lomin)``,
  SRW_TAC [numSimps.ARITH_ss][arithmeticTheory.MIN_DEF, nrange_def,
                              LET_THM]);

val nrange_max = store_thm(
  "nrange_max",
  ``nrange v1 b1 sz1 /\ nrange v2 b2 sz2 ==>
    nrange (MAX v1 v2) (MAX b1 b2)
           (let lomax = MAX b1 b2 in
            let himax = MAX (b1 + sz1) (b2 + sz2) in
              himax - lomax)``,
  SRW_TAC [numSimps.ARITH_ss][arithmeticTheory.MAX_DEF, nrange_def,
                              LET_THM]);

val nrange_cond = store_thm(
  "nrange_cond",
  ``nrange v1 b1 sz1 /\ nrange v2 b2 sz2 ==>
    nrange (if P then v1 else v2)
           (MIN b1 b2)
           (let min = MIN b1 b2 in
            let max = MAX (b1 + sz1) (b2 + sz2) in
              max - min)``,
  SRW_TAC [numSimps.ARITH_ss][arithmeticTheory.MAX_DEF,
                              arithmeticTheory.MIN_DEF,
                              nrange_def, LET_THM]);

val _ = export_theory()
