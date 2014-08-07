structure TCP1_seq32PropsScript =
struct

open HolKernel Parse boolLib

open TCP1_baseTypesTheory integer_word32Theory
open simpLib boolSimps numSimps BasicProvers bossLib intLib

val _ = new_theory "TCP1_seq32Props";

val int_ge = integerTheory.int_ge
val INT_LE_SUB_RADD = integerTheory.INT_LE_SUB_RADD
val INT_LT_SUB_RADD = integerTheory.INT_LT_SUB_RADD
val INT_LE_SUB_LADD = integerTheory.INT_LE_SUB_LADD
val INT_LT_SUB_LADD = integerTheory.INT_LT_SUB_LADD
val w2in2w1 = integer_word32Theory.w2i_n2w_1
val w2in2w2 = integer_word32Theory.w2i_n2w_2


val WORD32_ss =
    rewrites [word32Theory.HB_def, word32Theory.WL_def,
              word32Theory.MOD_WL_def, word32Theory.word_L_def,
              word32Theory.MSB_EVAL, word32Theory.MSBn_def,
              bitsTheory.BIT_def, bitsTheory.BITS_def,
              arithmeticTheory.MOD_2EXP_def, bitsTheory.DIV_2EXP_def,
              word32Theory.n2w_11, word32Theory.TWO_COMP_def,
              word32Theory.TWO_COMP_EVAL, word32Theory.WORD_NEG_NEG,
              word32Theory.ADD_EVAL, word32Theory.WORD_SUB_REFL,
              word32Theory.word_0, word32Theory.w2n_11,
              word32Theory.WORD_ADD_SUB2, word32Theory.w2n_EVAL,
              word32Theory.WORD_ADD_SUB3,
              REWRITE_RULE [word32Theory.word_0] word32Theory.WORD_ADD_CLAUSES,
              REWRITE_RULE [word32Theory.word_0] word32Theory.WORD_NEG_EQ_0]

val _ = augment_srw_ss [WORD32_ss,
                        rewrites [int_ge, integerTheory.int_gt,
                                  INT_LE_SUB_RADD, INT_LT_SUB_RADD,
                                  INT_LE_SUB_LADD, INT_LT_SUB_LADD]]

val w2n_eq_0 = store_thm(
  "w2n_eq_0",
  ``(w2n (w:word32) = 0) = (w = n2w 0)``,
  `0 = w2n (n2w 0 : word32)`
    by SRW_TAC [][] THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) THEN
  SRW_TAC [][]);
val _ = export_rewrites ["w2n_eq_0"]

val div_lemma = prove(
  ``0 < x /\ ~((n DIV x) MOD 2 = 1) ==> n MOD (2 * x) < x``,
  STRIP_TAC THEN
  Q.SPEC_THEN `x` MP_TAC arithmeticTheory.DIVISION THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (Q.SPEC_THEN `n` MP_TAC) THEN
  Q.ABBREV_TAC `q = n DIV x` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = n MOD x` THEN POP_ASSUM (K ALL_TAC) THEN
  SRW_TAC [][] THEN
  `(q * x + r) MOD (2 * x) =
      ((q * x) MOD (2 * x) + r MOD (2 * x)) MOD (2 * x)`
     by (MATCH_MP_TAC (GSYM arithmeticTheory.MOD_PLUS) THEN
         SRW_TAC [][arithmeticTheory.LESS_MULT2]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  `(q * x) MOD (2 * x) = x * q MOD 2`
      by PROVE_TAC [DECIDE ``0n < 2``, arithmeticTheory.MULT_COMM,
                    arithmeticTheory.MOD_COMMON_FACTOR] THEN
  `q MOD 2 < 2`
      by PROVE_TAC [DECIDE ``0n < 2``, arithmeticTheory.DIVISION] THEN
  `q MOD 2 = 0` by DECIDE_TAC THEN
  SRW_TAC [][arithmeticTheory.MOD_MOD, arithmeticTheory.LESS_MULT2] THEN
  Q_TAC SUFF_TAC `r MOD (2 * x) = r` THEN1 SRW_TAC [][] THEN
  MATCH_MP_TAC arithmeticTheory.LESS_MOD THEN DECIDE_TAC);

val MSB_n2w = store_thm(
  "MSB_n2w",
  ``word32$MSB (n2w n) = 2147483648n <= word32$MOD_WL n``,
  SRW_TAC [][] THEN EQ_TAC THEN STRIP_TAC THENL [
    `0 < 2147483648n` by SRW_TAC [][] THEN
    FIRST_ASSUM (Q.SPEC_THEN `n` STRIP_ASSUME_TAC o
                 MATCH_MP arithmeticTheory.DIVISION) THEN
    Q.ABBREV_TAC `q = n DIV 2147483648` THEN POP_ASSUM (K ALL_TAC) THEN
    Q.ABBREV_TAC `r = n MOD 2147483648` THEN POP_ASSUM (K ALL_TAC) THEN
    `0 < 2n` by SRW_TAC [][] THEN
    FIRST_ASSUM (Q.SPEC_THEN `q` STRIP_ASSUME_TAC o
                 MATCH_MP arithmeticTheory.DIVISION) THEN
    Q.ABBREV_TAC `m = q DIV 2` THEN POP_ASSUM (K ALL_TAC) THEN
    Q.ABBREV_TAC `s = q MOD 2` THEN POP_ASSUM (K ALL_TAC) THEN
    `n = m * 4294967296 + (2147483648 + r)`
       by SRW_TAC [ARITH_ss][] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [arithmeticTheory.MOD_TIMES],
    SUBST_ALL_TAC (DECIDE ``4294967296 = 2 * 2147483648n``) THEN
    `0 < 2147483648n` by SRW_TAC [][] THEN
    PROVE_TAC [div_lemma, arithmeticTheory.NOT_LESS]
  ]);
val _ = export_rewrites ["MSB_n2w"]

val w4294967296 = store_thm(
  "w4294967296",
  ``4294967296w : word32 = 0w``,
  SRW_TAC [][]);
val _ = export_rewrites ["w4294967296"]

val seq32_leq_plus_num = store_thm(
  "seq32_leq_plus_num",
  ``!(s: 'a seq32) (n:num). (s <= s + n) = (n MOD 4294967296 <= 2147483648)``,
  REPEAT GEN_TAC  THEN Cases_on `s` THEN
  SRW_TAC [][seq32_plus_def, seq32_leq_def, seq32_diff_def] THEN
  Q.ABBREV_TAC `N = n MOD 4294967296` THEN
  `N < 4294967296` by SRW_TAC [][Abbr`N`, arithmeticTheory.DIVISION] THEN
  Q.ABBREV_TAC `M = 4294967296 - N` THEN
  Cases_on `M < 2147483648` THENL [
    SRW_TAC [][w2i_n2w_1] THEN
    SRW_TAC [ARITH_ss][Abbr`M`],
    Cases_on `N = 0` THENL [
      Q.UNABBREV_ALL_TAC THEN SRW_TAC [][w2i_n2w_1],
      `2147483648 <= M /\ M < 4294967296`
         by SRW_TAC[ARITH_ss][Abbr`M`] THEN
      SRW_TAC [][w2i_n2w_2] THEN
      SRW_TAC [][INT_LE_SUB_RADD] THEN
      SRW_TAC [ARITH_ss][Abbr`M`, Abbr`N`]
    ]
  ]);
val _ = export_rewrites ["seq32_leq_plus_num"]


val seq32_add_num_minus = store_thm(
  "seq32_add_num_minus",
  ``!(s:'a seq32) (n:num). n < 2147483648 ==> (s + n - s = int_of_num n)``,
  REPEAT GEN_TAC THEN Cases_on `s` THEN
  SRW_TAC [][seq32_plus_def, seq32_diff_def,
             w2i_n2w_1]);

open metisLib

val seq32_geq_plus_num = store_thm(
  "seq32_geq_plus_num",
  ``!(s:'a seq32) (n:num). (s + n >= s) = (n MOD 4294967296 < 2147483648)``,
  REPEAT GEN_TAC THEN Cases_on `s` THEN
  SRW_TAC [][seq32_geq_def, seq32_plus_def, seq32_diff_def]);
val _ = export_rewrites ["seq32_geq_plus_num"]

val seq32_lt_add_lcancel = store_thm(
  "seq32_lt_add_lcancel",
  ``!(s:'a seq32) n m. (s + n < s + m) = w2i (n2w n - n2w m) < 0``,
  REPEAT GEN_TAC THEN Cases_on `s` THEN
  SRW_TAC [][seq32_diff_def, seq32_plus_def, seq32_lt_def,
             word32Theory.WORD_SUB_PLUS]);
val _ = export_rewrites ["seq32_lt_add_lcancel"]

val seq32_add_0 = store_thm(
  "seq32_add_0",
  ``(x:'a seq32) + 0n = x``,
  Cases_on `x` THEN SRW_TAC [][seq32_plus_def]);
val _ = export_rewrites ["seq32_add_0"]

val strong_word_nchotomy = store_thm(
  "strong_word_nchotomy",
  ``!w:word32. ?n:num. n < 4294967296 /\ (w = n2w n)``,
  GEN_TAC THEN
  Q.SPEC_THEN `w` (Q.X_CHOOSE_THEN `m` SUBST_ALL_TAC)
              word32Theory.word_nchotomy THEN
  Q.EXISTS_TAC `m MOD 4294967296` THEN
  SRW_TAC [][arithmeticTheory.DIVISION]);

val NOT_LESS = arithmeticTheory.NOT_LESS
val NOT_LESS_EQ = arithmeticTheory.NOT_LESS_EQUAL

val seq32_add_num_sub = store_thm(
  "seq32_add_num_sub",
  ``(!x:'a. x = ARB) /\ (s2 >= s1:'a seq32) ==>
    (s1 + Num(s2 - s1) = s2)``,
  Cases_on `s1` THEN Cases_on `s2` THEN
  SRW_TAC [][seq32_geq_def,
             seq32_diff_def,
             seq32_plus_def] THEN
  Q.SPEC_THEN `w'` (Q.X_CHOOSE_THEN `n` STRIP_ASSUME_TAC)
              strong_word_nchotomy THEN
  Q.SPEC_THEN `w` (Q.X_CHOOSE_THEN `m` STRIP_ASSUME_TAC)
              strong_word_nchotomy THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [WORD_SUB_EQN] THEN
  SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `n - m < 2147483648` THENL [
      FULL_SIMP_TAC (srw_ss()) [w2i_n2w_1] THEN SRW_TAC [ARITH_ss][],
      `2147483648 <= n - m /\ n - m < 4294967296` by DECIDE_TAC  THEN
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                    [w2i_n2w_2, integerTheory.INT_SUB_LE]
    ],
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `n + 4294967296 - m < 2147483648` THENL [
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss ++ WORD32_ss)
                    [w2i_n2w_1, arithmeticTheory.ADD_MODULUS],
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2i_n2w_2,
                                            integerTheory.INT_SUB_LE,
                                            NOT_LESS_EQ, NOT_LESS]
    ]
  ]);

val w2i_n2w_0_leq = store_thm(
  "w2i_n2w_0_leq",
  ``n1 < 4294967296 /\ n2 < 4294967296 /\ 0 <= w2i (n2w (n1 - n2)) ==>
    n1 - n2 < 2147483648``,
  STRIP_TAC THEN
  SPOSE_NOT_THEN (ASSUME_TAC o
                  REWRITE_RULE [arithmeticTheory.NOT_LESS]) THEN
  `n1 - n2 < 4294967296` by DECIDE_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [w2in2w2] THEN
  DECIDE_TAC);

val seq32_nchotomy = TypeBase.nchotomy_of ``:'a seq32``

val seq32_num_sub_lt = store_thm(
  "seq32_num_sub_lt",
  ``s1:'a seq32 < s2 + n /\ s1 >= s2 ==> Num(s1 - s2) < n``,
  Q.SPEC_THEN `s1` (Q.X_CHOOSE_THEN `a1` (Q.X_CHOOSE_THEN `w1` SUBST_ALL_TAC))
                   seq32_nchotomy THEN
  Q.SPEC_THEN `s2` (Q.X_CHOOSE_THEN `a2` (Q.X_CHOOSE_THEN `w2` SUBST_ALL_TAC))
                   seq32_nchotomy THEN
  SIMP_TAC (srw_ss()) [seq32_lt_def, seq32_geq_def, seq32_plus_def,
                       seq32_diff_def] THEN
  Q.SPEC_THEN `w1` (Q.X_CHOOSE_THEN `j` STRIP_ASSUME_TAC)
              strong_word_nchotomy THEN
  Q.SPEC_THEN `w2` (Q.X_CHOOSE_THEN `i` STRIP_ASSUME_TAC)
              strong_word_nchotomy THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `i <= j` THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
    REPEAT STRIP_TAC THEN
    `w2i (n2w j - n2w i) = w2i (n2w (j - i))` by SRW_TAC [][WORD_SUB_EQN] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `j - i < 2147483648` by PROVE_TAC [w2i_n2w_0_leq] THEN
    Q_TAC SUFF_TAC `j - i < n` THEN1 SRW_TAC [][w2in2w1] THEN
    Q_TAC SUFF_TAC `j < i + n` THEN1 DECIDE_TAC THEN
    SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
    `j - (i + n) < 2147483648` by DECIDE_TAC THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2i_n2w_1, WORD_SUB_EQN],

    FULL_SIMP_TAC (srw_ss()) [NOT_LESS_EQ] THEN
    `w2i (n2w j - n2w i) = w2i (n2w (j + 4294967296 - i))`
       by SRW_TAC [ARITH_ss][WORD_SUB_EQN] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    REPEAT STRIP_TAC THEN
    `j + 2147483648 < i`
       by (SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
           `2147483648 <= j + 4294967296 - i /\
            j + 4294967296 - i < 4294967296` by DECIDE_TAC THEN
           FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2i_n2w_2]) THEN
    Q.PAT_ASSUM `0 <= w2i (n2w X)` (K ALL_TAC) THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2i_n2w_1] THEN
    REPEAT VAR_EQ_TAC THEN
    `0 < n`
       by (SPOSE_NOT_THEN (ASSUME_TAC o SIMP_RULE (srw_ss()) [NOT_LESS]) THEN
           Q.PAT_ASSUM `w2i x < 0` MP_TAC THEN
           ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [WORD_SUB_EQN] THEN
           ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2i_n2w_1]) THEN
    ASM_REWRITE_TAC [] THEN
    Q.PAT_ASSUM `w2i x < 0` MP_TAC THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [WORD_SUB_EQN] THEN
    Cases_on `j + 4294967296 - (i + n) MOD 4294967296 < 2147483648` THEN1
          ASM_SIMP_TAC (srw_ss()) [w2i_n2w_1] THEN
    FULL_SIMP_TAC (srw_ss()) [NOT_LESS] THEN
    `(i + n) MOD 4294967296 <= j + 2147483648` by DECIDE_TAC THEN
    `(i + n) MOD 4294967296 < i` by DECIDE_TAC THEN
    `4294967296 <= i + n`
       by (SPOSE_NOT_THEN (ASSUME_TAC o
                           REWRITE_RULE [NOT_LESS_EQ]) THEN
           FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                         [arithmeticTheory.LESS_MOD]) THEN
    STRIP_TAC THEN
    `j < (i + n) MOD 4294967296`
       by (SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
           Q.ABBREV_TAC `N = (i + n) MOD 4294967296` THEN
           `j + 4294967296 - N = (j - N) + 4294967296` by DECIDE_TAC THEN
           `n2w (j + 4294967296 - N) = n2w (j - N) : word32`
                   by ASM_SIMP_TAC (srw_ss())
                                   [arithmeticTheory.ADD_MODULUS] THEN
           `j - N < 2147483648` by DECIDE_TAC THEN
           `w2i (n2w (j + 4294967296 - N)) = w2i (n2w (j - N))`
              by SRW_TAC [][] THEN
           `_ = (&)(j - N)` by SRW_TAC [][w2i_n2w_1] THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
    Q_TAC SUFF_TAC `!x y n. 0 < n /\ x < y MOD n /\ n <= y ==> x + n < y`
           THEN1 ASM_SIMP_TAC (srw_ss()) [] THEN
    REPEAT (POP_ASSUM (K ALL_TAC)) THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (Q.SPEC_THEN `y` STRIP_ASSUME_TAC o
                 MATCH_MP arithmeticTheory.DIVISION) THEN
    Q.ABBREV_TAC `q = y DIV n` THEN POP_ASSUM (K ALL_TAC) THEN
    Q.ABBREV_TAC `r = y MOD n` THEN POP_ASSUM (K ALL_TAC) THEN
    SRW_TAC [][] THEN
    `~(q =0)`
       by (STRIP_TAC THEN
           FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []) THEN
    MATCH_MP_TAC arithmeticTheory.LESS_LESS_EQ_TRANS THEN
    Q.EXISTS_TAC `n + r` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
    Cases_on `q` THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                  [arithmeticTheory.MULT_CLAUSES]
  ]);

val seq32_gt_refl = store_thm(
  "seq32_gt_refl",
  ``(x:'a seq32 > x) = F``,
  SRW_TAC [][seq32_gt_def] THEN
  Cases_on `x` THEN
  SRW_TAC [][seq32_diff_def, w2i_n2w_1]);
val _ = export_rewrites ["seq32_gt_refl"]

val seq32_add_assoc = store_thm(
  "seq32_add_assoc",
  ``((x : 'a seq32) + y:num) + z = x + (y + z)``,
  Cases_on `x` THEN
  SRW_TAC [][seq32_plus_def, GSYM word32Theory.WORD_ADD_ASSOC]);

val seq32_sub_id = store_thm(
  "seq32_sub_id",
  ``(x:'a seq32) - x = 0``,
  Cases_on `x` THEN
  SRW_TAC [][seq32_diff_def, w2i_n2w_1]);
val _ = export_rewrites ["seq32_sub_id"]

val seq32_lt_Num_diff_imp = store_thm(
  "seq32_lt_Num_diff_imp",
  ``s1 >= s2 /\ n < Num(s1:'a seq32 - s2) ==> s2 + n < s1``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  Cases_on `n1 = n2` THENL [
    SRW_TAC [WORD32_ss][TCP1_baseTypesTheory.seq32_lt_def,
                        TCP1_baseTypesTheory.seq32_diff_def,
                        TCP1_baseTypesTheory.seq32_plus_def,
                        w2in2w1, WORD_SUB_EQN],
    ALL_TAC
  ] THEN
  SRW_TAC [WORD32_ss][TCP1_baseTypesTheory.seq32_diff_def,
                      TCP1_baseTypesTheory.seq32_plus_def,
                      TCP1_baseTypesTheory.seq32_lt_def,
                      TCP1_baseTypesTheory.seq32_geq_def,
                      WORD_SUB_EQN]
  THENL [
    `n1 - n2 < 2147483648`
      by (SPOSE_NOT_THEN (ASSUME_TAC o
                          REWRITE_RULE [arithmeticTheory.NOT_LESS]) THEN
          `n1 - n2 < 4294967296` by DECIDE_TAC THEN
          FULL_SIMP_TAC (srw_ss()) [w2in2w2] THEN
          DECIDE_TAC) THEN
    FULL_SIMP_TAC (srw_ss()) [w2in2w1, int_ge] THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2],

    `n1 - n2 < 2147483648`
      by (SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
          `n1 - n2 < 4294967296` by DECIDE_TAC THEN
          FULL_SIMP_TAC (srw_ss()) [w2in2w2] THEN DECIDE_TAC) THEN
    FULL_SIMP_TAC (srw_ss()) [w2in2w1, int_ge] THEN
    `n2 + n < 4294967296` by DECIDE_TAC THEN
    SRW_TAC [][arithmeticTheory.DIVISION] THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2],

    `n1 + 4294967296 - n2 < 2147483648`
       by (SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
          `n1 + 4294967296 - n2 < 4294967296` by DECIDE_TAC THEN
          FULL_SIMP_TAC (srw_ss()) [w2in2w2] THEN
          DECIDE_TAC) THEN
    FULL_SIMP_TAC (srw_ss()) [w2in2w1] THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2],

    `n1 + 4294967296 - n2 < 2147483648`
       by (SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
          `n1 + 4294967296 - n2 < 4294967296` by DECIDE_TAC THEN
          FULL_SIMP_TAC (srw_ss()) [w2in2w2] THEN
          DECIDE_TAC) THEN
    FULL_SIMP_TAC (srw_ss()) [w2in2w1] THEN
    `n2 + n < 4294967296` by DECIDE_TAC THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2, arithmeticTheory.DIVISION,
                                         INT_LT_SUB_RADD]
  ]);

val lt_Num_seq_diff = store_thm(
  "lt_Num_seq_diff",
  ``s1 >= s2 /\ n < 2147483648 ==>
    (n < Num(s1:'a seq32 - s2)) = (s2 + n < s1)``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  Cases_on `n1 = n2` THENL [
    SRW_TAC [WORD32_ss][TCP1_baseTypesTheory.seq32_lt_def,
                        TCP1_baseTypesTheory.seq32_diff_def,
                        TCP1_baseTypesTheory.seq32_plus_def,
                        w2in2w1, WORD_SUB_EQN],
    ALL_TAC
  ] THEN
  SRW_TAC [WORD32_ss][TCP1_baseTypesTheory.seq32_diff_def,
                      TCP1_baseTypesTheory.seq32_plus_def,
                      TCP1_baseTypesTheory.seq32_lt_def,
                      TCP1_baseTypesTheory.seq32_geq_def,
                      WORD_SUB_EQN]
  THENL [
    `n1 - n2 < 2147483648 /\ n2 + n - n1 < 2147483648` by DECIDE_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [w2in2w1, int_ge] THEN
    DECIDE_TAC,

    `n1 - n2 < 2147483648`
       by (SPOSE_NOT_THEN (ASSUME_TAC o
                           REWRITE_RULE [arithmeticTheory.NOT_LESS]) THEN
           `n1 - n2 < 4294967296` by DECIDE_TAC THEN
           FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                         [w2in2w2, int_ge,
                          INT_LE_SUB_LADD]) THEN
    FULL_SIMP_TAC (srw_ss()) [w2in2w1, int_ge] THEN
    `n2 + n < 4294967296` by DECIDE_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [arithmeticTheory.DIVISION] THEN
    `n2 + n + 4294967296 - n1 < 4294967296 /\
     2147483648 <= n2 + n + 4294967296 - n1` by DECIDE_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [w2in2w2, INT_LT_SUB_RADD] THEN
    DECIDE_TAC,

    `n1 + 4294967296 - n2 < 2147483648`
       by (`n1 + 4294967296 - n2 < 4294967296` by DECIDE_TAC THEN
           SPOSE_NOT_THEN (ASSUME_TAC o
                           REWRITE_RULE [arithmeticTheory.NOT_LESS]) THEN
           FULL_SIMP_TAC (srw_ss()) [w2in2w2, int_ge,
                                     INT_LE_SUB_LADD] THEN
           FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []) THEN
    ASM_SIMP_TAC (srw_ss()) [w2in2w1] THEN
    `2147483648 <= n2 + n - n1` by DECIDE_TAC THEN
    Cases_on `4294967296 <= n2 + n - n1` THENL [
      `n2w (n2 + n - n1) = n2w (n2 + n - n1 - 4294967296) : word32`
         by SRW_TAC [WORD32_ss][arithmeticTheory.SUB_MOD] THEN
      `n2 + n - n1 - 4294967296 < 2147483648` by DECIDE_TAC THEN
      ASM_SIMP_TAC (srw_ss()) [w2in2w1] THEN DECIDE_TAC,
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2] THEN
      ASM_SIMP_TAC (srw_ss()) [INT_LT_SUB_RADD] THEN
      DECIDE_TAC
    ],

    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val seq32_leq_geq = store_thm(
  "seq32_leq_geq",
  ``~2147483648 < s1 - s2  ==> (s1:'a seq32 >= s2) = (s2 <= s1)``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  ASM_SIMP_TAC (srw_ss()) [seq32_geq_def, seq32_leq_def, seq32_diff_def] THEN
  Cases_on `n1 = n2` THENL [
    SRW_TAC [WORD32_ss][w2in2w1, int_ge],
    ALL_TAC
  ] THEN
  SRW_TAC [][WORD_SUB_EQN] THENL [
    PROVE_TAC [arithmeticTheory.LESS_EQUAL_ANTISYM],

    Cases_on `n1 - n2 < 2147483648` THENL [
      ASM_SIMP_TAC (srw_ss()) [w2in2w1, int_ge] THEN
      `n2 + 4294967296 - n1 < 4294967296` by DECIDE_TAC THEN
      `2147483648 <= n2 + 4294967296 - n1` by DECIDE_TAC THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)
                   [w2in2w2, INT_LE_SUB_RADD],
      `w2i (n2w (n1 - n2)) = ~(4294967296 - (&)(n1 - n2))`
         by ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1]
    ],

    Cases_on `n2 - n1 < 2147483648` THENL [
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1, w2in2w2],
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2] THEN
      `n1 + 4294967296 - n2 < 2147483648`
         by (SPOSE_NOT_THEN (ASSUME_TAC o
                             REWRITE_RULE [NOT_LESS]) THEN
             `w2i (n2w (n1 + 4294967296 - n2)) =
                  ~(4294967296 - (&)(n1 + 4294967296 - n2))`
                by ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2] THEN
             FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []) THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []
    ],

    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val seq32_sub_bounded = store_thm(
  "seq32_sub_bounded",
  ``(s1:'a seq32) <= s2 /\ s2 < s1 + n /\ 0 < n /\ n < 2147483648n ==>
    ~2147483648 < s2 - s1``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [WORD32_ss][WORD_SUB_EQN, seq32_diff_def, seq32_leq_def,
                      seq32_lt_def, seq32_plus_def]
  THENL [
    `n1 = n2` by DECIDE_TAC THEN SRW_TAC [WORD32_ss][w2in2w1],
    `n2 + 4294967296 - n1 < 4294967296` by DECIDE_TAC THEN
    Cases_on `n2 + 4294967296 - n1 < 2147483648` THENL [
      ASM_SIMP_TAC (srw_ss()) [w2in2w1],
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2,
                                           INT_LT_SUB_LADD]
    ],
    `n1 = n2` by DECIDE_TAC THEN SRW_TAC [WORD32_ss][w2in2w1],
    `n2 + 4294967296 - n1 < 4294967296` by DECIDE_TAC THEN
    Cases_on `n2 + 4294967296 - n1 < 2147483648` THENL [
      ASM_SIMP_TAC (srw_ss()) [w2in2w1],
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2] THEN
      Q_TAC SUFF_TAC `~(n1 = n2 + 2147483648)` THEN1 DECIDE_TAC THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
      Cases_on `n + (n2 + 2147483648) < 4294967296` THENL [
        FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.DIVISION] THEN
        `n2 + 4294967296 - (n + (n2 + 2147483648)) = 2147483648 - n`
           by DECIDE_TAC THEN
        FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1],
        `(n + (n2 + 2147483648)) MOD 4294967296 = n + n2 - 2147483648`
           by (`n + (n2 + 2147483648) = 4294967296 + (n + n2 - 2147483648)`
                   by DECIDE_TAC THEN
               ASM_REWRITE_TAC [] THEN
               ASM_SIMP_TAC (srw_ss())
                            [arithmeticTheory.ADD_MODULUS_RIGHT] THEN
               DECIDE_TAC) THEN
        FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
        `n2w (6442450944 - n) : word32 = n2w (2147483648 - n)`
           by (SRW_TAC [WORD32_ss][] THEN
               `6442450944 - n = 4294967296 + (2147483648 - n)`
                  by DECIDE_TAC THEN
               ASM_SIMP_TAC (srw_ss())
                            [arithmeticTheory.ADD_MODULUS_RIGHT]) THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1]
      ]
    ],

    Cases_on `n2 - n1 < 2147483648` THENL [
      ASM_SIMP_TAC (srw_ss()) [w2in2w1],
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2] THEN
      Q_TAC SUFF_TAC `~(n2 = n1 + 2147483648)` THEN1 DECIDE_TAC THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1]
    ],

    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Cases_on `n2 - n1 < 2147483648` THENL [
      ASM_SIMP_TAC (srw_ss()) [w2in2w1],
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2]
    ],

    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val seq32_lt_gt_incompatible = store_thm(
  "seq32_lt_gt_incompatible",
  ``(s1:'a seq32 > s2 /\ s1 < s2) = F``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  Q_TAC SUFF_TAC
        `(w2i (n2w n1 - n2w n2) > 0 /\ w2i (n2w n1 - n2w n2) < 0) = F`
         THEN1 SRW_TAC [][seq32_diff_def, seq32_lt_def, seq32_gt_def] THEN
  intLib.ARITH_TAC);

val seq32_lt_refl = store_thm(
  "seq32_lt_refl",
  ``~(s1:'a seq32 < s1)``,
  SRW_TAC [][seq32_lt_def]);
val _ = export_rewrites ["seq32_lt_refl"]

val seq32_geq_diff_bounds = store_thm(
  "seq32_geq_diff_bounds",
  ``s1:'a seq32 >= s2 ==> 0 <= s1 - s2 /\ s1 - s2 < 2147483648``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [ARITH_ss][WORD_SUB_EQN, seq32_geq_def, seq32_diff_def]
  THENL [
    Q_TAC SUFF_TAC `n1 - n2 < 2147483648` THEN1
          ASM_SIMP_TAC (srw_ss()) [w2in2w1] THEN
    DECIDE_TAC,
    Q_TAC SUFF_TAC `n1 + 4294967296 - n2 < 2147483648` THEN1
          ASM_SIMP_TAC (srw_ss()) [w2in2w1] THEN
    DECIDE_TAC
  ]);

val seq32_Num_diff_upperbound = store_thm(
  "seq32_Num_diff_upperbound",
  ``s1:'a seq32 >= s2 ==> Num(s1 - s2) < 2147483648``,
  STRIP_TAC THEN IMP_RES_TAC seq32_geq_diff_bounds THEN
  Q_TAC SUFF_TAC `int_of_num (Num(s1 - s2)) < int_of_num 2147483648`
        THEN1 SRW_TAC [][] THEN
  `int_of_num (Num(s1 - s2)) = s1 - s2`
     by SRW_TAC [][integerTheory.INT_OF_NUM] THEN
  POP_ASSUM SUBST_ALL_TAC THEN SRW_TAC [][]);


val seq32_Num_diff_lt_imp = store_thm(
  "seq32_Num_diff_lt_imp",
  ``Num(s1 - s2) < n /\ n < 2147483648 /\ s1 >= s2 ==> s2 + n > s1``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  Cases_on `n1 = n2` THENL [
    SRW_TAC [ARITH_ss][WORD_SUB_EQN, seq32_diff_def, seq32_plus_def,
                       seq32_geq_def, seq32_gt_def, w2in2w1],
    ALL_TAC
  ] THEN
  STRIP_TAC THEN
  Q_TAC SUFF_TAC `w2i (n2w (n2 + n) - n2w n1) > 0`
        THEN1 SRW_TAC [][seq32_gt_def, seq32_plus_def, seq32_diff_def] THEN
  Q_TAC SUFF_TAC `w2i (n2w (n2 + n - n1)) > 0`
        THEN1 SRW_TAC [ARITH_ss][WORD_SUB_EQN] THEN
  `s1 - s2 >= 0` by FULL_SIMP_TAC (srw_ss())[seq32_geq_def] THEN
  `w2i (n2w n1 - n2w n2) >= 0`
     by (SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [seq32_diff_def]) THEN
  Cases_on `n2 <= n1` THENL [
    `n2w n1 - n2w n2 = n2w (n1 - n2) : word32` by SRW_TAC [][WORD_SUB_EQN] THEN
    `(n1 - n2) MOD 4294967296 < 2147483648` by FULL_SIMP_TAC (srw_ss()) [] THEN
    `n1 - n2 < 4294967296` by DECIDE_TAC THEN
    `n1 - n2 < 2147483648` by FULL_SIMP_TAC (srw_ss()) [] THEN
    `n1 - n2 < n` by (SRW_TAC [][] THEN
                      FULL_SIMP_TAC (srw_ss()) [seq32_diff_def, w2in2w1]) THEN
    `n2 + n - n1 < 4294967296` by DECIDE_TAC THEN
    SRW_TAC [ARITH_ss][],

    `n1 < n2` by DECIDE_TAC THEN
    `n1 + 4294967296 - n2 < 4294967296` by DECIDE_TAC THEN
    `n2w n1 - n2w n2 = n2w (n1 + 4294967296 - n2) : word32`
       by SRW_TAC [][WORD_SUB_EQN] THEN
    `n1 + 4294967296 - n2 < 2147483648`
       by FULL_SIMP_TAC (srw_ss()) [] THEN
    `s1 - s2 = w2i (n2w (n1 + 4294967296 - n2))`
       by FULL_SIMP_TAC (srw_ss()) [seq32_diff_def, WORD_SUB_EQN] THEN
    ` _ = int_of_num (n1 + 4294967296 - n2)` by SRW_TAC [][w2in2w1] THEN
    `n1 + 4294967296 - n2 < n` by FULL_SIMP_TAC (srw_ss()) [] THEN
    `4294967296 < n2 + n - n1` by DECIDE_TAC THEN
    `n2 + n - n1 < 4294967296 + 2147483648` by DECIDE_TAC THEN
    `(n2 + n - n1) MOD 4294967296 = n2 + n - n1 - 4294967296`
       by intLib.ARITH_TAC THEN
    Q_TAC SUFF_TAC `0 < n2 + n - n1 - 4294967296` THEN1 SRW_TAC [][] THEN
    Q.ABBREV_TAC `bigN = n2 + n - n1` THEN
    DECIDE_TAC
  ]);

(* gets messy ...
val seq32_lt_monotone_num = store_thm(
  "seq32_lt_monotone_num",
  ``s1:'a seq32 < s2 ==> s1 + (n:num) < s2 + n``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [TypeBase.nchotomy_of "seq32"] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [][seq32_lt_def, seq32_plus_def, seq32_diff_def, WORD_SUB_EQN]
  THENL [
    Cases_on `n1 - n2 < 2147483648` THENL [
      FULL_SIMP_TAC (srw_ss()) [w2in2w1],
      `n1 - n2 < 4294967296` by DECIDE_TAC THEN
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2]
    ],
    Cases_on `n1 + 4294967296 - n2 < 2147483648` THENL [
      FULL_SIMP_TAC (srw_ss()) [w2in2w1],
      `n1 + 4294967296 - n2 < 4294967296` by DECIDE_TAC THEN
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2] THEN
      `n2 <= n1 + 2147483648` by DECIDE_TAC THEN
      Q.ABBREV_TAC `nn1 = (n + n1) MOD 4294967296` THEN
      Q.ABBREV_TAC `nn2 = (n + n2) MOD 4294967296` THEN
      `nn1 < 4294967296 /\ nn2 < 4294967296`
         by SRW_TAC [][arithmeticTheory.DIVISION, Abbr`nn1`, Abbr`nn2`] THEN
      Cases_on `nn2 <= nn1` THENL [
        `nn1 + 4294967296 - nn2 = nn1 - nn2 + 4294967296`
           by DECIDE_TAC THEN
        `n2w (nn1 + 4294967296 - nn2) : word32 = n2w(nn1 - nn2)`
           by (POP_ASSUM SUBST_ALL_TAC THEN
               SRW_TAC [][arithmeticTheory.ADD_MODULUS]) THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        Q_TAC SUFF_TAC `2147483648 <= nn1 - nn2` THEN1
              ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2] THEN

*)


val w2i_n2w_lt0 = store_thm(
  "w2i_n2w_lt0",
  ``n1 < 4294967296 /\ n2 < 4294967296 /\ n1 < n2 /\
    w2i (n2w (n1 + 4294967296 - n2)) < 0 ==>
    2147483648 <= n1 + 4294967296 - n2``,
  STRIP_TAC THEN
  SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS_EQ]) THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1]);

val w2i_n2w_0_leq2 = store_thm(
  "w2i_n2w_0_leq2",
  ``n1 < 4294967296 /\ n2 < 4294967296 /\ n1 < n2 /\
    0 <= w2i (n2w (n1 + 4294967296 - n2)) ==>
    n1 + 4294967296 - n2 < 2147483648``,
  STRIP_TAC THEN
  SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
  `n1 + 4294967296 - n2 < 4294967296` by DECIDE_TAC THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2]);

val seq32_Num_sub_lt_monotone = store_thm(
  "seq32_Num_sub_lt_monotone",
  ``s1 >= s3 /\ s2 >= s3 ==>
    ((Num(s1:'a seq32 - s3) < Num(s2 - s3)) = (s1 < s2))``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2) /\
   (?w3 a3. s3 = SEQ32 a3 w3)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2) /\
   (?n3. n3 < 4294967296 /\ w3 = n2w n3)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [ARITH_ss]
          [seq32_lt_def, seq32_geq_def, seq32_plus_def, seq32_diff_def,
           WORD_SUB_EQN]
  THENL [
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1],

    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1, w2in2w2],

    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1, w2in2w2],

    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],

    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1, w2in2w2],

    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2, w2in2w1],

    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2, w2in2w1]
  ]);

val seq32_gt_imp_lt = store_thm(
  "seq32_gt_imp_lt",
  ``s1 > s2 ==> s2 < s1``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [ARITH_ss]
          [seq32_lt_def, seq32_gt_def, seq32_plus_def, seq32_diff_def,
           WORD_SUB_EQN] THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1, w2in2w2]);

val seq32_geq_disj = store_thm(
  "seq32_geq_disj",
  ``(!x:'a. x = ARB) ==> ((s1:'a seq32 >= s2) = ((s1 = s2) \/ (s1 > s2)))``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [ARITH_ss]
          [seq32_gt_def, seq32_geq_def, seq32_diff_def, WORD_SUB_EQN]);

val seq32_sub_eq0 = store_thm(
  "seq32_sub_eq0",
  ``(!x:'a. x = ARB) ==> ((s2:'a seq32 - s1 = 0) = (s1 = s2))``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [ARITH_ss][seq32_diff_def, WORD_SUB_EQN] THENL [
    Cases_on `n2 - n1 < 2147483648` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1, w2in2w2],
    Cases_on `n2 + 4294967296 - n1 < 2147483648` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1, w2in2w2]
  ]);

val seq32_gt_antisym = store_thm (
  "seq32_gt_antisym",
  ``((s1 : 'a seq32) > s2 /\ s2 > s1) = F``,
  PROVE_TAC [seq32_lt_gt_incompatible, seq32_gt_imp_lt]);

val seq32_geq_refl = store_thm(
  "seq32_geq_refl",
  ``(s1 : 'a seq32) >= s1``,
  SRW_TAC [][seq32_geq_def]);
val _ = export_rewrites ["seq32_geq_refl"]

val seq32_geq_antisym = store_thm(
  "seq32_geq_antisym",
  ``(!x:'a. x = ARB) /\ (s1 : 'a seq32) >= s2 /\ s2 >= s1 ==> (s1 = s2)``,
  PROVE_TAC [seq32_geq_disj, seq32_gt_refl, seq32_gt_antisym]);

val seq32_not_gt = store_thm(
  "seq32_not_gt",
  ``~(s1:'a seq32 > s2) = (s1 <= s2)``,
  SRW_TAC [][seq32_gt_def, seq32_leq_def] THEN intLib.ARITH_TAC);

val seq32_leq_disj = store_thm(
  "seq32_leq_disj",
  ``(!x:'a. x = ARB) ==> ((s1:'a seq32 <= s2) = (s1 < s2 \/ (s1 = s2)))``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [][seq32_diff_def, seq32_leq_def, seq32_lt_def, WORD_SUB_EQN] THENL [
    Cases_on `n1 - n2 < 2147483648` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1, w2in2w2],
    Cases_on `n1 + 4294967296 - n2 < 2147483648` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1, w2in2w2]
  ]);

val seq32_add_posint = store_thm(
  "seq32_add_posint",
  ``(s1:'a seq32) + int_of_num n = s1 + n``,
  `(?w1 a1. s1 = SEQ32 a1 w1)` by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [][seq32_plus'_def, seq32_plus_def, integer_word32Theory.i2w_def]);
val _ = export_rewrites ["seq32_add_posint"]

val seq32_geq_imp_leq = store_thm(
  "seq32_geq_imp_leq",
  ``(s1 : 'a seq32) >= s2 ==> s2 <= s1``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [ARITH_ss][seq32_geq_def, seq32_leq_def, seq32_diff_def,
                     WORD_SUB_EQN]
  THENL [
    `n1 = n2` by DECIDE_TAC THEN FULL_SIMP_TAC (srw_ss()) [w2in2w1],
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2],
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2],
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val seq32_lt_discrete = store_thm(
  "seq32_lt_discrete",
  ``((s1 : 'a seq32) < s2 /\ s2 < s1 + 1n) = F``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [ARITH_ss][seq32_diff_def, seq32_lt_def, seq32_plus_def,
                     WORD_SUB_EQN]
  THENL [
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    `(n1 + 1 = 4294967296) \/ n1 + 1 < 4294967296` by DECIDE_TAC THENL [
      SRW_TAC [][] THEN
      `n2w (n2 + 4294967296): word32 = n2w n2`
        by (`n2w (n2 + 4294967296):word32 = n2w n2 + n2w 4294967296`
              by SRW_TAC [][] THEN
           `4294967296w : word32 = 0w` by SRW_TAC [][] THEN
           POP_ASSUM SUBST_ALL_TAC THEN
           ASM_REWRITE_TAC [] THEN SRW_TAC [][]) THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      Cases_on `w2i (n2w n2) < 0` THEN ASM_REWRITE_TAC [] THEN
      `2147483648 <= n2` by
          (SPOSE_NOT_THEN ASSUME_TAC THEN
           `w2i (n2w n2) = (&)n2` by SRW_TAC [ARITH_ss][w2i_n2w_1] THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
      SRW_TAC [ARITH_ss][w2i_n2w_1],
      ASM_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `w2i (n2w (n2 + 4294967296 - (n1 + 1))) < 0` THEN
      ASM_REWRITE_TAC [] THEN
      `2147483648 <= n2 + 4294967296 - (n1 + 1)`
         by SRW_TAC [ARITH_ss][w2i_n2w_lt0] THEN
      `n1 - n2 < 2147483648` by DECIDE_TAC THEN
      SRW_TAC [][w2i_n2w_1]
    ],
    Cases_on `w2i (n2w (n1 + 4294967296 - n2)) < 0` THEN
    ASM_REWRITE_TAC [] THEN
    `2147483648 <= n1 + 4294967296 - n2`
       by SRW_TAC [ARITH_ss][w2i_n2w_lt0] THEN
    `n2 - (n1 + 1) < 2147483648` by DECIDE_TAC THEN
    SRW_TAC [ARITH_ss][w2i_n2w_1],
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)[]
  ]);

val _ = export_theory()

end (* struct *)
