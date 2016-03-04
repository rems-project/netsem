open HolKernel Parse boolLib

open TCP1_baseTypesTheory integer_wordTheory
open simpLib boolSimps numSimps BasicProvers bossLib intLib
open lcsymtacs
val _ = new_theory "TCP1_seq32Props";

val int_ge = integerTheory.int_ge
val INT_LE_SUB_RADD = integerTheory.INT_LE_SUB_RADD
val INT_LT_SUB_RADD = integerTheory.INT_LT_SUB_RADD
val INT_LE_SUB_LADD = integerTheory.INT_LE_SUB_LADD
val INT_LT_SUB_LADD = integerTheory.INT_LT_SUB_LADD
val w2in2w1 = integer_wordTheory.w2i_n2w_pos
val w2in2w2 = integer_wordTheory.w2i_n2w_neg
val INT_MAX32 = SIMP_CONV (srw_ss()) [wordsTheory.INT_MAX_def] ``INT_MAX(:32) : num``

val WORD32_ss =
    rewrites [bitTheory.BIT_def, bitTheory.BITS_def, INT_MAX32,
              bitTheory.MOD_2EXP_def, bitTheory.DIV_2EXP_def,
              wordsTheory.n2w_11, wordsTheory.WORD_ADD_0,
              wordsTheory.word_add_n2w,
              wordsTheory.dimword_32,
              wordsTheory.dimindex_32,
              wordsTheory.WORD_NEG_NEG,
              wordsTheory.WORD_SUB_REFL,
              wordsTheory.word_0, wordsTheory.w2n_11,
              wordsTheory.WORD_ADD_SUB2,
              wordsTheory.WORD_ADD_SUB3,
              integer_wordTheory.INT_MIN_def,
              wordsTheory.INT_MIN_def,
              REWRITE_RULE [wordsTheory.word_0] wordsTheory.WORD_NEG_EQ_0]

val _ = augment_srw_ss [WORD32_ss,
                        rewrites [int_ge, integerTheory.int_gt,
                                  INT_LE_SUB_RADD, INT_LT_SUB_RADD,
                                  INT_LE_SUB_LADD, INT_LT_SUB_LADD]]

val w2n_eq_0 = store_thm(
  "w2n_eq_0[simp]",
  ``(w2n (w:word32) = 0) = (w = n2w 0)``,
  `0 = w2n (n2w 0 : word32)`
    by SRW_TAC [][] THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) THEN
  SRW_TAC [][]);

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

val w4294967296 = store_thm(
  "w4294967296[simp]",
  ``4294967296w : word32 = 0w``,
  SRW_TAC [][]);

val seq32_leq_plus_num = store_thm(
  "seq32_leq_plus_num[simp]",
  ``!(s: 'a seq32) (n:num). (s <= s + n) = (n MOD 4294967296 <= 2147483648)``,
  REPEAT GEN_TAC  THEN Cases_on `s` THEN
  SRW_TAC [][seq32_plus_def, seq32_leq_def, seq32_diff_def] THEN
  Q.ABBREV_TAC `N = n MOD 4294967296` THEN
  `N < 4294967296` by SRW_TAC [][Abbr`N`, arithmeticTheory.DIVISION] THEN
  Q.ABBREV_TAC `M = 4294967296 - N` THEN
  Cases_on `M < 2147483648` THENL [
    SRW_TAC [][w2i_n2w_pos, wordsTheory.word_2comp_n2w, w2i_n2w_pos] THEN
    SRW_TAC [ARITH_ss][Abbr`M`, Abbr`N`],
    Cases_on `N = 0` THENL [
      markerLib.UNABBREV_ALL_TAC THEN
      SRW_TAC [][w2i_n2w_pos, wordsTheory.word_2comp_n2w],
      `2147483648 <= M /\ M < 4294967296`
         by SRW_TAC[ARITH_ss][Abbr`M`] THEN
      SRW_TAC [][w2i_n2w_neg, wordsTheory.word_2comp_n2w] THEN
      SRW_TAC [ARITH_ss][Abbr`M`, Abbr`N`]
    ]
  ]);

val seq32_add_num_minus = store_thm(
  "seq32_add_num_minus",
  ``!(s:'a seq32) (n:num). n < 2147483648 ==> (s + n - s = int_of_num n)``,
  REPEAT GEN_TAC THEN Cases_on `s` THEN
  SRW_TAC [][seq32_plus_def, seq32_diff_def,
             w2i_n2w_pos]);

open metisLib

val ZEROI_LEQ_W2I = store_thm(
  "ZEROI_LEQ_W2I[simp]",
  ``0 ≤ w2i w ⇔ 0w ≤ w``,
  METIS_TAC[word_0_w2i, WORD_LEi]);

val EVEN_SEGMENTS = store_thm(
  "EVEN_SEGMENTS",
  ``0 < m ⇒ ((n DIV m) MOD 2 ≠ 1 ⇔ n MOD (2 * m) < m)``,
  strip_tac >>
  qspec_then `m` (IMP_RES_THEN (qspec_then `n` strip_assume_tac))
    arithmeticTheory.DIVISION >>
  qabbrev_tac `q = n DIV m` >> qabbrev_tac `r = n MOD m` >>
  markerLib.RM_ALL_ABBREVS_TAC >> rw[] >>
  qspec_then `2` (qspec_then `q` strip_assume_tac o
                  SIMP_RULE bool_ss [DECIDE ``0n < 2``])
                 arithmeticTheory.DIVISION >>
  qabbrev_tac `q0 = q DIV 2` >> qabbrev_tac `rq = q MOD 2` >>
  markerLib.RM_ALL_ABBREVS_TAC >> rw[] >>
  `rq = 0 ∨ rq = 1` by simp[] >> simp[]
  >- (asm_simp_tac (bool_ss ++ numSimps.MOD_ss)
                   [arithmeticTheory.MULT_ASSOC,
                    DECIDE ``0n < 2 * m ⇔ 0 < m``] >>
      simp[]) >>
  simp[arithmeticTheory.LEFT_ADD_DISTRIB] >>
  asm_simp_tac (bool_ss ++ numSimps.MOD_ss)
     [arithmeticTheory.MULT_ASSOC, DECIDE ``0n < 2 * m ⇔ 0 < m``] >>
  simp[]);

val ZERO_LEQ_N2W = store_thm(
  "ZERO_LEQ_N2W[simp]",
  ``0w:'a word ≤ n2w n ⇔ n MOD (dimword(:'a)) ≤ INT_MAX(:'a)``,
  simp_tac bool_ss [wordsTheory.word_le_n2w, LET_THM, bitTheory.BIT_ZERO,
                    wordsTheory.ZERO_LT_dimword, arithmeticTheory.ZERO_MOD,
                    arithmeticTheory.ZERO_LESS_EQ] >>
  simp[] >>
  qabbrev_tac `N = dimindex(:α) - 1` >>
  simp[bitTheory.SUC_SUB, wordsTheory.dimword_def] >>
  qabbrev_tac `M = 2 EXP N` >>
  `0 < M` by simp[Abbr`M`] >>
  `2 ** dimindex (:'a) = 2 * M`
    by (simp[Abbr`M`, Abbr`N`] >>
        Cases_on `dimindex(:'a)` >-
          (MP_TAC wordsTheory.DIMINDEX_GT_0 >>
           asm_simp_tac bool_ss [DECIDE ``x:num < x ⇔ F``]) >>
        simp[arithmeticTheory.EXP]) >>
  simp[EVEN_SEGMENTS, wordsTheory.INT_MAX_def])

val ZERO_LT_N2W = store_thm(
  "ZERO_LT_N2W",
  ``0w:'a word < n2w n ⇔
      0 < n MOD dimword(:'a) ∧ n MOD dimword(:'a) ≤ INT_MAX(:'a)``,
  simp_tac bool_ss [wordsTheory.word_lt_n2w, LET_THM,
                    wordsTheory.ZERO_LT_dimword, arithmeticTheory.ZERO_MOD] >>
  simp_tac bool_ss [wordsTheory.dimword_def, bitTheory.BIT_ZERO] >>
  simp[] >>
  qabbrev_tac `N = dimindex(:'a) - 1` >>
  simp[wordsTheory.INT_MAX_def, bitTheory.SUC_SUB] >>
  qabbrev_tac `M = 2 EXP N` >>
  `2 ** dimindex (:'a) = 2 * M`
    by (simp[Abbr`M`, Abbr`N`] >>
        Cases_on `dimindex(:'a)` >-
          (MP_TAC wordsTheory.DIMINDEX_GT_0 >>
           asm_simp_tac bool_ss [DECIDE ``x:num < x ⇔ F``]) >>
        simp[arithmeticTheory.EXP]) >> simp[] >>
  `0 < M` by simp[Abbr`M`] >> simp[EVEN_SEGMENTS] >> metis_tac[]);

val seq32_geq_plus_num = store_thm(
  "seq32_geq_plus_num[simp]",
  ``!(s:'a seq32) (n:num). (s + n >= s) = (n MOD 4294967296 < 2147483648)``,
  REPEAT GEN_TAC THEN Cases_on `s` THEN
  SRW_TAC [][seq32_geq_def, seq32_plus_def, seq32_diff_def,
             w2i_n2w_pos, wordsTheory.word_le_n2w, LET_THM] >> DECIDE_TAC);

val seq32_lt_add_lcancel = store_thm(
  "seq32_lt_add_lcancel",
  ``!(s:'a seq32) n m. (s + n < s + m) <=> w2i (n2w n - n2w m : word32) < 0``,
  REPEAT GEN_TAC THEN Cases_on `s` THEN
  SRW_TAC [][seq32_diff_def, seq32_plus_def, seq32_lt_def,
             wordsTheory.WORD_SUB_PLUS]);
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
  Q.ISPEC_THEN `w` (Q.X_CHOOSE_THEN `m` SUBST_ALL_TAC)
              wordsTheory.word_nchotomy THEN
  Q.EXISTS_TAC `m MOD 4294967296` THEN
  SRW_TAC [][arithmeticTheory.DIVISION]);

val NOT_LESS = arithmeticTheory.NOT_LESS
val NOT_LESS_EQ = arithmeticTheory.NOT_LESS_EQUAL

local
open arithmeticTheory
val SUB_RIGHT_ADD' = prove(
  ``x - y + (z : num) = if y <= x then x + z - y else z``,
  DECIDE_TAC);

val mod_add_lemma = prove(
  ``0 < c ==> (x MOD c = (x + c) MOD c)``,
  STRIP_TAC THEN
  IMP_RES_THEN
    (fn th => ONCE_REWRITE_TAC [GSYM th]) bitTheory.MOD_PLUS_RIGHT THEN
  SRW_TAC [][]);

val mod_sub_lemma = prove(
  ``0 < c /\ y <= x ==> ((x - y) MOD c = (x MOD c + (c - y MOD c)) MOD c)``,
  STRIP_TAC THEN
  Q.SPEC_THEN `c` MP_TAC arithmeticTheory.DIVISION THEN ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fn th =>
                 (MAP_EVERY (fn q => Q.SPEC_THEN q STRIP_ASSUME_TAC th)
                            [`x`,`y`])) THEN
  Q.ABBREV_TAC `q = y DIV c` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = y MOD c` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `s = x DIV c` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `t = x MOD c` THEN POP_ASSUM (K ALL_TAC) THEN
  ASM_REWRITE_TAC [arithmeticTheory.SUB_PLUS] THEN
  `q * c <= s * c`
      by (SRW_TAC [ARITH_ss][LE_MULT_RCANCEL] THEN
          SPOSE_NOT_THEN ASSUME_TAC THEN
          `s + 1 <= q` by DECIDE_TAC THEN
          `(s + 1) * c <= q * c`
             by SRW_TAC [ARITH_ss][LE_MULT_RCANCEL] THEN
          `s * c + t < q * c`
             by (FULL_SIMP_TAC bool_ss [RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN
                 DECIDE_TAC) THEN
          DECIDE_TAC) THEN
  `r <= (s - q) * c + t` by DECIDE_TAC THEN
  `s * c + t - q * c = (s - q) * c + t`
     by ASM_SIMP_TAC bool_ss [RIGHT_SUB_DISTRIB, SUB_RIGHT_ADD'] THEN
  `((s-q)*c + t - r) MOD c = ((s-q)*c + t - r + c) MOD c`
      by PROVE_TAC [mod_add_lemma] THEN
  `(s - q) * c + t - r + c = (s - q) * c + (t + (c - r))`
      by ASM_SIMP_TAC bool_ss
           [SUB_RIGHT_ADD',
            DECIDE ``r < (z:num) ==>
                          ((x:num) + y + z - r = x + (y + (z - r)))``] THEN
  ASM_SIMP_TAC bool_ss [MOD_TIMES]);
in
val WORD_SUB_EQN = store_thm(
  "WORD_SUB_EQN",
  ``n2w y - n2w x : word32 =
      if x <= y then n2w (y - x)
      else n2w (y MOD 4294967296 + 4294967296 - x MOD 4294967296)``,
  `!x y c. 0 < c ==> ((x MOD c + y) MOD c = (x + y) MOD c)`
     by METIS_TAC [arithmeticTheory.MOD_PLUS, arithmeticTheory.MOD_MOD] THEN
  `(2 ** 32 = 4294967296n) /\ 0 < 4294967296n` by SRW_TAC [][] THEN
  `SUC 31 = 32` by SRW_TAC [][] THEN COND_CASES_TAC THEN1
     (SRW_TAC[][wordsTheory.n2w_sub]) THEN
  ASM_SIMP_TAC (srw_ss()) [wordsTheory.word_sub_def, wordsTheory.n2w_11,
                           mod_sub_lemma, wordsTheory.word_2comp_n2w,
                           wordsTheory.word_add_n2w] THEN
  Q_TAC SUFF_TAC `x MOD 4294967296n <= 4294967296n`
        THEN1 METIS_TAC [arithmeticTheory.LESS_EQ_ADD_SUB] THEN
  SRW_TAC [][arithmeticTheory.DIVISION, arithmeticTheory.LESS_OR_EQ]);

end (* local *)


val seq32_add_num_sub = store_thm(
  "seq32_add_num_sub",
  ``(!x:'a. x = ARB) /\ (s2 >= s1:'a seq32) ==>
    (s1 + Num(s2 - s1) = s2)``,
  Cases_on `s1` THEN Cases_on `s2` THEN
  SRW_TAC [][seq32_geq_def, seq32_diff_def, seq32_plus_def] THEN
  qcase_tac `w1 - w2 : word32` THEN
  Q.SPEC_THEN `w1` (Q.X_CHOOSE_THEN `n` STRIP_ASSUME_TAC)
              strong_word_nchotomy THEN
  Q.SPEC_THEN `w2` (Q.X_CHOOSE_THEN `m` STRIP_ASSUME_TAC)
              strong_word_nchotomy THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [WORD_SUB_EQN] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `n - m < 2147483648` THENL [
      FULL_SIMP_TAC (srw_ss()) [w2i_n2w_pos] THEN SRW_TAC [ARITH_ss][],
      FULL_SIMP_TAC (srw_ss()) [] >>
      `n - m < 4294967296n` by DECIDE_TAC >> fs[] >>
      simp[]
    ],
    `n + 4294967296n - m < 4294967296n` by DECIDE_TAC >>
    fs[] >>
    simp[w2i_n2w_pos] >> asm_simp_tac (srw_ss() ++ numSimps.MOD_ss) []
  ]);

val w2i_n2w_0_leq = store_thm(
  "w2i_n2w_0_leq",
  ``n1 < 4294967296 /\ n2 < 4294967296 /\ 0 <= w2i (n2w (n1 - n2) :word32) ==>
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
  qspec_then `s1`
    (qx_choosel_then [`a1`, `w1`] SUBST_ALL_TAC) seq32_nchotomy >>
  qspec_then `s2`
    (qx_choosel_then [`a2`, `w2`] SUBST_ALL_TAC) seq32_nchotomy >>
  SIMP_TAC (srw_ss()) [seq32_lt_def, seq32_geq_def, seq32_plus_def,
                       seq32_diff_def] THEN
  Q.ISPEC_THEN `w1` (Q.X_CHOOSE_THEN `j` STRIP_ASSUME_TAC)
              strong_word_nchotomy THEN
  Q.ISPEC_THEN `w2` (Q.X_CHOOSE_THEN `i` STRIP_ASSUME_TAC)
              strong_word_nchotomy THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `i <= j` THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
    REPEAT STRIP_TAC THEN
    `w2i (n2w j - n2w i : word32) =
      w2i (n2w (j - i) : word32)` by SRW_TAC [][WORD_SUB_EQN] THEN
    simp[] THEN
    `j - i < 2147483648` by METIS_TAC [w2i_n2w_0_leq, ZEROI_LEQ_W2I] THEN
    `j - i < n` suffices_by simp[w2in2w1] THEN
    Q_TAC SUFF_TAC `j < i + n` THEN1 DECIDE_TAC THEN
    SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
    `j - (i + n) < 2147483648` by DECIDE_TAC THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2i_n2w_pos, WORD_SUB_EQN],

    FULL_SIMP_TAC (srw_ss()) [NOT_LESS_EQ] THEN
    `w2i (n2w j - n2w i : word32) = w2i (n2w (j + 4294967296 - i) : word32)`
       by SRW_TAC [ARITH_ss][WORD_SUB_EQN] THEN simp[] >>
    strip_tac >>
    `0 ≤ w2i (n2w j - n2w i : word32)` by simp[] >>
    first_x_assum SUBST_ALL_TAC >>
    `j + 2147483648 < i`
       by (SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
           `2147483648 <= j + 4294967296 - i /\
            j + 4294967296 - i < 4294967296` by DECIDE_TAC THEN
           FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2i_n2w_neg]) THEN
    Q.PAT_ASSUM `0 <= w2i (n2w X)` (K ALL_TAC) THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2i_n2w_pos] THEN
    REPEAT VAR_EQ_TAC THEN
    `0 < n`
       by (SPOSE_NOT_THEN (ASSUME_TAC o SIMP_RULE (srw_ss()) [NOT_LESS]) THEN
           Q.PAT_ASSUM `w2i x < 0` MP_TAC THEN
           ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [WORD_SUB_EQN] THEN
           ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2i_n2w_pos]) THEN
    ASM_REWRITE_TAC [] THEN
    Q.PAT_ASSUM `w2i x < 0` MP_TAC THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [WORD_SUB_EQN] THEN
    Cases_on `j + 4294967296 - (i + n) MOD 4294967296 < 2147483648` THEN1
          simp[w2i_n2w_pos] THEN
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
           `w2i (n2w (j + 4294967296 - N) : word32) =
             w2i (n2w (j - N) : word32)`
              by SRW_TAC [][] THEN
           `_ = (&)(j - N)` by simp[w2i_n2w_pos] THEN
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
  SRW_TAC [][seq32_diff_def, w2i_n2w_pos]);
val _ = export_rewrites ["seq32_gt_refl"]

val seq32_add_assoc = store_thm(
  "seq32_add_assoc",
  ``((x : 'a seq32) + y:num) + z = x + (y + z)``,
  Cases_on `x` THEN
  SRW_TAC [][seq32_plus_def, GSYM wordsTheory.WORD_ADD_ASSOC]);

val seq32_sub_id = store_thm(
  "seq32_sub_id",
  ``(x:'a seq32) - x = 0``,
  Cases_on `x` THEN
  SRW_TAC [][seq32_diff_def, w2i_n2w_pos]);
val _ = export_rewrites ["seq32_sub_id"]

val seq32_lt_Num_diff_imp = store_thm(
  "seq32_lt_Num_diff_imp",
  ``s1 >= s2 /\ n < Num(s1:'a seq32 - s2) ==> s2 + n < s1``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  Cases_on `n1 = n2` THEN1
    SRW_TAC [WORD32_ss][TCP1_baseTypesTheory.seq32_lt_def,
                        TCP1_baseTypesTheory.seq32_diff_def,
                        TCP1_baseTypesTheory.seq32_plus_def,
                        w2in2w1, WORD_SUB_EQN] THEN
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
  Cases_on `n1 = n2` THEN1
    SRW_TAC [][TCP1_baseTypesTheory.seq32_lt_def,
               TCP1_baseTypesTheory.seq32_diff_def,
               TCP1_baseTypesTheory.seq32_plus_def,
               w2in2w1, WORD_SUB_EQN] >>
  SRW_TAC [][TCP1_baseTypesTheory.seq32_diff_def,
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
                         [w2in2w2, int_ge, INT_LE_SUB_LADD]) THEN
    FULL_SIMP_TAC (srw_ss()) [w2in2w1, int_ge] THEN
    `n2 + n < 4294967296` by DECIDE_TAC THEN
    `n2 + n + 4294967296 - n1 < 4294967296 /\
     2147483648 <= n2 + n + 4294967296 - n1` by DECIDE_TAC THEN
    simp[w2in2w2, INT_LT_SUB_RADD],

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
         by SRW_TAC [][arithmeticTheory.SUB_MOD] THEN
      `n2 + n - n1 - 4294967296 < 2147483648` by DECIDE_TAC THEN
      simp[w2in2w1],
      simp[w2in2w1,w2in2w2]
    ],

    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val seq32_leq_geq = store_thm(
  "seq32_leq_geq",
  ``-2147483648 < s1 - s2  ==> (s1:'a seq32 >= s2) = (s2 <= s1)``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  ASM_SIMP_TAC (srw_ss()) [seq32_geq_def, seq32_leq_def, seq32_diff_def] THEN
  Cases_on `n1 = n2` >- simp[w2in2w1, int_ge] >>
  SRW_TAC [][WORD_SUB_EQN] THENL [
    PROVE_TAC [arithmeticTheory.LESS_EQUAL_ANTISYM],

    Cases_on `n1 - n2 < 2147483648` THENL [
      ASM_SIMP_TAC (srw_ss()) [w2in2w1, int_ge] THEN
      `n2 + 4294967296 - n1 < 4294967296` by DECIDE_TAC THEN
      `2147483648 <= n2 + 4294967296 - n1` by DECIDE_TAC THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)
                   [w2in2w2, INT_LE_SUB_RADD],
      `w2i (n2w (n1 - n2) : word32) = -(4294967296 - (&)(n1 - n2))`
         by (simp[w2in2w2, GSYM integerTheory.INT_SUB,
                  GSYM integerTheory.INT_ADD] >>
             intLib.ARITH_TAC) >>
      FULL_SIMP_TAC (srw_ss()) [] THEN
      simp[w2in2w1]
    ],

    Cases_on `n2 - n1 < 2147483648` THENL [
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1, w2in2w2],
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2] THEN
      `n1 + 4294967296 - n2 < 2147483648`
         by (SPOSE_NOT_THEN (ASSUME_TAC o
                             REWRITE_RULE [NOT_LESS]) THEN
             `w2i (n2w (n1 + 4294967296 - n2) : word32) =
                  ~(4294967296 - (&)(n1 + 4294967296 - n2))`
                by (simp[w2in2w2, GSYM integerTheory.INT_SUB,
                         GSYM integerTheory.INT_ADD] >> intLib.ARITH_TAC) >>
             FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []) THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []
    ],

    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val seq32_sub_bounded = store_thm(
  "seq32_sub_bounded",
  ``(s1:'a seq32) <= s2 /\ s2 < s1 + n /\ 0 < n /\ n < 2147483648n ==>
    -2147483648 < s2 - s1``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [][WORD_SUB_EQN, seq32_diff_def, seq32_leq_def,
             seq32_lt_def, seq32_plus_def]
  THENL [
    `n1 = n2` by DECIDE_TAC THEN SRW_TAC [][w2in2w1],
    `n2 + 4294967296 - n1 < 4294967296` by DECIDE_TAC THEN
    Cases_on `n2 + 4294967296 - n1 < 2147483648` THENL [
      simp[w2in2w1],
      simp[w2in2w2, INT_LT_SUB_LADD]
    ],
    `n1 = n2` by DECIDE_TAC THEN SRW_TAC [][w2in2w1],
    `n2 + 4294967296 - n1 < 4294967296` by DECIDE_TAC THEN
    Cases_on `n2 + 4294967296 - n1 < 2147483648` THENL [
      simp[w2in2w1],
      simp[w2in2w2] THEN
      `n1 ≠ n2 + 2147483648` suffices_by DECIDE_TAC THEN
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
      simp[w2in2w1],
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w2] THEN
      Q_TAC SUFF_TAC `~(n2 = n1 + 2147483648)` THEN1 DECIDE_TAC THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1]
    ],

    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    Cases_on `n2 - n1 < 2147483648` THENL [
      simp[w2in2w1],
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
        `(w2i (n2w n1 - n2w n2 : word32) > 0 /\ w2i (n2w n1 - n2w n2 : word32) < 0) = F`
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
  Cases_on `n1 = n2` >-
    SRW_TAC [ARITH_ss][WORD_SUB_EQN, seq32_diff_def, seq32_plus_def,
                       seq32_geq_def, seq32_gt_def, w2in2w1] >>
  STRIP_TAC THEN
  `w2i (n2w (n2 + n) : word32 - n2w n1) > 0`
     suffices_by SRW_TAC [][seq32_gt_def, seq32_plus_def, seq32_diff_def] >>
  `w2i (n2w (n2 + n - n1) : word32) > 0` suffices_by
       (simp[WORD_SUB_EQN] >> rw[] >> pop_assum mp_tac >>
        `n + n2 - n1 = 0` by simp[] >> simp[word_0_w2i]) >>
  `s1 - s2 >= 0` by FULL_SIMP_TAC (srw_ss())[seq32_geq_def] THEN
  `w2i (n2w n1 - n2w n2 : word32) >= 0`
     by (SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [seq32_diff_def]) THEN
  Cases_on `n2 <= n1` THENL [
    `n2w n1 - n2w n2 = n2w (n1 - n2) : word32` by SRW_TAC [][WORD_SUB_EQN] THEN
    `(n1 - n2) MOD 4294967296 < 2147483648`
       by (FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] >>
           `n1 - n2 < 4294967296` by simp[] >> fs[]>> simp[]) >>
    `n1 - n2 < 4294967296` by DECIDE_TAC THEN
    `n1 - n2 < 2147483648` by FULL_SIMP_TAC (srw_ss()) [] THEN
    `n1 - n2 < n` by (SRW_TAC [][] THEN
                      FULL_SIMP_TAC (srw_ss()) [seq32_diff_def, w2in2w1]) THEN
    `n2 + n - n1 < 4294967296` by DECIDE_TAC THEN
    SRW_TAC [ARITH_ss][w2in2w1],

    `n1 < n2` by DECIDE_TAC THEN
    `n1 + 4294967296 - n2 < 4294967296` by DECIDE_TAC THEN
    `n2w n1 - n2w n2 = n2w (n1 + 4294967296 - n2) : word32`
       by SRW_TAC [][WORD_SUB_EQN] THEN
    `n1 + 4294967296 - n2 < 2147483648`
       by FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
    `s1 - s2 = w2i (n2w (n1 + 4294967296 - n2) : word32)`
       by FULL_SIMP_TAC (srw_ss()) [seq32_diff_def, WORD_SUB_EQN] THEN
    ` _ = int_of_num (n1 + 4294967296 - n2)` by simp[w2in2w1] THEN
    `n1 + 4294967296 - n2 < n` by FULL_SIMP_TAC (srw_ss()) [] THEN
    `4294967296 < n2 + n - n1` by DECIDE_TAC THEN
    `n2 + n - n1 < 4294967296 + 2147483648` by DECIDE_TAC THEN
    `(n2 + n - n1) MOD 4294967296 = n2 + n - n1 - 4294967296`
       by intLib.ARITH_TAC THEN
    Q.ABBREV_TAC `bigN = n2 + n - n1` THEN
    `n2w bigN : word32 = n2w (bigN MOD 4294967296)` by simp[] >>
    simp[w2in2w1]
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
    w2i (n2w (n1 + 4294967296 - n2) : word32) < 0 ==>
    2147483648 <= n1 + 4294967296 - n2``,
  STRIP_TAC THEN
  SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [NOT_LESS_EQ]) THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [w2in2w1]);

val w2i_n2w_0_leq2 = store_thm(
  "w2i_n2w_0_leq2",
  ``n1 < 4294967296 /\ n2 < 4294967296 /\ n1 < n2 /\
    0 <= w2i (n2w (n1 + 4294967296 - n2) : word32) ==>
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

val w2i_eq0 = store_thm(
  "w2i_eq0[simp]",
  ``((w2i w = 0) ⇔ (w = 0w)) ∧ ((0 = w2i w) ⇔ (w = 0w))``,
  simp[w2i_def, EQ_IMP_THM] >> rw[]);

val ZEROLT_W2I = store_thm(
  "ZEROLT_W2I",
  ``0 < w2i w ⇔ 0w < w``,
  eq_tac >> strip_tac
  >- (`0 ≤ w2i w` by intLib.ARITH_TAC >>
      `0w ≤ w` by metis_tac[ZEROI_LEQ_W2I] >>
      fs[wordsTheory.WORD_LESS_OR_EQ] >> rw[] >>
      fs[word_0_w2i]) >>
  `0w ≤ w` by metis_tac[wordsTheory.WORD_LESS_OR_EQ] >>
  `0 ≤ w2i w` by metis_tac[ZEROI_LEQ_W2I] >>
  full_simp_tac bool_ss [integerTheory.INT_LE_LT] >>
  fs[wordsTheory.WORD_LESS_REFL]);

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
           WORD_SUB_EQN]
  THENL [
    `n1 = n2` by simp[] >> fs[word_0_w2i],
    fs[ZEROLT_W2I, ZERO_LT_N2W] >>
    `n1 - n2 < 4294967296` by simp[] >> fs[] >>
    simp[w2in2w2],
    fs[ZEROLT_W2I, ZERO_LT_N2W] >>
    `n1 + 4294967296 - n2 < 4294967296` by simp[] >> fs[] >>
    simp[w2in2w2],
    full_simp_tac (srw_ss() ++ ARITH_ss)[]
  ]);

val seq32_geq_disj = store_thm(
  "seq32_geq_disj",
  ``(!x:'a. x = ARB) ==> ((s1:'a seq32 >= s2) = ((s1 = s2) \/ (s1 > s2)))``,
  `(?w1 a1. s1 = SEQ32 a1 w1) /\ (?w2 a2. s2 = SEQ32 a2 w2)`
      by PROVE_TAC [seq32_nchotomy] THEN
  `(?n1. n1 < 4294967296 /\ w1 = n2w n1) /\
   (?n2. n2 < 4294967296 /\ w2 = n2w n2)`
      by PROVE_TAC [strong_word_nchotomy] THEN
  SRW_TAC [ARITH_ss]
          [seq32_gt_def, seq32_geq_def, seq32_diff_def, WORD_SUB_EQN,
           ZEROLT_W2I, ZERO_LT_N2W]);

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
  SRW_TAC [][seq32_plus'_def, seq32_plus_def, integer_wordTheory.i2w_def]);
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
      Cases_on `w2i (n2w n2 : word32) < 0` THEN ASM_REWRITE_TAC [] THEN
      `2147483648 <= n2` by
          (SPOSE_NOT_THEN ASSUME_TAC THEN
           `w2i (n2w n2 : word32) = (&)n2`
              by SRW_TAC [ARITH_ss][w2i_n2w_pos] THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
      SRW_TAC [ARITH_ss][w2i_n2w_pos],
      ASM_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `w2i (n2w (n2 + 4294967296 - (n1 + 1)) : word32) < 0` THEN
      ASM_REWRITE_TAC [] THEN
      `2147483648 <= n2 + 4294967296 - (n1 + 1)`
         by SRW_TAC [ARITH_ss][w2i_n2w_lt0] THEN
      `n1 - n2 < 2147483648` by DECIDE_TAC THEN
      simp[w2i_n2w_pos]
    ],
    Cases_on `w2i (n2w (n1 + 4294967296 - n2) : word32) < 0` THEN
    ASM_REWRITE_TAC [] THEN
    `2147483648 <= n1 + 4294967296 - n2`
       by SRW_TAC [ARITH_ss][w2i_n2w_lt0] THEN
    `n2 - (n1 + 1) < 2147483648` by DECIDE_TAC THEN
    SRW_TAC [ARITH_ss][w2i_n2w_pos],
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)[]
  ]);

val _ = export_theory()
