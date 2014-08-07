(* A HOL98 specification of TCP *)
(* this file is a theory about the relationships between integers and 32-bit
   words  *)
(*[ RCSID "$Id: integer_word32Script.sml,v 1.1 2005/07/12 15:53:17 tjr22 Exp $" ]*)

open HolKernel Parse boolLib

open word32Theory integerTheory

open bossLib

val _ = new_theory "integer_word32";

val _ = Version.registerTheory "$RCSfile: integer_word32Script.sml,v $" "$Revision: 1.1 $" "$Date: 2005/07/12 15:53:17 $";

val ARITH_ss = numSimps.ARITH_ss

val mod_add_lemma = prove(
  ``0 < c ==> (x MOD c = (x + c) MOD c)``,
  STRIP_TAC THEN
  IMP_RES_THEN
    (fn th => ONCE_REWRITE_TAC [GSYM th]) bitsTheory.MOD_PLUS_RIGHT THEN
  SRW_TAC [][]);

open arithmeticTheory
val SUB_RIGHT_ADD' = prove(
  ``x - y + (z : num) = if y <= x then x + z - y else z``,
  DECIDE_TAC);

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
                                (x + y + z - r = x + (y + (z - r)))``] THEN
  ASM_SIMP_TAC bool_ss [MOD_TIMES]);

val WORD_SUB_EQN = store_thm(
  "WORD_SUB_EQN",
  ``n2w y - n2w x : word32 =
      if x <= y then n2w (y - x)
      else n2w (y MOD 4294967296 + 4294967296 - x MOD 4294967296)``,
  `!x y c. 0 < c ==> ((x MOD c + y) MOD c = (x + y) MOD c)`
     by METIS_TAC [arithmeticTheory.MOD_PLUS, arithmeticTheory.MOD_MOD] THEN
  `(2 ** 32 = 4294967296n) /\ 0 < 4294967296n` by SRW_TAC [][] THEN
  `SUC 31 = 32` by SRW_TAC [][] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [word_sub, TWO_COMP_EVAL, ADD_EVAL, n2w_11,
                           MOD_WL_def, WL_def, HB_def, TWO_COMP_def,
                           mod_sub_lemma] THEN
  Q_TAC SUFF_TAC `x MOD 4294967296n <= 4294967296n`
        THEN1 METIS_TAC [arithmeticTheory.LESS_EQ_ADD_SUB] THEN
  SRW_TAC [][arithmeticTheory.DIVISION, arithmeticTheory.LESS_OR_EQ]);

(* -------------------------------------------------- *)
(*                   WORD32                           *)
(* -------------------------------------------------- *)

(* conversion between 2's-complement word32 and integer: *)

val i2w_def = Define`
  i2w (i:int) = if i < 0 then word_2comp (n2w (Num ~i)) else n2w (Num i)
`;

val w2i_def = Define`
  w2i (w:word32) = if MSB w then
                     ~(int_of_num (w2n (word_2comp w)))
                   else int_of_num (w2n w)
`;

val INT32_SIGNED_MAX_def = Phase.phase 1 Define`
  INT32_SIGNED_MAX = word32$n2w 2147483647
`;

open bitsTheory
val THE_WL = SIMP_RULE arith_ss [HB_def,arithmeticTheory.ADD1] WL_def;
val MSB_EVAL2 = GEN_ALL (REWRITE_RULE [MSBn_def,HB_def] MSB_EVAL);
val TWO_COMP_EVAL2 = GEN_ALL (SIMP_RULE arith_ss [TWO_COMP_def,THE_WL]
                                        TWO_COMP_EVAL);


val w2i_n2w_1 = store_thm(
  "w2i_n2w_1",
  ``x < 2147483648 ==> (w2i (n2w x) = int_of_num x)``,
  SRW_TAC [ARITH_ss][w2i_def, w2n_EVAL, MOD_WL_def, WL_def, HB_def] THEN
  FULL_SIMP_TAC (srw_ss()) [MSB_EVAL2, BIT_def, BITS_def, MOD_2EXP_def,
                            DIV_2EXP_def] THEN
  FULL_SIMP_TAC (srw_ss()) [LESS_DIV_EQ_ZERO]);

val w2i_n2w_2 = store_thm(
  "w2i_n2w_2",
  ``2147483648 <= x /\ x < 4294967296 ==>
    (w2i (n2w x) = ~(4294967296 - int_of_num x))``,
  SRW_TAC [][w2i_def, w2n_EVAL, MOD_WL_def, WL_def, HB_def] THENL [
    SRW_TAC [ARITH_ss]
            [TWO_COMP_EVAL2, w2n_EVAL, MOD_WL_def, WL_def, HB_def] THEN
    SRW_TAC [ARITH_ss][GSYM integerTheory.INT_SUB],
    FULL_SIMP_TAC (srw_ss()) [MSB_EVAL2, BIT_def, BITS_def, MOD_2EXP_def,
                              DIV_2EXP_def] THEN
    Q_TAC SUFF_TAC `x DIV 2147483648 = 1` THEN1
          (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
    MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `x - 2147483648` THEN
    DECIDE_TAC
  ]);


val _ = export_theory()
