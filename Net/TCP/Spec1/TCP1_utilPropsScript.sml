(* A HOL98 specification of TCP *)

(* Proofs of properties of various utility definitions *)

(*[ RCSID "$Id: TCP1_utilPropsScript.sml,v 1.3 2006/02/09 08:59:04 mn200 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse

open bossLib

open HolDoc

local open arithmeticTheory stringTheory pred_setTheory integerTheory
           finite_mapTheory realTheory word16Theory word32Theory
           containerTheory in end;

val _ = new_theory "TCP1_utilProps";

val _ = BasicProvers.augment_srw_ss [rewrites [LET_THM]]

val _ = Version.registerTheory "$RCSfile: TCP1_utilPropsScript.sml,v $" "$Revision: 1.3 $" "$Date: 2006/02/09 08:59:04 $";

open TCP1_utilsTheory

val fm_exists_thm = store_thm(
  "fm_exists_thm",
  ``(fm_exists FEMPTY P = F) /\
    (fm_exists (fm |+ (k,v)) P = (P (k,v) \/ fm_exists (fm \\ k) P))``,
  SIMP_TAC (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.DNF_ss)
          [fm_exists_def, finite_mapTheory.FAPPLY_FUPDATE_THM,
           finite_mapTheory.DOMSUB_FAPPLY_THM, EQ_IMP_THM] THEN
  PROVE_TAC []);
val _ = Phase.add_to_phase 1 "fm_exists_thm"

val _ = augment_srw_ss [rewrites [pairTheory.UNCURRY]]

val SND_SPLIT_REV_0_EQ_nil = store_thm(
  "SND_SPLIT_REV_0_EQ_NIL",
  ``!n x y. (SND (SPLIT_REV_0 n x y) = []) = LENGTH y <= n``,
  Induct THENL [
    RW_TAC list_ss [SPLIT_REV_0_def] THEN
    Cases_on `y` THEN RW_TAC list_ss [],
    Cases_on `y` THEN RW_TAC list_ss [SPLIT_REV_0_def]
  ]);
val _ = BasicProvers.export_rewrites ["SND_SPLIT_REV_0_EQ_NIL"]

val SPLIT_REV_2ND = prove(
  ``!n x y. SND (SPLIT_REV_0 n x y) = SND (SPLIT_REV_0 n [] y)``,
  Induct THEN SRW_TAC [][SPLIT_REV_0_def] THEN
  Cases_on `y` THEN SRW_TAC [][SPLIT_REV_0_def]);

val SPLIT_REV_1ST = prove(
  ``!n x y. FST (SPLIT_REV_0 n x y) = APPEND (FST (SPLIT_REV_0 n [] y)) x``,
  Induct THEN SRW_TAC [][SPLIT_REV_0_def] THEN
  Cases_on `y` THENL [
    SRW_TAC [][SPLIT_REV_0_def],
    SIMP_TAC (srw_ss()) [SPLIT_REV_0_def] THEN
    ONCE_ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
  ]);

val TAKE_lemma = prove(
  ``TAKE 0 x = [] /\ TAKE n [] = [] /\
    (!n. TAKE (SUC n) (h::t) = h :: TAKE n t)``,
  SRW_TAC [][TAKE_def, SPLIT_REV_def, SPLIT_REV_0_def] THENL [
    Cases_on `n` THEN SRW_TAC [][SPLIT_REV_0_def],
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [SPLIT_REV_1ST])) THEN
    SRW_TAC [][listTheory.REVERSE_APPEND]
  ]);

val TAKE_THM = save_thm(
  "TAKE_THM",
  CONJ TAKE_lemma
       (CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV
                  (last (CONJUNCTS TAKE_lemma))))
val _ = Phase.add_to_phase 1 "TAKE_THM";

val DROP_lemma = prove(
  ``DROP 0 x = x /\ DROP n [] = [] /\
    !n. DROP (SUC n) (h :: t) = DROP n t``,
  SRW_TAC [][DROP_def, SPLIT_REV_def, SPLIT_REV_0_def] THEN
  MATCH_ACCEPT_TAC SPLIT_REV_2ND);

val DROP_THM = save_thm(
  "DROP_THM",
  CONJ DROP_lemma
       (CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV
                  (last (CONJUNCTS DROP_lemma))))
val _ = Phase.add_to_phase 1 "DROP_THM";

val SPLIT_THM = store_thm(
  "SPLIT_THM",
  ``SPLIT n l = (TAKE n l, DROP n l)``,
  SRW_TAC [][SPLIT_def, SPLIT_REV_def, SPLIT_REV_0_def, DROP_def, TAKE_def]);
val _ = Phase.add_to_phase 1 "SPLIT_THM";

val DROP_EQ_NIL = store_thm(
  "DROP_EQ_NIL",
  ``(DROP n l = []) = LENGTH l <= n``,
  SRW_TAC [][DROP_def, SPLIT_REV_def]);
val _ = Phase.add_to_phase 1 "DROP_EQ_NIL";

val TAKE_ALL = store_thm(
  "TAKE_ALL",
  ``!n l. (TAKE n l = l) = LENGTH l <= n``,
  Induct THENL[
    SIMP_TAC (srw_ss()) [TAKE_THM, listTheory.LENGTH_NIL] THEN PROVE_TAC [],
    Cases_on `l` THEN SRW_TAC [][TAKE_THM]
  ]);
val _ = Phase.add_to_phase 1 "TAKE_ALL";

val TAKE_ALL_IMPLICATION = save_thm(
  "TAKE_ALL_IMPLICATION",
  #2 (CONJ_PAIR (SIMP_RULE (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] TAKE_ALL)))
val _ = Phase.add_to_phase 1 "TAKE_ALL_IMPLICATION";

val num_floor_and_frac_thm = store_thm(
  "num_floor_and_frac_thm",
  ``num_floor_and_frac x = let n = num_floor x in (n, x - real_of_num n)``,
  SIMP_TAC bool_ss [num_floor_def, num_floor_and_frac_def]);
val _ = Phase.add_to_phase 1 "num_floor_and_frac_thm"

val ORDERINGS_THM = store_thm(
  "ORDERINGS_THM",
  ``ORDERINGS {} = {[]} /\
    ORDERINGS {x} = {[x]} /\
    (~(x = y) ==> ORDERINGS {x;y} = {[x;y]; [y;x]})``,
  SRW_TAC [][pred_setTheory.EXTENSION, ORDERINGS_def,
             pred_setTheory.SPECIFICATION, EQ_IMP_THM,
             listTheory.LENGTH_NIL] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  POP_ASSUM MP_TAC THEN
  `x' = [] \/ ?h t. x' = h::t` by PROVE_TAC [listTheory.list_CASES] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  SIMP_TAC (srw_ss()) [listTheory.LENGTH_NIL] THENL [
    PROVE_TAC [listTheory.MEM],
    ALL_TAC
  ] THEN
  Cases_on `t` THEN SIMP_TAC (srw_ss()) [listTheory.LENGTH_NIL] THEN
  metisLib.METIS_TAC [listTheory.MEM]);
val _ = Phase.add_to_phase 1 "ORDERINGS_THM"




val _ = export_theory();
