open HolKernel boolLib Parse bossLib

open finite_mapTheory

val _ = new_theory "fmapUtils"

val Punique_range_def = Define`
  Punique_range (P : 'b -> bool) (fm : 'a |-> 'b) : ('a # 'b) option =
    if ?!k. k IN FDOM fm /\ P (fm ' k) then
      SOME (@p. FST p IN FDOM fm /\ (fm ' (FST p) = SND p) /\ P (fm ' (FST p)))
    else
      NONE
`

val Puniq_alt_def = Define`
  Puniq_alt P acc fm =
    if ?k. k IN FDOM fm /\ P (fm ' k) then
      case acc of
         NONE -> if ?!k. k IN FDOM fm /\ P (fm ' k) then
                   SOME (@p. FST p IN FDOM fm /\ (SND p = fm ' (FST p)) /\
                             P (fm ' (FST p)))
                 else NONE
      || SOME _ -> NONE
    else acc
`;

val Puniq_alt_rwt = store_thm(
  "Puniq_alt_rwt",
  ``(Puniq_alt P acc FEMPTY = acc) /\
    (Puniq_alt P acc (fm |+ (k,v)) =
       if P v then
         case acc of
           NONE -> Puniq_alt P (SOME(k,v)) (fm \\ k)
        || SOME _ -> NONE
       else Puniq_alt P acc (fm \\ k))``,
  CONJ_TAC THEN1 SRW_TAC [][Puniq_alt_def, EXISTS_UNIQUE_DEF] THEN
  Cases_on `P v` THEN SRW_TAC [][] THENL [
    Cases_on `acc` THEN SRW_TAC [][] THENL [
      REWRITE_TAC [Puniq_alt_def] THEN SRW_TAC [][] THENL [
        METIS_TAC [DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM],
        METIS_TAC [DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM],

        SELECT_ELIM_TAC THEN
        SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss)
                 [pairTheory.EXISTS_PROD, pairTheory.FORALL_PROD] THEN
        DISJ1_TAC THEN ASM_REWRITE_TAC [] THEN
        METIS_TAC [DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM],

        SELECT_ELIM_TAC THEN
        SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss)
                 [pairTheory.EXISTS_PROD, pairTheory.FORALL_PROD] THEN
        DISJ1_TAC THEN ASM_REWRITE_TAC [] THEN
        METIS_TAC [DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM],

        (* METIS_TAC bug  -
             METIS_TAC [FAPPLY_FUPDATE_THM,
                        DOMSUB_FAPPLY_THM] returns an invalid tactic *)
        FULL_SIMP_TAC bool_ss [EXISTS_UNIQUE_DEF] THEN
        METIS_TAC [FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM],

        FULL_SIMP_TAC bool_ss [EXISTS_UNIQUE_DEF] THEN
        METIS_TAC [FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM],

        METIS_TAC [FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM]
      ],
      REWRITE_TAC [Puniq_alt_def] THEN SRW_TAC [][] THEN
      METIS_TAC [FAPPLY_FUPDATE_THM]
    ],
    Cases_on `acc` THEN SRW_TAC [][Puniq_alt_def] THENL [
      FULL_SIMP_TAC (srw_ss()) [],

      AP_TERM_TAC THEN SRW_TAC [][FUN_EQ_THM] THEN
      Cases_on `FST p = k` THEN
      SRW_TAC [][DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM],

      FULL_SIMP_TAC (srw_ss()) [],

      METIS_TAC [DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM, EXISTS_UNIQUE_DEF],

      FULL_SIMP_TAC (srw_ss()) [],

      METIS_TAC [DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM],

      FULL_SIMP_TAC (srw_ss()) [],

      METIS_TAC [DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM],
      METIS_TAC [DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM],
      FULL_SIMP_TAC (srw_ss()) [],
      METIS_TAC [DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM],
      METIS_TAC [DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM]
    ]
  ]);
val _ = BasicProvers.export_rewrites ["Puniq_alt_rwt"]


val Puniq_alt_Puniq = store_thm(
  "Puniq_alt_Puniq",
  ``Punique_range P fm = Puniq_alt P NONE fm``,
  SRW_TAC [][Punique_range_def, Puniq_alt_def] THENL [
    AP_TERM_TAC THEN SRW_TAC [][FUN_EQ_THM] THEN METIS_TAC [],
    METIS_TAC []
  ]);
val _ = BasicProvers.export_rewrites ["Puniq_alt_Puniq"]

val _ = export_theory ()
