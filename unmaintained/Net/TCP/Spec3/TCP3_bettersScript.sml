open HolKernel boolLib bossLib Parse BasicProvers

local open TCP3_hostLTSTheory in end;

open finite_mapTheory pred_setTheory

val _ = new_theory "TCP3_betters";
val _ = remove_ovl_mapping "fmap_every"
                           {Name = "fmap_every", Thy = "TCP1_hostLTS"}

val _ = remove_ovl_mapping "fmap_every_pred"
                           {Name = "fmap_every_pred", Thy = "TCP1_hostLTS"}

fun Store_thm(n,t,tac) = (store_thm(n,t,tac) before export_rewrites [n])

val better_fmap_every = Store_thm(
  "better_fmap_every",
  ``(fmap_every f FEMPTY = SOME FEMPTY) /\
    (fmap_every f (fm |+ (k,v)) =
        case f v of
           NONE -> NONE
        || SOME v' -> (case fmap_every f (fm \\ k) of
                          NONE -> NONE
                       || SOME fm' -> SOME (fm' |+ (k,v'))))``,
  SRW_TAC [][TCP3_hostLTSTheory.fmap_every_def, LET_THM] THENL [
    Cases_on `f v` THEN SRW_TAC [][],
    Cases_on `f v` THEN SRW_TAC [][],
    Cases_on `f v` THEN SRW_TAC [][],
    METIS_TAC [],
    Cases_on `f v` THEN SRW_TAC [][]
  ]);

val better_fmap_every_pred = Store_thm(
  "better_fmap_every_pred",
  ``(fmap_every_pred f FEMPTY = SOME {FEMPTY}) /\
    (fmap_every_pred f (fm |+ (k,v)) =
        case f v of
           NONE -> NONE
        || SOME s -> (case fmap_every_pred f (fm \\ k) of
                         NONE -> NONE
                      || SOME fms -> SOME (IMAGE (\ (fm,v). (fm |+ (k,v)))
                                                 (fms CROSS s))))``,
  SRW_TAC [][TCP3_hostLTSTheory.fmap_every_pred_def] THEN
  SRW_TAC [][] THENL [
    SRW_TAC [][Once pred_setTheory.EXTENSION] THEN
    METIS_TAC [FDOM_EQ_EMPTY],

    Cases_on `f v` THEN SRW_TAC [][],

    METIS_TAC [],

    METIS_TAC [],

    FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][DISJ_IMP_THM, FORALL_AND_THM] THEN
    Cases_on `f v` THEN1 METIS_TAC [] THEN
    `!y. y IN FRANGE (fm \\ k) ==> ?z. f y = SOME z`
       by METIS_TAC [TypeBase.nchotomy_of ``:'a option``] THEN
    SRW_TAC [][] THEN
    SRW_TAC [][finite_mapTheory.FAPPLY_FUPDATE_THM,
               finite_mapTheory.DOMSUB_FAPPLY_THM] THEN
    SRW_TAC [boolSimps.COND_elim_ss][] THEN
    SRW_TAC [][IMP_CONJ_THM, FORALL_AND_THM] THEN
    SRW_TAC [][Once pred_setTheory.EXTENSION, EQ_IMP_THM] THENL [
      Q.EXISTS_TAC `(x' \\ k, x' ' k)` THEN SRW_TAC [][] THEN
      SRW_TAC [][] THENL [
        SRW_TAC [][fmap_EXT, pred_setTheory.EXTENSION] THEN
        SRW_TAC [][EQ_IMP_THM] THENL [
          FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN
          METIS_TAC [],
          SRW_TAC [][finite_mapTheory.FAPPLY_FUPDATE_THM,
                     finite_mapTheory.DOMSUB_FAPPLY_THM]
        ],

        SRW_TAC [][pred_setTheory.EXTENSION, EQ_IMP_THM] THEN
        FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN METIS_TAC [],

        METIS_TAC [finite_mapTheory.DOMSUB_FAPPLY_THM]
      ],

      Cases_on `x''` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN
      METIS_TAC [],

      Cases_on `x''` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [],

      Cases_on `x''` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [],

      Cases_on `x''` THEN SRW_TAC [][] THEN
      Cases_on `x'''=k` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.FAPPLY_FUPDATE_THM]
    ]
  ]);

val _ = remove_ovl_mapping "bound_ports_protocol_autobind"
                           {Name = "bound_ports_protocol_autobind",
                            Thy = "TCP1_auxFns"}


val better_bound_ports_protocol_autobind = Store_thm(
  "better_bound_ports_protocol_autobind",
  ``bound_ports_protocol_autobind pr FEMPTY = {} /\
    bound_ports_protocol_autobind pr (socks |+ (sid, s)) =
      case s.ps1 of
         NONE -> bound_ports_protocol_autobind pr (socks \\ sid)
      || SOME p -> if proto_of s.pr = pr then
                     p INSERT bound_ports_protocol_autobind pr (socks \\ sid)
                   else bound_ports_protocol_autobind pr (socks \\ sid)``,
  SRW_TAC [][TCP3_auxFnsTheory.bound_ports_protocol_autobind_def] THEN
  Cases_on `s.ps1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [boolSimps.DNF_ss][] THEN
  SRW_TAC [][EXTENSION] THEN PROVE_TAC []);

val stream_reass_easy_case = Store_thm(
  "stream_reass_easy_case",
  ``stream_reass x {} = []``,
  SRW_TAC [][TCP3_absFunTheory.stream_reass_def] THEN
  `myrel = (\x. F)`
     by (SRW_TAC [][Abbr`myrel`, pred_setTheory.EXTENSION] THEN
         SRW_TAC [][IN_DEF]) THEN
  Q_TAC SUFF_TAC `cs = {[]}` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][Abbr`cs`, IN_DEF] THEN
  SRW_TAC [][pred_setTheory.EXTENSION, EQ_IMP_THM] THEN
  Cases_on `x` THEN SRW_TAC [][] THEN
  POP_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN SRW_TAC [][]);


val fakefundel_def = Define`
  fakefundel f k = (\e. if e = k then ARB else f e)
`;

val funupd_same_key = Store_thm(
  "funupd_same_key",
  ``(funupd f1 k v1 = funupd f2 k v2) =
      (v1 = v2 /\ fakefundel f1 k = fakefundel f2 k)``,
  SRW_TAC [][TCP1_utilsTheory.funupd_def, fakefundel_def, EQ_IMP_THM,
             FUN_EQ_THM] THEN
  METIS_TAC []);

val fakefundel_funupd = store_thm(
  "fakefundel_funupd",
  ``fakefundel (funupd f k1 v) k2 =
       if k1 = k2 then fakefundel f k2
       else funupd (fakefundel f k2) k1 v``,
  SRW_TAC [][FUN_EQ_THM, TCP1_utilsTheory.funupd_def, fakefundel_def] THEN
  METIS_TAC [])
val _ = Phase.add_to_phase 2 "fakefundel_funupd"

val fakefundel_comm = Store_thm(
  "fakefundel_comm",
  ``fakefundel (fakefundel f k1) k2 = fakefundel (fakefundel f k2) k1``,
  SRW_TAC [][fakefundel_def] THEN METIS_TAC []);


val _ = export_theory();
