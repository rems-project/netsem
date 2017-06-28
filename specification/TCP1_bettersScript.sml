(* A HOL98 specification of TCP *)

(* Rewrite theorems derived from those automatically inferred, but
   better suited to symbolic evaluation of the specification.  Also
   some other useful theorems. *)

(*[ RCSID "$Id: TCP1_bettersScript.sml,v 1.84 2007/06/14 07:33:12 mn200 Exp $" ]*)

open HolKernel boolLib Parse

val _ = new_theory "TCP1_betters";

structure Q = struct open Q open OldAbbrevTactics end


(* an explanation of what the heck is going on with what are now three
   "post - LTS" files:

     NetEval          : contains the munged LTS relation
     TCP1_evalSupport : contains definitions of constants specifically
                        needed for evaluation
     TCP1_betters     : contains rewrite theorems better suited to
                        rewriting than the originals, and other helpful
                        bits and pieces.
*)

open BasicProvers bossLib

local open TCP1_evalSupportTheory in end;

open TCP1_paramsTheory TCP1_auxFnsTheory TCP1_hostLTSTheory TCP1_preHostTypesTheory
open finite_mapTheory pred_setTheory
open TCP1_seq32PropsTheory

open HolDoc metisLib

val WORD_SUB_EQN = TCP1_seq32PropsTheory.WORD_SUB_EQN

val _ = print "Some 1-1 properties from TCP1_hostTypes\n"
(* useful to know that the File "constructor" is injective *)
val File_11 = store_thm(
  "File_11",
  ``!p q. (File p = File q) = (p = q)``,
  SIMP_TAC (srw_ss()) [TCP1_paramsTheory.file_component_equality,
                       TCP1_paramsTheory.File_def,
                       pairTheory.FORALL_PROD]);
val _ = BasicProvers.export_rewrites ["File_11"];


val Sock_11 = store_thm(
  "Sock_11",
  ``!p q. (Sock p = Sock q) = (p = q)``,
  SIMP_TAC (srw_ss()) [TCP1_hostTypesTheory.Sock_def, pairTheory.FORALL_PROD,
                       TCP1_hostTypesTheory.socket_component_equality,
                       CONJ_ASSOC]);
val _ = BasicProvers.export_rewrites ["Sock_11"];

val _ = print "Now proving various \"better\" versions of some definitions\n";

fun p1store_thm (nm,g,tac) = store_thm(nm, g, tac) before
			     Phase.add_to_phase 1 nm

val better_nextfd = p1store_thm(
  "better_nextfd",
  ``nextfd WinXP_Prof_SP1 map fd = ~(fd IN FDOM map) /\
    nextfd FreeBSD_4_6_RELEASE map fd = (fd = leastfd fd. ~(fd IN FDOM map)) /\
    nextfd Linux_2_4_20_8 map fd = (fd = leastfd fd. ~(fd IN FDOM map))``,
  SRW_TAC [][windows_arch_def, nextfd_def]);

val better_local_ips = p1store_thm(
  "better_local_ips",
  ``local_ips (f |+ (k, r)) = r.ipset UNION local_ips (f \\ k) /\
    local_ips FEMPTY = {}``,
  SRW_TAC [][local_ips_def] THEN
  ONCE_REWRITE_TAC [EXTENSION] THEN
  SRW_TAC [][] THEN PROVE_TAC []);

val _ = augment_srw_ss [rewrites [LET_THM]]
val better_outroute_ifids = p1store_thm(
  "better_outroute_ifids",
  ``outroute_ifids (i2, []) = [] /\
    outroute_ifids (i2, (rte::rtes)) =
      let nm = rte.destination_netmask
      in
          APPEND (if mask nm i2 = mask nm rte.destination_ip
                  then [rte.ifid] else []) (outroute_ifids (i2, rtes))``,
  BasicProvers.SRW_TAC [][TCP1_preHostTypesTheory.outroute_ifids_def,
                          TCP1_preHostTypesTheory.routeable_def,
                          TCP1_utilsTheory.MAP_OPTIONAL_def]);

val better_is_localnet = p1store_thm(
  "better_is_localnet",
  ``is_localnet FEMPTY i = F /\
    is_localnet (fm |+ (k, v)) i =
       let m = v.netmask
       in
           mask m i = mask m v.primary \/ is_localnet (fm \\ k) i``,
  BasicProvers.SRW_TAC [][TCP1_preHostTypesTheory.is_localnet_def,
                          RIGHT_AND_OVER_OR, EXISTS_OR_THM]);



val better_dequeue = p1store_thm(
  "better_dequeue",
  ``dequeue dq (Timed([],d), q', msg) = (q' = Timed([], d) /\ msg = NONE) /\
    dequeue dq (Timed([v], d), q', msg) =
       (msg = SOME v /\ q' = Timed([], never_timer)) /\
    dequeue dq (Timed(v1::v2::vs, d), q', msg) =
       (msg = SOME v1 /\ q' = Timed(v2::vs, dq))``,
  Cases_on `q'` THEN
  Cases_on `p` THEN
  BasicProvers.SRW_TAC [][TCP1_preHostTypesTheory.dequeue_def] THEN
  BasicProvers.SRW_TAC [][EQ_IMP_THM])

val better_enqueue = store_thm(
  "better_enqueue",
  ``enqueue dq (Timed (q,d), msg, q', queued) =
      ((INFINITE_RESOURCES ==> queued) /\
       (q' = Timed(if queued then (APPEND q [msg], dq) else (q,d))))``,
  Cases_on `q'` THEN
  Cases_on `p` THEN
  BasicProvers.SRW_TAC [][TCP1_preHostTypesTheory.enqueue_def])


val better_in_local = p1store_thm(
  "better_in_local",
  ``in_local FEMPTY i = in_loopback i /\
    in_local (fm |+ (k, v)) i = (i IN v.ipset \/ in_local (fm \\ k) i)``,
  SRW_TAC [boolSimps.DNF_ss][TCP1_preHostTypesTheory.in_local_def] THEN
  PROVE_TAC [])


val WORD32_ss =
    rewrites [bitTheory.BIT_def, bitTheory.BITS_def,
              bitTheory.MOD_2EXP_def, bitTheory.DIV_2EXP_def,
              wordsTheory.n2w_11, wordsTheory.w2n_11,
              wordsTheory.WORD_NEG_NEG,
              wordsTheory.WORD_SUB_REFL,
              wordsTheory.word_0,
              wordsTheory.INT_MIN_def,
              wordsTheory.dimword_32,
              wordsTheory.dimindex_32,
              REWRITE_RULE [wordsTheory.word_0] wordsTheory.WORD_NEG_EQ_0]


val tcp_ARB = store_thm(
  "tcp_ARB",
  ``(x : tcpForeign = TcpForeign) /\
    (y : tcpLocal = TcpLocal)``,
  SRW_TAC [][TypeBase.nchotomy_of ``:tcpForeign``,
             TypeBase.nchotomy_of ``:tcpLocal``])

val LET_ELIM = prove(``bool$LET f v = !x. (v = x) ==> f x``, SRW_TAC [][])




val number_skip_def = Phase.phase 1 Define`
  (number_skip (c:num) skip [] = []) /\
  (number_skip c skip (h::t) =
     if SOME c = skip then (c+1, h) :: number_skip (c + 2) skip t
     else (c, h) :: number_skip (c + 1) skip t)
`;

val MEM_number_skip = store_thm(
  "MEM_number_skip",
  ``!l x c skip.
        MEM x (number_skip c skip l) =
        ?n. c <= n /\
            case skip of
              NONE => (x = (n, EL (n - c) l)) /\ n - c < LENGTH l
            | SOME m => ((m < c \/ n < m) /\ (x = (n, EL (n - c) l)) /\
                         n - c < LENGTH l) \/
                        (m < n /\ c <= m /\
                         (x = (n, EL (n - c - 1) l)) /\
                         n - c - 1 < LENGTH l)``,
  Induct THEN Cases_on `skip` THEN SRW_TAC [][number_skip_def] THEN
  FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl)) THENL [
    SRW_TAC [numSimps.ARITH_ss, boolSimps.CONJ_ss][EQ_IMP_THM] THENL [
      `n - c = SUC (n - (c + 1))` by DECIDE_TAC THEN
      SRW_TAC [][],
      Cases_on `n = c` THEN1 ASM_REWRITE_TAC [] THEN
      `n - c = SUC (n - (c + 1))` by DECIDE_TAC THEN
      SRW_TAC [numSimps.ARITH_ss][]
    ],
    SRW_TAC [][EQ_IMP_THM]THENL [
      SRW_TAC [numSimps.ARITH_ss, boolSimps.CONJ_ss][],
      SRW_TAC [numSimps.ARITH_ss, boolSimps.CONJ_ss][] THEN
      `n - (c + 1) = SUC (n - (c + 2))` by DECIDE_TAC THEN
      SRW_TAC [][],
      FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [],
      FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [],
      SRW_TAC [numSimps.ARITH_ss, boolSimps.CONJ_ss][] THEN
      Cases_on `n = c + 1` THEN ASM_REWRITE_TAC [] THEN
      `n - (c + 1) = SUC (n - (c + 2))` by DECIDE_TAC THEN
      SRW_TAC [numSimps.ARITH_ss][]
    ],
    SRW_TAC [][EQ_IMP_THM] THENL [
      Q.EXISTS_TAC `c` THEN SRW_TAC [numSimps.ARITH_ss][],
      Q.EXISTS_TAC `n` THEN
      `n - c = SUC (n - (c + 1))` by DECIDE_TAC THEN
      SRW_TAC [numSimps.ARITH_ss][],
      Q.EXISTS_TAC `n` THEN
      `n - c = SUC (n - (c + 1))` by DECIDE_TAC THEN
      SRW_TAC [numSimps.ARITH_ss][],
      Q.EXISTS_TAC `n` THEN
      Q_TAC SUFF_TAC `n - c - 1 = SUC (n - (c + 1) - 1)` THEN1
        (SRW_TAC [][] THENL [
           MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS THEN
           Q.EXISTS_TAC `c + 1` THEN ASM_REWRITE_TAC [] THEN
           SIMP_TAC (srw_ss()) [],
           POP_ASSUM (K ALL_TAC) THEN DISJ2_TAC THEN
           DECIDE_TAC
         ]) THEN
      `n - c - 1 = n - (c + 1)` by DECIDE_TAC THEN
      POP_ASSUM SUBST_ALL_TAC THEN DECIDE_TAC,
      Cases_on `n = c` THEN SRW_TAC [][] THEN
      Q.EXISTS_TAC `n` THEN
      `n - c = SUC (n - (c + 1))` by DECIDE_TAC THEN
      SRW_TAC [][] THENL [
        DECIDE_TAC,
        DISJ1_TAC THEN POP_ASSUM (K ALL_TAC) THEN DECIDE_TAC
      ],
      Cases_on `n = c` THEN SRW_TAC [][] THEN
      Q.EXISTS_TAC `n` THEN
      `n - c = SUC (n - (c + 1))` by DECIDE_TAC THEN
      SRW_TAC [][] THENL [
        DECIDE_TAC,
        DISJ1_TAC THEN DECIDE_TAC
      ],
      Cases_on `n = c` THEN SRW_TAC [][] THEN
      Q.EXISTS_TAC `n` THEN SRW_TAC [][] THENL [
        DECIDE_TAC,
        DISJ2_TAC THEN
        `n - c - 1 = n - (c + 1)` by DECIDE_TAC THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        Q_TAC SUFF_TAC `n - (c + 1) = SUC (n - (c + 1) - 1)` THEN1
           (DISCH_THEN SUBST_ALL_TAC THEN SRW_TAC [][] THEN
            DECIDE_TAC) THEN
        DECIDE_TAC
      ]
    ]
  ]);

val MEM_nskip0 = save_thm(
  "MEM_nskip0",
  SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) []
            (Q.INST [`c` |-> `0`] (SPEC_ALL MEM_number_skip)))





(* is this right? K: yes. *)
val wf_reass_def = Phase.phase 1 Define`
  wf_reass s = case s.spliced_urp of
                 NONE => LENGTH s.data < 2147483648
               | SOME n => n >= s.seq /\ n < s.seq + LENGTH s.data + 1n /\
                           LENGTH s.data < 2147483647
`;

val tcp_reass_myrel = prove(
  ``EVERY wf_reass rsegq ==>
    {(i,c) |
       (?rseg. rseg IN' rsegq /\ i >= rseg.seq /\
               i < rseg.seq + LENGTH rseg.data +
                   (if rseg.spliced_urp <> NONE then 1i else 0) /\
               case rseg.spliced_urp of
                  NONE => c = SOME (EL (Num (i - rseg.seq)) rseg.data)
                | SOME v => if i > v then
                              c = SOME (EL (Num (i - rseg.seq - 1)) rseg.data)
                            else if i = v then c = NONE
                            else
                              c = SOME (EL (Num(i - rseg.seq)) rseg.data))} =
    FOLDL
      (\s sq. s UNION
              (case sq.spliced_urp of
                  SOME n => if sq.seq <= n /\
                               n < sq.seq + LENGTH sq.data + 1n
                            then {(n,NONE)} else {}
                | NONE => {}) UNION
              LIST_TO_SET
                    (MAP (λ(n,e). (sq.seq + n, SOME e))
                         (number_skip 0 (OPTION_MAP (\x. Num(x - sq.seq))
                                                    sq.spliced_urp)
                                      sq.data))) {} rsegq``,
  Q.ABBREV_TAC
    `setcomprel =
        \i c rseg q. rseg IN' q /\ i >= rseg.seq /\
                     i < rseg.seq + LENGTH rseg.data +
                         (if rseg.spliced_urp <> NONE then 1i else 0) /\
                     case rseg.spliced_urp of
                        NONE => c = SOME (EL (Num(i - rseg.seq)) rseg.data)
                      | SOME v => if i > v then
                                    c = SOME (EL(Num(i - rseg.seq - 1))
                                                rseg.data)
                                  else if i = v then c = NONE
                                  else c = SOME (EL(Num(i - rseg.seq))
                                                   rseg.data)` THEN
  POP_ASSUM (ASSUME_TAC o SIMP_RULE bool_ss [FUN_EQ_THM]) THEN
  `(!i c rseg q. setcomprel i c rseg q ==> !h. setcomprel i c rseg (h::q)) /\
   (!i c rseg q. ~(setcomprel i c rseg []))`
      by (POP_ASSUM (ASSUME_TAC o GSYM) THEN SRW_TAC [][]) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  Q_TAC SUFF_TAC
    `!rsegq X.
        EVERY wf_reass rsegq ==>
        (FOLDL
           (\s sq.
              s UNION
              (case sq.spliced_urp of
                  NONE => {}
                | SOME v => if sq.seq <= v /\
                               v < sq.seq + LENGTH sq.data + 1n
                            then {(v,NONE)} else {}) UNION
              LIST_TO_SET
                     (MAP (λ(n,e). (sq.seq + n, SOME e))
                          (number_skip 0 (OPTION_MAP (\x. Num(x - sq.seq))
                                                     sq.spliced_urp)
                                       sq.data)))
           X rsegq =
         X UNION {(i,c) | ?rseg. setcomprel i c rseg rsegq})`
    THEN1 SIMP_TAC (srw_ss()) [] THEN
  Induct THENL [
    SRW_TAC [][pred_setTheory.EXTENSION],

    ASM_SIMP_TAC (srw_ss()) [GSYM containerTheory.UNION_APPEND,
                             wf_reass_def] THEN
    POP_ASSUM (K ALL_TAC) THEN
    ASM_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION, EQ_IMP_THM,
                             listTheory.MEM_MAP] THEN
    REPEAT STRIP_TAC THENL [
      ASM_REWRITE_TAC [],

      POP_ASSUM MP_TAC THEN Cases_on `h.spliced_urp` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      DISJ2_TAC THEN Q.EXISTS_TAC `h` THEN
      Q.PAT_X_ASSUM `!i c rseg q. X = setcomprel i c rseg q`
                  (ASSUME_TAC o GSYM) THEN
      ASM_SIMP_TAC (srw_ss()) [],

      POP_ASSUM MP_TAC THEN
      Cases_on `h.spliced_urp` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][MEM_nskip0] THEN SRW_TAC [][] THEN DISJ2_TAC THEN
      Q.EXISTS_TAC `h` THEN
      Q.PAT_X_ASSUM `!i c rseg q. X = setcomprel i c rseg q`
                  (ASSUME_TAC o GSYM) THEN
      ASM_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss)
                   [seq32_leq_plus_num, arithmeticTheory.LESS_MOD,
                    seq32_add_num_minus, seq32_lt_add_lcancel] THEN
      FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl)) THENL [
        SRW_TAC [numSimps.ARITH_ss][WORD_SUB_EQN] THEN
        SRW_TAC [numSimps.ARITH_ss, WORD32_ss]
                [integer_wordTheory.w2i_n2w_neg,
                 integerTheory.INT_LT_SUB_RADD],

        FULL_SIMP_TAC (srw_ss()) [] THEN CONJ_TAC THENL [
          SRW_TAC [][seq32_add_assoc] THEN
          SRW_TAC [numSimps.ARITH_ss][WORD_SUB_EQN] THEN
          SRW_TAC [numSimps.ARITH_ss, WORD32_ss]
                  [integer_wordTheory.w2i_n2w_neg,
                   integerTheory.INT_LT_SUB_RADD],

          `h.seq + n < x'`
             by ASM_SIMP_TAC (srw_ss()) [seq32_lt_Num_diff_imp] THEN
          `~(h.seq + n > x')` by PROVE_TAC [seq32_lt_gt_incompatible] THEN
          ASM_SIMP_TAC (srw_ss()) [] THEN
          DISCH_THEN SUBST_ALL_TAC THEN
          FULL_SIMP_TAC (srw_ss()) []
        ],

        ASM_SIMP_TAC (srw_ss() ++ WORD32_ss ++ ARITH_ss)
                     [seq32_add_assoc, WORD_SUB_EQN,
                      integer_wordTheory.w2i_n2w_neg,
                      integerTheory.INT_LT_SUB_RADD] THEN
        `n < 2147483648` by DECIDE_TAC THEN
        `LENGTH h.data < 2147483648` by DECIDE_TAC THEN
        `h.seq + n > x'` by PROVE_TAC [seq32_Num_diff_lt_imp] THEN
        `int_of_num n - 1 = int_of_num (n - 1)`
           by SRW_TAC [ARITH_ss][integerTheory.INT_SUB] THEN
        `Num(int_of_num(n - 1)) = n - 1`
           by SRW_TAC [ARITH_ss][integerTheory.INT_OF_NUM] THEN
        ASM_SIMP_TAC (srw_ss()) []
      ],

      PROVE_TAC [],
      ASM_REWRITE_TAC [],
      Q.PAT_X_ASSUM `setcomprel VV XX YY ZZ` MP_TAC THEN
      Q.PAT_X_ASSUM `!i c rseg q. XX = setcomprel i c rseg q`
                  (ASSUME_TAC o GSYM) THEN
      ASM_SIMP_TAC (srw_ss()) [] THEN STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (K ALL_TAC o assert(is_forall o concl))) THENL [
        DISJ1_TAC THEN VAR_EQ_TAC THEN
        Cases_on `h.spliced_urp` THEN
        FULL_SIMP_TAC (srw_ss()) [] THENL [
          DISJ2_TAC THEN
          Q.EXISTS_TAC `(Num(i - h.seq),EL(Num(i - h.seq)) h.data)` THEN
          SRW_TAC [][seq32_add_num_sub, tcp_ARB, seq32_num_sub_lt,
                     MEM_nskip0] THEN
          Q_TAC SUFF_TAC `~(LENGTH h.data = 0)` THEN1 DECIDE_TAC THEN
          DISCH_THEN SUBST_ALL_TAC THEN
          FULL_SIMP_TAC (srw_ss()) [] THEN
          PROVE_TAC [tcp_ARB, seq32_geq_disj, seq32_lt_gt_incompatible,
                     seq32_lt_refl],

          `i < h.seq + (LENGTH h.data + 1)`
            by SRW_TAC [][GSYM seq32_add_assoc] THEN
          `LENGTH h.data + 1 < 2147483648 /\ LENGTH h.data < 2147483648`
            by DECIDE_TAC THEN
          Cases_on `i > x'` THENL [
            FULL_SIMP_TAC (srw_ss()) [] THEN
            SIMP_TAC (srw_ss()) [pairTheory.EXISTS_PROD] THEN
            DISJ2_TAC THEN Q.EXISTS_TAC `Num(i - h.seq)` THEN
            SRW_TAC [][MEM_nskip0, tcp_ARB, seq32_add_num_sub,
                       EXISTS_OR_THM, seq32_num_sub_lt,
                       seq32_Num_sub_lt_monotone, seq32_gt_imp_lt] THEN
            DISJ2_TAC THEN
            `0 < LENGTH h.data`
               by (Q_TAC SUFF_TAC `~(LENGTH h.data = 0)` THEN1 DECIDE_TAC THEN
                   DISCH_THEN SUBST_ALL_TAC THEN
                   FULL_SIMP_TAC (srw_ss()) [] THEN
                   PROVE_TAC [tcp_ARB, seq32_geq_disj, seq32_lt_discrete,
                              seq32_gt_imp_lt, seq32_lt_gt_incompatible,
                              seq32_lt_refl]) THEN
            Q_TAC SUFF_TAC `Num(i - h.seq - 1) = Num(i - h.seq) - 1` THEN1
                  SRW_TAC [][] THEN
            Q_TAC SUFF_TAC `int_of_num(Num(i - h.seq - 1)) =
                            int_of_num(Num(i - h.seq) - 1)` THEN1
                  SRW_TAC [][] THEN
            Q_TAC SUFF_TAC `1 <= i - h.seq` THEN1
                  (STRIP_TAC THEN
                   `0 <= i - h.seq - 1 /\ 0 <= i - h.seq`
                      by intLib.ARITH_TAC THEN
                   `(int_of_num(Num(i - h.seq - 1)) = i - h.seq - 1) /\
                    (int_of_num(Num(i - h.seq)) = i - h.seq)`
                       by ASM_SIMP_TAC bool_ss [integerTheory.INT_OF_NUM] THEN
                   ASM_REWRITE_TAC [] THEN
                   `1 <= Num (i - h.seq)`
                       by (Q_TAC SUFF_TAC `1 <= int_of_num(Num(i - h.seq))`
                                 THEN1 SRW_TAC [][] THEN
                           ASM_REWRITE_TAC []) THEN
                   Q_TAC SUFF_TAC
                         `int_of_num(Num(i - h.seq) - 1) = i - h.seq - 1`
                         THEN1 SRW_TAC [][] THEN
                   ASM_SIMP_TAC bool_ss [GSYM integerTheory.INT_SUB]) THEN
            `0 <= i - h.seq` by PROVE_TAC [seq32_geq_diff_bounds] THEN
            Q_TAC SUFF_TAC `~(i - h.seq = 0)` THEN1 intLib.ARITH_TAC THEN
            SRW_TAC [][seq32_sub_eq0, tcp_ARB] THEN
            STRIP_TAC THEN VAR_EQ_TAC THEN
            PROVE_TAC [seq32_geq_disj, tcp_ARB, seq32_gt_antisym,
                       seq32_gt_refl],
            FULL_SIMP_TAC (srw_ss()) [] THEN
            Cases_on `i = x'`
              THEN1 FULL_SIMP_TAC (srw_ss()) [seq32_geq_imp_leq] THEN
            `0 < LENGTH h.data`
               by (Q_TAC SUFF_TAC `~(LENGTH h.data = 0)` THEN1 DECIDE_TAC THEN
                   DISCH_THEN SUBST_ALL_TAC THEN
                   FULL_SIMP_TAC (srw_ss()) [] THEN
                   `x' = h.seq /\ i = h.seq`
                      by PROVE_TAC [tcp_ARB, seq32_geq_disj, seq32_lt_discrete,
                                    seq32_gt_imp_lt] THEN
                   PROVE_TAC []) THEN
            FULL_SIMP_TAC (srw_ss()) [] THEN DISJ2_TAC THEN
            SRW_TAC [][pairTheory.EXISTS_PROD, MEM_nskip0, EXISTS_OR_THM] THEN
            Q.EXISTS_TAC `Num(i - h.seq)` THEN
            SRW_TAC [][seq32_add_num_sub, tcp_ARB,
                       seq32_Num_sub_lt_monotone] THEN
            `i < x'` by PROVE_TAC [seq32_not_gt, seq32_leq_disj, tcp_ARB] THEN
            Q_TAC SUFF_TAC `Num(i - h.seq) < LENGTH h.data`
                  THEN1 SRW_TAC [][] THEN
            Q_TAC SUFF_TAC `Num(x' - h.seq) <= LENGTH h.data`
                  THEN1 PROVE_TAC [seq32_Num_sub_lt_monotone,
                                   arithmeticTheory.LESS_LESS_EQ_TRANS] THEN
            Q_TAC SUFF_TAC `Num(x' - h.seq) < LENGTH h.data + 1`
                  THEN1 DECIDE_TAC THEN
            PROVE_TAC [seq32_num_sub_lt, seq32_add_assoc]
          ]
        ],

        METIS_TAC[]
      ]
    ]
  ]);

val better_tcp_reass0 = prove(
  ``EVERY wf_reass rsegq ==>
    tcp_reass seq rsegq =
      let myrel =
        FOLDL
          (\s sq.
              s UNION
              (case sq.spliced_urp of
                  NONE => {}
                | SOME n =>
                    if sq.seq <= n /\ n < sq.seq + LENGTH sq.data + 1n then
                      {(n, NONE)}
                    else {}) UNION
              LIST_TO_SET
                (MAP (λ(n,e). (sq.seq + n, SOME e))
                     (number_skip 0 (OPTION_MAP (\x. Num(x - sq.seq))
                                                sq.spliced_urp) sq.data)))
          {} rsegq
      in
        { (cs',len,FIN) |
             ?cs. cs' = CONCAT_OPTIONAL cs /\
                  (!n:num. n < LENGTH cs ==> (seq+n,EL n cs) IN myrel) /\
                  (~?c. (seq+LENGTH cs,c) IN myrel) /\
                  (len = LENGTH cs) /\
                  FIN = EXISTS (\rseg. rseg.seq + LENGTH rseg.data +
                                         (if rseg.spliced_urp <> NONE then 1
                                          else 0) =
                                       seq + LENGTH cs /\
                                       rseg.FIN) rsegq }``,
  SIMP_TAC bool_ss [TCP1_auxFnsTheory.tcp_reass_def,
                    listTheory.EXISTS_MEM,
                    tcp_reass_myrel] THEN
  SRW_TAC [][]);

val tcp_reass_build_defn = Defn.Hol_defn "tcp_reass_build" `
  tcp_reass_build (s:tcpForeign seq32) (acc:'a list set) cs =
    if ~FINITE cs then {}
    else
      let nexts = cs INTER { p |  FST p = s }  in
      let rest = cs INTER { p | ~(FST p = s) }
      in
          if nexts = {} then acc
          else
            let newacc = IMAGE (\old. IMAGE (\p. APPEND old [SND p]) nexts) acc
            in
              tcp_reass_build (s + 1n) (BIGUNION newacc) rest
`;

val COMPL_GSPEC = prove(
  ``COMPL { x | P x } = { x | ~P x}``,
  SRW_TAC [][EXTENSION]);

val (tcp_reass_build_def, tcp_reass_build_ind) = Defn.tstore_defn(
   tcp_reass_build_defn,
   WF_REL_TAC `measure (\ (n, a, s). CARD s)` THEN
   REPEAT GEN_TAC THEN
   `!P. {(p1: tcp_seq_foreign,p2:'a) | (p1,p2) | P p1 } =
        { p | P (FST p)  }`
      by (SRW_TAC [][EXTENSION] THEN Cases_on `x` THEN
          SRW_TAC [][]) THEN
   ASM_SIMP_TAC (srw_ss()) [] THEN
   Q_TAC SUFF_TAC
         `!P (cs : tcpForeign seq32 # 'a -> bool).
             FINITE cs ==> ~(cs INTER P = {}) ==>
             CARD (cs INTER COMPL P) < CARD cs` THEN1
         (SRW_TAC [][] THEN
          FIRST_X_ASSUM (Q.SPEC_THEN `{ p | FST p = s }`
                                     MP_TAC) THEN
          SRW_TAC [][COMPL_GSPEC]) THEN
   GEN_TAC THEN
   HO_MATCH_MP_TAC FINITE_INDUCT THEN
   SRW_TAC [][INSERT_INTER] THEN
   Cases_on `e IN P` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
   `CARD (cs INTER COMPL P) <= CARD cs` by PROVE_TAC [CARD_INTER_LESS_EQ] THEN
   DECIDE_TAC);

fun ABS_EQ_CONV t = let
  val (l, r) = dest_eq t
  val (lv, lb) = dest_abs l
  val _ = assert is_abs r
in
  FUN_EQ_CONV THENC RAND_CONV (ALPHA_CONV lv) THENC
  BINDER_CONV (BINOP_CONV BETA_CONV)
end t

val ABS_EQ_TAC = CONV_TAC ABS_EQ_CONV THEN GEN_TAC

val _ = augment_srw_ss [WORD32_ss]


val n2w_mod = prove(
  ``n2w (x MOD 4294967296) : word32 = n2w x``,
  SRW_TAC [][]);

val seq_mod = prove(
  ``(s : 'a seq32) + (n MOD 4294967296)  = s + n``,
  Cases_on `s` THEN SRW_TAC [][TCP1_baseTypesTheory.seq32_plus_def,
                               n2w_mod]);

val seq_add_elim = prove(
  ``((s : 'a seq32) + (n:num) = s) = (n MOD 4294967296 = 0)``,
  Cases_on `s` THEN
  SRW_TAC [][TCP1_baseTypesTheory.seq32_plus_def,
             wordsTheory.WORD_ADD_INV_0_EQ, wordsTheory.word_0]);

val build_lemma1 = prove(
  ``!seq A M pfx cs.
         FINITE M /\ (!c. ~((seq + LENGTH cs, c) IN M)) /\
         (!n. n < LENGTH cs ==> (seq + n, EL n cs) IN M) /\
         pfx IN A ==>
         (APPEND pfx cs) IN tcp_reass_build seq A M``,
  HO_MATCH_MP_TAC tcp_reass_build_ind THEN
  SIMP_TAC (srw_ss()) [GSYM RIGHT_EXISTS_AND_THM,
                       GSYM LEFT_EXISTS_AND_THM,
                       GSYM LEFT_FORALL_IMP_THM] THEN
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] THEN
  REPEAT (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC [tcp_reass_build_def] THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  COND_CASES_TAC THENL [
    Q_TAC SUFF_TAC `cs = []` THEN1 SRW_TAC [numSimps.ARITH_ss][] THEN
    Cases_on `cs` THEN SRW_TAC [][] THEN
    `(seq + 0n, EL 0 (h::t)) IN M` by SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `(seq, h) IN { p | FST p = seq }` by SRW_TAC [][] THEN
    `(seq, h) IN M INTER { p | FST p = seq }` by SRW_TAC [][] THEN
    PROVE_TAC [NOT_IN_EMPTY],

    Cases_on `cs` THENL [
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `?e. e IN M INTER {p | FST p = seq}`
          by METIS_TAC [SET_CASES, IN_INSERT] THEN
      POP_ASSUM MP_TAC THEN SIMP_TAC (srw_ss()) [] THEN
      Cases_on `e` THEN SRW_TAC [][] THEN PROVE_TAC [],

      (* cons case *)
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Q.ABBREV_TAC `q = (seq, h)` THEN
      `h = SND q` by SRW_TAC [][] THEN
      POP_ASSUM SUBST1_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      SRW_TAC [][] THENL [
      (* now blow away the conditions on the (specialised) inductive
         hypothesis *)
        Q_TAC SUFF_TAC
              `!c. ~((seq + 1n + LENGTH t, c) IN M)` THEN1 SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1,
                                  seq32_add_assoc,
                                  arithmeticTheory.ADD_COMM],

        FIRST_X_ASSUM (Q.SPEC_THEN `SUC n` MP_TAC) THEN
        SRW_TAC [][arithmeticTheory.ADD1, seq32_add_assoc,
                   arithmeticTheory.ADD_COMM],

        SRW_TAC [][seq32_add_assoc, seq_add_elim] THEN
        Q_TAC SUFF_TAC `n < 4294967295` THEN1
              SRW_TAC [numSimps.ARITH_ss][] THEN
        Q_TAC SUFF_TAC `LENGTH t < 4294967296` THEN1 DECIDE_TAC THEN
        SPOSE_NOT_THEN ASSUME_TAC THEN
        Q.ABBREV_TAC `N = LENGTH t` THEN
        FIRST_X_ASSUM (Q.SPEC_THEN `(SUC N) MOD 4294967296` MP_TAC) THEN
        `SUC N MOD 4294967296 < SUC N`
           by (MATCH_MP_TAC arithmeticTheory.LESS_LESS_EQ_TRANS THEN
               Q.EXISTS_TAC `4294967296` THEN
               SRW_TAC [numSimps.ARITH_ss][arithmeticTheory.DIVISION]) THEN
        ASM_REWRITE_TAC [] THEN
        FULL_SIMP_TAC (srw_ss()) [TCP1_baseTypesTheory.seq32_plus_def,
                                  seq_mod],

        FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
        SRW_TAC [][]
      ]
    ]
  ]);

val CARD_ENUMERATE_LOWER_BOUND = prove(
  ``!s. FINITE s ==>
        !n.  ((n:num) <= CARD s) =
             ?f. (!x y. x < n /\ y < n ==> ((f(x) = f(y)) = (x = y))) /\
                 (!x. x < n ==> f x IN s)``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THENL [
    EQ_TAC THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN DECIDE_TAC,
    EQ_TAC THENL [
      `(n = 0) \/ ?m. n = SUC m`
         by PROVE_TAC [arithmeticTheory.num_CASES] THEN
      SRW_TAC [][] THEN
      Q.EXISTS_TAC `\x. if x = m then e else f x` THEN
      SRW_TAC [][] THENL [
        `y < m` by DECIDE_TAC THEN PROVE_TAC [],
        `x < m` by DECIDE_TAC THEN PROVE_TAC [],
        `x < m /\ y < m` by DECIDE_TAC THEN PROVE_TAC [],
        `x < m` by DECIDE_TAC THEN PROVE_TAC []
      ],
      STRIP_TAC THEN
      Cases_on `?z. z < n /\ (f z = e)` THENL [
        POP_ASSUM STRIP_ASSUME_TAC THEN
        `?m. n = SUC m` by (Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
        Q.ABBREV_TAC `g = \i. if i < m then if i = z then f m else f i
                              else f i` THEN
        `!x y. x < m /\ y < m ==> ((g x = g y) = (x = y))`
            by SRW_TAC [numSimps.ARITH_ss][] THEN
        `!x. x < m ==> g x IN s`
            by (SRW_TAC [][] THEN
                PROVE_TAC [prim_recTheory.LESS_SUC_REFL,
                           prim_recTheory.LESS_REFL,
                           arithmeticTheory.LESS_TRANS]) THEN
        `m <= CARD s` by METIS_TAC [] THEN
        SRW_TAC [][],
        `!x. x < n ==> f x IN s` by PROVE_TAC [] THEN
        RES_TAC THEN
        METIS_TAC [arithmeticTheory.LESS_EQ_SUC_REFL,
                   arithmeticTheory.LESS_EQ_TRANS]
      ]
    ]
  ]);

val CARD_ENUMERATE_UPPER_BOUND = prove(
  ``!s. FINITE s ==>
        !n. (CARD s <= n) =
            (s = {} \/
            ?f. (!x. x < n ==> f x IN s) /\
                (!y. y IN s ==> ?x. x < n /\ (f x = y)))``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN
  `(n = 0) \/ ?m. n = SUC m`
     by PROVE_TAC [arithmeticTheory.num_CASES] THEN1
    SRW_TAC [][EXISTS_OR_THM] THEN
  SRW_TAC [][] THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC `\x. e` THEN SRW_TAC [][] THEN
    PROVE_TAC [prim_recTheory.LESS_0],
    Q.EXISTS_TAC `\x. if x = m then e else f x` THEN
    SRW_TAC [][] THENL [
      `x < m` by DECIDE_TAC THEN PROVE_TAC [],
      PROVE_TAC [prim_recTheory.LESS_SUC_REFL],
      PROVE_TAC [arithmeticTheory.LESS_TRANS, prim_recTheory.LESS_SUC_REFL,
                 prim_recTheory.LESS_REFL]
    ],
    Cases_on `s = {}` THEN SRW_TAC [][] THEN
    `?d. d IN s` by PROVE_TAC [IN_INSERT, SET_CASES] THEN
    Cases_on `f m = e` THENL [
      Q.EXISTS_TAC `\n. if f n = e then d else f n` THEN
      SRW_TAC [][] THENL [
        PROVE_TAC [arithmeticTheory.LESS_TRANS, prim_recTheory.LESS_SUC_REFL],
        `?i. i < SUC m /\ f i = y` by PROVE_TAC [] THEN
        `~(i = m)` by PROVE_TAC [] THEN
        `i < m` by DECIDE_TAC THEN
        Q.EXISTS_TAC `i` THEN SRW_TAC [][] THEN PROVE_TAC []
      ],
      `?i. i < SUC m /\ f i = e` by PROVE_TAC [] THEN
      `~(i = m)` by PROVE_TAC [] THEN
      `i < m` by DECIDE_TAC THEN
      Q.EXISTS_TAC `\x. if f x = e then f m else f x` THEN
      SRW_TAC [][] THENL [
        `m < SUC m` by DECIDE_TAC THEN PROVE_TAC [],
        `x < SUC m` by DECIDE_TAC THEN PROVE_TAC [],
        `?j. j < SUC m /\ f j = y` by PROVE_TAC [] THEN
        `~(f j = f i)` by PROVE_TAC [] THEN
        `j < m \/ (j = m)` by DECIDE_TAC THEN1 PROVE_TAC [] THEN
        Q.EXISTS_TAC `i` THEN SRW_TAC [][]
      ]
    ]
  ]);

val build_lemma2 = prove(
  ``!seq A M.
       FINITE M /\ CARD (IMAGE FST M) < 4294967296 /\
       cs IN tcp_reass_build seq A M ==>
       ?pfx sfx. pfx IN A /\ (cs = APPEND pfx sfx) /\
                 (!n. n < LENGTH sfx ==> (seq + n, EL n sfx) IN M) /\
                 !c. ~((seq + LENGTH sfx, c) IN M)``,
  HO_MATCH_MP_TAC tcp_reass_build_ind THEN
  SIMP_TAC (srw_ss()) [GSYM RIGHT_EXISTS_AND_THM,
                       GSYM LEFT_EXISTS_AND_THM,
                       GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC [tcp_reass_build_def] THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.CONJ_ss) [] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL [
    STRIP_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`cs`, `[]`] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
    PROVE_TAC [pairTheory.FST],

    STRIP_TAC THEN
    Q.ABBREV_TAC `Q = {p:tcpForeign seq32 # 'a | ~(FST p = seq)}` THEN
    `CARD (IMAGE FST (M INTER Q)) < 4294967296`
       by METIS_TAC [CARD_INTER_LESS_EQ, arithmeticTheory.LESS_EQ_LESS_TRANS,
                     INTER_FINITE, IMAGE_FINITE, CARD_SUBSET, IMAGE_INTER] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    MAP_EVERY Q.EXISTS_TAC [`old`, `SND p :: sfx`] THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THENL [
      Cases_on `n` THEN1 SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1, seq32_add_assoc,
                                arithmeticTheory.ADD_COMM],

      FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1, seq32_add_assoc,
                                arithmeticTheory.ADD_COMM] THEN
      `(seq + (LENGTH sfx + 1) = seq)` by METIS_TAC [] THEN
      `(LENGTH sfx + 1) MOD 4294967296 = 0` by METIS_TAC [seq_add_elim] THEN
      `4294967296 <= LENGTH sfx + 1`
         by (SPOSE_NOT_THEN
               (ASSUME_TAC o
                REWRITE_RULE [arithmeticTheory.NOT_LESS_EQUAL]) THEN
             FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) []) THEN
      `4294967294 < LENGTH sfx` by DECIDE_TAC THEN
      Q.ABBREV_TAC `g = \n:num. seq + n` THEN
      `!x y. x < 4294967296 /\ y < 4294967296 ==>
             ((g x = g y) = (x = y))`
         by (Q.UNABBREV_TAC `g` THEN Cases_on `seq` THEN
             SIMP_TAC (srw_ss()) [TCP1_baseTypesTheory.seq32_plus_def,
                                  wordsTheory.WORD_EQ_ADD_LCANCEL]) THEN
      `!x. x < 4294967296 ==> g x IN IMAGE FST M`
         by (Q.UNABBREV_TAC `g` THEN
             ASM_SIMP_TAC (srw_ss()) [] THEN
             REPEAT STRIP_TAC THEN Cases_on `x` THENL [
               ASM_SIMP_TAC (srw_ss()) [pairTheory.EXISTS_PROD] THEN
               PROVE_TAC [],
               Cases_on `n < LENGTH sfx` THENL [
                 ASM_SIMP_TAC (srw_ss()) [pairTheory.EXISTS_PROD,
                                          arithmeticTheory.ADD1,
                                          seq32_add_assoc] THEN
                 PROVE_TAC [],
                 CCONTR_TAC THEN DECIDE_TAC
               ]
             ]) THEN
      `4294967296 <= CARD (IMAGE FST M)`
         by (ASM_SIMP_TAC bool_ss [CARD_ENUMERATE_LOWER_BOUND,
                                   IMAGE_FINITE] THEN
             Q.EXISTS_TAC `g` THEN ASM_REWRITE_TAC []) THEN
      DECIDE_TAC
    ]
  ]);

val better_tcp_reass1 = prove(
  ``EVERY wf_reass rsegq ==>
    let myrel =
          FOLDL (\s sq. s UNION
                        (case sq.spliced_urp of
                            NONE => {}
                          | SOME v => if sq.seq <= v /\
                                         v < sq.seq + LENGTH sq.data + 1n
                                      then {(v, NONE)}
                                      else {}) UNION
                        LIST_TO_SET
                          (MAP (λ(n,e). (sq.seq + n, SOME e))
                               (number_skip 0
                                  (OPTION_MAP (\x. Num(x - sq.seq))
                                              sq.spliced_urp)
                                  sq.data))) {}
    in
      CARD (IMAGE FST (myrel rsegq)) < 4294967296 ==>
      tcp_reass seq rsegq =
        let cs_set = tcp_reass_build seq {[]} (myrel rsegq)
        in
            IMAGE (\cs. (CONCAT_OPTIONAL cs,
                         LENGTH cs,
                         EXISTS (\rseg.
                                    rseg.seq + LENGTH rseg.data +
                                    (if rseg.spliced_urp <> NONE then 1
                                     else 0) =
                                    seq + LENGTH cs /\ rseg.FIN)
                                rsegq)) cs_set``,
  STRIP_TAC THEN
  ASM_SIMP_TAC bool_ss [better_tcp_reass0] THEN
  SIMP_TAC pure_ss [LET_ELIM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC bool_ss [LET_THM] THEN
  Q.HO_MATCH_ABBREV_TAC `f (myrel rsegq) = g (myrel rsegq)` THEN
  Q_TAC SUFF_TAC `(!M. FINITE M /\ CARD (IMAGE FST M) < 4294967296 ==>
                       (f M = g M)) /\ FINITE (myrel rsegq)`
        THEN1 PROVE_TAC [] THEN
  `FINITE (myrel rsegq)`
     by (Q.UNABBREV_TAC `myrel` THEN
         Q.HO_MATCH_ABBREV_TAC
           `FINITE (FOLDL (\s sq. s UNION XX sq UNION
                                  LIST_TO_SET (h sq)) {} rsegq)` THEN
         Q_TAC SUFF_TAC
            `(!rsegq X. FINITE (FOLDL (\s sq. s UNION XX sq UNION
                                             LIST_TO_SET (h sq))
                                     X rsegq) = FINITE X) /\
             (!xx. FINITE (XX xx))`
            THEN1 SRW_TAC [][] THEN
         `!xx. FINITE (XX xx)`
            by (markerLib.UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
                Cases_on `xx.spliced_urp` THEN SRW_TAC [][]) THEN
         ASM_REWRITE_TAC [] THEN
         Induct THEN SRW_TAC [][]) THEN
  ASM_SIMP_TAC (srw_ss()) [Abbr`f`, Abbr`g`] THEN
  REPEAT (POP_ASSUM (K ALL_TAC)) THEN
  SIMP_TAC (srw_ss()) [EXTENSION] THEN GEN_TAC THEN STRIP_TAC THEN
  Q.X_GEN_TAC `e` THEN EQ_TAC THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `cs` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_X_ASSUM `e = _` (K ALL_TAC) THENL [
    rename1 `cs1 = CONCAT_OPTIONAL cs2` THEN
    Q.EXISTS_TAC `cs2` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
    `cs2 = APPEND [] cs2` by SRW_TAC [][] THEN
    POP_ASSUM SUBST1_TAC THEN
    MATCH_MP_TAC build_lemma1 THEN
    SRW_TAC [][],
    Q.EXISTS_TAC `cs` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
    `?pfx sfx. pfx IN {[]} /\ (cs = APPEND pfx sfx) /\
               (!n. n < LENGTH sfx ==> (seq + n, EL n sfx) IN M) /\
               (!c. ~((seq + LENGTH sfx, c) IN M))`
        by METIS_TAC [build_lemma2] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
  ]);

val tcp_reass_q_ok_def = Define`
  tcp_reass_q_ok rsegq =
     ?s : tcpForeign seq32.
       EVERY (\rseg. ~(s >= rseg.seq /\
                       s < rseg.seq + LENGTH rseg.data +
                           (if rseg.spliced_urp <> NONE then 1n else 0)))
             rsegq
`;

val o_ABS_R = combinTheory.o_ABS_R

val CARD_EQ_0' =
    CONJ CARD_EQ_0
         (CONV_RULE (BINDER_CONV (RAND_CONV (LAND_CONV (REWR_CONV EQ_SYM_EQ))))
                    CARD_EQ_0)

val INJ_SUBSET = prove(
  ``P0 SUBSET P /\ INJ f P Q ==> INJ f P0 Q``,
  SRW_TAC [][INJ_DEF, SUBSET_DEF]);

val INJ_INSERT = prove(
  ``~(e IN P) /\ INJ f (e INSERT P) Q ==> INJ f P (Q DELETE f e)``,
  REWRITE_TAC [INJ_DEF, IN_INSERT, IN_DELETE] THEN REPEAT STRIP_TAC THEN
  PROVE_TAC []);

val SURJ_INSERT_RNG = prove(
  ``~(e IN Q) /\ SURJ f P (e INSERT Q) ==>
    SURJ f (P DIFF {x | f x = e})  Q``,
  SRW_TAC [][SURJ_DEF] THEN PROVE_TAC []);

val EXTEND_SURJ = prove(
  ``SURJ f P Q ==> SURJ f (e INSERT P) (f e INSERT Q)``,
  SRW_TAC [][SURJ_DEF] THEN PROVE_TAC []);

val EXTEND_INJ = prove(
  ``~(e IN P) /\ ~(f e IN Q) /\ INJ f P Q ==>
    INJ f (e INSERT P) (f e INSERT Q)``,
  SRW_TAC [][INJ_DEF] THEN PROVE_TAC []);

val INJ_EQ_CARD_SURJ = prove(
  ``!s1. FINITE s1 ==>
         !s2 f. FINITE s2 /\ (CARD s1 = CARD s2) /\ INJ f s1 s2 ==>
                SURJ f s1 s2``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [boolSimps.CONJ_ss][CARD_EQ_0'] THENL [
    SRW_TAC [][INJ_DEF, SURJ_DEF],
    Q.ABBREV_TAC `s2' = s2 DELETE f e` THEN
    `INJ f s1 s2'` by PROVE_TAC [INJ_INSERT] THEN
    `f e IN s2` by PROVE_TAC [IN_INSERT, INJ_DEF] THEN
    `CARD s2' = CARD s2 - 1` by PROVE_TAC [CARD_DELETE] THEN
    `CARD s2' = CARD s1` by PROVE_TAC [DECIDE ``SUC x - 1 = x``] THEN
    `FINITE s2'` by SRW_TAC [][] THEN
    `SURJ f s1 s2'` by PROVE_TAC [] THEN
    `s2 = f e INSERT s2'` by SRW_TAC [][] THEN
    SRW_TAC [][EXTEND_SURJ]
  ]);

val CARD_DIFF' = prove(
  ``!s. FINITE s ==> !t. CARD (s DIFF t) = CARD s - CARD (s INTER t)``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN
  Cases_on `e IN t` THENL [
    SRW_TAC [][] THEN
    `(e INSERT s) INTER t = e INSERT (s INTER t)`
       by (SRW_TAC [][EXTENSION] THEN PROVE_TAC []) THEN
    POP_ASSUM SUBST1_TAC THEN
    SRW_TAC [][],
    SRW_TAC [][FINITE_DIFF] THEN
    `(e INSERT s) INTER t = s INTER t`
       by (SRW_TAC [][EXTENSION] THEN PROVE_TAC []) THEN
    SRW_TAC [][arithmeticTheory.SUB_LEFT_SUC] THEN
    `CARD (s INTER t) <= CARD s` by SRW_TAC [][CARD_INTER_LESS_EQ] THEN
    DECIDE_TAC
  ]);

val SURJ_EMPTY_DOM = prove(
  ``SURJ f {} P = (P = {})``,
  SRW_TAC [][SURJ_DEF, EXTENSION]);


val CARD_0_LT = prove(
  ``!s. FINITE s ==> ((0 < CARD s) = ?x. x IN s)``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [][EXISTS_OR_THM]);

val CARD_EQ_1 = prove(
  ``!s. FINITE s ==> ((CARD s = 1) = ?e. s = {e})``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN
  EQ_TAC THEN STRIP_TAC THEN SRW_TAC [][] THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][EXTENSION] THEN PROVE_TAC []);

val SURJ_LE_CARD_INJ = prove(
  ``!s2. FINITE s2 ==>
         !s1. FINITE s1 /\ (CARD s1 <= CARD s2) /\ SURJ f s1 s2 ==>
              INJ f s1 s2 /\ (CARD s1 = CARD s2)``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.CONJ_ss)[CARD_EQ_0'] THEN
  REPEAT (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `s1' = s1 DIFF {x | f x = e}` THEN
  `SURJ f s1' s2` by METIS_TAC [SURJ_INSERT_RNG] THEN
  `0 < CARD s1` by (SPOSE_NOT_THEN ASSUME_TAC THEN
                    `CARD s1 = 0` by DECIDE_TAC THEN
                    `s1 = {}` by PROVE_TAC [CARD_EQ_0'] THEN
                    PROVE_TAC [SURJ_EMPTY_DOM, IN_INSERT,
                               NOT_IN_EMPTY]) THEN
  `CARD s1' < CARD s1`
     by (SRW_TAC [][CARD_DIFF'] THEN
         Q_TAC SUFF_TAC `0 < CARD (s1 INTER {x | f x = e})` THEN1
               DECIDE_TAC THEN
         SRW_TAC [][CARD_0_LT] THEN
         METIS_TAC [SURJ_DEF, IN_INSERT]) THEN
  `CARD s1' <= CARD s2` by DECIDE_TAC THEN
  `INJ f s1' s2 /\ (CARD s1' = CARD s2)` by METIS_TAC [FINITE_DIFF] THEN
  `CARD s1 = SUC (CARD s2)` by DECIDE_TAC THEN
  `CARD s1' + 1 = CARD s1` by DECIDE_TAC THEN
  `CARD s1' = CARD s1 - CARD (s1 INTER {x | f x = e})`
     by (Q.UNABBREV_TAC `s1'` THEN
         Q.UNDISCH_THEN `FINITE s1` MP_TAC THEN
         SIMP_TAC (srw_ss()) [CARD_DIFF']) THEN
  `CARD (s1 INTER {x | f x = e}) <= CARD s1`
     by SRW_TAC [][CARD_INTER_LESS_EQ] THEN
  `CARD (s1 INTER {x | f x = e}) = 1` by DECIDE_TAC THEN
  `?d. s1 INTER {x | f x = e} = {d}`
     by PROVE_TAC [INTER_FINITE, CARD_EQ_1] THEN
  `d IN s1 /\ (f d = e)` by FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
  `s1 = d INSERT s1'`
     by (Q.PAT_X_ASSUM `s1 INTER X = {d}` MP_TAC THEN
         SRW_TAC [][EXTENSION] THEN PROVE_TAC []) THEN
  `~(d IN s1')` by (Q.UNABBREV_TAC `s1'` THEN
                    SIMP_TAC (srw_ss()) [] THEN
                    ASM_REWRITE_TAC []) THEN
  METIS_TAC [EXTEND_INJ]);

val CARD_EQ_INJ_EQ_SURJ = prove(
  ``!s1 s2. FINITE s1 /\ FINITE s2 /\ (CARD s1 = CARD s2) ==>
            (INJ f s1 s2 = SURJ f s1 s2)``,
  PROVE_TAC [SURJ_LE_CARD_INJ, INJ_EQ_CARD_SURJ,
             arithmeticTheory.LESS_EQ_REFL]);

val FINITE_w32_UNIV = prove(
  ``FINITE (UNIV : word32 set)``,
  REWRITE_TAC [FINITE_WEAK_ENUMERATE] THEN
  MAP_EVERY Q.EXISTS_TAC [`n2w`, `4294967296`] THEN
  SRW_TAC [][strong_word_nchotomy]);

val CARD_w32_UNIV = prove(
  ``CARD (UNIV : word32 set) = 4294967296``,
  REWRITE_TAC [DECIDE ``(n:num = m) = (n <= m /\ m <= n)``] THEN
  SIMP_TAC (srw_ss()) [FINITE_w32_UNIV, CARD_ENUMERATE_LOWER_BOUND,
                       CARD_ENUMERATE_UPPER_BOUND] THEN CONJ_TAC
  THENL [
    (* onto case *)
    Q.EXISTS_TAC `n2w` THEN PROVE_TAC [strong_word_nchotomy],
    Q.EXISTS_TAC `n2w` THEN SRW_TAC [][]
  ]);

val FINITE_foreign_s32_UNIV = prove(
  ``FINITE (UNIV : tcpForeign seq32 set)``,
  REWRITE_TAC [FINITE_WEAK_ENUMERATE] THEN
  MAP_EVERY Q.EXISTS_TAC [`\n. SEQ32 TcpForeign (n2w n)`, `4294967296`] THEN
  SRW_TAC [][] THEN Cases_on `e` THEN
  SRW_TAC [][tcp_ARB] THEN PROVE_TAC [strong_word_nchotomy]);

val CARD_foreign_s32_UNIV = prove(
  ``CARD (UNIV : tcpForeign seq32 set) = 4294967296``,
  REWRITE_TAC [DECIDE ``(n:num = m) = (n <= m /\ m <= n)``] THEN
  SIMP_TAC (srw_ss()) [FINITE_foreign_s32_UNIV, CARD_ENUMERATE_LOWER_BOUND,
                       CARD_ENUMERATE_UPPER_BOUND] THEN CONJ_TAC THEN
  Q.EXISTS_TAC `\n. SEQ32 TcpForeign (n2w n)` THEN
  SRW_TAC [][] THEN Cases_on `y` THEN
  SRW_TAC [][tcp_ARB] THEN PROVE_TAC [strong_word_nchotomy]);

val q_ok_cardinality = prove(
  ``EVERY wf_reass rsegq ==>
    let myrel =
          FOLDL (\s sq. s UNION
                        (case sq.spliced_urp of
                            NONE => {}
                          | SOME v => if sq.seq <= v /\
                                         v < sq.seq + LENGTH sq.data + 1n
                                      then {(v,NONE)}
                                      else {}) UNION
                        LIST_TO_SET
                          (MAP (λ(n,e). (sq.seq + n, SOME e))
                               (number_skip 0
                                  (OPTION_MAP (\x. Num(x - sq.seq))
                                              sq.spliced_urp)
                                  sq.data))) {}
    in
        (CARD (IMAGE FST (myrel rsegq)) < 4294967296) =
        tcp_reass_q_ok rsegq``,
  STRIP_TAC THEN SIMP_TAC pure_ss [LET_ELIM] THEN
  REPEAT (GEN_TAC THEN STRIP_TAC) THEN
  CONV_TAC (BINOP_CONV (REWR_CONV (tautLib.TAUT `p = ~~p`))) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [arithmeticTheory.NOT_LESS] THEN
  SIMP_TAC (srw_ss()) [tcp_reass_q_ok_def, o_ABS_R] THEN
  `FINITE (myrel rsegq)`
     by (Q.UNABBREV_TAC `myrel` THEN
         Q.HO_MATCH_ABBREV_TAC
           `FINITE (FOLDL (\s sq. s UNION f sq UNION
                                  LIST_TO_SET (h sq)) {} rsegq)` THEN
         Q_TAC SUFF_TAC
            `(!rsegq X. FINITE (FOLDL (\s sq. s UNION f sq UNION
                                                LIST_TO_SET (h sq))
                                      X rsegq) = FINITE X) /\
             (!x. FINITE (f x))`
            THEN1 SRW_TAC [][] THEN
         `!x. FINITE (f x)`
            by (SRW_TAC [][Abbr`f`] THEN Cases_on `x.spliced_urp` THEN
                SRW_TAC [][]) THEN
         ASM_SIMP_TAC (srw_ss()) [] THEN Induct THEN SRW_TAC [][]) THEN
  ASM_SIMP_TAC (srw_ss()) [CARD_ENUMERATE_LOWER_BOUND, IMAGE_FINITE,
                           listTheory.EXISTS_MEM, pairTheory.EXISTS_PROD] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    `!s c. (s,c) IN myrel rsegq ==>
           ?rseg. rseg IN' rsegq /\ s >= rseg.seq /\
                  s < rseg.seq + LENGTH rseg.data +
                      (if rseg.spliced_urp <> NONE then 1i else 0i)`
        by (MP_TAC (GSYM tcp_reass_myrel) THEN
            ASM_REWRITE_TAC [] THEN SIMP_TAC (srw_ss()) [] THEN
            METIS_TAC[]) THEN
    ONCE_REWRITE_TAC [GSYM seq32_add_posint] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN
    Q_TAC SUFF_TAC `!s : tcpForeign seq32. ?x. x < 4294967296 /\ f x = s`
          THEN1 METIS_TAC [] THEN
    Q_TAC SUFF_TAC `SURJ f (count 4294967296) UNIV` THEN1
          SRW_TAC [][SURJ_DEF, count_def] THEN
    `CARD (count 4294967296) = 4294967296` by SRW_TAC [][CARD_COUNT] THEN
    Q_TAC SUFF_TAC `INJ f (count 4294967296) UNIV` THEN1
          PROVE_TAC [CARD_EQ_INJ_EQ_SURJ, CARD_foreign_s32_UNIV,
                     FINITE_COUNT, FINITE_foreign_s32_UNIV] THEN
    SRW_TAC [][INJ_DEF, count_def],

    Q.EXISTS_TAC `\n. SEQ32 TcpForeign (n2w n)` THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    MP_TAC (GSYM tcp_reass_myrel) THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC (srw_ss()) [] THEN DISCH_THEN (K ALL_TAC) THEN
    Q.X_GEN_TAC `x` THEN
    POP_ASSUM (Q.SPEC_THEN `SEQ32 TcpForeign (n2w x)`
                           (Q.X_CHOOSE_THEN `rseg` STRIP_ASSUME_TAC)) THEN
    STRIP_TAC THEN
    CONV_TAC SWAP_VARS_CONV THEN Q.EXISTS_TAC `rseg` THEN
    Cases_on `rseg.spliced_urp` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    ASM_SIMP_TAC (srw_ss() ++ boolSimps.COND_elim_ss ++ boolSimps.DNF_ss) []
  ]);

val LET_FORALL = prove(``LET f v = !x. (v = x) ==> f x``, SRW_TAC [][]);
val LET_RAND' = prove(``P (LET f v) = LET (P o f) v``, SRW_TAC [][])
val LET_RATOR' = prove(
  ``(LET f v) x = LET (combin$C f x) v``,
  SRW_TAC [][combinTheory.C_THM]);

val o_ABS_R = prove(
  ``f o (\x. g x) = (\x. f (g x))``,
  SRW_TAC [][FUN_EQ_THM])
val o_UNCURRY_R = prove(
  ``f o UNCURRY g = UNCURRY ((o) f o g)``,
  SRW_TAC [][pairTheory.UNCURRY, FUN_EQ_THM]);
val C_ABS_L = prove(
  ``combin$C (\x. f x) y = (\x. f x y)``,
  SRW_TAC [][FUN_EQ_THM])
val C_UNCURRY_L = prove(
  ``combin$C (UNCURRY f) x = UNCURRY (combin$C (combin$C o f) x)``,
  SRW_TAC [][FUN_EQ_THM, pairTheory.UNCURRY])
val RAISE_LETS_CONV =
    SIMP_CONV pure_ss [o_ABS_R, o_UNCURRY_R, C_ABS_L, C_UNCURRY_L,
                       LET_RATOR', LET_RAND']
fun ELIM_LET t = if is_let t andalso is_var (rand t) then
                   (REWR_CONV LET_THM THENC BETA_CONV) t
                 else NO_CONV t
val RAISE_LETS_TAC = CONV_TAC RAISE_LETS_CONV THEN
                     REPEAT (CONV_TAC (HO_REWR_CONV LET_FORALL) THEN
                             GEN_TAC THEN
                             DISCH_THEN (fn th => REWRITE_TAC [th] THEN
                                                  ASSUME_TAC th) THEN
                             CONV_TAC (DEPTH_CONV ELIM_LET))


val better_tcp_reass = store_thm(
  "better_tcp_reass",
  ``EVERY wf_reass rsegq /\
    tcp_reass_q_ok rsegq ==>
    tcp_reass seq rsegq =
      let myrel =
            FOLDL (\s sq. s UNION
                          (case sq.spliced_urp of
                              NONE => {}
                            | SOME v => if sq.seq <= v /\
                                           v < sq.seq + LENGTH sq.data + 1n
                                        then {(v, NONE)}
                                        else {}) UNION
                          LIST_TO_SET
                            (MAP (λ(n,e). (sq.seq + n, SOME e))
                                 (number_skip 0n
                                     (OPTION_MAP (\x. Num(x - sq.seq))
                                                 sq.spliced_urp)
                                     sq.data))) {} in
      let cs_set = tcp_reass_build seq {[]} (myrel rsegq)
      in
          IMAGE (\cs. (CONCAT_OPTIONAL cs,
                       LENGTH cs,
                       EXISTS (\rseg.
                                  rseg.seq + LENGTH rseg.data +
                                  (if rseg.spliced_urp <> NONE then 1i
                                   else 0i) =
                               seq + LENGTH cs /\ rseg.FIN)
                              rsegq)) cs_set``,
  REPEAT STRIP_TAC THEN RAISE_LETS_TAC THEN
  MP_TAC better_tcp_reass1 THEN
  ASM_SIMP_TAC bool_ss [] THEN
  SIMP_TAC (srw_ss()) [] THEN ASM_SIMP_TAC bool_ss [] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC q_ok_cardinality THEN ASM_SIMP_TAC bool_ss [] THEN
  ASM_SIMP_TAC (srw_ss()) []);

val FINITE_GSPEC_AND = prove(
  ``FINITE { x | P x} \/ FINITE {x | Q x} ==> FINITE ({ x | P x /\ Q x})``,
  SRW_TAC [][GSPEC_AND] THEN PROVE_TAC [INTER_COMM, INTER_FINITE]);

val COND_EXPAND_DNF = prove(
  ``(if p then q else r) = (p /\ q \/ ~p /\ r)``,
  REWRITE_TAC [COND_EXPAND] THEN tautLib.TAUT_TAC);

val fid_ref_count_thm = store_thm(
  "fid_ref_count_thm",
  ``(!v. fid_ref_count(FEMPTY, v) = 0) /\
    (!fm k v1 v2. fid_ref_count(fm |+ (k,v1), v2) =
                  (if v1 = v2 then 1 else 0) + fid_ref_count(fm \\ k, v2))``,
  SRW_TAC [boolSimps.CONJ_ss]
          [fid_ref_count_def, RRESTRICT_DEF, GSPEC_F,
           DOMSUB_FAPPLY_THM, RIGHT_AND_OVER_OR, GSPEC_OR,
           GSYM INSERT_SING_UNION, GSYM CONJ_ASSOC,
           FAPPLY_FUPDATE_THM, FINITE_GSPEC_AND] THEN
  SRW_TAC [][] THENL [
    ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN REWRITE_TAC [COND_EXPAND_DNF] THEN
    SRW_TAC [boolSimps.CONJ_ss][GSPEC_OR, FINITE_GSPEC_AND,
                                GSYM INSERT_SING_UNION,
                                arithmeticTheory.ADD1] THEN
    SIMP_TAC arith_ss [] THEN REPEAT AP_TERM_TAC THEN
    SRW_TAC [][FUN_EQ_THM, EQ_IMP_THM],
    SRW_TAC [boolSimps.CONJ_ss, boolSimps.COND_elim_ss]
            [LEFT_AND_OVER_OR, arithmeticTheory.ADD1] THEN
    SIMP_TAC arith_ss [] THEN REPEAT AP_TERM_TAC THEN
    SRW_TAC [][FUN_EQ_THM, EQ_IMP_THM],
    SRW_TAC [boolSimps.COND_elim_ss, boolSimps.CONJ_ss][LEFT_AND_OVER_OR]
  ]);

val _ = BasicProvers.export_rewrites ["fid_ref_count_thm"]


val IP_11 = store_thm(
  "IP_11",
  ``!w1 w2 x1 x2 y1 y2 z1 z2.
       x1 < 256 /\ x2 < 256 /\ y1 < 256 /\ y2 < 256 /\ z1 < 256 /\ z2 < 256 ==>
       (IP w1 x1 y1 z1 = IP w2 x2 y2 z2) =
       (w1 = w2 /\ x1 = x2 /\ y1 = y2 /\ z1 = z2)``,
  SIMP_TAC bool_ss [EQ_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC (bool_ss ++ numSimps.REDUCE_ss)
           [IP_def, TypeBase.one_one_of ``:TCP1_baseTypes$ip``] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN intLib.ARITH_TAC);

val mask8_IP = store_thm(
  "mask8_IP",
  ``!w x y z. x < 256 /\ y < 256 /\ z < 256 ==>
              mask (NETMASK 8) (IP w x y z) = IP w 0 0 0``,
  REPEAT STRIP_TAC THEN
  SIMP_TAC (bool_ss ++ numSimps.REDUCE_ss)
           [mask_def, IP_def, arithmeticTheory.ADD_CLAUSES] THEN
  REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  REWRITE_TAC [GSYM arithmeticTheory.ADD_ASSOC] THEN
  MATCH_MP_TAC arithmeticTheory.DIV_MULT THEN DECIDE_TAC);

val mask24_IP = store_thm(
  "mask24_IP",
  ``!w x y z. x < 256 /\ y < 256 /\ z < 256 ==>
              mask (NETMASK 24) (IP w x y z) = IP w x y 0``,
  REPEAT STRIP_TAC THEN
  SIMP_TAC (bool_ss ++ numSimps.REDUCE_ss)
           [mask_def, IP_def, arithmeticTheory.ADD_CLAUSES] THEN
  REWRITE_TAC [DECIDE ``65536 = 256n * 256``] THEN
  REWRITE_TAC [DECIDE ``16777216 = 65536 * 256n``] THEN
  REWRITE_TAC [arithmeticTheory.MULT_ASSOC,
               GSYM arithmeticTheory.RIGHT_ADD_DISTRIB] THEN
  REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  MATCH_MP_TAC arithmeticTheory.DIV_MULT THEN ASM_REWRITE_TAC []);

val mask0_IP = store_thm(
  "mask0_IP",
  ``!w x y z. x < 256 /\ y < 256 /\ z < 256 /\ w < 256 ==>
              mask (NETMASK 0) (IP w x y z) = IP 0 0 0 0``,
  REPEAT STRIP_TAC THEN
  SIMP_TAC (bool_ss ++ numSimps.REDUCE_ss) [mask_def, IP_def] THEN
  Q.SUBGOAL_THEN `w * 16777216 + x * 65536 + y * 256 + z < 4294967296`
  ASSUME_TAC THENL [DECIDE_TAC, ALL_TAC] THEN
  ASM_SIMP_TAC bool_ss  [arithmeticTheory.LESS_DIV_EQ_ZERO,
                         arithmeticTheory.MULT_CLAUSES]);

val mask4_IP = store_thm(
  "mask4_IP",
  ``!w x y z. x < 256 /\ y < 256 /\ z < 256 /\ w < 256 ==>
              mask (NETMASK 4) (IP w x y z) = IP (w DIV 16 * 16) 0 0 0``,
 REPEAT STRIP_TAC THEN
 SIMP_TAC (srw_ss()) [mask_def, IP_def] THEN
 Q.SUBGOAL_THEN `x * 65536 + (y * 256 + z) < 16777216` ASSUME_TAC THENL [
   DECIDE_TAC,
   ALL_TAC
 ] THEN
 `!x. x DIV 268435456 = (x DIV 16777216) DIV 16`
     by (`268435456n = 16777216 * 16` by SRW_TAC [][] THEN
         ASM_REWRITE_TAC [] THEN
         SRW_TAC [][GSYM arithmeticTheory.DIV_DIV_DIV_MULT]) THEN
 SRW_TAC [][GSYM arithmeticTheory.ADD_ASSOC, arithmeticTheory.DIV_MULT] THEN
 SRW_TAC [][GSYM arithmeticTheory.MULT_ASSOC]);

(*
val ipmask_broadcast = Define`
  ipmask_broadcast (NETMASK m) (ip n) = ip (n + 2 EXP (32 - m) - 1)
*)

open arithmeticTheory
val zero_lt_xy = prove(
  ``(0n < x * y) = (0 < x /\ 0 < y)``,
  PROVE_TAC [NOT_ZERO_LT_ZERO, MULT_EQ_0])

val LESS_RMUL_CANCEL = LT_MULT_RCANCEL

val div_lt = prove(
  ``0 < y ==> (x DIV y < z) = (x < y * z)``,
  STRIP_TAC THEN
  Q.SPEC_THEN `y` MP_TAC DIVISION THEN ASM_REWRITE_TAC [] THEN
  DISCH_THEN (Q.SPEC_THEN `x` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `q = x DIV y` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = x MOD y` THEN POP_ASSUM (K ALL_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  EQ_TAC THEN STRIP_TAC THENL [
    MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN Q.EXISTS_TAC `SUC q * y` THEN
    CONJ_TAC THEN1 SRW_TAC [][MULT_CLAUSES] THEN
    CONV_TAC (LAND_CONV (REWR_CONV MULT_COMM)) THEN
    SRW_TAC [][] THEN DECIDE_TAC,
    Q_TAC SUFF_TAC `q * y < z * y` THEN1 SRW_TAC [][LESS_RMUL_CANCEL] THEN
    MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `q * y + r` THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [AC MULT_ASSOC MULT_COMM]
  ]);


val divmod_lemma = store_thm(
  "divmod_lemma",
  ``0 < y /\ 0 < z ==> (x DIV y) MOD z = (x MOD (y * z)) DIV y``,
  STRIP_TAC THEN
  `0 < y * z` by SRW_TAC [][zero_lt_xy] THEN
  Q.SPEC_THEN `y * z` MP_TAC arithmeticTheory.DIVISION THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (Q.SPEC_THEN `x` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `q = x DIV (y * z)` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = x MOD (y * z)` THEN POP_ASSUM (K ALL_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  `q * (y * z) = (q * z) * y` by SRW_TAC [][AC MULT_ASSOC MULT_COMM] THEN
  SRW_TAC [][ADD_DIV_ADD_DIV, MOD_TIMES, div_lt]);

val better_ip_case = p1store_thm(
  "better_ip_case",
  ``ip_CASE (IP w x y z) (\v. ip (f v)) =
      let ipnum = w * 2 EXP 24 + x * 2 EXP 16 + y * 2 EXP 8 + z in
      let res = f ipnum in
      let  lo8 = res MOD 256 in
      let hi24 = res DIV 256 in
      let lo16 = hi24 MOD 256 in
      let hi16 = hi24 DIV 256 in
      let lo24 = hi16 MOD 256 in
      let hi24 = hi16 DIV 256 in
        IP hi24 lo24 lo16 lo8``,
  SRW_TAC [][IP_def, arithmeticTheory.DIV_DIV_DIV_MULT] THEN
  Q.ABBREV_TAC `r = f (w * 16777216 + x * 65536 + y * 256 + z)` THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [GSYM arithmeticTheory.ADD_ASSOC] THEN
  Q.SPEC_THEN `16777216` (MP_TAC o SIMP_RULE (srw_ss()) [])
              arithmeticTheory.DIVISION THEN
  DISCH_THEN (Q.SPEC_THEN `r` MP_TAC) THEN
  DISCH_THEN (fn th => CONV_TAC (LAND_CONV (K th))) THEN
  REWRITE_TAC [arithmeticTheory.EQ_ADD_LCANCEL] THEN
  CONV_TAC (RAND_CONV
                (LAND_CONV
                     (SIMP_CONV (srw_ss()) [divmod_lemma]))) THEN
  Q.SPEC_THEN `65536`
              (MP_TAC o SIMP_RULE (srw_ss()) []) DIVISION THEN
  DISCH_THEN (Q.SPEC_THEN `r MOD 16777216` MP_TAC) THEN
  DISCH_THEN (fn th => CONV_TAC (LAND_CONV (K th))) THEN
  REWRITE_TAC [EQ_ADD_LCANCEL] THEN
  `16777216n = 65536 * 256` by SRW_TAC [][] THEN
  POP_ASSUM SUBST_ALL_TAC THEN SRW_TAC [][MOD_MULT_MOD] THEN
  SRW_TAC [][divmod_lemma] THEN
  Q.SPEC_THEN `256` (MP_TAC o SIMP_RULE (srw_ss()) []) DIVISION THEN
  DISCH_THEN (Q.SPEC_THEN `r MOD 65536` MP_TAC) THEN
  DISCH_THEN (fn th => CONV_TAC (LAND_CONV (K th))) THEN
  REWRITE_TAC [EQ_ADD_LCANCEL] THEN
  `65536n = 256 * 256` by SRW_TAC [][] THEN
  POP_ASSUM SUBST_ALL_TAC THEN SRW_TAC [][MOD_MULT_MOD]);


val _ = BasicProvers.export_rewrites ["IP_11", "mask8_IP", "mask24_IP",
                                      "mask0_IP", "mask4_IP"]

val route_and_enqueue_oq_no_error = store_thm(
  "route_and_enqueue_oq_no_error",
  ``route_and_enqueue_oq (rttab, ifds, oq, msg, oq', NONE, arch) =
      (test_outroute (msg, rttab, ifds, arch) = SOME NONE /\
       enqueue_oq(oq,msg,oq',T))``,
  SRW_TAC [][route_and_enqueue_oq_def, EQ_IMP_THM] THENL [
    Cases_on `test_outroute (msg,rttab,ifds,arch)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN Cases_on `x` THEN
    FULL_SIMP_TAC (srw_ss()) [],
    Cases_on `test_outroute (msg,rttab,ifds,arch)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN Cases_on `x` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `queued` THEN FULL_SIMP_TAC (srw_ss()) []
  ]);

val route_and_enqueue_oq_error = store_thm(
  "route_and_enqueue_oq_error",
  ``route_and_enqueue_oq (rttab, ifds, oq, msg, oq', SOME e, arch) =
      ?v. test_outroute(msg, rttab, ifds, arch) = SOME v /\
          case v of
             NONE => enqueue_oq (oq, msg, oq', F) /\ (e = ENOBUFS)
           | SOME e' => oq = oq' /\ e = e'``,
  SIMP_TAC (srw_ss()) [route_and_enqueue_oq_def] THEN
  Cases_on `test_outroute(msg, rttab, ifds, arch)` THEN
  SIMP_TAC (srw_ss()) [] THEN
  Cases_on `x` THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.COND_elim_ss) [] THEN
  PROVE_TAC []);

(* above 2 theorems could serve as definition of route_and_enqueue_oq, but
   perhaps proving them as consequences is a useful sanity check. *)

val _ = BasicProvers.export_rewrites
          ["route_and_enqueue_oq_error", "route_and_enqueue_oq_no_error"]

val GSPEC_ID_sym = prove(
  ``{p | x = p} = {x}``,
  SRW_TAC [][pred_setTheory.EXTENSION] THEN PROVE_TAC []);

(* hideous proof ! *)
val (revised, asm) = let
  val base = #2 (strip_forall (concl TCP1_auxFnsTheory.bound_port_allowed_def))
  val r = rhs base
  val setexp = rand (rand r)
  val abs = rand setexp
  val ex_t = rand (#2 (dest_abs abs))
  val ugly = last (strip_conj (#2 (dest_exists ex_t)))
  val vars = [``s:socket``, ``arch :arch``, ``sf:sockflags``, ``is:ip option``]
  val newf = list_mk_abs (vars, ugly)
  val newf_applied = list_mk_comb(newf, vars)
  val newf_eqn_t = mk_eq(mk_var("newf", type_of newf), newf)
  val newf_eqn = SYM (ASSUME newf_eqn_t)
  val newf_elim = SYM (LIST_BETA_CONV newf_applied)
in
  ((REWRITE_RULE [newf_eqn] o ONCE_REWRITE_RULE [newf_elim])
     TCP1_auxFnsTheory.bound_port_allowed_def,
   newf_eqn_t)
end

fun elim_eq_asm t th = let
  val v = lhs t
  val th = DISCH t th
  val th = GEN v th
  val th = CONV_RULE FORALL_IMP_CONV th
in
  MP th (ISPEC (rhs t) EXISTS_REFL)
end

val better_bound_port_allowed0 = prove(
  ``^asm ==>
       bound_port_allowed pr FEMPTY sf arch is p = T /\
       bound_port_allowed pr (socks |+ (sid, s)) sf arch is p =
         case s.ps1 of
            NONE => bound_port_allowed pr (socks \\ sid) sf arch is p
          | SOME port =>
              bound_port_allowed pr (socks \\ sid) sf arch is p /\
              ((p = port) /\ proto_eq s.pr pr ==> ~newf s arch sf is)``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [revised] THEN
  POP_ASSUM (K ALL_TAC) THEN
  Cases_on `s.ps1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL [
    PROVE_TAC [],
    FIRST_X_ASSUM (Q.SPEC_THEN `s'` STRIP_ASSUME_TAC) THEN
    SRW_TAC [][] THEN Cases_on `s = s'` THEN SRW_TAC [][],
    PROVE_TAC [optionTheory.option_CASES],
    PROVE_TAC [],
    PROVE_TAC [optionTheory.SOME_11]
  ]);
val better_bound_port_allowed = save_thm(
  "better_bound_port_allowed",
  (elim_eq_asm asm o BETA_RULE o simpLib.ASM_SIMP_RULE pure_ss [] o
   UNDISCH) better_bound_port_allowed0)
val _ = Phase.add_to_phase 1 "better_bound_port_allowed"

val better_bound_ports_protocol_autobind = p1store_thm(
  "better_bound_ports_protocol_autobind",
  ``bound_ports_protocol_autobind pr FEMPTY = {} /\
    bound_ports_protocol_autobind pr (socks |+ (sid, s)) =
      case s.ps1 of
         NONE => bound_ports_protocol_autobind pr (socks \\ sid)
       | SOME p => if proto_of s.pr = pr then
                     p INSERT bound_ports_protocol_autobind pr (socks \\ sid)
                   else bound_ports_protocol_autobind pr (socks \\ sid)``,
  SRW_TAC [][TCP1_auxFnsTheory.bound_ports_protocol_autobind_def] THEN
  Cases_on `s.ps1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [boolSimps.DNF_ss][] THEN
  SRW_TAC [][EXTENSION] THEN PROVE_TAC []);

val INSERT_CROSS = store_thm(
  "INSERT_CROSS",
  ``!P Q x. (x INSERT P) CROSS Q = IMAGE (\q. (x, q)) Q UNION (P CROSS Q)``,
  SRW_TAC [][pred_setTheory.EXTENSION, pred_setTheory.IN_CROSS,
             EQ_IMP_THM] THEN SRW_TAC [][] THEN
  DISJ1_TAC THEN Q.EXISTS_TAC `SND x'` THEN SRW_TAC [][]);

val INSERT_UNION_INSERT = save_thm(
  "INSERT_UNION_INSERT",
  Q.SPECL [`x`,`s`,`y INSERT t`] pred_setTheory.INSERT_UNION_EQ)





(* ----------------------------------------------------------------------
    facts about time, maintaining the time and time_infty "constructors"
   ---------------------------------------------------------------------- *)

val time_lt_refl = store_thm(
  "time_lt_refl",
  ``~(t:time < t)``,
  Cases_on `t` THEN SRW_TAC [][TCP1_baseTypesTheory.time_lt_def,
                               realTheory.REAL_LT_REFL])

val time_le_refl = store_thm(
  "time_le_refl",
  ``(t:time) <= t``,
  Cases_on `t` THEN SRW_TAC [][TCP1_baseTypesTheory.time_lte_def]);

val IS_SOME_exists = prove(
  ``IS_SOME v = (?v0. v = SOME v0)``,
  Cases_on `v` THEN SRW_TAC [][]);


(* more betters *)

val better_make_syn_segment = store_thm(
  "better_make_syn_segment",
  ``make_syn_segment cb (i1,i2,p1,p2) ts_val seg =
      ?urp_any ack_any.
        let cbrcv_win = cb.rcv_wnd in
        let cbrqrscale = cb.request_r_scale in
        let cbtadvmss = cb.t_advmss in
        let cbtmaxseg = cb.t_maxseg in
        let cbtfreqtstmp = cb.tf_req_tstmp in
        let cbtsrecent = cb.ts_recent in
        let cbiss = cb.iss in
        let win = n2w cbrcv_win in
        let ws = OPTION_MAP CHR cbrqrscale in
        let mss = (case cbtadvmss of
                      NONE => NONE
                    | SOME n => SOME (n2w n)) in
        let ts = do_tcp_options cbtfreqtstmp cbtsrecent ts_val
        in
              w2n win = cbrcv_win /\
              (IS_SOME cbrqrscale ==> ORD (THE ws) = THE cbrqrscale) /\
              (case ws of NONE => T | SOME v => ORD v <= TCP_MAXWINSCALE) /\
              (IS_SOME cbtadvmss ==>
                 THE cbtadvmss = w2n (n2w (THE cbtadvmss) : word16)) /\
              (seg = <| is1 := SOME i1; is2 := SOME i2; ps1 := SOME p1;
                        ps2 := SOME p2; seq := cbiss; ack := ack_any;
                        URG := F; ACK := F; PSH := F; RST := F; SYN := T;
                        FIN := F; win := win; ws := ws; urp := urp_any;
                        mss := mss; ts := ts; data := [] |>)``,
  SRW_TAC [][make_syn_segment_def, RES_EXISTS_THM,
             IS_SOME_exists, GSYM RIGHT_EXISTS_AND_THM,
             GSYM LEFT_FORALL_IMP_THM, RIGHT_AND_FORALL_THM,
             wordsTheory.word_0] THEN
  Cases_on `cb.t_advmss` THEN FULL_SIMP_TAC (srw_ss()) []);

val better_make_ack_segment = store_thm(
  "better_make_ack_segment",
  ``make_ack_segment cb FIN (i1,i2,p1,p2) ts_val seg =
      ?urp_any.
         let cbrcv_win = cb.rcv_wnd in
         let cbrcv_scale = cb.rcv_scale in
         let cb_doing_tstmp = cb.tf_doing_tstmp in
         let cb_ts_recent = cb.ts_recent in
         let win = n2w (cbrcv_win >> cbrcv_scale) in
         let ts = do_tcp_options cb.tf_doing_tstmp cb.ts_recent ts_val
         in
           w2n win = cbrcv_win >> cbrcv_scale /\
           seg = <|is1 := SOME i1; is2 := SOME i2; ps1 := SOME p1;
                   ps2 := SOME p2;
                   seq := if FIN then cb.snd_una else cb.snd_nxt;
                   ack := cb.rcv_nxt;
                   URG := F; ACK := T; PSH := F; RST := F; SYN := F;
                   FIN := FIN; win := win; ws := NONE; urp := urp_any;
                   mss := NONE; ts := ts; data := []|>``,
  SRW_TAC [][make_ack_segment_def, wordsTheory.word_0, RES_EXISTS_THM,
             prove(``I = \x.x``, SRW_TAC [][FUN_EQ_THM])]);

val better_bsd_make_phantom_segment = store_thm(
  "better_bsd_make_phantom_segment",
  ``bsd_make_phantom_segment cb (i1,i2,p1,p2) ts_val cantsndmore seg =
      ?urp_any.
         let cbrcv_win = cb.rcv_wnd in
         let cbrcv_scale = cb.rcv_scale in
         let cb_doing_tstmp = cb.tf_doing_tstmp in
         let cb_ts_recent = cb.ts_recent in
         let win = n2w (cbrcv_win >> cbrcv_scale) in
         let FIN = (cantsndmore /\ cb.snd_una < (cb.snd_max - 1)) in
         let ts = do_tcp_options cb.tf_doing_tstmp cb.ts_recent ts_val
         in
           w2n win = cbrcv_win >> cbrcv_scale /\
           seg = <|is1 := SOME i1; is2 := SOME i2; ps1 := SOME p1;
                   ps2 := SOME p2; seq := if FIN then cb.snd_una else cb.snd_max;
                   ack := cb.rcv_nxt;
                   URG := F; ACK := F; PSH := F; RST := F; SYN := F;
                   FIN := FIN; win := win; ws := NONE; urp := urp_any;
                   mss := NONE; ts := ts; data := []|>``,
  SRW_TAC [][bsd_make_phantom_segment_def, wordsTheory.word_0, RES_EXISTS_THM,
             prove(``I = \x.x``, SRW_TAC [][FUN_EQ_THM])]);


(* useful stuff about tcp sequences *)

val tcp_seq_flip_sense_eq = store_thm(
  "tcp_seq_flip_sense_eq",
  ``(tcp_seq_foreign_to_local v1 = SEQ32 TcpLocal x1) =
       (v1 = SEQ32 TcpForeign x1) /\
    (tcp_seq_local_to_foreign v2 = SEQ32 TcpForeign x2) =
       (v2 = SEQ32 TcpLocal x2)``,
  Cases_on `v1` THEN Cases_on `v2` THEN
  SRW_TAC [][TCP1_baseTypesTheory.tcp_seq_foreign_to_local_def,
             TCP1_baseTypesTheory.tcp_seq_local_to_foreign_def,
             TCP1_baseTypesTheory.seq32_coerce_def, tcp_ARB,
             TCP1_baseTypesTheory.tcpLocal2num_thm,
             TCP1_baseTypesTheory.tcpForeign2num_thm]);

open TCP1_utilsTheory
open TCP1_utilPropsTheory
val rounddown_leq = prove(
  ``0 < b ==> rounddown b v <= v``,
  SRW_TAC [][rounddown_def] THEN
  PROVE_TAC [arithmeticTheory.DIVISION, arithmeticTheory.LESS_EQ_EXISTS]);

val rounddup_eq_args = prove(
  ``0 < v ==> (roundup v v = v)``,
  SRW_TAC [][roundup_def] THEN
  SRW_TAC [numSimps.ARITH_ss]
          [arithmeticTheory.ADD_DIV_RWT, arithmeticTheory.LESS_DIV_EQ_ZERO]);

val roundup_lt_base = prove(
  ``v < b ==> (roundup b v = if v = 0 then 0 else b)``,
  SRW_TAC [][roundup_def] THENL [
    SRW_TAC [numSimps.ARITH_ss][arithmeticTheory.LESS_DIV_EQ_ZERO],
    `v + (b - 1) = b + (v - 1)` by SRW_TAC [numSimps.ARITH_ss][] THEN
    `0 < b` by SRW_TAC [numSimps.ARITH_ss][] THEN
    ASM_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD_DIV_RWT] THEN
    SRW_TAC [numSimps.ARITH_ss][arithmeticTheory.LESS_DIV_EQ_ZERO]
  ]);

val let_forall = prove(
  ``(bool$LET f v ==> p) = !x. (x = v) ==> f x ==> p``,
  SIMP_TAC bool_ss [LET_THM]);

val let_forall2 = prove(
  ``(bool$LET P v) = !x. (x = v) ==> P x``,
  SIMP_TAC bool_ss [LET_THM]);

fun var_eq_var t = let val (l,r) = dest_eq t in is_var l andalso is_var r end


val calculate_buf_sizes_EQ_implication = prove(
  ``cb_t_maxseg < NUMERAL n ==>
    ((NUMERAL n, x, y ,z) =
       calculate_buf_sizes cb_t_maxseg seg_mss bwdp localp
                           rcvbuf sndbuf cb_tf_doing_tstmp arch) ==>
     (NUMERAL n =  MIN SB_MAX (roundup y (option_CASE bwdp rcvbuf I))) /\
     (x = bool$LET (\sndbufsize'.
                      if sndbufsize' < y then sndbufsize'
                      else MIN SB_MAX (roundup y sndbufsize'))
                   (option_CASE bwdp sndbuf I)) /\
     (NUMERAL y = MIN cb_t_maxseg (MAX 64 (option_CASE seg_mss MSSDFLT I))) /\
     (z = bool$LET
            (\mss.
               MIN (10 * mss) (MAX (2 * mss) (10 * 1460)))
            (if linux_arch arch then y
             else (y - calculate_tcp_options_len cb_tf_doing_tstmp)))``,
  `NUMERAL n = n` by SRW_TAC [][arithmeticTheory.NUMERAL_DEF] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  `NUMERAL y = y` by SRW_TAC [][arithmeticTheory.NUMERAL_DEF] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  SIMP_TAC bool_ss [calculate_buf_sizes_def, TCP1_paramsTheory.SB_MAX_def] THEN
  CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV (GSYM combinTheory.I_THM)))) THEN
  LET_ELIM_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN REPEAT VAR_EQ_TAC THEN
  `mss <= t_maxseg''` by SRW_TAC [][Abbr`mss`] THEN
  `t_maxseg' <= cb_t_maxseg` by SRW_TAC [][Abbr`t_maxseg'`] THEN
  `mss' <= t_maxseg'` by SRW_TAC [][Abbr`mss'`] THEN
  `mss' <= cb_t_maxseg` by DECIDE_TAC THEN
  `~(rcvbufsize' < t_maxseg')`
      by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN DECIDE_TAC) THEN
  Q.UNDISCH_THEN `Abbrev ~do_rfc3390` MP_TAC THEN
  REWRITE_TAC [markerTheory.Abbrev_def] THEN
  DISCH_THEN (SUBST_ALL_TAC o EQF_INTRO) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.UNDISCH_THEN `Abbrev (mss = mss')` MP_TAC THEN
  REWRITE_TAC [markerTheory.Abbrev_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val roundup_x0 = store_thm(
  "roundup_x0[simp]",
  ``roundup x 0 = 0``,
  SRW_TAC[][roundup_def] THEN Cases_on `x = 0` THEN SRW_TAC[][] THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [arithmeticTheory.LESS_DIV_EQ_ZERO]);

val calculate_buf_sizes_EQ0 = prove(
  ``cb_t_maxseg < NUMERAL n ==>
     (((NUMERAL n, x, y ,z) =
        calculate_buf_sizes cb_t_maxseg seg_mss bwdp localp rcvbuf sndbuf
                            cb_tf_doing_tstmp arch)) =
     ((NUMERAL n = MIN SB_MAX (roundup y (option_CASE bwdp rcvbuf I))) /\
      (x = bool$LET (\sndbufsize'.
                       if sndbufsize' < y then sndbufsize'
                       else MIN SB_MAX (roundup y sndbufsize'))
                    (option_CASE bwdp sndbuf I)) /\
      (NUMERAL y = MIN cb_t_maxseg (MAX 64 (option_CASE seg_mss MSSDFLT I))) /\
      (z = bool$LET
            (\mss.
               MIN (10 * mss) (MAX (2 * mss) (10 * 1460)))
            (if linux_arch arch then y
             else (y - calculate_tcp_options_len cb_tf_doing_tstmp))))``,
             cheat);
(*
    STRIP_TAC THEN EQ_TAC THEN1
    (STRIP_TAC THEN IMP_RES_TAC calculate_buf_sizes_EQ_implication THEN
     ASM_REWRITE_TAC [TCP1_paramsTheory.MCLBYTES_def]) THEN
  `NUMERAL n = n` by SRW_TAC [][arithmeticTheory.NUMERAL_DEF] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  `NUMERAL y = y` by SRW_TAC [][arithmeticTheory.NUMERAL_DEF] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC [TCP1_paramsTheory.SB_MAX_def] THEN
  LET_ELIM_TAC THEN
  RULE_ASSUM_TAC (fn th =>
                     if is_eq (concl th) then
                       CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def)) th
                     else th) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  ASM_SIMP_TAC bool_ss [calculate_buf_sizes_def,
                        TCP1_paramsTheory.SB_MAX_def] THEN
  LET_ELIM_TAC THEN VAR_EQ_TAC THEN
  Q.UNDISCH_THEN `Abbrev(do_rfc3390 = F)`
                 (SUBST_ALL_TAC o EQF_INTRO o
                  REWRITE_RULE [markerTheory.Abbrev_def]) THEN
  `mss <= t_maxseg'` by SRW_TAC [][Abbr`mss`] THEN
  `mss' <= t_maxseg'` by SRW_TAC [][Abbr`mss'`] THEN
  `t_maxseg' <= cb_t_maxseg` by SRW_TAC [][Abbr`t_maxseg'`] THEN
  `mss' <= cb_t_maxseg` by DECIDE_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `cb_t_maxseg < 262144 /\ cb_t_maxseg < roundup t_maxseg' rcvbufsize'`
     by (SIMP_TAC (srw_ss()) [Abbr`n`] THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  `~(rcvbufsize' < t_maxseg')`
      by (STRIP_TAC THEN
          `~(rcvbufsize' = 0)`
             by (DISCH_THEN SUBST_ALL_TAC THEN
                 REV_FULL_SIMP_TAC (srw_ss()) []) THEN
          `roundup t_maxseg' rcvbufsize' = t_maxseg'`
             by ASM_SIMP_TAC (srw_ss()) [roundup_lt_base] THEN
          metisLib.METIS_TAC [arithmeticTheory.LESS_LESS_EQ_TRANS,
                              arithmeticTheory.LESS_TRANS,
                              prim_recTheory.LESS_REFL]) THEN
  Q.UNDISCH_THEN `Abbrev (mss' = mss)` MP_TAC THEN
  REWRITE_TAC [markerTheory.Abbrev_def] THEN
  POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN REPEAT VAR_EQ_TAC THEN
  FULL_SIMP_TAC (srw_ss()) []
  cheat);
*)

val calculate_buf_sizes_EQ = store_thm(
  "calculate_buf_sizes_EQ",
  ``cb_t_maxseg < NUMERAL n ==>
     (((NUMERAL n, x, y ,z) =
        calculate_buf_sizes cb_t_maxseg seg_mss bwdp localp rcvbuf sndbuf
          cb_tf_doing_tstmp arch)) =
     (let maxseg = MIN cb_t_maxseg (MAX 64 (option_CASE seg_mss MSSDFLT I)) in
      let yval = if linux_arch arch then maxseg
                 else (maxseg - calculate_tcp_options_len cb_tf_doing_tstmp)
      in
        (NUMERAL n = MIN SB_MAX (roundup maxseg (option_CASE bwdp rcvbuf I))) /\
        (x = bool$LET (\sndbufsize'.
                         if sndbufsize' < maxseg then sndbufsize'
                         else MIN SB_MAX (roundup maxseg sndbufsize'))
                    (option_CASE bwdp sndbuf I)) /\
        (y = maxseg) /\
        (z = yval * MIN (10 * yval) (MAX (2 * yval) (10 * 1460))))``,
(*  ASSUME_TAC (SIMP_RULE (bool_ss ++ boolSimps.CONJ_ss) [LET_THM]
                        calculate_buf_sizes_EQ0) THEN
  SIMP_TAC bool_ss [LET_THM] THEN *)
  cheat);
(* FIRST_ASSUM ACCEPT_TAC); *)

val calculate_buf_sizes2 = prove(
  ``~((MIN (NUMERAL cbtm) (MAX 64 (option_CASE seg_mss MSSDFLT I))) =
      NUMERAL tm_out) ==>
    ((rcvbufsize', sndbufsize', NUMERAL tm_out, snd_cwnd) =
     calculate_buf_sizes (NUMERAL cbtm) seg_mss bw_delay_product_for_rt
                         is_local_conn rcvbufsize sndbufsize
                         cb_tf_doing_tstmp arch) ==>
    let maxseg = MIN (NUMERAL cbtm) (MAX 64 (option_CASE seg_mss MSSDFLT I)) in
    let mss = if linux_arch arch then maxseg
              else (maxseg - calculate_tcp_options_len cb_tf_doing_tstmp)
    in
      (rcvbufsize' = NUMERAL tm_out) /\
      (option_CASE bw_delay_product_for_rt rcvbufsize I = NUMERAL tm_out) /\
      (sndbufsize' =
        let sndbuf' = option_CASE bw_delay_product_for_rt sndbufsize I in
          if sndbuf' < NUMERAL tm_out then sndbuf'
          else MIN SB_MAX (roundup t_maxseg'' sndbuf')) /\
      (snd_cwnd = MIN (10 * mss) (MAX (2 * mss) (10 * 1460))) /\
      rcvbufsize' < t_maxseg''``,
      cheat);
(*  SIMP_TAC bool_ss [calculate_buf_sizes_def, LET_THM, pairTheory.UNCURRY,
                    pairTheory.PAIR_EQ, pairTheory.FST, pairTheory.SND] THEN
  REPEAT COND_CASES_TAC THEN FULL_SIMP_TAC (srw_ss()) []); *)

val calculate_buf_sizes2' = prove(
  let val (g, imp) = dest_imp (concl calculate_buf_sizes2)
      val (t1, t2) = dest_imp imp
  in
    mk_imp(g, mk_imp(t2, t1))
  end,
  cheat);
(*  SIMP_TAC bool_ss [calculate_buf_sizes_def, LET_THM, pairTheory.UNCURRY,
                    pairTheory.PAIR_EQ, pairTheory.FST, pairTheory.SND] THEN
  Q.ABBREV_TAC
    `maxseg = MIN (NUMERAL cbtm)
                  (MAX 64 (option_CASE seg_mss MSSDFLT I))` THEN
  Q.ABBREV_TAC
    `maxseg' = rounddown
                 MCLBYTES
                 (maxseg - calculate_tcp_options_len cb_tf_doing_tstmp)` THEN
  Q.ABBREV_TAC `maxseg'' = if linux_arch arch then maxseg else maxseg'` THEN
  Cases_on `NUMERAL tm_out < maxseg''` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN STRIP_TAC THEN
  `maxseg'' < NUMERAL tm_out`
     by FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.NOT_LESS,
                                  arithmeticTheory.LESS_OR_EQ] THEN
  Cases_on `rcvbufsize' = NUMERAL tm_out` THEN ASM_SIMP_TAC (srw_ss()) []); *)


val calculate_buf_sizes_EQ2 = save_thm(
  "calculate_buf_sizes_EQ2",
  DISCH_ALL (IMP_ANTISYM_RULE (UNDISCH calculate_buf_sizes2)
                              (UNDISCH calculate_buf_sizes2')));


(* stuff from testEval.sml *)
val better_real_of_int = save_thm(
  "better_real_of_int",
  LIST_CONJ (map (fn f => SIMP_RULE (srw_ss()) []
                                      (f TCP1_utilsTheory.real_of_int_def))
                 [Q.SPEC `0`, Q.SPEC `int_of_num (NUMERAL n)`,
                  Q.SPEC `~int_of_num(NUMERAL n)`]));
val _ = Phase.add_to_phase 1 "better_real_of_int"


val _ = export_theory()
