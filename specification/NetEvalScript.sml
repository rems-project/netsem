(* A HOL98 specification of TCP *)

(* This file provides an alternate view of the specification,
   one which is more amenable to symbolic evaluation.  Think of
   it as a precompilation phase. *)

(*[ RCSID "$Id: NetEvalScript.sml,v 1.79 2006/10/04 10:23:17 tjr22 Exp $" ]*)

open HolKernel Parse boolLib bossLib

open HolDoc

local open TCP1_hostLTSTheory in end;

val _ = new_theory "NetEval";
val _ = BasicProvers.augment_srw_ss [rewrites [LET_THM]]

open BasicProvers

(* ugly jiggery pokery to retain the reduction relation's uses of let *)
val letsubstitute = new_definition(
  "letsubstitute",
  ``letsubstitute = LET``);


val better_dupfd_1 = prove(
  ``(FD (Num n) < OPEN_MAX_FD /\ fd' = FD ((LEAST) P) /\ p) =
    let doit = (FD(Num n) < OPEN_MAX_FD) in
    let fd'' = if doit then FD ((LEAST) P) else FD 0 in
      doit /\ fd' = fd'' /\ p``,
  SIMP_TAC (std_ss ++ boolSimps.CONJ_ss) [CONJ_ASSOC, LET_THM]);

val sock_wants_to_rexmtX_def = Define`
  sock_wants_to_rexmtX smap shift d sid sock tcp_sock v =
     (sid IN FDOM smap /\ sock = smap ' sid /\
      sock.pr = TCP_PROTO tcp_sock /\
      tcp_sock.cb.tt_rexmt = SOME (Timed((v,shift), d)) /\
      timer_expires d)
`;

val better_timer_tt_rexmtsyn_clause = prove(
  ``(a0 = timer_tt_rexmtsyn_1 /\ a1 = rp_tcp /\ a1' = misc nonurgent /\
     a2 = h with <| socks := socks |++ [(sid,sock)]; oq := oq|> /\
     a3 = Lh_tau /\
     a4 = h with <| socks := socks |++ [(sid,sock')]; oq := oq'|> /\
     sock.pr = TCP_PROTO tcp_sock /\
     tcp_sock.cb.tt_rexmt = SOME (Timed((RexmtSyn,shift), d)) /\
     timer_expires d /\ p) =
    (a0 = timer_tt_rexmtsyn_1 /\ a1 = rp_tcp /\ a1' = misc nonurgent /\
     a2 = h with <| socks := socks |++ [(sid,sock)]; oq := oq|> /\
     sock_wants_to_rexmtX (a2.socks) shift d sid sock tcp_sock RexmtSyn /\
     a3 = Lh_tau /\
     a4 = a2 with <| socks := socks |++ [(sid,sock')]; oq := oq'|> /\
     p)``,
   REWRITE_TAC [sock_wants_to_rexmtX_def] THEN
   EQ_TAC THEN STRIP_TAC THEN
   SRW_TAC [][finite_mapTheory.FUPDATE_LIST_THM] THEN
   TRY (ACCEPT_TAC TRUTH) THEN
   REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
   SRW_TAC [][finite_mapTheory.FUPDATE_LIST_THM]);

val lconj_def = Define`(lconj) x y = (x /\ y)`;
val _ = set_fixity "lconj" (Infixr 400);

val lconj_cong = store_thm(
  "lconj_cong",
  ``(p = p') ==> (p' ==> (q = q')) ==> ((p lconj q) = (p' lconj q'))``,
  REWRITE_TAC [lconj_def] THEN tautLib.TAUT_TAC);

val lconj_rewrites = store_thm(
  "lconj_rewrites",
  ``((T lconj q) = q) /\ ((F lconj q) = F) /\ ((p lconj F) = F) /\
    ((p lconj T) = p)``,
  SRW_TAC [][lconj_def]);
val _ = export_rewrites ["lconj_rewrites"]

val better_sock_wants_to_rexmtX = store_thm(
  "better_sock_wants_to_rexmtX",
  ``sock_wants_to_rexmtX FEMPTY shift d sid sock tcp_sock v = F /\
    sock_wants_to_rexmtX (smap |+ (sid', sock')) shift d sid sock tcp_sock v =
        (sid = sid' /\ sock = sock' /\
         TCP_PROTO tcp_sock = sock'.pr   lconj
         SOME (Timed((v,shift), d)) = tcp_sock.cb.tt_rexmt   lconj
         timer_expires d \/
         sock_wants_to_rexmtX (smap \\ sid') shift d sid sock tcp_sock v)``,
  SRW_TAC [][sock_wants_to_rexmtX_def, lconj_def] THEN
  EQ_TAC THEN STRIP_TAC THEN
  SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [],
    Cases_on `sid = sid'` THEN
    FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.NOT_EQ_FAPPLY,
                              finite_mapTheory.DOMSUB_FAPPLY_NEQ],
    SRW_TAC [][finite_mapTheory.NOT_EQ_FAPPLY,
               finite_mapTheory.DOMSUB_FAPPLY_NEQ]
  ]);

val better_timer_tt_rexmt_clause = prove(
  ``(a0 = timer_tt_rexmt_1 /\ a1 = rp_tcp /\ a1' = misc nonurgent /\
     a2 = h with <| socks := socks |++ [(sid,sock)]; oq := oq |> /\
     a3 = Lh_tau /\
     a4 = h with <| socks := socks |++ [(sid,sock'')]; oq := oq'|> /\
     sock.pr = TCP_PROTO tcp_sock /\
     sock'.pr = TCP_PROTO tcp_sock' /\
     (tcp_sock.st NOTIN {CLOSED; LISTEN; SYN_SENT; CLOSE_WAIT; FIN_WAIT_2;
                        TIME_WAIT} \/
      (tcp_sock.st = LISTEN /\ bsd_arch h.arch)
     ) /\
     tcp_sock.cb.tt_rexmt = SOME (Timed((Rexmt, shift), d)) /\
     timer_expires d /\ p) =
    (a0 = timer_tt_rexmt_1 /\ a1 = rp_tcp  /\ a1' = misc nonurgent /\
     a2 = h with <| socks := socks |++ [(sid,sock)]; oq := oq |> /\
     a3 = Lh_tau /\
     sock_wants_to_rexmtX (a2.socks) shift d sid sock tcp_sock Rexmt /\
     a4 = h with <| socks := socks |++ [(sid,sock'')]; oq := oq'|> /\
     sock'.pr = TCP_PROTO tcp_sock' /\
     (let st = tcp_sock.st in
        ~(st = CLOSED) /\ (~(st = LISTEN) \/ bsd_arch h.arch) /\ ~(st = SYN_SENT) /\
        ~(st = CLOSE_WAIT) /\ ~(st = FIN_WAIT_2) /\ ~(st = TIME_WAIT)) /\ p)``,
  REWRITE_TAC [sock_wants_to_rexmtX_def,
               pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY,
               DE_MORGAN_THM, LET_THM] THEN BETA_TAC  THEN
  EQ_TAC THEN STRIP_TAC THEN
  SRW_TAC [][finite_mapTheory.FUPDATE_LIST_THM] THEN
  TRY (ACCEPT_TAC TRUTH) THEN
  REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  SRW_TAC [][finite_mapTheory.FUPDATE_LIST_THM]) handle e => Raise e;

val better_timer_tt_persist_clause = prove(
  ``(a0 = timer_tt_persist_1 /\ a1' = rp_tcp /\ a1 = misc nonurgent /\
     a2 = h with <|socks := socks |++ [(sid,sock)]; oq := oq|> /\
     a3 = Lh_tau /\
     a4 = h with <|socks := socks |++ [(sid,sock'')]; oq := oq'|> /\
     sock.pr = TCP_PROTO tcp_sock /\ sock'.pr = TCP_PROTO tcp_sock' /\
     tcp_sock.cb.tt_rexmt = SOME (Timed ((Persist,shift),d)) /\
     timer_expires d /\ p) =
    (a0 = timer_tt_persist_1 /\ a1' = rp_tcp /\ a1 = misc nonurgent /\
     a2 = h with <|socks := socks |++ [(sid,sock)]; oq := oq|> /\
     a3 = Lh_tau /\
     sock_wants_to_rexmtX (a2.socks) shift d sid sock tcp_sock Persist /\
     sock'.pr = TCP_PROTO tcp_sock' /\
     a4 = h with <| socks := socks |++ [(sid,sock'')]; oq := oq'|> /\
     p)``,
  REWRITE_TAC [sock_wants_to_rexmtX_def] THEN EQ_TAC THEN STRIP_TAC THEN
  SRW_TAC [][finite_mapTheory.FUPDATE_LIST_THM] THEN
  TRY (ACCEPT_TAC TRUTH) THEN
  REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  SRW_TAC [][finite_mapTheory.FUPDATE_LIST_THM]);

val sockcbfld_expires_def = Define`
  sockcbfld_expires smap sid sock tcp_sock d fld =
    (sid IN FDOM smap /\ sock = smap ' sid /\ sock.pr = TCP_PROTO tcp_sock /\
     fld (tcp_sock.cb) = SOME (Timed((), d)) /\ timer_expires d)
`;

val better_sockcbfld_expires = store_thm(
  "better_sockcbfld_expires",
  ``sockcbfld_expires FEMPTY sid sock tcp_sock d fld = F /\
    sockcbfld_expires (smap |+ (sid', sock')) sid sock tcp_sock d fld =
      (sid = sid' /\ sock = sock' /\
       TCP_PROTO tcp_sock = sock'.pr lconj
       SOME (Timed((), d)) = fld (tcp_sock.cb) lconj timer_expires d \/
       sockcbfld_expires (smap \\ sid') sid sock tcp_sock d fld)``,
  SRW_TAC [][sockcbfld_expires_def, EQ_IMP_THM, lconj_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THENL [
    Cases_on `sid = sid'` THEN
    FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.NOT_EQ_FAPPLY,
                              finite_mapTheory.DOMSUB_FAPPLY_NEQ],
    SRW_TAC [][finite_mapTheory.NOT_EQ_FAPPLY,
               finite_mapTheory.DOMSUB_FAPPLY_NEQ]
  ]);

val better_timer_tt_keep_clause = prove(
  ``(a0 = timer_tt_keep_1 /\ a1' = rp_tcp /\ a1 = network nonurgent /\
     a2 = h with
          <|socks := socks |++
                     [(sid, Sock(SOME fid,sf,
                                 SOME i1,SOME p1,SOME i2,SOME p2,
                                 es,cantsndmore,cantrcvmore,
                                 TCP_Sock
                                    (st,cb,NONE,sndq,sndurp,rcvq,
                                     rcvurp,iobc)))];
            oq := oq|> /\
     a3 = Lh_tau /\
     a4 = h with <|socks := socks |++ [(sid, s2)]; oq := oq'|> /\
     cb.tt_keep = SOME (Timed ((),d)) /\ timer_expires d /\ p) =
    (a0 = timer_tt_keep_1 /\ a1' = rp_tcp /\ a1 = network nonurgent /\
     a2 = h with
          <|socks := socks |++
                     [(sid, Sock(SOME fid,sf,
                                 SOME i1,SOME p1,SOME i2,SOME p2,
                                 es,cantsndmore,cantrcvmore,
                                 TCP_Sock
                                    (st,cb,NONE,sndq,sndurp,rcvq,
                                     rcvurp,iobc)))];
            oq := oq|> /\
     a3 = Lh_tau /\
     sockcbfld_expires (a2.socks) sid
                       (Sock(SOME fid,sf,
                                 SOME i1,SOME p1,SOME i2,SOME p2,
                                 es,cantsndmore,cantrcvmore,
                                 TCP_Sock
                                      (st,cb,NONE,sndq,sndurp,rcvq,
                                       rcvurp,iobc)))
                       (TCP_Sock0(st,cb,NONE,sndq,sndurp,rcvq,
                                 rcvurp,iobc)) d
                       tcpcb_tt_keep /\
     a4 = h with <|socks := socks |++ [(sid, s2)]; oq := oq'|> /\
     p)``,
  REWRITE_TAC [sockcbfld_expires_def] THEN EQ_TAC THEN STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.FUPDATE_LIST_THM,
                            TCP1_hostTypesTheory.Sock_def,
                            TCP1_hostTypesTheory.TCP_Sock0_def,
                            TCP1_hostTypesTheory.TCP_Sock_def] THEN
  FIRST_ASSUM ACCEPT_TAC);

val better_timer_tt_2msl = prove(
  ``(a0 = timer_tt_2msl_1 /\ a1' = rp_tcp /\ a1 = misc nonurgent /\
     a2 = h with socks := socks |++ [(sid,sock)] /\
     a3 = Lh_tau /\
     a4 = h with socks := socks |++ [(sid,sock')] /\
     sock.pr = TCP_PROTO tcp_sock /\
     tcp_sock.cb.tt_2msl = SOME (Timed ((),d)) /\
     timer_expires d /\ p) =
    (a0 = timer_tt_2msl_1 /\ a1' = rp_tcp /\ a1 = misc nonurgent /\
     a2 = h with socks := socks |++ [(sid,sock)] /\
     a3 = Lh_tau /\
     sockcbfld_expires (a2.socks) sid sock tcp_sock d tcpcb_tt_2msl /\
     a4 = h with socks := socks |++ [(sid,sock')] /\ p)``,
  REWRITE_TAC [sockcbfld_expires_def] THEN EQ_TAC THEN STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.FUPDATE_LIST_THM] THEN
  SRW_TAC [][] THEN FIRST_ASSUM ACCEPT_TAC);

val better_timer_tt_delack = prove(
  ``(a0 = timer_tt_delack_1 /\ a1' = rp_tcp /\ a1 = misc nonurgent /\
     a2 = h with <|socks := socks |++ [(sid,sock)]; oq := oq|> /\
     a3 = Lh_tau /\
     a4 = h with <|socks := socks |++ [(sid,sock'')]; oq := oq'|> /\
     sock.pr = TCP_PROTO tcp_sock /\ sock'.pr = TCP_PROTO tcp_sock' /\
     tcp_sock.cb.tt_delack = SOME (Timed ((),d)) /\ timer_expires d /\ p) =
    (a0 = timer_tt_delack_1 /\ a1' = rp_tcp /\ a1 = misc nonurgent /\
     a2 = h with <|socks := socks |++ [(sid,sock)]; oq := oq|> /\
     a3 = Lh_tau /\
     sockcbfld_expires (a2.socks) sid sock tcp_sock d tcpcb_tt_delack /\
     sock'.pr = TCP_PROTO tcp_sock' /\
     a4 = h with <|socks := socks |++ [(sid,sock'')]; oq := oq'|> /\
     p)``,
  REWRITE_TAC [sockcbfld_expires_def] THEN EQ_TAC THEN STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.FUPDATE_LIST_THM] THEN
  SRW_TAC [][] THEN FIRST_ASSUM ACCEPT_TAC);

val better_timer_tt_conn_est = prove(
  ``(a0 = timer_tt_conn_est_1 /\ a1' = rp_tcp /\ a1 = misc nonurgent /\
     a2 = h with <|socks := socks |++ [(sid,sock)]; oq := oq|> /\
     a3 = Lh_tau /\
     a4 = h with <|socks := socks |++ [(sid,sock')]; oq := oq'|> /\
     sock.pr = TCP_PROTO tcp_sock /\
     tcp_sock.cb.tt_conn_est = SOME (Timed ((),d)) /\
     timer_expires d /\ p) =
    (a0 = timer_tt_conn_est_1 /\ a1' = rp_tcp /\ a1 = misc nonurgent /\
     a2 = h with <|socks := socks |++ [(sid,sock)]; oq := oq|> /\
     a3 = Lh_tau /\
     sockcbfld_expires (a2.socks) sid sock tcp_sock d tcpcb_tt_conn_est /\
     a4 = h with <|socks := socks |++ [(sid,sock')]; oq := oq'|> /\
     p)``,
  REWRITE_TAC [sockcbfld_expires_def] THEN EQ_TAC THEN STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.FUPDATE_LIST_THM] THEN
  SRW_TAC [][] THEN FIRST_ASSUM ACCEPT_TAC);

val better_timer_tt_fin_wait_2 = prove(
  ``(a0 = timer_tt_fin_wait_2_1 /\ a1' = rp_tcp /\ a1 = misc nonurgent /\
     a2 = h with socks := socks |++ [(sid,sock)] /\
     a3 = Lh_tau /\
     a4 = h with socks := socks |++ [(sid,sock')] /\
     sock.pr = TCP_PROTO tcp_sock /\
     tcp_sock.cb.tt_fin_wait_2 = SOME (Timed ((),d)) /\
     timer_expires d /\ p) =
    (a0 = timer_tt_fin_wait_2_1 /\ a1' = rp_tcp /\ a1 = misc nonurgent /\
     a2 = h with socks := socks |++ [(sid,sock)] /\
     a3 = Lh_tau /\
     sockcbfld_expires (a2.socks) sid sock tcp_sock d tcpcb_tt_fin_wait_2 /\
     a4 = h with socks := socks |++ [(sid,sock')] /\ p)``,
  REWRITE_TAC [sockcbfld_expires_def] THEN EQ_TAC THEN STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.FUPDATE_LIST_THM] THEN
  SRW_TAC [][] THEN FIRST_ASSUM ACCEPT_TAC);

val sock_might_deliver_def = Define`
  sock_might_deliver smap sid sock arch =
    (sid IN FDOM smap /\ smap ' sid = sock /\
     (?tcp_sock. sock.pr = TCP_PROTO tcp_sock /\
                 (tcp_sock.st IN {ESTABLISHED; CLOSE_WAIT; FIN_WAIT_1;
                                  FIN_WAIT_2; CLOSING; LAST_ACK; TIME_WAIT} /\
                  tcp_sock.cb.snd_una <> tcp_sock.cb.iss \/
                  tcp_sock.st IN {SYN_SENT; SYN_RECEIVED} /\ sock.cantsndmore
                                         /\ tcp_sock.cb.tf_shouldacknow)))
`;

val better_deliver_out_1a = prove(
  ``(a0 = deliver_out_1 /\ a1' = rp_tcp /\ a1 = network nonurgent /\
     a2 = h with <|socks := socks |++ [(sid,sock)]; oq := oq|> /\
     a3 = Lh_tau /\
     a4 = h with <|socks := socks |++ [(sid,sock')]; oq := oq'|> /\
     sid NOTIN FDOM socks /\
     sock =
     Sock
       (fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,
        es,cantsndmore,cantrcvmore,TCP_PROTO tcp_sock) /\
     tcp_sock = TCP_Sock0(st,cb,NONE,sndq,sndurp,rcvq,rcvurp,iobc) /\
     (st IN {ESTABLISHED; CLOSE_WAIT; FIN_WAIT_1; FIN_WAIT_2; CLOSING;
             LAST_ACK; TIME_WAIT} /\ cb.snd_una <> cb.iss \/
      st IN {SYN_SENT; SYN_RECEIVED} /\ cantsndmore /\ cb.tf_shouldacknow) /\ p) =
    (a0 = deliver_out_1 /\ a1' = rp_tcp /\ a1 = network nonurgent /\
     a2 = h with <|socks := socks |++ [(sid,sock)]; oq := oq|> /\
     a3 = Lh_tau /\
     sock_might_deliver a2.socks sid sock a2.arch /\
     a4 = h with <|socks := socks |++ [(sid,sock')]; oq := oq'|> /\
     sid NOTIN FDOM socks /\
     sock =
     Sock
       (fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,
        es,cantsndmore,cantrcvmore,TCP_PROTO tcp_sock) /\
     tcp_sock = TCP_Sock0(st,cb,NONE,sndq,sndurp,rcvq,rcvurp,iobc) /\ p)``,
  REWRITE_TAC [sock_might_deliver_def, TCP1_hostTypesTheory.Sock_def,
               TCP1_hostTypesTheory.TCP_Sock0_def,
               finite_mapTheory.FUPDATE_LIST_THM] THEN
  EQ_TAC THEN STRIP_TAC THEN
  Q.ABBREV_TAC `myset = {ESTABLISHED; CLOSE_WAIT; FIN_WAIT_1; FIN_WAIT_2;
                         CLOSING; LAST_ACK; TIME_WAIT}` THEN
  POP_ASSUM (K ALL_TAC) THEN REPEAT BasicProvers.VAR_EQ_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val better_sock_might_deliver = store_thm(
  "better_sock_might_deliver",
  ``sock_might_deliver FEMPTY sid sock arch = F /\
    sock_might_deliver (smap |+ (sid', sock')) sid sock arch =
      (sid' = sid /\ sock' = sock /\
       (?tcp_sock.
           sock.pr = TCP_PROTO tcp_sock /\
           (tcp_sock.st IN {ESTABLISHED; CLOSE_WAIT; FIN_WAIT_1;
                            FIN_WAIT_2; CLOSING; LAST_ACK;
                            TIME_WAIT} /\
            tcp_sock.cb.snd_una <> tcp_sock.cb.iss \/
            tcp_sock.st IN {SYN_SENT; SYN_RECEIVED} /\
            sock.cantsndmore /\ tcp_sock.cb.tf_shouldacknow)) \/
       sock_might_deliver (smap \\ sid') sid sock arch)``,
  REWRITE_TAC [sock_might_deliver_def] THEN
  Q.ABBREV_TAC `myset = {ESTABLISHED; CLOSE_WAIT; FIN_WAIT_1; FIN_WAIT_2;
                         CLOSING; LAST_ACK; TIME_WAIT}` THEN
  POP_ASSUM (K ALL_TAC) THEN
  SRW_TAC [][EQ_IMP_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.DOMSUB_FAPPLY_NEQ,
                            finite_mapTheory.NOT_EQ_FAPPLY] THEN
  Cases_on `sid = sid'` THEN
  FULL_SIMP_TAC (srw_ss()) [finite_mapTheory.DOMSUB_FAPPLY_NEQ,
                            finite_mapTheory.NOT_EQ_FAPPLY]);

val sock_has_quad_def = Define`
  sock_has_quad fm k s (i1,p1,i2,p2) =
    (k IN FDOM fm /\ fm ' k = s /\
     s.is1 = SOME i1 /\ s.ps1 = SOME p1 /\
     s.is2 = SOME i2 /\ s.ps2 = SOME p2)
`;

val better_deliver_in_3 = prove(
  ``(a0 = deliver_in_3 /\ a1 = rp_tcp /\ a2 = network nonurgent /\
     a3 = h with <| socks := socks |++ [(sid,sock)];
                    iq := iq; oq := oq |> /\
     a4 = Lh_tau /\ a5 = h' /\ sid NOTIN FDOM socks /\
     sock.pr = TCP_PROTO tcp_sock /\ sane_socket sock /\
     dequeue_conj /\
     seg_conj /\
     sock.is1 = SOME i1 /\ sock.ps1 = SOME p1 /\
     sock.is2 = SOME i2 /\ sock.ps2 = SOME p2 /\ p) =
    (a0 = deliver_in_3 /\ a1 = rp_tcp /\ a2 = network nonurgent /\
     a4 = Lh_tau /\ a5 = h' /\
     sock_has_quad a3.socks sid sock (i1,p1,i2,p2) /\
     a3 = h with <| socks := socks |++ [(sid, sock)];
                    iq := iq; oq := oq |> /\
     sid NOTIN FDOM socks /\
     sock.pr = TCP_PROTO tcp_sock /\ sane_socket sock /\
     dequeue_conj /\ seg_conj /\ p)``,
  REWRITE_TAC [sock_has_quad_def] THEN EQ_TAC THEN
  SRW_TAC [][finite_mapTheory.FUPDATE_LIST_THM])


val better_sock_has_quad = store_thm(
  "better_sock_has_quad",
  ``sock_has_quad FEMPTY k s (i1,p1,i2,p2) = F /\
    sock_has_quad (fm |+ (k0, s0)) k s (i1,p1,i2,p2) =
      (k0 = k /\ s = s0 /\
       s0.is1 = SOME i1 /\ s0.ps1 = SOME p1 /\
       s0.is2 = SOME i2 /\ s0.ps2 = SOME p2 \/
       sock_has_quad (fm \\ k0) k s (i1,p1,i2,p2))``,
  SRW_TAC [boolSimps.DNF_ss][sock_has_quad_def] THEN
  Cases_on `k = k0` THEN
  SRW_TAC [][finite_mapTheory.FAPPLY_FUPDATE_THM,
             finite_mapTheory.DOMSUB_FAPPLY_THM] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []);

val _ = print "About to mechanically rework tcp_output_required to make it\n"
val _ = print "work better with deliver_out_1\n"

val tcpcb_ty = ``:tcpcb``
val cb_t = mk_var("cb", tcpcb_ty)
val tt_rexmt_accessor = ``TCP1_hostTypes$tcpcb_tt_rexmt``
val snd_nxt_accessor = ``TCP1_hostTypes$tcpcb_snd_nxt``
val transform_output_required  = let
  fun recurse_replace tf t =
      tf t
      handle HOL_ERR _ => let
               val (abstn, value) = dest_let t
               val (v, body) = dest_abs abstn
             in
               mk_let(mk_abs(v, recurse_replace tf body), value)
             end
  fun simp t = rhs (concl (SIMP_CONV (srw_ss()) [] t))
  fun transform_cond_arm c = let
    open pairSyntax
  in
    if optionSyntax.is_some c then let
        val f = optionSyntax.dest_some c
        val (v, bdy) = dest_abs f
        val rexmt = simp (mk_comb(tt_rexmt_accessor, bdy))
        val snd_nxt = simp (mk_comb(snd_nxt_accessor, bdy))
      in
        list_mk_pair([T, mk_abs(v, rexmt), mk_abs(v, snd_nxt)])
      end
    else
      list_mk_pair([F, mk_abs(cb_t, mk_comb(tt_rexmt_accessor, cb_t)),
                    mk_abs(cb_t, mk_comb(snd_nxt_accessor, cb_t))])
  end
  fun replace_conds tm = let
    val (g, t, e) = dest_cond tm
  in
    mk_cond(g,
            replace_conds t handle HOL_ERR _ => transform_cond_arm t,
            replace_conds e handle HOL_ERR _ => transform_cond_arm e)
  end
  fun expand_lets t =
      if is_let t then
        expand_lets (Term.beta_conv(mk_comb(rand (rator t), rand t)))
      else t



  fun transform t = let
    val (bdy_abs, value) = dest_let t
    val (v, body) = dest_abs bdy_abs
    val optty = optionSyntax.dest_option (type_of v)
    val (dom,rng) = dom_rng optty
    val _ = dom = tcpcb_ty andalso rng = tcpcb_ty orelse failwith "foo"
    val value' = replace_conds (expand_lets value)
    val v' = mk_var(#1 (dest_var v), type_of value')
    val body_comps = pairSyntax.strip_pair body
    val body_comps' = map (fn t => if t = v then v' else t) body_comps
    val body' = pairSyntax.list_mk_pair body_comps'
  in
    mk_let(mk_abs(v', body'), value')
  end
in
  recurse_replace transform
end

val tcp_output_required_alt_def = new_definition(
  "tcp_output_required_alt_def",
  let
    val base_t = concl TCP1_auxFnsTheory.tcp_output_required_def
    val (l, r) = dest_eq (#2 (strip_forall base_t))
    val (f, args) = strip_comb l
    val r' = transform_output_required r
    val ty' = list_mk_fun(map type_of args, type_of r')
    val f' = mk_var("tcp_output_required_alt", ty')
  in
    mk_eq(list_mk_comb(f', args), r')
  end)
val _ = Phase.add_to_phase 2 "tcp_output_required_alt_def";
val _ = print "Defined tcp_output_required_alt function \n";

val alt_ty = type_of (prim_mk_const {Name = "tcp_output_required_alt",
                                     Thy = "NetEval"})
val (argtys, ret_ty) = strip_fun alt_ty
val result_tys = pairSyntax.strip_prod ret_ty
val updates = List.drop(result_tys, 2)
val tt_rexmt_upd_ty = hd updates
val snd_nxt_upd_ty = hd (tl updates)
val persist = mk_var("persist", bool)
val tt_rexmt = mk_var("tt_rexmt_upd", tt_rexmt_upd_ty)
val snd_nxt = mk_var("snd_nxt_upd", snd_nxt_upd_ty)
val sock0 = ``let cb = tcp_sock.cb in
              let new_tt_rexmt = ^tt_rexmt cb in
              let new_snd_nxt = ^snd_nxt cb
              in
                sock with
                  pr := TCP_PROTO (tcp_sock with
                                     cb := cb with
                                       <| tt_rexmt := new_tt_rexmt;
                                          snd_nxt := new_snd_nxt |>)``

fun replace_tcp_output_required t = let
  (* t is the let clause of the form
        let (do_output, persist_fun) = tcp_output_required args
     want to replace this with a term of the form
        let (do_output, persist, rexmt_upd, snd_nxt_upd) =
                tcp_output_required_alt args
     where do_output gets the same value, persist is true iff
     persist_fun was SOME f, and rexmt_upd and snd_nxt_upd are functions
     that embody the changes f would make to those fields of a tcpcb.
   *)
  open pairSyntax
  val (absn, value) = dest_let t
  val (_, args) = strip_comb value
  val (doo_pfun, bdy) = dest_pabs absn
  val (do_output, pfun) = dest_pair doo_pfun
  val (c1, c2) = dest_conj bdy
  val c1' = mk_disj(do_output, persist)
  val c2' = mk_comb(rator c2, sock0)
in
  mk_let(mk_pabs(list_mk_pair([do_output,persist,tt_rexmt,snd_nxt]),
                 mk_conj(c1' ,c2')),
         list_mk_comb(``tcp_output_required_alt``, args))
end

val _ = print "Finding deliver_out_1 clause\n"
val deliver_out_1_clause =
    valOf (List.find (free_in ``tcp_output_required``)
                     (strip_disj
                        (rhs
                           (#2 (strip_forall
                                  (concl
                                     TCP1_hostLTSTheory.host_redn0_cases))))))
val deliver_out_1_conj =
    valOf (List.find (free_in ``tcp_output_required``)
                     (strip_conj (#2 (strip_exists deliver_out_1_clause))))
val new_conj = replace_tcp_output_required deliver_out_1_conj

val _ = print "Proving new and old clauses equivalent\n"

fun differing_pairs acc = let
  val (t1, t2) = hd acc
in
  case (dest_term t1, dest_term t2) of
    (COMB(f,x), COMB(g,y)) => let
    in
      case Term.compare(f, g) of
        EQUAL => differing_pairs ((x,y)::acc)
      | _ => differing_pairs((f, g)::acc)
    end
  | (LAMB(v1,b1), LAMB(v2, b2)) => let
      val nv = variant (union (free_vars b1) (free_vars b2)) v1
    in
      differing_pairs((subst[v1 |-> nv] b1, subst[v2 |-> nv] b2)::acc)
    end
  | _ => acc
end

val mylet_thm = prove(
  ``(!x. f (LET f' x) = g (LET g' x)) ==>
    (f (LET f' v) = g (LET g' v))``,
  SIMP_TAC (srw_ss()) []);

fun mylet_tac (asl, w) = let
  val (l,r) = dest_eq w
  val (f, x) = dest_comb l
  val (g, y) = dest_comb r
  val (f', x') = dest_let x
  val (g', y') = dest_let y
  val _ = Term.compare (x', y') = EQUAL orelse raise failwith "foo"
  val var = bvar f' handle HOL_ERR _ => genvar (type_of x')
in
  MATCH_MP_TAC mylet_thm THEN
  CONV_TAC (RAND_CONV (ALPHA_CONV var)) THEN
  TRY (CONV_TAC (HO_REWR_CONV pairTheory.FORALL_PROD)) THEN
  REPEAT GEN_TAC THEN
  CONV_TAC (BINOP_CONV (RAND_CONV (REWR_CONV LET_THM THENC
                                   pairLib.GEN_BETA_CONV)))
end (asl, w)

fun sock_eq_tac (asl, w) = let
  fun sel t = type_of t = ``:socket`` andalso not (is_var t)
  val set = find_maximal_terms sel w
  val _ = HOLset.numItems set = 2 orelse failwith "foo"
  val s = Listsort.sort (measure_cmp term_size) (HOLset.listItems set)
  val subgoal = mk_eq(hd (tl s), hd s)
in
  SUBGOAL_THEN subgoal (fn th => SUBST_ALL_TAC th THEN REWRITE_TAC [])
end(asl,w)

val _ = print "Proving rewrite ... "
fun with_ctxt t =
    ``sock = Sock (fids, sf, is1, ps1, is2, ps2, es,
                   cantsndmore, cantrcvmore, TCP_PROTO tcp_sock) /\
      P /\ Q /\ ^t``


val leading_conj_elim =
    tautLib.TAUT_PROVE ``((p /\ q) = (p /\ r)) = (p ==> (q = r))``
val better_deliver_out_1b = prove(
  mk_eq(with_ctxt deliver_out_1_conj, with_ctxt new_conj),
  REWRITE_TAC [TCP1_hostTypesTheory.Sock_def, leading_conj_elim] THEN
  REPEAT STRIP_TAC THEN
  REPEAT VAR_EQ_TAC THEN
  REWRITE_TAC [tcp_output_required_alt_def,
               TCP1_auxFnsTheory.tcp_output_required_def] THEN
  ONCE_REWRITE_TAC [LET_THM] THEN
  REPEAT mylet_tac THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
  SIMP_TAC std_ss [LET_THM] THEN
  sock_eq_tac THEN
  SRW_TAC [][TCP1_hostTypesTheory.socket_component_equality] THEN
  SRW_TAC [][TCP1_hostTypesTheory.tcp_socket_component_equality] THEN
  SRW_TAC [][TCP1_hostTypesTheory.tcpcb_component_equality]);
val _ = print "done\n"

(* ----------------------------------------------------------------------
    code to remove a general class of inefficient idiom,

      where stuff like
           (?fldv1 fldv2 fldv4 fldv5.
                 v = <| fld1 := fldv1; fld2 := fldv2;
                        fld3 := v3   ; fld4 := fldv4;
                        fld5 := fldv5; fld6 := v6  |>)
      appears.  This should be simplified to
           (v.fld3 = v3) /\ (v.fld6 = v6)
      removing all of the existential quantifiers in advance, rather than
      forcing the evaluation code to do it itself.  This idiom is common
      (rife, even) in deliver_in_* where it is used to specify certain
      fields of segments that are pulled out of the input queue.

      The idiom may have its maintainability or readability advantages
      but it's not good for execution.

   ---------------------------------------------------------------------- *)

fun bigrec_subtypes ss thyname tyname = let
  val con = prim_mk_const{Name = tyname, Thy = thyname}
  val ty = type_of con
  val (argtys, _) =  strip_fun ty
  fun foldthis(ty,ss) = let
    val {Tyop, Thy, ...} = dest_thy_type ty
  in
    if is_substring GrammarSpecials.bigrec_subdivider_string Tyop then let
        val {rewrs, convs} = TypeBase.simpls_of ty
        val ss' = simpLib.SSFRAG {convs = convs, rewrs = rewrs,
                                  ac = [], dprocs = [], filter = NONE,
                                  congs = [], name = NONE}
      in
        simpLib.merge_ss [ss, ss']
      end
    else
      ss
  end
in
  List.foldl foldthis ss argtys
end

fun remove_ugly_existential_idiom t = let
  (* simp needs to resolve multiple field references, and then do a whole
     bunch of unwinds *)
  val notapp_err = mk_HOL_ERR "NetEval" "remove_ugly_existential_idiom"
                              "not applicable"
  val (exvars, body) = strip_exists t
  val _ = is_eq body andalso not (null exvars) orelse
          raise notapp_err
  val (l,r,ty) = dest_eq_ty body
  val _ = is_var l orelse is_var r orelse raise notapp_err
  val {Thy,Tyop,...} = dest_thy_type ty
  val compeqth_name = Tyop ^ "_component_equality"
  val compeqth = DB.fetch Thy compeqth_name
      handle HOL_ERR _ => raise notapp_err
  val {convs,rewrs} = TypeBase.simpls_of ty
  val ss0 = simpLib.SSFRAG {convs = convs, rewrs = rewrs,
                            ac = [], filter = NONE, dprocs = [],
                            congs = [], name = NONE}
  val ss = bigrec_subtypes ss0 Thy Tyop
in
  STRIP_QUANT_CONV (REWR_CONV compeqth) THENC
  simpLib.SIMP_CONV (bool_ss ++ combinSimps.COMBIN_ss ++ ss) [] THENC
  REPEATC Unwind.UNWIND_EXISTS_CONV
end t

val REMOVE_UGLY_ss = simpLib.SSFRAG {
  ac = [], congs = [], convs = [{conv = K (K remove_ugly_existential_idiom),
                                 key = SOME ([], ``?x. P x``),
                                 name = "remove_ugly_existential_idiom",
                                 trace = 2}],
  dprocs = [], filter = NONE,
  rewrs = [], name = SOME "REMOVE_UGLY"};


fun bad_sock_exists t = let
  val (v, body) = dest_exists t
  fun socktype ty = mem ty [``:socket``, ``:tcp_socket``]
  val _ =   socktype (type_of v) orelse raise mk_HOL_ERR "" "" ""
  val sock_ts = find_terms (fn t => socktype (type_of t) andalso
                                    free_in v t) body
  fun bad_term t = let
    val (f, args) = strip_comb t
  in
    length args = 2 andalso v = last args andalso
    is_const f andalso
    is_substring "_fupd" (#1 (dest_const f))
  end
  fun good_fmap t = let
    val (fm, kv) = finite_mapSyntax.dest_fupdate t
  in
    (let
       val (k, u) = pairSyntax.dest_pair kv
     in
       u = v
     end handle HOL_ERR _ => false) orelse
    good_fmap fm
  end handle HOL_ERR _ => false
  fun good_term t = let
    val (l, r) = dest_eq t
  in
    l = v orelse r = v orelse
    (finite_mapSyntax.is_fmap_ty (type_of l) andalso
     (good_fmap l orelse good_fmap r))
  end handle HOL_ERR _ => false
in
  exists bad_term sock_ts andalso
  not (can (find_term good_term) body)
end handle HOL_ERR _ => false

fun deal_to_bad_sock_exists t =
    if bad_sock_exists t then
      (HO_REWR_CONV TCP1_hostTypesTheory.EXISTS_socket ORELSEC
       HO_REWR_CONV TCP1_hostTypesTheory.EXISTS_tcp_socket) t
    else NO_CONV t

val deal_to_bad_socks =
    simpLib.SSFRAG {ac = [],
                    convs = [{conv = K (K deal_to_bad_sock_exists),
                              key = SOME ([], ``?s:'a. P s``),
                              name = "deal_to_bad_socks", trace = 2}],
                    congs = [], dprocs = [], filter = NONE, rewrs = [],
                    name = NONE}

(* ----------------------------------------------------------------------
    A brand new, tip-top method for ridding the world of ugly finite map
    bindings
  ---------------------------------------------------------------------- *)

val fmscan_def = Define`
  fmscan fm k v = (k IN FDOM fm /\ fm ' k = v)
`;

val better_fmscan = store_thm(
  "better_fmscan",
  ``fmscan FEMPTY k v = F /\
    fmscan (fm |+ (k', v')) k v = (k = k' /\ v = v' \/
                                   fmscan (fm \\ k') k v)``,
  SRW_TAC [][fmscan_def] THEN
  Cases_on `k = k'` THEN
  SRW_TAC [][finite_mapTheory.DOMSUB_FAPPLY_THM,
             finite_mapTheory.FAPPLY_FUPDATE_THM] THEN
  PROVE_TAC []);

fun topdown_find_terms P t = let
  (* find all terms satisfying P except those that are subterms of terms
     already satisfying P *)
  fun recurse acc t =
      if P t then HOLset.add(acc, t)
      else case dest_term t of
             COMB(t1, t2) => recurse (recurse acc t2) t1
           | LAMB(v, bdy) => recurse acc bdy
           | _ => acc
in
  recurse empty_tmset t
end

exception TrivialBind
fun big_fat_warning fmt t = let
  fun is_rname t = type_of t = ``:rule_ids`` andalso is_const t
  val rulename = #1 (dest_const (find_term is_rname t))
in
  print "*****\n";
  print ("***** Very upset about fmap binding in "^rulename^":\n");
  print ("***** "^term_to_string fmt^"\n");
  print "*****\n"
end

fun UNBETA_LIST tlist =
    case tlist of
      [] => ALL_CONV
    | (t::ts) => UNBETA_CONV t THENC RATOR_CONV (UNBETA_LIST ts)

fun strip_fupd t = let
  fun recurse acc t = let
    val (b, kv) = finite_mapSyntax.dest_fupdate t
  in
    recurse (kv::acc) b
  end handle HOL_ERR _ => (t, List.rev acc)
in
  recurse [] t
end

val domsub_t = ``finite_map$fdomsub``
val dest_domsub = let
  val ddomsub_exn = mk_HOL_ERR "finite_mapSyntax" "dest_domsub"
                               "Term not a domain subtraction"
in
  dest_binop domsub_t ddomsub_exn
end
val is_domsub = can dest_domsub
fun mk_domsub(fm, k) = let
  val (dom,rng) = finite_mapSyntax.dest_fmap_ty (type_of fm)
in
  list_mk_comb(Term.inst[alpha |-> dom, beta |-> rng] domsub_t, [fm, k])
end


fun split_at cmp e list = let
  fun recurse acc [] = raise Fail "fatal error 90210"
    | recurse acc (h::t) = if cmp(e, h) = EQUAL then (List.rev acc, t)
                           else recurse (h::acc) t
in
  recurse [] list
end

fun is_uninclusion v t = let
  val in_t = dest_neg t
  val (f, args) = strip_comb in_t
  val _ = assert (same_const pred_setSyntax.in_tm) f
  val _ = length args = 2 orelse failwith "foo"
  val (fdom, arg) = dest_comb (hd (tl args))
in
  same_const finite_mapSyntax.fdom_t fdom andalso
  Term.compare(arg, v) = EQUAL
end handle HOL_ERR _ => false

fun fmt_ok fmt t = let
  (* check that t is an acceptable variant of fmt.
       fmt is of the form  var |+ (k1, v1) |+ (k2, v2) ...
       t is acceptable if of the form
                           var |+ (k1, v1') |+ (k2, v2') ..
       or if there is just one (k1, v1) pair in fmt, and t is of
       the form
                           var \\ k1
       or if there is just one (k1, v1) pair in fmt, and t is of the
       form
                           ~(k1 IN FDOM var)
  *)
  val (b, kvs) = strip_fupd fmt
  val (ks, _) = ListPair.unzip (map pairSyntax.dest_pair kvs)
in
  (length ks = 1 andalso
   let val (fm, k) = dest_domsub t
   in
     Term.compare(fm, b) = EQUAL andalso Term.compare(k, hd ks) = EQUAL
   end handle HOL_ERR _ => false) orelse
  (length ks = 1 andalso is_uninclusion b t andalso
   let val t0 = dest_neg t
       val (_, args) = strip_comb t0
   in
     Term.compare (hd args, hd ks) = EQUAL andalso
     Term.compare (rand (hd (tl args)), b) = EQUAL
   end handle HOL_ERR _ => false) orelse
  (let val (b', kvs') = strip_fupd t
       val (ks', _) = ListPair.unzip (map pairSyntax.dest_pair kvs')
   in
     length ks = length ks' andalso
     ListPair.all (fn (t1, t2) => Term.compare(t1, t2) = EQUAL) (ks, ks')
   end)
end

fun push_exists_in_then c t = let
  val (_, bod) = dest_exists t
in
  if is_exists bod then SWAP_EXISTS_CONV THENC
                        BINDER_CONV (push_exists_in_then c)
  else c
end t


val fmscan_t = prim_mk_const{ Name = "fmscan", Thy = "NetEval"}
fun fmap_exists_conv t = let
  val (v, body0) = dest_exists t
  val (vname, ty) = dest_var v
  val _ = assert finite_mapSyntax.is_fmap_ty ty
  val (_, body) = strip_exists body0
  val cs = strip_conj body
  fun is_fmt t = finite_mapSyntax.is_fmap_ty (type_of t) andalso
                 free_in v t orelse
                 is_uninclusion v t
  fun get_binding c = let
    val (l, r) = dest_eq c
  in
    if is_fmt l andalso is_var r andalso v <> r then
      SOME (r, l, c, REWR_CONV EQ_SYM_EQ)
    else if is_fmt r andalso is_var l andalso v <> l then
      SOME (l, r, c, ALL_CONV)
    else NONE
  end handle HOL_ERR _ => NONE
  val bindings0 = List.mapPartial get_binding cs (* bindings have v term on R*)
  fun check_binding (b as (var, fmt, _, _)) =
      if is_var fmt then raise TrivialBind
      else if #1 (strip_fupd fmt) = v then
        (* expected case *) SOME b
      else
        (big_fat_warning fmt t; NONE)
  val bindings = List.mapPartial check_binding bindings0
  val _ = assert (not o null) bindings
  val (concrete_var, fmt, cjn, cv) = hd bindings
  val fm_terms = HOLset.listItems (topdown_find_terms is_fmt body)
  val (has_unincl, unincl_t) =
      case List.find (fn t => is_neg t andalso fmt_ok fmt t) fm_terms of
        NONE => (false, T)  (* unincl_t value should never be used *)
      | SOME t => (true, t)

  val _ =
      if not has_unincl then
        case List.find (fn t => not (fmt_ok fmt t) andalso t <> v) fm_terms of
          NONE => ()
        | SOME fmt => (big_fat_warning fmt t; failwith "No can do")
      else ()

  val (befores0, afters0) = split_at Term.compare cjn cs
  val befores = List.filter (not o aconv unincl_t) befores0
  val afters = List.filter (not o aconv unincl_t) afters0
  val (cjn, cv) = if has_unincl then (mk_conj(cjn, unincl_t), LAND_CONV cv)
                  else (cjn, cv)
  val rearranged_body =
      case (befores, afters) of
        ([], []) => list_mk_conj[T, cjn, T]
      | ([], _) => list_mk_conj[T, cjn, list_mk_conj afters]
      | (_, []) => list_mk_conj[list_mk_conj befores, cjn, T]
      | _ => list_mk_conj [list_mk_conj befores, cjn,
                           list_mk_conj afters]
  val rearranged_thm = refuteLib.CONJ_ACI (mk_eq(body, rearranged_body))
  val eqnormed_thm = QCONV (RAND_CONV (LAND_CONV cv)) rearranged_body
  val normed_body = TRANS rearranged_thm eqnormed_thm
  val vmap0 = Binarymap.mkDict Term.compare
  fun mk_abstracted_vs(fmt, dict) = let
    val (_, kvs) = strip_fupd fmt
    val (_, vs) = ListPair.unzip (map pairSyntax.dest_pair kvs)
    fun insert (v, dict) =
        case Binarymap.peek(dict, v) of
          NONE => Binarymap.insert(dict, v, genvar (type_of v))
        | SOME _ => dict
  in
    List.foldl insert dict vs
  end
  val pure_fm_terms = filter (not o is_neg) fm_terms
  val vmap = List.foldl mk_abstracted_vs vmap0 pure_fm_terms
  val revinst = Binarymap.foldl (fn (v, gv, acc) => (v |-> gv) :: acc) [] vmap
  val abstracted_vs = if has_unincl then [v]
                      else map (Term.subst revinst) pure_fm_terms
  val fmt' = Term.subst revinst fmt
  fun mk_pred_ty n = if n = 0 then bool
                     else type_of v --> mk_pred_ty (n - 1)
  val pred_ty = mk_pred_ty (length abstracted_vs)
  val P = mk_var("P", pred_ty)
  val Q = mk_var("Q", pred_ty)
  val P_applied = list_mk_comb(P, abstracted_vs)
  val Q_applied = list_mk_comb(Q, abstracted_vs)
  val lcentre0 = mk_eq(concrete_var, fmt')
  val lcentre = if has_unincl then mk_conj(lcentre0, unincl_t) else lcentre0
  val lgoal = mk_exists(v, list_mk_conj[P_applied, lcentre, Q_applied])
  fun remove_lonevar t = let
    val (_, lastkv) = finite_mapSyntax.dest_fupdate fmt
    val k = #1 (pairSyntax.dest_pair lastkv)
  in
      if t = v then mk_domsub(concrete_var, k)
      else t
  end
  val rgoal_versions =
      map (Term.subst [v |-> concrete_var] o
           Term.subst [fmt' |-> concrete_var])
          (map remove_lonevar abstracted_vs)
  val scan_constraints = let
    val (_, fmt_kvs) = strip_fupd fmt'
    val kvs = map pairSyntax.dest_pair fmt_kvs
    val fmscan' = let
      val (k1, v1) = hd kvs
    in
      Term.inst [alpha |-> type_of k1, beta |-> type_of v1] fmscan_t
    end
  in
    list_mk_conj (map (fn (k,v) => list_mk_comb(fmscan', [concrete_var, k, v]))
                      kvs)
  end
  val rgoal =
      list_mk_conj[list_mk_comb(P, rgoal_versions),
                   scan_constraints,
                   list_mk_comb(Q, rgoal_versions)]
  val fm_gv = genvar (type_of v)
  val unincl_tac =
      if has_unincl then
        IMP_RES_TAC finite_mapTheory.DOMSUB_NOT_IN_DOM
      else ALL_TAC
  val body_th = prove(mk_eq(lgoal, rgoal),
                      REWRITE_TAC [fmscan_def] THEN EQ_TAC THEN
                      STRIP_TAC THENL [
                        unincl_tac,
                        IMP_RES_THEN
                          (X_CHOOSE_THEN fm_gv STRIP_ASSUME_TAC)
                          finite_mapTheory.FM_PULL_APART THEN
                        FIRST_X_ASSUM SUBST_ALL_TAC THEN unincl_tac THEN
                        REPEAT (POP_ASSUM MP_TAC)
                      ] THEN
                      ASM_REWRITE_TAC [finite_mapTheory.FAPPLY_FUPDATE,
                                       finite_mapTheory.DOMSUB_FUPDATE,
                                       finite_mapTheory.FDOM_FUPDATE,
                                       finite_mapTheory.FUPDATE_EQ,
                                       pred_setTheory.IN_INSERT] THEN
                      REPEAT STRIP_TAC THEN
                      EXISTS_TAC fm_gv THEN
                      REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
                      ASM_REWRITE_TAC [])
  val normed_body_t = rhs (concl normed_body)
  val abs_over = if has_unincl then [v] else List.rev pure_fm_terms
  val abstracted_body_th =
      FORK_CONV (UNBETA_LIST abs_over, RAND_CONV (UNBETA_LIST abs_over))
                normed_body_t
  val body_usethis = TRANS normed_body abstracted_body_th
in
  push_exists_in_then (BINDER_CONV (K body_usethis) THENC
                       REWR_CONV body_th THENC
                       FORK_CONV (LIST_BETA_CONV,
                                  RAND_CONV LIST_BETA_CONV)) t
end handle TrivialBind => Unwind.UNWIND_EXISTS_CONV t

val host_redn0_eval = let
  open TCP1_hostTypesTheory TCP1_hostLTSTheory
  val prodexps = [FORALL_host, EXISTS_host]
  datatype action = Rwt of thm | Simp of thm
  fun simp act th0 =
      case act of
        Rwt eqth => (CONV_RULE (CHANGED_CONV (PURE_REWRITE_CONV [eqth])) th0
                     handle (e as HOL_ERR _) =>
                            (print ("Failed to rewrite "^thm_to_string eqth);
                             Raise e))
      | Simp th =>
        (CONV_RULE (CHANGED_CONV (SIMP_CONV pureSimps.pure_ss [th])) th0
         handle (e as HOL_ERR _) =>
                (print ("Failed to simp "^thm_to_string th);
                 raise e))
  fun simpl eqths th =
      case eqths of
        [] => th
      | h::t => simpl t (simp h th)

  val cases =
      simpl (map Rwt [better_dupfd_1,
                      better_deliver_out_1b,
                      better_deliver_in_3,
                      SYM letsubstitute,
                      better_timer_tt_rexmtsyn_clause,
                      better_timer_tt_rexmt_clause,
                      better_timer_tt_persist_clause,
                      better_timer_tt_keep_clause, better_timer_tt_2msl,
                      better_timer_tt_delack,
                      better_timer_tt_conn_est,
                      better_timer_tt_fin_wait_2,
                      better_deliver_out_1a])
            host_redn0_cases
  val _ = print "Done \"better\" simplifications\n"
  val cases = SIMP_RULE (bool_ss ++ REMOVE_UGLY_ss ++ deal_to_bad_socks)
                        [TCP1_hostTypesTheory.Sock_def,
                         TCP1_hostTypesTheory.TCP_Sock0_def,
                         TCP1_hostTypesTheory.TCP_Sock_def,
                         TCP1_hostTypesTheory.UDP_Sock0_def,
                         TCP1_hostTypesTheory.UDP_Sock_def,
                         finite_mapTheory.FUPDATE_LIST_THM] cases
  val _ = print "Starting munger ... "
  val revised = Evaluator.general_cases_munger cases [2,3] prodexps
  val _ = print "done\n"
  val dequeues_moved =
      CONV_RULE ((STRIP_QUANT_CONV o RHS_CONV o EVERY_DISJ_CONV o
                  STRIP_QUANT_CONV o TRY_CONV o markerLib.move_conj_left o
                  can o find_term o same_const) ``TCP1_preHostTypes$dequeue_iq``)
                revised
in
  save_thm("host_redn0_eval",
           CONV_RULE (DEPTH_CONV fmap_exists_conv)
                     (simpl [Rwt letsubstitute] dequeues_moved))
end;



(* generate equivalence theorems for all possible label forms: *)
val label_constructors = TypeBase.constructors_of ``:Lhost0``;
fun app_letter avoids ty = let
  val tyop_char1 = String.sub(#1 (dest_type ty),0)
      handle HOL_ERR _ => String.sub(dest_vartype ty, 1)
in
  Lexis.gen_variant Lexis.tmvar_vary avoids (str tyop_char1)
end

fun match_typel pats concretes = let
  fun recurse acc ps cs =
      case ps of
        [] => acc
      | (p::pats) => recurse (raw_match_type p (hd cs) acc) pats (tl cs)
in
  recurse ([], []) pats concretes
end

fun mk_term split_here con = let
  fun mk_from_singlety acc ty = let
    val {Tyop = tyop, Thy, Args = args} = dest_thy_type ty
  in
    if mem tyop split_here then let
        val cons = TypeBase.constructors_of ty
        fun inst_ty c = let
          val (_, dest) = strip_fun (type_of c)
          val ty_args = #2 (dest_type dest)
          val (inst, _) = match_typel ty_args args
        in
          Term.inst inst c
        end
        val insted_cons = map inst_ty cons
      in
        List.concat (map (mk_from_base acc) insted_cons)
      end
    else let
        val s = app_letter acc ty
      in
        [(mk_var(s, ty), s::acc)]
      end
  end
  and foldthis (ty, t0_accs) = let
    val (t0s, accs) = ListPair.unzip t0_accs
    val tuple_accs = List.concat (map (fn acc => mk_from_singlety acc ty) accs)
  in
    List.concat
      (map (fn t0 =>
               map (fn (tuple, acc) => (mk_comb(t0, tuple), acc)) tuple_accs)
           t0s)
  end
  and mk_from_base (acc : string list) (base : term) : (term * string list) list= let
    val (tys, _) = strip_fun (type_of base)
  in
    List.foldl foldthis [(base, acc)] tys
  end
in
  mk_from_base
    (Overload.known_constants (term_grammar.overload_info (term_grammar())))
    con
end

local
  val label_rwts = let
    open TCP1_host0Theory TCP1_LIBinterfaceTheory
  in
    [pairTheory.PAIR_EQ, Lhost0_11, Lhost0_distinct,
     GSYM Lhost0_distinct, LIB_interface_11, LIB_interface_distinct,
     GSYM LIB_interface_distinct]
  end
  val quick_label_CONV = REWRITE_CONV label_rwts
  fun find_arg posn eqn = let
    val (l, _) = dest_eq eqn
    val (_, args) = strip_comb l
  in
    List.nth(args, posn)
  end
in
fun mk_simped t = let
  val label_match = PART_MATCH (find_arg 4) host_redn0_eval t
in
  CONV_RULE (RAND_CONV (EVERY_DISJ_CONV quick_label_CONV)) label_match
end
end (* local *)

fun mapi f arg = let
  fun recurse i acc arg =
      case arg of
        [] => List.rev acc
      | (h::t) => recurse (i + 1) (f i h :: acc) t
in
  recurse 0 [] arg
end

fun prove_and_save_con t = let
  val cname = #1 (dest_const t)
  val c_terms = map #1 (mk_term ["LIB_interface", "prod"] t)
  fun const_names t =
      find_terms
      (fn t => is_const t andalso
               #1 (dest_type (#2 (strip_fun ((type_of t))))) <> "prod") t
  fun mk_name t = let
    val cns = List.rev (const_names t)
  in
    "quick_redn_" ^
    String.concat (map (fn t => #1 (dest_const t) ^ "_") cns) ^ "thm"
  end

  fun mapthis t = let
    val nm = mk_name t
  in
    print ("Generating "^nm^"\n");
    ignore (save_thm (nm, mk_simped t))
  end

in
  app mapthis c_terms
end

val _ = map prove_and_save_con label_constructors

val _ = export_theory ();
