(* An approximate characterisation of urgency
     - modelled on the Spec1 version *)

(*
loadPath := "../Spec1" :: !loadPath
*)

open HolKernel boolLib Parse bossLib

local open TCP3_hostLTSTheory in end

val _ = new_theory "TCP3_urgency";

val _ = augment_srw_ss [rewrites [finite_mapTheory.FUPDATE_LIST,
                                  TCP3_hostTypesTheory.Sock_def]]

val nonurgent_host_def = Define`
  nonurgent_host h S0 M =
    !rn rp rc lbl h' S' M'.
        ~(rn /* rp, rc */ (h, S0, M) -- lbl --> (h',S',M')) \/
        ~is_urgent rc
`;

val urgent_rules = store_thm(
  "urgent_rules",
  ``is_urgent rc /\ rn /* rp, rc */ (h0,S0,M0) -- lab --> (h1,S1,M1) ==>
    rn IN {accept_1; accept_4; accept_5; close_5; connect_2; connect_3;
           connect_4;
           recv_8a; recv_15; recv_20; recv_23; send_5a; send_7; send_15;
           send_16; send_17}``,
  Cases_on `rc` THEN
  REWRITE_TAC [TCP1_preHostTypesTheory.is_urgent_def] THEN
  Cases_on `b` THEN REWRITE_TAC [] THEN
  REWRITE_TAC [TCP3_hostLTSTheory.host_redn0_cases,
               TypeBase.distinct_of ``:rule_cat``,
               GSYM (TypeBase.distinct_of ``:rule_cat``),
               TypeBase.one_one_of ``:rule_cat``,
               TCP1_preHostTypesTheory.urgent_def,
               TCP1_preHostTypesTheory.nonurgent_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [pred_setTheory.IN_INSERT] THEN
  FULL_SIMP_TAC bool_ss [TCP1_utilsTheory.ASSERTION_FAILURE_def]);

val nonurgent_approx_def = Define`
    nonurgent_approx a2 =
      let ts = a2.ts in
        let socks = a2.socks in
        !tid.
          tid IN FDOM ts ==>
          let tstid = ts ' tid
          in
           (!sid d lis.
               tstid = Timed (Accept2 sid, d) ==>
               let sockssid = socks ' sid
               in
                 ?tcp_sock.
                    sockssid.pr = TCP_PROTO tcp_sock /\
                    tcp_sock.st = LISTEN /\           (* for accept_5 *)
                    sockssid.cantrcvmore = F /\       (* for accept_4 *)
                    (tcp_sock.lis = SOME lis /\ ~(lis.q = []) ==>
                     let sid' = LAST lis.q in
                     let ssid' = socks ' sid' in
                     ?tcp_sock'.
                        ssid'.pr = TCP_PROTO tcp_sock' /\
                        let s'st = tcp_sock'.st in
                        let s'es = ssid'.es in
                          (s'st = ESTABLISHED ==>  (* for accept_1 *)
                           s'es = SOME ECONNABORTED))) /\
           (!sid d. ts ' tid = Timed(Close2 sid, d) ==> (* for close_5 *)
                  let sock = socks ' sid
                  in
                      ?tcp_sock.
                         sock.pr = TCP_PROTO tcp_sock /\
                         let st = tcp_sock.st in
                           ~(st = FIN_WAIT_2) /\ ~(st = TIME_WAIT) /\
                           ~(st = CLOSED)) /\
         (!sid d. ts ' tid = Timed(Connect2 sid, d) ==>
                  let sock = socks ' sid
                  in
                     ?tcp_sock.
                        sock.pr = TCP_PROTO tcp_sock /\
                        let st = tcp_sock.st in
                          ~(st IN
                              {ESTABLISHED; CLOSE_WAIT; (* for connect_2 *)
                               CLOSED}) /\              (* for connect_3 *)
                          (st = SYN_SENT ==>
                           sock.es = NONE)) /\          (* for connect_4 *)
         (!sid n opts d.
             ts ' tid = Timed(Recv2(sid, n, opts), d) ==>
             let s = socks ' sid in
               s.es = NONE /\ (* for recv_8a *)
               !udp_sock.
                  s.pr = UDP_PROTO udp_sock ==>
                  udp_sock.rcvq = []) (* for recv_15, recv_20 and recv_23 *) /\
         (!sid str opts d ipas.
             ts ' tid = Timed(Send2(sid, ipas, str, opts), d) ==>
             let s = socks ' sid
             in
               ~s.cantsndmore /\          (* for send_7 *)
               s.es = NONE /\             (* for send_16 and send_5a *)
               (proto_of s.pr = PROTO_UDP ==>
                s.cantsndmore = T /\      (* for send_15 *)
                (!ips addrs. (ipas = SOME (ips, addrs)) ==> (* for send_17 *)
                            ~(ips = NONE /\ s.is2 = NONE)) /\
                STRLEN (IMPLODE str) <= UDPpayloadMax a2.arch /\
                (bsd_arch a2.arch ==>
                 STRLEN (IMPLODE str) <= s.sf.n(SO_SNDBUF))))
`;

val LAST_APPEND_1 = store_thm(
  "LAST_APPEND_1",
  ``!l x. LAST (APPEND l [x]) = x``,
  Induct THEN SRW_TAC [][listTheory.LAST_DEF]);
val _ = export_rewrites ["LAST_APPEND_1"]


val approx_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [TCP3_hostLTSTheory.host_redn0_cases] THEN
  CONV_TAC
    (RAND_CONV
       (EVERY_DISJ_CONV
          (STRIP_QUANT_CONV (LAND_CONV (SIMP_CONV (srw_ss()) []))))) THEN
  REWRITE_TAC [TCP1_utilsTheory.neq_def,
               TCP1_utilsTheory.NOTIN_def] THEN
  STRIP_TAC THEN
  Q.PAT_ASSUM `rc = y` SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [TCP1_preHostTypesTheory.is_urgent_def])
THEN
  TRY (FIRST_X_ASSUM CONTR_TAC) THEN
  Q.PAT_ASSUM `nonurgent_approx x` MP_TAC THEN
  SRW_TAC [][nonurgent_approx_def, LET_THM] THEN
  Q.EXISTS_TAC `tid` THEN
  ASM_SIMP_TAC (srw_ss()) [finite_mapTheory.NOT_EQ_FAPPLY,
                           TCP3_hostTypesTheory.TCP_Sock_def,
                           TCP3_hostTypesTheory.UDP_Sock_def,
                           TCP3_hostTypesTheory.TCP_Sock0_def,
                           TCP3_hostTypesTheory.UDP_Sock0_def]


val accept_1_approx = store_thm(
  "accept_1_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(accept_1 /* rp, rc */ (h,S0,M0) -- lbl --> (h',S',M'))``,
  approx_tac THEN SRW_TAC [][EXISTS_OR_THM]);

val accept_4_approx = store_thm(
  "accept_4_approx",
  ``nonurgent_approx a2 /\ is_urgent rc ==>
    ~(accept_4 /* rp, rc */ (a2,S0,M0) -- lbl --> (h',S',M'))``,
  approx_tac);

val accept_5_approx = store_thm(
  "accept_5_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(accept_5 /* rp, rc */ (h,S0,M0) -- lbl --> (h',S1,M1))``,
  approx_tac THEN
  Q.PAT_ASSUM `TCP_PROTO y = x` (MP_TAC o SYM) THEN
  FULL_SIMP_TAC (srw_ss()) []);

val close_5_approx = store_thm(
  "close_5_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(close_5 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac);

val connect_2_approx = store_thm(
  "connect_2_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(connect_2 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac THEN
  Q.PAT_ASSUM `TCP_PROTO y = x` (MP_TAC o SYM) THEN
  ASM_SIMP_TAC (srw_ss()) []);

val connect_3_approx = store_thm(
  "connect_3_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(connect_3 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac THEN
  Q.PAT_ASSUM `TCP_PROTO y = x` (MP_TAC o SYM) THEN
  ASM_SIMP_TAC (srw_ss()) []);

val connect_4_approx = store_thm(
  "connect_4_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(connect_4 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac);

val recv_8a_approx = store_thm(
  "recv_8a_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(recv_8a /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac)

val recv_15_approx = store_thm(
  "recv_15_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(recv_15 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac);

val recv_20_approx = store_thm(
  "recv_20_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(recv_20 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac);

val recv_23_approx = store_thm(
  "recv_23_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(recv_23 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac);

val send_5a_approx = store_thm(
  "send_5a_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(send_5a /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac);

val send_7_approx = store_thm(
  "send_7_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(send_7 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac);

val send_15_approx = store_thm(
  "send_15_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(send_15 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac THEN
  SIMP_TAC (srw_ss()) [TCP3_hostTypesTheory.proto_of_def]);

val send_16_approx = store_thm(
  "send_16_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(send_16 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac THEN Cases_on `str` THEN SRW_TAC [][]);

val send_17_approx = store_thm(
  "send_17_approx",
  ``nonurgent_approx h /\ is_urgent rc ==>
    ~(send_17 /* rp, rc */ (h,S0,M0) -- lbl --> h')``,
  approx_tac THEN
  SRW_TAC [numSimps.ARITH_ss][TCP3_hostTypesTheory.proto_of_def])


val nonurgent_characterisation = store_thm(
  "nonurgent_characterisation",
  ``!h. nonurgent_approx h ==> nonurgent_host h S0 M0``,
  SIMP_TAC bool_ss [nonurgent_host_def, GSYM IMP_DISJ_THM] THEN
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC urgent_rules THEN
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) THEN
  PROVE_TAC [accept_1_approx, accept_4_approx, accept_5_approx,
             close_5_approx,
             connect_2_approx, connect_3_approx, connect_4_approx,
             recv_8a_approx, recv_15_approx, recv_20_approx, recv_23_approx,
             send_5a_approx, send_7_approx, send_15_approx, send_16_approx,
             send_17_approx]);

val _ = export_theory();





