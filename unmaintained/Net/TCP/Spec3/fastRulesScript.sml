open HolKernel boolLib bossLib

val _ = new_theory "fastRules";

(* ----------------------------------------------------------------------
    rule improving transformations
   ---------------------------------------------------------------------- *)

val ss = srw_ss()

fun host_forallexists th = let
  val _ = print "HOST_FORALL_EXISTS "
in
  SIMP_RULE (srw_ss()) [TCP3_hostTypesTheory.FORALL_host,
                        TCP3_hostTypesTheory.EXISTS_host] th
end

fun socket_forallexists th = let
  val _ = print "SOCKET_FORALL_EXISTS "
in
  SIMP_RULE (srw_ss()) [TCP3_hostTypesTheory.FORALL_socket,
                        TCP3_hostTypesTheory.EXISTS_socket] th
end

fun tcp_socket_forallexists th = let
  val _ = print "TCP_SOCKET_FORALL_EXISTS "
in
  SIMP_RULE (srw_ss()) [TCP3_hostTypesTheory.FORALL_tcp_socket,
                        TCP3_hostTypesTheory.EXISTS_tcp_socket] th
end

fun remove_consts th = let
  val _ = print "REM_CONSTS "
in
  REWRITE_RULE [finite_mapTheory.FUPDATE_LIST_THM,
		TCP3_hostTypesTheory.Sock_def,
		TCP3_hostTypesTheory.TCP_Sock_def,
		TCP3_hostTypesTheory.TCP_Sock0_def,
		TCP1_baseTypesTheory.OK'_fd_def,
		TCP1_baseTypesTheory.OK'_def,
		TCP1_baseTypesTheory.OK'_one_def,
		TCP1_paramsTheory.ff_default_def,
		TCP1_paramsTheory.sf_default_def,
		TCP1_paramsTheory.File_def,
                TCP1_timersTheory.never_timer_def] th
end

(* deliver_out_1 fix *)
val do1_lemma = prove(
  ``(do_output,persist_fun) IN tcp_output_required /\
    (sock.pr = TCP_PROTO tcp_sock) ==>
    option_case
       sock
       (\f. sock with pr := TCP_PROTO (tcp_sock with cb updated_by f))
       persist_fun =
    sock``,
  SRW_TAC [][IN_DEF, TCP3_auxFnsTheory.tcp_output_required_def] THEN
  SRW_TAC [][] THEN
  Q.SPEC_THEN `sock` FULL_STRUCT_CASES_TAC
              TCP3_hostTypesTheory.socket_literal_nchotomy THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.SPEC_THEN `tcp_sock` FULL_STRUCT_CASES_TAC
              TCP3_hostTypesTheory.tcp_socket_literal_nchotomy THEN
  FULL_SIMP_TAC (srw_ss()) []);
val Sock_pr = prove(
  ``(Sock(fid,sf,i1,p1,i2,p2,es,csmore,crmore,pr) : TCP3_hostTypes$socket).pr =
    pr``,
  SRW_TAC [][TCP3_hostTypesTheory.Sock_def]);

fun do1_fix th =
    if free_in ``deliver_out_1`` (concl th) then
      (print "DO1_FIX ";
       SIMP_RULE (bool_ss ++ boolSimps.CONJ_ss ++ SatisfySimps.SATISFY_ss)
                 [do1_lemma, Sock_pr]
                 th)
    else th

(* ---------------------------------------------------------------------- *)





(* a composition of all the transformations *)
val stdtransform = tcp_socket_forallexists o socket_forallexists o
                   host_forallexists o remove_consts o do1_fix

(* emit theorems *)
val _ = let
  val ids = TypeBase.constructors_of ``:rule_ids``
  val cases = TCP3_hostLTSTheory.host_redn0_cases
  open simpLib
  val ssfrag = let val {convs,rewrs} = TypeBase.simpls_of ``:rule_ids``
               in
                 SSFRAG { ac = [], congs = [], convs = convs,
                          dprocs = [], filter = NONE, rewrs = rewrs }
               end
  val ss = bool_ss ++ ssfrag
  fun gen_fast id = SIMP_RULE ss [] (SPEC id cases)

  fun appthis id = let
    val nm = #Name (dest_thy_const id)
    val _ = print ("Working on "^ nm ^": ")
    val _ = print "INITIAL "
    val th0 = gen_fast id
    val th' = stdtransform th0
    val _ = print "\n"
  in
    ignore (save_thm ("fast_"^nm, th'))
  end
in
  List.app appthis ids
end

val _ = export_theory()


