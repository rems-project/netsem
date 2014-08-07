(* this is an -*- sml -*- file *)
(* ******************************************************************************** *)
(* function to produce a list of stream transitions *)

(*

val dep_tokens = fn s => let val delim = fn c => c = #" " in String.tokens delim s end;
val loadDeps = fn s => app (load o (implode o rev o tl o tl o tl o rev o explode)) (tl (dep_tokens s));

loadDeps "testScript.uo: GroundConflate.uo /auto/groups/tthee/local/hol98/sigobj/bossLib.ui Version.ui HolDoc.ui /auto/groups/tthee/local/hol98/sigobj/Parse.ui /auto/groups/tthee/local/hol98/sigobj/HolKernel.ui TCP3_absFunTheory.ui /auto/groups/tthee/local/hol98/sigobj/boolLib.ui /auto/groups/tthee/local/hol98/sigobj/containerTheory.ui fmapUtilsTheory.ui" handle e => Raise e;

*)

(* loadPath := !loadPath @ ["../Spec1"]; *)

(* val _ = quietdec := true; *)

open HolKernel boolLib Parse bossLib testEval;

open TCP3_absFunTheory fmapUtilsTheory TCP1_net1Theory

open GroundConflate

(* these from testEval *)
open testEval

(* val _ = quietdec := false; *)

val base_ss =
    srw_ss() ++ rewrites [realTheory.REAL_INJ,
                                  realTheory.REAL_OF_NUM_MUL,
                                  realTheory.REAL_OF_NUM_ADD,
                                  finite_mapTheory.DOMSUB_FUPDATE_THM,
                                  option_cond_thms, IS_SOME_IMP_ELIM];

val phase1_ss = base_ss ++ CLET_ss ++ strCONV_ss ++ updeq_CONV_ss ++
                        option_cong_ss ++ cond_ss ++ lconj_cong_ss ++
                        rathandler_SS ++ safe_rewrite_SS ++ pending_SS ++
                        GSPEC_ss ++ boolSimps.CONJ_ss ++
                        numrelnorm.CANON_ss ++ noliterals_SS ++
                        rewrites phase1_abbreviations;
val phase2_ss = phase1_ss ++ rewrites phase2_abbreviations ++
                realSimps.REAL_ARITH_ss ++ q_ok_SS;

(* FIXME - this is hopelessly inefficient because e.g. for transitions
(n,l,n') (n',l',n''), n' is obtained by simplification twice
(simplification acts on transitions) *)

fun abs_trans {quad, h1, msgs, h2, lbl, h1', msgs', h2'} =
    let
	val tm = ``TCP3_absFun$abs_trans ^quad (^h1,LIST_TO_SET ^msgs,^h2) (Lnet1_to_Lnet0 ^lbl) (^h1',LIST_TO_SET ^msgs',^h2')``
	val p = fn th => #2 (dest_eq (concl th))
	val SC = fn ths => fn tm => (p (SIMP_CONV (phase2_ss) ths tm)) handle UNCHANGED => tm
	val tm1 = (SC [abs_trans_def, abs_lbl_def, abs_hosts_def, LetComputeTheory.CLET_THM,LET_THM] tm)
	val tm2 = (SC
		       [LetComputeTheory.CLET_THM,LET_THM
		      , host1_to_3_def, socket1_to_3_def, tcp_socket1_to_3_def, tcpcb1_to_3_def
		      , abs_hosts_one_sided_def

		      , TCP1_net1Theory.Lnet1_to_Lnet0_def,fetch "TCP1_net1" "Lnet1_case_def",pairTheory.pair_case_thm,fetch "TCP1_host0" "Lhost0_case_def"
		      , TCP1_paramsTheory.File_def
		      , finite_mapTheory.FAPPLY_FUPDATE_THM(*, finite_mapTheory.RRESTRICT_FUPDATE, finite_mapTheory.RRESTRICT_FEMPTY *)
		      , TCP1_netTypesTheory.EXISTS_tcpSegment
		      , TCP1_utilPropsTheory.DROP_THM (* 30 *)
		       ]
		       tm1)
    in
	tm2
    end;

(* does not include rewrites 62 and beyond *)

exception evalAbsFun of string;

(* assumes test is first to send - quad is directional *)
fun quad_of_trace t =
    let
	val quad = (case List.find (fn msgs => msgs <> []) t of
			SOME [msg] =>
			(* FIXME assumes first msg is a TCP msg *)
			    ``let msg = case ^msg of TCP msg -> msg || _ -> ARB "quad_of_trace" in
				  (THE (msg.is1)
				 ,THE (msg.ps1)
				 ,THE (msg.is2)
				 ,THE (msg.ps2))``
						   | NONE => raise (evalAbsFun "quad_of_trace"))
	fun f x = #2 (dest_eq (#2 (dest_thm x)))
	val quad = f (SIMP_CONV phase2_ss [] quad)
    in
	quad
    end;


(* ******************************************************************************** *)
(* command line *)



fun main () =
let

val _ = if length (CommandLine.arguments()) <> 2 then
	    (TextIO.output(TextIO.stdErr,
			   "Usage: "^CommandLine.name() ^
			   "spec1nettrace.net.thydata spec3nettrace.net.thydata\n")
	   ; OS.Process.exit OS.Process.failure)
	else ();

val [spec1tracename,spec3tracename] = CommandLine.arguments();

(* val [spec1tracename,spec3tracename] = ["trace0593/trace0593.net.thydata",""]; (* FIXME remove *) *)

val _ = print ("evalAbsFun: reading spec1 network trace from file "^spec1tracename^"\n");

val t = GroundConflate.read_ground_net_trace spec1tracename;

val t1 = List.map
	     (fn ((h1h2,msgs,lbl,h1'h2',msgs'),(rn,rp,rc)) =>
		 let
		     val (h1,h2) = pairSyntax.dest_pair h1h2
		     val (h1',h2') = pairSyntax.dest_pair h1'h2'
		 in
		     {h1=h1,msgs=msgs,h2=h2,lbl=lbl,h1'=h1',h2'=h2',msgs'=msgs'}
		 end
	     )
	     t;

(* FIXME assumes that at least one message is sent *)
val quad = quad_of_trace (map (fn {msgs,...} => msgs) t1);

(* include the quad, also combine msgs into HOL lists. Note that up to this point, we still have rn rp rc info *)
val t2 = List.map
	     (fn {h1,h2,msgs,lbl,h1',h2',msgs'} =>{quad=quad,h1=h1,msgs=listSyntax.mk_list(msgs,``:msg``),h2=h2,lbl=lbl,h1'=h1',h2'=h2',msgs'=listSyntax.mk_list(msgs',``:msg``)})
	     t1;

val _ = print ("evalAbsFun: applying abstraction function\n");

val t3 = List.map (fn x => (print "."; abs_trans x)) t2;

val _ = print "\n";

val _ = print ("evalAbsFun: writing spec3 network trace to file "^spec3tracename^"\n");

val _ = DiskThms.write_file spec3tracename (List.map
						(fn tm => ("",mk_thm([], GroundConflate.mk_eq_arb tm)))
						t3);

in () end;


fun isSuffix s1 s2 =
    let
	val i = String.size s2 - String.size s1
	val i = if i < 0 then 0 else i
	val s2' = String.extract (s2,i, NONE)
    in
	s1 = s2'
    end;

(* this is truly horrible, but I wanted to avoid splitting this into another file *)
val _ = if isSuffix "evalAbsFun.exe" (CommandLine.name()) then main () else ();
