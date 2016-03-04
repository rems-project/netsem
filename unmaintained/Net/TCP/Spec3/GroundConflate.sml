(* this is actually a Spec1 file FIXME move *)

(* want to actually read the ground trace *)

(*
val dep_tokens = fn s =>
		    let
		       val delim = fn c => c = #" "
		   in
			String.tokens delim s
		    end;

(* also need to strip . suffix, assume suffix of length 3 *)

val loadDeps = fn s => app (load o (implode o rev o tl o tl o tl o rev o explode)) (tl (dep_tokens s));

loadDeps "CheckTraces.uo: strings.uo testEval.uo"; /auto/groups/tthee/local/hol98/sigobj/DiskThms.ui"; Version.ui";

 /auto/groups/tthee/local/hol98/sigobj/seq.ui /auto/groups/tthee/local/hol98/sigobj/pairSyntax.ui /auto/groups/tthee/local/hol98/sigobj/Parse.ui /auto/groups/tthee/local/hol98/sigobj/Term.ui /auto/groups/tthee/local/hol98/sigobj/finite_mapSyntax.ui /auto/groups/tthee/local/hol98/sigobj/Feedback.ui /auto/groups/tthee/local/hol98/sigobj/simpLib.ui";

(* this also needed *)
loadDeps "TCP1_net1_to_netScript.uo: TCP1_net1Theory.ui /auto/groups/tthee/local/hol98/sigobj/bossLib.ui /auto/groups/tthee/local/hol98/sigobj/listTheory.ui Version.ui TCP1_netTheory.ui HolDoc.ui /auto/groups/tthee/local/hol98/sigobj/Parse.ui /auto/groups/tthee/local/hol98/sigobj/HolKernel.ui /auto/groups/tthee/local/hol98/sigobj/boolLib.ui";



*)

(* ******************************************************************************** *)
(* dependencies *)

open HolKernel boolLib bossLib Parse

open testEval TCP1_net1Theory

(* ******************************************************************************** *)
(* spec *)

(* We want to retain the maximum amount of information possible. This
includes such things as rn, rp and rc. This additional information,
although not present in the Spec3 ground net trace, allows us to check
the transitions more easily.
*)

(* ******************************************************************************** *)
(* creating ground net trace *)

exception ConflateGround of string;

fun dest_Lh_senddatagram l =
    let
	val r = fn () => raise (ConflateGround "dest_Lh_senddatagram: not a Lh_senddatagram")
    in
	case is_comb l of
	    true =>
	    let
		val (l,msg) = dest_comb l
		val _ = case (l = ``TCP1_host0$Lh_senddatagram``) of true => () | false => r ()
	    in
		msg
	    end
	  | false => r ()
    end;

fun dest_Lh_recvdatagram l =
    let
	val r = fn () => raise (ConflateGround "dest_Lh_recvdatagram: not a Lh_recvdatagram")
    in
	case is_comb l of
	    true =>
	    let
		val (l,msg) = dest_comb l
		val _ = case (l =  ``TCP1_host0$Lh_recvdatagram``) of true => () | false => r ()
	    in
		msg
	    end
	  | false => r ()
    end;

val is_Lh_senddatagram = can dest_Lh_senddatagram;
val is_Lh_recvdatagram = can dest_Lh_recvdatagram;

fun is_Lh_sendrecvdatagram x = (is_Lh_senddatagram x) orelse (is_Lh_recvdatagram x);

fun create_ground_net_trace (file1, file2) = let

val _ = print "GroundConflate: Reading trace files\n";

val t = DiskThms.read_file file1 handle e => Raise e;

val t' =  DiskThms.read_file file2 handle e => Raise e;

(* (string * thm) list *)

val t = List.map #2 t;

val t' = List.map #2 t';

(* ground spec1 trace conflator- outputs a ground network trace *)

fun th_to_hlh th =
    let
	val c = concl th
	val (host_redn_h_l,h') = dest_comb c
	val (host_redn_h,l) = dest_comb host_redn_h_l
	val (hr,h) = dest_comb host_redn_h
    in
	(hr,h,l,h')
    end;

fun dummy_epsilon_transition u = (``(ARB "ruleids"):rule_ids(*FIXME*)``,u,``TCP1_host0$Lh_epsilon 0:Lhost0``,u);

fun hosts_to_net (h1,h2) = ``(^h1,^h2)``;

fun lbl_to_nlbl l (h:term) = ``(Ln1_host(^h,^l))``;

fun dest_lh_epsilon l =
    let
	val r = fn () => raise (ConflateGround "dest_lh_epsilon: not an Lh_epsilon")
    in
	case is_comb l of
	    true =>
	    let
		val (l,dur) = dest_comb l
		val _ = case l = ``TCP1_host0$Lh_epsilon`` of true => () | false => r ()
	    in
		dur
	    end
	  | false => r ()
    end;

fun is_lh_epsilon l = can dest_lh_epsilon l;

(*
  val eps = #3 (th_to_hlh ((hd t')));

  dest_lh_epsilon ``ARB``(*eps*);

  dest_lh_epsilon eps;

  is_lh_epsilon eps;

  is_lh_epsilon ``ARB``;

  is_lh_epsilon ``TCP1_host0$Lh_epsilon 0``;
*)


fun ln_epsilon dur = ``Ln1_epsilon ^dur``;

(*

INPUTS: are two lists of [(h0,l0,h1);(h1,l1,h2)...] transitions

NOTATION: (hn,ln,h(n+1)) and (h,l,h') for these transitions. (n,nl,n')
is the corresponding network transition.

INVARIANT: (m = length xs + length ys). m is a dummy variable that
could (should?) be removed, but is here to make induction clearer.

INVARIANT: h of xs is u, similarly for v, i.e. u is "current" state of
a given host relative to the trace. This only makes a difference when
xs or ys is [], because u,v are derived from h' of the previous
transition.

INVARIANT IEPS: xs,ys projected onto epsilons are identical

*)

fun dest_hr hr =
    let val (_,[rn,rp,rc]) = strip_comb hr
    in (rn,rp,rc) end;

fun k x y = x;

fun filter1 f xs = case xs of
		       [] => []
		     | x::xs => if f x then xs else x::(filter1 f xs);

fun process_Lh_sendrecvdatagram l msgs = (
    if is_Lh_recvdatagram l then filter1 (fn x => x = (dest_Lh_recvdatagram l)) msgs
    else if is_Lh_senddatagram l then (dest_Lh_senddatagram l::msgs)
    else msgs);

fun f (xs,ys) (u,v) msgs m =
    case (xs,ys) of
      ([],[]) => []
    | (xs,ys) => let

	val _ = print ((int_to_string m)^"\n")
	(* What to do when an arg is []? We insert a dummy
	   epsilon, so that the other list gets processed. If the
	   other list contains an epsilon ... but IEPS ensures this
	   can't happen *)

	val ((hr1,h1,l1,h'1),xs') =
	    case xs of [] => (dummy_epsilon_transition u,[])
                     | (x::xs) => (th_to_hlh x,xs)
	val ((hr2,h2,l2,h'2),ys') =
	    case ys of [] => (dummy_epsilon_transition v,[])
                     | (y::ys) => (th_to_hlh y,ys)

	val n = hosts_to_net (h1,h2)
	val {l = l, n' = n', msgs' = msgs', hr = hr, rest = rest} = (
	    case (is_lh_epsilon l1, is_lh_epsilon l2) of
		(true,true) => (case dest_lh_epsilon l1 = dest_lh_epsilon l2 of
				    true => (let
						 val msgs' = msgs
					     in
						 {l = ln_epsilon (dest_lh_epsilon l1)
						, n' = hosts_to_net (h'1,h'2)
						, msgs' = msgs'
						, hr = hr1
						, rest = f (xs',ys') (h'1,h'2) msgs' (m-2)
						 }
					     end)
				  | false => k (raise Match) ("FIXME: encoutered two epsilons which did not have same duration."))

				   (* l2 is not an epsilon so process *)
	      | (true,false) => (let
				     val msgs' = process_Lh_sendrecvdatagram l2 msgs
				 in
				     {l = lbl_to_nlbl l2 ``Aux``
				    , n' = hosts_to_net (h1,h'2)
				    , msgs' = msgs'
				    , hr = hr2
				    , rest = f (xs,ys') (h1,h'2) msgs' (m-1)
				     }
				 end)
	      | (false,_) => (let
				  val msgs' = process_Lh_sendrecvdatagram l1 msgs
			      in
				  {l = lbl_to_nlbl l1 ``Test``
				 , n' = hosts_to_net (h'1,h2)
				 , msgs' = msgs'
				 , hr = hr1
				 , rest = f (xs',ys) (h'1,h2) msgs' (m-1)
				  }
				 end)
		(* l1 is not an epsilon so process. case (false,false) should probably never happen with real observed traces, but process one or the other *)
	)
	val rnrprc = dest_hr hr
      in
	  {n=n,msgs=msgs,l=l,n'=n',msgs'=msgs',rnrprc=rnrprc}::rest
      end;

fun f' (t1,t2) =
    let
	val (hr1,h1,l1,h'1) = th_to_hlh (hd t1)
	val (hr2,h2,l2,h'2) = th_to_hlh (hd t2)
    in
	f (t1,t2) (h1,h2) [] (List.length t1 + List.length t2)
    end;

val _ = print "GroundConflate: combining traces\n";

in
 time f' (t,t')
end (* big function block, starting at fun create_ground_net_trace above *)
(*
runtime: 64.548s,    gctime: 15.745s,     systime: 0.124s.
why is this so slow?
*)


(* ******************************************************************************** *)
(* second stage- mangle labels to Lnet0 model *)

(* open TCP1_net1Theory; *)

fun lnet1_to_lnet0 l1 =
    #2 (dest_eq (concl (SIMP_CONV std_ss [TCP1_net1Theory.Lnet1_to_Lnet0_def,fetch "TCP1_net1" "Lnet1_case_def",pairTheory.pair_case_thm,fetch "TCP1_host0" "Lhost0_case_def"] ``Lnet1_to_Lnet0 ^l1``)));

(*
val ls = List.map #2 nln's;
lnet1_to_lnet0 (hd ls);
List.map lnet1_to_lnet0 ls;
*)

(* write out to file just for the record - rather than using REFL, which
   requires writing out the terms twice, equate the terms to ARB. *)
fun mk_eq_arb t = mk_eq(t, mk_arb (type_of t))

fun to_thm {n=n,msgs=msgs,l=l,n'=n',msgs'=msgs',rnrprc=(rn,rp,rc)} =
    let
	val msgs = listSyntax.mk_list (msgs,``:msg``)
	val msgs' = listSyntax.mk_list (msgs',``:msg``)
    in
	mk_thm([], mk_eq_arb ``((^n,^msgs,^l,^n',^msgs'),(^rn,^rp,^rc))``)
    end;

fun write_ground_net_trace fname nlns =
    let
	val _ = print ("GroundConflate: writing to file "^fname^"\n")
    in
	DiskThms.write_file fname (#2 (List.foldr (fn (th,(count,acc)) => (count+1,(int_to_string count,th)::acc)) (0,[]) (List.map to_thm nlns)))
    end;


(* ******************************************************************************** *)
(* read ground net trace from file *)

fun read_ground_net_trace fname =
    let
	fun from_thm th =
	    let
		val (nmsln'ms',rnrprc) = (pairSyntax.dest_pair (#1 (dest_eq (concl th))))
		val [n,ms,l,n',ms'] = pairSyntax.spine_pair nmsln'ms'
		val [rn,rp,rc] = pairSyntax.spine_pair rnrprc
	    in
		((n,#1 (listSyntax.dest_list ms),l,n',#1 (listSyntax.dest_list ms')),(rn,rp,rc))
	    end
    in
	List.map from_thm (List.map #2 (DiskThms.read_file fname))
	handle e => Raise e
    end;


(* ******************************************************************************** *)
(* command line args *)

fun isSuffix s1 s2 =
    let
	val i = String.size s2 - String.size s1
	val i = if i < 0 then 0 else i
	val s2' = String.extract (s2,i, NONE)
    in
	s1 = s2'
    end;

fun main () =
	let
	    val _ = if length (CommandLine.arguments()) <> 3 then
			(TextIO.output(TextIO.stdErr,
				       "Usage: "^CommandLine.name() ^
				       "testtrace.epsilon.thydata.grounded auxtrace.epsilon.thydata.grounded trace.net.thydata\n")
		       ; OS.Process.exit OS.Process.failure)
		    else ()

	    val [stest,saux,snet] = CommandLine.arguments()

	    val t = create_ground_net_trace (stest,saux)

	    val _ = write_ground_net_trace snet t
	 in
	     ()
	 end;

(* this is truly horrible, but I wanted to avoid splitting this into another file *)
val _ = if isSuffix "GroundConflate.exe" (CommandLine.name()) then main () else ();

