structure GroundTrace :> GroundTrace =
struct

open testEval

fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")

fun extract_trace namedthms = let
  fun recurse acc n = let
    val ns = StringCvt.padLeft #"0" 4 (Int.toString n)
    val th = assoc ("trace_step"^ns) namedthms
  in
    recurse (th::acc) (n + 1)
  end handle HOL_ERR _ => List.rev acc
in
  recurse [] 0
end

fun output_trace fname thmlist = let
  fun namethm (th, (i,acc)) = let
    val name = "trace_step" ^ StringCvt.padLeft #"0" 4 (Int.toString i)
  in
    (i + 1, (name, th) :: acc)
  end
  val (_, named_thms) = List.foldl namethm (0, []) thmlist
in
  DiskThms.write_file fname (List.rev named_thms)
end

(* given a set of inequalities over variables with algebraic domains,
   where some of the inequalities are with ground values (e.g., FID 0,
   to pick a typical one), find an instantation for the variables *)

fun do_freshness th = let
  fun dest_ineq1 t = let
    val (l,r) = dest_eq (dest_neg t)
    val lpart = if is_var l then [(l,r)] else []
    val rpart = if is_var r then [(r,l)] else []
  in
    lpart @ rpart
  end
  fun is_ineq1 t = not (null (dest_ineq1 t)) handle HOL_ERR _ => false
  val ineqs = List.filter is_ineq1 (hyp th)
  fun build_csets (ineq,db) = let
    val csts = dest_ineq1 ineq
    fun do_1cst ((v,t),db) =
        case Binarymap.peek(db,v) of
          NONE => Binarymap.insert(db,v,[t])
        | SOME clist => Binarymap.insert(db,v,t::clist)
  in
    List.foldl do_1cst db csts
  end
  (* cdb is a map from vars to lists of things that the vars aren't
     allowed to equal *)
  val cdb = List.foldl build_csets (Binarymap.mkDict Term.compare) ineqs
  fun add_unconstrained (v, db) =
      case Binarymap.peek(db, v) of
        NONE => Binarymap.insert(db, v, [])
      | _ => db
  val cdb = List.foldl add_unconstrained cdb (free_vars (concl th))
  fun resolve_cst theta (v, avoids0) = let
    val avoids = map (Term.subst theta) avoids0
    val ty = type_of v
    val cs = TypeBase.constructors_of ty
    val c = hd cs
    val (argty,rngty) = dom_rng (type_of c)
    val _ = argty = ``:num$num`` orelse failwith "Need :num as first argty"
    fun findmax (t, acc) = let
      val (f, args) = strip_comb t
    in
      if f = c then let
          val n = Arbnum.toInt (numSyntax.dest_numeral (hd args))
        in
          if n >= acc then n + 1
          else acc
        end
      else if mem f cs then acc
      else acc
    end
    val max = List.foldl findmax 0 avoids
    fun mk_value ty tm = let
      val (d,r) = dom_rng ty
    in
      mk_value r (mk_comb(tm, mk_arb d))
    end handle HOL_ERR _ => tm
    val instwith =
        mk_value rngty (mk_comb(c,numSyntax.mk_numeral (Arbnum.fromInt max)))
  in
    warn ("Freshness instantiation for variable "^ #1 (dest_var v)^" : "^
           term_to_string instwith);
    SOME {redex = v, residue = instwith}
  end handle Empty => NONE
           | HOL_ERR _ => NONE
  fun foldthis (k,v,acc) =
      case resolve_cst acc (k,v) of
        NONE => acc
      | SOME i => i::acc
in
  Binarymap.foldl foldthis [] cdb
end

fun ground_trace hnd tracefile = let
  val _ =
    if FileSys.access (tracefile, [FileSys.A_READ]) then ()
    else (warn ("Trace file "^tracefile^" doesn't exist - skipping it");
          raise Fail "NOFILE")

  val namedthms = DiskThms.read_file tracefile
  val _ = warn ("Loaded trace from disk file "^tracefile)

  val trace = extract_trace namedthms
  val lasthyps = hyp (last trace)

  open ground_tickers
  val (tick_inst, tickhypelims) = time_analyse_hyps lasthyps
  val _ = warn "Computed ticker instantiations"

  fun do_inst inst th = let
    fun foldthis({redex,residue},th) =
        ADD_ASSUM (mk_eq(redex,residue)) th
  in
    testEval.eliminate_hyp_equalities hnd (List.foldl foldthis th inst)
  end

  fun do_cuts cutths th = List.foldl (uncurry PROVE_HYP) th cutths

  val last_tick_insted0 = do_cuts tickhypelims (do_inst tick_inst (last trace))
  val last_tick_simped = valOf (ctxt_then_body hnd last_tick_insted0)

  val rate_inst = let
    fun filtthis t = let
      val (n, ty) = dest_var t
    in
      type_of t = realSyntax.real_ty andalso
      String.isPrefix "rate" n
    end
  in
    map (fn t => {redex = t, residue = realSyntax.term_of_int Arbint.one})
        (List.filter filtthis (free_varsl (hyp last_tick_simped)))
  end

  val last_tick_with_rates =
      valOf (ctxt_then_body hnd (do_inst rate_inst last_tick_simped))
  val _ = warn "Eliminated various rate constraints"



val last_with_freshness = let
  val th = last_tick_with_rates
in
  valOf (ctxt_then_body hnd (do_inst (do_freshness th) th))
end
val _ = warn "Instantiated freshness variables";

val remaining_hyps = filter (not o is_vrecord) (hyp last_with_freshness)

val arith_th = let
  val int_inst = find_int_inst.find_int_inst remaining_hyps
in
  if not (null int_inst) then
    valOf (ctxt_then_body hnd (do_inst int_inst last_with_freshness))
  else last_with_freshness
end

val remaining_hyps = filter (not o is_vrecord) (hyp arith_th)
val remaining_vars = HOLset.listItems (FVL remaining_hyps empty_tmset)

fun record_elim (v, th) = let
  val vty = type_of v
in
  if not (null (TypeBase.fields_of vty)) then let
      val {Thy,Tyop,...} = dest_thy_type vty
      val nchot = concl (ISPEC v (DB.fetch Thy (Tyop ^ "_literal_nchotomy")))
      val _ = warn ("N-chotomising variable "^ #1 (dest_var v) ^ " of type "^
                    Tyop)
    in
      valOf (ctxt_then_body hnd (ADD_ASSUM nchot th))
    end
  else th
end

val arith_th = List.foldl record_elim arith_th remaining_vars

fun extract_inst th = let
  val vrecs = List.mapPartial (Lib.total dest_vrecord) (hyp th)
  fun to_inst t =
      if is_var t then (t |-> mk_arb (type_of t))
      else lhs t |-> rhs t
in
  map to_inst vrecs
end

val finalinst = extract_inst arith_th

fun elim_vrecords th = let
  fun elimth (t, th) =
      PROVE_HYP (EQT_ELIM (ISPEC (dest_vrecord t) boolTheory.DATATYPE_TAG_THM))
                th
      handle HOL_ERR _ => th
in
  HOLset.foldl elimth th (hypset th)
end

fun finalise_th accmap th = let
  val base = elim_vrecords (INST finalinst th)
  fun one_thm acclist th = let
    fun disch(h, (accmap, th)) = let
      val th' = DISCH h th
      val (imp,con) = dest_imp (concl th')
    in
      case Binarymap.peek (accmap, h) of
        NONE => let
          val imp_simped = QCONV (SIMP_CONV phase2_ss []) imp
        in
          if rhs (concl imp_simped) = boolSyntax.T then let
              val imp_T = EQT_ELIM imp_simped
            in
              (Binarymap.insert(accmap, concl imp_T, imp_T), MP th' imp_T)
            end
          else (accmap, UNDISCH th')
        end
      | SOME imp_T => (accmap, MP th' imp_T)
    end
  in
    HOLset.foldl disch (accmap,th) (hypset th)
  end
  val (accmap, th) = one_thm accmap base
in
  (accmap, SIMP_RULE phase2_ss [] th)
end

fun finalise_theorems n (accmap, accths) thlist =
  case thlist of
    [] => (accmap, List.rev accths)
  | th::ths => let
      fun pad w n = StringCvt.padLeft #" " w (Int.toString n)
      val _ = print ("Grounding theorem #"^pad 3 n)
      val _ = print (" (accmap: "^pad 4 (Binarymap.numItems accmap))
      val _ = print (", hyps: " ^ pad 4 (HOLset.numItems (hypset th)))
      val _ = print ")\n"
      val (accmap', th') = finalise_th accmap th
    in
      finalise_theorems (n + 1) (accmap', th'::accths) ths
    end

val tickmap = List.foldl (fn (th,map) => Binarymap.insert(map,concl th, th))
                         (Binarymap.mkDict Term.compare)
                         tickhypelims
val (final_acc, final_trace) = finalise_theorems 1 (tickmap, []) trace

fun checklist thl = let
  fun recurse n lasthost thl =
      case thl of
        [] => true
      | h :: t => let
          val (_, args) = strip_comb (concl h)
          val host0 = List.nth(args, 3)
          val host = last args
        in
          (null (free_varsl (concl h :: hyp h)) orelse
           raise Fail ("free vars in thm #"^Int.toString n)) andalso
          (null (hyp h) orelse
           raise Fail ("Hypothesis remains in thm #"^Int.toString n)) andalso
          (aconv lasthost host0 orelse
           raise Fail ("Hosts don't match in thm #"^Int.toString n)) andalso
          recurse (n + 1) host t
        end
in
  recurse 0 (List.nth (#2 (strip_comb (concl (hd thl))), 3)) thl
end

in
  (if checklist final_trace then
     (warn "Trace grounded successfully.";
      output_trace (tracefile ^ ".grounded") final_trace;
      true)
   else
     (output_trace (tracefile ^ ".weird") final_trace ; false))
  handle Fail s => (warn s;
                    output_trace (tracefile ^ "ungrounded") final_trace;
                    false)

end

open GroundTraceMain
fun do_one_file arg =
    ok := ((ground_trace TextIO.stdErr arg handle Fail s => false)
           andalso !ok)

val _ = app do_one_file args

open OS.Process
val _ = if !ok then exit success else exit failure

end (* struct *)