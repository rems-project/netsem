structure fmap_match :> fmap_match =
struct

open HolKernel boolLib

fun fmkey_match simp fmpat concmap = let
  open finite_mapSyntax pairSyntax
  val (fmpat0, kv) = dest_fupdate fmpat
  val (conckey, vpat) = dest_pair kv
  fun extract fmap = let
    val (cmap, kv) = dest_fupdate fmap
    val (k,v) = dest_pair kv
  in
    if Term.aconv conckey k then
      (v, cmap, NONE)
    else let
        val (v, cmap0, th0_opt) = extract cmap
	val th_opt = Option.map (fn th => RATOR_CONV (RAND_CONV (K th)) fmap)
				th0_opt
        val noteq_th = EQT_ELIM (simp (mk_neg(mk_eq(conckey, k))))
        val t =
	    case th_opt of
	      NONE => fmap
	    | SOME th => rhs (concl th)
        val comm_th0 = PART_MATCH (lhs o rand)
                                  finite_mapTheory.FUPDATE_COMMUTES
                                  t
	val comm_th = MP comm_th0 noteq_th
	val th = case th_opt of NONE => comm_th | SOME th0 => TRANS th0 comm_th
      in
        (v,mk_fupdate(cmap0,kv),SOME th)
      end
  end
  val (v_inst, map_inst, eqth) = extract concmap
  val fm_inst = if is_var fmpat0 then [fmpat0 |-> map_inst]
                else #1 (match_term fmpat0 map_inst)
  val v_inst = if is_var vpat then [vpat |-> v_inst]
               else #1 (match_term vpat v_inst)
  (* hope two insts are compatible *)
in
  (fm_inst @ v_inst, Option.map SYM eqth)
end


datatype posn = Left | Right
type inst = {redex:term, residue:term} list
type preconv = (posn list * thm option) list
type task = term * term * posn list


fun match d s limit (acc as (sigma,cnv)) deferred_fms tasklist = let
  val fullmatch = match
  val match = match (d - 1) s limit
  val simp = s
in
  if d = 0 then (acc, deferred_fms, tasklist)
  else
  case tasklist of
    [] => if length deferred_fms < limit then
            fullmatch (d - 1) s (length deferred_fms) acc [] deferred_fms
          else
            (acc, deferred_fms, tasklist)
  | (p,c,posn) :: rest => let
      open finite_mapSyntax
      fun adjust_task0 i (p,c,posn) = (Term.subst i p, c, posn)
      fun adjust_tasks i = map (adjust_task0 i)
    in
      if is_fupdate p then let
          val (pfm, pkv) = dest_fupdate p
          val (pk,pv) = pairSyntax.dest_pair pkv
          val (cfm, ckv) = dest_fupdate c
          val (ck, cv) = pairSyntax.dest_pair ckv
        in
          if is_var pk then
            match acc ((p,c,posn)::deferred_fms) rest
          else let
              val (i,th) = fmkey_match simp p c
            in
              match (i @ sigma, (posn,th) :: cnv)
                    (adjust_tasks i deferred_fms)
                    (adjust_tasks i rest)
            end
        end
      else
        case dest_term p of
          VAR _ => let
            val i = [p |-> c]
          in
            match (i @ sigma, cnv)
                  (adjust_tasks i deferred_fms)
                  (adjust_tasks i rest)
          end
        | CONST _ => if aconv p c then
                       match acc deferred_fms rest
                     else raise Fail ("failed to match " ^
                                      #Name (dest_thy_const p))
        | COMB(p1,p2) => let
            val (c1, c2) = dest_comb c
                handle HOL_ERR _ => raise Fail "Comb in pattern fails to match"
          in
            match acc deferred_fms
                  ((p1,c1,Left::posn) :: (p2,c2,Right::posn) :: rest)
          end
        | LAMB _ => raise Fail "Can't match pattern abstractions"
    end
end

fun count_updates t = let
  open finite_mapSyntax
  fun recurse acc tlist =
      case tlist of
        [] => acc
      | t::ts => if is_fupdate t then
                   recurse (acc + 1) ts
                 else let
                   in
		     case dest_term t of
		       VAR _ => recurse acc ts
		     | CONST _ => recurse acc ts
		     | COMB(t1,t2) => recurse acc (t1::t2::ts)
		     | LAMB(_, b) => recurse acc (b::ts)
                   end
in
  recurse 0 [t]
end

fun preconv2conv pc0 t = let
  val pc = List.mapPartial (fn (p, th) => if isSome th then
					     SOME (List.rev p, valOf th)
					  else NONE)
			   pc0
  fun split (acc as (heres, lefts, rights)) pths =
      case pths of
	[] => acc
      | ([], th) :: rest => split (th :: heres, lefts, rights) rest
      | (Left::prest, th) :: rest =>
	split (heres, (prest,th) :: lefts, rights) rest
      | (Right::prest, th) :: rest =>
	split (heres, lefts, (prest,th)::rights) rest
  fun traverse pths =
      case pths of
	[] => ALL_CONV
      | _ => let
	  val (heres,lefts,rights) = split ([],[],[]) pths
	in
	  case heres of
	    [] => RATOR_CONV (traverse lefts) THENC
		  RAND_CONV (traverse rights)
	  | th :: _ => K th
	end
in
  traverse pc t
end

fun apply_mresult (i,pc) th = let
  val ith = INST i th
in
  CONV_RULE (preconv2conv pc) ith
end

fun fm_match simp p c = let
  val cnt = count_updates p + 1
  val (acc, tlist, _) =   match ~1 simp cnt ([], []) [] [(p,c,[])]
in
  (acc, tlist)
end

end (* struct *)
