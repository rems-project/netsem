open HolKernel boolLib Parse BasicProvers bossLib



(* called to turn (?x. P x) ==> Q into !x. P x ==> Q, and to do this
   recursively as long as such a pattern exists at the top level *)
fun repeated_limp_ex_conv t =
    TRY_CONV (LEFT_IMP_EXISTS_CONV THENC
              BINDER_CONV repeated_limp_ex_conv) t

datatype ffc_act = Check of term | LoseBvar
fun find_free_conds bvars acc tlist =
    case tlist of
      [] => acc
    | Check t::ts => let
      in
        if is_cond t then let
            val (g, _, _) = dest_cond t
            val ok_guard = not (List.exists (C free_in g) bvars) andalso
                           not (can (find_term is_cond) g)
          in
            if ok_guard then
              find_free_conds bvars (t::acc) ts
            else find_free_conds bvars acc (Check g :: ts)
          end
        else
          case dest_term t of
            COMB(t1, t2) => find_free_conds bvars acc (Check t1::Check t2::ts)
          | LAMB(v, bod) => find_free_conds (v::bvars) acc
                                            (Check bod::LoseBvar::ts)
          | _ => find_free_conds bvars acc ts
      end
    | LoseBvar :: ts => find_free_conds (tl bvars) acc ts

fun best_eliminable_condguard limit tlist = let
  val conds = find_free_conds [] [] (map Check tlist)
  fun numfvs t = HOLset.numItems (FVL [t] empty_tmset)
  fun order(t1,t2) = Int.compare(numfvs t1, numfvs t2)

(*  fun order(t1, t2) =
      Int.compare(term_size t2, term_size t1) (* want bigger terms earlier *) *)in
  case List.find (fn t => term_size t > limit)
                 (Listsort.sort order conds)
   of NONE => NONE
    | SOME c => SOME (#1 (dest_cond c))
end


fun is_eliminable_equality t = let
  val (l, r) = dest_eq t
in
  is_var l andalso not (free_in l r) orelse
  is_var r andalso not (free_in r l)
end handle HOL_ERR _ => false

val existential_append_idiom0 = prove(
  (* this appears in deliver_in_3 *)
  ``!l1 conc. (conc = APPEND l1 (k :: l2)) =
              case conc of
                 [] -> F
              || h::t -> (k = h) /\ (t = l2) /\ (l1 = []) \/
                         (?l1'. (l1 = h::l1') /\ (t = APPEND l1' (k :: l2)))``,
  let open SingleStep in
    Induct THEN SRW_TAC [][] THEN Cases_on `conc` THEN
    SRW_TAC [][] THEN PROVE_TAC []
  end)

val existential_append_idiom = let
  val base = SPEC_ALL existential_append_idiom0
  (* only provide one specialisation, because the nil case
        [] = APPEND l1 (k :: l2)
     is already handled by the built-in rewrites, which know that
        ([] = APPEND l1 l2) = (l1 = []) /\ (l2 = [])
     and so rewrite the former to false without any extra help *)
in
  Phase.phase_imm 1
                  (SIMP_RULE (srw_ss()) [] (Q.INST [`conc` |-> `h::t`] base))
end
