(* A HOL98 specification of TCP *)

(* This file contains helper functions for the symbolic evaluator *)
structure Evaluator =
struct

open HolKernel boolLib simpLib BasicProvers

fun expansion_type expth =
    type_of (bvar (rand (lhs (#2 (dest_forall (concl expth))))))

fun exp_is_forall expth =
    is_forall (lhs (#2 (dest_forall (concl expth))))

fun exp_is_exists expth =
    is_exists (lhs (#2 (dest_forall (concl expth))))

fun find_forall_for ty thlist =
    List.find (fn th => expansion_type th = ty andalso exp_is_forall th) thlist

(* cases = case theorem for reduction relation
   inputlist = list of numbers corresponding to those positions in the
               relation that correspond to "input" parameters, others are
               outputs, natch.
   prodexpansions = expansion theorems for record types *)
fun general_cases_munger cases inputlist prodexpansions = let
  fun apply_inputexpansions t = let
    fun recurse n t = let
      val (v, _) = dest_forall t
      val finisher =
          if mem n inputlist then
            case find_forall_for (type_of v) prodexpansions of
              NONE => ALL_CONV
            | SOME th => HO_REWR_CONV th
          else ALL_CONV
    in
      (BINDER_CONV (recurse (n + 1)) THENC finisher) t
    end handle HOL_ERR _ => ALL_CONV t
  in
    recurse 0 t
  end
  val exists_exps = GSYM RIGHT_EXISTS_AND_THM ::
                    GSYM LEFT_EXISTS_AND_THM ::
                    List.filter exp_is_exists prodexpansions
in
  CONV_RULE (apply_inputexpansions THENC
             STRIP_QUANT_CONV
               (RAND_CONV (SIMP_CONV (srw_ss()) exists_exps)))
            cases
end

fun EQ_CONJ_CONV t = let
  (* t is a conjunction.  If any of the conjuncts are non-recursive
     equalities between single variables and anything else, replace all
     other occurrences of that single variable with the other side of the
     equality *)
  val cs = strip_conj t
  fun is_var_eq t = let
    val (l,r) = dest_eq t
  in
    if is_var l andalso not (free_in l r) then SOME true
    else if is_var r andalso not (free_in r l) then SOME false
    else NONE
  end handle HOL_ERR _ => NONE
  fun check others t =
      case is_var_eq t of
        SOME true => exists (free_in (lhs t)) others
      | SOME false => exists (free_in (rhs t)) others
      | NONE => false
  fun findpos0 P acc [] = NONE
    | findpos0 P acc (h::t) = if P (acc @ t) h then SOME(h, length acc)
                              else findpos0 P (h::acc) t
  fun findpos P l = findpos0 P [] l
  fun traverse current to_avoid f t =
      if current > to_avoid then (f t, ~1)
      else let
          val (l, r) = dest_conj t
          val (newl, newc) = traverse current to_avoid f l
          val (newr, c) = traverse newc to_avoid f r
        in
          (mk_conj (newl, newr), c)
        end handle HOL_ERR _ =>
                   if current = to_avoid then (t, current + 1)
                   else (f t, current + 1)
in
  case findpos check cs of
    SOME (eqn, i) => let
      val (v, orientation) = if is_var (lhs eqn) then (lhs eqn, true)
                             else (rhs eqn, false)
      val gv = genvar (type_of v)
      val (template, _) = traverse 0 i (subst [v |-> gv]) t
      val t_th = ASSUME t
      val eq_th0 = List.nth (CONJUNCTS t_th, i)
      val eq_th = if orientation then eq_th0 else SYM eq_th0
      val forward = SUBST [gv |-> eq_th] template t_th
      val t_th = ASSUME (concl forward)
      val eq_th0 = List.nth (CONJUNCTS t_th, i)
      val eq_th = if orientation then eq_th0 else SYM eq_th0
      val back = SUBST [gv |-> SYM eq_th] template t_th
    in
      IMP_ANTISYM_RULE (DISCH_ALL forward) (DISCH_ALL back)
    end
  | NONE => NO_CONV t
end

end (* struct *)
