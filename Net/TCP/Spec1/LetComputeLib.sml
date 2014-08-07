structure LetComputeLib :> LetComputeLib =
struct

open HolKernel Parse LetComputeTheory boolLib

val _ = Version.register "$RCSfile: LetComputeLib.sml,v $" "$Revision: 1.17 $" "$Date: 2005/07/14 02:12:23 $";

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars LetComputeTheory.LetCompute_grammars
end
open Parse

val ERR = mk_HOL_ERR "LetComputeLib"

(* manifest constants, tweakable parameters, if you like *)
val comp_limit = 10
val unknown_const_value = 20

(* the CLET library's most important terms *)
val CLET_t = ``LetCompute$CLET``
val value_t = ``LetCompute$value``
val pending_t = ``LetCompute$pending``

fun dest_clet t = let
  val (f, args) = strip_comb t
  val _ = assert (same_const CLET_t) f
in
  case args of
    [bdy, value] => (bdy, value)
  | _ => raise ERR "dest_clet" "Not a clet"
end
val is_clet = can dest_clet

fun dest_pending t = let
  val (f, x) = dest_comb t
  val _ = assert (same_const pending_t) f
      handle HOL_ERR _ => raise ERR "dest_pending" "Term not a pending"
in
  x
end
val is_pending = can dest_pending



fun count_occurrences acc v t =
    case dest_term t of
      VAR _ => if t = v then acc + 1 else acc
    | CONST _ => acc
    | COMB(f,x) => count_occurrences (count_occurrences acc v f) v x
    | LAMB(v', b) => if v = v' then acc
                     else count_occurrences acc v b


(* ----------------------------------------------------------------------
    CLET_CONV

    CLET_CONV performs a beta reduction through a let if
      * the argument is a variable or a constant; or
      * the argument is a value tag wrapped around a variable or constant; or
      * the argument has a value tag, and the bound variable occurs just once
        in the body of the abstraction;

   ---------------------------------------------------------------------- *)

fun CLET_CONV t = let
  val (f, args) = strip_comb t
  val _ = assert (same_const CLET_t) f
  val _ = assert (fn t => length t = 2) args
  val [vbody, v_arg] = args
  val (v, body) = dest_abs vbody
  (* can't be bothered with paired or anded lets *)
  val value_conv = (* to be called when value has a value tag *)
      REWR_CONV LetComputeTheory.CLET_THM THENC
      RAND_CONV (REWR_CONV LetComputeTheory.value_def) THENC
      BETA_CONV
in
  if is_var v_arg orelse is_const v_arg then
    REWR_CONV LetComputeTheory.CLET_THM THENC BETA_CONV
  else if (same_const (rator v_arg) value_t handle HOL_ERR _ => false) then
    if is_var (rand v_arg) orelse is_const (rand v_arg) then
      value_conv
    else let
        val c = count_occurrences 0 v body
      in
        if c = 1 then value_conv
        else NO_CONV
      end
  else NO_CONV
end t

(* ----------------------------------------------------------------------
    structure_reduction_CONV

    takes a term of the form
      CLET (\v. f v) (structure e1 e2 .. en)
    and translates this into

      let v_1 = e1 in
      let v_2 = e2 in
      ...
      let v_n = en in
        f (structure v_1 v_2 .. v_n)

    This is similar to what happens with constructors that are not
    being treated aggressively, but "structure" can be any complicated
    tree structure of constants, with the constants pulled from a
    dictionary of acceptable terms.
   ---------------------------------------------------------------------- *)

val boring_ts = [combinSyntax.K_tm, combinSyntax.o_tm]
fun interestingp t =
    List.find (same_const t) boring_ts = NONE
fun app_letter ty = let
  fun c1 s = String.extract(s, 0, SOME 1)
in
  c1 (#1 (dest_type ty))
  handle HOL_ERR _ => String.substring (dest_vartype ty, 1, 1)
end

fun isSuffix s1 s2 =
    if size s1 > size s2 then false
    else
      String.extract(s2, size s2 - size s1, SOME (size s1)) = s1

fun takewhile p [] = []
  | takewhile p (x::xs) = if p x then x :: takewhile p xs else []

val brss = GrammarSpecials.bigrec_subdivider_string
fun namer basev = let
  val (basename,_) = dest_var basev
  fun rest path ty = let
    val interesting_path = filter (interestingp o #1) path
    val (first_interesting_t, n) = hd interesting_path
    val (nm, _) = dest_const first_interesting_t
  in
    if isSuffix "_fupd" nm then let
        val rest = String.substring(nm, 0, size nm - 5)
        val delim =
            if is_substring brss rest then brss else "_"
        val (tyname, fld) = Substring.position delim (Substring.all rest)
        val fld = String.extract(Substring.string fld, size delim, NONE)
      in
        mk_var(basename ^ "_" ^ fld, ty)
      end
    else if same_const pairSyntax.comma_tm first_interesting_t then let
        val tuplepath =
            takewhile (same_const pairSyntax.comma_tm o #1) interesting_path
        val numstring = String.concat (map (Int.toString o #2)
                                           (List.rev tuplepath))
      in
        mk_var(basename ^ "_" ^ app_letter ty ^ numstring, ty)
      end
    else mk_var(app_letter ty, ty)
  end handle List.Empty => mk_var(app_letter ty, ty)
in
  rest
end

(* ----------------------------------------------------------------------
    create_skeleton strmap avoids v t

    produces a term-skeleton skel and an instantiation map, phi such that

      inst phi skel = t

    skel is made up solely of variables that appear in the domain of phi
    and constants that appear in the strmap.  The variables in the domain
    of phi are further chosen to avoid the list of variables given in
    avoids.  To be represented in teh skeleton, the head of a application
    must be a constant in the strmap.
  ---------------------------------------------------------------------- *)

exception NoChange
fun create_skeleton0 strmap avoid_vars v path vars t = let
  val create_skeleton = create_skeleton0 strmap avoid_vars v
in
  if is_const t orelse is_var t then raise NoChange
  else let
      val (f, args) = strip_comb t
      fun c2ids t = let val {Name,Thy,...} = dest_thy_const t in (Name,Thy) end
    in
      if HOLset.member(strmap, f) then let
          fun foldthis (t, (all_unchanged, n, skels, vars)) = let
            val (unc, (skel, vars)) =
                (false, create_skeleton ((f,n)::path) vars t)
                handle NoChange => (true, (t, vars))
          in
            (unc andalso all_unchanged, n + 1, skel :: skels, vars)
          end
          val (unc, _, skel_args, vars) =
              List.foldl foldthis (true,1,[],vars) args
          val skel_args = List.rev skel_args
        in
          if unc then raise NoChange
          else
            (list_mk_comb(f, skel_args), vars)
        end
      else let
          val (vars_l, varmap) = vars
          val var = variant (avoid_vars @ vars_l) (namer v path (type_of t))
        in
          (var, (var::vars_l, Binarymap.insert(varmap, var, t)))
        end
    end
end

fun create_skeleton strmap avoid_vars v t = let
  val vars0 = Binarymap.mkDict Term.compare
  val (skel, (_, vars)) =
      create_skeleton0 strmap avoid_vars v [] ([], vars0) t
      handle NoChange => (t, ([], vars0))
in
  (skel, vars)
end






fun structure_reduction_CONV strmap t = let
  val (clet_t, args) = strip_comb t
  val _ = length args = 2 andalso same_const clet_t CLET_t orelse
          raise ERR "structure_reduction_CONV" "Not applicable"
  val (absfn, value) = (hd args, hd (tl args))
  val avoid_vars = free_varsl [absfn, value]
  val (should_be_value_t, value) = dest_comb value
  val _ = assert (same_const value_t) should_be_value_t
  val (v, body) = dest_abs absfn
  val (skel, vars) = create_skeleton strmap avoid_vars v value
  val _ = assert (not o is_var) skel
  fun mk_clet (var, body, value) = let
    val absn = mk_abs(var, body)
    val clet =
        mk_thy_const{Name = "CLET", Thy = "LetCompute",
                     Ty = type_of absn --> type_of value --> type_of body}
    val value_t = inst [alpha |-> type_of value] value_t
  in
    list_mk_comb(clet, [absn, mk_comb(value_t, value)])
  end
  fun foldthis (v, t, result) = mk_clet(v, result, t)
  val new_term = Binarymap.foldl foldthis (subst [v |-> skel] body) vars
  val normleft = RAND_CONV (REWR_CONV value_def) THENC
                 REWR_CONV CLET_THM THENC BETA_CONV
  fun normright n = if n = 0 then ALL_CONV
                    else normleft THENC normright (n - 1)
  val normed_left = normleft t
  val normed_right = SYM (QCONV (normright (Binarymap.numItems vars)) new_term)
in
  TRANS normed_left normed_right
end

fun pending_structure_reduction_CONV strmap t = let
  val (should_be_pending, eqn) = dest_comb t
  val inapplicable = ERR "pending_structure_reduction_CONV" "Not applicable"
  val _ = assert (same_const pending_t) should_be_pending
          handle HOL_ERR _ => raise inapplicable
  val (var, value) = dest_eq eqn handle HOL_ERR _ => raise inapplicable
  val avoids = free_vars value
  val (skel, vars) = create_skeleton strmap avoids var value
  val _ = assert (not o is_var) skel handle HOL_ERR _ => raise inapplicable
  val new_base = mk_eq(var, skel)
  fun mk_clet (v, subvalue, result) = let
    val clet_t = inst [alpha |-> type_of v, beta |-> type_of result] CLET_t
  in
    list_mk_comb(clet_t, [mk_abs(v, result), subvalue])
  end
  val new_term = Binarymap.foldl mk_clet new_base vars
  fun unwind_n_clets n = if n = 0 then ALL_CONV
                         else REWR_CONV CLET_THM THENC BETA_CONV THENC
                              unwind_n_clets (n - 1)
in
  (SYM o
   (unwind_n_clets (Binarymap.numItems vars) THENC
    REWR_CONV (GSYM pending_def)))
  new_term
end






fun record_update_fns tyname = let
  val ((thy, _), (th, _)) = hd (DB.find (tyname ^ "_fn_updates"))
  fun consts_from_fupd_thm th =
      map (#1 o strip_comb o lhs o #2 o strip_forall) (strip_conj (concl th))
  val upds = consts_from_fupd_thm th
  val subupd_fns = let
    val upd1 = hd upds
    val (name, updty) = dest_const upd1
  in
    if is_substring GrammarSpecials.bigrec_subdivider_string name then let
        fun get_subtype ty = #1 (dom_rng (#1 (dom_rng ty)))
        fun name ty = #1 (dest_type ty)
        fun get_subupds upd = let
          val subty = get_subtype (type_of upd)
          val th = DB.fetch thy (name subty ^ "_fn_updates")
        in
          consts_from_fupd_thm th
        end
      in
        List.concat (map get_subupds upds)
      end
    else []
  end
in
  upds @ subupd_fns
end






(* ----------------------------------------------------------------------
    pending_CONV

    eliminates pending(x) terms (which will appear as hypotheses).
    If x is not an equality, or if x is an equality of the wrong sort
    of shape, then pending(x) simply becomes x.
   ---------------------------------------------------------------------- *)



fun pending_CONV t = let
  val (f, arg) = dest_comb t
  val _ = assert (same_const pending_t) f
in
  if not (is_eq arg) then REWR_CONV pending_def
  else let
      val (l, r) = dest_eq arg
      fun okeq(l,r) = is_var l andalso not (free_in l r)
    in
      if is_var l andalso is_var r then REWR_CONV pending_def
      else if okeq(r,l) then RAND_CONV (REWR_CONV EQ_SYM_EQ)
      else if okeq(l,r) then NO_CONV
      else REWR_CONV pending_def
    end
end t

(* ----------------------------------------------------------------------
    CLET_UNWIND
   ---------------------------------------------------------------------- *)

fun push_CLET_in c t =
    (* pushes the let at the top of t into t through as many lets
       lying underneath it as possible, and then applies c at that point.
       Thus, c will be applied to a term where CLET_CLET_TRANSPOSE doesn't
       apply, but this point may still be a let.  *)
    ((HO_REWR_CONV CLET_CLET_TRANSPOSE THENC
      LAND_CONV (ABS_CONV (push_CLET_in c))) ORELSEC
     c) t

fun rearrange_conjs c =
  (* argument is a conjunction of many things, including at least one
     instance of c; re-arrange it so that it is of the form c /\
     otherstuff will fail if there isn't a c *)
    markerLib.move_conj_left (equal c)

val elimination_thm = prove(
  ``(?x. (x = e) /\ P x) = CLET (\x. P x) e``,
  simpLib.SIMP_TAC boolSimps.bool_ss [CLET_THM]);

val not_elim = prove(``~p = (p = F)``, REWRITE_TAC [])
val eqt_intro = prove(``p = (p = T)``, REWRITE_TAC [])

fun EXISTS_TO_LET_CONV eqn t = let
  (* t is of form ?x. body, where body is a series of conjuncts, one
     of which is eqn.  Move that eqn to leftmost position, and eliminate it
     by appealing to the theorem |- (?x. (x = e) /\ P x) = let x = e in P x,
     (elimination_thm above) *)
  val (v, body) = dest_exists t
  fun mk_eqn t0 = let
  in
    if is_eq t0 then
      if lhs t0 = v then ALL_CONV
      else REWR_CONV EQ_SYM_EQ
    else if is_neg t0 then REWR_CONV not_elim
    else REWR_CONV eqt_intro
  end t0
  val renamed_elimination =
      CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV (ALPHA_CONV v))))
                (INST_TYPE [alpha |-> type_of v] elimination_thm)
in
  BINDER_CONV (rearrange_conjs eqn THENC
               FORK_CONV (mk_eqn, UNBETA_CONV v)) THENC
  REWR_CONV renamed_elimination THENC
  LAND_CONV (BINDER_CONV BETA_CONV)
end t





fun push_in_and_eliminate v eqn t = let
  (* t is an existentially quantified term, v is one of the
     existentially bound variables.  Push v to the bottom of the list
     of variables, and then over any lets that may be at the top level
     of the body, and then call EXISTS_TO_LET_CONV. *)
  fun start c t = let
    val (v', _) = dest_exists t
  in
    if v' = v then c t
    else BINDER_CONV (start c) t
  end
  fun push_over_exes c t =
      ((HO_REWR_CONV SWAP_EXISTS_THM THENC
        BINDER_CONV (push_over_exes c)) ORELSEC
       c) t
  fun push_over_lets c t =
      ((HO_REWR_CONV EXISTS_CLET_THM THENC
        LAND_CONV (ABS_CONV (push_over_lets c))) ORELSEC
       c) t
in
  start (push_over_exes (push_over_lets (EXISTS_TO_LET_CONV eqn))) t
end

datatype dir = L | R
fun CLET_UNWIND tm = let
  (* tm is an existential formula.  Check tm's body for eliminable
     equalities, including those that may be lurking in the bodies of CLET
     expressions.  If one is found, pull it out from underneath any lets,
     and then call push_in_and_eliminate *)
  val (vs, body) = strip_exists tm
  fun look_for_eqn pth must_avoid t = let
    (* look for an eliminable eqn for one of the variables in vs,
       and return the "let-path" to get to that eqn.
       The let path is the sequence of left-right moves needed to
       find the eqn in the body amongst its conjuncts.  The empty path
       corresponds to no lets to be moved.

       Assume:  1.  t has no existentials in it (they've all been moved
                    up to the top of the term), and are now above us.
                2.  All the lets are over single variable abstractions.
                    Occurrences of LET (UNCURRY f) e must have been removed.
    *)
    val (hdop, args) = strip_comb t
  in
    case args of
      [arg1, arg2] => let
        val {Name,Thy,...} = dest_thy_const hdop
                             handle HOL_ERR _ => {Name = "", Thy = "",
                                                  Ty = bool}
      in
        case (Name, Thy) of
          ("/\\", "bool") => let
          in
            case look_for_eqn (L :: pth) must_avoid arg1 of
              NONE => look_for_eqn (R :: pth) must_avoid arg2
            | x => x
          end
        | ("CLET", "LetCompute") => let
            val value = arg2
            open HOLset
            val (letbv, body) = dest_abs arg1
            val letvars = FVL [letbv] empty_tmset
            val valfvs = FVL [value] empty_tmset
            fun calc_new_avoid(v, avoid) =
                if not (isEmpty(intersection(valfvs, avoid))) then
                  union(avoid, letvars)
                else avoid
            val must_avoid = Binarymap.map calc_new_avoid must_avoid
          in
            look_for_eqn pth must_avoid body
          end
        | ("=", "min") => let
            open HOLset
            fun consider_pair(var, valuepart) =
                if is_var var then
                  case Binarymap.peek (must_avoid, var) of
                    NONE => NONE
                  | SOME set => let
                      val fvs = FVL [valuepart] empty_tmset
                    in
                      if isEmpty (intersection(set, fvs)) then
                        SOME (t, var, List.rev pth, set)
                      else NONE
                    end
                else NONE
          in
            case consider_pair (arg1, arg2) of
              NONE => consider_pair (arg2, arg1)
            | x => x
          end
        | _ => NONE
      end
    | [arg1] => if same_const hdop boolSyntax.negation andalso is_var arg1
                then
                  case Binarymap.peek(must_avoid, arg1) of
                    NONE => NONE
                  | SOME set => SOME (t, arg1, List.rev pth, set)
                else NONE
    | [] => if is_var t then
              case Binarymap.peek(must_avoid, t) of
                NONE => NONE
              | SOME set => SOME (t, t, List.rev pth, set)
            else NONE
    | x => NONE
  end
  fun foldthis (v, m) = Binarymap.insert(m, v, HOLset.singleton Term.compare v)
  val avoids0 = List.foldl foldthis (Binarymap.mkDict Term.compare) vs
  fun rearrange_body (eqn, path, avoids) t = let
    (* working at the level below the existential quantifiers,
       transform t so that it looks like a (possibly empty) chain of
       lets, all of which we'll be able to push the existential of var
       over, with a set of conjuncts underneath, where one of the
       conjuncts is an eliminable equation involving var.  The set
       avoids tells us which lets will have to be pushed out of the
       way. *)
    val (f, args) = strip_comb t
  in
    case args of
      [arg1, arg2] => let
        val {Name,Thy,...} = dest_thy_const f
            handle HOL_ERR _ => {Name = "", Thy = "", Ty = bool}
      in
        case (Name, Thy) of
          ("/\\", "bool") => let
            val (conval, rwt) =
                case hd path of
                  L => (LAND_CONV, LEFT_CLET_AND_THM)
                | R => (RAND_CONV, RIGHT_CLET_AND_THM)
            fun pull_lets_out t =
                TRY_CONV (HO_REWR_CONV rwt THENC
                          LAND_CONV (ABS_CONV pull_lets_out)) t

          in
            conval (rearrange_body (eqn, tl path, avoids)) THENC
            pull_lets_out
          end
        | ("CLET", "LetCompute") => let
            val (letvar, letbody) = dest_abs arg1
            val continuation = let
              val deepc =
                  (LAND_CONV (ABS_CONV (rearrange_conjs eqn)) THENC
                   HO_REWR_CONV (SYM RIGHT_CLET_AND_THM)) ORELSEC
                  REWR_CONV CLET_SIMP
            in
              if HOLset.member(avoids, letvar) then
                (* have to move this let down, and then out of the way *)
                push_CLET_in deepc
              else ALL_CONV
            end
          in
            LAND_CONV (ABS_CONV (rearrange_body(eqn, path, avoids))) THENC
            continuation
          end
        | _ => ALL_CONV
      end
    | _ => ALL_CONV
  end t
in
  case look_for_eqn [] avoids0 body of
    SOME (eqn, var, path, avoids) =>
    STRIP_QUANT_CONV (rearrange_body (eqn, path, avoids)) THENC
    push_in_and_eliminate var eqn
  | NONE => NO_CONV
end tm

(* ----------------------------------------------------------------------
    draw_out_fmaps

    traverse a term of lets and conjunctions, and if any conjunct includes
    a variable of a finite-map type, attempt to draw that conjunct out
    past any lets that have scope over it.
   ---------------------------------------------------------------------- *)

fun is_movable_fmap_tm avoid t = let
  (* Predicate to determine whether or not a conjunct can be moved outside
     the scope of a let where it might then play a role in finite-map
     elimination (done by Net_fmap_analyse).

     A conjunct is only movable if it doesn't mention the avoid variable.
     It must further be one of the following forms:
       1. an inequality (useful for catching inequalities on keys)
       2. ~(k IN FDOM f)   (ditto)
       3. an equality on finite maps (these are the basic input to the
          finite-map analyser; the others are optional bonuses if they
          occur)
  *)
  fun unencumbered t = not (free_in avoid t)
  fun in_fdom t = let
    val (f, args) = strip_comb t
  in
    same_const f pred_setSyntax.in_tm andalso
    same_const (rand (hd (tl args))) finite_mapSyntax.fdom_t
  end
  fun interesting_undomain t = let
    val x = dest_neg t
  in
    in_fdom x orelse is_eq x
  end handle HOL_ERR _ => false
  fun fm_equality t = let
    val (_, t') = strip_forall t
    val (l, r, ty) = dest_eq_ty t'
  in
    finite_mapSyntax.is_fmap_ty ty
  end handle HOL_ERR _ => false

in
  unencumbered t andalso (fm_equality t orelse interesting_undomain t)
end

fun draw_out_fmaps t = let
  fun recurse t = let
    val (f, args) = strip_comb t
  in
    case args of
      [arg1, arg2] => let
        val {Name, Thy, ...} = dest_thy_const f
            handle HOL_ERR _ => {Name = "", Ty = bool, Thy = ""}
      in
        case (Name, Thy) of
          ("/\\", "bool") => BINOP_CONV recurse
        | ("CLET", "LetCompute") => let
            val (bv, body) = dest_abs arg1
            fun grab_fmaps t =
                (* move fmaps left ; fail if there were none *)
                (markerLib.move_conj_left (is_movable_fmap_tm bv) THENC
                 TRY_CONV (RAND_CONV grab_fmaps THENC REWR_CONV CONJ_ASSOC)) t
            val stage1 = if is_clet body then recurse else grab_fmaps
          in
            TRY_CONV (LAND_CONV (ABS_CONV stage1) THENC
                      HO_REWR_CONV (SYM RIGHT_CLET_AND_THM))
          end
        | _ => ALL_CONV
      end
    | _ => ALL_CONV
  end t
in
  recurse t
end

(* ----------------------------------------------------------------------
    cse_elim_CONV

    common sub-expression elimination.  A rather specialised instance
    of this.  Checks to see if a term matches

       CLET (\v. f v e) e

    and rewrites this to CLET (\v. f v v) e.  In other words, the only
    common sub-expressions eliminated are those that appear as pending
    computations outside lets.

    cse_elim_CONV does this for all outermost lets.
    cse_elim1_CONV does it for the top-level let, if any.
   ---------------------------------------------------------------------- *)

val cse_elim_thm = prove(
  ``CLET (\v. f v e) (value e) = CLET (\v. f v v) (value e)``,
  REWRITE_TAC [CLET_THM, value_def] THEN BETA_TAC THEN REWRITE_TAC [])

fun cse_elim1_CONV t = let
  val (fbody, value) = dest_clet t
  val (f, value) = dest_comb value
  val _ = assert (same_const value_t) f
  val (var, body) = dest_abs fbody
  val _ = assert (free_in value) body handle HOL_ERR _ => raise Conv.UNCHANGED
in
  LAND_CONV (BINDER_CONV (UNBETA_CONV value THENC
                          RATOR_CONV (UNBETA_CONV var))) THENC
  REWR_CONV cse_elim_thm THENC
  LAND_CONV (ALPHA_CONV var THENC
             BINDER_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV))
end t

fun cse_elim_CONV t =
    TRY_CONV (cse_elim1_CONV THENC
              TRY_CONV (LAND_CONV (BINDER_CONV cse_elim_CONV))) t

(* ----------------------------------------------------------------------
    grounded_let_CONV

    a conversion for allowing a let beta-reduction if the value is
    grounded (i.e., includes no free variables).  It is made into a
    "reducer", which means that the simplifier only applies it as a
    last resort.  This means in turn that ground value will get a
    chance to be simplified themselves before they are reduced.
   ---------------------------------------------------------------------- *)

fun has_free_var t = let
  fun recurse set t =
      case dest_term t of
        VAR _ => not (HOLset.member(set, t))
      | CONST _ => false
      | COMB(t1, t2) => recurse set t1 orelse recurse set t2
      | LAMB(v, b) => recurse (HOLset.add(set, v)) b
in
  recurse empty_tmset t
end

fun grounded_let_CONV t = let
  val (fbody, value) = dest_clet t
  val (f, value) = dest_comb value
  val _ = assert (same_const value_t) f
  val _ = assert (not o has_free_var) value
in
  REWR_CONV LetComputeTheory.CLET_THM THENC
  RAND_CONV (REWR_CONV LetComputeTheory.value_def) THENC
  BETA_CONV
end t

val grounded_reducer = let
  fun apply _ t =
      grounded_let_CONV t before
      Trace.trace(2, Trace.TEXT ("grounded_reducer reduces "^term_to_string t))
in
  Traverse.REDUCER {initial = Fail "", (* never used *)
                    addcontext = (fn (c, thl) => c), (* ctxt ignored *)
                    apply = apply}
end

(* ----------------------------------------------------------------------
    CLET_ss
   ---------------------------------------------------------------------- *)

val CLET_ss =
    simpLib.SSFRAG {ac = [], congs = [CLET_congruence],
                     convs = [{conv = K (K CLET_CONV),
                               key = SOME ([], ``CLET f x``),
                               name = "CLET_CONV", trace = 2},
                              {conv = K (K pending_CONV),
                               key = SOME ([], ``pending x``),
                               name = "pending_CONV", trace = 2}],
                     dprocs = [grounded_reducer], filter = NONE,
                     rewrs = [LetComputeTheory.LET_CLET,
                              combinTheory.C_ABS_L,
                              combinTheory.o_ABS_R,
                              pairTheory.C_UNCURRY_L,
                              pairTheory.o_UNCURRY_R,
                              LetComputeTheory.value_def,
                              LetComputeTheory.CLET_CLET_AND_ELIM]}

end; (* struct *)
