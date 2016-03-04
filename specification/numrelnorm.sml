structure numrelnorm :> numrelnorm =
struct

(* code to normalise formulae involving = and <= over natural numbers *)

(* based on the existing code for doing normalisation within number terms
   in src/num/arith/src/numSimps.sml
*)

open HolKernel boolLib simpLib

val ERR  = mk_HOL_ERR "numrelnorm"


open Arbint numSyntax
datatype rel = leq | eq

(* used to represent the canonical form of a relation formula:
     - rel is the relation,
     - the term-int list is the list of sub-terms with coefficients.  Use
       the term ``1`` plus a coefficient to represent literals.
       A positive coefficient indicates that the term should be on the right
       of the relation symbol, while a negative coefficient says it should be
       on the left
*)
datatype lin = LIN of rel * (term, int) Binarymap.dict

fun mk_numeral i = numSyntax.mk_numeral (Arbint.toNat i)
fun dest_numeral t = Arbint.fromNat (numSyntax.dest_numeral t)

val one_tm = mk_numeral one


fun rel_to_mk leq = mk_leq
  | rel_to_mk eq = mk_eq

fun dest_rel t = let
  val (l, r) = dest_eq t
  val _ = assert (equal numSyntax.num o type_of) l
in
  (eq, l, r)
end handle HOL_ERR _ => let
             val (l, r) = dest_leq t
           in
             (leq, l, r)
           end
val is_rel = can dest_rel


fun tc_to_t (t, c) = if c = one then t
                     else if t = one_tm then mk_numeral c
                     else mk_mult(mk_numeral c, t)
fun negc (t, c) = (t, ~c)


fun lin_to_term (LIN (rel, terms)) = let
  fun foldthis (t, c, acc as (ls, rs)) =
      if c < zero then (tc_to_t (t, ~c) :: ls, rs)
      else if c > zero then (ls, tc_to_t (t, c) :: rs)
      else acc
  val (lefts, rights) = Binarymap.foldr foldthis ([], []) terms
in
  rel_to_mk rel (list_mk_plus lefts handle HOL_ERR _ => zero_tm,
                 list_mk_plus rights handle HOL_ERR _ => zero_tm)
end

(* assumes multiplications are canonicalised: all leaves are of the form
   c * t, with c a literal
 *)
fun map_update(d, k, c) =
    case Binarymap.peek(d, k) of
      NONE => Binarymap.insert(d,k,c)
    | SOME c' => Binarymap.insert(d,k,c + c')

fun lint_of_t negated acc t =
      let
        val (t1, t2) = dest_plus t
      in
        lint_of_t negated (lint_of_t negated acc t1) t2
      end handle HOL_ERR _ =>
      let
        val (t1, t2) = dest_minus t
      in
        lint_of_t (not negated) (lint_of_t negated acc t1) t2
      end handle HOL_ERR _ =>
      let
        val (c, t) = dest_mult t
      in
        if negated then map_update(acc, t, ~(dest_numeral c))
        else map_update(acc, t, dest_numeral c)
      end

fun term_to_lin t = let
  val (rel, l, r) = dest_rel t
  val d = Binarymap.mkDict Term.compare
in
  LIN (rel, lint_of_t true (lint_of_t false d r) l)
end

fun is_canonical t = let
  val (l, r) = dest_mult t
in
  is_numeral l andalso
  (r = one_tm orelse let val ms = strip_mult r
                     in all (not o is_numeral) ms andalso
                        Listsort.sorted Term.compare ms
                     end)
end handle HOL_ERR _ => false

fun canonicalise_mult_CONV t =
    if is_plus t orelse is_minus t then
      BINOP_CONV canonicalise_mult_CONV t
    else let
        open arithmeticTheory
        fun ACMULT r l =
            EQT_ELIM (AC_CONV (MULT_ASSOC, MULT_COMM) (mk_eq(l,r)))
        val _ = if is_canonical t then raise UNCHANGED else ()
        val multiplicands = strip_mult t
        val (lits, rest0) = partition is_numeral multiplicands
        val rest = Listsort.sort Term.compare rest0
      in
        if null rest then
          (numLib.REDUCE_CONV THENC REWR_CONV (GSYM MULT_RIGHT_1)) t
        else if null lits then
          if Listsort.sorted Term.compare rest0 then
            REWR_CONV (GSYM MULT_LEFT_1) t
          else
            (ACMULT (list_mk_mult rest) THENC REWR_CONV (GSYM MULT_LEFT_1)) t
        else let
            val reassociated = mk_mult(list_mk_mult lits, list_mk_mult rest)
          in
            (ACMULT reassociated THENC LAND_CONV numLib.REDUCE_CONV) t
          end
      end

fun CALL_ARITH thms tm = let
  val asms = map concl thms
  val new_rhs = lin_to_term (term_to_lin tm)
  val _ = assert (not o aconv tm) new_rhs
  val thm = numLib.ARITH_PROVE (list_mk_imp (asms, mk_eq(tm, new_rhs)))
in
  rev_itlist (C MP) thms thm
end

exception NoGood
fun summand_bases (t, acc) =
    (* return a acc UNION set of possible coefficient bases in t,
       raise NoGood if the summand is not canonical  *)
    if is_mult t then let
        val (l, r) = dest_mult t
        val (nonnums, base) = if is_numeral l then (strip_mult r, r)
                              else (strip_mult t, t)
      in
        if all (not o is_numeral) nonnums andalso
           Listsort.sorted Term.compare nonnums
        then HOLset.add(acc, base)
        else raise NoGood
      end
    else if is_minus t then raise NoGood
    else if is_numeral t then
      if t <> zero_tm then HOLset.add(acc, one_tm) else acc
    else HOLset.add(acc, t)

fun term_bases tm = List.foldl summand_bases empty_tmset (strip_plus tm)

fun CANON_FORM_ARITH thms tm = let
  val (_, l, r) = dest_rel tm
  val continue = let
    val lbases = term_bases l
    val rbases = term_bases r
  in
    not (HOLset.isEmpty (HOLset.intersection(lbases, rbases)))
  end handle NoGood => true
in
  if continue then BINOP_CONV canonicalise_mult_CONV THENC CALL_ARITH thms
  else raise ERR "CANON_FORM_ARITH" "Nothing to do with this formula"
end tm

val (CACHED_CANON,cache) = Cache.CACHE(is_rel, CANON_FORM_ARITH)

val CANON_REDUCER = let
  exception CTXT of thm list
  fun get_ctxt e = (raise e) handle CTXT c => c
  fun add_ctxt(ctxt, newthms) = let
    val addthese =
        filter (numSimps.is_arith_asm o concl)
               (flatten (map CONJUNCTS newthms))
  in
    CTXT (addthese @ get_ctxt ctxt)
  end
  open Traverse
in
  REDUCER {addcontext = add_ctxt,
           apply = fn args => CACHED_CANON (get_ctxt (#context args)),
           initial = CTXT [], name = SOME "numrelnorm.CANON_REDUCER"}
end

val CANON_ss = SSFRAG {convs = [], rewrs = [], congs = [],
                       filter = NONE, ac = [], dprocs = [CANON_REDUCER],
                       name = SOME "numrelnorm.CANON_ss" }

end (* struct *)
