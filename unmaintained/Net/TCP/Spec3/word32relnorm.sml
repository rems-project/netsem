structure word32relnorm :> word32relnorm =
struct

open HolKernel Parse boolLib word32Theory

(* ----------------------------------------------------------------------
    canoniser
   ---------------------------------------------------------------------- *)

val n2w = Term`word32$n2w`
fun mk_numeral i = mk_comb(n2w, numSyntax.mk_numeral (Arbint.toNat i))
val one_t = mk_numeral Arbint.one

val plus_t = Term`word32$word_add`
val mult_t = Term`word32$word_mul`

fun err f msg = mk_HOL_ERR "word32Syntax" f msg

val dest_mult = dest_binop mult_t (err "dest_mult" "not a multiplication")
val dest_plus = dest_binop plus_t (err "dest_plus" "not an addition")
fun mk_plus(t1,t2) = list_mk_comb(plus_t, [t1,t2])
fun mk_mult(t1,t2) = list_mk_comb(mult_t, [t1,t2])

fun list_mk_plus summands = let
  fun recurse acc t =
      case t of
        [] => acc
      | h::rest => recurse (mk_plus(acc,h)) rest
in
  if null summands then raise err "list_mk_plus" "empty list"
  else recurse (hd summands) (tl summands)
end

fun is_numeral t =
    same_const (rator t) n2w andalso
    numSyntax.is_numeral (rand t) handle HOL_ERR _ => false

fun is_good t = let
  val (l,r) = dest_mult t
in
  is_numeral l
end handle HOL_ERR _ => false

val MULT_LEFT_1 = List.nth(CONJUNCTS (SPEC_ALL word32Theory.WORD_MULT_CLAUSES),
                           2)

fun non_coeff t = if is_good t then rand t
                  else if is_numeral t then one_t
                  else t
fun give_coeff t = if is_good t then ALL_CONV t
                   else REWR_CONV (SYM MULT_LEFT_1) t
val distrib = GSYM word32Theory.WORD_RIGHT_ADD_DISTRIB
fun merge t = let
  val (l,r) = dest_plus t
in
  if is_numeral l andalso is_numeral r then
    word32Lib.WORD_CONV
  else
    BINOP_CONV give_coeff THENC
    REWR_CONV distrib THENC LAND_CONV word32Lib.WORD_CONV
end t

val ADD_RID = List.nth(CONJUNCTS WORD_ADD_CLAUSES, 1)

local
  open GenPolyCanon
in

val wordadd_gci =
    GCI { dest = dest_plus,
          assoc_mode = L,
          assoc = WORD_ADD_ASSOC,
          symassoc = GSYM WORD_ADD_ASSOC,
          comm = WORD_ADD_COMM,
          r_asscomm = derive_r_asscomm WORD_ADD_ASSOC WORD_ADD_COMM,
          l_asscomm = derive_l_asscomm WORD_ADD_ASSOC WORD_ADD_COMM,
          is_literal = is_numeral,
          non_coeff = non_coeff,
          merge = merge,
          postnorm = REWR_CONV (CONJUNCT1 (SPEC_ALL WORD_MULT_CLAUSES)) ORELSEC
                     TRY_CONV (REWR_CONV MULT_LEFT_1),
          left_id = CONJUNCT1 WORD_ADD,
          right_id = ADD_RID,
          reducer = word32Lib.WORD_CONV}
end

val ADDL_CANON_CONV = GenPolyCanon.gencanon wordadd_gci

structure W32Rel_Base =
struct
  open Abbrev
  type t = Arbint.int
  val dest = dest_plus
  val zero = Arbint.zero
  val one = Arbint.one
  val one_t = one_t
  val mk = mk_plus
  val listmk = list_mk_plus
  fun toNat t = Arbint.fromNat (numSyntax.dest_numeral (rand t))
  fun destf t = let
    val (l,r) = dest_mult t
  in
    (toNat l, r)
  end handle HOL_ERR _ => if is_numeral t then (toNat t, one_t)
                          else (Arbint.one, t)
  fun mkf (i,t) = let
    val i_t = mk_numeral i
  in
    if t = one_t then i_t else mk_mult(i_t, t)
  end
  val canon = ADDL_CANON_CONV
  val addid = REWR_CONV (GSYM ADD_RID)
  val op+ = Arbint.+
  val op- = Arbint.-
  val op~ = Arbint.~
  val op< = Arbint.<

  val destrel = dest_eq
  val opr = Term`min$= : word32 -> word32 -> bool`
  val rwt = WORD_EQ_ADD_LCANCEL
end

structure W32EQNorm = GenRelNorm(W32Rel_Base)
fun word32_eqnorm t = let
  (* canonises first *)
  val (l,r) = dest_eq t
in
  BINOP_CONV ADDL_CANON_CONV THENC
  W32EQNorm.gen_relnorm
end t

end;
