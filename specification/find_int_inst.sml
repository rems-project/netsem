structure find_int_inst :> find_int_inst =
struct

open HolKernel boolLib

fun dest_plus t = numSyntax.dest_plus t
    handle HOL_ERR _ => intSyntax.dest_plus t
    handle HOL_ERR _ => realSyntax.dest_plus t
fun dest_mult t = numSyntax.dest_mult t
    handle HOL_ERR _ => intSyntax.dest_mult t
    handle HOL_ERR _ => realSyntax.dest_mult t
fun dest_leq t = numSyntax.dest_leq t
    handle HOL_ERR _ => let
             val (l,r) = numSyntax.dest_less t
           in
             (numSyntax.mk_plus(l, numSyntax.mk_numeral Arbnum.one), r)
           end
    handle HOL_ERR _ => intSyntax.dest_leq t
    handle HOL_ERR _ => realSyntax.dest_leq t
    handle HOL_ERR _ => let
             val (l,r) = realSyntax.dest_less t
           in
             (realSyntax.mk_plus(l, realSyntax.one_tm), r)
           end

fun dest_lit t = Arbint.fromNat (numSyntax.dest_numeral t)
    handle HOL_ERR _ => intSyntax.int_of_term t
    handle HOL_ERR _ => realSyntax.int_of_term t


exception GetOut

fun find_int_inst remaining_hyps = let
  val remaining_vars = FVL remaining_hyps empty_tmset
  val (integral, others) =
      HOLset.foldl
        (fn (e,(int,oth)) =>
            if mem (type_of e) [numSyntax.num, intSyntax.int_ty,
                                realSyntax.real_ty] then
              (e::int,oth)
            else (int,e::oth))
        ([],[])
        remaining_vars

  val _ = not (null integral) orelse raise GetOut

  fun mk_coeff vi c =
      List.tabulate(length integral + 1,
                    (fn n => if n = vi then c else Arbint.zero))
  fun mk_litcoeff n =
      List.rev (n :: List.tabulate(length integral, K Arbint.zero))


  fun dest_coeff t =
      if is_var t then
        mk_coeff (index (equal t) integral) Arbint.one
      else let
          val (l,r) = dest_mult t
        in
          if is_var l then
            mk_coeff (index (equal l) integral) (dest_lit r)
          else
            mk_coeff (index (equal r) integral) (dest_lit l)
        end

  val add_coeffs = ListPair.map Arbint.+
  val neg_coeffs = map Arbint.~

  fun coeff_list t = let
    val (l,r) = dest_plus t
  in
    add_coeffs (coeff_list l, coeff_list r)
  end handle HOL_ERR _ => dest_coeff t
      handle HOL_ERR _ => mk_litcoeff (dest_lit t)

  fun int_constraint t = let
    val (l,r) = dest_leq t
  in
    [add_coeffs(neg_coeffs (coeff_list l), coeff_list r)]
  end handle HOL_ERR _ => let
               val (l,r) = dest_eq t
               val c = add_coeffs(neg_coeffs (coeff_list l), coeff_list r)
             in
               [c, neg_coeffs c]
             end


  val constraints =
      List.concat (List.mapPartial (Lib.total int_constraint) remaining_hyps)
      @
      List.mapPartial (fn v => if type_of v = numSyntax.num then
                                 SOME (dest_coeff v)
                               else NONE) integral

  val db = OmegaMLShadow.dbempty (length integral + 1)

  fun add_csts normalc csts db exc = let
    open OmegaMLShadow
  in
    case csts of
      [] => normalc db
    | c::cs => add_check_factoid db
                                 (gcd_check_dfactoid (fromArbList c, ASM ()))
                                 (add_csts normalc cs)
                                 exc
  end

  fun handle_result r = let
    open OmegaMLShadow
  in
    case r of
      SATISFIABLE v =>
      List.tabulate (length integral, (fn i => PIntMap.find i v))
    | x => raise Fail "Not satisfiable"
  end

  val values =
      add_csts (fn db => OmegaMLShadow.work db handle_result)
               constraints
               db
               handle_result

  fun mapthis (var, value) =
      if type_of var = numSyntax.num then
        var |-> numSyntax.mk_numeral (Arbint.toNat value)
      else if type_of var = intSyntax.int_ty then
        var |-> intSyntax.term_of_int value
      else
        var |-> realSyntax.term_of_int value

in

  ListPair.map mapthis (integral, values)

end handle GetOut => []




end;
