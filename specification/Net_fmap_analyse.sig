signature Net_fmap_analyse =
sig

  include Abbrev
  val fm_onestep : term list -> (thm list -> conv) -> conv
  val outermost_varkey_elim : term HOLset.set -> conv -> conv

  val single_simple : conv

  val last_call : term ref

end;

(*

   [fn_onestep ctxt kc vc t] tries to eliminate equalities over finite
   maps in term t.  The conv parameters kc and vc are used to reduce
   equalities between keys and values in the finite maps respectively.
   The ctxt argument is a list of terms representing the current
   assumptions.  It's assumed that these will have been fed into the
   provided conversions appropriately, so that they will make use of the
   assumptions.

*)