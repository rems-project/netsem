signature numrelnorm =
sig

  include Abbrev
  val CANON_ss : simpLib.ssfrag
  val cache    : Cache.cache
  val CANON_FORM_ARITH : thm list -> term -> thm

end;
