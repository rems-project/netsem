signature LetComputeLib =
sig

  include Abbrev
  val CLET_t : term
  val value_t : term
  val pending_t : term

  val dest_clet : term -> term * term
  val is_clet : term -> bool

  val dest_pending : term -> term
  val is_pending : term -> bool

  val CLET_CONV : conv
  val pending_CONV : conv
  val CLET_ss : simpLib.ssfrag
  val CLET_UNWIND : conv

  val draw_out_fmaps : conv
  val structure_reduction_CONV : term HOLset.set -> conv
  val pending_structure_reduction_CONV : term HOLset.set -> conv
  val record_update_fns : string -> term list

  val cse_elim1_CONV : conv
  val cse_elim_CONV : conv

  val grounded_let_CONV : conv

end;
