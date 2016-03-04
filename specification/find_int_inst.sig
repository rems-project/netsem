signature find_int_inst =
sig

  include Abbrev
  val find_int_inst : term list -> {residue : term, redex : term} list

end
