signature ground_tickers =
sig

  include Abbrev
  val time_analyse_hyps : term list -> {redex : term, residue : term} list *
                                       thm list

end

(*
   [time_analyse_hyps tlist] returns an instantiation for the hypotheses'
   tick variables, as well as a list of theorems demonstrating that the
   Time_Pass_ticker hypotheses all hold under this instantiation.

*)