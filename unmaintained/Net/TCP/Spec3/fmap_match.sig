signature fmap_match =
sig

  include Abbrev
  datatype posn = Left | Right
  type inst = {redex:term, residue:term} list
  type preconv = (posn list * thm option) list
  type task = term * term * posn list
  val match : int ->                (* no. of steps to perform: ~1 for as many
                                       as necessary *)
              (term -> thm) ->      (* simplifier for keys *)
              int ->                (* no. of iterations permitted *)
              (inst * preconv) ->   (* accumulator *)
              task list ->          (* deferred finite map matches *)
              task list ->          (* matches to perform *)
              ((inst * preconv) * task list * task list)
                                    (* accumulated, deferred,
                                       remaining matches *)

  val count_updates : term -> int

  val preconv2conv : preconv -> conv
  val apply_mresult : (inst * preconv) -> thm -> thm
  val fm_match : (term -> thm) -> term -> term ->
		 ((inst * preconv) * task list)

end;


