signature Phase = sig

    exception PhaseRange

    (* for use in Script files *)
    val add_to_phase : int -> string -> unit
    val phase : int -> ('a -> HolKernel.thm) -> 'a -> HolKernel.thm
    val phase_x : int -> (string -> 'b -> HolKernel.thm) ->
                  string -> 'b -> HolKernel.thm
    (* for use in Theory or other files *)
    val add_to_phase_imm : int -> HolKernel.thm -> unit
    val phase_imm : int -> HolKernel.thm -> HolKernel.thm
    (* read back the phase list *)
    val get_phase_list : int -> HolKernel.thm list

end
