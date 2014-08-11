(* A HOL98 specification of TCP *)

(* Expansion phase maintenance *)

structure Phase :> Phase =
struct

open HolKernel boolLib

exception PhaseRange

val max_phase = 3;

val phase_lists = Array.array (max_phase + 1, [])

fun adjoin_to_theory s =
    HolKernel.adjoin_to_theory
        { sig_ps = NONE,
          struct_ps =
          SOME (fn pps =>
                   (PP.add_string pps s;
                    PP.add_newline pps))}

fun add_to_phase n defname =
    if n < 0 orelse n > max_phase then
        raise PhaseRange
    else
        adjoin_to_theory ("val _ = Phase.add_to_phase_imm " ^ Int.toString n
                          ^ " " ^ defname ^ ";");

fun guess_defname thm = let  (* won't work for xDefine *)
  val cs = thm |> concl |> strip_forall |> #2 |> strip_conj
  fun head_of_clause t = let
    val (_, body) = strip_forall t
    val (l, _) = dest_eq body
    val (f, _) = strip_comb l
  in
    #Name (dest_thy_const f)
  end
in
    head_of_clause (List.hd cs) ^ !Defn.def_suffix
end

fun phase n f v =
    let val thm = f v in
        add_to_phase n (guess_defname thm);
        thm
    end

fun phase_x n f name v =
    let val thm = f name v in
	add_to_phase n (name ^ !Defn.def_suffix);
	thm
    end

fun add_to_phase_imm n def =
    if n < 0 orelse n > max_phase then
        raise PhaseRange
    else
        Array.update (phase_lists, n, def :: Array.sub (phase_lists,n))

fun phase_imm n thm =
    (add_to_phase_imm n thm;
     thm)

fun get_phase_list n =
    if n < 0 orelse n > max_phase then
        raise PhaseRange
    else
        List.rev (Array.sub (phase_lists,n))

end (* struct *)
