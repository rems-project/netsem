(* A HOL98 specification of TCP *)

(* Standalone syntax checker for trace files *)

open TraceFiles Parse

val args = CommandLine.arguments()

fun err s = TextIO.output(TextIO.stdErr, s)

val _ =
    case args of
      [] => (err ("Usage: "^CommandLine.name()^" file [files]\n");
             Process.exit Process.failure)
    | _ => ()

val lhost0_ty = Type.mk_type("Lhost0", [])
val host_ty = Type.mk_type("host", [])
fun right_type tclass ty t =
    case Type.compare(ty, Term.type_of t) of
      EQUAL => true
    | _ => (err (tclass ^ " " ^ term_to_string t ^ " does not have type " ^
                 Parse.type_to_string ty ^ "\n"); false)

fun ground tclass t okvars =
    if null (Lib.set_diff (Term.free_vars t) okvars) then true
    else (err(tclass ^ " " ^ term_to_string t ^
              " includes unacceptable free variables\n");
          false)

fun check_label t = ground "Label" t [] andalso right_type "Label" lhost0_ty t

val host_vars = [``initial_ticker_count : tstamp seq32``,
                 ``initial_ticker_remdr : real``]
fun check_host t = ground "Host" t host_vars andalso
                   right_type "Host" host_ty t

fun my_all f list = let
  fun recurse acc [] = acc
    | recurse acc (h::t) = recurse (f h andalso acc) t
in
  recurse true list
end

fun check_file fname = let
  val _ = err("Loading "^fname^"... ")
  val (h, labels) = host_and_labels_from_file fname
in
  if check_host h andalso my_all check_label labels then (err("OK\n"); true)
  else false
end handle _ => (err ("Exception raised attempting "^fname^"\n"); false)

val _ = Globals.interactive := true
val _ = Globals.guessing_overloads := false
val _ = Globals.guessing_tyvars := false

val _ = Process.exit (if my_all check_file args then Process.success
                      else Process.failure)
