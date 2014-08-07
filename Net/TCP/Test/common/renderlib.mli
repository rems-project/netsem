open Nettypes;;
open Parserlib;;

(* FIXME remove this in favour of going via string functions *)
val render_nsparsemsg_to_chan: out_channel -> ns_parse_return -> uint -> string -> string option -> unit;;

(* FIXME used in mkdiag.ml strangely, aim to remove when understand mkdiag code, and replace with timecomment_option_to_string *)
val render_timestamp: uint -> uint -> string

(*
val duration_to_string: duration -> string
*)

val timecomment_option_to_string: timecomment option -> string

val lh_epsilon_to_string: duration -> string

val ns_parse_return_to_string: ns_parse_return -> string
val spec3_parse_return_to_string: spec3_parse_return -> string
