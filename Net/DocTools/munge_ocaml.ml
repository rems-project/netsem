(* File munge_ocaml.ml *) 

(* This does sundry ocaml source syntax munging to all parts of
stdin after open Udplange;; *)

let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    let _ = Munge_lexer.munge_ocaml lexbuf in ()
  with Munge_lexer.Eof ->
    exit 0
