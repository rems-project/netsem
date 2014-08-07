(* File munge.ml *) 

(* This does sundry syntax munging to all parts of
stdin between <[ ... ]> (and doesn't echo the delimiters) *)

let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    let _ = Munge_lexer.munge lexbuf in ()
  with Munge_lexer.Eof ->
    exit 0

