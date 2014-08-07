(* File rebracket.ml *)

(* this converts [[ and ]] to $<[ and ]>$  *)

let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    let _ = Munge_lexer.rebracket lexbuf in ()
  with Munge_lexer.Eof ->
    exit 0

