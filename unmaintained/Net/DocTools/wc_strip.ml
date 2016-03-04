(* File wc_strip.ml *)

(* this hackily removes \[..\],  [[...]], \... and whichversion.1..whichversion.2 *)

let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    let _ = Munge_lexer.wc lexbuf in ()
  with Munge_lexer.Eof ->
    exit 0

