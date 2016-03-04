{
  open Parser        (* The type token is defined in parser.mli *)
  exception Eof

  let debug s = ();;
}

rule token = parse
  [' ' '\t']     { token lexbuf }     (* skip blanks *)
| ['\n' ]        { debug "EOL"; EOL }
| "["            { debug "LSQBRKT"; LSQBRKT }
| "]"            { debug "RSQBRKT"; RSQBRKT }
| "="            { debug "EQUALS"; EQUALS }
| ";"            { debug "SC"; SC }
| "EXEC_LIBD"      { debug "LIBD"; LIBD }
| "EXEC_HOLTCPCB"  { debug "HOLTCPCB"; HOLTCPCB }
| "EXEC_SLURP"     { prerr_endline "SLURP"; debug "SLURP"; SLURP }
| "EXEC_INJECTOR"  { debug "INJECTOR"; INJECTOR }
| ['a'-'z' 'A'-'Z' '0'-'9' ':' '\\' '/' '.' '-' '(' ')' '_' '{' '}' '\"']+ { debug ("STRING: " ^(Lexing.lexeme lexbuf)); STRING(Lexing.lexeme lexbuf) }
| eof            { raise Eof }
