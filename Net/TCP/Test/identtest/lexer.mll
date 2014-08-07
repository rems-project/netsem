{
open Parser
exception Eof
}

rule token = parse
  [' ' '\t' '\n']  { token lexbuf }    (* skip blanks *)
| "*-"         { SEP }
| "*Comment="  { COMMENT }
| "*Length="   { LENGTH }
| "*Data="     { DATA }
| ['A'-'Z' 'a'-'z' '0'-'9' '_']*
      { STRING(Lexing.lexeme lexbuf) }
