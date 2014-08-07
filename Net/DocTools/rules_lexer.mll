(* File lexer.mll *)
{
exception Eof
open Rules_parser

let debug s = () (*print_endline s*)

} 

rule rules = parse
        _* "\n####"                  {debug "START     "; START     (Lexing.lexeme lexbuf)}
      | "\n::"                       {debug "SECTION   "; SECTION   (Lexing.lexeme lexbuf)}
      | "\n:-"                       {debug "SUBSECTION"; SUBSECTION(Lexing.lexeme lexbuf)}
      | "\n%"                        {debug "RULE      "; RULE      (Lexing.lexeme lexbuf)}
      | "\n --in>"                   {debug "ARROWIN   "; ARROWIN   (Lexing.lexeme lexbuf)}
      | "\n --out>"                  {debug "ARROWOUT  "; ARROWOUT  (Lexing.lexeme lexbuf)}
      | "\n --tau>"" "*              {debug "ARROWTAU  "; ARROWTAU  (Lexing.lexeme lexbuf)}
      | "\n ="" "*                   {debug "EQUAL     "; EQUAL     (Lexing.lexeme lexbuf)}
      | [^'\n']*                     {debug "REST      "; REST      (Lexing.lexeme lexbuf)}
      | "\n  "[^'\n']*               {debug "INDENT    "; INDENT    (Lexing.lexeme lexbuf)}
      | "\n"(" "*)                   {debug "BLANK     "; BLANK     (Lexing.lexeme lexbuf)} 
      | "\n##"([^'#']+)eof           {debug "STOP      "; STOP      (Lexing.lexeme lexbuf)}


and newrules = parse
        _* "\n####\n"                {debug "START     "; START     (Lexing.lexeme lexbuf)}
      | "::"                         {debug "SECTION   "; SECTION   (Lexing.lexeme lexbuf)}
      | ":-"                         {debug "SUBSECTION"; SUBSECTION(Lexing.lexeme lexbuf)}
      | "%"                          {debug "RULE      "; RULE      (Lexing.lexeme lexbuf)}
      | "  --in>"                    {debug "ARROWIN   "; ARROWIN   (Lexing.lexeme lexbuf)}
      | "  --out>"                   {debug "ARROWOUT  "; ARROWOUT  (Lexing.lexeme lexbuf)}
      | "  --tau>"" "*               {debug "ARROWTAU  "; ARROWTAU  (Lexing.lexeme lexbuf)}
      | "  ="" "*                    {debug "EQUAL     "; EQUAL     (Lexing.lexeme lexbuf)}
      | [^'\n']*                     {debug "REST      "; REST      (Lexing.lexeme lexbuf)}
      | "\n  "[^'\n']*               {debug "INDENT    "; INDENT    (Lexing.lexeme lexbuf)}
      | "\n"(" "*)                   {debug "BLANK     "; BLANK     (Lexing.lexeme lexbuf)} 
      | "\n##"([^'#']+)eof           {debug "STOP      "; STOP      (Lexing.lexeme lexbuf)}


