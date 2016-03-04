 /* File parser.mly */

%{
let deindent s = 
  String.sub s 3 ((String.length s) -3)

(* beautiful robust code... *)

let rulename s = 
  let _ = (Str.string_match 
      (Str.regexp " *\([A-Za-z][A-Za-z0-9.]*\) *\(.*\)")
      s
      0 ) in
  Str.matched_group 1 s

let ruleannot s =
  let _ = (Str.string_match 
      (Str.regexp " *\([A-Za-z][A-Za-z0-9.]*\) *\(.*\)")
      s
      0 ) in
  Str.matched_group 2 s

let strip s = 
  let _ = (Str.string_match 
      (Str.regexp " *\([^\n]*\)" )
      s
      0 ) in
  Str.matched_group 1 s
    

%}

%token <string> START
%token <string> SECTION
%token <string> SUBSECTION
%token <string> RULE
%token <string> ARROWIN
%token <string> ARROWOUT
%token <string> ARROWTAU
%token <string> EQUAL
%token <string> INDENT
%token <string> BLANK
%token <string> REST
%token <string> STOP
%start main             /* the entry point */
%type <Rules_syntax.t list> main
%%

main:
    START blanks body STOP             { $3  }
;

body:
        /*empty*/                      { [] }
   |    element body                   { $1 :: $2 }
;
element:
    SECTION REST comment               { Rules_syntax.Section( strip $2, $3)  }
  | SUBSECTION REST comment            { Rules_syntax.Subsection( strip $2 , $3  )}
  | RULE REST blanks indents relation indents condition comment { Rules_syntax.Rule (rulename $2,ruleannot $2,$4,$5,$6,$7,$8) }
;

condition:
    blanks                             { "" }
  | blanks indents blanks              { $2  }
;

comment:
    blanks                             { "" }
  | blanks commentbody blanks          {  $2  }
;
commentbody:
    indents                            { $1 }
  | commentbody blanks indents         { $1 ^ $2 ^ $3}
;    

relation: 
     ARROWIN REST                      { Rules_syntax.In( $2 )}
  |  ARROWOUT REST                     { Rules_syntax.Out( $2 )}
  |  ARROWTAU                          { Rules_syntax.Tau }
  |  EQUAL                             { Rules_syntax.Equal  }
;

blanks:
     /*empty*/                         { "" }
  |  BLANK blanks                      { "\n" ^ $2 }
;

indents:
     INDENT                            { deindent $1  }
   | INDENT  indents                   { (deindent $1) ^ "\n" ^ $2  }




