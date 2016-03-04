 /* File parser.mly */
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
%right INDENT
%left BLANK
%start main             /* the entry point */
%type <Syntax.t list> main
%%

main:
    START blanks body STOP             { $3  }
;

body:
        /*empty*/                      { [] }
   |    element body                   { $1 :: $2 }
;
element:
    SECTION REST comment               { Syntax.Section( $2, $3)  }
  | SUBSECTION REST comment            { Syntax.Subsection( $2 , $3  )}
  | RULE REST blanks indents relation indents condition comment { Syntax.Rule ($2,"",$4,$5,$6,$7,$8) }
;

condition:
    blanks                             { "" }
  | indents blanks                     { $1  }
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
     ARROWIN REST                      { Syntax.In( $2 )}
  |  ARROWOUT REST                     { Syntax.Out( $2 )}
  |  ARROWTAU                          { Syntax.Tau }
  |  EQUAL                             { Syntax.Equal  }
;

blanks:
     /*empty*/                         { "" }
  |  BLANK blanks                      { $1 ^ $2 }
;

indents:
     INDENT                            { $1  }
   | INDENT  indents                   { $1 ^ $2  }




