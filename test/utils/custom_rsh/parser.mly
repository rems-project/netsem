%{
open Parsetypes;;
%}

%token EOL
%token LSQBRKT RSQBRKT EQUALS SC
%token LIBD HOLTCPCB SLURP INJECTOR
%token <string> STRING

%token EOL

%start main             /* the entry point */
%type <Parsetypes.parse_ret> main
%%

main:
  program environment args EOL  { ($1,$2,$3) }
;;

program:
  LIBD { EXEC_LIBD }
| HOLTCPCB { EXEC_HOLTCPCB }
| SLURP { EXEC_SLURP }
| INJECTOR { EXEC_INJECTOR }
;;

environment:
  LSQBRKT RSQBRKT { [] }
| LSQBRKT env_inner RSQBRKT { $2 }
;;

env_inner:
  STRING EQUALS STRING SC { [($1, $3)] }
| STRING EQUALS STRING SC env_inner { ($1, $3)::$5 }
;;

args:
  LSQBRKT RSQBRKT { [] }
| LSQBRKT args_inner RSQBRKT { $2 }
;;

args_inner:
  string SC { [$1] }
| string SC args_inner { $1::$3 }

string:
  STRING { $1 }
| STRING string { $1^" "^$2 }
;;
