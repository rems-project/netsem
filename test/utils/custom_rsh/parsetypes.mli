type program =
    EXEC_LIBD
  | EXEC_HOLTCPCB
  | EXEC_SLURP
  | EXEC_INJECTOR;;

type parse_ret = program * (string * string) list * string list;;
