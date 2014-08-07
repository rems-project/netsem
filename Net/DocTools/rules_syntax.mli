type r =
    Out of string
  | In of string
  | Tau
  | Equal

type t =
    Section of string * string      (* name,comment *)
  | Subsection of string * string   (* name,comment *)
  | Rule of string * string * string * r *       string * string * string
         (* name,    annot,   lhs,     relation, rhs,     cond,    comment *)

