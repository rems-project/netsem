(* ---------------------------------------------------------------------- *)
(* Netsem Project: simple latex diagram library                           *)
(* Steve Bishop - Created 20031016                                        *)
(* $Id: latexdiag.mli,v 1.5 2004/12/18 14:41:22 pes20 Exp $ *)
(* ---------------------------------------------------------------------- *)

type alignment =
    LEFT
  | RIGHT
  | CENTRE
  | ALL

type color =
    BLACK
  | LIGHTGRAY
  | DARKGRAY

type diaglib_object =
    (* LABEL of x * y * max box length * angle * alignment * string *)
    LABEL of int * int * int * int * alignment * string
    (* LINE of x1 * y1 * x2 * y2 * colour *)
  | LINE of  int * int * int * int * color
    (* ARROW of x1 * y1 * x2 * y2 * label * label position *)
  | ARROW of int * int * int * int * string * alignment
    (* DISC of x * y * diameter *)
  | DISC of int * int * int

type diaglib_hnd


(* -=-=-=-=-=-=-=-=-=-=-=-=--=-=--=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


(* diaglib_init: latex_preamble_filename -> latex_postamble_filename ->
     page_width -> page_height -> document_title -> handle *)
val diaglib_init: string -> string -> int -> int -> string -> diaglib_hnd

(* diaglib_add: handle -> object to add -> unit *)
val diaglib_add: diaglib_hnd -> diaglib_object -> unit

(* diablib_emit: handle -> latex_output_filename -> unitlength -> scale -> unit *)
val diaglib_emit: diaglib_hnd -> string -> float option -> float option -> unit

(* Delimit string appropriately for LaTeX *)
val convert_string: string -> string
