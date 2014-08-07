open Unix;;
open Nettypes;;
open Parserlib;;

type merge_input =
    MESSAGE of ns_parse_return
  | FINISH;;

(* Write merger file header to the specified channel *)
val writeMergeHeader: out_channel -> unit;;

(* Write our merger header's footer to the specified channel *)
val writeMergeHeaderFooter: out_channel -> unit;;

(* Write a custom string to the file header *)
val writeCustomHeader: out_channel -> string -> unit;;

val string_of_time: time -> string;;

(* generateEpsilonTransition (time in us) (time in us) *)
(* Generate an epsilon transition from the specified times *)
val generateEpsilonTransition: time -> time -> string;;

(* Given a list of parsed messages pick the minimum *)
(* with respect to the timestamp ordering *)
val findMinimum: (ns_parse_return * time * string option) list -> (ns_parse_return * time * string option) ;;


