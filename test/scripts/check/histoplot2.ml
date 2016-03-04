open Arg;;

(* options *)

let number_of_bars = ref 20 (* default value *)
let input_fname = ref ""
let output_fname = ref ""



let process_args =
  let args_list = [
(*
    ("-o", String(function f -> output_fname := f),
     "Filename for gnuplot output");
*)
(*
    ("-bars", Int(function i -> number_of_bars := i),
     "Number of bars");
*)
(*
    ("-preamble", String(function f -> page_preamble := f),
     "Filename of latex preamble template");
    ("-postamble", String(function f -> page_postamble := f),
     "Filename of latex postamble template");
    ("-read-labels", String(function f -> read_labels_filename := Some f),
     "Filename of overriding label definition file to read. The actual name is not yet used, but this turns on annotated-mode");
*)
(* filename from -read-labels is not yet used (plan was to include a latex include as specified, but not needed now *)
(* -write-labels is not yet used (plan was to write the mng part of the normal label, but not clear it's needed *)
(*
    ("-write-labels", String(function f -> write_labels_filename := Some f),
     "Filename of overriding label definition file to write");
*)
(*
    ("-width", Int(function i -> page_width := i),
     "Width of page (in \\unitlengths)");
    ("-height", Int(function i -> page_height := i),
     "Height of page (in \\unitlengths)");
    ("-left-margin-offset", Int(function i -> left_margin := i),
     "Distance of left margin from left edge (in unitlengths)");
    ("-right-margin-offset", Int(function i -> right_margin := i),
     "Distance of right margin from left edge (in unitlengths)");
*)
  ] in
  let usage_string = "wlog histogram builder\n" ^
    "histoplot2 [options] input_file > outputfile " in
  parse args_list (function f -> input_fname := f) usage_string;
  if !input_fname = "" then
    (usage args_list usage_string; exit(1));


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

exception Parse_error

let fd = Unix.openfile !input_fname [Unix.O_RDONLY] 0
let ch = Unix.in_channel_of_descr fd

let rec readdata started s0 count0 =
  try
    let s = input_line ch in
    (* try to parse as an int, if not try to parse as a float, if not, fail *)
(*      try
        int_of_string s
      with Failure _ -> raise (Failure ("parse error at line: "^string_of_int line)) in
*)
    (* check increasingness *)
    (* if x < mymax then raise (Failure ("input not in increasing order at line: "^string_of_int line));*)
    if started then (
      if s=s0 then
        readdata started s0 (count0+1)
      else (
        print_string (s0 ^ " " ^ string_of_int count0 ^ "\n");
        readdata started s 1
       )
     ) else
      readdata true s 1
  with
    End_of_file ->
      ()

let _ = readdata false "" 0

(*

let (data_rev,datamin,datamax) = (readdata [] 100000 (0-100000) 0)
let data = List.rev data_rev

let _ = number_of_bars := datamax-datamin + 1

let counts = Array.make !number_of_bars 0


(*
let bar_width = (datamax -. datamin) /. (float_of_int !number_of_bars)
let bar_of_val x = max 0 (min (!number_of_bars -1) (int_of_float ((x -. datamin ) /. bar_width)))

let centre_of_bar i = datamin +. ((0.5 +. float_of_int i) *. bar_width )
let left_of_bar i = centre_of_bar i -. (0.5 *. bar_width)
let right_of_bar i = centre_of_bar i +. (0.5 *. bar_width)

let debug_print_point x =
  print_string "data= " ; print_float x;
  let i = bar_of_val x in
  print_string "  bar= ";print_int i;
  print_string "  ";print_float (left_of_bar i);
  print_string "  ";print_float (centre_of_bar i);
  print_string "  ";print_float (right_of_bar i);
  print_string "\n";
  flush stdout

(* debug print of assignment of data to bars
let _ = List.iter (debug_print_point) data
*)
*)

let bar_of_val x = x-datamin
let centre_of_bar i = (float)(i+datamin)

let _ = List.iter (function x -> let bar=bar_of_val x in counts.(bar)<- 1+ counts.(bar)) data

let _ = for i = 0 to (!number_of_bars -1) do (
  print_float (centre_of_bar i);
  print_string "  ";
  print_int counts.(i);
  print_string "\n") done

let total = List.fold_left (+) 0 data
let number =  List.length data
let mean = (float)total /. (float_of_int number)

let _ =
  prerr_string ("file: "^ !input_fname ^ "  count="^string_of_int number ^ "  mean="^string_of_float mean ^"\n")

*)
