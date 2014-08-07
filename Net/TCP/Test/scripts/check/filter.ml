open Arg



(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

let domain_fname = ref ""
let invert = ref false

let process_args =
  let args_list = [
    ("-domain", String(function f -> domain_fname := f),
     "Filename for domain");
    ("-invert", Unit(function _ -> invert := true),
     "Select lines not in domain");
  ] in
  let usage_string = "Filter stdin, taking all lines with a characters 8-11 field that exists in domain_fname\n" ^
    "filter -domain domain_file" in
  parse args_list (function f -> ()) usage_string;
  if !domain_fname = "" then
    (usage args_list usage_string; exit(1))


let ch = open_in !domain_fname

let tbl = Hashtbl.create 2000

let _ = try
  while true do
    let s = input_line ch in
    let firstspace = try  String.index s ' ' with Not_found -> String.length s in
    let s1 = String.sub s 0 firstspace  in
(*    let s2 = String.sub s (1+firstspace) (String.length s - firstspace -1) in *)
    Hashtbl.add tbl s1 ()
  done
with
  End_of_file -> ()

let _ = try
  while true do
    let s = input_line stdin in
    let s1 = String.sub s 7 4 in
(*
    let firstspace = try (String.index s ' ') with Not_found -> String.length s  in
    let s1 = String.sub s 0 firstspace  in
*)
(*    let s2 = String.sub s (1+firstspace) (String.length s - firstspace -1) in  *)
    let found = try
      Hashtbl.find tbl s1; true
    with
      Not_found -> false in
    if (found && not(!invert)) || ((not found) && !invert) then
      output_string stdout (s ^"\n");
  done
with
  End_of_file -> ()

