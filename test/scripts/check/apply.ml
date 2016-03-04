open Arg



(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)
let rule_ids_fname = ref ""
let rule_usage_fname = ref ""

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

  let map_fname = ref ""

let default_value = ref (None:string option)

let process_args =
  let args_list = [
    ("-map", String(function f -> map_fname := f),
     "Filename for map");
    ("-default", String(function f -> default_value := Some f),
     "default result value");
  ] in
  let usage_string = "Apply finite string map to stdin\n" ^
    "coverage -map map_file" in
  parse args_list (function f -> ()) usage_string;
  if !map_fname = "" then
    (usage args_list usage_string; exit(1))


let ch = open_in !map_fname

let tbl = Hashtbl.create 2000

let _ = try
  while true do
    let s = input_line ch in
    let firstspace = String.index s ' ' in
    let s1 = String.sub s 0 firstspace  in
    let s2 = String.sub s (1+firstspace) (String.length s - firstspace -1) in
    Hashtbl.add tbl s1 s2
  done
with
  End_of_file -> ()




let _ = try
  while true do
    let s1 = input_line stdin in
(*    prerr_string (s1 ^"foo\n"); *)
    let s2 = try
      Hashtbl.find tbl s1
    with
      Not_found -> (match !default_value with
        None -> raise (Failure ("Key string not found in map:"^s1))
      | Some s -> s)
    in
    output_string stdout (s1 ^" "^ s2^"\n")
  done
with
  End_of_file -> ()

