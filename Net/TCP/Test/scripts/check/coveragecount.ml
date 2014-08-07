open Arg


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)
let rule_ids_fname = ref ""
let rule_usage_fname = ref ""

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)


let process_args =
  let args_list = [
    ("-rules", String(function f -> rule_ids_fname := f),
     "Filename for rule ids");
    ("-usage", String(function f -> rule_usage_fname := f),
     "Filename for rule ids");
  ] in
  let usage_string = "Rule coverage analysis\n" ^
    "coverage -rules rule_ids_file -usage rule_usage_file" in
  parse args_list (function f -> ()) usage_string;
  if !rule_ids_fname = "" || !rule_usage_fname = "" then
    (usage args_list usage_string; exit(1))


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

let rule_ids_ch = open_in !rule_ids_fname
let rule_usage_ch = open_in !rule_usage_fname

let rec read_strings ch =
  try
    let s = input_line ch in s:: read_strings ch
  with
    End_of_file -> []


let rule_ids = Array.of_list (read_strings rule_ids_ch)
let n = Array.length rule_ids

let max_rule_id_length = Array.fold_left (function a -> function b -> max a (String.length b)) 0 rule_ids

let pad n s = s ^ (String.make (n - String.length s) ' ')

(* high performance... *)
let i_of_string s =
  let rec f i = if i>=n then raise (Failure ("usage not found: "^s)) else (if s=rule_ids.(i) then i else f (i+1)) in
  f 0



(* process usages *)
let count = Array.make n 0
let _ =
  try
    while true do
      let s = input_line rule_usage_ch  in
      let i = i_of_string s in
      count.(i) <- 1 + count.(i)
    done
  with
    End_of_file -> ()


let _ =
  for i = 0 to n-1 do
    print_string (pad max_rule_id_length  rule_ids.(i)) ;
    print_string "  ";
    print_int count.(i);
    print_string "\n"
  done

let _ =  close_in_noerr rule_ids_ch
let _ =  close_in_noerr rule_usage_ch


