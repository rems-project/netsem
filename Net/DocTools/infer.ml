(* File infer.ml *)

type myInOut = Inside of char | Outside

type point = Normal of char | Rule of int*int*int*int*int | RuleBody

let min_rule_width = 5

(*regard rb (a string list) as a 2-dimensional array of chars
  (0,0)  (1,0)  (2,0)   size_x = 3   size_y = 2   space-filled, no \n
  (0,1)  (1,1)  (2,1)
*)

let typeset_rules (insert_munge_code, rb) =
  let size_x = List.fold_left max 0 (List.map String.length rb) in
  let size_y = List.length rb in

  let d(x,y) =  if (x<0 || x>= size_x || y<0 || y>=size_y) then
    Outside
  else
    try
      Inside (String.get(List.nth rb y) x)
    with
      Invalid_argument(s) -> Inside(' ') in

  let is_blank(x,y) = match d(x,y) with
    Outside -> true
  | Inside(c) -> c=' '   in

  let is_minus(x,y) = match d(x,y) with
    Outside -> false
  | Inside(c) -> c='-' in

  let rec is_blank_hor(x1,x2,y)  = if x1>=x2 then
    true
  else
    is_blank(x1,y) && is_blank_hor(x1+1,x2,y) in

  let rec next_non_minus(x,y) = if not(is_minus(x,y)) then
    x
  else
    next_non_minus(x+1,y) in

(* return the list of start and end coordinates of --- segments in line y,
   starting from column x *)
  let rec line_starts_hor (x,y) =
    if x>= size_x then
      []
    else if is_minus(x,y) then
      let x2 = next_non_minus(x,y)  in
      if (x2-x) >= min_rule_width then
        (x,x2,y) :: line_starts_hor(x2+1,y)
      else
        line_starts_hor(x2+1,y)
    else
      line_starts_hor(x+1,y)   in


  (* find the top and bottom of a rule, ie the y coordinates of the first line
     and 1+ that of the last line *)
  let rec rule_top (x1,x2,y) = if is_blank_hor(x1,x2,y-1) then y else rule_top(x1,x2,y-1)  in
  let rec rule_bot (x1,x2,y) = if is_blank_hor(x1,x2,y+1) then y+1 else rule_bot(x1,x2,y+1) in


  let rule_top_bot (x1,x2,y) = (x1,x2,rule_top(x1,x2,y),y,rule_bot(x1,x2,y)) in

  let rec rules2 y rs = if y>= size_y then
    rs
  else
    (List.map rule_top_bot (line_starts_hor(0,y))) @ (rules2 (y+1) rs) in

  let rules = rules2 0 [] in

  let rec point2 (x,y) rs = match rs with
    [] -> (match d(x,y) with Outside -> Normal(' ') | Inside(c) -> Normal(c))
  | (x1,x2,y_top,y2,y_bot)::rs  ->
      if x=x1 && y=y2 then
        Rule(x1,x2,y_top,y2,y_bot)
      else if x>=x1 && x<x2 && y>=y_top && y< y_bot then
        RuleBody
      else
        point2 (x,y) rs    in

  let point (x,y) = point2 (x,y) rules in

  let rec get_string(x1,x2,y) = if x1>=x2 then "" else match  d(x1,y) with Outside -> " "^get_string(x1+1,x2,y) | Inside(c) -> (String.make 1 c)^get_string(x1+1,x2,y) in
  let get_string_mng(x1,x2,y) = let s = get_string(x1,x2,y) in if insert_munge_code then "<["^s^"]>" else s in

  let rec typeset_clauses(x1,x2,y_top,y_bot) =
    if y_top=y_bot then
      ()
    else
      ((print_string (get_string_mng(x1,x2,y_top))) ;
       if y_top=y_bot-1 then
         ()
       else (
         print_string "\\\\ " ;
           typeset_clauses(x1,x2,y_top+1,y_bot) )) in

  let typeset_rule(x1,x2,y_top,y,y_bot) =
    print_string "\\autoinfer{\\begin{array}{l}" ;
    typeset_clauses(x1,x2,y_top,y) ;
    print_string "\\end{array}}{\\begin{array}{l}" ;
    typeset_clauses(x1,x2,y+1,y_bot);
    print_string "\\end{array}}" in

  print_newline ();
  for y = 0 to size_y do
    for x =0 to size_x do
      match point(x,y) with
        Normal(c) -> print_char(c)
      | Rule(x1,x2,y_top,y,y_bot) -> typeset_rule(x1,x2,y_top,y,y_bot)
      | RuleBody -> print_char(' ')
    done;
    print_newline ()
  done




let is_start_line(l) = l="<RULES" || l="<RULES["
let is_end_line(l) = l="RULES>" || l="]RULES>"
let is_munge_start_line(l) = l="<RULES["

let report_error(s) = print_endline("INFER ERROR: "^s);prerr_endline("INFER ERROR: "^s)

(* returns a list of strings, top one first *)
let rec read_rules_block rb =
  try
    let current_line = read_line () in
    if is_start_line(current_line) then (
      report_error("unexpected start line");
      read_rules_block rb )
    else if is_end_line(current_line) then
      List.rev rb
    else read_rules_block(current_line::rb)
  with
    End_of_file -> (
      report_error("unexpected end of file in rules block");
      List.rev rb )



let _ =
try
  while true do
    let current_line = read_line() in
    if is_start_line(current_line) then
      typeset_rules(is_munge_start_line(current_line), read_rules_block [])
    else
      print_endline(current_line)
  done
with
  End_of_file -> ()


