(* File rules_to_latex.ml *)

exception Error

open Rules_syntax

let latex_rel = function
    Out(l) -> "\\out{<["^l^"]>}"
  | In(l) -> "\\inp{<["^l^"]>}"
  | Tau -> "\\ttau"
  | Equal -> "=" 
        

(* watch out - this code is copied in rules_to_latex.ml and munge_lexer.mll.  yuk *)
let letterify_char c = 
  if ((c>='a' && c<='z') || (c>='A' && c <='Z')) 
  then c 
  else if c='.' then 'X'
  else if (c>= '1' && c<='9') then char_of_int ((int_of_char c)+16)
  else if (c='0') then 'Z'
  else c
      
let name_to_latex_command s = 
  let ss = String.copy s in 
  for i =0 to (String.length s)-1 do
    String.set ss i (letterify_char (String.get ss i))
  done ;
  ss^"X"

        
        
(* convert rule file element to a pair of strings, the first to go in the file of latex rule macro definitions and the 
second to go in the tmp-rules file *)

let latex_element = function 
    Section(name,comment) -> ("",  "\\rsection{"^name^"}{"^comment^"}\n" )
  | Subsection(name,comment) ->  ("",  "\\rsubsection{"^name^"}{"^comment^"}\n")
  | Rule(name,annot,lhs,rel,rhs,cond,c) -> 
      let latex_command = name_to_latex_command name in
      (("\\newcommand{\\" ^ latex_command ^"}{")
       ^
         (if cond<>"--" then  (
           if  c<>"" then 
             "\\rrulecc{"^name^"}{"^annot^"}{<["^lhs^"]>}{"^(latex_rel rel)^"}{<["^rhs^"]>}{<["^cond^"]>}{"^c^"}" 
           else                                                                                                 
             "\\rrulecn{"^name^"}{"^annot^"}{<["^lhs^"]>}{"^(latex_rel rel)^"}{<["^rhs^"]>}{<["^cond^"]>}{"^c^"}" ) 
         else  (if c<>"" then                                                                                 
           "\\rrulenc{"^name^"}{"^annot^"}{<["^lhs^"]>}{"^(latex_rel rel)^"}{<["^rhs^"]>}{<["^cond^"]>}{"^c^"}" 
         else                                                                                                 
           "\\rrulenn{"^name^"}{"^annot^"}{<["^lhs^"]>}{"^(latex_rel rel)^"}{<["^rhs^"]>}{<["^cond^"]>}{"^c^"}" ))
       ^
         "}\n\n"
           ,
       ("\\showrule{"^name^"}\n"))



let arg_ruledefs = (ref "tmp-rawruledefs.tex") 
    
let _ = (Arg.parse 
           [("-ruledefs",Arg.String(fun s-> arg_ruledefs:=s),"filename for latex rule definitions")]
           (fun s -> ())
           "use with options:") 

let file_ruledefs = open_out (!arg_ruledefs) 


let process_element  u e = 
  (u;
   let (s1,s2) = latex_element e in
   (output_string file_ruledefs s1 ; 
    print_string s2 ))
      
let _ =
  let lexbuf = Lexing.from_channel stdin in
  let errorreport () = 
    print_endline "The last lexeme read was:";
    print_endline  ("`"^(Lexing.lexeme lexbuf) ^ 
                    "' from " ^
                    (string_of_int (Lexing.lexeme_start lexbuf))^
                    " to "^
                    (string_of_int (Lexing.lexeme_end lexbuf))) in
  try
    List.fold_left process_element () (Rules_parser.main Rules_lexer.rules lexbuf) ;
    close_out file_ruledefs
  with 
      Rules_lexer.Eof ->  exit 0
  |   Parsing.Parse_error -> 
      print_endline "Caught Parsing.Parse_error";
      errorreport ();
      exit 1
  |   Failure s -> 
      print_endline ("Caught Failure("^s^")");
      errorreport ();
      exit 1
        



