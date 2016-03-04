open Parserlib;;
open Renderlib;;

let trace_contents fname =
  let inch = Unix.in_channel_of_descr (Unix.openfile fname [Unix.O_RDONLY] 0) in
  let env = Threadparsing.create_parse_env () in
  let result = ref [] in
    try
      let lexbuf = Lexing.from_channel inch in
	while true do
	  let next =
            try
              Parser.spec3main env Lexer.token lexbuf
            with
		Threadparsing.Parse_error ->
		  print_endline ("Fatal: Parse error in file " ^ fname);
		  (match !result with
		       [] -> print_endline "(Failed to parse header information block)"
		     | SPEC3_PARSE_RETURN(tco,_,_)::_ -> print_endline
			 ("Last label parsed had timecomment: " ^ timecomment_option_to_string tco ));
		  exit 1
	  in
	  let _ =  print_string "Got one! \n" in
	    (result := next::(!result))
	done; []
    with Lexer.Eof -> (* List.rev *) !result;;

let _ =
  let [_;f] = Array.to_list Sys.argv in
  let _ = trace_contents f in
    ()
;;

