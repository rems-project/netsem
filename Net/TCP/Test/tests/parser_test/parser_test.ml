open Parserlib;;
open Unix;;

let parsepacket fname =
  let fd = Unix.openfile fname [O_RDONLY] 0 in
  let ch = Unix.in_channel_of_descr fd in
  let env = Threadparsing.create_parse_env () in
  try let lexbuf = Lexing.from_channel ch in
      while true do
        let result =
	  Parser.main env Lexer.token lexbuf
	in
	  match result with
	    PARSE_RETURN(_,_,r) ->
	      (match r with
		HOLSNDMSG(_) -> prerr_endline "HOLSNDMSG"
	      | HOLRCVMSG(_) -> prerr_endline "HOLRCVMSG"
	      |	HOLLOOPMSG(_) -> prerr_endline "HOLLOOPMSG"
	      | LIBCALL(_) -> prerr_endline "LIBCALL"
	      | LIBRETURN(_) -> prerr_endline "LIBRETURN"
	      | TCPTRACE(_) -> prerr_endline "TCPTRACE"
	      |	HOLEPSILON(_) -> prerr_endline "HOLEPSILON"
	      |	HOLABSTIME(_) -> prerr_endline "HOLABSTIME"
	      )
      done
  with Lexer.Eof ->
    exit 0;;

let t = Thread.create parsepacket (Array.get (Sys.argv) 1) in
Thread.join t

