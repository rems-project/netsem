open Parserlib;;
open Ocamllib;;
open Libcalls;;
open Librender;;
open Unix;;
open Thread;;
open ThreadUnix;;
open Platform;;

exception Fatal of string;;
exception Argerror of string * unit;;

let parsepacket sd =
  let parseenv = Threadparsing.create_parse_env () in
  let lexbuf = Lexing.from_channel (Unix.in_channel_of_descr sd) in
  let rec loop continue =
    if continue then
      (
       let result =
	 try Some(Parser.main parseenv Lexer.token lexbuf)
	 with _ -> None in
       match result with
	 Some(PARSE_RETURN(_,_,LIBCALL(tid,x))) ->
	   (
	    let libreturn = makelibcalls x in
	    let s = lib_return_render libreturn tid in
	    let _ = Sock.write sd (" "^s) in (* FIXME tjr not sure about the space- was in librender previously *)
	      ();
	      loop true
	   )
       | Some(_) -> raise(Fatal("Error: parser returned an unexpected message type"))
       | None -> loop false
      )
    else ()
  in loop true;;


let cmdlineargs = "Usage: libd -priv TCP ip port\n                  UNIX unixsockname";;

let check_cmdline_args argv =
  let len = Array.length argv in
  let pos = ref 1 in
  if(len < 3) then
    (raise(Argerror("Incorrect arguments: ", print_endline(cmdlineargs))))
  else
    let priv =
      if((Array.get argv !pos) = "-priv") then
	(pos := !pos + 1; true)
      else
	false in
    (if((Array.get argv !pos) = "TCP") then
      let sd = ThreadUnix.socket PF_INET SOCK_STREAM 0 in
      let _ = setsockopt sd SO_REUSEADDR true in
      let addr = ADDR_INET (inet_addr_of_string (Array.get argv (!pos + 1)),
			    int_of_string (Array.get argv (!pos + 2))) in
      let _ = bind sd addr in
      let _ = listen sd 0 in
      let (sdconn, sdaddr) = ThreadUnix.accept sd in
      (* Output the libd pid *)
      let pidstr = string_of_int (int_of_tid (gettid ())) ^ "\n\n" in
      Sock.write sdconn pidstr;
      (priv, sd, sdconn)
    else if((Array.get argv !pos) = "UNIX") then
      let sd = Unix.socket PF_UNIX SOCK_STREAM 0 in
      let _ = Unix.setsockopt sd SO_REUSEADDR true in
      let addr = ADDR_UNIX (Array.get argv (!pos + 1)) in
      let _ = Unix.bind sd addr in
      let _ = Unix.listen sd 0 in
      let (sdconn, sdaddr) = Unix.accept sd in
      (priv, sd, sdconn)
    else
      (raise(Argerror("Incorrect arugments: ", print_endline(cmdlineargs)))));;

let _ =
  let (priv, sd, sdconn) = check_cmdline_args Sys.argv in
  if (not priv) && not ((check_platform ()) = WIN32) then
    setuid (getuid ());
  let _ = parsepacket sdconn in
  let _ = Unix.close sdconn in
  Unix.close sd;;

