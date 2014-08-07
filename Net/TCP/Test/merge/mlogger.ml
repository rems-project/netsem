open Platform;;
open Parserlib;;
open Printf;;
open Unix;;
open Nettypes;;
open Int64;;
open Holrender;;
open Holparselib;;
open Librender;;
open Tcpcbrender;;

exception Argerror of string;;
exception FatalError of string;;
exception MergeFinished;;


(* Type for input stream: (input_fd, offset, optional output_fd) *)
type fd_type =
    FILE of file_descr
  | SOCKET of file_descr
;;

type input_state =
    READY
  | FINISH
  | MSG of Parserlib.ns_parse_return
;;

type stream_state = {
    fd    : fd_type;
    ch    : in_channel;
    lexb  : Lexing.lexbuf option;
    off   : int64;
    state : input_state;
    out   : file_descr option;
  } ;;

let lastTraceTime = ref (uint 0, uint 0);;

(* Usage string *)
(* Caution when tweaking the spacing/formatting !! *)
let usage =
"Usage: mlogger outfile [[FILE name offset |\n                         \
    TCP ip port offset [outfile] |\n                         \
    UNIX name offset [outfile]] [...]]";;


(* Parse the command line arguments - Yuck *)
(* For syntax see usage string above *)
let parse_cmd_line_args c =
  let len = Array.length c in
  let _ =

    (* Sanity check *)
    if(len < 5) then
      (print_endline usage;
      raise(Argerror("Too few command line options.")))
    in

  (* Open the output file *)
  let outfile = openfile (Array.get c 1) [O_CREAT; O_WRONLY; O_TRUNC] 432 in

  (* Parse the arguments to form the input tuple list *)
  let inputlist =
    try
      let rec loop n l=
	if(n >= len) then
	  l (* return the completed list *)

	else if((Array.get c n) = "FILE") then
	  (* We're parsing a FILE option *)
	  let in_fd = openfile (Array.get c (n+1)) [O_RDONLY] 0 in
	  let out_fd = None in
	  let offset = Int64.of_string (Array.get c (n+2)) in
	  loop (n+3) ((FILE in_fd, offset, out_fd)::l)

	else if((Array.get c n) = "UNIX") then
	  (* We're parsing a UNIX socket option *)
	  let _ = print_endline "UNIX" in
	  let in_fd = socket PF_UNIX SOCK_STREAM 0 in
	  let _ = bind in_fd (ADDR_UNIX(Array.get c (n+1))) in
	  let _ = listen in_fd 1 in
	  let offset = Int64.of_string (Array.get c (n+2)) in
	  let t =
	    if (n+3 < len) then
	      Some(Array.get c (n+3))
	    else
	      None in
	  let out_fd =
	    (* Do we need to dump the sockets input to file? *)
	    match t with
	      None -> None
	    | Some x ->
		if ((x != "FILE") && (x != "UNIX") && (x != "TCP")) then
		  Some(openfile x [O_WRONLY; O_CREAT] 432)
		else
		  None
	  in
	  match out_fd with
	    None -> loop (n+3) ((SOCKET in_fd, offset, out_fd)::l)
	  | Some x -> loop (n+4) ((SOCKET in_fd, offset, out_fd)::l)

	else if((Array.get c n) = "TCP") then
	  (* We're parsing a TCP socket option *)
	  let in_fd = socket PF_INET SOCK_STREAM 6 in
	  let _ = bind in_fd (ADDR_INET(inet_addr_of_string(Array.get c (n+1)),
				       int_of_string(Array.get c (n+2)))) in
	  let _ = listen in_fd 1 in
	  let offset = Int64.of_string (Array.get c (n+3)) in
	  let t =
	    if (n+4 < len) then
	      Some(Array.get c (n+4))
	    else
	      None in
	  let out_fd =
	    match t with
	      (* Do we need to dump the sockets input to file *)
	      None -> None
	    | Some x ->
		if ((x != "FILE") && (x != "UNIX") && (x != "TCP")) then
		  Some(openfile x [O_WRONLY; O_CREAT] 432)
		else
		  None
	  in
	  match out_fd with
	    None -> loop (n+4) ((SOCKET in_fd, offset, out_fd)::l)
	  | Some x -> loop (n+5) ((SOCKET in_fd, offset, out_fd)::l)

	else
	  (* None of the above: the user has erred *)
	  ( raise(Argerror("Incorrect command line options.")))
      in loop 2 []

    with Unix_error(e, s1, s2) ->
      (print_endline (error_message e);
       raise(FatalError("Socket error")))
    | _ ->
      (print_endline usage;
       raise(Argerror("Incorrect command line options.")))
  in
  (outfile,inputlist);;


(* Create a list of connected fds from the input fds *)
(* The main purpose is to accept connections to *)
(* listening sockets. For file fds we simply duplicate *)
(* the fd to be consistent in having two fds for each *)
(* input stream *)
let rec prepareInputs inputlist =
  match inputlist with
    [] -> []
  | (inp,off,out)::xs ->
      match inp with
	FILE x ->
	  let fd = dup x in
	  ({ fd = FILE fd;
	     ch = in_channel_of_descr fd;
	     lexb = None;
	     off = off;
	     state = READY;
	     out = out
	   })::(prepareInputs xs)
      | SOCKET x ->
	  let fd = fst(accept x) in
	  ({ fd = FILE fd;
	     ch = in_channel_of_descr fd;
	     lexb = None;
	     off = off;
	     state = READY;
	     out = out
	   })::(prepareInputs xs);;

(* Walk through the list of input fds and *)
(* the list of connected fds closing them all *)
let closeInputs originalfds connectionfds =
  (* The connected sockets and duplicated file fds *)
  let rec closeConnections connlist =
    match connlist with
      [] -> ()
    | x::xs ->
	(match x.fd with
	  FILE f -> close f; closeConnections xs
	| SOCKET s -> close s; closeConnections xs) in

  (* The original fds opened during cmd-line arg parsing *)
  let rec closeOriginals inputlist =
    match inputlist with
      [] -> ()  (* (fd, off, outfd) -- remeber to close the outfds *)
    | (FILE x,  _, _)::xs -> close x; closeOriginals xs
    | (SOCKET x,  _, None)::xs -> close x; closeOriginals xs;
    | (SOCKET x,  _, Some y)::xs -> close x; close y; closeOriginals xs
  in
  (closeConnections connectionfds; closeOriginals originalfds);;



(* Write our header to the merged output file *)
let writeMergeHeader out =
  let header1 = sprintf
      "(* Netsem logging & merging tool (mlogger) - Date: %s   *)\n"
    (Platform.gettimeofday ()) in
  let header2 = sprintf
      "(* ----------------------------------------\
          ---------------------------------- *)\n" in
  let _ = Unix.write out header2 0 (String.length header2) in
  let _ = Unix.write out header1 0 (String.length header1) in
  let _ = Unix.write out header2 0 (String.length header2) in
  ();;


(* Scan through all of the headers in the input *)
(* files writing these to the merged output *)
(* file (moduluo the BEGINs) *)
let writeInputHeaders out inlist =
  let header2 = sprintf
      "(* ----------------------------------------\
      ---------------------------------- *)\n" in
  let rec loop l =
    match l with
      [] -> ()
    | x::xs ->
	let line = (input_line x.ch)^"\n" in
	let _ =
	  match x.out with
	    None -> ()
	  | Some f ->
	      let _ = Unix.write f line 0 (String.length line)
	      in ()
	in let _ =
	  if(line = "(* BEGIN *)\n") then
	    let str = sprintf "(* Offset applied: %s microseconds *)\n"
		(Int64.to_string x.off) in
	    let _ = Unix.write out str 0 (String.length str) in
	    (match xs with
	      [] -> ()
	    | (x::xs) ->
		let _ = Unix.write out header2 0 (String.length header2) in ());
	    loop xs
	  else
	   let _ = Unix.write out line 0 (String.length line) in
	   loop (x::xs)
	in ()
  in loop inlist;;


let doParsing env inlist =
  let rec loop l =
    match l with
      [] -> []
    | x::xs ->
	match x.state with
	  READY ->
	    (match x.lexb with
	      None ->
		loop (({x with lexb = Some(Lexing.from_channel x.ch)})::xs)
	    | Some lexbuf ->
		try
		  (let parseout = Parser.main env Lexer.token lexbuf in
		  ({x with state = (MSG parseout)})::(loop xs))
                with Lexer.Eof ->
		  ({x with state = FINISH}::(loop xs)))
	| _ -> x::(loop xs)
  in loop inlist;;


let findMinimum mlist =
  let rec loop l min =
    match l with
      [] ->
	(match min with
	  None -> raise MergeFinished
	| Some x -> x, mlist)
    | x::xs ->
	match x.state with
	  FINISH -> loop xs min
	| READY -> raise(FatalError("Tried to merge an input in the READY state"))
	| MSG(y) ->
	    match min with
	      None -> loop xs (Some x)
	    | Some msg ->
		(let (m_t1, m_t2) =
		  (match msg.state with
		    MSG d  ->
		      let (os, ous) = (Int64.div msg.off (Int64.of_string "1000000"),
				       Int64.rem msg.off (Int64.of_string "1000000")) in
		      (match d with
			PARSE_RETURN(topt, sopt, data) ->
			  (match topt with
			    None -> (os, ous)
			  | Some(TIMECOMMENT(t1,t2,str)) -> (t1 +. os, t2 +. ous)
			  )
			)
		  | _ -> raise(FatalError("findMinimum -- expected a MSG!")) )
	        in
		let (p_t1, p_t2) =
		  match y with
		    PARSE_RETURN(topt, sopt, data) ->
		      let (os, ous) = (Int64.div x.off (Int64.of_string "1000000"),
				       Int64.rem x.off (Int64.of_string "1000000")) in
		      (match topt with
			None -> (os, ous)
		      | Some(TIMECOMMENT(t1,t2,str)) -> (t1 +. os, t2 +. ous)
		      )
		in
	(*	printf "m_t1=%s m_t2=%s p_t1=%s p_t2=%s\n\n" (Int64.to_string m_t1)     *)
	(*	  (Int64.to_string m_t2) (Int64.to_string p_t1) (Int64.to_string p_t2); *)
		if(m_t1 <. p_t1) then
		  loop xs min
		else if((m_t1 ==. p_t1) && (m_t2 <=. p_t2)) then
		  loop xs min
		else
		  loop xs (Some x))
  in loop mlist None;;

let rec updateUsed update l =
  match l with
    [] -> []
  | x::xs ->
      if(x = update) then
	({x with state = READY})::xs
      else
	x::(updateUsed update xs);;


let outputMinimum min out =
  match min.state with
    MSG(PARSE_RETURN(times,commentl,parsedata)) ->
      let _ =
	match times with
	  None -> ()
	| Some (TIMECOMMENT(t1,t2,str)) ->
	    let t1 = t1 +. (Int64.div min.off (Int64.of_string "1000000")) in
	    let t2 = t2 +. (Int64.rem min.off (Int64.of_string "1000000")) in
	    (* Print the epsilon transitions first *)
	    let _ =
	      if (!lastTraceTime = (uint 0, uint 0)) then lastTraceTime := (t1,t2)
	      else
		(let d1 = Int64.sub t1 (fst(!lastTraceTime)) in
		let d2 =
		  if(t2 <. snd(!lastTraceTime)) then
		    Int64.sub (Int64.of_string "1000000")  (Int64.sub (snd(!lastTraceTime)) t2)
		  else
		    Int64.sub t2 (snd(!lastTraceTime)) in
		let _ =
		  if (d1 ==. (uint 0)) && (d2 ==. (uint 0)) then () else
		  let eps = sprintf "Lh_epsilon(duration %s %s);\n\n"
		      (Int64.to_string d1) (Int64.to_string d2) in
		  let _ = Unix.write out eps 0 (String.length eps) in
		  lastTraceTime := (t1, t2) in ())
	    in
	    (* Print the timestamp *)
	    let s = sprintf "(** %s.%s %s **)\n" (Int64.to_string t1)
		(Int64.to_string t2) str in
	    (* Write the timestamp to the merged output *)
	    let _ = Unix.write out s 0 (String.length s) in
	    (* and to any output file (for a socket input) if required to *)
	    match min.out with
	      None -> ()
	    | Some o -> let _ = Unix.write o s 0 (String.length s) in ()
      in
      let _ =
	let rec loop x =
	  match x with
	    None -> ()
	  | Some y ->
	      (match y with
		[] -> ()
	      | (c::cs) -> (let _ =  Unix.write out (c^"\n") 0 ((String.length c) + 1) in ());
			    (match min.out with
			      None -> ()
			    | Some o -> (let _ = Unix.write o (c^"\n") 0 ((String.length c) +1) in ());
			    loop (Some cs)))
	in loop commentl in
      ((match min.out with
	None ->
          (* print the calls to the main output *)
	  (match parsedata with
	    HOLSNDMSG(sndmsg) ->
	      (match sndmsg with
		TCPMSG(tcp) -> render_tcp_inner out tcp SENDDGRAM
	      | UDPMSG(udp) -> render_udp_inner out udp SENDDGRAM
	      | ICMPMSG(icmp) -> render_icmp_inner out icmp SENDDGRAM)
          | HOLLOOPMSG(loopmsg) ->
	      (match loopmsg with
                TCPMSG(tcp) -> render_tcp_inner out tcp LOOPDGRAM
	      | UDPMSG(udp) -> render_udp_inner out udp LOOPDGRAM
              | ICMPMSG(icmp) -> render_icmp_inner out icmp LOOPDGRAM)
	  | HOLRCVMSG(rcvmsg) ->
	      (match rcvmsg with
		TCPMSG(tcp) -> render_tcp_inner out tcp RECVDGRAM
	      | UDPMSG(udp) -> render_udp_inner out udp RECVDGRAM
	      | ICMPMSG(icmp) -> render_icmp_inner out icmp RECVDGRAM)
	  | LIBCALL(tid, libcall) -> lib_render_to_socket out parsedata
	  | LIBRETURN (tid, libreturn) -> lib_render_to_socket out parsedata
	  | TCPTRACE(sid, addr,state,tcpcb) ->  tcpcb_trace_render_to_socket out parsedata)
      |	Some o ->
          (* ech the calls to an output file if required to *)
	  (match parsedata with
	    HOLSNDMSG(sndmsg) ->
	      (match sndmsg with
		TCPMSG(tcp) -> render_tcp_inner o tcp SENDDGRAM;  render_tcp_inner out tcp SENDDGRAM
	      | UDPMSG(udp) -> render_udp_inner o udp SENDDGRAM; render_udp_inner out udp SENDDGRAM
	      | ICMPMSG(icmp) -> render_icmp_inner o icmp SENDDGRAM; render_icmp_inner out icmp SENDDGRAM)
	  | HOLLOOPMSG(loopmsg) ->
              (match loopmsg with
                TCPMSG(tcp) -> render_tcp_inner o tcp LOOPDGRAM; render_tcp_inner out tcp LOOPDGRAM
	      | UDPMSG(udp) -> render_udp_inner o udp LOOPDGRAM; render_udp_inner out udp LOOPDGRAM
              | ICMPMSG(icmp) -> render_icmp_inner o icmp LOOPDGRAM; render_icmp_inner out icmp LOOPDGRAM)
	  | HOLRCVMSG(rcvmsg) ->
	      (match rcvmsg with
		TCPMSG(tcp) -> render_tcp_inner o tcp RECVDGRAM; render_tcp_inner out tcp RECVDGRAM
	      | UDPMSG(udp) -> render_udp_inner o udp RECVDGRAM; render_udp_inner out udp RECVDGRAM
	      | ICMPMSG(icmp) -> render_icmp_inner o icmp RECVDGRAM; render_icmp_inner out icmp RECVDGRAM)
	  | LIBCALL(tid, libcall) -> lib_render_to_socket o parsedata; lib_render_to_socket out parsedata
	  | LIBRETURN (tid, libreturn) -> lib_render_to_socket o parsedata;
	      lib_render_to_socket out parsedata
	  | TCPTRACE(addr,state,tcpcb) ->  tcpcb_trace_render_to_socket o parsedata;
	      tcpcb_trace_render_to_socket out parsedata);
	  (let _ = Unix.write o "\n" 0 (String.length "\n") in ()));
      (let _ = Unix.write out "\n" 0 (String.length "\n") in ()))
  | _ -> raise(FatalError("outputMinimum: input channel not in the required state"))
;;


let _ =
  (* out = merged output file, inputlist = list of input streams *)
  let (out, inputlist) = parse_cmd_line_args Sys.argv in

  (* connect the fds which need connecting *)
  let mergelist = prepareInputs inputlist in

  (* Write the merge header to out *)
  (* Write individual headers to out and outoptions *)
  (* Write a single BEGIN comment to out *)
  let _ = writeMergeHeader out in
  let _ = writeInputHeaders out mergelist in
  let beginstr = "(* BEGIN *)\n" in
  let _ = Unix.write out beginstr 0 (String.length beginstr) in

  (* Parse input from all of the streams *)
  let parseenv = Threadparsing.create_parse_env () in
  let newlist = doParsing parseenv mergelist in

  (* Select minimum time respecting the stream offsets *)
  (* Output minimum entry and parse next packet -- *)
  (* be careful with FINISHED streams *)
  (* Repeat until all streams are FINISHED *)
  let _ =
    let rec loop l =
      try
	let (min, mergelist) = findMinimum l in
	let mergelist = updateUsed min mergelist in
	let _ = outputMinimum min out in
	let l = doParsing parseenv mergelist in
	loop l
      with MergeFinished -> ()
    in loop newlist
  in

  (* Clean up the fds *)
  let _ = closeInputs inputlist newlist in
  let _ = close out in
  ();;
