open Thread;;
open Unix;;
open Parsetypes;;
open Parser;;
open ThreadUnix;;
open Platform;;
exception Fatal of string;;

(* ------------------------------------------------------------ *)
(* We require some environment variables to be set: *)
(*  EXEC_LIBD - path to libd *)
(*  EXEC_SLURP - path to slurper *)
(*  EXEC_INJECTOR - path to injector *)
(*  EXEC_HOLTCPCP - path to holtcpcb *)
(* ------------------------------------------------------------ *)

(* Maximum size of the listening queue *)
let max_listening_connections = 50;;
let env_prog_err = "custom_rsh: attempt to run an invalid program or environment variable not found: ";;

(* Debugging *)
let rec print_list x =
	match x with
		[] -> ()
	| (x::xs) -> prerr_endline x; print_list xs;;

(* Check and get the command-line arguments: custom_rsh ipaddr port *)
let check_cmdline_args argv =
  let len = Array.length argv in
  if(len != 3) then
    raise(Fatal("Incorrect arguments: custom_rsh ipaddr port"))
  else
    (Array.get argv 1, Array.get argv 2);;

let lookup prog =
  match prog with
    EXEC_LIBD -> "EXEC_LIBD"
  | EXEC_SLURP -> "EXEC_SLURP"
  | EXEC_INJECTOR -> "EXEC_INJECTOR"
  | EXEC_HOLTCPCB -> "EXEC_HOLTCPCB";;

let process_env env =
  match env with
    (var,str) ->
      (var^"="^str);;

let lexer_input_function sd buf len =
  let rec loop () =
	try recv sd buf 0 len []
	with Unix_error(e,s1,s2) -> prerr_endline ("EXCP: "^(error_message e)^"\n"); raise (Unix_error(e,s1,s2))
	(*with Unix_error(EAGAIN,_,_) -> loop ()
	   | Unix_error(ECONNRESET,_,_) -> 0
	   | Unix_error(ENOTCONN,_,_) -> 0
	   | Unix_error(EINTR,_,_) -> loop()*)
  in loop();;

(* Thread to deal with each connection *)
let worker sdconn =
  let running_pid = ref 0 in
  let lexbuf = Lexing.from_function (lexer_input_function sdconn) in
  let rec loop () =
	try
      let (prog, envl, argsl) = Parser.main Lexer.token lexbuf in
      (* Do something *)
      let progcmd =
        try Some(Sys.getenv (lookup prog))
	    with Not_found -> None in
        match progcmd with
	      None -> prerr_endline (env_prog_err^(lookup prog))
        | Some(prog_path) -> (
	      let envarray = Array.concat [environment ();
									   Array.of_list (List.map process_env envl);] in
	      (*Debugging only: print_list argsl;*)
	      let argarray = Array.of_list argsl in
	      let pid = create_process_env prog_path argarray envarray stdin stdout stderr in
	      running_pid := pid;
	      loop ()
	      )
	with Lexer.Eof -> ()
    | Unix_error(e,s1,s2) -> prerr_endline ("EXCP: "^(error_message e)^"\n"); raise (Unix_error(e,s1,s2)) in
  loop ();
  let _ = try Platform.win32_terminate_process !running_pid 0
          with _ -> () in
  prerr_endline "KILLED";
  close sdconn;;


(* Start listening *)
let (ip, port) = check_cmdline_args Sys.argv in
let sd = ThreadUnix.socket PF_INET SOCK_STREAM 6(*TCP*) in
let _ = bind sd (ADDR_INET(inet_addr_of_string(ip), int_of_string(port))) in
let _ = listen sd max_listening_connections in
let rec f x = (
    try
		let sdconn = fst(ThreadUnix.accept sd) in
	    let _ = Thread.create worker sdconn in
		()
	with
		_ -> f());
	f()
in f ();
close sd;;
