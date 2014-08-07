(* Netsem TThee -- TCP Testing (host) Executive Engine *)
(* Steve Bishop -- Created 20021210                    *)
(* $Id: tthee.ml,v 1.76 2006/08/17 11:29:32 tjr22 Exp $ *)

(* ----------------------------------------------- *)
(* READER HEALTH WARNING: Sometimes we don't       *)
(* bother locking a structure, because we believe  *)
(* OCAML assignment is atomic.                     *)
(* Careful, however!  If we wait on a condition,   *)
(* we'd better use the corresponding lock, since   *)
(* the wait assumes the event can only happen      *)
(* when the lock is not held.  If it happens       *)
(* when the lock is held, we might miss the event! *)
(* ----------------------------------------------- *)

(* ----------------------------------------------- *)
(* HEALTH WARNING: this code is multi-threaded --  *)
(* break it at your own risk! You may wish to      *)
(* adhere to the following mutex locking policy:   *)
(*  a) All required locks should be obtained in    *)
(*     one phase                                   *)
(*  b) All locks should be released in a seperate  *)
(*     phase                                       *)
(*  c) Locks must be obtained in the order         *)
(*     specified in a given subsection's comments  *)
(*  d) Locks should be released in the reverse     *)
(*     order to that specified by (c)              *)
(* ----------------------------------------------- *)

open Nettypes;;
open Netconv;;
open Parserlib;;
open Holparselib;;
(* open Render;; *)
open Librender;;
open Sock;;
open Holrender;;
open Mergelib;;
open Renderlib;;
open Platform;;
open Holtypes;;

open Thread;;
open Mutex;;
open Printf;;
open Lexing;;

(* NB: ThreadUnix must appear after Unix although *)
(* where something specifically relies on a given *)
(* version the code should explicitly prefix the  *)
(* the module name                                *)
open Unix;;
open ThreadUnix;;

exception TThee_fatal of string;;





(* -------------------------------------------------------------------- *)
(*                           Useful defs                                *)
(* -------------------------------------------------------------------- *)

let listen_max_conns = 1;;

(* Time after which threads blocked waiting for streams to *)
(* connect and reach a post header state unblock.          *)
(* Default = 30.0 seconds. This is used to ensure that     *)
(* any merger threads do not block indefinitely and that   *)
(* things can be shutdown nicely                           *)
let no_action_delay = 30.0;;

(* Write to a channel, flushing after use *)
let output_string_and_flush ch str =
  output_string ch str;
  Pervasives.flush ch;;

(* Safely write to stderr with a trailing endline, flushing after use *)
(* ** SHADOWS Pervasives.prerr_endline ** *)
(* (note that Pervasives.prerr_endline performs two operations, and so
   a context switch can occur between s and "\n") *)
let prerr_endline s =
  output_string_and_flush Pervasives.stderr (s^"\n");;

(* Debug levels: 0-None 1-Messages *)
(*               2-Funtrace 3-Verbose 4-Really verbose *)
let (debug_OFF, debug_MSG, debug_FUN, debug_VER, debug_MUT) = 0,1,2,3,4;;
let debug_level = ref debug_OFF;;

(* Print a debug message str at level n *)
let debug_print n str =
  if(!debug_level >= n) then
    let pid = Unix.getpid() in
    let tid = Thread.id (Thread.self ()) in
    let s = "(PID "^(string_of_int pid)^", TID "^(string_of_int tid)^") "^str in
    prerr_endline s (* must use _endline variant; this autoflushes *)
  else ();;


(* Set the debug_level to level n *)
let set_debug_level n =
  if (n < debug_OFF) or (n > debug_MUT) then
    raise (TThee_fatal("Invalid debug level:"^(string_of_int n)))
  else
    debug_level := n;
    debug_print debug_MSG ("Debugging enabled, level: "^(string_of_int n));;

(* Write to a channel, flushing after use *)
let output_string_and_flush ch str =
  output_string ch str;
  Pervasives.flush ch;;

(* Construct a uint32 representing an IP address *)
let ip_of_ints a b c d =
  let (ip, c) = input_uint32_net [Char.chr a; Char.chr b; Char.chr c; Char.chr d] in
  ip;;

let port_of_int a =
  uint a;;

(* The obvious thing *)
let lift f x =
  match x with
    None -> None
  | Some(y) -> Some(f y);;




(* -------------------------------------------------------------------- *)
(*                              Common                                  *)
(* -------------------------------------------------------------------- *)

(* The type of events that happen on a stream. These   *)
(* are the events that are passed to our internal      *)
(* callback handlers                                   *)
type stream_info =
    STREAM_HEADER of string
  | STREAM_PARSEDATA of ns_parse_return
  | STREAM_EOF;;

(* The type of our internal callback functions *)
type callback = {
    cb_id: unit ref;
    cb_fun: stream_info -> unit
  } ;;

type connection_state = {
    sd: file_descr;            (* Connected socket descriptor from accept() *)
    ch: in_channel;            (* and associated input channel *)
    lb: Lexing.lexbuf option   (* and lex buffer *)
  } ;;

(* The states that a log channel can be in *)
type connection_state_option =
    UNCONNECTED
  | CONNECTED_PREHDR of connection_state   (* before we have read the file header *)
  | CONNECTED_POSTHDR of connection_state  (* after we have read the file header *)
  | FINISHED                               (* informing callbacks of EOF *)
  | REALLYFINISHED ;;                      (* selector thread has terminated *)


(* Log_handle: These are TCP sockets for now (otherwise we have to perform) *)
(* sanity checking in order to ensure that we don't use a UNIX *)
(* domain logging channel with remote execution etc, etc...  *)

(* WARNING: obtain lock before reading or modifying cbs and before *)
(* changing the state *)
type log_handle = {
    lock: Mutex.t;           (* Lock for log_cbs, connected_posthdr, reallyfinished_cond *)
    fd: file_descr;          (* Listening socket *)
    state: connection_state_option ref;  (* no lock required; only accessed by selector thread *)
    cbs: callback list ref;
    connected_posthdr: Condition.t;  (* signalled once when state >= CONNECTED_POSTHDR *)
    reallyfinished_cond: Condition.t;  (* signalled once state >= REALLYFINISHED *)
  } ;;

type log_callback_handle = {
    cb_valid: bool ref;
    logch: log_handle;
    cb: callback
  } ;;

exception Invalid_log_callback_handle of string * log_callback_handle;;

(* Type of command channels *)
type sock_type =
    TCP of ip * port
  | UNIX of string;;

(* try_connect file_descr sockaddr = unit *)
(* Connects to a listening socket. On failure *)
(* performs exponential backoff and retries *)
(* a few times *)
let try_connect sd addr =
  debug_print debug_VER "try_connect() entered";
  let rec connect_loop n wait err =
    debug_print debug_VER ("  try_connect(): connect_loop n="^(string_of_int n));
    if n=0 then
      (debug_print debug_VER "try_connect() failed";
       match err with
         None -> () (* can not get to this state *)
       | Some(e) -> raise(e))
    else
      try ThreadUnix.connect sd addr
      with x ->
        (Thread.delay wait;
         connect_loop (n-1) (float_mul 2.0 wait) (Some x)) in
  connect_loop 4 1.0 None;
  debug_print debug_VER "try_connect() returned successfully";;






(* -------------------------------------------------------------------- *)
(*                              Executor (the nice kind ;-)             *)
(* -------------------------------------------------------------------- *)

exception Exec_assert of string;;

(* Applications that we can execute *)
type exec_program =
    EXEC_LIBD
  | EXEC_SLURP
  | EXEC_INJECTOR
  | EXEC_HOLTCPCB
  | EXEC_MIRROR
  | EXEC_TSCAL (* for windows only *)

(* These strings should be fully qualifed path names *)
(* e.g. /TCP/Test/slurp/slurp *)
type exec_paths = {
    libd_path : string;
    slurp_path : string;
    injector_path : string;
    holtcpcb_path : string;
    mirror_path : string;
  } ;;

type rsh_client =
    SSH of string       (* path of ssh client *)
  | CUSTOM_RSH of int   (* port of listening CUSTOM_RSH daemon *)
;;

(* Execution locations *)
type exec_params =
    LOCAL of exec_paths
  | REMOTE of string * rsh_client * exec_paths;;

(* Lookup application paths *)
let exec_lookup_exec_path ep prog =
  match prog with
    EXEC_LIBD -> ep.libd_path
  | EXEC_SLURP -> ep.slurp_path
  | EXEC_INJECTOR -> ep.injector_path
  | EXEC_HOLTCPCB -> ep.holtcpcb_path
  | EXEC_MIRROR -> ep.mirror_path
  | EXEC_TSCAL -> raise (TThee_fatal "EXEC_TSCAL is only valid on WinXP (Time calibration)");;

let exec_lookup_exec_path_customrsh prog =
  match prog with
    EXEC_LIBD -> "L"
  | EXEC_SLURP -> "S"
  | EXEC_INJECTOR -> "I"
  | EXEC_HOLTCPCB -> "T"
  | EXEC_MIRROR -> "M"
  | EXEC_TSCAL -> "C"

(* Functions for making environment variable defs *)
let rec exec_mklocalenv envlist =
  match envlist with
    [] -> []
  | (x,y)::xs -> (x^"="^y)::(exec_mklocalenv xs);;

let rec exec_mkremote_unix_env envlist =
  match envlist with
    [] -> ""
  | (x,y)::xs -> (x^"="^y)^" "^(exec_mkremote_unix_env xs);;

let rec exec_mkremote_unix_args arglist =
  match arglist with
    [] -> ""
  | [x] -> x^" "
  | x::xs -> x^" "^(exec_mkremote_unix_args xs);;

let rec exec_mkcustomrsh_env envlist =
  let f (x,y) = x^"="^y in
  String.concat "$" (List.map f envlist);;

let rec exec_mkcustomrsh_args arglist =
  let f x =
    if String.contains x ' ' then
      "\"" ^ x ^ "\""
    else
      x in
  String.concat " " (List.map f arglist);;

(* do_exec execparam program arglist envlist = pid, fd  *)
(* Takes a program execution parameter record, a        *)
(* program to execute, an argument list and an          *)
(* environment list and executes the program either     *)
(* locally or remotely depending upon the parameters    *)
(* Returns the pid of the new process and the input     *)
(* to it's control pipe (used for clean termination)    *)
let do_exec execparam prog arglist envlist =
  debug_print debug_FUN "do_exec() called";
(* FIXME amgb debug code
print_endline "*** do_exec arg list = ";
List.iter print_endline arglist; *)
  let (pid,fdi,fdo, redirect) =
    match execparam with
      LOCAL(ep) -> (
	let prog_path = exec_lookup_exec_path ep prog in
	debug_print debug_VER ("  local: "^prog_path^" "^
			       (exec_mkremote_unix_args arglist));
	let (fdo,fdi) = ThreadUnix.pipe () in
	let args = Array.of_list (prog_path::arglist) in
	let env = Array.of_list (exec_mklocalenv envlist) in
	let pid = Unix.create_process_env prog_path args env fdo stdout stderr in
	(pid,fdi,fdo,fdi (*hacky workaround that will be ignored*)))
    | REMOTE(host,rsh,ep) ->
	(
	match rsh with
	  SSH(ssh_path) ->
	    let prog_path = exec_lookup_exec_path ep prog in
	    let remote_cmd = "env " ^ (exec_mkremote_unix_env envlist) ^
	      prog_path ^ " " ^ (exec_mkremote_unix_args arglist) in
	    let pty1,pty2 = getpty () in
	    debug_print debug_VER ("  "^host^": "^remote_cmd);
	    let redirect = Unix.openfile "/dev/null" [O_RDWR] 0 in
	    let args = Array.of_list (ssh_path::"-t"::host::remote_cmd::[]) in
(* FIXME amgb debug code print_endline ("remote command = " ^ remote_cmd); *)
	    let pid = Unix.create_process ssh_path args pty1 redirect redirect in
	    (pid,pty1,pty2,redirect)
	|  CUSTOM_RSH(remote_port) ->
	    let remote_prog = exec_lookup_exec_path_customrsh prog in
	    let envstr = (exec_mkcustomrsh_env envlist)  in
	    let argstr = if prog=EXEC_TSCAL then (exec_mkcustomrsh_args arglist) else "dummy_prog_name " ^ (exec_mkcustomrsh_args arglist) in

	    let remote_cmd = remote_prog ^ envstr ^ (if prog=EXEC_TSCAL then argstr ^ "\n" else "*" ^ argstr^"*\n") in
	    debug_print debug_VER ("remote_cmd: "^remote_cmd);
	    let sd = ThreadUnix.socket PF_INET SOCK_STREAM 6 (*TCPIP*) in
	    let _ = try ThreadUnix.connect sd (ADDR_INET(inet_addr_of_string host, remote_port))
		with _ -> debug_print debug_OFF ("######SOME CONNECT ERROR OCCURED######\n")
	    in
 	    (* let ch = out_channel_of_descr sd in
	    let _ = Pervasives.output ch remote_cmd 0 (String.length remote_cmd) in *)
	    let _ = Sock.write sd remote_cmd in
	    (0, sd, sd, sd))  (* we don't have a pipe here so this is a hacky work around *)
  in
  debug_print debug_FUN "do_exec() returned succesfully";
(* FIXME amgb debug code print_endline "do_exec returned"; *)
  (pid,fdi,fdo,redirect);;

(* Executioner  *)
(* val do_kill: exec_param pipe_input_fd redirect_fd pid = bool    *)
(* Kills a forked process -- if the process is load it             *)
(* just kills it's pid. If it is remote ssh then it writes         *)
(* to it's control pipe then closes it (this will kill the remote  *)
(* process chain and eventually our local child process            *)
(* If the process is custom rsh then raise an exception for now    *)
(* Also closed the fd redirect_fd used to redirect stdout and      *)
(* and stderr when forking processes using ssh                     *)
(* --- *)
let do_kill execparams pipei pipeo redirect pid =
  match execparams with
    LOCAL(_) ->
      close pipeo;
      close pipei;
      (try kill pid 9; true
      with _ -> false)
  | REMOTE(_,SSH(_),_) ->
       debug_print debug_VER "do_kill(): done write and close";
       kill pid 9;
       (* Kill the master pty and the slave goes away too *)
       close pipei;
       close redirect;
       let _ = waitpid [] pid in
       true
  | REMOTE(_,CUSTOM_RSH(_),_) ->
      shutdown pipeo SHUTDOWN_SEND;
      close pipei;
      debug_print debug_VER "do_kill(): closed custom_rsh pipe";
      true;;
(* --- *)


(* -------------------------------------------------------------------- *)
(*                              Selector                                *)
(* -------------------------------------------------------------------- *)

exception Selector_Fatal of string;;

(* selector_thread log_channel = unit                 *)
(* One selector thread is spawned per log channel     *)
(* It operates in one of four states:                 *)
(* i) If the log channel is unconnected it accepts    *)
(* a new connection then goes into CONNECTED_PREHDR   *)
(* state                                              *)
(* ii) In CONNECTED_PREHDR it reads continually from  *)
(* the channel until all the headers have been read   *)
(* The headers are given to all registered callback   *)
(* functions and log is left in CONNECTED_POSTHDR     *)
(* state                                              *)
(* iii) In CONNECTED_POSTHDR messages are parsed from *)
(* the channel until EOF is reached. Each parsed      *)
(* is passed to all registered callbacks. EOF forces  *)
(* the stream into FINISHED state                     *)
(* iv) In FINISHED stated, STREAM_EOF is sent to each *)
(* registered callback and the thread dies nicely     *)
let selector_thread logch =
  debug_print debug_FUN "selector_thread() started";
  let parseenv = Threadparsing.create_parse_env () in
  let _ =
    while not (!(logch.state) = FINISHED) do
      match !(logch.state) with
	UNCONNECTED ->
	  (* Accept a connection and build new connection record *)
	  (* Update state to CONNECTED_PREHDR *)
	  debug_print debug_VER "  selector(): UNCONNECTED";
	  let (connsd, saddr) =
	    try ThreadUnix.accept logch.fd
	    with _ -> raise(Selector_Fatal("accept failed")) in
	  let chan = in_channel_of_descr connsd in
	  let connstate =
	    { sd = connsd;
	      ch = chan;
	      lb = None (* Don't create lexbuf here -- wait until after hdrs are read *)
	    } in
	  logch.state := CONNECTED_PREHDR(connstate);
      | CONNECTED_PREHDR(conn) ->
	  (* Keep reading from input channel until either all of the headers *)
	  (* are read in (upto BEGIN) or until EOF. Send the headers to all of *)
	  (* the registered callback functions and leave in state *)
	  (* CONNECTED_POSTHDR to assert that all the headers have been read *)
	  debug_print debug_VER "  selector(): CONNECTED_PREHDR";
	  (* Read all headers *)
	  let hdrstr =
	    let rec read_loop str =
	      let line =
	      try (input_line conn.ch)^"\n"
	      with End_of_file -> raise(Selector_Fatal("Got EOF whilst reading headers"))
	      in
	      try if((String.sub line 0 11) = "(* BEGIN *)") then str
	          else read_loop (str^line)
	      with Invalid_argument(_) -> read_loop (str^line)
	    in read_loop ""
	  in
	  (* Send headers to registered callbacks *)
	  List.iter (function f -> (f.cb_fun) (STREAM_HEADER(hdrstr))) !(logch.cbs);
	  (* Create lexbuffer ready for parsing *)
	  let newconn =
	    { sd = conn.sd;
	      ch = conn.ch;
	      lb = Some(Lexing.from_channel conn.ch)  (* Create lexbuffer *)
	    } in
	  logch.state := CONNECTED_POSTHDR(newconn);
          Mutex.lock logch.lock;
	  Condition.broadcast logch.connected_posthdr;
          Mutex.unlock logch.lock
      | CONNECTED_POSTHDR(conn) ->
	  (* Try and parse the next message from the channel. Send read messages *)
	  (* to all registered callback functions. If EOF then enter FINISHED state *)
	  debug_print debug_VER "  selector(): CONNECTED_POSTHDR";
	  let lexb =
	    match conn.lb with
	      None -> raise (Selector_Fatal("In CONNECT_POSTHDR state but don't have a lexbuf"))
	    | Some(lb) -> lb in
	(try
	  let parseout = Parser.main parseenv Lexer.token lexb in
	  debug_print debug_VER "  selector(): handing messages to the callbacks";
	  List.iter (function f -> (f.cb_fun) (STREAM_PARSEDATA(parseout))) !(logch.cbs)
	with
	  Lexer.Eof -> close conn.sd; logch.state := FINISHED
	| Sys_error(_) -> close conn.sd; logch.state := FINISHED)
      |	FINISHED -> ()  (* Shouldn't get here due to loop invariant *)
      |	REALLYFINISHED -> ()  (* Shouldn't get here *)
    done in

  (* EOF was read in the last cycle. Send EOF to all registered *)
  (* callbacks and die *)
  debug_print debug_VER "  selector(): FINISHED";
  debug_print debug_VER "  selector(): Sending EOF to all registered callbacks";
  List.iter (function f -> (f.cb_fun) STREAM_EOF) !(logch.cbs);
  debug_print debug_VER "  selector(): Done sending EOF to callbacks; signalling completion";
  Mutex.lock logch.lock;
  logch.state := REALLYFINISHED;
  Mutex.unlock logch.lock;
  Condition.broadcast logch.reallyfinished_cond;
  match !(logch.state) with
    CONNECTED_PREHDR(connstate) ->
      close connstate.sd
  | _ -> ();  (* shouldn't get to this case *)
  debug_print debug_FUN "  selector(): closed log connected fd\nselector thread exited normally";;


(* Wait until a selector's log is connected POSTHDR *)
(* Used to ensure that no race conditions occur during *)
(* process start up *)
let selector_wait_until_connected logch =
  let is_connected st =
    match st with
      UNCONNECTED -> false
    | CONNECTED_PREHDR(x) -> false
    | _ -> true in
  Mutex.lock logch.lock;
  while not (is_connected !(logch.state)) do
    Condition.wait logch.connected_posthdr logch.lock;
  done;
  Mutex.unlock logch.lock;;


(* Wait until a log's selector thread has died *)
(* Used to ensure that no race conditions occur during *)
(* process start up *)
let selector_wait_until_really_finished logch =
  debug_print debug_VER "selector_wait_until_really_finished() called";
  Mutex.lock logch.lock;
  while !(logch.state) <> REALLYFINISHED do
      (debug_print debug_VER "selector_wait_until_really_finished going to sleep";
       Condition.wait logch.reallyfinished_cond logch.lock;
       debug_print debug_VER "selector_wait_until_really_finished woke up")
  done;
  Mutex.unlock logch.lock;
  debug_print debug_VER "selector_wait_until_really_finished() returned ok";;






(* -------------------------------------------------------------------- *)
(*                              Logs                                    *)
(* -------------------------------------------------------------------- *)

(* create_fresh_log bindip = handle *)
(* Create a fresh listening log (socket) and register with selector *)
let create_fresh_log bindip =
  debug_print debug_FUN "create_fresh_log() called";
  let sd = ThreadUnix.socket PF_INET SOCK_STREAM 0 in
  let _ = Unix.setsockopt sd Unix.SO_REUSEADDR true in

  (* Bind to the default iface and auto select an ephemeral port *)
  let ipaddr = inet_addr_of_string bindip in
  let _ = Unix.bind sd (ADDR_INET(ipaddr, 0)) in
  let boundaddr = Unix.getsockname sd in
  let (ip,port) =
    match boundaddr with
      ADDR_UNIX(x) -> raise (TThee_fatal("create_fresh_log(): ADDR_UNIX not yet supported!"))
    | ADDR_INET(ip,port) -> (ip,port) in
  let _ = Unix.listen sd listen_max_conns in
  debug_print debug_VER ("  create_fresh_log(): log listening ip:"^
			 (string_of_inet_addr ip)^ " port:"^(string_of_int port));

  (* Create a fresh log handle *)
  let log_handle = { lock = Mutex.create();
		     fd = sd;
		     state = ref UNCONNECTED;
		     cbs = ref [];
		     connected_posthdr = Condition.create ();
                     reallyfinished_cond = Condition.create ();
		   } in

  (* Create fresh selector thread for this log *)
  let tid = string_of_int (Thread.id (Thread.create selector_thread log_handle)) in
  let pid = string_of_int (Unix.getpid ()) in
  debug_print debug_VER ("  create_fresh_log(): selector_thread (PID "^pid^" TID "^tid^")");
  debug_print debug_FUN "create_fresh_log() returned normally";
  log_handle;;

(* destroy_log handle = unit *)
(* Destroy a log channel once it is finished with *)
let destroy_log handle =
  debug_print debug_FUN "destroy_log() called";
  close handle.fd;
  debug_print debug_FUN "destroy_log() returned normally";;


(* get_log_name log_handle = ip * port *)
(* Return the ip and port a log is listening on *)
let get_log_name handle =
  match (Unix.getsockname handle.fd) with
    ADDR_UNIX(s) -> raise (TThee_fatal("get_log_name: expected an ADDR_INET"))
  | ADDR_INET(ip,port) -> (string_of_inet_addr ip, string_of_int port)
;;

(* log_register_callback log_handle callback = log_callback_handle *)
(* Generic callback registration function *)
let log_register_callback logch cb =
  debug_print debug_FUN "log_register_callback() called";
  debug_print debug_MUT "  log_register_callback(): waiting for mutex";
  Mutex.lock logch.lock;
  debug_print debug_MUT "  log_register_callback(): obtained mutex";
  let callback = {
    cb_id = ref ();
    cb_fun = cb
  }  in
  logch.cbs := callback::!(logch.cbs);
  Mutex.unlock logch.lock;
  debug_print debug_MUT "  log_register_callback(): released mutex";
  debug_print debug_VER "log_register_callback returned successfully";
  { cb_valid = ref true;
    logch = logch;
    cb = callback; } ;;

(* log_deregister_callback log_callback_handle = unit *)
(* Generic callback registration function. On deregistering a callback *)
(* a STREAM_EOF message is passed to the callback function. This ensures *)
(* things terminate nicely ;-) *)
let log_deregister_callback cbhnd =
  debug_print debug_FUN "log_deregister_callback() called";
  if not !(cbhnd.cb_valid) then
    raise(Invalid_log_callback_handle("log_deregister_callback", cbhnd))
  else
    debug_print debug_MUT "  log_deregister_callback(): waiting for mutex";
    let _ = Mutex.lock cbhnd.logch.lock in
    debug_print debug_MUT "  log_deregister_callback(): obtained mutex";
    let new_cb_list =
      let keep_predicate y =
	if y.cb_id == cbhnd.cb.cb_id then false
	else true in
      List.filter keep_predicate !(cbhnd.logch.cbs)
    in
    cbhnd.cb.cb_fun (STREAM_EOF);
    cbhnd.logch.cbs := new_cb_list;
    cbhnd.cb_valid := false;
    Mutex.unlock cbhnd.logch.lock;
    debug_print debug_MUT "  log_deregister_callback(): released mutex";
    debug_print debug_FUN "log_deregister_callback() returned successfully";;






(* -------------------------------------------------------------------- *)
(*                              Merger                                  *)
(* -------------------------------------------------------------------- *)

type merger_output_mode =
    RAW
  | HOLDEF;;  (* Put HOL decorations around output *)

(* Per channel queue state *)
type merge_channel_state = {
    logch    : log_handle;
    (* Queue of parse messages *)
    (* WARNING: obtain q_lock before reading or writing queue *)
    q_lock   : Mutex.t;
    queue    : (merge_input * time) Queue.t;
    (* Callback handle associated with queue *)
    cbhnd    : log_callback_handle option ref;
    (* Offset to be applied to messages in this queue *)
    offset     : time ref;
    identifier : string option
  } ;;


type merger_handle = {
    m_valid       : bool ref;             (* Handle valid *)
    m_output_mode : merger_output_mode;   (* Are we in HOL output mode *)
    m_outch       : out_channel;          (* Channel to write merged msgs to *)
    m_tid         : Thread.t option ref;  (* Merger TID -- so we can do a join on merger_destroy *)
    m_delta       : uint ref;             (* Per-merger time delta correction *)
    m_hdr_string  : string ref;               (* Custom header string merger is to print at top of output *)

    (* Registered callback input queues *)
    m_in_list     : merge_channel_state list ref;

    (* Stops the merger thread from starting until the user says we *)
    (* can begin (once all logs have been registered) and all the   *)
    (* log headers have been read in.                               *)
    (* INVARIANT: m_number_registered_cbs = List.length m_in_list   *)
    m_number_registered_cbs   : int ref;       (* Number of registered callbacks *)
    m_number_registered_cbs_lock : Mutex.t;    (* Lock for the above *)
    m_thread_try_start : Condition.t;    (* Signalled when a cb goes posthdr *)
    m_thread_number_cbs_posthdr : int ref;  (* Number of cbs that are posthdr *)
    (* Does the caller say that the merger can begin *)
    m_user_said_begin_cond : Condition.t;
    m_user_said_begin_lock : Mutex.t;
    m_user_said_begin : bool ref;

    (* New data in queues? *)
    m_new_data_mutex : Mutex.t;
    m_new_data_cond  : Condition.t;
    m_new_data : bool ref;
  } ;;

exception Merger_invalid_handle of string * merger_handle;;
exception Merger_deregister_failed of string;;
exception Merger_fatal of string;;
exception Merger_done;;
exception Merger_continue_loop;;

(* Test whether a queue is empty or not *)
let queue_isempty q =
  try
    let _ = Queue.peek q in false
  with Queue.Empty -> true;;

(* merger_begin handle delta hdr_string = unit *)
(* Starts the merger process once all logs have been registered *)
(* Delta is the per-thread merger delay *)
(* Hdr_string is any custom string that needs to be written *)
(* to the merger file header *)
let merger_begin hnd d hdr_string =
  hnd.m_delta := d;
  Mutex.lock hnd.m_user_said_begin_lock;
  hnd.m_user_said_begin := true;
  hnd.m_hdr_string := hdr_string;
  Condition.broadcast hnd.m_user_said_begin_cond;
  Mutex.unlock hnd.m_user_said_begin_lock;
  debug_print debug_VER "merger_begin(): signalled merger_thread to begin";;

(* Merger thread *)
let merger_thread hnd =
  debug_print debug_FUN "merger_thread() started";
  (* Timestamp of the last message emitted *)
  let last_msg_time = ref None in
  (* Sequence number of merged output messages *)
  let last_msg_seq = ref 0 in

  (* Write merge file header *)
  let _ = writeMergeHeader hnd.m_outch in

  (* Wait until we can start -- i.e. that the caller has signalled *)
  (* that the merger can start by a call to merger_begin() and that *)
  (* all of the logs registered with the merger have had their headers *)
  (* written to the final merge output *)

  debug_print debug_VER "  merger_thread(): waiting to start";

  (* Wait for signal from merger_begin () *)
  Mutex.lock hnd.m_user_said_begin_lock;
  while not !(hnd.m_user_said_begin) do
      Condition.wait hnd.m_user_said_begin_cond hnd.m_user_said_begin_lock
  done;
  Mutex.unlock hnd.m_user_said_begin_lock;

  debug_print debug_VER "  merger_thread(): signalled by user to begin";

  (* Wait until all logs have had their headers written out to the merge output *)
  (* We use a timed_wait here in order not to block forever -- this is useful   *)
  (* for things like libd which don't produce any messages (or headers) until   *)
  (* after the first call is made (and hence ns_init() gets called).            *)
  Mutex.lock hnd.m_number_registered_cbs_lock;
  (try
     while !(hnd.m_thread_number_cbs_posthdr) <> !(hnd.m_number_registered_cbs) do
       condition_rel_timedwait
         hnd.m_thread_try_start
         hnd.m_number_registered_cbs_lock
         no_action_delay
     done
   with
    Unix_error(ETIMEDOUT,_,_) ->
      debug_print debug_OFF "## WARNING: merger thread started before all the headers were read");
  Mutex.unlock hnd.m_number_registered_cbs_lock;

  (* Write out custom header string *)
  writeCustomHeader hnd.m_outch !(hnd.m_hdr_string);
  (* Write BEGIN line after all of the headers*)
  writeMergeHeaderFooter hnd.m_outch;
  debug_print debug_VER "  merger_thread(): has started...";

  (* Have to flush the channel here just in case none of the tools ever produce *)
  (* any output (in which case the custom header doesn't get written otherwise) *)
  Pervasives.flush hnd.m_outch;

  (* If handle is no longer valid and all queues are empty then *)
  (* the thread can terminate. This will always happen in a finite *)
  (* amount of time as the destruction of the merger handle deregisters *)
  (* all callbacks sending FINISH messages to the end of each queue *)
  let thread_done () =
    if !(hnd.m_valid) then false
    else
      (* Check that all the queues are empty *)
      let finish_check x =
	Mutex.lock x.q_lock;
	if queue_isempty x.queue then
	  (Mutex.unlock x.q_lock;
	  true)
	else
	  let (m,_) = Queue.peek x.queue in
	  Mutex.unlock x.q_lock;
	  match m with
	    FINISH -> true
	  | _ -> false in
      let fold_function b x = b && (finish_check x) in
      List.fold_left fold_function true !(hnd.m_in_list)
  in

  let first_msg = ref true in
  while not (thread_done ()) do
    debug_print debug_VER "  merger_thread(): restarting merger loop";

    (* Get the current time of day *)
    let currtime = getdecenttimeofday () in

    (* Create a list of potential minimal messages *)
    (* (from the heads of the non-empty queues) *)
    (* and a list of empty queues *)
    let (msg_list, emptyq_list) =
      let rec loop l msgs emptyqs =
	debug_print debug_VER "  merger_thread(): getting potential minimal messages";
	match l with
	  [] -> msgs,emptyqs
	| (x::xs) ->
	    Mutex.lock x.q_lock;
	    if queue_isempty x.queue then
	      (Mutex.unlock x.q_lock;
	       loop xs msgs ((x.q_lock, x.queue)::emptyqs))
	    else
	      match Queue.peek x.queue with
		(FINISH, time) ->
		  Mutex.unlock x.q_lock;
		  loop xs msgs emptyqs
	      |	(MESSAGE(msg), time) ->
		  Mutex.unlock x.q_lock;
		  loop xs ((msg, time, x.identifier)::msgs) emptyqs
      in loop !(hnd.m_in_list) [] []
    in

    (* If msg_list is empty then wait on new data and loop *)
    if(msg_list = []) then
      (debug_print debug_VER "  merger_thread(): msg_list empty, waiting for more data";
       debug_print debug_MUT "  merger_thread(1): attempt m_new_data_mutex";
       Mutex.lock hnd.m_new_data_mutex;
       debug_print debug_MUT "  merger_thread(1): got m_new_data_mutex";
       while not !(hnd.m_new_data) do
	 Condition.wait hnd.m_new_data_cond hnd.m_new_data_mutex
       done;
       hnd.m_new_data := false;
       debug_print debug_MUT "  merger_thread(1): release m_new_data_mutex";
       Mutex.unlock hnd.m_new_data_mutex) (* back to start of emit_loop from here! *)

    else  (* we have some messages so continue *)
      (* From the list of potential minimal messages pick the actual minimum (minE) *)
      (debug_print debug_VER "  merger_thread(): about to find the actual minimum";
       let (minE, minEt, minId) = findMinimum msg_list in    (* message and arrival time *)

       (* Check that currentTime - arrival(minE) > delta *)
       let diff = currtime -. minEt in
       let emit =
	 if (diff <=. !(hnd.m_delta)) then
	   (* Wait until delta has expired or a new message has arrived. *)
           (* If timer expires then continue and emit else we may have a *)
           (* new minE so loop *)
           (* ###TODO: FOR EFFICIENCY here check if the new message is on an empty queue *)
           let delay =
	     let t_delay = !(hnd.m_delta) -. diff in
	     float_div (Int64.to_float t_delay) 1000000.0 in
           debug_print debug_MUT "  merger_thread(2): attempt m_new_data_mutex";
           Mutex.lock hnd.m_new_data_mutex;
           debug_print debug_MUT "  merger_thread(2): got m_new_data_mutex";
           let something_arrived =
             try
               while not !(hnd.m_new_data) do
                 condition_rel_timedwait
                   hnd.m_new_data_cond
                   hnd.m_new_data_mutex
                   delay
               done;
               true (* new data arrived *)
             with
               Unix_error(ETIMEDOUT,_,_) ->
                 false (* no new data arrived *) in
           debug_print debug_MUT "  merger_thread(2): release m_new_data_mutex";
           Mutex.unlock hnd.m_new_data_mutex;
	   not something_arrived  (* emit only if no new data arrived in the meantime *)
	 else true
       in

       if emit then
         (* Remove the emitted message from its queue *)
	 (let remove success x =
	   Mutex.lock x.q_lock;
	   if queue_isempty x.queue then
	     (Mutex.unlock x.q_lock;
	      success)
	   else
	     let (m,t) = Queue.peek x.queue in
	     if (m,t) = (MESSAGE(minE), minEt) then
	       (debug_print debug_VER "  merger_thread(): removing emitted message from its queue";
		let _ = Queue.take x.queue in
		Mutex.unlock x.q_lock;
		true
	       )
	     else
	       (Mutex.unlock x.q_lock;
		success) in
	 if not (List.fold_left remove false !(hnd.m_in_list)) then
	   raise (Merger_fatal("Couldn't find minimum entry to remove from queue"))
	 else ();

         (* Emit the message *)
         (* Generate an epsilon transition if time has elapsed since last emit *)
	 let eps =
	   match minE with
	     PARSE_RETURN(Some(TIMECOMMENT(time,_)),_,_) ->
	       (match (!last_msg_time) with
		 None -> last_msg_time := Some(time); ""
	       | Some(t) ->
		   last_msg_time := Some(time);
		   generateEpsilonTransition t time)
	   | PARSE_RETURN(None,_,_) -> ""
	 in
         (* Output epsilon transition to output channel *)
	 if (String.length eps) >0 then
	   (let scomment = sprintf "\n(* Merge Index: %d *)\n" (!last_msg_seq) in
	   last_msg_seq := !last_msg_seq + 1;
	   output_string hnd.m_outch (scomment^eps)) (* no need to flush *)
	 else ();
	 (* Print basetime if first message *)
	 if !first_msg then
	   (first_msg := false;
	    let timestr =
	      match minE with
		PARSE_RETURN(Some(TIMECOMMENT(time,_)),_,_) ->
		  sprintf "(* BASETIME *)\nabstime %s\n(* EMITESAB *)\n\n"
		    (string_of_time time)
	      |	_ -> "" in
	    output_string hnd.m_outch timestr)
	 else ();
	 (* Render message to output channel *)
	 let scomment = sprintf "Merge Index: %d" (!last_msg_seq) in
	 last_msg_seq := !last_msg_seq + 1;
(*match minId with None -> () | (Some x) -> print_string x; omfg what a hack *)
   render_nsparsemsg_to_chan hnd.m_outch minE (uint 0) scomment minId;
	 Pervasives.flush hnd.m_outch)
       else () )
  done;
  debug_print debug_FUN "merger_thread() returned normally";;


(* merger_create out_channel output_mode = merger_handle *)
(* Create a new merger thread outputting to out_channel *)
let merger_create outch mode =
  (* Create merger handle *)
  debug_print debug_FUN "merger_create() called";
  let hnd =  {
    m_valid = ref true;
    m_output_mode = mode;
    m_outch = outch;
    m_tid = ref None;
    m_delta = ref (uint 0);   (* updated by merger_begin *)
    m_hdr_string = ref "";    (* updated by merger_begin *)
    m_in_list = ref [];
    m_number_registered_cbs = ref 0;
    m_number_registered_cbs_lock = Mutex.create ();
    m_thread_try_start = Condition.create ();
    m_thread_number_cbs_posthdr = ref 0;
    m_user_said_begin_cond = Condition.create ();
    m_user_said_begin_lock = Mutex.create ();
    m_user_said_begin = ref false;
    m_new_data_mutex = Mutex.create ();
    m_new_data_cond = Condition.create();
    m_new_data = ref false
  } in
  (*### TODO: stuff depending on output mode *)
  let _ =
    match mode with
      RAW -> ()
    | HOLDEF -> () in
  (* Create merger thread *)
  let tid = Thread.create merger_thread hnd in
  hnd.m_tid := Some(tid);   (* needed to do join on merger_destroy *)
  debug_print debug_FUN "merger_create() returned successfully";
  hnd;;


(* merger_register_log handle log_handle out_channel_option = unit *)
(* Register a specific log with the merger referenced by handle *)
(* and  with optional echo to out_channel out_channel_option *)
let merger_register_named_log handle logch echoch_opt id_opt =
  if not !(handle.m_valid) then
    raise(Merger_invalid_handle("merger_register_log", handle))
  else
    (* Update merger state with registered callback *)
    let merge_channel_state =
      { logch = logch;
	q_lock = Mutex.create ();
	queue = Queue.create ();
	cbhnd = ref (None);
	offset = ref (uint 0);
  identifier = id_opt
      } in

    (* Add merger queue to the handles list *)
    (* NB: this is deliberately here. You don't want to register the callback *)
    (* until the merger is listening *)
    Mutex.lock handle.m_number_registered_cbs_lock;
    handle.m_number_registered_cbs := !(handle.m_number_registered_cbs) + 1;
    handle.m_in_list := merge_channel_state::(!(handle.m_in_list));
    Mutex.unlock handle.m_number_registered_cbs_lock;

    (* Create callback handling function *)
    let callback_function msg =
      debug_print debug_VER "merger_callback_function() called";
      let local_msg_time = getdecenttimeofday () in
      debug_print debug_VER "  merger_callback_function(): got time of day";
      match msg with
	STREAM_EOF ->
	  (* Add finish entry to merger's queue *)
	  debug_print debug_VER "  merger_callback_function(): got STREAM_EOF";
	  debug_print debug_MUT "  merger_callback_function(): waiting for mutexes (EOF)";
	  Mutex.lock merge_channel_state.q_lock;
	  debug_print debug_MUT "  merger_callback_function(3): waiting for last mutex (EOF)";
	  Mutex.lock handle.m_new_data_mutex;
	  debug_print debug_MUT "  merger_callback_function(3): obtained mutexes (EOF)";
	  let _ = Queue.add (FINISH, local_msg_time) merge_channel_state.queue in
	  handle.m_new_data := true;
	  Condition.broadcast handle.m_new_data_cond;
	  debug_print debug_MUT "  merger_callback_function(3): releasing mutex";
	  Mutex.unlock handle.m_new_data_mutex;
	  Mutex.unlock merge_channel_state.q_lock;
	  debug_print debug_MUT "  merger_callback_function(): released mutex"
      |	STREAM_HEADER(str) ->
	  (* Write header string to merger output *)
	  debug_print debug_VER "  merger_callback_function(): got STREAM_HEADER";
	  (* Headers output bypassing merger thread -- it's easier this way *)
          let _ = output_string_and_flush handle.m_outch str in

	  (* Find the start of the NTP offset= entry *)
	  let position =
	    let rec find_offset start =
	      let p = try String.index_from str start 'o' with
		Not_found -> 0
	      in
	      if (p = 0) then p
	      else if ((String.sub str p 7) = "offset=") then
	        p+7
	      else
		find_offset (p+1)
	    in find_offset 0
	  in

	  (* Parse the NTP header offset value *)
	  if(position != 0) then
	    (let dot_index = String.index_from str position '.' in
	    (* Test if negative required: if msecs=0 then negative zero isn't negative *)
	    let is_negative = (String.get str position = '-') in
	    let msecs_offset = Int64.of_string (String.sub str position (dot_index-position)) in
	    let usecs_offset = Int64.of_string (String.sub str (dot_index+1) 3) in
	    let abs_offset = ((Int64.abs msecs_offset) *. (uint 1000)) +. usecs_offset in
	    let offset = if is_negative then Int64.neg abs_offset else abs_offset in
	    output_string_and_flush handle.m_outch ("(* Applying NTP offset: "^(Int64.to_string offset)^"us *)\n");
	    output_string_and_flush handle.m_outch "(* -------------------------------------------------------------------------- *)\n\n";
            (* Place the ntp offset value in the handle *)
	    merge_channel_state.offset := offset)
	  else ();


          (* Write header string to optional echo channel *)
	  (match echoch_opt with
	    None -> ()
	  | Some(ch) ->
	      output_string_and_flush ch (str^"(* BEGIN *)\n"));

	  debug_print debug_MUT "  merger_callback_function(): waiting for m_number_registered_cbs mutex";
	  Mutex.lock handle.m_number_registered_cbs_lock;
	  debug_print debug_MUT "  merger_callback_function(): obtained m_number_registered_cbs mutex";
	  handle.m_thread_number_cbs_posthdr := !(handle.m_thread_number_cbs_posthdr) + 1;
	  Condition.broadcast handle.m_thread_try_start;
	  Mutex.unlock handle.m_number_registered_cbs_lock;
	  debug_print debug_MUT "  merger_callback_function(): release m_number_registered_cbs mutex"
      |	STREAM_PARSEDATA(msg) ->
	  debug_print debug_VER "  merger_callback_function(): got STREAM_PARSEDATA";
	  (* Write msg to optional echo channel *)
	  let _ =
	    (match echoch_opt with
	      None -> ()
	    | Some(ch) ->
		(render_nsparsemsg_to_chan ch msg (uint_zero) "" None);
    (* nb. the 'None' here may ultimately turn out not to be the desired behaviour - AB*)
		Pervasives.flush ch ) in

	  (* Apply adjustments to the message timestamp *)
	  let time_corrected_msg =
	    match msg with
	      PARSE_RETURN(ts,c,m) ->
		let new_ts =
		  match ts with
		    None ->
		      raise(Merger_fatal("Got a msg with no timestamp in the merger callback function"))
		  | Some(TIMECOMMENT(time,str)) ->
		      TIMECOMMENT(time +. !(merge_channel_state.offset), str) in
		MESSAGE(PARSE_RETURN(Some new_ts, c, m)) in

	  (* Get the merger's queue mutex *)
	  debug_print debug_MUT "  merger_callback_function(): waiting for mutexes (PARSEDATA)";
	  Mutex.lock merge_channel_state.q_lock;
	  debug_print debug_MUT "  merger_callback_function(4): waiting for last mutex (PARSEDATA)";
	  Mutex.lock handle.m_new_data_mutex;
	  debug_print debug_MUT "  merger_callback_function(4): obtained mutexes";

	  (* Add the message to the queue *)
	  let _ = Queue.add (time_corrected_msg, local_msg_time) merge_channel_state.queue in
	  (* Signal new input *)
	  handle.m_new_data := true;
	  Condition.broadcast handle.m_new_data_cond;

	  (* Unlock the mutex *)
	  debug_print debug_MUT "  merger_callback_function(4): releasing mutexes";
	  Mutex.unlock handle.m_new_data_mutex;
	  Mutex.unlock merge_channel_state.q_lock;
	  debug_print debug_MUT "  merger_callback_function(): released mutex"
    in
    (* Register callback *)
    let cbhnd = log_register_callback logch callback_function in
    let _ = merge_channel_state.cbhnd := Some(cbhnd) in
    ();;

let merger_register_log handle logch echoch_opt = merger_register_named_log handle logch echoch_opt None;;

(* merger_deregister_log handle log_handle = unit *)
(* Unregister log_handle from the merger referenced by handle *)
let merger_deregister_log handle logch =
  if not !(handle.m_valid) then
    raise(Merger_invalid_handle("merger_register_log", handle))
  else
    (* Search the merger's input list for this logch and deregister it *)
    let find_and_deregister x =
      if (x.logch.lock == logch.lock) then
	match !(x.cbhnd) with
	  None -> ()
	| Some(cb) -> log_deregister_callback cb; x.cbhnd := None
    in
    List.iter find_and_deregister !(handle.m_in_list);;

(* merger_destroy handle = unit *)
(* Destroy the merger referenced by handle. This unregisters all *)
(* the callbacks registered with the referenced merger first to ensure *)
(* things terminate nicely *)
let merger_destroy handle =
  debug_print debug_FUN "merger_destroy() called";
  if not !(handle.m_valid) then
    raise(Merger_invalid_handle("merger_destroy_handle", handle))
  else
    (* Deregister all callbacks *)
    let deregister x =
      match !(x.cbhnd) with
	None -> ()
      | Some(cb) -> log_deregister_callback cb; x.cbhnd := None
    in
    List.iter deregister !(handle.m_in_list);

    (* Signal merger thread to die *)
    (* We don't want to empty the list of queues (or the queues *)
    (* themselves) as we may wish the merge to finish what it was *)
    (* doing first! *)
    handle.m_valid := false;
    (* In case the merge thread is blocked signal it to wake up for new *)
    (* data and then wait for it to die before returning *)
    debug_print debug_MUT "  merger_destroy(5): attempt m_new_data_mutex";
    Mutex.lock handle.m_new_data_mutex;
    debug_print debug_MUT "  merger_destroy(5): got m_new_data_mutex";
    handle.m_new_data := true;
    Condition.broadcast handle.m_new_data_cond;
    debug_print debug_MUT "  merger_destroy(5): release m_new_data_mutex";
    Mutex.unlock handle.m_new_data_mutex;
    (match !(handle.m_tid) with
      None -> ()
    | Some(t) -> Thread.join t);
    debug_print debug_FUN "merger_destroy() returned successfully";;






(* -------------------------------------------------------------------- *)
(*                              Libd                                    *)
(* -------------------------------------------------------------------- *)

type libd_handle = {
    (* Handle valid? *)
    valid : bool ref;
    (* Libd parameters *)
    exec : exec_params;
    cmdch : sock_type;
    logch : log_handle;
    pid : int;
    pipei : Unix.file_descr;
    pipeo : Unix.file_descr;
    redirect : Unix.file_descr;
    tid : Thread.t option ref;
    cmdsd : Unix.file_descr;
    cmdlb : Lexing.lexbuf;
    remote_pid : int;
    (* Libd thread mgmt info -- WARNING: *)
    (* Libd shared memory. You MUST obtain the mutex libd_mgmt_mutex *)
    (* before accessing libd_outstanding_calls_counter or waiting    *)
    (* on or signalling the condition libd_no_outstanding_calls.     *)
    libd_outstanding_calls_counter : int ref;
    libd_no_outstanding_calls : Condition.t;
    libd_some_outstanding_calls : Condition.t;
    libd_mgmt_mutex : Mutex.t;

    (* -- DEBUGGING INFORMATION -- *)
    tcpdebug : bool;
    envlist : (string * string) list;
    arglist : string list;
    cmdin : in_channel
    } ;;

exception Libd_hard_fail of string;;
exception Libd_invalid_handle of string * libd_handle;;
exception Libd_kill_failed of string * int * exec_params;;

let libd_mgmt_thread hnd =
  debug_print debug_FUN "libd_mgmt_thread() started";
  let parseenv = Threadparsing.create_parse_env () in
  let terminate = ref false in
  let _ =
    while !(hnd.valid) && !terminate do
      try
	(* If there are outstanding calls *)
	if(!(hnd.libd_outstanding_calls_counter) > 0) then
	  (let result = Parser.main parseenv Lexer.token hnd.cmdlb in
	  debug_print debug_VER "  libd_mgmt_thread(): have eaten an asynchronous call";
	  match result with
	    PARSE_RETURN(_,_,r) ->
	      match r with
		LIBRETURN(_,x) ->
		  (* We have the Lh_return so reduce the waiting count and *)
		  (* if there are no more outstanding returns then signal  *)
		  (* any waiting synchronous calls *)
		  debug_print debug_MUT "  libd_mgmt_thread(): waiting for mutex";
		  let _ = Mutex.lock hnd.libd_mgmt_mutex in
		  debug_print debug_MUT "  libd_mgmt_thread(): obtained mutex";
		  let _ = hnd.libd_outstanding_calls_counter := !(hnd.libd_outstanding_calls_counter) - 1 in
		  let _ = if (!(hnd.libd_outstanding_calls_counter) = 0) then
		    Condition.broadcast hnd.libd_no_outstanding_calls in
		  let _ =  Mutex.unlock hnd.libd_mgmt_mutex in
		  debug_print debug_MUT "  libd_mgmt_thread(): released mutex"
	      | _ ->
		  raise(Libd_hard_fail("libd_mgmt_thread: got a Parser message that was NOT a libreturn"))
	  )
	else
	  (Mutex.lock hnd.libd_mgmt_mutex;
	   Condition.wait hnd.libd_some_outstanding_calls hnd.libd_mgmt_mutex;
	   Mutex.unlock hnd.libd_mgmt_mutex)
      with Lexer.Eof -> debug_print debug_MSG "  libd_mgmt_thread(): died with Lexer.Eof";
	   terminate := true
    done in
  debug_print debug_FUN "libd_mgmt_thread() completed successfully";;


(* libd_create exec_params cmd_channel log_channel tcp_debug = handle *)
(* Create a new libd daemon *)
let libd_create execparams cmdch logch tcpdebug priv =
  let _ = debug_print debug_FUN "libd_create() called" in
  (* Do some sanity checking first then construct *)
  (* cmd_channel string *)
  let arglist =
    (match cmdch with
      TCP(ip,port) -> "TCP"::(render_ip_dots(ip))::(Int64.to_string(port))::[]
    | UNIX(name) ->
	let s1 = "UNIX"::name::[] in
	(match execparams with
	  LOCAL(_) -> s1
	| _ -> raise (Libd_hard_fail("Can NOT use a UNIX DOMAIN command socket \
                                      to communicate with a remote host!")))) in
  let arglist = if priv then "-priv"::arglist else arglist in
  (* Create list of environment variables *)
  let (logip, logport) = get_log_name logch in
  let e1 = ("NS_ADDR", logip) in
  let e2 = ("NS_PORT", logport) in
  let debug = if tcpdebug then "1" else "0" in
  let e3 = ("NS_DEBUG", debug) in
  let envlist = e1::e2::e3::[] in
  (* Go away and fork process *)
  let (pid,pipei,pipeo,redirect) = do_exec execparams EXEC_LIBD arglist envlist in
  (*let _ = close pipeo in
  let _ = close pipei in*)
  (* Now try and connect to libd on the cmd_channel *)
  let sd =
    match cmdch with
      TCP(ip,port) -> ThreadUnix.socket PF_INET SOCK_STREAM 0
    | UNIX(name) -> ThreadUnix.socket PF_UNIX SOCK_STREAM 0 in
  let _ = setsockopt sd SO_REUSEADDR true in
  let _ =
    match cmdch with
      TCP(ip,port) ->
	let iaddr = inet_addr_of_string(render_ip_dots(ip)) in
	let iport = Int64.to_int port in
	try_connect sd (ADDR_INET(iaddr, iport))
    | UNIX(name) ->
	try_connect sd (ADDR_UNIX(name)) in
  (* Create in_channel and lexing buffer *)
  let ch = Unix.in_channel_of_descr sd in
  let temp = input_line ch in
  let remote_pid = int_of_string temp in
  let lb = Lexing.from_channel ch in
  let hnd = {
    valid = ref true;
    exec = execparams;
    cmdch = cmdch;
    logch = logch;
    tcpdebug = tcpdebug;
    envlist = envlist;
    arglist = arglist;
    pid = pid;
    pipei = pipei;
    pipeo = pipeo;
    redirect = redirect;
    tid = ref None;
    cmdsd = sd;
    cmdin = ch;
    cmdlb = lb;
    remote_pid = remote_pid;
    libd_outstanding_calls_counter = ref 0;
    libd_no_outstanding_calls = Condition.create ();
    libd_some_outstanding_calls = Condition.create ();
    libd_mgmt_mutex = Mutex.create ()
  } in
  (* Create the libd management thread (for eating up async libd returns *)
  let ttid = Thread.create libd_mgmt_thread hnd in
  let _ = hnd.tid := Some ttid in
  let _ = Thread.delay 2.00 in    (* delay to give everything time to start *)
  let _ = debug_print debug_FUN "libd_create() returned successfully" in
  hnd;;

(* libd_destroy handle = unit *)
(* Destroy the referenced libd daemon *)
let libd_destroy handle =
  debug_print debug_FUN "libd_destroy() called";
  close handle.cmdsd;
  if not !(handle.valid) then
    raise(Libd_invalid_handle("libd_destroy", handle))
  else
    if (do_kill handle.exec handle.pipei handle.pipeo handle.redirect handle.pid) then
      debug_print debug_VER "  libd_destroy(): killed libd process successfully"
    else
      raise(Libd_kill_failed("Failed to kill remote process", handle.pid, handle.exec));
  selector_wait_until_really_finished handle.logch;
  debug_print debug_FUN "libd_destroy() returned successfully";
  handle.valid := false;;

(* libd_getpid handle = uint *)
(* Get the remote-end pid of the remote libd process *)
let libd_getpid handle =
  debug_print debug_FUN "libd_getpid() called";
  if not !(handle.valid) then
    raise(Libd_invalid_handle("libd_getpid", handle))
  else
    (debug_print debug_FUN "libd_getpid() returned successfully";
    uint handle.remote_pid);;

(* libd_call handle libcall = libreturn *)
(* Make a LIB call via the referenced libd daemon and wait for the return *)
let libd_call handle libcall =
  let _ = if not !(handle.valid) then
    raise(Libd_invalid_handle("libd_call", handle)) in
  (* Check that there are no outstanding async calls. If there are *)
  (* then wait to be signalled that there are none. THE WHILE LOOP IS IMPORTANT! *)
  let _ =
    let _ = Mutex.lock handle.libd_mgmt_mutex in
    while !(handle.libd_outstanding_calls_counter) > 0 do
	Condition.wait handle.libd_no_outstanding_calls handle.libd_mgmt_mutex
    done in
   let _ =  Mutex.unlock handle.libd_mgmt_mutex in
  (* Make the call *)
  let call_str = lib_call_render (snd(libcall)) (fst(libcall)) in
  let _ = Sock.write handle.cmdsd call_str in
  (* Wait for the results *)
  let parseenv = Threadparsing.create_parse_env () in
  let result = (try Parser.main parseenv Lexer.token handle.cmdlb
               with Lexer.Eof -> raise(Libd_hard_fail("libd_call: Lexer.Eof exception. \nCall string: " ^ call_str ^ "  \nLexbuf: " ^ (handle.cmdlb.lex_buffer)))) in
  let lib_return = match result with
    PARSE_RETURN(_,_,r) ->
      (match r with
	LIBRETURN(x) -> x
      |	_ ->
	  raise(Libd_hard_fail("libd_call: got a Parser message that was NOT a libreturn"))
      ) in
  lib_return;;

(* libd_call handle  libcall = unit *)
(* Make a LIB call via the referenced libd daemon and don't wait *)
let libd_call_async handle libcall =
  let _ = if not !(handle.valid) then
    raise(Libd_invalid_handle("libd_call_async", handle)) in
  (* Increment the number of outstanding async calls *)
  let _ = Mutex.lock handle.libd_mgmt_mutex in
  let _ = handle.libd_outstanding_calls_counter := !(handle.libd_outstanding_calls_counter) + 1 in
  let _ = Condition.broadcast handle.libd_some_outstanding_calls in
  let _ = Mutex.unlock handle.libd_mgmt_mutex in
  (* Make the asynchronous call *)
  let call_str = lib_call_render (snd(libcall)) (fst(libcall)) in
  Sock.write handle.cmdsd call_str;;
  (* And, we're done I hope! The libd_mgmt_thread is now *)
  (* responsible for binning any Lh_returns once we signal it *)






(* -------------------------------------------------------------------- *)
(*                              Injector                                *)
(* -------------------------------------------------------------------- *)

type injector_handle = {
    (* Handle valid? *)
    valid : bool ref;
    exec : exec_params;
    (* Process identifier *)
    pid : int;
    pipei : file_descr;
    pipeo : file_descr;
    redirect : file_descr;
    (* Command socket *)
    cmdsd : file_descr;

    (* -- DEBUGGING INFORMATION -- *)
    (* Command channel passed to creat callback list removing the callback *)
    (* associated with the handle we hold *)
    cmdch : sock_type;
    (* Command parameters passed to do_exec *)
    arglist : string list;
  } ;;

exception Injector_hard_fail of string;;
exception Injector_invalid_handle of string * injector_handle;;
exception Injector_kill_failed of string * int * exec_params;;

(* injector_create: execparams cmd_channel = handle *)
(* Create a new injector daemon *)
let injector_create execparams cmdch =
  (* Do some sanity checking then construct *)
  (* cmd_channel string *)
  let arglist =
    match cmdch with
      TCP(ip,port) -> "TCP"::(render_ip_dots(ip))::(Int64.to_string(port))::[]
    | UNIX(name) ->
	let s1 = "UNIX"::name::[] in
	(match execparams with
	  LOCAL(_) -> s1
	| _ -> raise (Injector_hard_fail("Can NOT use a UNIX DOMAIN command socket \
                                          to communicate with a remote host!"))) in
  (* Go away and fork process *)
  let (pid,pipei,pipeo,redirect) = do_exec execparams EXEC_INJECTOR arglist [] in
  (* Now try and connect to injector on the cmd_channel *)
  let sd =
    match cmdch with
      TCP(ip,port) -> ThreadUnix.socket PF_INET SOCK_STREAM 0
    | UNIX(name) -> ThreadUnix.socket PF_UNIX SOCK_STREAM 0 in
  let _ = setsockopt sd SO_REUSEADDR true in
  let _ =
    match cmdch with
      TCP(ip,port) ->
	let iaddr = inet_addr_of_string(render_ip_dots(ip)) in
	let iport = Int64.to_int port in
	try_connect sd (ADDR_INET(iaddr, iport))
    | UNIX(name) ->
	try_connect sd (ADDR_UNIX(name)) in
  {
   valid = ref true;
   exec = execparams;
   cmdch = cmdch;
   arglist = arglist;
   pid = pid;
   pipei = pipei;
   pipeo = pipeo;
   redirect = redirect;
   cmdsd = sd
 } ;;


(* injector_inject handle holdatagram = unit *)
(* Inject a HOL record datagram via the referenced daemon *)
let injector_inject handle holsndmsg =
  if not !(handle.valid) then
    raise(Injector_invalid_handle("injector_inject", handle))
  else
    (* Make the asynchronous call *)
    match holsndmsg with
      TCPMSG(segment) ->
	let s = render_tcp_inner segment SENDDGRAM in
	  Sock.write handle.cmdsd s
    | UDPMSG(dgram) ->
	let s = render_udp_inner  dgram SENDDGRAM in
	  Sock.write handle.cmdsd s
    | ICMPMSG(msg) ->
	let s = render_icmp_inner msg SENDDGRAM in
	  Sock.write handle.cmdsd s
;;


(* injector_destroy handle = unit *)
(* Destroy the referenced injector daemon *)
let injector_destroy handle =
  if not !(handle.valid) then
    raise(Injector_invalid_handle("injector_destroy", handle))
  else
    if (do_kill handle.exec handle.pipei handle.pipeo handle.redirect handle.pid) then
      debug_print debug_VER "  injector_destroy(): do_kill was successful"
    else
      raise(Injector_kill_failed("Failed to kill remote process",
				 handle.pid, handle.exec));
  close handle.cmdsd;
  handle.valid := false;;






(* -------------------------------------------------------------------- *)
(*                              Slurper                                 *)
(* -------------------------------------------------------------------- *)

type slurper_handle = {
    (* Handle valid? *)
    valid : bool ref;
    exec : exec_params;
    logch : log_handle;
    pid : int;
    pipei : Unix.file_descr;
    pipeo : Unix.file_descr;
    redirect : Unix.file_descr;

    (* -- DEBUGGING INFORMATION -- *)
    (* Original arguments to create *)
    iface : string;
    filter : string option;
    hostips : ip option;
  } ;;

type slurper_callback_handle = {
    (* Callback handle valid? *)
    validcb : bool ref;
    (* Associated slurper handle *)
    hnd : slurper_handle;
    (* Real callback handle *)
    realhnd : log_callback_handle;
  } ;;

exception Slurper_invalid_handle of string * slurper_handle;;
exception Slurper_kill_failed of string * int * exec_params;;
exception Slurper_invalid_callback_handle of string * slurper_callback_handle;;
exception Slurper_callback_handle_mismatch of string * slurper_handle * slurper_callback_handle;;

(* slurper_create execparams log_channel iface filter hostip = handle *)
(* Create a new slurper daemon *)
(*  iface is the interface to sniff on *)
(*  log_channel specifies the socket to output HOL labels to *)
(*  filter is an optional filter string *)
(*  hostip if set specifies the ip address of the sending host *)
let slurper_create execparams log_channel iface filter hostips =
  let _ = debug_print debug_FUN "slurper_create() called" in
  (* Create hostip address option *)
  let hostip =
    match hostips with
      None -> []
    | Some(ip) -> "-h"::(render_ip_dots ip)::[] in
  (* Build up most of the command line options *)
  let (logip,logport) = get_log_name log_channel in
  let connection_args =
    iface::"TCP"::(logip)::(logport)::[] in
  (* Enclose the filter string in double quotes if going to *)
  (* be passed to a remote shell via ssh *)
  let filter_args =
    match filter with
      None -> []
    | Some(f) -> (
	match execparams with
	  LOCAL(_) -> [f]
	| REMOTE(_,rsh,_) ->
	    match rsh with
	      SSH(_) -> ["\""^f^"\""]
	    | CUSTOM_RSH(_) -> [f]) in
  (* Build up the final arg list *)
  let args_list = hostip @ connection_args @ filter_args in
  (* Go away and fork process *)
  let (pid,pipei,pipeo,redirect) = do_exec execparams EXEC_SLURP args_list [] in
  let _ = debug_print debug_VER "  slurper_create(): waiting for log channel to connect" in
  let _ = selector_wait_until_connected log_channel in
  let _ = debug_print debug_VER "  slurper_create(): log channel connected" in
  let _ = debug_print debug_FUN "slurper_create() returned successfully" in
  {
   valid = ref true;
   exec = execparams;
   logch = log_channel;
   iface = iface;
   filter = filter;
   hostips = hostips;
   pid = pid;
   pipei = pipei;
   pipeo = pipeo;
   redirect = redirect;
 } ;;


(* slurper_register_callback handle callback = slurper_callback_handle *)
(* Register a new callback with log channel for the *)
(* slurper referenced by handle *)
let slurper_register_callback handle cb =
  if not !(handle.valid) then
    raise(Slurper_invalid_handle("slurper_register_callback", handle))
  else
    let callback_function msg =
      match msg with
	STREAM_EOF -> ()
      |	STREAM_HEADER(x) -> ()
      |	STREAM_PARSEDATA(PARSE_RETURN(t,s,data)) ->
	  (match data with
	    HOLSNDMSG(x) -> cb(x)
	  | HOLLOOPMSG(x) -> cb(x)
	  | HOLRCVMSG(x) -> cb(x)
	  | _ -> () ) in
    (* Add callback function to the callback list of the log_channel *)
    let log_cb_handle = log_register_callback handle.logch callback_function in
    { validcb = ref true; hnd = handle; realhnd = log_cb_handle };;


(* slurper_deregister_callback handle callback_handle = unit *)
(* Unregister the given callback *)
let slurper_deregister_callback handle cb_handle =
  if not !(handle.valid) then
    raise(Slurper_invalid_handle("slurper_deregister_callback", handle))
  else if not !(cb_handle.validcb) then
    raise(Slurper_invalid_callback_handle("slurper_deregister_callback", cb_handle))
  else if (cb_handle.hnd.valid != handle.valid) then
    raise(Slurper_callback_handle_mismatch("slurper_deregister_callback",
					  handle, cb_handle))
  else
    (* Rebuild the callback list removing the callback *)
    (* associated with the handle we hold *)
    let _ = log_deregister_callback cb_handle.realhnd in
    cb_handle.validcb := false;;


(* slurper_destroy handle = unit *)
(* Destroy the referenced slurper daemon *)
let slurper_destroy handle =
  let _ = debug_print debug_FUN "slurper_destroy() called" in
  if not !(handle.valid) then
    raise(Slurper_invalid_handle("slurper_destroy", handle))
  else
    if (do_kill handle.exec handle.pipei handle.pipeo handle.redirect handle.pid) then
      debug_print debug_VER "  slurper_destroy(): kill successful"
    else
      raise(Slurper_kill_failed("Failed to kill remote process",
				handle.pid, handle.exec));
    selector_wait_until_really_finished handle.logch;
    debug_print debug_FUN "slurper_destroy() returned successfully";
    handle.valid := false;;





(* -------------------------------------------------------------------- *)
(*                              Holtcpcb                                *)
(* -------------------------------------------------------------------- *)

type action_flag =
    AF_INPUT
  | AF_OUTPUT
  | AF_DROP
  | AF_USER;;

type holtcpcb_handle = {
    (* Handle valid? *)
    valid : bool ref;
    exec : exec_params;
    logch : log_handle;
    pid : int;
    pipei : file_descr;
    pipeo : file_descr;
    redirect : file_descr;

    (* -- DEBUGGING INFORMATION -- *)
    (* Action flag list passed to create *)
    act_flag_list : action_flag list;
  } ;;

type holtcpcb_callback_handle = {
    (* Callback handle valid? *)
    validcb : bool ref;
    (* Associated holtcpcb instance *)
    hnd : holtcpcb_handle;
    (* Real callback handle *)
    realhnd : log_callback_handle
  } ;;

exception Holtcpcb_invalid_action_mask of string * int;;
exception Holtcpcb_invalid_handle of string * holtcpcb_handle;;
exception Holtcpcb_kill_failed of string * int * exec_params;;
exception Holtcpcb_invalid_callback_handle of string * holtcpcb_callback_handle;;
exception Holtcpcb_callback_handle_mismatch of string * holtcpcb_handle * holtcpcb_callback_handle;;


(* Make numeric action_mask for holtcpcb command line *)
let holtcpcb_make_actionmask act_flag_list =
  let mask =
    let rec loop l =
      match l with
	[] -> 0
      | AF_INPUT::xs -> 1 + (loop xs)
      | AF_OUTPUT::xs -> 2 + (loop xs)
      |	AF_DROP::xs -> 4 + (loop xs)
      |	AF_USER::xs -> 8 + (loop xs)
    in loop act_flag_list
  in
  if mask > 15 then
    raise(Holtcpcb_invalid_action_mask("holtcpcb_make_actionmask", mask))
  else
    string_of_int mask;;


(* holtcpcb_create execparams log_channel action_mask = handle *)
(* Create a fresh holtcpcb daemon instance *)
let holtcpcb_create execparams logch act_flag_list =
  (* Create holtcpcb arguments *)
  let (logip,logport) = get_log_name logch in
  let argslist = "-n"::(holtcpcb_make_actionmask act_flag_list)::"-z"::logip::logport::[] in
  (* Make the process *)
  let (pid,pipei,pipeo,redirect) = do_exec execparams EXEC_HOLTCPCB argslist [] in
  let _ = debug_print debug_VER "  holtcpcb_create(): waiting for log channel to connect" in
  let _ = selector_wait_until_connected logch in
  let _ = debug_print debug_VER "  holtcpcb_create(): log channel connected" in
  {
   valid = ref true;
   exec = execparams;
   logch = logch;
   act_flag_list = act_flag_list;
   pid = pid;
   pipei = pipei;
   pipeo = pipeo;
   redirect = redirect
 } ;;


(* holtcpcb_register_callback handle callback = holtcpcb_callback_handle *)
(* Register a new callback function with the holtcpcb instances log *)
let holtcpcb_register_callback handle cb =
  if not !(handle.valid) then
    raise(Holtcpcb_invalid_handle("holtcpcb_register_callback", handle))
  else
    let callback_function msg =
      match msg with
	STREAM_EOF -> ()
      |	STREAM_HEADER(x) -> ()
      |	STREAM_PARSEDATA(PARSE_RETURN(t,s,data)) ->
	  (match data with
	    TCPTRACE(x) -> cb (x)
	  | _ -> ()) in
    (* Register the callback function *)
    let log_cb_handle = log_register_callback handle.logch callback_function in
    { validcb = ref true; hnd = handle; realhnd = log_cb_handle };;

(* holtcpcb_deregister_callback handle callback_handle = unit *)
(* Unregister a callback *)
let holtcpcb_deregister_callback handle cb_handle =
 if not !(handle.valid) then
    raise(Holtcpcb_invalid_handle("holtcpcb_deregister_callback", handle))
  else if not !(cb_handle.validcb) then
    raise(Holtcpcb_invalid_callback_handle("holtcpcb_deregister_callback", cb_handle))
  else if (cb_handle.hnd.valid != handle.valid) then
    raise(Holtcpcb_callback_handle_mismatch("holtcpcb_deregister_callback",
					  handle, cb_handle))
  else
    (* Remove the registered callback *)
    let _ = log_deregister_callback cb_handle.realhnd in
    cb_handle.validcb := false;;


(* holtcpcb_destroy handle = unit *)
(* Destroy the referenced holtcpcb daemon *)
let holtcpcb_destroy handle =
  if not !(handle.valid) then
    raise(Holtcpcb_invalid_handle("holtcpcb_destroy", handle))
  else
    if (do_kill handle.exec handle.pipei handle.pipeo handle.redirect handle.pid) then
      debug_print debug_VER "  holtcpcb_destroy(): kill successful"
    else
      raise(Holtcpcb_kill_failed("Failed to kill remote process",
				 handle.pid, handle.exec));
    selector_wait_until_really_finished handle.logch;
    handle.valid := false;;

type mirror_handle = {
  valid : bool ref;
  exec : exec_params;
  logch : log_handle;
  pid : int;
  pipei : file_descr;
  pipeo : file_descr;
  redirect : file_descr;
} ;;

exception Mirror_invalid_handle of string * mirror_handle;;
exception Mirror_kill_failed of string * int * exec_params;;

(* mirror_create execparams log_channel iface rewritelist opts = handle *)
(* Create a fresh magic mirror instance *)
let mirror_create execparams log_channel iface rewritelist opts =
  (* Build args list *)
  let logip, logport = get_log_name log_channel in
  let argslist = (iface::"TCP"::logip::logport::rewritelist) @
    (match opts with
      None -> []
    | Some x -> x) in
  (* Create process *)
  let (pid,pipei,pipeo,redirect) = do_exec execparams EXEC_MIRROR argslist [] in
  let _ = selector_wait_until_connected log_channel in
  {
    valid = ref true;
    exec = execparams;
    logch = log_channel;
    pid = pid;
    pipei = pipei;
    pipeo = pipeo;
    redirect = redirect;
  };;

(* mirror_destroy handle = unit *)
(* Destroy a magic mirror process *)
let mirror_destroy handle =
  if not !(handle.valid) then
    raise (Mirror_invalid_handle("mirror_destroy", handle))
  else
    if (do_kill handle.exec handle.pipei handle.pipeo handle.redirect handle.pid) then
      debug_print debug_VER "  mirror_destroy(): kill successful"
    else
      raise(Mirror_kill_failed("Failed to kill remote process",
         handle.pid, handle.exec));
    selector_wait_until_really_finished handle.logch;
    handle.valid := false;;

(* re-calibrate time on WinXP using TSCCal *)
let tsccal_start a e =
  let ep = {
    libd_path = "NOT REQUIRED";
    slurp_path = "NOT REQUIRED";
    injector_path = "NOT REQUIRED";
    holtcpcb_path = "NOT REQUIRED";
    mirror_path = "NOT REQUIRED"
  } in
  let args = [string_of_int a; string_of_int e] in
  let del = float_of_int ((a * e + 10000)/1000)  in
  let eps = (REMOTE("192.168.0.3",CUSTOM_RSH(60000),ep)) in
  let (pid,fdi,fdo,red) = do_exec eps EXEC_TSCAL args [] in
  let _ = delay del in
  let b = do_kill eps fdi fdo red pid in ()



(* -------------------------------------------------------------------- *)
(*                              THE END                                 *)
(* -------------------------------------------------------------------- *)
