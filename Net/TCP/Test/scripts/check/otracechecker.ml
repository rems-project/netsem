(* otracechecker -- Parallelising Trace Checker for the TCP semantics project *)

(* $Id: otracechecker.ml,v 1.42 2006/02/21 11:21:16 amgb2 Exp $ *)

(* This Ocaml implementation replaces a previous Perl version. *)

(* Idea for doing status.dat properly:

   In a loop, open a (preexisting; see mkfifo(1)) FIFO, write the
   current state to it, close it, and sleep for a second.  Note that
   the open should be forked off into a separate thread.

   In a loop, open a preexisting FIFO, write the current state to it,
   and then every time the state changes, write the new state to it.
   When a write dies with EPIPE, close the FIFO and terminate the
   thread.  Write a ^L between states.

   This provides two useful status.dat-like semantics: get the current
   state immediately, and watch the state evolve.

*)

let debug = ref true;;
let speedtestonly = ref false;;  (* experts only; do not use! *)
let proclimit = ref None;;  (* default max number of args per process is unbounded *)
let statusfile = ref None;;  (* file to write status reports to *)
let dynamicmode = ref false;;  (* use dynamic mode to communicate filenames to workers *)
let execdelay = ref 0;;  (* minimum time between execs (in seconds) *)
let restartdelay = ref (Some 7200);; (* minimum time to wait before attempting to restart a worker
                                        after a *machine or startup* crash, in seconds, or None if
                                        workers are not restarted after such crashes.  Note that
                                        we always restart after a trace crash. *)
let cmd = ref ["./trace_checker.exe"];;  (* default command to run *)
let abortcmd = ref None;;  (* command to run on an aborted job, if any *)
let hostspec : (string option * string option * int * string option) list ref =
  ref [(None,None,4,None)];;
  (* default vector of:
     rsh, host, number of processes, and optional inuse tester program
     (null hostname is local, null rsh name is default) *)
let inuseprefix = ["-i"];;  (* XXX prepended to inuse tester program name and placed after first element of cmd; better to have the whole chunk in the -j, but don't see how to parse easily *)
let infiles : string list ref = ref [];;  (* files to process *)


(* remote shell command: will be !rshcmd host command args *)
let rshcmd = ref ["/usr/bin/ssh"; "-ttx"; "-e"; "none"];;
(* ARGH: have a choice: -tt means process cleanup works, but normal EOF isn't passed on;
   -T means v.v. *)

(*
   -tt forces allocation of a pty; this has the side-effect that
   killing the ssh will kill the remote command immediately.

   -x disables X11 forwarding.

   -e none disables the escape char, making the session fully transparent

   Annoyingly, allocating a TTY also means that the current terminal
   settings are mucked up by SSH.  You can avoid this by redirecting
   stdin (e.g., < /dev/null), but you will get lots of warnings from
   tcgetattr().
*)

(*
   really, when using !RSH, it would be good to quote the arguments
   appropriately; ssh concatenates all its args (with spaces), and
   passes the lot to $SHELL -c as a single argument.
*)


(* "make pipes be piping hot", as Larry says *)
(* and let them be thread-safe, too *)
let fd_print_string fd s =
  let rec go s =
    let len = String.length s in
    let n = Unix.write fd s 0 len in
    if n < len then
      go (String.sub s n (len-n))
  in
  go s;;
let print_string s = fd_print_string Unix.stdout s;;
(* or be silent *)
(* let print_string s = ();; *)

let null : 'a list -> bool
    = function
        [] -> true
      | _  -> false

let rec copy : int -> 'a -> 'a list
    = fun n x ->
      if n <= 0 then [] else x :: copy (n-1) x

let timefmtz : Unix.tm -> string
    = fun tm ->
      Printf.sprintf "%04d-%02d-%02d T %02d:%02d:%02d Z (%s)"
        (tm.Unix.tm_year + 1900) (tm.Unix.tm_mon + 1) tm.Unix.tm_mday
        tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec
        [|"Sun";"Mon";"Tue";"Wed";"Thu";"Fri";"Sat"|].(tm.Unix.tm_wday);;

let timestamp : unit -> string
    = fun () ->
      timefmtz (Unix.gmtime(Unix.time ()));;

let mtimestamp : unit -> string
    = fun () ->
      let t = Unix.time () in
      Printf.sprintf "<%s> %0.0f"
        (timefmtz (Unix.gmtime t)) t;;

let showsettings : unit -> unit
    = fun () ->
      print_string "Current settings:\n";
      print_string (Sys.argv.(0)^" ");
      print_string (String.concat " " (List.map (fun (r,h,n,i) -> "-j"^(match r with None -> "" | Some r -> r^":")^(match h with None -> "" | Some h -> h^":")^string_of_int n^(match i with None -> "" | Some i -> "="^i)) !hostspec)^" ");
      print_string ("-m"^(match !proclimit with
        None -> "-1" | Some n -> string_of_int n)^" ");
      print_string (match !statusfile with None -> "" | Some f -> "-s"^f^" ");
      print_string (if !dynamicmode then "-y " else "");
      print_string ("-w"^string_of_int !execdelay^" ");
      print_string ("-d"^(match !restartdelay with None -> "-1" | Some n -> string_of_int n)^" ");
      print_string (match !abortcmd with None -> "" | Some xs -> "-z"^String.concat " " xs^" ; ");
      print_string ("-r"^String.concat " " !rshcmd^" ; ");
      print_string ("-c"^String.concat " " !cmd^" ; ");
      print_string ("<" ^ string_of_int (List.length !infiles)^" input files>\n");;

let usage : unit -> unit
    = fun () ->
      print_string ("\
Usage: "^Sys.argv.(0)^" <options> <file> ...
Options:
  -j[[<rsh>:]<hostname>:]<nproc>[=<inuse>]
                        Use <nproc> worker threads, locally or
                          on <hostname>, with <inuse> as the
                          inuse-detection program if any,
                          and using the specified rsh program
                          if given.  (extra specs add more workers)
  -m<n>                 Maximum number of files to process with
                          a single worker instance (-1 for unbounded)
  -c<cmd> <arg> ... \\;  Worker command to run
  -f<file>              Read files to process from <file>, separated
                          by whitespace.  Use - for stdin
  -s<file>              Write status reports to <file> rather than stdout
  -y                    Use dYnamic mode to communicate filenames
                          to workers (worker command must use the
                          simple accept protocol)
  -w<n>                 Minimum time between execs (in seconds)
  -d<n>                 Minimum time between fatal-crash restarts
                          (-1 to disable fatal-crash restarts)
  -z<cmd> <arg> ... \\;  Command to invoke for an aborted file;
                          passed filename and abort type
  -r<cmd> <arg> ... \\;  RSH/SSH command to run for remote workers
  <file>                Process <file>\n");;

let arg_fail s =
  usage ();
  showsettings ();
  print_string (s^"\n");
  exit 255;;

(*
   Give multiple -j arguments to specify multiple hosts as workers, e.g.:

   ptracechecker -j1 -jstriatum:2 -jcortex:4

   would give one process locally, two on striatum, and four on cortex.
*)

(* return a list of the whitespace-separated words in the file named (stdin if "-") *)
let readwords : string -> string list
    = fun filename ->
      let (ic,ic_close_thunk) =
        if filename = "-" then
          (stdin, fun _ -> ())
        else
          try (open_in filename, close_in) with Sys_error(s) -> arg_fail ("Couldn't open file list file "^filename^": "^s)
      in
      let buf = String.create 65536 in  (* chosen arbitrarily *)
      let rec loop s =
        let n = input ic buf 0 (String.length buf) in
        if n = 0 then
          s
        else
          loop (s^String.sub buf 0 n)
      in
      let ws = Str.split (Str.regexp "[ \t\n]+") (loop "") in
      ic_close_thunk ic;
      ws;;

let rec read_until_semi : string -> string list -> string list -> string list * string list
    = fun optname cs -> function
        [] -> arg_fail ("Option `"^optname^"': expected terminating `;'")
      | (x::xs) when x = ";" -> (List.rev cs, xs)
      | (x::xs) -> read_until_semi optname (x::cs) xs;;

(* process arguments into the relevant global variables *)
let opt_j_re = Str.regexp "\\(\\([^:=]*\\):\\)?\\(\\([^:=]*\\):\\)?\\([0-9]+\\)\\(=\\([^:=]*\\)\\)?";;
let do_args : unit -> unit
    = fun () ->
      let gothostspec = ref false in
      let rec go = function
          [] -> []
        | (x::xs) ->
            if String.length x > 0 && x.[0] = '-' then
              (* option handling *)
              let opt = String.sub x 0 (min (String.length x) 2) in
              if List.mem opt ["-j";"-m";"-f";"-s";"-y";"-c";"-r";"-w";"-d";"-z"] then
                if List.mem opt ["-j";"-m";"-f";"-s";"-c";"-r";"-w";"-d";"-z"] then  (* has argument *)
                  (let (arg,xs) =
                    if String.length x > 2 then
                      (String.sub x 2 (String.length x - 2),xs)
                    else match xs with
                      [] -> arg_fail ("Option `"^opt^"' requires an argument")
                    | (x::xs) -> (x,xs) in
                  match opt with
                    "-j" -> let spec =
                      if Str.string_match opt_j_re arg 0 then
                        let (r,h) =
                          try
                            let s1 = Str.matched_group 2 arg in
                            try
                              let s2 = Str.matched_group 4 arg in
                              (Some s1, Some s2)
                            with
                              Not_found ->
                                (None, Some s1)
                          with
                            Not_found ->
                              (None, None) in
                        let n = try int_of_string (Str.matched_group 5 arg) with Not_found | Failure(_) -> arg_fail ("Option `-j': expected integer after colon") in
                        let i = try Some (Str.matched_group 7 arg) with Not_found -> None in
                        (r,h,n,i)
                      else
                        arg_fail ("Option `-j': expected [[<rsh>:]<hostname>:]<nproc>[=<inuse>]")
                          (* NB: <rsh> must be a single command, with no arguments *)
                    in
                    (if !gothostspec then
                      hostspec := !hostspec @ [spec]
                    else
                      (hostspec := [spec]; gothostspec := true));
                    go xs
                  | "-m" -> proclimit := Some (int_of_string arg); go xs
                  | "-f" -> infiles := !infiles @ readwords arg; go xs
                  | "-s" -> statusfile := Some arg; go xs
                  | "-w" -> execdelay := int_of_string arg; go xs
                  | "-d" -> let n = int_of_string arg in
                    restartdelay := (if n = -1 then None else Some n); go xs
                  | "-z" -> let (cs,xs) = read_until_semi "-z" [arg] xs in
                    abortcmd := Some cs;
                    go xs
                  | "-c" -> let (cs,xs) = read_until_semi "-c" [arg] xs in
                    cmd := cs;
                    go xs
                  | "-r" -> let (cs,xs) = read_until_semi "-r" [arg] xs in
                    rshcmd := cs;
                    go xs
                  | _ ->
                      arg_fail ("Internal argument parsing error: "^opt))
                else  (* has no argument *)
                  (match opt with
                    "-y" -> dynamicmode := true; go xs
                  | _ ->
                      arg_fail ("Internal argument parsing error: "^opt))
              else
                arg_fail ("Option `"^opt^"' not recognised")
            else
              (x::xs)  (* done; return trailing args *)
      in
      infiles := !infiles @ go (List.tl (Array.to_list Sys.argv));
      if null !infiles then arg_fail ("At least one input file required");
      if !debug then showsettings ();;


(* worker descriptor data type *)

type workerstate =
    Init
  | WaitingUntilExecSafe
  | Starting
  | WaitingForWork
  | Processing of string
  | Completed of string
  | Killed of string option
  | Crashed of string option
  | CantStart
  | WaitingForRestart
  | Finishing
  | Finished
  | LocalCrash
  | WaitingForIdle

type workerstatus =
    { st : workerstate;
      asleep : bool;      (* is the worker currently SIGSTOPped? *)
    };;

type worker = {
    (* NB: no locks on refs, because there's only one writer for each, and
       we believe OCaml assignment is atomic *)
    tid : Thread.t option ref;
    idstr : string;
    host : string;
    cmd : string list;
    pid : int option ref;
    (* and various bits of status info, changes notified by cond *)
    schg : Condition.t;
    status : workerstatus ref;
    startctr : int ref;        (* number of times worker process (re)started *)
    cantstartctr : int ref;    (* number of times worker process crashed, not counting trace crashes *)
    jobctr : int ref;          (* number of jobs submitted *)
    jobcompletectr : int ref;  (* number of jobs completed successfully *)
    jobcrashctr : int ref;     (* number of jobs crashed *)
    jobkillctr : int ref;      (* number of jobs killed (because in-use) *)
  };;


let render_workerstatus : workerstatus -> (string * string option)
    = function ws ->
      let (st,arg) =
        match ws.st with
          Init                 -> ("Init"                , None  )
        | WaitingUntilExecSafe -> ("WaitingUntilExecSafe", None  )
        | Starting             -> ("Starting"            , None  )
        | WaitingForWork       -> ("WaitingForWork"      , None  )
        | Processing(s)        -> ("Processing"          , Some s)
        | Completed(s)         -> ("Completed"           , Some s)
        | Killed(so)           -> ("Killed"              , so    )
        | Crashed(so)          -> ("Crashed"             , so    )
        | CantStart            -> ("CantStart"           , None  )
        | WaitingForRestart    -> ("WaitingForRestart"   , None  )
        | Finishing            -> ("Finishing"           , None  )
        | Finished             -> ("Finished"            , None  )
        | LocalCrash           -> ("LocalCrash"          , None  )
        | WaitingForIdle       -> ("WaitingForIdle"      , None  )
      in
      ((st ^ if ws.asleep then "-" else ""), arg)

let render_worker : worker -> string
    = let rw ws =
        match render_workerstatus ws with
          (s1,None   ) -> s1
        | (s1,Some s2) -> s1 ^ " " ^ Filename.basename s2
      in
      fun w ->
      Printf.sprintf "[%3s] on %25s: %4d jobs, %4d cmpl %4d crsh %4d kill, %4d starts, %4d cantstarts.  %s."
        w.idstr w.host
        !(w.jobctr) !(w.jobcompletectr) !(w.jobcrashctr) !(w.jobkillctr)
        !(w.startctr) !(w.cantstartctr)
        (rw !(w.status))


(* generate the worker list (of command prefixes) from the hostspec *)
let gen_workerlist : Condition.t -> (string option * string option * int * string option) list -> worker list
    = fun cond hostspec ->
      let mkcmds (mr,mh,n,mi) =
        let cmd =
          let inuse = match mi with
            None   -> []
          | Some i -> inuseprefix @ [i]
          in
          let (h,rsh) = match (mh,mr) with
            (None  , _     ) -> ("localhost", [])
          | (Some h, None  ) -> (h,           !rshcmd @ [h])
          | (Some h, Some r) -> (h,           [r;h])
          in
          (h, rsh @ [List.hd !cmd] @ inuse @ List.tl !cmd)  (* XXX horrible hack! *)
        in
        copy n cmd
      in
      let workers = List.concat (List.map mkcmds hostspec) in
      if !debug then begin
        print_string ("Using a total of "^string_of_int (List.length workers)
                      ^" workers on "^string_of_int (List.length hostspec)
                      ^" hosts:\n");
        ignore (List.map (fun (_,c) -> print_string (String.concat " " c ^ "\n")) workers)
      end;
      (* now build the worker structures from the (host,command) pairs *)
      let go (n,xs) (h,c) =
        (n+1,{tid = ref None;
              idstr = string_of_int n;
              host = h;
              cmd = c;
              pid = ref None;
              schg = cond;
              status = ref { st = Init; asleep = false };
              startctr = ref 0;
              cantstartctr = ref 0;
              jobctr = ref 0;
              jobcompletectr = ref 0;
              jobcrashctr = ref 0;
              jobkillctr = ref 0;
            }::xs)
      in
      List.rev (snd (List.fold_left go (1,[]) workers));;

(* BEWARE: Ocaml 3.07's posix.c has this to say in the C function
   caml_io_mutex_lock():

  /* Problem: if a signal occurs at this point,
     and the signal handler raises an exception, we will not
     unlock the mutex.  The alternative (doing the setspecific
     before locking the mutex is also incorrect, since we could
     then unlock a mutex that is unlocked or locked by someone else. */

  This of course means that IO around a fork() is unsafe.  Grr.

  For some reason, the below code works fine on astrocyte, but on ged
  it locks up waiting for the IO mutex before showing any sign of
  having entered the child branch of the fork.  I suspect the above is
  the reason.

*)


module MyMutex :
(* Reimplements mutices, removing two crucial restrictions:

   (1) locking a mymutex that is already locked always blocks, no
       matter which thread calls lock (even the same thread that
       locked it in the first place is blocked)

   (2) any thread may unlock the mutex; it needn't be the locking
       thread.

   Neither of these behaviours are guaranteed by POSIX / Pthreads /
   OCaml threads.
*)
    sig
      type t
      val create : unit -> t
      val lock : t -> unit
      val unlock : t -> unit
    end =

  struct

    type t = { isset : bool ref;
               lock : Mutex.t;
               cond : Condition.t
             }

    let create () =
      { isset = ref false;
        lock = Mutex.create ();
        cond = Condition.create ()
      }

    let lock m =
      Mutex.lock m.lock;
      (* block until m unlocked *)
      while !(m.isset) do
        Condition.wait m.cond m.lock
      done;
      (* lock it *)
      m.isset := true;
      Mutex.unlock m.lock

    let unlock m =
      Mutex.lock m.lock;
      (* unlock it *)
      m.isset := false;
      (* signal waiters *)
      Condition.signal m.cond;
      Mutex.unlock m.lock

  end;;

module TSQueue :
(* Implements thread-safe queues with explicit EOF and transactional pop *)
    sig
      type 'a t
      type token
      val create : unit -> 'a t
      val push : 'a t -> 'a -> unit
      val pusheof : 'a t -> unit
      val beginpop : 'a t -> ('a * token) option
      val commitpop : token -> unit
      val abortpop : token -> unit
      val pop : 'a t -> 'a option
      val ateof : 'a t -> bool
      val length : 'a t -> int * int  (* definitely still in queue, pending *)
    end =

  struct

    type 'a t = { q : 'a Queue.t;
                  eof : bool ref;
                  outstanding : int ref;
                  lock : Mutex.t;
                  cond : Condition.t;
                  }

    type token = bool -> unit

    let create () = {
      q = Queue.create ();
      eof = ref false;
      outstanding = ref 0;
      lock = Mutex.create ();
      cond = Condition.create ()
    }

    let push tsq x =  (* push a datum *)
      Mutex.lock tsq.lock;
      if !(tsq.eof) then
        raise (Failure "tsqueue_push after EOF");
      Queue.add x tsq.q;
      Condition.signal tsq.cond;
      Mutex.unlock tsq.lock

    let pusheof tsq =  (* push EOF *)
      Mutex.lock tsq.lock;
      if !(tsq.eof) then
        raise (Failure "tsqueue_pusheof after EOF");
      tsq.eof := true;
      Condition.broadcast tsq.cond;  (* multiple threads may wake here! *)
      Mutex.unlock tsq.lock

    let is_empty q =  (* helper function *)
      try ignore (Queue.peek q); false with Queue.Empty -> true

    let beginpop tsq =  (* blocks until something is available; returns None for EOF,
                           otherwise returns element and token; the token must be
                           either committed (to keep the element) or aborted (to return it). *)
      Mutex.lock tsq.lock;
      while is_empty tsq.q && (!(tsq.outstanding) <> 0 || not !(tsq.eof)) do
        Condition.wait tsq.cond tsq.lock
      done;
      let rv =
        try
          let x = Queue.take tsq.q in
          tsq.outstanding := !(tsq.outstanding) + 1;
          let once = ref true in
          Some (x,
                fun commit ->
                  Mutex.lock tsq.lock;
                  if !once then
                    ((if commit then
                      ()
                    else
                      Queue.add x tsq.q);
                     tsq.outstanding := !(tsq.outstanding) - 1;
                     once := false;
                     Condition.broadcast tsq.cond;  (* multiple threads may wake here! *)
                     Mutex.unlock tsq.lock)
                  else
                    (Mutex.unlock tsq.lock;
                     raise (Failure "TSQueue: multiple commit/abort")))
        with
          Queue.Empty ->
            if !(tsq.outstanding) = 0 && !(tsq.eof) then
              None
            else
              raise (Failure "TSQueue: internal error")
      in
      Mutex.unlock tsq.lock;
      rv

    let commitpop token =
      token true

    let abortpop token =
      token false

    let pop tsq =
      match beginpop tsq with
        None -> None
      | Some(x,tok) ->
          commitpop tok;
          Some x

    let ateof tsq =
      Mutex.lock tsq.lock;
      let rv = is_empty tsq.q && !(tsq.outstanding) = 0 && !(tsq.eof) in
      Mutex.unlock tsq.lock;
      rv

    let length tsq =
      Mutex.lock tsq.lock;
      let len = Queue.length tsq.q in
      let pend = !(tsq.outstanding) in
      Mutex.unlock tsq.lock;
      (len,pend)

  end


(* machinery to implement a global minimum delay between execs *)
let wait_until_exec_safe =
  let execlock = MyMutex.create () in
  function () ->
    MyMutex.lock execlock;
    (* spawn a thread to release lock at the appointed time *)
    let _ =
      Thread.create (fun () ->
        Thread.delay (float_of_int !execdelay);
        MyMutex.unlock execlock) ()
    in
    (* return immediately in calling thread *)
    ();;


(* read lines from channel, processing each with f, until either EOF
   or a line matches one of the regexps.  In either case, return the
   specified value *)
let wait_for_match : in_channel -> (string -> unit) -> 'a -> (Str.regexp * 'a) list -> 'a
    = fun ic f eofv rvs ->
      let rec find rvs s =
        match rvs with
          [] -> None
        | ((r,v)::rvs) ->
            if Str.string_match r s 0 then
              Some v
            else
              find rvs s
      in
      let rec loop () =
        match (try Some (input_line ic) with End_of_file -> None) with
          None -> eofv
        | Some s ->
            f s;
            match find rvs s with
              None -> loop ()
            | Some v -> v
      in
      loop ()


(* main program *)
let main () =
  do_args ();
  let statuschange_cond = Condition.create () in
  let workerlist = gen_workerlist statuschange_cond !hostspec in
  (if not !dynamicmode then
    raise (Failure("Sorry, non-dynamic mode unsupported at present.")));

  let worklist = TSQueue.create () in
  let worklistlength = List.length !infiles in
  ignore (List.map (TSQueue.push worklist) !infiles);
  TSQueue.pusheof worklist;

  (* signal handling *)
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let kill_signalled = ref false in  (* true means please die ASAP *)

  (* the code that each worker thread runs *)
  let rec worker_main worker =
    let tprint s = print_string ("["^worker.idstr^"]: "^s) in
    let setstatus_ext state asleep =
      let status = { st = state; asleep = asleep } in
      worker.status := status;
      Condition.broadcast worker.schg;
      let (st,arg) = render_workerstatus status in
      let data = match arg with
        None -> "-"
      | Some s -> s in
      print_string ("=="^st^" "^worker.host^"["^worker.idstr^"] \""^data^"\" at "^mtimestamp ()^"\n")
    in
    let setstatus state =
      setstatus_ext state false  (* if we get state-change info, we are certainly not asleep! *)
    in
    let setasleep asleep =
      setstatus_ext !(worker.status).st asleep
    in
    let rec outer_loop () =
      (* start command *)
      setstatus WaitingUntilExecSafe;
      tprint "Starting child.\n";
      if !kill_signalled then raise (Failure "Thread death requested");
      wait_until_exec_safe ();
      if !kill_signalled then raise (Failure "Thread death requested");
      setstatus Starting;
      (if !debug then tprint ("Executing "^String.concat " " worker.cmd^"...\n"));
      let (in1,out1) = Unix.pipe () in  (* data written to out will appear at in *)
      let (in2,out2) = Unix.pipe () in  (* data written to out will appear at in *)

      (try Unix.access (List.hd worker.cmd) [Unix.X_OK] with
      Unix.Unix_error(_) -> raise (Failure ("Command "^List.hd worker.cmd^" is not executable!")));

      worker.startctr := !(worker.startctr) + 1; Condition.broadcast worker.schg;
      let pid = Unix.fork () in
      (if pid <> 0 then  (* we are parent *)
        (worker.pid := Some pid;  (* save pid for killing purposes later *)
         Unix.close in1;  (* we don't need these ends of the pipes *)
         Unix.close out2)
      else  (* we are child *)
        ((* WARNING: the child must not make any slow call; if OCaml is
            induced to invoke enter_blocking_section(), then a race occurs
            which frequently ends in deadlock.  Sadly, this means that if
            the exec fails, it must do so silently.  Hmm, it's possible that
            even raising an exception is fatal :-( *)
         Unix.dup2 in1 Unix.stdin; Unix.close in1; Unix.close out1;  (* redirect stdin *)
         Unix.dup2 out2 Unix.stdout; Unix.dup2 out2 Unix.stderr;  (* redirect std{out,err} *)
         Unix.close out2; Unix.close in2;
         (try
           Unix.execv (List.hd worker.cmd) (Array.of_list worker.cmd)
         with
           _ -> ());
         exit 255));

      let out_child = Unix.out_channel_of_descr out1 in  (* out to child's stdin *)
      let in_child = Unix.in_channel_of_descr in2 in  (* in from child's stdout *)

      let do_abortcmd job reason =
        match !abortcmd with
          None -> ()
        | Some cmd ->
            ignore (Sys.command (String.concat " " (cmd @ [job;reason])))
      in

      let tprint_sub s = tprint (">"^s^"\n") in

      let ready_re      = Str.regexp "Ready.$" in
      let inuse_wait_re = Str.regexp "INUSE WAIT:" in
      let inuse_kill_re = Str.regexp "INUSE KILL:" in
      let inuse_stop_re = Str.regexp "INUSE STOP:" in
      let inuse_cont_re = Str.regexp "INUSE CONT:" in

      let wait_for_event () =
        wait_for_match in_child tprint_sub 0
          [(ready_re,1);
           (inuse_wait_re,2);
           (inuse_kill_re,3);
           (inuse_stop_re,4);
           (inuse_cont_re,5);
         ]
      in

      let rec inner_loop job_token =
        match wait_for_event () with
        | 4 ->  (* INUSE STOP *)
            setasleep true;
            inner_loop job_token
        | 5 ->  (* INUSE CONT *)
            setasleep false;
            inner_loop job_token
        | (0 as n)     (* EOF *)
        | (2 as n) ->  (* INUSE WAIT *)
            ((match job_token with
              None ->
                setstatus (Crashed(None))
            | Some(x,tok) ->
                (do_abortcmd x "CRASHED";
                 TSQueue.commitpop tok;
                 worker.jobcrashctr := !(worker.jobcrashctr) + 1; (* signalled by setstatus *)
                 setstatus (Crashed(Some(x)))));
             (if n = 2 then
               setstatus WaitingForIdle;
              match wait_for_event () with
                0 -> ()
              | _ -> raise (Failure ("Unexpected event after INUSE WAIT: protocol violation"))
             );
             (false,job_token <> None))

        | 3 ->  (* INUSE KILL *)
            ((match job_token with
              None ->
                setstatus (Killed(None))
            | Some(x,tok) ->
                (do_abortcmd x "KILLED";
                 TSQueue.abortpop tok;
                 worker.jobkillctr := !(worker.jobkillctr) + 1; (* signalled by setstatus *)
                 setstatus (Killed(Some x))));
             (match wait_for_event () with
               2 -> ()
             | _ -> raise (Failure ("Expected INUSE WAIT after INUSE KILL: protocol violation")));
             setstatus WaitingForIdle;
             (match wait_for_event () with
               0 -> ()
             | _ -> raise (Failure ("Unexpected event after INUSE WAIT: protocol violation")));
             (false,true))

        | 1 ->  (* Ready *)
            ((match job_token with
              None ->
                setstatus WaitingForWork
            | Some(x,tok) ->
                (TSQueue.commitpop tok;
                 worker.jobcompletectr := !(worker.jobcompletectr) + 1;  (* signalled by setstatus *)
                 setstatus (Completed(x))));
             (* try to get more work *)
             match TSQueue.beginpop worklist with
               None ->
                 (true,false)
             | Some (x,tok) ->
                 tprint ("Doing "^x^"...\n");
                 (try
                   output_string out_child (x^"\n");
                   flush out_child
                 with
                   Sys_error(s) -> if !debug then tprint ("Ignoring Sys_error("^s^") on output.\n"));
                 worker.jobctr := !(worker.jobctr) + 1;  (* signalled by setstatus *)
                 setstatus (Processing(x));
                 inner_loop (Some (x,tok)))

        | n ->
            raise (Failure ("Never happen: event number "^string_of_int n))
      in

      let close_and_reap () =
        (if !debug then tprint "Closing and reaping.\n");
        (try
          close_out out_child;
          close_in in_child
        with
          Sys_error(s) -> if !debug then tprint ("Ignoring Sys_error("^s^") on close.\n"));
        let (_,status) = Unix.waitpid [] pid in
        worker.pid := None;
        (if !debug then begin
          tprint ("Child process "^string_of_int pid^" ("^String.concat " " worker.cmd^") completed:\n");
          tprint (match status with
            Unix.WEXITED(n)   -> "  Exited with code "^string_of_int n^".\n"
          | Unix.WSIGNALED(n) -> "  Died on signal "^string_of_int n^".\n"
          | Unix.WSTOPPED(n)  -> "  Stopped on signal "^string_of_int n^".\n");
          tprint ("  at "^ timestamp () ^".\n")
        end)
      in

      match inner_loop None with
        (true,_) ->  (* ran out of work *)
          setstatus Finishing;
          (* read any more child output and close channels *)
          tprint "No more work for child.\n";
          (if !debug then tprint "Sending quit command.\n");
          output_string out_child "quit\n";
          flush out_child;
          while wait_for_event () <> 0 do
            (if !debug then tprint "Ignoring event while waiting for EOF.\n")
          done;
          (if !debug then tprint "Got EOF from child.\n");
          close_and_reap ();
          setstatus Finished;
          ()  (* exit thread *)
      | (false,ok_to_restart) ->  (* command died for some reason *)
          (tprint "Command yielded unexpected EOF.\n";
           close_and_reap ();
           if ok_to_restart then
             ((if !debug then tprint "Reaped dead process; restarting.\n");
              outer_loop ())
           else
             (worker.cantstartctr := !(worker.cantstartctr) + 1;
              (if !debug then tprint "Command failed before `Ready.'; giving up.\n");
              (match !restartdelay with
              | None ->
                  setstatus CantStart;
                  ()  (* exit thread; we're not restarting after a fatal crash *)
              | Some d ->
                  setstatus WaitingForRestart;
                  Thread.delay (float_of_int d);
                  outer_loop ())
             )
          )
    in

    try
      outer_loop ()
    with
      Sys_error(s) ->
        setstatus LocalCrash;
        tprint ("Thread died: Sys_error: "^s^".\n")
    | Failure(s) ->
        setstatus LocalCrash;
        tprint ("Thread died: Failure: "^s^".\n")
    | Unix.Unix_error(e,c,a) ->
        setstatus LocalCrash;
        tprint ("Thread died: Unix_error: "^c^"("^a^"): "^Unix.error_message e^".\n")
    | _ ->
        setstatus LocalCrash;
        tprint ("Thread died.\n")

  in

  (* the code of the master thread *)

  (* open status file *)
  let (emit_status,close_status) =
    match !statusfile with
      Some f ->
        let emit s =
          let fd = Unix.openfile f [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_TRUNC] 0o666 in
          fd_print_string fd s;
          Unix.close fd
        in
        (emit, fun () -> ())
    | None ->
        (fd_print_string Unix.stdout, fun () -> ())
  in

  (* fork off threads *)
  if !debug then print_string "Forking threads.\n";

  let killchildren signal =
    kill_signalled := true;
    ignore (List.map
              (fun w ->
                match !(w.pid) with
                  None -> ()
                | Some pid -> try Unix.kill pid signal with _ -> ()
              ) workerlist
           );
    print_string (string_of_int (Unix.getpid ()) ^ ": Cleaned up processes on signal "^string_of_int signal^".  Process should exit within 30 seconds!\n");
    Thread.delay 30.0;
    exit 3
  in

  Sys.set_signal Sys.sigint (Sys.Signal_handle killchildren);
  Sys.set_signal Sys.sigterm (Sys.Signal_handle killchildren);

  ignore (List.map
            (fun w ->
              let tid = Thread.create worker_main w in
              w.tid := Some tid)
            workerlist
         );

  (* wait till they're all finished *)
  if !debug then print_string "Threads forked; master thread waiting for completion.\n";

  let dummy_lock = Mutex.create () in
  let stop_status = ref false in
  let rec status_display () =
    let (r,p) = TSQueue.length worklist in
    let d = worklistlength - (r+p) in
    let t = worklistlength in
    emit_status ("\nWorker status at "^mtimestamp()^":\n"^String.concat "\n" (List.map render_worker workerlist)^"\n"^Printf.sprintf "Worklist status: %d complete, %d pending, %d todo of %d\n\n" d p r t);
    if !stop_status then
      ()
    else begin
      Mutex.lock dummy_lock;
      Condition.wait statuschange_cond dummy_lock;
      Mutex.unlock dummy_lock;
      status_display ()
    end in
  let status_thread = Thread.create status_display () in

  ignore (List.map
            (fun w ->
              match !(w.tid) with None -> () | Some t -> Thread.join t
            ) workerlist
         );
  if !debug then print_string "All threads reaped.\n";

  if not (TSQueue.ateof worklist) then
    print_string "WARNING: worklist not completed.\n";

  stop_status := true;
  Condition.broadcast statuschange_cond;
  Thread.join status_thread;

  close_status ();;

let _ = main ()

