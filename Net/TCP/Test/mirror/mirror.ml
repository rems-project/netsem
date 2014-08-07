(********************)
(* The Magic Mirror *)
(********************)

(* This is a utility which takes as paramters the name of a network interface
 * and a list of pairs (realip, fakeip). It starts a slurper and an injector
 * on the given interface and then waits for TCP packets whose source matches
 * a known 'real' host and whose destination matches a known 'fake' host. For
 * each such packet received, the magic mirror produces a new packet with the
 * source replaced by the IP of its corresponding 'fake' host and the
 * destination replaced by the IP of the corresponding 'real' host. In this
 * way, two hosts can be induced to talk to one another while their
 * conversation is relayed entirely through the magic mirror. The mirror can
 * then drop, duplicate and delay packets to mimic the effect of an unreliable
 * network.
 *
 * Command-line syntax is:
 *    mirror iface TCP ip port [opts] realip fakeip [realip fakeip ...]
 *    mirror iface UNIX socket [opts] realip fakeip [realip fakeip ...]
 *
 * Supplying only one realip-fakeip pair is legal but ineffectual. opts can
 * contain any or all of:
 *
 * -d delay     Delay all emitted packets by up to delay seconds
 * -l prob      Lose packets entirely with probability prob
 * -n copies    Emit between 1 and copies copies of each packet which is
 *                not lost
 *
 * 'TCP ip port' or 'UNIX socket' specify a socket to connect to to report
 * the mirror's configuration when it starts up. It doesn't generate any output
 * while it's running, but we want to record the IP addresses being rewritten
 * in the trace so that they can be fixed up later before checking.
 *
 * Note that hosts will usually not emit a packet to a fake ip unless they
 * believe a valid route exists. This can be done (as root) with a command
 * such as:
 *
 *    route add fakeip mirrorhost
 *
 * where mirrorhost is the IP address of the host running the mirror. A
 * convenient setup is to add a route for a different subnet, eg:
 *
 *    route add 192.168.14.0 mirrorhost
 *
 * and then use the corresponding address on the 192.168.14.0 subnet as the
 * fake IP for each of the hosts on the 192.168.13.0 subnet. *)

open Thread
open Unix
open Printf

open Holparselib
open Holrender
open Holtypes
open Nettypes
open Parser
open Parserlib

exception Bad_ip of string

(* Default configuration *)
let maxdel = ref 0.0 (* Maximum delay on packet in seconds *)
let maxdup = ref 1 (* Maximum number of duplicates of each packet *)
let drop = ref 0.0 (* Probability of dropping a given packet *)

(* Path to binaries to invoke *)
let injector_path = "../injector/injector"
let slurper_path = "../slurp/slurp"

(* Unix socket names *)
let injectorsock = "/tmp/magicmirror." ^ string_of_int(getpid ()) ^ ".inject"
let slurpersock = "/tmp/magicmirror." ^ string_of_int(getpid ()) ^ ".slurp"

(* Make a function call and ignore errors, eg. for removing temp files *)
let void f x = try f x; () with Unix_error(_,_,_) -> ()

(* Keep trying something until it succeeds, backing off exponentially. Used
   when, eg., we're trying to connect to the injector and it might not have
   created a listening socket yet. *)
let retry f x =
  let rec loop n d =
    try f x
    with e ->
      (* Nettypes redefines the infix floating point multiplication operator *)
      if n = 0 then raise e else delay d; loop (n-1) (float_mul d 2.0)
  in loop 8 0.1

(* Exit with error *)
let die s =
  print_endline s;
  Pervasives.exit 1

let string_of_ip ip = match ip with
                      None -> "none"
                    | Some(n) ->
                        (Int64.to_string ((n >> 24) &. 0xffL))
                ^ "." ^ (Int64.to_string ((n >> 16) &. 0xffL))
                ^ "." ^ (Int64.to_string ((n >>  8) &. 0xffL))
                ^ "." ^ (Int64.to_string (n &. 0xffL))

let ip_of_string s = try
  let dot1 = String.index s '.' in
  let dot2 = String.index_from s (dot1 +1) '.' in
  let dot3 = String.index_from s (dot2 +1) '.' in
  let a = Int64.of_string (String.sub s 0 dot1) in
  let b = Int64.of_string (String.sub s (dot1 +1) (dot2 - dot1 -1)) in
  let c = Int64.of_string (String.sub s (dot2 +1) (dot3 - dot2 -1)) in
  let d = Int64.of_string (String.sub s (dot3 +1) ((String.length s) - dot3 -1))
  in
  Some ((a << 24) |. (b << 16) |. (c << 8) |. d)
  with
  _ -> raise (Bad_ip s)

(* Parse arguments to the program *)
let get_cmdline_args argv =
  let usage = "
Usage: mirror iface TCP ip port [opts] realip fakeip [realip fakeip ...]
       mirror iface UNIX socket [opts] realip fakeip [realip fakeip ...]
where -d specifies maximum delay on packets
      -n specifies maximum duplication count
      -l specifies probability of loss\n" in
  let iplist = ref [] in
  let len = Array.length argv in
  if (len < 5) then
    die usage
  else
  let iface, typ, ip = argv.(1), argv.(2), argv.(3) in
  let port, args =
    if typ = "TCP" then
      argv.(4), Array.to_list (Array.sub argv 5 (len - 5))
    else
      "", Array.to_list (Array.sub argv 4 (len - 4)) in
  let rec read_args l =
    match l with
      [] -> ()
    | s1::(s2::x) ->
        (if (s1 = "-d") then
          try
            maxdel := float_of_string s2;
            assert (!maxdel >= 0.0)
          with _ -> die ("Illegal delay: " ^ s2)
        else if (s1 = "-n") then
          try
            maxdup := int_of_string s2;
            assert (!maxdup >= 1)
          with _ -> die ("Illegal duplication count: " ^ s2)
        else if (s1 = "-l") then
          try
            drop := float_of_string s2;
            assert (!drop >= 0.0 && !drop <= 1.0)
          with _ -> die ("Illegal drop probability: " ^ s2)
        else
          iplist := (ip_of_string s1, ip_of_string s2)::(!iplist));
        read_args x
    | _ -> die usage
  in read_args args;
  try
    iface, !iplist, typ, ip, port
  with
    Bad_ip s -> die ("Fatal error: couldn't parse this as an IP address: " ^ s)

let get_opts () =
  "Maximum packet delay: " ^ (string_of_float !maxdel) ^ "s\n" ^
  "Maximum duplicates: " ^ (string_of_int !maxdup) ^ "\n" ^
  "Loss probability: " ^ (string_of_float !drop) ^ "\n";;

(* Given a TCP segment and our list of real/fake IP addresses, figure out
   whether this is a segment we should be rewriting (and return it) or a
   segment we should just ignore (return None) *)
let update_seg real_to_fake s =
  let fake_to_real = List.map (function a,b -> b,a) real_to_fake in
  let src, dst = s.is1, s.is2 in
    if (List.mem_assoc src real_to_fake && List.mem_assoc dst fake_to_real)
      then Some { s with is1 = List.assoc src real_to_fake;
                         is2 = List.assoc dst fake_to_real }
    else None

(* Body of a thread which waits for d seconds, then injects a TCP segment *)
let injector_thread_body (d, sdout, seg, lock) =
  delay d;
  Mutex.lock lock;
  let s = render_tcp_inner  seg SENDDGRAM in
    Sock.write sdout s;
  Mutex.unlock lock

(* Connect a logging channel over TCP or UNIX socket as requested *)
let connect_log typ ip port =
  if typ = "TCP" then
    let sd = Unix.socket PF_INET Unix.SOCK_STREAM 6 in
    Unix.setsockopt sd SO_REUSEADDR true;
    Unix.connect sd (ADDR_INET(inet_addr_of_string ip, int_of_string port));
    sd
  else
    let sd = Unix.socket PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.setsockopt sd SO_REUSEADDR true;
    Unix.connect sd (ADDR_UNIX ip);
    sd;;

(* Here begins the program proper *)
let _ =
  let iface, iplist, typ, ip, port = get_cmdline_args Sys.argv in
  (* First open our logging channel *)
  let sdlog = connect_log typ ip port in
  let out_hdr = sprintf "(* Magic mirror - Running on host: %s *)\n" (Platform.gethostname()) in
  Sock.write sdlog out_hdr;
  let out_hdr2 = sprintf "(* Options:\n%s*)\n" (get_opts ()) in
  Sock.write sdlog out_hdr2;

  (* TODO: At this point, the mirror should really also write out the IP
     address pairs it's rewriting between, so that a post-processing tool can
     pick them out of the trace and do the relevant fixing-up*)

  Sock.write sdlog "(* BEGIN *)";
  (* Create slurper and injector processes and open sockets *)
  void unlink injectorsock;
  void unlink slurpersock;
  let injector_args = Array.of_list [injector_path; "UNIX"; injectorsock] in
  let injector_pid = create_process injector_path injector_args
                                                        stdin stdout stderr in
  let sdout = Unix.socket PF_UNIX Unix.SOCK_STREAM 0 in
  (try
    retry (Unix.connect sdout) (ADDR_UNIX injectorsock);
  with Unix_error(_) ->
    die "Fatal error: Couldn't connect to injector (are you root?)");
  let sd = Unix.socket PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.bind sd (ADDR_UNIX slurpersock);
  Unix.listen sd 0;
  let slurper_args = Array.of_list [slurper_path; iface; "UNIX"; slurpersock;
                                                                     "tcp"] in
  let slurper_pid = create_process slurper_path slurper_args
                                                        stdin stdout stderr in
  let (sdin, _) = Unix.accept sd in
  (* Now we can talk to the slurper on sdin and the injector on sdout *)
  let inch = in_channel_of_descr sdin in
  let injector_lock = Mutex.create () in
  Random.self_init ();
  print_endline (get_opts ());
  print_endline "Magic mirror running ...";
  (* Skip lines until we see the BEGIN (parser chokes on the header) *)
  let rec loop () =
    if input_line inch <> "(* BEGIN *)" then loop () else ()
  in loop ();
  let env = Threadparsing.create_parse_env () in
  let lexbuf = Lexing.from_channel (in_channel_of_descr sdin) in
  (* Ready to start parsing! *)
  while true do
    let parseres = Parser.main env Lexer.token lexbuf in
    let holmsg =
       match parseres with
        PARSE_RETURN(_,_,HOLRCVMSG(x)) -> x
      | _ -> die "Fatal error: got an unexpected (impossible?) label type" in
    match holmsg with
      TCPMSG(segment) ->
        match update_seg iplist segment with
          Some(newseg) ->
            if ((Random.float 1.0) < !drop) then () else
            let rec spawn n =
              let d = Random.float !maxdel in
              ignore (Thread.create injector_thread_body
                                          (d, sdout, newseg, injector_lock));
              if n=0 then () else spawn (n - 1)
            in spawn (1 + (Random.int !maxdup))
        | None -> ();
  done;
  let _ = kill injector_pid 9 in
  let _ = kill slurper_pid 9 in
  let _ = void unlink injectorsock in
  let _ = void unlink slurpersock in
  ();;
