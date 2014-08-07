open Thread;;
open Array;;
open Unix;;
open String;;
open Parser;;
open Rawsock;;
open Errors;;
open Platform;;
open Printf;;

exception Fatal of string;;

let void f x = try f x; () with _ -> ();;
let term = ref 0;;
let num_send_retries = 13;;

let slurpin = "slurpin.hol"
let slurpinj = "slurpinj.hol"
let slurpout = "slurp.out"
let unixsockname = "/tmp/slurpinternalsocket."^string_of_int(getppid ());;

(* slurpinject-test iface injectfile *)
let check_cmdline_args argv =
  let len = Array.length argv in
  if(len != 4) then
    raise(Fatal("Incorrect arguments: slurpinject-test iface injectfile diffresultsfile"))
  else
    (Array.get argv 1, Array.get argv 2, Array.get argv 3);;

let rcvsocket_results sd fd =
  let slen = 2048 in
  let str = String.create slen in
  let rec loop x =
    if(!term = 1) then
	let _ = close sd in
	let _ = close fd in ()
    else
      let lenr =
	let rec l1 x =
	  let res = try recv sd str 0 slen [] with
            Unix.Unix_error(EINTR,b,c) -> l1 ();
	  in
	    if(res = 0) then (term := 1; res)
	    else res
	in l1 ()
      in
      if (lenr != 0) then
	let lens =
          let rec l2 x = try write fd str 0 lenr with
            Unix.Unix_error(EINTR,b,c) -> l2 () in
	  l2 ()
	in
	if(lenr != lens) then
	  raise(Fatal("Did not commit to the temporary file all data received"))
	else loop ()
      else loop ()
  in loop ();;

let rcvsocket x =
  let _ = printf "Creating socket to receive slurper output on...\n"; flush Pervasives.stdout in
  let sd = socket PF_UNIX SOCK_STREAM 0 in
  let _ = (void) unlink unixsockname in
  let addr = ADDR_UNIX(unixsockname) in
  let _ = bind sd addr in
  let _ = listen sd 0 in
  let (sdconn, sdaddr) = accept sd in
  let fd = openfile slurpin [O_WRONLY; O_CREAT] 432 in
  rcvsocket_results sdconn fd;;

let writepkt sd addr pkt =
  (match (check_platform ()) with
    BSD -> (String.set pkt 10 (Char.chr 0); String.set pkt 11 (Char.chr 0);
	    let t = String.get pkt 2 in
	    (String.set pkt 2 (String.get pkt 3); String.set pkt 3 t);
	    let t = String.get pkt 6 in
	    (String.set pkt 6 (String.get pkt 7); String.set pkt 7 t))
  | _ -> ());
  let rec loop p n =
    match n with
      0 -> raise(Fatal("Number of write retries for RAWSOCK exceeded"))
    | _ ->
	let len = String.length p in
	let lensent = sendto sd p 0 len [] addr in
	if(len != lensent) then
	  loop (String.sub p lensent (len-lensent)) (n-1)
	else ()
  in loop pkt num_send_retries;;

let doinsertion x =
  let fd = openfile x [O_RDONLY] 0 in
  let sd = raw_socket PF_INET 0 in
  let _ = raw_sockopt_hdrincl sd in
  let addr = ADDR_INET ((inet_addr_of_string "0.0.0.0"), 0) in
  let loop = ref true in
  try
    let lexbuf = Lexing.from_channel (Unix.in_channel_of_descr fd) in
    while !loop do
      try let pkt = Parser.main Lexer.token lexbuf in
        (writepkt sd addr pkt; delay 0.25)
      with Parse_error(s) -> print_endline ("Error: "^s)
      |	Parsing.Parse_error -> loop := false
    done
  with Lexer.Eof ->
    ();;

(* ------------------- *)

let sendinject x =
  let _ = printf "\nDoing injection...\n"; flush Pervasives.stdout in
  let sd = socket PF_UNIX SOCK_STREAM 0 in
  let addr = ADDR_UNIX(unixsockname) in
  let _ = connect sd addr in
  let fd = openfile slurpinj [O_RDONLY] 0 in
  let slen = 2048 in
  let str = String.create slen in
  let rec loop x =
    let lenr =
      let rec doRead x =
	try read fd str 0 slen with
	  Unix.Unix_error(EINTR,a,b) -> doRead ()
      in doRead ()
    in
    match lenr with
      0 -> ()
    | n ->
	let lens =
	  let rec doSend x =
	    try send sd str 0 lenr [] with
	      Unix.Unix_error(EINTR,a,b) -> doSend ()
	  in
	  doSend ()
	in
	if(lens != lenr) then
	  raise(Fatal("Unable to complete doInject"))
	else
	  loop ()
  in
  loop ();;

(* ------------------- *)

let diff_packets inpkt outpkt len pktno out =
  let rec loop n =
    if(n = len) then true
    else if(n = 4) then loop (n+1)
    else if(n = 5) then loop (n+1)
    else if(n = 10) then loop (n+1)
    else if(n = 11) then loop (n+1)
    else
      if((String.get inpkt n) != (String.get outpkt n)) then
	(fprintf out "--------\n";
	 fprintf out "Diff of packet %d failed.   <-----\n" pktno;
	 fprintf out "Packet %d: differs in at least byte position %d\n" pktno n;
	 false)
      else
	loop (n+1)
  in loop 0;;


let diff_results fin fout dout=
  let fdin = openfile fin [O_RDONLY] 0 in
  let fdout = openfile fout [O_RDONLY] 0 in
  let diffout = openfile dout [O_WRONLY; O_CREAT] 432 in
  let out = out_channel_of_descr diffout in
  try
    let inlexbuf = Lexing.from_channel (Unix.in_channel_of_descr fdin) in
    let outlexbuf = Lexing.from_channel (Unix.in_channel_of_descr fdout) in
    let loop = ref true in
    let n = ref 0 in
    let correct = ref false in
    while !loop do
      try
	let inpkt = Parser.main Lexer.token inlexbuf in
	let outpkt = Parser.main Lexer.token outlexbuf in
	let inlen = String.length inpkt in
	let outlen = String.length outpkt in
	if(inlen != outlen) then
	  (fprintf out "--------\n";
	   fprintf out "Diff of packet %d failed.  <-----\n" !n;
	   fprintf out "Lengths do not match! %d != %d\n" inlen outlen;
	   fprintf out "Original packet: %s\n Output packet: %s\n\n" inpkt outpkt)
	else
	  ((correct := !correct || (diff_packets inpkt outpkt inlen !n out));
	   n := !n + 1)
      with Parse_error(s) -> print_endline ("Error: "^s)
      |	Parsing.Parse_error -> loop := false
    done;
    fprintf out "Diff of %d packets was OK.\n" !n
  with Lexer.Eof ->
    ();;


(* ------------------- *)

let _ =
  let (iface, file, diffout) = check_cmdline_args Sys.argv in
  let _ = printf "Netsem identity test (slurpinject) started....\n";
    flush Pervasives.stdout in
  let recv_thr = Thread.create rcvsocket () in
  let _ = printf "Forking slurper process...\n" in
  let slurp_args = Array.of_list ["../slurp/slurp"; iface; "UNIX";
				  unixsockname; "tcp or icmp"] in
  let slurp_pid = create_process "../slurp/slurp" slurp_args stdin stdout stderr in
  let _ = delay 3.00 in
  let _ = printf "Inserting packets from test file...\n"; flush Pervasives.stdout in
  let _ = doinsertion file in
  let _ = delay 3.00 in
  let _ = kill slurp_pid 9 in
  let _ = term := 1 in
  let _ = join recv_thr in
  let _ = term := 0 in
  let _ = printf "Replacing Lh_recvdatagram with Lh_senddatagram in slurped file...\n";
    flush Pervasives.stdout in
  let fd = openfile slurpinj [O_WRONLY; O_CREAT] 432 in
  let sed_args = Array.of_list ["/usr/bin/sed"; "s/Lh_recvdatagram/Lh_senddatagram/"; slurpin] in
  let sed_pid  = create_process "/usr/bin/sed" sed_args stdin fd stderr in
  let _ = waitpid [] sed_pid in
  let _ = close fd in
  let _ = (void) unlink unixsockname in
  let _ = printf "Forking pcap packet sniffer process...\n";
    flush Pervasives.stdout in
  let sniff_args = Array.of_list ["./pcapslurp"; "-o"; slurpout; "-i"; iface; "-c";
				  "10000"; "-f"; "tcp or icmp"] in
  let sniff_pid = create_process "./pcapslurp" sniff_args stdin stdout stderr in
  let _ = printf "Forking injector process...\n";
    flush Pervasives.stdout in
  let injector_args = Array.of_list ["../injector/injector"; "UNIX"; unixsockname] in
  let injector_pid = create_process "../injector/injector" injector_args stdin stdout stderr in
  let _ = delay 3.00 in
  let _ = sendinject () in
  let _ = delay 3.00 in
  let _ = kill injector_pid 9 in
  let _ = kill sniff_pid 9 in
  let _ = (void) unlink unixsockname in
  let _ = printf "\nDoing diff...\n\n"; flush Pervasives.stdout in
  let _ = diff_results file slurpout diffout in
  ();;


