open Thread;;
open Array;;
open Unix;;
open String;;

exception Fatal of string;;
let sendrcv_string_len = 2048;;   (* length of send/rcv strings *)
let ignore f x = try f x; () with _ -> ();;

(* Some temporary files *)
(* Not created in /tmp as we want this to work under Windows to! *)
let unixsockname = "slurpinternalsocket."^string_of_int(getppid());;
let rcv_unixsockname = "slurpinteralsocket2."^string_of_int(getppid());;
let tmpfile = "slurpinternaltemp."^string_of_int(getppid());;
let tmpfile2 = "slurpinternaltemp2."^string_of_int(getppid());;
let tmpfile3 = "slurpinternaltemp3."^string_of_int(getppid());;
let term = ref 0;;

(* injectslurp iface holtcp-testfile outputfile *)
let args = "Usage: injectslurp iface holtcp-testfile outputfile";;
let check_cmdline_args argv =
  let len = Array.length argv in
  if (len != 4) then
    raise(Fatal("Incorrect arguments: "^args))
  else
    (Array.get argv 1, Array.get argv 2, Array.get argv 3);;

(* Receive slurper output and write to file *)
(* Terminate at end of file or when signalled to terminate by parent *)
let rcvsocket_results sd fd =
  let str = String.create sendrcv_string_len in
  let rec loop x =
    if(!term = 1) then
	let _ = close sd in
	let _ = close fd in ()
    else
      let lenr =
	let rec l1 x =
	  let res =
	    try recv sd str 0 sendrcv_string_len []
	    with Unix.Unix_error(EINTR,b,c) -> l1 () in
	  if(res = 0) then (term := 1; res)
	  else res in
	l1 () in
      if (lenr != 0) then
	let lens =
          let rec l2 x =
	    try write fd str 0 lenr
	    with Unix.Unix_error(EINTR,b,c) -> l2 () in
	  l2 ()	in
	if(lenr != lens) then
	  raise(Fatal("Did not commit to the temporary file all data received"))
	else loop ()
      else loop ()
  in loop ();;

let rcvsocket f =
  let sd = socket PF_UNIX SOCK_STREAM 0 in
  let _ = (ignore) unlink rcv_unixsockname in
  let addr = ADDR_UNIX(rcv_unixsockname) in
  let _ = bind sd addr in
  let _ = listen sd 0 in
  let (sdconn, sdaddr) = accept sd in
  let fd = openfile f [O_WRONLY; O_CREAT] 432 in
  rcvsocket_results sdconn fd;;

(* ------------------- *)

let sendinject f =
  let sd = socket PF_UNIX SOCK_STREAM 0 in
  let addr = ADDR_UNIX(unixsockname) in
  let _ = connect sd addr in
  let fd = openfile f [O_RDONLY] 0 in
  let str = String.create sendrcv_string_len in
  let rec loop x =
    let _ = delay 0.25 in
    let lenr =
      let rec doRead x =
	try read fd str 0 sendrcv_string_len with
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


(* Input: HOLTCP file *)
(* Fork injector process -- listens *)
(* Spawn thread slurp listener -- listens. Output TO HOLTCP file *)
(* Fork slurper process -- connects to listener *)
(* Send file to injector -- connects to injector process *)
(* Once inject send done, pause then kill injector then slurper processes *)
(* Terminate listening thread *)
(* Run sed to strip comments and change Lh_recvdatagram to Lh_senddatagram *)
(* Diff input and output *)
(* Diffs should be identical *)


let _ =
  let (iface, file, output) = check_cmdline_args Sys.argv in
  let _ = (ignore) unlink unixsockname in
  let _ = print_endline "Forking injector process..."; flush Pervasives.stdout in
  let injector_args = Array.of_list ["../injector/injector"; "UNIX"; unixsockname] in
  let injector_pid = create_process "../injector/injector" injector_args stdin stdout stderr in
  let _ = delay 0.50 in
  let _ = print_endline "Creating thread to receive slurped packets..."; flush Pervasives.stdout in
  let rcv_thread = Thread.create rcvsocket output in
  let _ = delay 0.50 in
  let _ = print_endline "Forking slurper process..."; flush Pervasives.stdout in
  let slurper_args = Array.of_list ["../slurp/slurp"; iface; "UNIX"; rcv_unixsockname; "tcp or icmp"] in
  let slurper_pid = create_process "../slurp/slurp" slurper_args stdin stdout stderr in
  let _ = delay 0.50 in
  let _ = print_endline "Sending hol tcp packets to injector..."; flush Pervasives.stdout in
  let _ = sendinject file in
  let _ = delay 3.00 in
  let _ = kill injector_pid 9 in
  let _ = delay 3.00 in
  let _ = kill slurper_pid 9 in
  let _ = term := 1 in
  let _ = join rcv_thread in
  let _ = (ignore) unlink unixsockname in
  let _ = (ignore) unlink rcv_unixsockname in
  let _ = print_endline "Running sed..."; flush Pervasives.stdout in
  let _ = (ignore) unlink tmpfile in
  let _ = (ignore) unlink tmpfile2 in
  let _ = (ignore) unlink tmpfile3 in
  let fd = openfile tmpfile  [O_WRONLY; O_CREAT] 432 in
  let sed_args = Array.of_list ["/usr/bin/sed"; "-e"; "s/Lh_recvdatagram/Lh_senddatagram/g"; output] in
  let sed_pid  = create_process "/usr/bin/sed" sed_args stdin fd stderr in
  let _ = waitpid [] sed_pid in
  let _ = close fd in
  let fd = openfile tmpfile2 [O_WRONLY; O_CREAT] 432 in
  let sed_args = Array.of_list ["/usr/bin/sed"; "-e"; "s/(\*[^'*']*\*)//g"; tmpfile] in
  let sed_pid  = create_process "/usr/bin/sed" sed_args stdin fd stderr in
  let _ = waitpid [] sed_pid in
  let _ = close fd in
  let fd = openfile tmpfile3 [O_WRONLY; O_CREAT] 432 in
  let sed_args = Array.of_list ["/usr/bin/sed"; "-e"; "s/(\*[^'*']*\*)//g"; file] in
  let sed_pid  = create_process "/usr/bin/sed" sed_args stdin fd stderr in
  let _ = waitpid [] sed_pid in
  let _ = close fd in
  let _ = print_endline "Running diff..."; flush Pervasives.stdout in
  let diff_args = Array.of_list ["/usr/bin/diff"; "-s"; "--ignore-all-space"; "--ignore-blank-lines"; tmpfile2; tmpfile3] in
  let diff_pid = create_process "/usr/bin/diff" diff_args stdin stdout stderr in
  let _ = waitpid [] diff_pid in
  let _ = (ignore) unlink tmpfile in
  let _ = (ignore) unlink tmpfile2 in
  let _ = (ignore) unlink tmpfile3 in
  ();;


