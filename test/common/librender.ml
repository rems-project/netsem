open Libcalls;;
(*open Parserlib;;*)
open Ocamllib;;
open Printf;;
(*open ThreadUnix;;*)
(*open Sock;;*)

exception Fatal of string;;

let render_int i =
  if i >= 0 then sprintf "%d" i
  else sprintf "~%d" (-i)

let fd_render fd =
  sprintf "FD %d" (int_of_fd fd);;

let tid_render td =
  sprintf "TID %d" (int_of_tid td);;

let ip_render ip =
  let ips = string_of_ip ip in
  let len = String.length ips in
  let _ =
    let rec loop i =
      if (i = len) then ()
      else if ((String.get ips i) = '.') then
	((String.set ips i ' '); loop (i+1))
      else
	loop (i+1)
    in loop 0
  in sprintf "IP %s" ips;;

let netmask_render nm =
  sprintf "NETMASK %d" (int_of_netmask nm);;

let ifid_render ifid =
  sprintf "IFID %s" (string_of_ifid ifid);;

let port_render port =
  sprintf "Port %d" (int_of_port port);;

let ipopt_render ipopt =
  match ipopt with
    None -> "NONE"
  | Some(x) -> sprintf "SOME(%s)" (ip_render x);;

let portopt_render portopt =
  match portopt with
    None -> "NONE"
  | Some(x) -> sprintf "SOME(%s)" (port_render x);;

let bool_render b =
  match b with
    false -> "F"
  | true-> "T";;


let bflag_render bflag =
  match bflag with
    Ocamllib.SO_BSDCOMPAT -> "SO_BSDCOMPAT"
  | Ocamllib.SO_REUSEADDR -> "SO_REUSEADDR"
  | Ocamllib.SO_KEEPALIVE -> "SO_KEEPALIVE"
  | Ocamllib.SO_OOBINLINE -> "SO_OOBINLINE"
  | Ocamllib.SO_DONTROUTE -> "SO_DONTROUTE"
  | Ocamllib.SO_BROADCAST -> "SO_BROADCAST"

let nflag_render nflag =
  match nflag with
    Ocamllib.SO_SNDBUF -> "SO_SNDBUF"
  | Ocamllib.SO_RCVBUF -> "SO_RCVBUF"
  | Ocamllib.SO_SNDLOWAT -> "SO_SNDLOWAT"
  | Ocamllib.SO_RCVLOWAT -> "SO_RCVLOWAT";;

let tflag_render tflag =
  match tflag with
    Ocamllib.SO_LINGER -> "SO_LINGER"
  | Ocamllib.SO_SNDTIMEO -> "SO_SNDTIMEO"
  | Ocamllib.SO_RCVTIMEO -> "SO_RCVTIMEO";;

let msgbflag_render msgflag =
  match msgflag with
    Ocamllib.MSG_PEEK -> "MSG_PEEK"
  | Ocamllib.MSG_OOB -> "MSG_OOB"
  | Ocamllib.MSG_WAITALL -> "MSG_WAITALL"
  | Ocamllib.MSG_DONTWAIT -> "MSG_DONTWAIT";;

let fbflag_render bflag =
  match bflag with
    Ocamllib.O_ASYNC -> "O_ASYNC"
  | Ocamllib.O_NONBLOCK -> "O_NONBLOCK";;

let fbflaglist_render flaglist =
  let flist = List.map fbflag_render flaglist in
  sprintf "[%s]" (String.concat "; " flist);;

let msgbflaglist_render bflaglist =
  let slist =
    let rec loop x =
      match x with
	[] -> []
      |	(x::xs) -> (msgbflag_render x)::(loop xs)
    in loop bflaglist
  in sprintf "[%s]" (String.concat "; " slist);;

let fdlist_render fdlist =
  let slist =
    let rec loop x =
      match x with
	[] -> []
      |	(x::xs) -> (fd_render x)::(loop xs)
    in loop fdlist
  in sprintf "[%s]" (String.concat "; " slist);;

let intpairopt_render i =
  match i with
    None -> "NONE"
  | Some (a,b) ->
      sprintf "SOME(%s, %s)" (render_int a) (render_int b);;

let ipoption_render ip =
  match ip with
    None -> "NONE"
  | Some(i) -> sprintf "SOME(%s)" (ip_render i);;

let portoption_render port =
  match port with
    None -> "NONE"
  | Some(p) -> sprintf "SOME(%s)" (port_render p);;

let ipoptportoptbool_render i =
  match i with
    None -> "NONE"
  | Some ((ip, port),b) ->
      sprintf "SOME((%s, %s),%s)" (ipoption_render ip) (portoption_render port) (bool_render b);;

let ipportoption_render i =
  match i with
    None -> "NONE"
  | Some(i,p) -> sprintf "SOME(%s, %s)" (ip_render i) (port_render p);;

let socktype_render r =
  match r with
    Ocamllib.SOCK_DGRAM -> "SOCK_DGRAM"
  | Ocamllib.SOCK_STREAM -> "SOCK_STREAM";;

let iplist_render iplist =
  let slist =
    let rec loop x=
      match x with
	[] -> []
      | (x::xs) -> (ip_render x)::(loop xs)
      in loop iplist
  in sprintf "[%s]" (String.concat "; " slist);;

let interface_render (ifid, ip, ips, nm) =
  sprintf "(%s, %s, %s, %s)" (ifid_render ifid) (ip_render ip) (iplist_render ips) (netmask_render nm);;

let interfacelist_render iflist =
  let slist =
    let rec loop x =
      match x with
	[] -> []
      | (x::xs) -> (interface_render x)::(loop xs)
      in loop iflist
  in sprintf "[%s]" (String.concat "; " slist);;

let sig_render s =
  match s with
    SIGABRT -> "SIGABRT"
  | SIGALRM -> "SIGALRM"
  | SIGBUS -> "SIGBUS"
  | SIGCHLD -> "SIGCHLD"
  | SIGCONT -> "SIGCONT"
  | SIGFPE -> "SIGFPE"
  | SIGHUP -> "SIGHUP"
  | SIGILL -> "SIGILL"
  | SIGINT -> "SIGINT"
  | SIGKILL -> "SIGKILL"
  | SIGPIPE -> "SIGPIPE"
  | SIGQUIT -> "SIGQUIT"
  | SIGSEGV -> "SIGSEGV"
  | SIGSTOP -> "SIGSTOP"
  | SIGTERM -> "SIGTERM"
  | SIGTSTP -> "SIGTSTP"
  | SIGTTIN -> "SIGTTIN"
  | SIGTTOU -> "SIGTTOU"
  | SIGUSR1 -> "SIGUSR1"
  | SIGUSR2 -> "SIGUSR2"
  | SIGPOLL -> "SIGPOLL"
  | SIGPROF -> "SIGPROF"
  | SIGSYS -> "SIGSYS"
  | SIGTRAP -> "SIGTRAP"
  | SIGURG -> "SIGURG"
  | SIGVTALRM -> "SIGVTALRM"
  | SIGXCPU -> "SIGXCPU"
  | SIGXFSZ -> "SUGXFSZ";;

let error_render e =
  match e with
    E2BIG -> "E2BIG"
  | EACCES -> "EACCES"
  | EADDRINUSE -> "EADDRINUSE"
  | EADDRNOTAVAIL -> "EADDRNOTAVAIL"
  | EAFNOSUPPORT -> "EAFNOSUPPORT"
  | EAGAIN -> "EAGAIN"
  | EWOULDBLOCK -> "EWOULDBLOCK"
  | EALREADY -> "EALREADY"
  | EBADF -> "EBADF"
  | EBADMSG -> "EBADMSG"
  | EBUSY -> "EBUSY"
  | ECANCELED -> "ECANCELED"
  | ECHILD -> "ECHILD"
  | ECONNABORTED -> "ECONNABORTED"
  | ECONNREFUSED -> "ECONNREFUSED"
  | ECONNRESET -> "ECONNRESET"
  | EDEADLK -> "EDEADLK"
  | EDESTADDRREQ -> "EDESTADDRREQ"
  | EDOM -> "EDOM"
  | EDQUOT -> "EDQUOT"
  | EEXIST -> "EEXIST"
  | EFAULT -> "EFAULT"
  | EFBIG -> "EFBIG"
  | EHOSTUNREACH -> "EHOSTUNREACH"
  | EIDRM -> "EIDRM"
  | EILSEQ -> "EILSEQ"
  | EINPROGRESS -> "EINPROGRESS"
  | EINTR -> "EINTR"
  | EINVAL -> "EINVAL"
  | EIO -> "EIO"
  | EISCONN -> "EISCONN"
  | EISDIR -> "EISDIR"
  | ELOOP -> "ELOOP"
  | EMFILE -> "EMFILE"
  | EMLINK -> "EMLINK"
  | EMSGSIZE -> "EMSGSIZE"
  | EMULTIHOP -> "EMULTIHOP"
  | ENAMETOOLONG -> "ENAMETOOLONG"
  | ENETDOWN -> "ENETDOWN"
  | ENETRESET -> "ENETRESET"
  | ENETUNREACH -> "ENETUNREACH"
  | ENFILE -> "ENFILE"
  | ENOBUFS -> "ENOBUFS"
  | ENODATA -> "ENODATA"
  | ENODEV -> "ENODEV"
  | ENOENT -> "ENOENT"
  | ENOEXEC -> "ENOEXEC"
  | ENOLCK -> "ENOLCM"
  | ENOLINK -> "NOLINK"
  | ENOMEM -> "ENOMEM"
  | ENOMSG -> "ENOMSG"
  | ENOPROTOOPT -> "ENOPROTOOPT"
  | ENOSPC -> "ENOSPC"
  | ENOSR -> "ENOSR"
  | ENOSTR -> "ENOSTR"
  | ENOSYS -> "ENOSYS"
  | ENOTCONN -> "ENOTCONN"
  | ENOTDIR -> "ENOTDIR"
  | ENOTEMPTY -> "ENOTEMPTY"
  | ENOTSOCK -> "ENOTSOCK"
  | ENOTSUP -> "ENOTSUP"
  | ENOTTY -> "ENOTTY"
  | ENXIO -> "ENXIO"
  | EOPNOTSUPP -> "EOPNOTSUPP"
  | EOVERFLOW -> "EOVERFLOW"
  | EPERM -> "EPERM"
  | EPIPE -> "EPIPE"
  | EPROTO -> "EPROTO"
  | EPROTONOSUPPORT -> "EPROTONOSUPPORT"
  | EPROTOTYPE -> "EPROTOTYPE"
  | ERANGE -> "ERANGE"
  | EROFS -> "EROFS"
  | ESPIPE -> "ESPIPE"
  | ESRCH -> "ESRCH"
  | ESTALE -> "ESTALE"
  | ETIME -> "ETIME"
  | ETIMEDOUT -> "ETIMEDOUT"
  | ETXTBSY -> "ETXTBSY"
  | EXDEV -> "EXDEV"
  | ESHUTDOWN -> "ESHUTDOWN"
  | EHOSTDOWN -> "EHOSTDOWN"
  | EUNKNOWN_UNIX_ERROR -> "EUNKNOWN_UNIX_ERROR"

let siglistopt_render s =
  match s with
    None -> "NONE"
  | Some siglist ->
      let slist =
	let rec loop y =
	  match y with
	    [] -> []
	  | (x::xs) -> (sig_render x)::(loop xs)
	in loop siglist
      in sprintf "SOME([%s])" (String.concat "; " slist);;


let lib_call_render_call lib =
  match lib with
    ACCEPT(fd) ->
      sprintf "accept(%s)" (fd_render fd)
  | BIND(fd,ipopt,portopt) ->
      sprintf "bind(%s, %s, %s)"
	(fd_render fd) (ipopt_render ipopt) (portopt_render portopt)
  | CONNECT(fd,ip,portopt) ->
      sprintf "connect(%s, %s, %s)"
	(fd_render fd) (ip_render ip) (portopt_render portopt)
  | CLOSE(fd) ->
      sprintf "close(%s)" (fd_render fd)
  | DISCONNECT(fd) ->
      sprintf "disconnect(%s)" (fd_render fd)
  | DUP(fd) ->
      sprintf "dup(%s)" (fd_render fd)
  | DUPFD(fd,fd2) ->
      sprintf "dupfd(%s, %s)" (fd_render fd) (render_int fd2)
  | GETFILEFLAGS(fd) ->
      sprintf "getfileflags(%s)" (fd_render fd)
  | SETFILEFLAGS(fd,  list) ->
      sprintf "setfileflags(%s, %s)" (fd_render fd) (fbflaglist_render list)
  | GETIFADDRS(_) ->
      sprintf "getifaddrs()"
  | GETSOCKNAME(fd) ->
      sprintf "getsockname(%s)" (fd_render fd)
  | GETPEERNAME(fd) ->
      sprintf "getpeername(%s)" (fd_render fd)
  | GETSOCKBOPT(fd, bflag) ->
      sprintf "getsockbopt(%s, %s)" (fd_render fd) (bflag_render bflag)
  | GETSOCKNOPT(fd, nflag) ->
      sprintf "getsocknopt(%s, %s)" (fd_render fd) (nflag_render nflag)
  | GETSOCKTOPT(fd, tflag) ->
      sprintf "getsocktopt(%s, %s)" (fd_render fd) (tflag_render tflag)
  | GETSOCKERR(fd) ->
      sprintf "getsockerr(%s)" (fd_render fd)
  | GETSOCKLISTENING(fd) ->
      sprintf "getsocklistening(%s)" (fd_render fd)
  | LISTEN(fd, i) ->
      sprintf "listen(%s, %s)" (fd_render fd) (render_int i)
  | RECV(fd, i, bflaglist) ->
      sprintf "recv(%s, %s, %s)" (fd_render fd) (render_int i) (msgbflaglist_render bflaglist)
  | PSELECT(fdl1,fdl2,fdl3,intpairopt,siglistopt) ->
      sprintf "pselect(%s, %s, %s, %s, %s)"
	(fdlist_render fdl1) (fdlist_render fdl2)
	(fdlist_render fdl3) (intpairopt_render intpairopt)
	(siglistopt_render siglistopt)
  | SEND(fd,ipport,str,bflaglist) ->
      sprintf "send(%s, %s, \"%s\", %s)"
	(fd_render fd) (ipportoption_render ipport) str (msgbflaglist_render bflaglist)
  | SETSOCKBOPT(fd,bflag,b) ->
      sprintf "setsockbopt(%s, %s, %s)" (fd_render fd) (bflag_render bflag)
	(bool_render b)
  | SETSOCKNOPT(fd,nflag,n) ->
      sprintf "setsocknopt(%s, %s, %s)"
	(fd_render fd) (nflag_render nflag) (render_int n)
  | SETSOCKTOPT(fd,tflag,t) ->
      sprintf "setsocktopt(%s, %s, %s)" (fd_render fd) (tflag_render tflag)
	(intpairopt_render t)
  | SHUTDOWN(fd,b1,b2) ->
      sprintf "shutdown(%s, %s, %s)" (fd_render fd) (bool_render b1)
	(bool_render b2)
  | SOCKATMARK(fd) ->
      sprintf "sockatmark(%s)" (fd_render fd)
  | SOCKET(st) ->
      sprintf "socket(%s)" (socktype_render st)

let lh_call_to_string lib tid =
  sprintf "Lh_call(%s, %s)" (tid_render tid) (lib_call_render_call lib)

let lib_call_render lib tid =
  lh_call_to_string lib tid ^ ";\n"

let lib_return_render_return libr =
  match libr with
    OK_UNIT(_) ->
      sprintf "OK()"
  | OK_FD(fd) ->
      sprintf "OK(%s)" (fd_render fd)
  | OK_BOOL(b) ->
      sprintf "OK(%s)" (bool_render b)
  | OK_INT(i) ->
      sprintf "OK(%s)" (render_int i)
  | OK_IP_PORT(ip,port) ->
      sprintf "OK(%s, %s)" (ip_render ip) (port_render port)
  | OK_IPOPT_PORTOPT(ips, ports) ->
      sprintf "OK(%s, %s)" (ipopt_render ips) (portopt_render ports)
  | OK_INT_INT_OPTION(x) ->
      sprintf "OK(%s)" (intpairopt_render x)
  | OK_FDLISTTRIPLE(f1,(f2,f3)) ->
      sprintf "OK(%s, (%s, %s))" (fdlist_render f1) (fdlist_render f2)
	(fdlist_render f3)
  | OK_STRING(s) ->
      sprintf "OK(\"%s\")" s
  | OK_FD_IP_PORT(fd,(ip,port)) ->
      sprintf "OK(%s, (%s, %s))" (fd_render fd) (ip_render ip)
	(port_render port)
  | OK_FILEFLAGLIST(flist) ->
      sprintf "OK(%s)" (fbflaglist_render flist)
  | OK_STRING_IP_PORT_BOOL(s, ipport) ->
      sprintf "OK(\"%s\", %s)"
        s (ipoptportoptbool_render ipport)
  | OK_INTERFACE_LIST(ifs) ->
      sprintf "OK(%s)" (interfacelist_render ifs)
  | FAIL(s) ->
      sprintf "FAIL(%s)" (error_render s)

let lh_return_to_string libr tid =
  sprintf "Lh_return(%s, %s)" (tid_render tid) (lib_return_render_return libr)

let lib_return_render libr tid =
  lh_return_to_string libr tid ^ ";\n"

(*
let lib_render_to_socket sd x =
  let s =
    match x with
      LIBCALL(tid,libcall) -> lib_call_render libcall tid
    | LIBRETURN(tid,libret) -> lib_return_render libret tid
    | _ -> raise(Fatal("Not a LIBCALL or LIBRETURN\n"))
  in Sock.write sd (" "^s);;
*)
