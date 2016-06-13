
module Print = struct

  let pp_libcall ppf v =
    let open Libcalls in
    let str = match v with
      | ACCEPT fd -> "accept"
      | BIND (fd, ipopt, portopt) -> "bind"
      | CLOSE fd -> "close"
      | CONNECT (fd, ip, portopt) -> "connect"
      | DISCONNECT fd -> "disconnect"
      | DUP fd -> "dup"
      | DUPFD (fd, n) -> "dupfd"
      | GETFILEFLAGS fd -> "getfileflags"
      | SETFILEFLAGS (fd, filebflags) -> "setfileflags"
      | GETIFADDRS () -> "getifaddrs"
      | GETSOCKNAME fd -> "getsockname"
      | GETPEERNAME fd -> "getpeername"
      | GETSOCKBOPT (fd, sockbflag) -> "getsockbopt"
      | GETSOCKNOPT (fd, socknflag) -> "getsocknopt"
      | GETSOCKTOPT (fd, socktflag) -> "getsocktopt"
      | GETSOCKERR fd -> "getsockerr"
      | GETSOCKLISTENING fd -> "getsocklistening"
      | LISTEN (fd, n) -> "listen"
      | RECV (fd, n, msgbflags) -> "recv"
      | PSELECT (readfds, writefds, exceptfds, timeout, sigmask) -> "pselect"
      | SEND (fd, ipportopt, data, msgbflags) -> "send"
      | SETSOCKBOPT (fd, sockbflag, b) -> "setsockbopt"
      | SETSOCKNOPT (fd, socknflag, n) -> "setsocknopt"
      | SETSOCKTOPT (fd, socktflag, vopt) -> "setsocktopt"
      | SHUTDOWN (fd, a, b) -> "shutdown"
      | SOCKATMARK fd -> "sockatmark"
      | SOCKET sockt -> "socket"
    in
    Format.pp_print_string ppf str

  let err_to_str =
    let open Ocamllib in
    function
    | E2BIG -> "e2big"
    | EACCES -> "eacces"
    | EADDRINUSE -> "eaddrinuse"
    | EADDRNOTAVAIL -> "eaddrnotavail"
    | EAFNOSUPPORT -> "eafnosupport"
    | EAGAIN -> "eagain"
    | EWOULDBLOCK -> "ewouldblock"
    | EALREADY -> "ealready"
    | EBADF -> "ebadf"
    | EBADMSG -> "ebadmsg"
    | EBUSY -> "ebusy"
    | ECANCELED -> "ecanceled"
    | ECHILD -> "echild"
    | ECONNABORTED -> "econnaborted"
    | ECONNREFUSED -> "econnrefused"
    | ECONNRESET -> "econnreset"
    | EDEADLK -> "edeadlk"
    | EDESTADDRREQ -> "edestaddrreq"
    | EDOM -> "edom"
    | EDQUOT -> "edquot"
    | EEXIST -> "eexist"
    | EFAULT -> "efault"
    | EFBIG -> "efbig"
    | EHOSTUNREACH -> "ehostunreach"
    | EIDRM -> "eidrm"
    | EILSEQ -> "eilseq"
    | EINPROGRESS -> "einprogress"
    | EINTR -> "eintr"
    | EINVAL -> "einval"
    | EIO -> "eio"
    | EISCONN -> "eisconn"
    | EISDIR -> "eisdir"
    | ELOOP -> "eloop"
    | EMFILE -> "emfile"
    | EMLINK -> "emlink"
    | EMSGSIZE -> "emsgsize"
    | EMULTIHOP -> "emultihop"
    | ENAMETOOLONG -> "enametoolong"
    | ENETDOWN -> "enetdown"
    | ENETRESET -> "enetreset"
    | ENETUNREACH -> "enetunreach"
    | ENFILE -> "enfile"
    | ENOBUFS -> "enobufs"
    | ENODATA -> "enodata"
    | ENODEV -> "enodev"
    | ENOENT -> "enoent"
    | ENOEXEC -> "enoexec"
    | ENOLCK -> "enolck"
    | ENOLINK -> "enolink"
    | ENOMEM -> "enomem"
    | ENOMSG -> "enomsg"
    | ENOPROTOOPT -> "enoprotopt"
    | ENOSPC -> "enospc"
    | ENOSR -> "enosr"
    | ENOSTR -> "enostr"
    | ENOSYS -> "enosys"
    | ENOTCONN -> "enotconn"
    | ENOTDIR -> "enotdir"
    | ENOTEMPTY -> "enotempty"
    | ENOTSOCK -> "enotsock"
    | ENOTSUP -> "enotsup"
    | ENOTTY -> "enotty"
    | ENXIO -> "enxio"
    | EOPNOTSUPP -> "eopnotsupp"
    | EOVERFLOW -> "eoverflow"
    | EPERM -> "eperm"
    | EPIPE -> "epipe"
    | EPROTO -> "eproto"
    | EPROTONOSUPPORT -> "eprotonosupport"
    | EPROTOTYPE -> "eprototype"
    | ERANGE -> "erange"
    | EROFS -> "erofs"
    | ESPIPE -> "espipe"
    | ESRCH -> "esrch"
    | ESTALE -> "estale"
    | ETIME -> "etime"
    | ETIMEDOUT -> "etimedout"
    | ETXTBSY -> "etxtbsy"
    | EXDEV -> "exdev"
    | ESHUTDOWN -> "eshutdown"
    | EHOSTDOWN -> "ehostdown"
    | EUNKNOWN_UNIX_ERROR -> "eunknown_unix_error"

  let pp_libreturn ppf v =
    let open Libcalls in
    let str = match v with
      | OK_UNIT () -> "ok_unit"
      | OK_FD fd -> "ok_fd"
      | OK_BOOL b -> "ok_bool"
      | OK_INT n -> "ok_int"
      | OK_IP_PORT (ip, port) -> "ok_ip_port"
      | OK_IPOPT_PORTOPT (ipopt, portopt) -> "ok_ipopt_portopt"
      | OK_INT_INT_OPTION intintopt -> "ok_int_int_option"
      | OK_FDLISTTRIPLE fdlists -> "ok_fdlisttriple"
      | OK_STRING s -> "ok_string"
      | OK_FD_IP_PORT (fd, (ip, port)) -> "ok_fd_ip_port"
      | OK_FILEFLAGLIST filebflags -> "ok_fileflaglist"
      | OK_STRING_IP_PORT_BOOL (s, opts) -> "ok_string_ip_port_bool"
      | OK_INTERFACE_LIST ifs -> "ok_interface_list"
      | FAIL err -> "fail " ^ err_to_str err
    in
    Format.pp_print_string ppf str

  let pp_hol ppf =
    let open Holtypes in
    function
    | TCPMSG tcp -> Format.pp_print_string ppf "tcp segment"
    | UDPMSG udp -> Format.pp_print_string ppf "udp message"
    | ICMPMSG icmp -> Format.pp_print_string ppf "icmp"

  let tcpstate_to_str =
    let open Tcpcbtypes in
    function
    | TCPCB_CLOSED -> "closed"
    | TCPCB_LISTEN -> "listen"
    | TCPCB_SYN_SENT -> "syn_sent"
    | TCPCB_SYN_RCVD -> "syn_rcvd"
    | TCPCB_ESTABLISHED -> "established"
    | TCPCB_CLOSE_WAIT -> "close_wait"
    | TCPCB_FIN_WAIT_1 -> "fin_wait_1"
    | TCPCB_CLOSING -> "closing"
    | TCPCB_LAST_ACK -> "last_ack"
    | TCPCB_FIN_WAIT_2 -> "fin_wait_2"
    | TCPCB_TIME_WAIT -> "time_wait"

  let tcpaction_to_str =
    let open Tcpcbtypes in
    function
    | TA_OUTPUT -> "output"
    | TA_INPUT -> "input"
    | TA_USER -> "user"
    | TA_RESPOND -> "respond"
    | TA_DROP -> "drop"

  let pp_trace ppf (tcpaction, tracesid, traceaddr, tcpstate, tcpcb) =
    Format.fprintf ppf "trace action %s state %s"
      (tcpaction_to_str tcpaction) (tcpstate_to_str tcpstate)

  let pp ppf =
    let open Parserlib in
    function
    | HOLSNDMSG h -> Format.fprintf ppf "holsend %a" pp_hol h
    | HOLLOOPMSG h -> Format.fprintf ppf "holloop %a" pp_hol h
    | HOLRCVMSG h -> Format.fprintf ppf "holrecv %a" pp_hol h
    | LIBCALL (_, lc) -> Format.fprintf ppf "libcall %a" pp_libcall lc
    | LIBRETURN (_, lr) -> Format.fprintf ppf "libreturn %a" pp_libreturn lr
    | TCPTRACE t -> pp_trace ppf t
    | HOLEPSILON _ -> Format.pp_print_string ppf "holepsilon"
    | HOLABSTIME _ -> Format.pp_print_string ppf "holabstime"
end

module Comparison = struct
  let same_holmsg a b =
    (* XXX: more fine-grained comparison *)
    let open Holtypes in
    match a, b with
    | TCPMSG _, TCPMSG _ -> true (* tcp_segment *)
    | UDPMSG _, UDPMSG _ -> true (* udp_datagram_hol *)
    | ICMPMSG _, ICMPMSG _ -> true (* icmp_message_hol *)
    | _ -> false

  let same_libcall (_, a) (_, b) =
    (* XXX: more fine-grained comparison *)
    let open Libcalls in
    match a, b with
    | ACCEPT _, ACCEPT _ -> true (* fd *)
    | BIND _, BIND _ -> true (* fd * ip option * port option *)
    | CLOSE _, CLOSE _ -> true (* fd *)
    | CONNECT _, CONNECT _ -> true (* fd * ip * port option *)
    | DISCONNECT _, DISCONNECT _ -> true (* fd *)
    | DUP _, DUP _ -> true (* fd *)
    | DUPFD _, DUPFD _ -> true (* fd * int *)
    | GETFILEFLAGS _, GETFILEFLAGS _ -> true (* fd *)
    | SETFILEFLAGS _, SETFILEFLAGS _ -> true (* fd * filebflag list *)
    | GETIFADDRS (), GETIFADDRS () -> true
    | GETSOCKNAME _, GETSOCKNAME _ -> true (* fd *)
    | GETPEERNAME _, GETPEERNAME _ -> true (* fd *)
    | GETSOCKBOPT _, GETSOCKBOPT _ -> true (* fd * sockbflag *)
    | GETSOCKNOPT _, GETSOCKNOPT _ -> true (* fd * socknflag *)
    | GETSOCKTOPT _, GETSOCKTOPT _ -> true (* fd * socktflag *)
    | GETSOCKERR _, GETSOCKERR _ -> true (* fd *)
    | GETSOCKLISTENING _, GETSOCKLISTENING _ -> true (* fd *)
    | LISTEN _, LISTEN _ -> true (* fd * int *)
    | RECV _, RECV _ -> true (* fd * int * msgbflag list *)
    | PSELECT _, PSELECT _ -> true (* fd list * fd list * fd list * (int * int) option * signal list option *)
    | SEND _, SEND _ -> true (* fd * (ip * port) option * string * msgbflag list *)
    | SETSOCKBOPT _, SETSOCKBOPT _ -> true (* fd * sockbflag * bool *)
    | SETSOCKNOPT _, SETSOCKNOPT _ -> true (* fd * socknflag * int *)
    | SETSOCKTOPT _, SETSOCKTOPT _ -> true (* fd * socktflag * (int * int) option *)
    | SHUTDOWN _, SHUTDOWN _ -> true (* fd * bool * bool *)
    | SOCKATMARK _, SOCKATMARK _ -> true (* fd *)
    | SOCKET _, SOCKET _ -> true (* sock_type *)
    | _ -> false

  let same_error a b =
    let open Ocamllib in
    match a, b with
    | E2BIG, E2BIG -> true
    | EACCES, EACCES -> true
    | EADDRINUSE, EADDRINUSE -> true
    | EADDRNOTAVAIL, EADDRNOTAVAIL -> true
    | EAFNOSUPPORT, EAFNOSUPPORT -> true
    | EAGAIN, EAGAIN -> true
    | EWOULDBLOCK, EWOULDBLOCK -> true
    | EALREADY, EALREADY -> true
    | EBADF, EBADF -> true
    | EBADMSG, EBADMSG -> true
    | EBUSY, EBUSY -> true
    | ECANCELED, ECANCELED -> true
    | ECHILD, ECHILD -> true
    | ECONNABORTED, ECONNABORTED -> true
    | ECONNREFUSED, ECONNREFUSED -> true
    | ECONNRESET, ECONNRESET -> true
    | EDEADLK, EDEADLK -> true
    | EDESTADDRREQ, EDESTADDRREQ -> true
    | EDOM, EDOM -> true
    | EDQUOT, EDQUOT -> true
    | EEXIST, EEXIST -> true
    | EFAULT, EFAULT -> true
    | EFBIG, EFBIG -> true
    | EHOSTUNREACH, EHOSTUNREACH -> true
    | EIDRM, EIDRM -> true
    | EILSEQ, EILSEQ -> true
    | EINPROGRESS, EINPROGRESS -> true
    | EINTR, EINTR -> true
    | EINVAL, EINVAL -> true
    | EIO, EIO -> true
    | EISCONN, EISCONN -> true
    | EISDIR, EISDIR -> true
    | ELOOP, ELOOP -> true
    | EMFILE, EMFILE -> true
    | EMLINK, EMLINK -> true
    | EMSGSIZE, EMSGSIZE -> true
    | EMULTIHOP, EMULTIHOP -> true
    | ENAMETOOLONG, ENAMETOOLONG -> true
    | ENETDOWN, ENETDOWN -> true
    | ENETRESET, ENETRESET -> true
    | ENETUNREACH, ENETUNREACH -> true
    | ENFILE, ENFILE -> true
    | ENOBUFS, ENOBUFS -> true
    | ENODATA, ENODATA -> true
    | ENODEV, ENODEV -> true
    | ENOENT, ENOENT -> true
    | ENOEXEC, ENOEXEC -> true
    | ENOLCK, ENOLCK -> true
    | ENOLINK, ENOLINK -> true
    | ENOMEM, ENOMEM -> true
    | ENOMSG, ENOMSG -> true
    | ENOPROTOOPT, ENOPROTOOPT -> true
    | ENOSPC, ENOSPC -> true
    | ENOSR, ENOSR -> true
    | ENOSTR, ENOSTR -> true
    | ENOSYS, ENOSYS -> true
    | ENOTCONN, ENOTCONN -> true
    | ENOTDIR, ENOTDIR -> true
    | ENOTEMPTY, ENOTEMPTY -> true
    | ENOTSOCK, ENOTSOCK -> true
    | ENOTSUP, ENOTSUP -> true
    | ENOTTY, ENOTTY -> true
    | ENXIO, ENXIO -> true
    | EOPNOTSUPP, EOPNOTSUPP -> true
    | EOVERFLOW, EOVERFLOW -> true
    | EPERM, EPERM -> true
    | EPIPE, EPIPE -> true
    | EPROTO, EPROTO -> true
    | EPROTONOSUPPORT, EPROTONOSUPPORT -> true
    | EPROTOTYPE, EPROTOTYPE -> true
    | ERANGE, ERANGE -> true
    | EROFS, EROFS -> true
    | ESPIPE, ESPIPE -> true
    | ESRCH, ESRCH -> true
    | ESTALE, ESTALE -> true
    | ETIME, ETIME -> true
    | ETIMEDOUT, ETIMEDOUT -> true
    | ETXTBSY, ETXTBSY -> true
    | EXDEV, EXDEV -> true
    | ESHUTDOWN, ESHUTDOWN -> true
    | EHOSTDOWN, EHOSTDOWN -> true
    | EUNKNOWN_UNIX_ERROR, EUNKNOWN_UNIX_ERROR -> true
    | _ -> false

  let same_libreturn (_, a) (_, b) =
    (* XXX: more fine-grained comparison *)
    let open Libcalls in
    match a, b with
    | OK_UNIT (), OK_UNIT () -> true
    | OK_FD _, OK_FD _ -> true (* fd *)
    | OK_BOOL _, OK_BOOL _ -> true (* bool *)
    | OK_INT _, OK_INT _ -> true (* int *)
    | OK_IP_PORT _, OK_IP_PORT _ -> true (* (ip * port) *)
    | OK_IPOPT_PORTOPT _, OK_IPOPT_PORTOPT _ -> true (* (ip option * port option) *)
    | OK_INT_INT_OPTION _, OK_INT_INT_OPTION _ -> true (* (int * int) option *)
    | OK_FDLISTTRIPLE _, OK_FDLISTTRIPLE _ -> true (* (fd list * (fd list * fd list)) *)
    | OK_STRING _, OK_STRING _ -> true (* string *)
    | OK_FD_IP_PORT _, OK_FD_IP_PORT _ -> true (* (fd * (ip * port)) *)
    | OK_FILEFLAGLIST _, OK_FILEFLAGLIST _ -> true (* filebflag list *)
    | OK_STRING_IP_PORT_BOOL _, OK_STRING_IP_PORT_BOOL _ -> true (* (string * ((ip option * port option) * bool) option) *)
    | OK_INTERFACE_LIST _, OK_INTERFACE_LIST _ -> true (* (ifid * ip * ip list * netmask) list *)
    | FAIL e1, FAIL e2 -> same_error e1 e2
    | _ -> false

  let same_tcptrace (a1, _, _, s1, cb1) (a2, _, _, s2, cb2) =
    (* tcpaction * tracesid * traceaddr * tcpstate * tcpcb *)
    let open Tcpcbtypes in
    let same_action a b = match a, b with
      | TA_OUTPUT, TA_OUTPUT
      | TA_INPUT, TA_INPUT
      | TA_USER, TA_USER
      | TA_RESPOND, TA_RESPOND
      | TA_DROP, TA_DROP -> true
      | _ -> false
    and same_state a b = match a, b with
      | TCPCB_CLOSED, TCPCB_CLOSED
      | TCPCB_LISTEN, TCPCB_LISTEN
      | TCPCB_SYN_SENT, TCPCB_SYN_SENT
      | TCPCB_SYN_RCVD, TCPCB_SYN_RCVD
      | TCPCB_ESTABLISHED, TCPCB_ESTABLISHED
      | TCPCB_CLOSE_WAIT, TCPCB_CLOSE_WAIT
      | TCPCB_FIN_WAIT_1, TCPCB_FIN_WAIT_1
      | TCPCB_CLOSING, TCPCB_CLOSING
      | TCPCB_LAST_ACK, TCPCB_LAST_ACK
      | TCPCB_FIN_WAIT_2, TCPCB_FIN_WAIT_2
      | TCPCB_TIME_WAIT, TCPCB_TIME_WAIT -> true
      | _ -> false
    and same_cb a b = true (* XXX: TODO *)
    in
    same_action a1 a2 && same_state s1 s2 && same_cb cb1 cb2

  let same a b =
    let open Parserlib in
    match a, b with
    | HOLSNDMSG a, HOLSNDMSG b -> same_holmsg a b
    | HOLLOOPMSG a, HOLLOOPMSG b -> same_holmsg a b
    | HOLRCVMSG a, HOLRCVMSG b -> same_holmsg a b
    | LIBCALL a, LIBCALL b -> same_libcall a b
    | LIBRETURN a, LIBRETURN b -> same_libreturn a b
    | TCPTRACE a, TCPTRACE b -> same_tcptrace a b
    | _ -> false
end

let take n xs =
  let rec more n xs acc =
    match n, xs with
    | 0, _ -> List.rev acc
    | _, x::xs -> more (pred n) xs (x::acc)
    | _, [] -> invalid_arg "n > |xs|"
  in
  more n xs []

let equal_len xs ys =
  let xlen = List.length xs
  and ylen = List.length ys
  in
  if xlen = ylen then
    (xs, ys)
  else if xlen > ylen then
    (Printf.printf "cutting first from %d downto %d\n" xlen ylen ;
     (take ylen xs, ys))
  else
    (Printf.printf "cutting second from %d downto %d\n" ylen xlen ;
     (xs, take xlen ys))

let diff fst snd =
  let r, _ =
    List.fold_left (fun (r, idx) (a, b) ->
        if r then
          if Comparison.same a b then
            (r, succ idx)
          else
            (Format.fprintf Format.std_formatter "comparison failed at event %d (excluding epsilon)\n%a <> %a\n" idx Print.pp a Print.pp b;
             (false, succ idx))
        else
          (r, succ idx))
      (true, 1) (List.combine fst snd)
  in
  if r then print_endline "same" else print_endline "different"

let parse ch =
  let acc = ref [] in
  let env = Threadparsing.create_parse_env () in
  try
    let lexbuf = Lexing.from_channel ch in
    let rec p1 allow_ts =
      let open Parserlib in
      match Parser.main env Lexer.token lexbuf with
      | PARSE_RETURN(_, _, r) -> (match r with
          | HOLEPSILON _ when allow_ts -> p1 false
          | HOLEPSILON _ -> invalid_arg "multiple epsilons"
          | HOLABSTIME _ -> p1 true
          | x -> acc := x :: !acc ; p1 true)
    in
    p1 true
  with Lexer.Eof -> List.rev !acc

let main fst snd =
  let parse1 file =
    let fd = Unix.openfile file [Unix.O_RDONLY] 0 in
    let ch = Unix.in_channel_of_descr fd in
    let r = parse ch in
    Unix.close fd ;
    r
  in
  let xs = parse1 fst
  and ys = parse1 snd
  in
  let xs, ys = equal_len xs ys in
  diff xs ys

let _ =
  match Sys.argv with
  | [| _ ; fst ; snd |] -> main fst snd
  | _ -> print_endline "need two arguments!"

