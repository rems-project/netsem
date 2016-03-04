open Ocamllib

type libstructure =
    ACCEPT of fd
  | BIND of fd * ip option * port option
  | CLOSE of fd
  | CONNECT of fd * ip * port option
  | DISCONNECT of fd
  | DUP of fd
  | DUPFD of fd * int
  | GETFILEFLAGS of fd
  | SETFILEFLAGS of fd * filebflag list
  | GETIFADDRS of unit
  | GETSOCKNAME of fd
  | GETPEERNAME of fd
  | GETSOCKBOPT of fd * sockbflag
  | GETSOCKNOPT of fd * socknflag
  | GETSOCKTOPT of fd * socktflag
  | GETSOCKERR of fd
  | GETSOCKLISTENING of fd
  | LISTEN of fd * int
  | RECV of fd * int * msgbflag list
  | PSELECT of fd list * fd list * fd list * (int * int) option * signal list option
  | SEND of fd * (ip * port) option * string * msgbflag list
  | SETSOCKBOPT of fd * sockbflag * bool
  | SETSOCKNOPT of fd * socknflag * int
  | SETSOCKTOPT of fd * socktflag * (int * int) option
  | SHUTDOWN of fd * bool * bool
  | SOCKATMARK of fd
  | SOCKET of sock_type


type libreturnstructure =
    OK_UNIT of unit
  | OK_FD of fd
  | OK_BOOL of bool
  | OK_INT of int
  | OK_IP_PORT of (ip * port)
  | OK_IPOPT_PORTOPT of (ip option * port option)
  | OK_INT_INT_OPTION of (int * int) option
  | OK_FDLISTTRIPLE of (fd list * (fd list * fd list))
  | OK_STRING of string
  | OK_FD_IP_PORT of (fd * (ip * port))
  | OK_FILEFLAGLIST of filebflag list
  | OK_STRING_IP_PORT_BOOL of (string * ((ip option * port option) * bool) option)
  | OK_INTERFACE_LIST of (ifid * ip * ip list * netmask) list
  | FAIL of Ocamllib.error

let makelibcalls c =
  try
  match c with
    ACCEPT(fd) ->
      OK_FD_IP_PORT (Ocamllib.accept fd)
  | BIND(fd,ipopt,portopt) ->
      OK_UNIT (Ocamllib.bind fd ipopt portopt)
  | CLOSE(fd) ->
      OK_UNIT (Ocamllib.close fd)
  | CONNECT(fd,ip,port) ->
      OK_UNIT (Ocamllib.connect fd ip port)
  | DISCONNECT(fd) ->
      OK_UNIT (Ocamllib.disconnect fd)
  | DUP(fd) ->
      OK_FD (Ocamllib.dup fd)
  | DUPFD(fd1,fd2) ->
      OK_FD (Ocamllib.dupfd fd1 fd2)
  | GETFILEFLAGS(fd) ->
      OK_FILEFLAGLIST (Ocamllib.getfileflags fd)
  | SETFILEFLAGS(fd, flaglist) ->
      OK_UNIT (Ocamllib.setfileflags fd flaglist)
  | GETIFADDRS () ->
      OK_INTERFACE_LIST(Ocamllib.getifaddrs ())
  | GETSOCKNAME(fd) ->
      OK_IPOPT_PORTOPT (Ocamllib.getsockname fd)
  | GETPEERNAME(fd) ->
      OK_IP_PORT (Ocamllib.getpeername fd)
  | GETSOCKBOPT(fd, bflag) ->
      OK_BOOL (Ocamllib.getsockbopt fd bflag)
  | GETSOCKNOPT(fd, nflag) ->
      OK_INT (Ocamllib.getsocknopt fd nflag)
  | GETSOCKTOPT(fd, tflag) ->
      OK_INT_INT_OPTION (Ocamllib.getsocktopt fd tflag)
  | GETSOCKERR(fd) ->
      OK_UNIT (Ocamllib.getsockerr fd)
  | GETSOCKLISTENING(fd)->
      OK_BOOL (Ocamllib.getsocklistening fd)
  | LISTEN(fd, n) ->
      OK_UNIT (Ocamllib.listen fd n)
  | RECV(fd, sz, bflaglist) ->
      OK_STRING_IP_PORT_BOOL (Ocamllib.recv fd sz bflaglist)
  | PSELECT(fds1,fds2,fds3,opt,siglistopt) ->
      OK_FDLISTTRIPLE (Ocamllib.pselect fds1 fds2 fds3 opt siglistopt)
  | SEND(fd,ipportop,str,bflaglist) ->
      OK_STRING (Ocamllib.send fd ipportop str bflaglist)
  | SETSOCKBOPT(fd,bflag,b) ->
      OK_UNIT (Ocamllib.setsockbopt fd bflag b)
  | SETSOCKNOPT(fd,nflag,n) ->
      OK_UNIT (Ocamllib.setsocknopt fd nflag n)
  | SETSOCKTOPT(fd,tflag,opt) ->
      OK_UNIT (Ocamllib.setsocktopt fd tflag opt)
  | SHUTDOWN(fd,b1,b2) ->
      OK_UNIT (Ocamllib.shutdown fd b1 b2)
  | SOCKATMARK(fd) ->
      OK_BOOL (Ocamllib.sockatmark fd)
  | SOCKET(st) ->
      OK_FD (Ocamllib.socket st)
  with Unix_error(e,s1,s2) -> FAIL(e)



