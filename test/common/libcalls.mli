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

val makelibcalls: libstructure -> libreturnstructure
