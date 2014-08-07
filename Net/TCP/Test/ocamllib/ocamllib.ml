type error =
    E2BIG
  | EACCES
  | EADDRINUSE
  | EADDRNOTAVAIL
  | EAFNOSUPPORT
  | EAGAIN
  | EWOULDBLOCK (* now assuming that EWOULDBLOCK = EAGAIN so should never be used *)
  | EALREADY
  | EBADF
  | EBADMSG
  | EBUSY
  | ECANCELED
  | ECHILD
  | ECONNABORTED
  | ECONNREFUSED
  | ECONNRESET
  | EDEADLK
  | EDESTADDRREQ
  | EDOM
  | EDQUOT
  | EEXIST
  | EFAULT
  | EFBIG
  | EHOSTUNREACH
  | EIDRM
  | EILSEQ
  | EINPROGRESS
  | EINTR
  | EINVAL
  | EIO
  | EISCONN
  | EISDIR
  | ELOOP
  | EMFILE
  | EMLINK
  | EMSGSIZE
  | EMULTIHOP
  | ENAMETOOLONG
  | ENETDOWN
  | ENETRESET
  | ENETUNREACH
  | ENFILE
  | ENOBUFS
  | ENODATA
  | ENODEV
  | ENOENT
  | ENOEXEC
  | ENOLCK
  | ENOLINK
  | ENOMEM
  | ENOMSG
  | ENOPROTOOPT
  | ENOSPC
  | ENOSR
  | ENOSTR
  | ENOSYS
  | ENOTCONN
  | ENOTDIR
  | ENOTEMPTY
  | ENOTSOCK
  | ENOTSUP
  | ENOTTY
  | ENXIO
  | EOPNOTSUPP
  | EOVERFLOW
  | EPERM
  | EPIPE
  | EPROTO
  | EPROTONOSUPPORT
  | EPROTOTYPE
  | ERANGE
  | EROFS
  | ESPIPE
  | ESRCH
  | ESTALE
  | ETIME
  | ETIMEDOUT
  | ETXTBSY
  | EXDEV
  | ESHUTDOWN
  | EHOSTDOWN
  | EUNKNOWN_UNIX_ERROR


exception Unix_error of error * string * string

let _ = Callback.register_exception "Ocamllib.Unix_error"
                                    (Unix_error(E2BIG, "", ""))

external error_message : error -> string = "unix_error_message"

let handle_unix_error f arg =
  try
    f arg
  with Unix_error(err, fun_name, arg) ->
    prerr_string Sys.argv.(0);
    prerr_string ": \"";
    prerr_string fun_name;
    prerr_string "\" failed";
    if String.length arg > 0 then begin
      prerr_string " on \"";
      prerr_string arg;
      prerr_string "\""
    end;
    prerr_string ": ";
    prerr_endline (error_message err);
    exit 2

(** {2 Signals types} *)
type signal =
    SIGABRT
  | SIGALRM
  | SIGBUS
  | SIGCHLD
  | SIGCONT
  | SIGFPE
  | SIGHUP
  | SIGILL
  | SIGINT
  | SIGKILL
  | SIGPIPE
  | SIGQUIT
  | SIGSEGV
  | SIGSTOP
  | SIGTERM
  | SIGTSTP
  | SIGTTIN
  | SIGTTOU
  | SIGUSR1
  | SIGUSR2
  | SIGPOLL    (* XSI only *)
  | SIGPROF    (* XSI only *)
  | SIGSYS     (* XSI only *)
  | SIGTRAP    (* XSI only *)
  | SIGURG
  | SIGVTALRM  (* XSI only *)
  | SIGXCPU    (* XSI only *)
  | SIGXFSZ    (* XSI only *)


(** {2 Socket types} *)

type fd
(** The abstract type of file descriptors *)

type ip
(** The abstract type of ip addresses *)

type port
(** The abstract type of inet ports *)

type tid
(** The abstract type of tids *)

type netmask
(** The abstract type of netmask *)

type ifid
(** The abstract type of ifids *)

type filebflag =
    O_NONBLOCK
  | O_ASYNC

type sockbflag =
    SO_BSDCOMPAT
  | SO_REUSEADDR
  | SO_KEEPALIVE
  | SO_OOBINLINE
  | SO_DONTROUTE
  | SO_BROADCAST (* NB this is not in the HOL model *)

type socknflag =
    SO_SNDBUF
  | SO_RCVBUF
  | SO_SNDLOWAT
  | SO_RCVLOWAT

type socktflag =
    SO_LINGER
  | SO_SNDTIMEO
  | SO_RCVTIMEO

type msgbflag =
    MSG_PEEK
  | MSG_OOB
  | MSG_WAITALL
  | MSG_DONTWAIT

type sock_type =
    SOCK_DGRAM
  | SOCK_STREAM


(** {2 Useful socket functions} *)

external ip_of_string : string -> ip = "nssock_ipofstring"
(** Conversion between string with format |XXX.YYY.ZZZ.TTT|
  and ip addresses. [ip_of_string] raises [Failure] when
  given a string that does not match this format. *)

external string_of_ip : ip -> string = "nssock_stringofip"
(** See {!Nssock.ip_of_string}. *)

external port_of_int: int -> port = "nssock_portofint"
(** Conversion between an int and ports *)

external int_of_port: port -> int = "nssock_intofport"
(** Conversion between a port and an int *)

external fd_of_int_private: int -> fd = "nssock_fdofint"
(** Conversion between an int and a fd *)

external int_of_fd: fd -> int = "nssock_intoffd"
(** Conversion between a fd and an int *)

external gettid: unit -> tid = "nssock_gettid"
(** Returns the process id *)

external int_of_tid: tid -> int = "nssock_int_of_tid"
(** Converts the tid into an int *)

external tid_of_int_private: int -> tid = "nssock_tid_of_int"
(** Converts the int into a tid *)

external ifid_of_string : string -> ifid = "nssock_ifidofstring"
(** Converts the string into an ifid *)

external string_of_ifid : ifid -> string = "nssock_stringofifid"
(** Converts the ifid into a string *)

external netmask_of_int : int -> netmask = "nssock_netmaskofint"
(** Converts the int into a netmask *)

external int_of_netmask : netmask -> int = "nssock_intofnetmask"
(** Converts the netmask into an int *)

(** {2 Socket Calls} *)

external accept: fd -> fd * (ip * port) = "nssock_accept"

external bind: fd -> ip option -> port option -> unit = "nssock_bind"

external close: fd -> unit = "nssock_close"
external connect: fd -> ip -> port option -> unit = "nssock_connect"
external disconnect: fd -> unit = "nssock_disconnect"
external dup: fd -> fd = "nssock_dup"
external dupfd: fd -> int -> fd = "nssock_dup2"

external getfileflags: fd -> filebflag list = "nssock_getfileflags"
external setfileflags: fd -> filebflag list -> unit = "nssock_setfileflags"

external getifaddrs: unit -> (ifid * ip * ip list * netmask) list = "nssock_getifaddrs"

external getsockname: fd -> ip option * port option = "nssock_getsockname"
external getpeername: fd -> ip * port = "nssock_getpeername"
external getsockbopt: fd -> sockbflag -> bool = "nssock_getsockbopt"
external getsocknopt: fd -> socknflag -> int = "nssock_getsocknopt"
external getsocktopt: fd -> socktflag -> (int * int) option = "nssock_getsocktopt"
external getsockerr: fd -> unit = "nssock_getsockerr"
external getsocklistening: fd -> bool = "nssock_getsocklistening"
external listen: fd -> int -> unit = "nssock_listen"

external recv: fd -> int -> msgbflag list -> (string * ((ip option * port option) * bool) option) = "nssock_recv"

external pselect: fd list -> fd list -> fd list -> (int * int) option ->
  signal list option -> fd list * (fd list * fd list) = "nssock_pselect"

external send: fd -> (ip * port) option -> string -> msgbflag list -> string = "nssock_send"

external setsockbopt: fd -> sockbflag -> bool -> unit = "nssock_setsockbopt"
external setsocknopt: fd -> socknflag -> int -> unit = "nssock_setsocknopt"
external setsocktopt: fd -> socktflag -> (int * int) option -> unit = "nssock_setsocktopt"

external shutdown: fd -> bool -> bool -> unit = "nssock_shutdown"
external sockatmark: fd -> bool = "nssock_sockatmark"
external socket: sock_type -> fd = "nssock_socket"

























