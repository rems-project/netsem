type error =
    E2BIG
  | EACCES
  | EADDRINUSE
  | EADDRNOTAVAIL
  | EAFNOSUPPORT
  | EAGAIN
  | EWOULDBLOCK
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
(** Raised by the system calls below when an error is encountered.
   The first component is the error code; the second component
   is the function name; the third component is the string parameter
   to the function, if it has one, or the empty string otherwise. *)

val error_message : error -> string
(** Return a string describing the given error code. *)

val handle_unix_error : ('a -> 'b) -> 'a -> 'b
(** [handle_unix_error f x] applies [f] to [x] and returns the result.
   If the exception [Unix_error] is raised, it prints a message
   describing the error and exits with code 2. *)


(** {2 Dreaded signals types} *)
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

val ip_of_string: string -> ip
(** Conversion between string with format |XXX.YYY.ZZZ.TTT|
  and ip addresses. [ip_of_string] raises [Failure] when
  given a string that does not match this format. *)

val string_of_ip: ip -> string
(** See {!Nssock.ip_of_string}. *)

val port_of_int: int -> port
(** Conversion between an int and ports *)

val int_of_port: port -> int
(** Conversion between a port and an int *)

val fd_of_int_private: int -> fd
(** THIS IS A PRIVATE FUNCTION -- DO NOT USE OR ELSE!!!!! *)
(** Conversion between an int and a fd *)

val int_of_fd: fd -> int
(** COnversion between a fd and an int *)

val gettid: unit -> tid
(** Returns the process id *)

val int_of_tid: tid -> int
(** Converts the tid into an int *)

val tid_of_int_private: int -> tid
(** Converts the int into a tid *)

val ifid_of_string : string -> ifid
(** Converts the string into an ifid *)

val string_of_ifid : ifid -> string
(** Converts the ifid into a string *)

val netmask_of_int : int -> netmask
(** Converts the int into a netmask *)

val int_of_netmask : netmask -> int
(** Converts the netmask into an int *)

(** {2 Socket Calls} *)

val accept: fd -> fd * (ip * port)

val bind: fd -> ip option -> port option -> unit

val close: fd -> unit

val connect: fd -> ip -> port option -> unit

val disconnect: fd -> unit

val dup: fd -> fd

val dupfd: fd -> int -> fd

val getfileflags: fd -> filebflag list
val setfileflags: fd -> filebflag list -> unit

val getifaddrs: unit -> (ifid * ip * ip list * netmask) list

val getsockname: fd -> ip option * port option
val getpeername: fd -> ip * port

val getsockbopt: fd -> sockbflag -> bool
val getsocknopt: fd -> socknflag -> int
val getsocktopt: fd -> socktflag -> (int * int) option

val getsockerr: fd -> unit

val getsocklistening: fd -> bool

val listen: fd -> int -> unit

val pselect: fd list -> fd list -> fd list -> (int * int) option ->
  signal list option -> fd list * (fd list * fd list)

val recv: fd -> int -> msgbflag list -> (string * ((ip option * port option) * bool) option)

val send: fd -> (ip * port) option -> string -> msgbflag list -> string

val setsockbopt: fd -> sockbflag -> bool -> unit
val setsocknopt: fd -> socknflag -> int -> unit
val setsocktopt: fd -> socktflag -> (int * int) option -> unit

val shutdown: fd -> bool -> bool -> unit

val sockatmark: fd -> bool

val socket: sock_type -> fd


