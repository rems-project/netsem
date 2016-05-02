(* A HOL98 specification of TCP *)

(* The datatype of (Unix) errors *)

(*[ RCSID "$Id: TCP1_errorsScript.sml,v 1.16 2004/12/09 15:43:08 kw217 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

val _ = new_theory "TCP1_errors";

(*: @chapter [[TCP1_errors]] Error codes

This file contains the datatype of all possible error codes.  The
names are generally the common Unix ones; in the case of Winsock, the
obvious mapping is used.  Not all error codes are used in the body of the specification; those that are are described in the `Errors' section of each socket call.


:*)

(*: @section [[errors_error]] GEN The type of errors

The union of all (relevant) errors on the supported architectures.

:*)

(* this list taken from interface.ml *)
val _ = Hol_datatype `error =
                              E2BIG
                            | EACCES
                            | EADDRINUSE
                            | EADDRNOTAVAIL
                            | EAFNOSUPPORT
                            | EAGAIN
                            | EWOULDBLOCK (*: only used if [[EWOULDBLOCK <> EAGAIN]] :*)
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
			    | EHOSTDOWN`
;

val _ = export_theory();
