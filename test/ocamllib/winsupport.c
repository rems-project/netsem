/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../../LICENSE.  */
/*                                                                     */
/***********************************************************************/


#include <caml/mlvalues.h>
#include <caml/callback.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/custom.h>

#include "unixsupport.h"
#include "cst2constr.h"

#include <errno.h>

#include "../nssock/ns_sockets.h"

/* Mapping of Windows error codes to POSIX error codes */

struct error_entry { unsigned long win_code; int range; int posix_code; };

static struct error_entry win_error_table[] = {
  { ERROR_INVALID_FUNCTION, 0, EINVAL},
  { ERROR_FILE_NOT_FOUND, 0, ENOENT},
  { ERROR_PATH_NOT_FOUND, 0, ENOENT},
  { ERROR_TOO_MANY_OPEN_FILES, 0, EMFILE},
  { ERROR_ACCESS_DENIED, 0, EACCES},
  { ERROR_INVALID_HANDLE, 0, EBADF},
  { ERROR_ARENA_TRASHED, 0, ENOMEM},
  { ERROR_NOT_ENOUGH_MEMORY, 0, ENOMEM},
  { ERROR_INVALID_BLOCK, 0, ENOMEM},
  { ERROR_BAD_ENVIRONMENT, 0, E2BIG},
  { ERROR_BAD_FORMAT, 0, ENOEXEC},
  { ERROR_INVALID_ACCESS, 0, EINVAL},
  { ERROR_INVALID_DATA, 0, EINVAL},
  { ERROR_INVALID_DRIVE, 0, ENOENT},
  { ERROR_CURRENT_DIRECTORY, 0, EACCES},
  { ERROR_NOT_SAME_DEVICE, 0, EXDEV},
  { ERROR_NO_MORE_FILES, 0, ENOENT},
  { ERROR_LOCK_VIOLATION, 0, EACCES},
  { ERROR_BAD_NETPATH, 0, ENOENT},
  { ERROR_NETWORK_ACCESS_DENIED, 0, EACCES},
  { ERROR_BAD_NET_NAME, 0, ENOENT},
  { ERROR_FILE_EXISTS, 0, EEXIST},
  { ERROR_CANNOT_MAKE, 0, EACCES},
  { ERROR_FAIL_I24, 0, EACCES},
  { ERROR_INVALID_PARAMETER, 0, EINVAL},
  { ERROR_NO_PROC_SLOTS, 0, EAGAIN},
  { ERROR_DRIVE_LOCKED, 0, EACCES},
  { ERROR_BROKEN_PIPE, 0, EPIPE},
  { ERROR_DISK_FULL, 0, ENOSPC},
  { ERROR_INVALID_TARGET_HANDLE, 0, EBADF},
  { ERROR_INVALID_HANDLE, 0, EINVAL},
  { ERROR_WAIT_NO_CHILDREN, 0, ECHILD},
  { ERROR_CHILD_NOT_COMPLETE, 0, ECHILD},
  { ERROR_DIRECT_ACCESS_HANDLE, 0, EBADF},
  { ERROR_NEGATIVE_SEEK, 0, EINVAL},
  { ERROR_SEEK_ON_DEVICE, 0, EACCES},
  { ERROR_DIR_NOT_EMPTY, 0, ENOTEMPTY},
  { ERROR_NOT_LOCKED, 0, EACCES},
  { ERROR_BAD_PATHNAME, 0, ENOENT},
  { ERROR_MAX_THRDS_REACHED, 0, EAGAIN},
  { ERROR_LOCK_FAILED, 0, EACCES},
  { ERROR_ALREADY_EXISTS, 0, EEXIST},
  { ERROR_FILENAME_EXCED_RANGE, 0, ENOENT},
  { ERROR_NESTING_NOT_ALLOWED, 0, EAGAIN},
  { ERROR_NOT_ENOUGH_QUOTA, 0, ENOMEM},
  { ERROR_INVALID_STARTING_CODESEG,
    ERROR_INFLOOP_IN_RELOC_CHAIN - ERROR_INVALID_STARTING_CODESEG,
    ENOEXEC },
  { ERROR_WRITE_PROTECT,
    ERROR_SHARING_BUFFER_EXCEEDED - ERROR_WRITE_PROTECT,
    EACCES },
  { WSAEINVAL, 0, EINVAL },
  { WSAEACCES, 0, EACCES },
  { WSAEBADF, 0, EBADF },
  { WSAEFAULT, 0, EFAULT },
  { WSAEINTR, 0, EINTR },
  { WSAEINVAL, 0, EINVAL },
  { WSAEMFILE, 0, EMFILE },
#ifdef WSANAMETOOLONG
  { WSANAMETOOLONG, 0, ENAMETOOLONG },
#endif
#ifdef WSAENFILE
  { WSAENFILE, 0, ENFILE },
#endif
  { WSAENOTEMPTY, 0, ENOTEMPTY },
  { 0, -1, 0 }
};

int ns_win32_maperr(unsigned long errcode)
{
  int i;

  for (i = 0; win_error_table[i].range >= 0; i++) {
    if (errcode >= win_error_table[i].win_code &&
        errcode <= win_error_table[i].win_code + win_error_table[i].range) {
      return win_error_table[i].posix_code;
    }
  }
  // Not found: save original error code, negated so that we can
  // recognize it in unix_error_message
  return -(int)errcode;
}

/* Windows socket errors */

#define EWOULDBLOCK             -WSAEWOULDBLOCK
#define EINPROGRESS             -WSAEINPROGRESS
#define EALREADY                -WSAEALREADY
#define ENOTSOCK                -WSAENOTSOCK
#define EDESTADDRREQ            -WSAEDESTADDRREQ
#define EMSGSIZE                -WSAEMSGSIZE
#define EPROTOTYPE              -WSAEPROTOTYPE
#define ENOPROTOOPT             -WSAENOPROTOOPT
#define EPROTONOSUPPORT         -WSAEPROTONOSUPPORT
#define ESOCKTNOSUPPORT         -WSAESOCKTNOSUPPORT
#define EOPNOTSUPP              -WSAEOPNOTSUPP
#define EPFNOSUPPORT            -WSAEPFNOSUPPORT
#define EAFNOSUPPORT            -WSAEAFNOSUPPORT
#define EADDRINUSE              -WSAEADDRINUSE
#define EADDRNOTAVAIL           -WSAEADDRNOTAVAIL
#define ENETDOWN                -WSAENETDOWN
#define ENETUNREACH             -WSAENETUNREACH
#define ENETRESET               -WSAENETRESET
#define ECONNABORTED            -WSAECONNABORTED
#define ECONNRESET              -WSAECONNRESET
#define ENOBUFS                 -WSAENOBUFS
#define EISCONN                 -WSAEISCONN
#define ENOTCONN                -WSAENOTCONN
#define ESHUTDOWN               -WSAESHUTDOWN
#define ETOOMANYREFS            -WSAETOOMANYREFS
#define ETIMEDOUT               -WSAETIMEDOUT
#define ECONNREFUSED            -WSAECONNREFUSED
#define ELOOP                   -WSAELOOP
#define EHOSTDOWN               -WSAEHOSTDOWN
#define EHOSTUNREACH            -WSAEHOSTUNREACH
#define EPROCLIM                -WSAEPROCLIM
#define EUSERS                  -WSAEUSERS
#define EDQUOT                  -WSAEDQUOT
#define ESTALE                  -WSAESTALE
#define EREMOTE                 -WSAEREMOTE
#define EBADMSG                 -1
#define ECANCELED               -1
#define EIDRM                   -1
#define EMULTIHOP               -1
#define ENODATA                 -1
#define ENOLINK                 -1
#define ENOMSG                  -1
#define ENOSR                   -1
#define ENOSTR                  -1
#define ENOTSUP                 -1
#define EOVERFLOW               -1
#define EPROTO                  -1
#define ETIME                   -1
#define ETXTBSY                 -1

#define EACCESS EACCES

#define EUNKNOWN_UNIX_ERROR

int ns_error_table[] = {
  E2BIG, EACCES, EADDRINUSE, EADDRNOTAVAIL, EAFNOSUPPORT,
  EAGAIN, EWOULDBLOCK, EALREADY, EBADF, EBADMSG, EBUSY,
  ECANCELED, ECHILD, ECONNABORTED, ECONNREFUSED, ECONNRESET,
  EDEADLK, EDESTADDRREQ, EDOM, EDQUOT,  EEXIST, EFAULT, EFBIG,
  EHOSTUNREACH,EIDRM, EILSEQ, EINPROGRESS,  EINTR, EINVAL, EIO,
  EISCONN, EISDIR, ELOOP, EMFILE, EMLINK, EMSGSIZE, EMULTIHOP,
  ENAMETOOLONG, ENETDOWN, ENETRESET, ENETUNREACH, ENFILE, ENOBUFS,
  ENODATA, ENODEV, ENOENT, ENOEXEC, ENOLCK, ENOLINK, ENOMEM, ENOMSG,
  ENOPROTOOPT, ENOSPC, ENOSR, ENOSTR, ENOSYS, ENOTCONN, ENOTDIR,
  ENOTEMPTY, ENOTSOCK, ENOTSUP, ENOTTY, ENXIO, EOPNOTSUPP, EOVERFLOW,
  EPERM, EPIPE, EPROTO, EPROTONOSUPPORT, EPROTOTYPE, ERANGE,
  EROFS, ESPIPE, ESRCH, ESTALE, ETIME, ETIMEDOUT, ETXTBSY, EXDEV,
  ESHUTDOWN, EHOSTDOWN, EUNKNOWN_UNIX_ERROR
};

static value * unix_error_exn = NULL;

void ns_unix_error(int errcode, char *cmdname, value cmdarg)
{
  CAMLparam0();
  CAMLlocal4(res,name,err,arg);

  name = err = arg = Val_unit;

  Begin_roots3 (name, err, arg);
    arg = cmdarg == Nothing ? copy_string("") : cmdarg;
    name = copy_string(cmdname);
    err =
      cst_to_constr(errcode, ns_error_table, sizeof(ns_error_table)/sizeof(int));
    if (unix_error_exn == NULL) {
      unix_error_exn = caml_named_value("Ocamllib.Unix_error");
      if (unix_error_exn == NULL)
        invalid_argument("Exception Ocamllib.Unix_error not initialized, please link Ocamllib.cma");
    }
    res = alloc_small(4, 0);
    Field(res, 0) = *unix_error_exn;
    Field(res, 1) = err;
    Field(res, 2) = name;
    Field(res, 3) = arg;
  End_roots();
  mlraise(res);
  CAMLreturn0;
}

void ns_uerror(cmdname, cmdarg)
     char * cmdname;
     value cmdarg;
{
  ns_unix_error(ns_win32_maperr(NS_ERROR_CODE), cmdname, cmdarg);
}
