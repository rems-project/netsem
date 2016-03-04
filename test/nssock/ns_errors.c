#include "ns_sockets.h"

#ifndef WIN32
char *geterrmsg(char *dest, int errcode)
{
  switch(errno) {
#ifdef LINUX
    case ENOSTR:
      sprintf(dest, "ENOSTR");
      break;
#endif
    case ECANCELED:
      sprintf(dest, "ECANCELED");
      break;
    case EPERM:
      sprintf(dest, "EPERM");
      break;
    case ENOENT:
      sprintf(dest, "ENOENT");
      break;
    case ESRCH:
      sprintf(dest, "ESRCH");
      break;
    case EINTR:
      sprintf(dest, "EINTR");
      break;
    case EIO:
      sprintf(dest, "EIO");
      break;
    case ENXIO:
      sprintf(dest, "ENXIO");
      break;
    case E2BIG:
      sprintf(dest, "E2BIG");
      break;
    case ENOEXEC:
      sprintf(dest, "ENOEXEC");
      break;
    case EBADF:
      sprintf(dest, "EBADF");
      break;
    case ECHILD:
      sprintf(dest, "ECHILD");
      break;
    case EAGAIN:
      sprintf(dest, "EAGAIN");
      break;
#if EAGAIN != EWOULDBLOCK
      /* NB: on most *nices, EAGAIN == EWOULDBLOCK, and so this case
         doesn't arise - we treat them both as EAGAIN.  On Windows,
         they are different; see below. */
    case EWOULDBLOCK:
      sprintf(dest, "EWOULDBLOCK");
      break;
#endif
    case ENOMEM:
      sprintf(dest, "ENOMEM");
      break;
    case EACCES:
      sprintf(dest, "EACCES");
      break;
    case EFAULT:
      sprintf(dest, "EFAULT");
      break;
    case ENOTBLK:
      sprintf(dest, "ENOTBLK");
      break;
    case EBUSY:
      sprintf(dest, "EBUSY");
      break;
    case EEXIST:
      sprintf(dest, "EEXIST");
      break;
    case EXDEV:
      sprintf(dest, "EXDEV");
      break;
    case ENODEV:
      sprintf(dest, "ENODEV");
      break;
    case ENOTDIR:
      sprintf(dest, "ENOTDIR");
      break;
    case EISDIR:
      sprintf(dest, "EISDIR");
      break;
    case EINVAL:
      sprintf(dest, "EINVAL");
      break;
    case ENFILE:
      sprintf(dest, "ENFILE");
      break;
    case EMFILE:
      sprintf(dest, "EMFILE");
      break;
    case ENOTTY:
      sprintf(dest, "ENOTTY");
      break;
    case ETXTBSY:
      sprintf(dest, "ETXTBSY");
      break;
    case EFBIG:
      sprintf(dest, "EFBIG");
      break;
    case ENOSPC:
      sprintf(dest, "ENOSPC");
      break;
    case ESPIPE:
      sprintf(dest, "ESPIPE");
      break;
    case EROFS:
      sprintf(dest, "EROFS");
      break;
    case EMLINK:
      sprintf(dest, "EMLINK");
      break;
    case EPIPE:
      sprintf(dest, "EPIPE");
      break;
    case EDOM:
      sprintf(dest, "EDOM");
      break;
    case ERANGE:
      sprintf(dest, "ERANGE");
      break;
    case EDEADLK:
      sprintf(dest, "EDEADLK");
      break;
    case ENAMETOOLONG:
      sprintf(dest, "ENAMETOOLONG");
      break;
    case ENOLCK:
      sprintf(dest, "ENOLCK");
      break;
    case ENOSYS:
      sprintf(dest, "ENOSYS");
      break;
    case ENOTEMPTY:
      sprintf(dest, "ENOTEMPTY");
      break;
    case ELOOP:
      sprintf(dest, "ELOOP");
      break;
    case ENOMSG:
      sprintf(dest, "ENOMSG");
      break;
    case EIDRM:
      sprintf(dest, "EIDRM");
      break;
    case EDQUOT:
      sprintf(dest, "EDQUOT");
      break;
    case EREMOTE:
      sprintf(dest, "EREMOTE");
      break;
    case EILSEQ:
      sprintf(dest, "EILSEQ");
      break;
    case EOVERFLOW:
      sprintf(dest, "EOVERFLOW");
      break;
#ifndef BSD
    case ECHRNG:
      sprintf(dest, "ECHRNG");
      break;
    case EL2NSYNC:
      sprintf(dest, "EL2NSYNC");
      break;
    case EL3HLT:
      sprintf(dest, "EL3HLT");
      break;
    case EL3RST:
      sprintf(dest, "EL3RST");
      break;
    case ELNRNG:
      sprintf(dest, "ELNRNG");
      break;
    case EUNATCH:
      sprintf(dest, "EUNATCH");
      break;
    case ENOCSI:
      sprintf(dest, "ENOCSI");
      break;
    case EL2HLT:
      sprintf(dest, "EL2HLT");
      break;
    case EBADE:
      sprintf(dest, "EBADE");
      break;
    case EBADR:
      sprintf(dest, "EBADR");
      break;
    case EXFULL:
      sprintf(dest, "EXFULL");
      break;
    case ENOANO:
      sprintf(dest, "ENOANO");
      break;
    case EBADRQC:
      sprintf(dest, "EBADRQC");
      break;
    case EBADSLT:
      sprintf(dest, "EBADSLT");
      break;
    case EBFONT:
      sprintf(dest, "EBFONT");
      break;
    case ENODATA:
      sprintf(dest, "ENODATA");
      break;
    case ETIME:
      sprintf(dest, "ETIME");
      break;
    case ENOSR:
      sprintf(dest, "ENOSR");
      break;
    case ENONET:
      sprintf(dest, "ENONET");
      break;
    case ENOPKG:
      sprintf(dest, "ENOPKG");
      break;
    case ENOLINK:
      sprintf(dest, "ENOLINK");
      break;
    case EADV:
      sprintf(dest, "EADV");
      break;
    case ESRMNT:
      sprintf(dest, "ESRMNT");
      break;
    case ECOMM:
      sprintf(dest, "ECOMM");
      break;
    case EPROTO:
      sprintf(dest, "EPROTO");
      break;
    case EMULTIHOP:
      sprintf(dest, "EMULTIHOP");
      break;
    case EDOTDOT:
      sprintf(dest, "EDOTDOT");
      break;
    case EBADMSG:
      sprintf(dest, "EBADMSG");
      break;
    case ENOTUNIQ:
      sprintf(dest, "ENOTUNIQ");
      break;
    case EBADFD:
      sprintf(dest, "EBADFD");
      break;
    case EREMCHG:
      sprintf(dest, "EREMCHG");
      break;
    case ELIBACC:
      sprintf(dest, "ELIBACC");
      break;
    case ELIBBAD:
      sprintf(dest, "ELIBBAD");
      break;
    case ELIBSCN:
      sprintf(dest, "ELIBSCN");
      break;
    case ELIBMAX:
      sprintf(dest, "ELIBMAX");
      break;
    case ELIBEXEC:
      sprintf(dest, "ELIBEXEC");
      break;
    case ERESTART:
      sprintf(dest, "ERESTART");
      break;
/*    case EDESTPIPE:
      sprintf(dest, "EDESTPIPE");
      break; */
#endif
    case EUSERS:
      sprintf(dest, "EUSERS");
      break;
    case ENOTSOCK:
      sprintf(dest, "ENOTSOCK");
      break;
    case EDESTADDRREQ:
      sprintf(dest, "EDESTADDRREQ");
      break;
    case EMSGSIZE:
      sprintf(dest, "EMSGSIZE");
      break;
    case EPROTOTYPE:
      sprintf(dest, "EPROTOTYPE");
      break;
    case ENOPROTOOPT:
      sprintf(dest, "ENOPROTOOPT");
      break;
    case EPROTONOSUPPORT:
      sprintf(dest, "EPROTONOSUPPORT");
      break;
    case ESOCKTNOSUPPORT:
      sprintf(dest, "ESOCKTNOSUPPORT");
      break;
    case EOPNOTSUPP:
      sprintf(dest, "EOPNOTSUPP");
      break;
    case EPFNOSUPPORT:
      sprintf(dest, "EPFNOSUPPORT");
      break;
    case EAFNOSUPPORT:
      sprintf(dest, "EAFNOSUPPORT");
      break;
    case EADDRINUSE:
      sprintf(dest, "EADDRINUSE");
      break;
    case EADDRNOTAVAIL:
      sprintf(dest, "EADDRNOTAVAIL");
      break;
    case ENETDOWN:
      sprintf(dest, "ENETDOWN");
      break;
    case ENETUNREACH:
      sprintf(dest, "ENETUNREACH");
      break;
    case ENETRESET:
      sprintf(dest, "ENETRESET");
      break;
    case ECONNABORTED:
      sprintf(dest, "ECONNABORTED");
      break;
    case ECONNRESET:
      sprintf(dest, "ECONNRESET");
      break;
    case ENOBUFS:
      sprintf(dest, "ENOBUFS");
      break;
    case EISCONN:
      sprintf(dest, "EISCONN");
      break;
    case ENOTCONN:
      sprintf(dest, "ENOTCONN");
      break;
    case ESHUTDOWN:
      sprintf(dest, "ESHUTDOWN");
      break;
    case ETOOMANYREFS:
      sprintf(dest, "ETOOMANYREFS");
      break;
    case ETIMEDOUT:
      sprintf(dest, "ETIMEDOUT");
      break;
    case ECONNREFUSED:
      sprintf(dest, "ECONNREFUSED");
      break;
    case EHOSTDOWN:
      sprintf(dest, "EHOSTDOWN");
      break;
    case EHOSTUNREACH:
      sprintf(dest, "EHOSTUNREACH");
      break;
    case EALREADY:
      sprintf(dest, "EALREADY");
      break;
    case EINPROGRESS:
      sprintf(dest, "EINPROGRESS");
      break;
    case ESTALE:
      sprintf(dest, "ESTALE");
      break;
#ifndef BSD
    case EUCLEAN:
      sprintf(dest, "EUCLEAN");
      break;
    case ENOTNAM:
      sprintf(dest, "ENOTNAM");
      break;
    case ENAVAIL:
      sprintf(dest, "ENAVAIL");
      break;
    case EISNAM:
      sprintf(dest, "EISNAM");
      break;
    case EREMOTEIO:
      sprintf(dest, "EREMOTEIO");
      break;

    case ENOMEDIUM:
      sprintf(dest, "ENOMEDIUM");
      break;
    case EMEDIUMTYPE:
      sprintf(dest, "EMEDIUMTYPE");
      break;
#endif
    default:
      sprintf(dest, "EUNKNOWN_UNIX_ERROR");
      break;
  }

  return dest;
}

#else //#ifndef WIN32

char *geterrmsg(char *dest, int errcode)
{
  switch(errcode) {
    case WSAEINTR:
      sprintf(dest, "EINTR");
      break;
    case WSAEBADF:(dest, "EBADF");
      break;
    case WSAEACCES:
      sprintf(dest, "EACCES");
      break;
    case WSAEFAULT:
      sprintf(dest, "EFAULT");
      break;
    case WSAEINVAL:
      sprintf(dest, "EINVAL");
      break;
    case WSAEMFILE:
      sprintf(dest, "EMFILE");
      break;
    case WSAEWOULDBLOCK:
      sprintf(dest, "EAGAIN");     /* have decided that WSAEWOULDBLOCK = EAGAIN on WinXP */
      break;
    case WSAEINPROGRESS:
      sprintf(dest, "EINPROGRESS");
      break;
    case WSAEALREADY:
      sprintf(dest, "EALREADY");
      break;
    case WSAENOTSOCK:
      sprintf(dest, "ENOTSOCK");
      break;
    case WSAEDESTADDRREQ:
      sprintf(dest, "EDESTADDRREQ");
      break;
    case WSAEMSGSIZE:
      sprintf(dest, "EMSGSIZE");
      break;
    case WSAEPROTOTYPE:
      sprintf(dest, "EPROTOTYPE");
      break;
    case WSAENOPROTOOPT:
      sprintf(dest, "ENOPROTOOPT");
      break;
    case WSAEPROTONOSUPPORT:
      sprintf(dest, "EPROTONOSUPPORT");
      break;
    case WSAESOCKTNOSUPPORT:
      sprintf(dest, "ESOCKTNOSUPPORT");
      break;
    case WSAEOPNOTSUPP:
      sprintf(dest, "EOPNOTSUPP");
      break;
    case WSAEPFNOSUPPORT:
      sprintf(dest, "EPFNOSUPPORT");
      break;
    case WSAEAFNOSUPPORT:
      sprintf(dest, "EAFNOSUPPORT");
      break;
    case WSAEADDRINUSE:
      sprintf(dest, "EADDRINUSE");
      break;
    case WSAEADDRNOTAVAIL:
      sprintf(dest, "EADDRNOTAVAIL");
      break;
    case WSAENETDOWN:
      sprintf(dest, "ENETDOWN");
      break;
    case WSAENETUNREACH:
      sprintf(dest, "ENETUNREACH");
      break;
    case WSAENETRESET:
      sprintf(dest, "ENETRESET");
      break;
    case WSAECONNABORTED:
      sprintf(dest, "ECONNABORTED");
      break;
    case WSAECONNRESET:
      sprintf(dest, "ECONNRESET");
      break;
    case WSAENOBUFS:
      sprintf(dest, "ENOBUFS");
      break;
    case WSAEISCONN:
      sprintf(dest, "EISCONN");
      break;
    case WSAENOTCONN:
      sprintf(dest, "ENOTCONN");
      break;
    case WSAESHUTDOWN:
      sprintf(dest, "ESHUTDOWN");
      break;
    case WSAETOOMANYREFS:
      sprintf(dest, "ETOOMANYREFS");
      break;
    case WSAETIMEDOUT:
      sprintf(dest, "ETIMEDOUT");
      break;
    case WSAECONNREFUSED:
      sprintf(dest, "ECONNREFUSED");
      break;
    case WSAELOOP:
      sprintf(dest, "ELOOP");
      break;
    case WSAENAMETOOLONG:
      sprintf(dest, "ENAMETOOLONG");
      break;
    case WSAEHOSTDOWN:
      sprintf(dest, "EHOSTDOWN");
      break;
    case WSAEHOSTUNREACH:
      sprintf(dest, "EHOSTUNREACH");
      break;
    case WSAENOTEMPTY:
      sprintf(dest, "ENOTEMPTY");
      break;
    case WSAEPROCLIM:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSAEUSERS:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSAEDQUOT:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSAESTALE:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSAEREMOTE:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSAEDISCON:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSASYSNOTREADY:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSAVERNOTSUPPORTED:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSANOTINITIALISED:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSAHOST_NOT_FOUND:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSATRY_AGAIN:
      sprintf(dest, "EAGAIN");
      break;
    case WSANO_RECOVERY:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
    case WSANO_DATA:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
/*    case WSANO_ADDRESS:
      sprintf(dest, "WSANO_ADDRESS");
      break;*/
    default:
      sprintf(dest, "EUNKNOWNERR(%d)", errcode);
      break;
  }

  return dest;
}

#endif //#ifndef WIN32
