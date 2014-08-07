/**************************************************************/
/* Netsem multi-platform sockets library - ns_sockets.h       */
/* Steve Bishop - Created 20020903                            */
/**************************************************************/
#ifndef NS_SOCKETS_H
#define NS_SOCKETS_H

/* #define LINUX 1 */
/* #define BSD   2 */
/* #define WIN32 4 */
#ifdef __linux
#define LINUX
#else
#ifdef __FreeBSD__
#define BSD
#endif
#endif

#define _POSIX_SELECT 1

#ifndef WIN32
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <errno.h>
#include <sys/errno.h>
#include <sys/select.h>
#include <dlfcn.h>
#include <sys/stat.h>
#ifndef BSD
#include <linux/net.h>
#else
#include <sys/uio.h>
#endif
#include <sys/ioctl.h>
#include <signal.h>
#include <sys/time.h>
#include <unistd.h>
#include <fcntl.h>
#else  //WIN32
#include <winsock2.h>
#include <process.h>
#include <windows.h>
#include <sys/timeb.h>
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <memory.h>
#include <time.h>


#ifndef WIN32  // !WIN32
#define ERRNO          errno
#define INVALID_SOCKET -1
#define SOCKET_ERROR   -1
typedef int SOCKET;
#define SD_RECEIVE      0
#define SD_SEND         1
#define SD_BOTH         2
#else		  // WIN32
#define ERRNO WSAGetLastError()
#ifndef socklen_t
typedef int socklen_t;
#define close closesocket
#define getpid _getpid

#ifndef EAGAIN
#define EAGAIN WSAEWOULDBLOCK
#endif
#ifndef EINVAL
#define EINVAL WSAEINTR
#endif
#ifndef EAFNOSUPPORT
#define EAFNOSUPPORT WSAEAFNOSUPPORT
#endif
#endif
#endif

#define NS_MAX_BUFFER_SIZE 65536
#define NS_TIME_SIZE 40
#define NUMSENDRETRIES 10
#define HIGHFD 1000
#define SMSTR  30
#define MEDSTR 80
#define LARGESTR 255

/* Copy of ERRNO */
extern int NS_ERROR_CODE;

/* Function definitions */
extern int ns_init();
extern int ns_getpid();
extern SOCKET ns_accept(SOCKET s, struct sockaddr *addr,
			socklen_t *addrlen);
extern int ns_bind(SOCKET sockfd, struct sockaddr *my_addr,
		  socklen_t addrlen);
extern int ns_close(SOCKET fd);
extern int ns_connect(SOCKET sockfd, const struct sockaddr *serv_addr,
		      socklen_t addrlen);
extern int ns_disconnect(SOCKET fd);

#ifndef WIN32
extern SOCKET ns_dup(SOCKET oldfd);
extern SOCKET ns_dup2(SOCKET oldfd, SOCKET newfd);
//Commented out to workaround the va_args problem
//extern int ns_fcntl(SOCKET fd, int cmd, long arg);
#endif

#ifdef BSD
extern int ns_getifaddrs();
#endif

extern int ns_getsockname(SOCKET s, struct sockaddr *name,
		          socklen_t *namelen);
extern int ns_getpeername(SOCKET s, struct sockaddr *name,
			  socklen_t *namelen);
extern int ns_getsockopt(SOCKET s, int level, int optname,
			 void *optval, socklen_t *optlen);

#ifndef WIN32
extern int ns_ioctl(SOCKET d, int request, ...);
#else
extern int ns_ioctlsocket(SOCKET s, long cmd, u_long* argp);
#endif

extern int ns_listen(SOCKET s, int backlog);
extern int ns_recv(SOCKET s, void *buf, size_t len, int flags);
extern int ns_recvfrom(SOCKET s, void *buf, size_t len, int flags,
		        struct sockaddr *from, socklen_t *fromlen);
extern int ns_recvmsg(SOCKET s, struct msghdr *msg, int flags);

#ifdef LINUX
extern int ns_pselect (int n, fd_set *readfds, fd_set *writefds,
		        fd_set *exceptfds, const struct timespec *timeout,
			  sigset_t *sigmask);
#endif

extern int ns_select (SOCKET n, fd_set *readfds, fd_set *writefds,
		       fd_set *exceptfds, struct timeval *timeout);

extern int ns_send(SOCKET s, const void *msg, size_t len, int flags);
extern int ns_sendto(SOCKET s, const void *msg, size_t len, int flags,
		      const struct sockaddr *to, socklen_t tolen);
extern int ns_sendmsg(SOCKET s, const struct msghdr *msg, int flags);

extern int ns_setsockopt(SOCKET s, int level, int optname,
		          const void *optval, socklen_t optlen);
extern int ns_shutdown(SOCKET s, int how);

#ifdef LINUX
extern int ns_sockatmark(SOCKET s);
#endif

extern SOCKET ns_socket(int domain, int type, int protocol);

#endif //NS_SOCKETS_H












