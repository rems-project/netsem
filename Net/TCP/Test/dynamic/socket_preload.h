/******************************************************************/
/* Netsem UNIX LD_PRELOAD hook sockets library - socket_preload.h  */
/* Steve Bishop - Created 20031118                                 */
/*******************************************************************/
#ifndef NS_SOCKETS_PRELOAD_H
#define NS_SOCKETS_PRELOAD_H

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


//#include <sys/types.h>
#include <stdio.h>
#include <stdarg.h>
#include <dlfcn.h>

struct sockaddr {
  unsigned short int sa_family;
  char sa_data[14];
};

typedef unsigned int socklen_t;
//typedef int size_t;
typedef int SOCKET;

struct msghdr
{
  void *msg_name;
  socklen_t msg_namelen;
  void *msg_iov;
  int msg_iovlen;
  void *msg_control;
  socklen_t msg_controllen;
  int msg_flags;
};

typedef void fd_set;

/* Function definitions */
extern SOCKET accept(SOCKET s, struct sockaddr *addr,
			socklen_t *addrlen);
extern int bind(SOCKET sockfd, struct sockaddr *my_addr,
		  socklen_t addrlen);
extern int close(SOCKET fd);
extern int connect(SOCKET sockfd, const struct sockaddr *serv_addr,
		      socklen_t addrlen);

extern SOCKET dup(SOCKET oldfd);
extern SOCKET dup2(SOCKET oldfd, SOCKET newfd);

extern int fcntl(SOCKET fd, int cmd, ...);
extern int getsockname(SOCKET s, struct sockaddr *name,
		          socklen_t *namelen);
extern int getpeername(SOCKET s, struct sockaddr *name,
			  socklen_t *namelen);
extern int getsockopt(SOCKET s, int level, int optname,
			 void *optval, socklen_t *optlen);

extern int ioctl(SOCKET d, int request, ...);


extern int listen(SOCKET s, int backlog);
extern int recv(SOCKET s, void *buf, size_t len, int flags);
extern int recvfrom(SOCKET s, void *buf, size_t len, int flags,
		        struct sockaddr *from, socklen_t *fromlen);
extern int recvmsg(SOCKET s, struct msghdr *msg, int flags);

#ifdef LINUX
extern int pselect (SOCKET n, fd_set *readfds, fd_set *writefds,
		        fd_set *exceptfds, void *timeout, void *sigmask);
#endif

extern int select (SOCKET n, fd_set *readfds, fd_set *writefds,
		       fd_set *exceptfds, void *timeout);

extern int send(SOCKET s, const void *msg, size_t len, int flags);
extern int sendto(SOCKET s, const void *msg, size_t len, int flags,
		      const struct sockaddr *to, socklen_t tolen);
extern int sendmsg(SOCKET s, const struct msghdr *msg, int flags);

extern int setsockopt(SOCKET s, int level, int optname,
		          const void *optval, socklen_t optlen);
extern int shutdown(SOCKET s, int how);

#ifdef LINUX
extern int sockatmark(SOCKET s);
#endif

extern SOCKET socket(int domain, int type, int protocol);

#endif //NS_SOCKETS_PRELOAD_H












