/******************************************************************/
/* Netsem UNIX LD_PRELOAD hook sockets library - socket_preload.c */
/* Steve Bishop - Created 20020903                                */
/* $Id $       */
/******************************************************************/
#include "socket_preload.h"
#include <errno.h>
//#include <dlfcn.h>

void *handle = 0;

typedef int (*read_ptr_t)(int, void*, size_t);
static read_ptr_t real_read;
typedef int (*write_ptr_t)(int, const void*, size_t);
static write_ptr_t real_write;
typedef int (*getsockopt_ptr_t)(int,int,int,void*,socklen_t*);
static getsockopt_ptr_t real_getsockopt;

#ifdef LINUX
#define SOL_SOCKET 1
#define SO_REUSEADDR 2
#else
#ifdef BSD
#define SOL_SOCKET 0xffff
#define SO_REUSEADDR 0x0004
#endif
#endif

SOCKET accept(SOCKET s, struct sockaddr *addr, socklen_t *addrlen)
{
  return ns_accept(s, addr, addrlen);
}

int bind(SOCKET sockfd, struct sockaddr *my_addr, socklen_t addrlen)
{
  return ns_bind(sockfd, my_addr, addrlen);
}

int close(SOCKET fd)
{
  return ns_close(fd);
}

int connect(SOCKET sockfd, const struct sockaddr *serv_addr,
	       socklen_t addrlen)
{
  return ns_connect(sockfd, serv_addr, addrlen);
}

SOCKET dup(SOCKET oldfd)
{
  return ns_dup(oldfd);
}

/*SOCKET dup2(SOCKET oldfd, SOCKET newfd)
{
  return ns_dup2(oldfd);
}*/

/*int fcntl(SOCKET fd, int cmd, ...)
{
  va_list args;
  return ns_fcntl(fd, cmd, args);
}
*/

int getsockname(SOCKET s, struct sockaddr *name,
	            socklen_t *namelen)
{
  return ns_getsockname(s, name, namelen);
}


int getpeername(SOCKET s, struct sockaddr *name,
		   socklen_t *namelen)
{
  return ns_getpeername(s, name, namelen);
}


int getsockopt(SOCKET s, int level, int optname,
		  void *optval, socklen_t *optlen)
{
  return ns_getsockopt(s, level, optname, optval, optlen);
}

/*int ioctl(SOCKET d, int request, ...)
{
  va_list args;
  return ns_ioctl(d, request, args);
}*/

int listen(SOCKET s, int backlog)
{
  return ns_listen(s, backlog);
}

/*
#ifdef LINUX
int pselect (SOCKET n, fd_set *readfds, fd_set *writefds,
	     fd_set *exceptfds, void *timeout, void *sigmask)
{
  return ns_pselect(n, readfds, writefds, exceptfds, timeout, sigmask);
}
#endif //#ifdef Linux
*/

int recv(SOCKET s, void *buf, size_t len, int flags)
{
  return ns_recv(s, buf, len, flags);
}

void initialise()
{
  if(handle != 0)
    return;

  if ((handle = dlopen("/lib/libc.so.6", RTLD_NOW)) == 0)
  {
    printf("socket_preload.initialise(): %s\n", dlerror());
    exit(1);
  }

  if ((real_read = dlsym(handle, "read")) == 0)
  {
    printf("socket_preload.initialise().read: %s\n", dlerror());
    exit(1);
  }

  if ((real_write = dlsym(handle, "write")) == 0)
  {
    printf("socket_preload.initialise().write: %s\n", dlerror());
    exit(1);
  }

  if ((real_getsockopt = dlsym(handle, "getsockopt")) == 0)
  {
    printf("socket_preload.initialise().getsockopt %s\n", dlerror());
    exit(1);
  }

  return;
}

int test_for_socket(int s)
{
  int result;
  unsigned int optval;
  socklen_t optlen;

  optlen = sizeof(optval);
  result = real_getsockopt(s, SOL_SOCKET, SO_REUSEADDR, &optval, &optlen);
  if((result == -1) && (errno == ENOTSOCK))
    return 0;
  else
    return 1;
}

int read(int s, void *buf, size_t len)
{
  initialise();
  if(test_for_socket(s) == 1)
    return ns_recv(s, buf, len , 0);
  else
    return real_read(s,buf,len);
}

int recvfrom(SOCKET s, void *buf, size_t len, int flags,
		struct sockaddr *from, socklen_t *fromlen)
{
  return ns_recvfrom(s, buf, len, flags, from, fromlen);
}


int recvmsg(SOCKET s, struct msghdr *msg, int flags)
{
  return ns_recvmsg(s, msg, flags);
}


/*int select (SOCKET n, fd_set *readfds, fd_set *writefds,
	       fd_set *exceptfds, void *timeout)
{
  return ns_select(n, readfds, writefds, exceptfds, timeout);
}*/

int send(SOCKET s, const void *msg, size_t len, int flags)
{
  return ns_send(s, msg, len, flags);
}

int write(int fd, const void *msg, size_t count)
{
  initialise();
  if(test_for_socket(fd) == 1)
    return ns_send(fd, msg, count, 0);
  else
    return real_write(fd,msg,count);
}

int sendto(SOCKET s, const void *msg, size_t len, int flags,
	      const struct sockaddr *to, socklen_t tolen)
{
  return ns_sendto(s, msg, len, flags, to, tolen);
}


int sendmsg(SOCKET s, const struct msghdr *msg, int flags)
{
  return ns_sendmsg(s, msg, flags);
}


int setsockopt(SOCKET s, int level, int optname,
		  const void *optval, socklen_t optlen)
{
  return ns_setsockopt(s, level, optname, optval, optlen);
}


int shutdown(SOCKET s, int how)
{
  return ns_shutdown(s, how);
}


int sockatmark(SOCKET s)
{
  return ns_sockatmark(s);
}


SOCKET socket(int domain, int type, int protocol)
{
  return ns_socket(domain, type, protocol);
}

