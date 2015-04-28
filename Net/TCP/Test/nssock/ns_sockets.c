/**************************************************************/
/* Netsem multi-platform sockets library - ns_sockets.c       */
/* Steve Bishop - Created 20020903                            */
/* $Id: ns_sockets.c,v 1.74 2004/06/28 16:38:34 mjas2 Exp $ */
/**************************************************************/
#include "ns_sockets.h"
#include "ns_sockets_int.h"
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "../common/ntpheader.h"
#ifndef WIN32
#include <net/if.h>
#endif
#ifdef BSD
#include <ifaddrs.h>
#endif
#ifdef WIN32
#include "tsctime/TSCtime.h"
#endif

SOCKET sd;
char *nsbuffer;
int init = 0;
char currentTime[NS_TIME_SIZE];
time_t currtime;
int debugf;
int dynamicLink = 0;


int NS_ERROR_CODE = 0;

/* ---------------------------------------- */
/* Define all of the dynamically bound
 * pointers to the real libc socket calls.
 * These are used if dynamicLink is set     */
/* ---------------------------------------- */

typedef SOCKET (*realcall_accept_ptr_t)(SOCKET, struct sockaddr*, socklen_t*);
static realcall_accept_ptr_t realcall_accept;

typedef int (*realcall_bind_ptr_t)(SOCKET, struct sockaddr*, socklen_t);
static realcall_bind_ptr_t realcall_bind;

typedef int (*realcall_close_ptr_t)(SOCKET);
static realcall_close_ptr_t realcall_close;

typedef int (*realcall_connect_ptr_t)(SOCKET, const struct sockaddr*, socklen_t);
static realcall_connect_ptr_t realcall_connect;

typedef SOCKET (*realcall_dup_ptr_t)(SOCKET);
static realcall_dup_ptr_t realcall_dup;

typedef SOCKET (*realcall_dup2_ptr_t)(SOCKET, SOCKET);
static realcall_dup2_ptr_t realcall_dup2;

typedef int (*realcall_getsockname_ptr_t)(SOCKET, struct sockaddr*, socklen_t*);
static realcall_getsockname_ptr_t realcall_getsockname;

typedef int (*realcall_getpeername_ptr_t)(SOCKET, struct sockaddr*, socklen_t*);
static realcall_getpeername_ptr_t realcall_getpeername;

typedef int (*realcall_getsockopt_ptr_t)(SOCKET, int, int, void*, socklen_t*);
static realcall_getsockopt_ptr_t realcall_getsockopt;

typedef int (*realcall_ioctl_ptr_t)(SOCKET, int, ...);
static realcall_ioctl_ptr_t realcall_ioctl;

#ifdef BSD
typedef int (*realcall_getifaddrs_ptr_t)(struct ifaddrs**);
static realcall_getifaddrs_ptr_t realcall_getifaddrs;
#endif

typedef int (*realcall_fcntl_ptr_t)(SOCKET, int, ...);
static realcall_fcntl_ptr_t realcall_fcntl;

typedef int (*realcall_listen_ptr_t)(SOCKET, int);
static realcall_listen_ptr_t realcall_listen;

typedef int (*realcall_recv_ptr_t)(SOCKET, void*, size_t, int);
static realcall_recv_ptr_t realcall_recv;

typedef int (*realcall_recvfrom_ptr_t)(SOCKET, void*, size_t, int, struct sockaddr*, socklen_t*);
static realcall_recvfrom_ptr_t realcall_recvfrom;

typedef int (*realcall_recvmsg_ptr_t)(SOCKET, struct msghdr*, int);
static realcall_recvmsg_ptr_t realcall_recvmsg;

#ifdef LINUX
typedef int (*realcall_pselect_ptr_t)(int, fd_set*, fd_set*, fd_set*, const struct timespec*, sigset_t*);
static realcall_pselect_ptr_t realcall_pselect;
#endif

typedef int (*realcall_select_ptr_t)(int, fd_set*, fd_set*, fd_set*, struct timeval*);
static realcall_select_ptr_t realcall_select;

typedef int (*realcall_send_ptr_t)(SOCKET, const void*, size_t, int);
static realcall_send_ptr_t realcall_send;

typedef int (*realcall_sendto_ptr_t)(SOCKET, const void*, size_t, int, const struct sockaddr*, socklen_t);
static realcall_sendto_ptr_t realcall_sendto;

typedef int (*realcall_sendmsg_ptr_t)(SOCKET, const struct msghdr*, int);
static realcall_sendmsg_ptr_t realcall_sendmsg;

typedef int (*realcall_setsockopt_ptr_t)(SOCKET, int, int, const void*, socklen_t);
static realcall_setsockopt_ptr_t realcall_setsockopt;

typedef int (*realcall_shutdown_ptr_t)(SOCKET, int);
static realcall_shutdown_ptr_t realcall_shutdown;

#ifdef LINUX
typedef int (*realcall_sockatmark_ptr_t)(SOCKET);
static realcall_sockatmark_ptr_t realcall_sockatmark;
#endif

typedef SOCKET (*realcall_socket_ptr_t)(int, int, int);
static realcall_socket_ptr_t realcall_socket;

/* ---------------------------------------- */
/* void sock_err(int err, char *str)
 * Arguments: err - error code
 *            str - pointer to a buffer
 * Returns:   void
 * Desc:      If an error occurs, report it
 *            and abort
 */
void sock_err(int err, char *str)
{
  perror(str);
  abort();
}


#ifndef WIN32
/* ---------------------------------------- */
/* void doDynamicCallRebinding()
 * Returns:   void
 * Desc:      If we are doing dynamic
 *            rebinding then manually bind
 *            all the real socket calls.
 */
void doDynamicCallRebinding()
{
  void *handle = NULL;

  if ((handle = dlopen("/lib/libc.so.6", RTLD_NOW)) == NULL) {
    printf("Failed to call dlopen in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_accept = dlsym(handle, "accept")) == NULL) {
    printf("Failed to rebind accept() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_bind = dlsym(handle, "bind")) == NULL) {
    printf("Failed to rebind bind() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_close = dlsym(handle, "close")) == NULL) {
    printf("Failed to rebind close() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_connect = dlsym(handle, "connect")) == NULL) {
    printf("Failed to rebind connect() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_dup = dlsym(handle, "dup")) == NULL) {
    printf("Failed to rebind dup() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_dup2 = dlsym(handle, "dup2")) == NULL) {
    printf("Failed to rebind dup2() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_getsockname = dlsym(handle, "getsockname")) == NULL) {
    printf("Failed to rebind getsockname() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_getpeername = dlsym(handle, "getpeername")) == NULL) {
    printf("Failed to rebind getpeername() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_getsockopt = dlsym(handle, "getsockopt")) == NULL) {
    printf("Failed to rebind getsockopt() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
#ifdef BSD
  if ((realcall_getifaddrs = dlsym(handle, "getifaddrs")) == NULL) {
    printf("Failed to rebind getifaddrs() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
#endif
  if ((realcall_ioctl = dlsym(handle, "ioctl")) == NULL) {
    printf("Failed to rebind ioctl() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_fcntl = dlsym(handle, "fcntl")) == NULL) {
    printf("Failed to rebind fcntl() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_listen = dlsym(handle, "listen")) == NULL) {
    printf("Failed to rebind listen() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_recv = dlsym(handle, "recv")) == NULL) {
    printf("Failed to rebind recv() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_recvfrom = dlsym(handle, "recvfrom")) == NULL) {
    printf("Failed to rebind recvfrom() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_recvmsg = dlsym(handle, "recvmsg")) == NULL) {
    printf("Failed to rebind recvmsg() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
#ifdef LINUX
  if ((realcall_pselect = dlsym(handle, "pselect")) == NULL) {
    printf("Failed to rebind pselect() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
#endif
  if ((realcall_select = dlsym(handle, "select")) == NULL) {
    printf("Failed to rebind select() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_send = dlsym(handle, "send")) == NULL) {
    printf("Failed to rebind send() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_sendto = dlsym(handle, "sendto")) == NULL) {
    printf("Failed to rebind sendto() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_sendmsg = dlsym(handle, "sendmsg")) == NULL) {
    printf("Failed to rebind sendmsg() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_setsockopt = dlsym(handle, "setsockopt")) == NULL) {
    printf("Failed to rebind setsockopt() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
  if ((realcall_shutdown = dlsym(handle, "shutdown")) == NULL) {
    printf("Failed to rebind shutdown() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
#ifdef LINUX
  if ((realcall_sockatmark = dlsym(handle, "sockatmark")) == NULL) {
    printf("Failed to rebind sockatmark() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
#endif
  if ((realcall_socket = dlsym(handle, "socket")) == NULL) {
    printf("Failed to rebind socket() in nssock.doDynamicCallRebinding: %s\n", dlerror());
    exit(1);
  }
}
#endif


/* ---------------------------------------- */
/* void ns_init()
 * Arguments: void
 * Returns:   0 ok; -1 otherwise
 * Desc:      Initialises the sockets library
 *            by opening a socket to a remote
 *            host for remote monitoring
 */
int ns_init()
{
  int ret;
  char str[LARGESTR], *timestr, hostname[LARGESTR];
  struct sockaddr_in dest;
  char *connaddr, *port, *debug, *dynLink;
  int connport;
  SOCKET tempfd;

#ifdef WIN32
  //Initialise the winsock library (version 2.2 compat)
  WORD wVersionRequested;
  WSADATA wsaData;
  int err;

  wVersionRequested = MAKEWORD( 2, 2 );
  err = WSAStartup( wVersionRequested, &wsaData );
  if ( err != 0 ) {
   fprintf(stderr, "Could not init winsock\n");
   abort();
  }
  if ( LOBYTE( wsaData.wVersion ) != 2 ||
       HIBYTE( wsaData.wVersion ) != 2 ) {
    fprintf(stderr, "Could not init winsock. Version 2 not available\n");
    WSACleanup( );
    abort();
  }

  // Initialise the timing library
  recalibrate();
#endif

  //Get the nssock environment variables
  str[0] = '\0';
  connaddr = getenv("NS_ADDR");
  if(connaddr == NULL) {
    fprintf(stderr, "NS_ADDR not set in the environment\n");
    abort();
  }
  port = getenv("NS_PORT");
  if(port == NULL) {
    fprintf(stderr, "NS_PORT not set in the environment\n");
    abort();
  }
  connport = atoi(port);
  debug = getenv("NS_DEBUG");
  if(debug == NULL)
    debugf = 0;
  else
    debugf = atoi(debug);

  dynLink = getenv("NS_DYNAMICLINK");
  if(dynLink == NULL)
    dynamicLink = 0;
  else
    dynamicLink = 1;

#ifdef WIN32
  dynamicLink = 0;  /* off by default on WIN32 */
#endif

  if(dynamicLink != 0)
    doDynamicCallRebinding();

  //Flag that the library has been initialised
  init = 1;

  //Create the socket we write debug to
  if(dynamicLink == 0)
    tempfd = socket(PF_INET, SOCK_STREAM, 0);
  else
    tempfd = realcall_socket(PF_INET, SOCK_STREAM , 0);
  if(tempfd == INVALID_SOCKET)
    sock_err(ERRNO, "Failed to create socket");

  //If possible, change the socket descriptor
  //to a high numbered one in order not to
  //interfere with our model
#ifdef LINUX
  sd = (SOCKET)HIGHFD;

  if(dynamicLink == 0) {
    if(dup2(tempfd, sd) == INVALID_SOCKET)
      sock_err(ERRNO, "Failed to duplicate socket");
    if(close(tempfd) == SOCKET_ERROR)
      sock_err(ERRNO, "Failed to close temporary fd");
  } else {
     if(realcall_dup2(tempfd, sd) == INVALID_SOCKET)
      sock_err(ERRNO, "Failed to duplicate socket");
     if(realcall_close(tempfd) == SOCKET_ERROR)
       sock_err(ERRNO, "Failed to close temporary fd");
  }
#else
  sd = tempfd;
#endif

#ifndef WIN32
  //Ensure we don't die because of a SIGPIPE
  signal(SIGPIPE, SIG_IGN);
#endif

  //Connect the socket to a listening server
  //using the ip/port specified in the environment
  //variables
#ifndef WIN32
  bzero(&dest, sizeof(dest));
#else
  ZeroMemory(&dest, sizeof(dest));
#endif
  dest.sin_family = AF_INET;
  dest.sin_addr.s_addr = inet_addr(connaddr);
  dest.sin_port = htons(connport);
  if(dynamicLink == 0)
    ret = connect(sd, (struct sockaddr*)&dest, sizeof(dest));
  else
    ret = realcall_connect(sd, (struct sockaddr*)&dest, sizeof(dest));

  if(ret == SOCKET_ERROR) {
    fprintf(stderr, "Failed to connect to socket %s:%d\n",
            connaddr, connport);
    sprintf(str, "Failed to connect to socket %s:%d",
			connaddr, connport);
    if(dynamicLink == 0)
      close(sd);
    else
      realcall_close(sd);
    sock_err(ERRNO, str);
  }

  //Output some usefull information to the debug socket
  sprintf(str, "(* ns_socket library initialised: connected to %s:%d *)\n",
	  connaddr, connport);
  print(str);

  gethostname(hostname, LARGESTR);
  time(&currtime);
  timestr = ctime(&currtime);
  timestr[strlen(timestr)-1] = '\0';
  sprintf(str, "(* Date: %s Host: %s *)\n", timestr, hostname);
  print(str);
  sprintf(str, "(* NTP STATUS: \n");
  print(str);
  printNTPheader(sd);
  sprintf(str, " *)\n");
  print(str);
  print("(* -------------------------------------------------------------------------- *)\n");
  print("(* BEGIN *)\n");
  return 0;
}


/* ---------------------------------------- */
/* void print(char *str)
 * Arguments: str - pointer to string buffer
 * Returns:   void
 * Desc:      Prints the buffer contents by
 *            writing it to the socket
 *            connected at initialisation time
 */
void print(char *str)
{
  int i, res;
  size_t len;
  char *string;

  //If the nssock library has not been initialised yet,
  //then initialise it as we won't have a socket
  //to write to!
  if(init == 0)
    ns_init();

  len = strlen(str);
  string = str;

  //Write the string to the socket, trying
  //NUMSENDRETRIES times.
  for(i=0; i<NUMSENDRETRIES; i++) {
    if(dynamicLink == 0)
      res = send(sd, string, (int)len, 0);
    else
      res = realcall_send(sd, string, (int)len, 0);

    if(res != SOCKET_ERROR) {
      if(len != res) { //whole string not sent
	string += res; //so send the remainder
	len = strlen(string);
	i=0;           //reset number of retries
	continue;	   //and try again
      } else {         //else all is written
	return;		   //so return
      }
    } else {				//an error occured so retry send
      if(ERRNO == EAGAIN)   //if error is EAGAIN then reset
	i=0;				//the number of retries counter
        continue;
    }
  }

  //Couldn't write all the data to the socket
  sock_err(ERRNO, "failed to write to connected socket");
}


/* ---------------------------------------- */
/* void prn_call(int tid, char * msg, ...)
 * Arguments: tid - current process id
 *            msg - message to print
 * Returns:   void
 * Desc:      Print a HOL TCP semantics style
 *            call label containing tid and
 *            the message
 */
void prn_call(int tid, char *msg, ...)
{
  va_list args;
  char str[LARGESTR], str2[LARGESTR];

  va_start(args, msg);
  vsprintf(str2, msg, args);
  sprintf(str, "%sLh_call (TID %d, %s);\n", ns_getcurrenttime_last(currentTime, NS_TIME_SIZE),
	  tid, str2);
  print(str);
  va_end(args);
}


/* ---------------------------------------- */
/* void prn_ret(int tid, char *msg, ...)
 * Arguments: tid - process identifier
 *            msg - pointer to string
 * Returns:   void
 * Desc:      Prints a HOL TCP semantics style
 *            return label containg tid and msg
 */
void prn_ret(int tid, char *msg, ...)
{
  va_list args;
  char str[LARGESTR], str2[LARGESTR];

  va_start(args, msg);
  vsprintf(str2, msg, args);
  sprintf(str, "%sLh_return (TID %d, %s);\n", ns_getcurrenttime_first(currentTime, NS_TIME_SIZE),
	  tid, str2);
  print(str);
  va_end(args);
}

/* void formatIP(char *ip)
 * Arguments: ip - ASCII ip address
 * Returns:   ip address with spaces instead of dots
 * Desc:      Procudes ip addresses suitable for HOL
 */
char *formatIP(char *ip)
{
  int len = strlen(ip);
  int i;

  for(i=0; i<len; i++)
    if(ip[i] == '.')
      ip[i] = ' ';

  return ip;
}


/* Returns the netmask as an int */
int formatNetmask(int nm)
{
  if(nm == 0xffffffff) return 32;
  if(nm == 0xfffffffc) return 31;
  if(nm == 0xfffffff8) return 30;
  if(nm == 0xfffffff4) return 29;
  if(nm == 0xfffffff0) return 28;
  if(nm == 0xffffffc0) return 27;
  if(nm == 0xffffff80) return 26;
  if(nm == 0xffffff40) return 25;
  if(nm == 0xffffff00) return 24;
  if(nm == 0xfffffc00) return 23;
  if(nm == 0xfffff800) return 22;
  if(nm == 0xfffff400) return 21;
  if(nm == 0xfffff000) return 20;
  if(nm == 0xffffc000) return 19;
  if(nm == 0xffff8000) return 18;
  if(nm == 0xffff4000) return 17;
  if(nm == 0xffff0000) return 16;
  if(nm == 0xfffc0000) return 15;
  if(nm == 0xfff80000) return 14;
  if(nm == 0xfff40000) return 13;
  if(nm == 0xfff00000) return 12;
  if(nm == 0xffc00000) return 11;
  if(nm == 0xff800000) return 10;
  if(nm == 0xff400000) return 9;
  if(nm == 0xff000000) return 8;
  if(nm == 0xfc000000) return 7;
  if(nm == 0xf8000000) return 6;
  if(nm == 0xf4000000) return 5;
  if(nm == 0xf0000000) return 4;
  if(nm == 0xc0000000) return 3;
  if(nm == 0x80000000) return 2;
  if(nm == 0x40000000) return 1;
  if(nm == 0x00000000) return 0;
  return -1;
}

/* Returns the process id */
int ns_getpid()
{
  return getpid();
}

/* ---------------------------------------- */
/* SOCKET ns_accept(SOCKET s, struct ....)
 * Desc: Wrapper for standard UNIX style
 *       accept() sockets call
 * Notes: SOME(If addr is NULL then normal socket
 * call does not return (ip, port) to the
 * caller. Unless an error occurs, a connection
 * succeeds thus we need the (ip, port) pair
 * for the remote end ==> we alter the observational
 * semantics of this call slightly!)
 */
SOCKET ns_accept(SOCKET s, struct sockaddr *addr, socklen_t *addrlen)
{
  SOCKET retval;
  int pid;
  char is2[SMSTR], ps2[SMSTR], err[MEDSTR], str[MEDSTR];
  struct sockaddr thisaddr;
  socklen_t thisaddrlen;
  is2[0] = ps2[0] =  err[0] = str[0] = '\0';

#ifndef WIN32
  if(s<0) {
    sprintf(str, "(* ASSERTION FAILED ns_accept(): call to accept with socket descriptor <0 *)\n");
    print(str);
    return EINVAL;
  }
#endif

  pid = getpid();

  prn_call(pid, "accept(FD %d)", s);

  thisaddrlen = sizeof(struct sockaddr);

  //Get the remote ip and port regardless of whether the
  //caller wants it. It needs to be passed out in the HOL return
  //label.
  if(dynamicLink == 0)
    retval = accept(s, &thisaddr, &thisaddrlen);
  else
    retval = realcall_accept(s, &thisaddr, &thisaddrlen);

  if(retval != SOCKET_ERROR) {
    sprintf(is2, "(IP %s)", formatIP(inet_ntoa(((struct sockaddr_in*)&thisaddr)->sin_addr)));
    sprintf(ps2, "(Port %d)", ntohs(((struct sockaddr_in*)&thisaddr)->sin_port));

    //If the caller requests the ip and port then copy it out
    //Use min of the two lengths to be safe
    if(addr != NULL) {
      *addrlen = min(*addrlen, thisaddrlen);
      memcpy(addr, &thisaddr, *addrlen);
    }
    prn_ret(pid, "OK(FD %d, (%s, %s))", retval, is2, ps2);
  } else {  //returned an error
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


/* ---------------------------------------- */
/* int ns_bind(SOCKET sockfd, struct ....)
 * Desc: Wrapper for standard UNIX style
 *       bind() sockets call
 * Notes: NONE
 */
int ns_bind(SOCKET sockfd, struct sockaddr *my_addr, socklen_t addrlen)
{
  int pid, retval;
  char is1[SMSTR], ps1[SMSTR], err[MEDSTR], str[MEDSTR];
  is1[0] = ps1[0] = err[0] =  str[0] = '\0';

#ifndef WIN32
  if(sockfd<0) {
    sprintf(str, "(* ASSERTION FAILED in ns_bind(): call to accept with socket descriptor <0 *)\n");
    print(str);
    return EINVAL;
  }
#endif

  pid = getpid();

  //Output the HOL TCP call label
  if(my_addr != NULL) {
    if(((struct sockaddr_in*)my_addr)->sin_addr.s_addr != 0)
      sprintf(is1, "SOME (IP %s)", formatIP(inet_ntoa(
	      ((struct sockaddr_in*)my_addr)->sin_addr)));
    else
      sprintf(is1, "NONE");

    if(((struct sockaddr_in*)my_addr)->sin_port != 0)
      sprintf(ps1, "SOME (Port %d)", ntohs(
             ((struct sockaddr_in*)my_addr)->sin_port));
    else
      sprintf(ps1, "NONE");
  }
  prn_call(pid, "bind(FD %d, %s, %s)", sockfd, is1, ps1);

  //Call the real bind and output HOL results label
  if(dynamicLink == 0)
    retval = bind(sockfd, my_addr, addrlen);
  else
    retval = realcall_bind(sockfd, my_addr, addrlen);

  if(retval != SOCKET_ERROR)
    prn_ret(pid, "OK()");
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


/* ---------------------------------------- */
/* int ns_close(SOCKET fd)
 * Desc: Wrapper for standard UNIX style
 *       close() sockets call
 * Notes: NONE
 */
int ns_close(SOCKET fd)
{
  int retval, pid;
  char err[MEDSTR];
  err[0] = '\0';

  pid = getpid();
  prn_call(pid, "close(FD %d)", fd);

  if(dynamicLink == 0)
    retval = close(fd);
  else
    retval = realcall_close(fd);

  if(retval != SOCKET_ERROR)
    prn_ret(pid, "OK()");
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


/* ---------------------------------------- */
/* int ns_connect(SOCKET sockfd, const struct ....)
 * Desc: Wrapper for standard UNIX style
 *       connect() sockets call
 * Notes: SOME(If the sin_family member of serv_addr
 * is set to AF_UNSPEC then this outputs a HOL disconnect
 * call rather than connect.)
 */
int ns_connect(SOCKET sockfd, const struct sockaddr *serv_addr,
	       socklen_t addrlen)
{
  int retval, pid;
  char err[MEDSTR], str[MEDSTR], is1[SMSTR], ps1[SMSTR];
  err[0] = str[0] = is1[0] = ps1[0] = '\0';

  pid = getpid();

  if(serv_addr == NULL) {
    sprintf(str, "(* ASSERTION FAILED in ns_connect(): bad call as serv_addr is NULL. *)\n");
    print(str);
    abort();
  }

  if(((struct sockaddr_in *)serv_addr)->sin_family == AF_UNSPEC) {
    prn_call(pid, "disconnect(FD %d)", sockfd);
    if(dynamicLink == 0)
      retval = connect(sockfd, serv_addr, addrlen);
    else
      retval = realcall_connect(sockfd, serv_addr, addrlen);
    if(retval != SOCKET_ERROR) {
      prn_ret(pid, "OK()");
    }
    else if(retval == SOCKET_ERROR) {
      NS_ERROR_CODE = ERRNO;
      prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
    }
    return retval;
  }
  else {
    sprintf(is1, "IP %s", formatIP(inet_ntoa(((struct sockaddr_in*)serv_addr)->sin_addr)));
    if(((struct sockaddr_in*)serv_addr)->sin_port != 0)
      sprintf(ps1, "SOME (Port %d)", ntohs(((struct sockaddr_in*)serv_addr)->sin_port));
    else
      sprintf(ps1, "NONE");
    prn_call(pid, "connect(FD %d, %s, %s)", sockfd, is1, ps1);

    if(dynamicLink == 0)
      retval = connect(sockfd, serv_addr, addrlen);
    else
      retval = realcall_connect(sockfd, serv_addr, addrlen);

    if(retval != SOCKET_ERROR)
      prn_ret(pid, "OK()");
    else {
      NS_ERROR_CODE = ERRNO;
      prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
    }
    return retval;
  }
}


#ifndef WIN32
/* ---------------------------------------- */
/* int ns_dup(SOCKET oldfd)
 * Desc: Wrapper for standard UNIX style
 *       dup() sockets call
 * Notes: SOME(Windows does not have any dup()
 * calls -- see ../Notes/windows.txt)
 */
SOCKET ns_dup(SOCKET oldfd)
{
  SOCKET retval;
  int pid;
  char err[MEDSTR];
  err[0] = '\0';

  pid = getpid();
  prn_call(pid, "dup(FD %d)", oldfd);

  if(dynamicLink == 0)
    retval = dup(oldfd);
  else
    retval = realcall_dup(oldfd);

  if(retval != SOCKET_ERROR)
    prn_ret(pid, "OK(FD %d)", retval);
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}

/* ---------------------------------------- */
/* int ns_dup2(SOCKET oldfd, SOCKET newfd)
 * Desc: Wrapper for standard UNIX style
 *       dup2() sockets call
 * Notes: SOME(Windows does not have any dup()
 * calls -- see ../Notes/windows.txt)
 */
SOCKET ns_dup2(SOCKET oldfd, SOCKET newfd)
{
  SOCKET retval;
  int pid;
  char err[MEDSTR];
  err[0] = '\0';

  pid = getpid();
  prn_call(pid, "dupfd(FD %d, %d)", oldfd, newfd);

  if(dynamicLink == 0)
    retval = dup2(oldfd, newfd);
  else
    retval = realcall_dup2(oldfd, newfd);

  if(retval != SOCKET_ERROR)
    prn_ret(pid, "OK(FD %d)", retval);
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}
#endif //#ifndef WIN32

#ifndef WIN32
/* ---------------------------------------- */
/* int ns_fcntl(SOCKET fd, int cmd, long arg)
 * Desc: Wrapper for standard UNIX style
 *       fcntl() sockets call
 * Implements: getfileflags(), setfileflags()
 * Notes: SOME(Windows does not use fcntl() calls.
 * It uses ioctlsocket() calls instead.)
 *
 * IMPORTANT: see notes regarding the va_args problem
 * workaround implemented in this definition
 */
int ns_fcntl(SOCKET fd, int cmd, long arg)
{
  int retval, pid;
  char err[50];

  if(cmd == F_GETFL) {
    pid = getpid();
    prn_call(pid, "getfileflags(FD %d)", fd);

    if(dynamicLink == 0)
      retval = fcntl(fd, cmd);
    else
      retval = realcall_fcntl(fd, cmd);

    if(retval != SOCKET_ERROR) {
/* On BSD and LINUX other flags are often set so this test fails */
//    if((retval & ~(O_NONBLOCK | O_ASYNC)) > 0) {
//	fprintf(stderr, "nssock ns_fcntl: flags other than O_NONBLOCK, O_ASYNC set. Assert failed!\n");
//	abort();
//      }
      prn_ret(pid, "OK([%s])", (retval & O_NONBLOCK) != 0 ?
	      ((retval & O_ASYNC) != 0 ? "O_NONBLOCK; O_ASYNC" : "O_NONBLOCK")
	      : ((retval & O_ASYNC) != 0 ? "O_ASYNC" : ""));
    } else {
      NS_ERROR_CODE = ERRNO;
      prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
    }
  } else if(cmd == F_SETFL) {
    pid = getpid();
    prn_call(pid, "setfileflags(FD %d, [%s])", fd,
	     (arg & O_NONBLOCK) != 0 ?
	     ((arg & O_ASYNC) != 0 ? "O_NONBLOCK; O_ASYNC" : "O_NONBLOCK")
	     : ((arg & O_ASYNC) != 0 ? "O_ASYNC" : ""));
    if(dynamicLink == 0)
      retval = fcntl(fd, cmd, arg);
    else
      retval = realcall_fcntl(fd, cmd, arg);
    if(retval != SOCKET_ERROR) {
      prn_ret(pid, "OK()");
    } else {
      NS_ERROR_CODE = ERRNO;
      prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
    }

  } else { //call not for us
    if(dynamicLink == 0)
      retval = fcntl(fd, cmd, arg);
    else
      retval = realcall_fcntl(fd, cmd,arg);
    return retval;
  }

  return retval;
}

#endif //#ifndef WIN32


/* ---------------------------------------- */
/* int ns_getsockname(SOCKET s, struct ....)
 * Desc: Wrapper for standard UNIX style
 *       getsockname() sockets call
 * Notes: NONE
 */
int ns_getsockname(SOCKET s, struct sockaddr *name,
	            socklen_t *namelen)
{
  int pid, retval;
  char err[MEDSTR], is1[SMSTR], ps1[SMSTR];
  err[0] = is1[0] = ps1[0] = '\0';

  pid = getpid();
  prn_call(pid, "getsockname(FD %d)", s);

  //Make the real call and print HOL return label
  if(dynamicLink == 0)
    retval = getsockname(s, name, namelen);
  else
    retval = realcall_getsockname(s, name, namelen);
  if(retval != SOCKET_ERROR) {
    if(((struct sockaddr_in*)name)->sin_addr.s_addr != 0)
      sprintf(is1, "SOME(IP %s)", formatIP(inet_ntoa(((struct sockaddr_in*)name)->sin_addr)));
    else
      sprintf(is1, "NONE");

    if(((struct sockaddr_in*)name)->sin_port != 0)
      sprintf(ps1, "SOME(Port %d)", ntohs(((struct sockaddr_in*)name)->sin_port));
    else
      sprintf(ps1, "NONE");

    prn_ret(pid, "OK(%s, %s)", is1, ps1);
  }
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


#ifdef BSD
/* ---------------------------------------- */
/* int ns_getifaddrs()
 * Desc: Wrapper for BSD style getifaddrs()
 *       sockets call
 * Notes: NONE
 */
int ns_getifaddrs(struct ifaddrs **ifad)
{
  struct otherips_ll {
    struct sockaddr_in addr;
    struct otherips_ll * next;
  };
  struct ifid_info {
    char name[SMSTR];
    struct sockaddr_in primaryip;
    struct otherips_ll * otherips;
    struct sockaddr_in netmask;
    struct ifid_info * next;
  };
  int retval, pid;
  struct ifaddrs *ifad_internal;
  struct ifid_info * ifids_head, * ifids_free, *ifids_next_prn, **ifids;
  struct otherips_ll *otherips, *otherips_next;
  char ifid[SMSTR], ip[SMSTR], others[LARGESTR], netmask[SMSTR], temp[SMSTR], output[10*LARGESTR], lastname[SMSTR], err[MEDSTR];
  ifids_head = NULL;
  ifids = &ifids_head;
  err[0] = ifid[0] = ip[0] = others[0] = netmask[0] = output[0] = lastname[0] = '\0';

  pid = getpid();
  prn_call(pid, "getifaddrs()");

  if(dynamicLink == 0)
    retval = getifaddrs(&ifad_internal);
  else
    retval = realcall_getifaddrs(&ifad_internal);

  if(retval != SOCKET_ERROR) {
    struct ifaddrs * ifads = ifad_internal;
    while(ifads != NULL) {
      if(strncmp(lastname, ifads->ifa_name, SMSTR) == 0) {
	//now add this IP address to the otherips for that interface
	switch(ifads->ifa_addr->sa_family) {
	case AF_INET:
	  otherips = (*ifids)->otherips;
	  if(otherips != NULL) {
	    while(otherips->next != NULL) {
	      otherips = otherips->next;
	    }
	    otherips->next = malloc(sizeof(struct otherips_ll));
	  }
	  else {
	    otherips = malloc(sizeof(struct otherips_ll));
	  }
	  (otherips->next)->addr = *((struct sockaddr_in *)ifads->ifa_addr);
	  (otherips->next)->next = NULL;
	default:
	  ifads = ifads->ifa_next;
	  break;
	}
      }
      else {
	//create a new interface info structure and fill it in
	switch((ifads->ifa_addr)->sa_family) {
	case AF_INET:
	  if(ifids_head != NULL)
	    ifids = &((*ifids)->next);
	  *ifids = malloc(sizeof(struct ifid_info));
	  memcpy(lastname, ifads->ifa_name, SMSTR);
	  strncpy((*ifids)->name, (ifads->ifa_name), SMSTR);
	  (*ifids)->primaryip = *((struct sockaddr_in *)ifads->ifa_addr);
	  (*ifids)->otherips = NULL;
	  (*ifids)->netmask = *((struct sockaddr_in *)ifads->ifa_netmask);
	default:
	  ifads = ifads->ifa_next;
	  break;
	}

      }
    }
    ifids = &((*ifids)->next);
    *ifids = NULL;
    freeifaddrs(*ifad);

    // now do the return
    ifids_next_prn = ifids_head;
    sprintf(output, "[");
    while(ifids_next_prn != NULL) {
      sprintf(ifid, "(IFID %s, ", ifids_next_prn->name);
      strcat(output, ifid);
      sprintf(ip, "IP %s, ", formatIP(inet_ntoa((ifids_next_prn->primaryip).sin_addr)));
      strcat(output, ip);
      otherips = ifids_next_prn->otherips;
      sprintf(others, "[");
      while(otherips != NULL) {
	sprintf(temp, "IP %s", formatIP(inet_ntoa((otherips->addr).sin_addr)));
	otherips = otherips->next;
	if(otherips != NULL) strcat(temp, ";");
	strcat(others, temp);
      }
      strcat(others, "], ");
      strcat(output, others);
      sprintf(netmask, "NETMASK %d)", formatNetmask(ntohl((ifids_next_prn)->netmask.sin_addr.s_addr)));
      strcat(output, netmask);

      ifids_next_prn = ifids_next_prn->next;
      if(ifids_next_prn != NULL) strcat(output, ";");
    }
    strcat(output, "]");
    prn_ret(pid, "OK(%s)", output);


    //free the memory
    for(ifids_free = ifids_head; ifids_free != NULL; ifids_free = ifids_next_prn) {
      if(ifids_free->otherips != NULL) {
	for(otherips = ifids_free->otherips; otherips != NULL; otherips = otherips_next) {
	  otherips_next = otherips->next;
	  free(otherips);
	}
      }
      ifids_next_prn = ifids_free->next;
      free(ifids_free);
    }

    if(dynamicLink == 0)
      retval = getifaddrs(ifad);
    else
      retval = realcall_getifaddrs(ifad);
    return retval;
  }
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (\"%s\")", geterrmsg(err, NS_ERROR_CODE));
    return retval;
  }
}
#endif // BSD


/* ---------------------------------------- */
/* int ns_getpeername(SOCKET s, struct ....)
 * Desc: Wrapper for standard UNIX style
 *       getpeername() sockets call
 * Notes: NONE
 */
int ns_getpeername(SOCKET s, struct sockaddr *name,
		   socklen_t *namelen)
{
  int retval, pid;
  char err[MEDSTR], ps2[SMSTR], *is2;
  err[0] = ps2[0] = '\0';

  pid = getpid();
  prn_call(pid, "getpeername(FD %d)", s);

  if(dynamicLink == 0)
    retval = getpeername(s, name, namelen);
  else
    retval = realcall_getpeername(s, name, namelen);
  if(retval != SOCKET_ERROR) {
    is2 = formatIP(inet_ntoa(((struct sockaddr_in*)name)->sin_addr));
    sprintf(ps2, "Port %d", ntohs(((struct sockaddr_in*)name)->sin_port));
    prn_ret(pid, "OK(IP %s, %s)", is2, ps2);
  }
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


/* ---------------------------------------- */
/* int ns_getsockopt(SOCKET s, int level, ...)
 * Desc: Wrapper for standard UNIX style
 *       getsockopt() sockets call
 * Implements: getsockbopt(), getsocknopt(),
 *             getsocktopt(), getsockerr(),
 *             getsocklistening()
 * Notes: SOME(The marshalling of the values
 * returned by the flags which return time values
 * needs to be verified as correct)
 */
int ns_getsockopt(SOCKET s, int level, int optname,
		  void *optval, socklen_t *optlen)
{
  int retval, pid;
  char err[MEDSTR];
  err[0] = '\0';

  pid = getpid();

  if(level != SOL_SOCKET) { //call not for us
    if(dynamicLink == 0)
      return (getsockopt(s, level, optname, optval, optlen));
    else
      return (realcall_getsockopt(s, level, optname, optval, optlen));
  }

  switch(optname) {
    case SO_REUSEADDR:
      prn_call(pid, "getsockbopt(FD %d, SO_REUSEADDR)", s);
      break;
    case SO_KEEPALIVE:
      prn_call(pid, "getsockbopt(FD %d, SO_KEEPALIVE)", s);
      break;
    case SO_OOBINLINE:
      prn_call(pid, "getsockbopt(FD %d, SO_OOBINLINE)", s);
      break;
    case SO_DONTROUTE:
      prn_call(pid, "getsockbopt(FD %d, SO_DONTROUTE)", s);
      break;
    case SO_BROADCAST:
      prn_call(pid, "getsockbopt(FD %d, SO_BROADCAST)", s);
      break;
    case SO_SNDBUF:
      prn_call(pid, "getsocknopt(FD %d, SO_SNDBUF)", s);
      break;
    case SO_RCVBUF:
      prn_call(pid, "getsocknopt(FD %d, SO_RCVBUF)", s);
      break;
    case SO_LINGER:
      prn_call(pid, "getsocktopt(FD %d, SO_LINGER)", s);
      break;
    case SO_ERROR:
      prn_call(pid, "getsockerr(FD %d)", s);
      break;
    case SO_ACCEPTCONN:
      prn_call(pid, "getsocklistening(FD %d)", s);
      break;

#ifdef LINUX
    case SO_BSDCOMPAT:
      prn_call(pid, "getsockbopt(FD %d, SO_BSDCOMPAT)", s);
      break;
#endif

#ifndef WIN32
    case SO_SNDLOWAT:
      prn_call(pid, "getsocknopt(FD %d, SO_SNDLOWAT)", s);
      break;
    case SO_RCVLOWAT:
      prn_call(pid, "getsocknopt(FD %d, SO_RCVLOWAT)", s);
      break;
    case SO_SNDTIMEO:
      prn_call(pid, "getsocktopt(FD %d, SO_SNDTIMEO)", s);
      break;
    case SO_RCVTIMEO:
      prn_call(pid, "getsocktopt(FD %d, SO_RCVTIMEO)", s);
      break;
#endif
    default:
      //Not a call that we're interested in
      if(dynamicLink == 0)
	return (getsockopt(s, level, optname, optval, optlen));
      else
	return (realcall_getsockopt(s, level, optname, optval, optlen));
      break;
  }

  if(dynamicLink == 0)
    retval = getsockopt(s, level, optname, optval, optlen);
  else
    retval = realcall_getsockopt(s, level, optname, optval, optlen);
  if(retval != SOCKET_ERROR) {
    switch(optname) {
      case SO_REUSEADDR:
	prn_ret(pid, "OK(%s)", (*((int*)optval) != 0) ? "T" : "F");
       	break;
      case SO_KEEPALIVE:
        prn_ret(pid, "OK(%s)", (*((int*)optval) != 0) ? "T" : "F");
	break;
      case SO_OOBINLINE:
	prn_ret(pid, "OK(%s)", (*((int*)optval) != 0) ? "T" : "F");
        break;
      case SO_DONTROUTE:
	prn_ret(pid, "OK(%s)", (*((int*)optval) != 0) ? "T" : "F");
	break;
      case SO_BROADCAST:
	prn_ret(pid, "OK(%s)", (*((int*)optval) != 0) ? "T" : "F");
	break;
      case SO_SNDBUF:
	prn_ret(pid, "OK(%d)", *((int*)optval));
	break;
      case SO_RCVBUF:
	prn_ret(pid, "OK(%d)", *((int*)optval));
        break;
      case SO_LINGER:
	if(((struct linger*)optval)->l_onoff == 0)
	  prn_ret(pid, "OK(NONE)");
	else
	  prn_ret(pid, "OK(SOME(%d, %d))", ((struct linger*)optval)->l_linger, 0);
	break;
      case SO_ERROR:
	if((*(int*)optval) == 0)
	  prn_ret(pid, "OK()");
	else {
	  NS_ERROR_CODE = *(int*)optval;
	  prn_ret(pid, "FAIL (%s)", geterrmsg(err,*(int*)optval));
	}
	break;
      case SO_ACCEPTCONN:
	prn_ret(pid, "OK(%s)", (*((int*)optval) != 0) ? "T" : "F");
	break;

#ifdef LINUX
      case SO_BSDCOMPAT:
	prn_ret(pid, "OK(%s)", (*((int*)optval) != 0) ? "T" : "F");
        break;
#endif

#ifndef WIN32
      case SO_SNDLOWAT:
	prn_ret(pid, "OK(%d)", *((int*)optval));
        break;
      case SO_RCVLOWAT:
	prn_ret(pid, "OK(%d)", *((int*)optval));
        break;
      case SO_SNDTIMEO:
	prn_ret(pid, "OK(SOME(%d, %d))", ((struct timeval*)optval)->tv_sec,
		((struct timeval*)optval)->tv_usec);
        break;
      case SO_RCVTIMEO:
	prn_ret(pid, "OK(SOME(%d, %d))", ((struct timeval*)optval)->tv_sec,
		((struct timeval*)optval)->tv_usec);
        break;
#endif
      default:
	print("(* getsockopt(): ERROR? Had an unexpected optname returned *)\n");
	break;
    }
  } else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}



#ifndef WIN32
/* ---------------------------------------- */
/* int ns_ioctl(SOCKET d, unsigned long request, ...)
 * Desc: Wrapper for standard UNIX style
 *       ioctl() sockets call
 * Implements: sockatmark()
 * Notes: SOME(Accepts a variable number
 * of arguements)
 */
int ns_ioctl(SOCKET d, unsigned long request, ...)
{
  va_list args;
  char err[MEDSTR];
  int *argp;
  int retval, pid;
  struct ifreq * ifreq;
  err[0] = '\0';

  if(request == SIOCATMARK) {

    //Initialise variable args
    va_start(args, request);
    argp = va_arg(args, int*);

    pid = getpid();
    prn_call(pid, "sockatmark(FD %d)", d);

    //Make the real ioctl call and print HOL labels
    if(dynamicLink == 0)
      retval = ioctl(d, request, argp);
    else
      retval = realcall_ioctl(d, request, argp);

    if(retval == 0) {
      if(argp == NULL) {
	print("(* ns_ioctl: got argp == NULL -- something went seriously wrong *)");
	va_end(args);
	return retval;
      }
      prn_ret(pid, "OK(%s)",  *argp != 0  ? "T" : "F");
    } else {
      NS_ERROR_CODE = ERRNO;
      prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
    }

    va_end(args);
    return retval;
  }

  else if(request == SIOCGIFNETMASK) {
    // we do this call, but don't output any HOL labels for it
    va_start(args, request);
    ifreq = va_arg(args, struct ifreq *);

    if(dynamicLink == 0)
      retval = ioctl(d, request, ifreq);
    else
      retval = realcall_ioctl(d, request, ifreq);

    va_end(args);
    return retval;
  }

  else if(request == SIOCGIFCONF) {

    struct otherips_ll {
      struct sockaddr_in addr;
      struct otherips_ll * next;
    };
    struct ifid_info {
      char name[SMSTR];
      struct sockaddr_in primaryip;
      struct otherips_ll * otherips;
      struct sockaddr_in netmask;
      struct ifid_info * next;
    };

    int len, lastlen;
    char * buf, *ptr, lastname[SMSTR], *cptr, temp[SMSTR], output[10*LARGESTR], ifid[SMSTR], ip[SMSTR], others[LARGESTR], netmask[SMSTR];
    struct ifconf ifc_internal, *ifc;
    struct ifid_info *ifids_head, *ifids_next_prn, *ifids_free, **ifids_next;
    struct ifreq *ifr, ifrcopy;
    struct sockaddr_in *sinptr;
    struct otherips_ll * otherips, *otherips_next;
    va_start(args, request);
    ifc = va_arg(args, struct ifconf *);

    lastname[0] = temp[0] = output[0] = ifid[0] = ip[0] = others[0] = netmask[0] = '\0';

    //print the call label
    pid = getpid();
    prn_call(pid, "getifaddrs()");

    //we don't know how many interfaces to allocate space for, so guess 100, and increment until we have enough buffer space for them all
    lastlen = 0;
    len = 100 * sizeof(struct ifreq);
    for( ; ; ) {
      buf = malloc(len);
      ifc_internal.ifc_len = len;
      ifc_internal.ifc_buf = buf;

      if(dynamicLink == 0)
	retval = ioctl(d, SIOCGIFCONF, &ifc_internal);
      else
	retval = realcall_ioctl(d, SIOCGIFCONF, &ifc_internal);

      if(retval < 0) {
	if(errno != EINVAL || lastlen != 0) {
	  NS_ERROR_CODE = ERRNO;
	  prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
	  return retval;
	}
      }
      else {
	if(ifc_internal.ifc_len == lastlen)
	  break;
	lastlen = ifc_internal.ifc_len;
      }
      len += 10 * sizeof(struct ifreq);
      free(buf);
    }

    ifids_head = NULL;
    ifids_next = &ifids_head;

    for(ptr = buf; ptr < buf + ifc_internal.ifc_len;) {
      ifr = (struct ifreq *) ptr;
      len = sizeof(struct sockaddr_in);
      ptr += sizeof(ifr->ifr_name) + len;

      if(ifr->ifr_addr.sa_family != AF_INET)
	continue; // ignore non-IP addresses
      if((cptr = strchr(ifr->ifr_name, ':')) != NULL)
	*cptr = 0; // get rid of the :0 in aliases for Linux

      if(strncmp(lastname, ifr->ifr_name, 16) == 0) {
	//now add this IP address to the otherips for that interface
	otherips = (*ifids_next)->otherips;
	while(otherips->next != NULL) {
	  otherips = otherips->next;
	}
	otherips->next = malloc(sizeof(struct otherips_ll));
	switch(ifr->ifr_addr.sa_family) {
	case AF_INET:
	  sinptr = (struct sockaddr_in *)&ifr->ifr_addr;
	  (otherips->next)->addr = *sinptr;
	  break;
	default:
	  break;
	}
	(otherips->next)->next = NULL;
      }

      else {
	//create a new interface info structure and fill it in
	if(ifids_head != NULL)
	  ifids_next = &((*ifids_next)->next);
	*ifids_next = malloc(sizeof(struct ifid_info));
	memcpy(lastname, ifr->ifr_name, 16);
	memcpy(&ifrcopy,ifr, sizeof(struct ifconf));
	memcpy((*ifids_next)->name, ifr->ifr_name, sizeof(ifr->ifr_name));
	(*ifids_next)->name[strlen(ifr->ifr_name)] = '\0';
	(*ifids_next)->otherips = NULL;
	switch(ifr->ifr_addr.sa_family) {
	case AF_INET:
	  memcpy(&(*ifids_next)->primaryip, (struct sockaddr_in *)&ifr->ifr_addr, sizeof(struct sockaddr_in));
	  break;
	default:
	  break;
	}
	// now get the netmask
	if(dynamicLink == 0)
	  ioctl(d, SIOCGIFNETMASK, &ifrcopy);
	else
	  realcall_ioctl(d, SIOCGIFNETMASK, &ifrcopy);
	memcpy(&(*ifids_next)->netmask, (struct sockaddr_in *)&ifrcopy.ifr_addr, sizeof(struct sockaddr_in));

      }
    }
    (*ifids_next)->next = NULL;

    // now output the HOL label
    ifids_next_prn = ifids_head;
    sprintf(output, "[");
    while(ifids_next_prn != NULL) {
      sprintf(ifid, "(IFID %s, ", ifids_next_prn->name);
      strcat(output, ifid);
      sprintf(ip, "IP %s, ", formatIP(inet_ntoa((ifids_next_prn->primaryip).sin_addr)));
      strcat(output, ip);
      otherips = ifids_next_prn->otherips;
      sprintf(others, "[");
      while(otherips != NULL) {
	sprintf(temp, "IP %s", formatIP(inet_ntoa((otherips->addr).sin_addr)));
	otherips = otherips->next;
	if(otherips != NULL) strcat(temp, ";");
	strcat(others, temp);
      }
      strcat(others, "], ");
      strcat(output, others);
      sprintf(netmask, "NETMASK %d)", formatNetmask(ntohl((ifids_next_prn)->netmask.sin_addr.s_addr)));
      strcat(output, netmask);

      ifids_next_prn = ifids_next_prn->next;

      if(ifids_next_prn != NULL) strcat(output, ";");
    }
    strcat(output, "]");
    prn_ret(pid, "OK(%s)", output);

    //free the memory
    for(ifids_free = ifids_head; ifids_free != NULL; ifids_free = ifids_next_prn) {
      if(ifids_free->otherips != NULL) {
	for(otherips = ifids_free->otherips; otherips != NULL; otherips = otherips_next) {
	  otherips_next = otherips->next;
	  free(otherips);
	}
      }
      ifids_next_prn = ifids_free->next;
      free(ifids_free);
    }

    va_end(args);
    if(dynamicLink == 0)
      retval = ioctl(d, request, ifc);
    else
      retval = realcall_ioctl(d, request, ifc);
    return retval;
  }
  else { //call not for us
  if(dynamicLink == 0)
      retval = ioctl(d, request, args);
    else
      retval = realcall_ioctl(d, request, args);
    return retval;
  }
}
#endif


#ifdef WIN32
/* ---------------------------------------- */
/* int ns_ioctlsocket(SOCKET s, long cmd, ...)
 * Desc: Wrapper for standard Windows style
 *       ioctlsocket() sockets call
 * Implements: getfileflags(), setfileflags(),
 *             sockatmark()
 * Notes: NONE
 *
 */
int ns_ioctlsocket(SOCKET s, long cmd, u_long* argp)
{
  int retval, pid;
  u_long val;
  char err[LARGESTR];
  pid = getpid();

  if(cmd == FIONBIO) { //getfilefl or setfilefl
    if(argp == NULL) {
      //we're doing a getfilebfl()
      prn_call(pid, "getfileflags(FD %d)", s);
      retval = ioctlsocket(s, cmd, argp);
      if(retval != SOCKET_ERROR)
  	prn_ret(pid, "OK(%s)", (*argp != 0) ? "[O_NONBLOCK]" : "[]");
      else {
	NS_ERROR_CODE = ERRNO;
	prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
      }
    } else {
      //we're doing a setfilebfl()
      prn_call(pid, "setfileflags(FD %d, [%s])", s, *argp == 0 ? "" : "O_NONBLOCK");
      retval = ioctlsocket(s, cmd, argp);
      if(retval != SOCKET_ERROR)
	prn_ret(pid, "OK()");
      else {
	NS_ERROR_CODE = ERRNO;
	prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
      }
    }
  } else if(cmd == SIOCATMARK) {  //sockatmark
    //we're doing a sockatmark()
    prn_call(pid, "sockatmark(FD %d)", s);
    retval = ioctlsocket(s, cmd, argp);
    if(retval != SOCKET_ERROR)
      prn_ret(pid, "OK(%s)", (*argp != 0) ? "T" : "F");
    else {
      NS_ERROR_CODE = ERRNO;
      prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
    }
  } else { //something we're not interested in
    retval = ioctlsocket(s, cmd, argp);
  }

  return retval;
}
#endif


/* ---------------------------------------- */
/* int ns_listen(SOCKET s, int backlog)
 * Desc: Wrapper for standard UNIX style
 *       listen() sockets call
 * Notes: NONE
 */
int ns_listen(SOCKET s, int backlog)
{
  int retval, pid;
  char err[MEDSTR];
  err[0] = '\0';

  pid = getpid();
  prn_call(pid, "listen(FD %d, %d)", s, backlog);

  if(dynamicLink == 0)
    retval = listen(s, backlog);
  else
    retval = realcall_listen(s, backlog);

  if(retval != SOCKET_ERROR)
    prn_ret(pid, "OK()");
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}



#ifdef LINUX
/* ---------------------------------------- */
/* void prn_sigmask(sigset_t *sigmask)
 * Arguements: sigmask - ptr to a signal mask
 * Returns: void
 * Desc: Prints a comma seperated list of the
 * names of signals present in sigmask to
 * the connected socket. Used by pselect()
 * implementation.
 */
void prn_sigmask(sigset_t *sigmask)
{
  char str[512];
  int first = 1;
  str[0] = '\0';

  if(sigismember(sigmask, SIGABRT) == 1) {
    sprintf(str, (first == 1) ? "SIGABRT" : "%s, SIGABRT", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGALRM) == 1) {
    sprintf(str, (first == 1) ? "SIGALRM" : "%s, SIGALRM", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGBUS) == 1) {
    sprintf(str, (first == 1) ? "SIGBUS" : "%s, SIGBUS", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGCHLD) == 1) {
    sprintf(str, (first == 1) ? "SIGCHLD" : "%s, SIGCHLD", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGCONT) == 1) {
    sprintf(str, (first == 1) ? "SIGCONT" : "%s, SIGCONT", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGFPE) == 1) {
    sprintf(str, (first == 1) ? "SIGFPE" : "%s, SIGFPE", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGHUP) == 1) {
    sprintf(str, (first == 1) ? "SIGHUP" : "%s, SIGHUP", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGILL) == 1) {
    sprintf(str, (first == 1) ? "SIGILL" : "%s, SIGILL", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGINT) == 1) {
    sprintf(str, (first == 1) ? "SIGINT" : "%s, SIGINT", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGKILL) == 1) {
    sprintf(str, (first == 1) ? "SIGKILL" : "%s, SIGKILL", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGPIPE) == 1) {
    sprintf(str, (first == 1) ? "SIGPIPE" : "%s, SIGPIPE", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGQUIT) == 1) {
    sprintf(str, (first == 1) ? "SIGQUIT" : "%s, SIGQUIT", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGSEGV) == 1) {
    sprintf(str, (first == 1) ? "SIGSEGV" : "%s, SIGSEGV", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGSTOP) == 1) {
    sprintf(str, (first == 1) ? "SIGSTOP" : "%s, SIGSTOP", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGTERM) == 1) {
    sprintf(str, (first == 1) ? "SIGTERM" : "%s, SIGTERM", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGTSTP) == 1) {
    sprintf(str, (first == 1) ? "SIGTSTP" : "%s, SIGTSTP", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGTTIN) == 1) {
    sprintf(str, (first == 1) ? "SIGTTIN" : "%s, SIGTTIN", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGTTOU) == 1) {
    sprintf(str, (first == 1) ? "SIGTTOU" : "%s, SIGTTOU", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGUSR1) == 1) {
    sprintf(str, (first == 1) ? "SIGUSR1" : "%s, SIGUSR1", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGUSR2) == 1) {
    sprintf(str, (first == 1) ? "SIGUSR2" : "%s, SIGUSR2", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGPOLL) == 1) {
    sprintf(str, (first == 1) ? "SIGPOLL" : "%s, SIGPOLL", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGPROF) == 1) {
    sprintf(str, (first == 1) ? "SIGPROF" : "%s, SIGPROF", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGSYS) == 1) {
    sprintf(str, (first == 1) ? "SIGSYS" : "%s, SIGSYS", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGTRAP) == 1) {
    sprintf(str, (first == 1) ? "SIGTRAP" : "%s, SIGTRAP", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGURG) == 1) {
    sprintf(str, (first == 1) ? "SIGURG" : "%s, SIGURG", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGVTALRM) == 1) {
    sprintf(str, (first == 1) ? "SIGVTALRM" : "%s, SIGVTALRM", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGXCPU) == 1) {
    sprintf(str, (first == 1) ? "SIGXCPU" : "%s, SIGXCPU", str);
    first = 0;
  }
  if(sigismember(sigmask, SIGXFSZ) == 1) {
    sprintf(str, (first == 1) ? "SIGXFSZ" : "%s, SIGXFSZ", str);
    first = 0;
  }

  if(first == 1)
    print ("NONE");
  else {
    sprintf(str, "SOME [%s]", str);
    print(str);
  }

}


/* ---------------------------------------- */
/* int ns_pselect(int n, fd_set *readfds, ...)
 * Desc: Wrapper for standard POSIX style
 *       pselect() sockets call
 * Notes: SOME(Linux only. Be warned -- this
 * function contains a lot of textual list
 * processing ;-)
 */
int ns_pselect (int n, fd_set *readfds, fd_set *writefds,
		fd_set *exceptfds, const struct timespec *timeout,
		sigset_t *sigmask)
{
  int pid, retval, i, first = 1;
  char str[MEDSTR], err[MEDSTR];
  str[0] = err[0] = '\0';

  //Output HOL TCP call label
  pid = getpid();
  sprintf(str, "%sLh_call (TID %d, pselect([", ns_getcurrenttime_last(currentTime, NS_TIME_SIZE), pid);
  print(str);

  for(i=0; i<n; i++) {
    if(FD_ISSET(i, readfds)) {
      sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
      print(str);
      first = 0;
    }
  }

  print("], [");
  first = 1;
  for(i=0; i<n; i++) {
    if(FD_ISSET(i, writefds)) {
      sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
      print(str);
      first = 0;
    }
  }

  print("], [");
  first = 1;
  for(i=0; i<n; i++) {
    if(FD_ISSET(i, exceptfds)) {
      sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
      print(str);
      first = 0;
    }
  }

  print("], ");

  if(timeout == NULL || ((int)timeout->tv_sec == 0 && (int)timeout->tv_nsec == 0))
    print("NONE, ");
  else {
    sprintf(str, "SOME (%d, %d), ", (int)timeout->tv_sec, (int)timeout->tv_nsec);
    print(str);
  }
  prn_sigmask(sigmask);
  print("));\n");

  //Make the real socket call and output HOL return labels
  if(dynamicLink == 0)
    retval = pselect(n , readfds, writefds, exceptfds, timeout, sigmask);
  else
    retval = realcall_pselect(n , readfds, writefds, exceptfds, timeout, sigmask);

  if(retval != SOCKET_ERROR) {
    sprintf(str, "%sLh_return (TID %d, OK([",
		ns_getcurrenttime_first(currentTime, NS_TIME_SIZE), pid);
    print(str);
    first = 1;
    for(i=0; i<n; i++) {
      if(FD_ISSET(i, readfds)) {
	sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
	print(str);
	first = 0;
      }
    }

    print("], ([");
    first = 1;
    for(i=0; i<n; i++) {
      if(FD_ISSET(i, writefds)) {
	sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
	print(str);
	first = 0;
      }
    }

    print("], [");
    first = 1;
    for(i=0; i<n; i++) {
      if(FD_ISSET(i, exceptfds)) {
	sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
	print(str);
	first = 0;
      }
    }
    print("])));\n");
  }
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}
#endif //#ifdef Linux



/* ---------------------------------------- */
/* int ns_recv(SOCKET s, void *buf, ....)
 * Desc: Wrapper for standard UNIX style
 *       recv() sockets call
 * Notes: NONE
 */
int ns_recv(SOCKET s, void *buf, size_t len, int flags)
{
  int pid, retval, comma = 0;
  char err[MEDSTR], blist[MEDSTR], str[MEDSTR];
  err[0] = blist[0] = str[0] = '\0';

  pid = getpid();

  if(flags & MSG_PEEK) {
    sprintf(blist, "MSG_PEEK");
    comma = 1;
  }

  if(flags & MSG_OOB) {
    if(comma == 0) {
      sprintf(blist, "MSG_OOB");
      comma = 1;
    } else
      sprintf(blist, "%s; MSG_OOB", blist);
  }

#ifndef WIN32
  if(flags & MSG_WAITALL) {
    if(comma == 0) {
      sprintf(blist, "MSG_WAITALL");
      comma = 1;
    } else
      sprintf(blist, "%s; MSG_WAITALL", blist);
  }

  if(flags & MSG_DONTWAIT) {
    if(comma == 0) {
      sprintf(blist, "MSG_DONTWAIT");
      comma = 1;
    } else
      sprintf(blist, "%s; MSG_DONTWAIT", blist);
  }
#endif

  prn_call(pid, "recv(FD %d, %d, [%s])", s, len, blist);

  if(dynamicLink == 0)
    retval = recv(s, buf, (int)len, flags);
  else
    retval = realcall_recv(s, buf, (int)len, flags);

  if(retval != SOCKET_ERROR) {
     sprintf(str, "%sLh_return (TID %d, OK(\"",
      	      ns_getcurrenttime_first(currentTime, NS_TIME_SIZE), pid);
    print(str);

    //nsbuffer must be larger than retval to ensure there is enough
    //room to delimit special characters
    nsbuffer = malloc(retval*3);
    assert(nsbuffer);
    delimit_print(nsbuffer, retval*3, buf, retval);
    free(nsbuffer);

    print("\", NONE));\n");
  } else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


/* ---------------------------------------- */
/* int ns_recvfrom(SOCKET s, void *buf, ....)
 * Desc: Wrapper for standard UNIX style
 *       recvfrom() sockets call
 * Notes: NONE
 */
int ns_recvfrom(SOCKET s, void *buf, size_t len, int flags,
		struct sockaddr *from, socklen_t *fromlen)
{
  int pid, retval, comma = 0;
  char err[MEDSTR], blist[MEDSTR], str[MEDSTR], ip_and_port[MEDSTR], ip[SMSTR], port[SMSTR];
  err[0] = blist[0] = str[0] = ip[0] = port[0] = ip_and_port[0] = '\0';

  pid = getpid();

  if(flags & MSG_PEEK) {
    sprintf(blist, "MSG_PEEK");
    comma = 1;
  }

  if(flags & MSG_OOB) {
    if(comma == 0) {
      sprintf(blist, "MSG_OOB");
      comma = 1;
    } else
      sprintf(blist, "%s; MSG_OOB", blist);
  }

#ifndef WIN32
  if(flags & MSG_WAITALL) {
    if(comma == 0) {
      sprintf(blist, "MSG_WAITALL");
      comma = 1;
    } else
      sprintf(blist, "%s; MSG_WAITALL", blist);
  }
  if(flags & MSG_DONTWAIT) {
    if(comma == 0) {
      sprintf(blist, "MSG_DONTWAIT");
      comma = 1;
    } else
      sprintf(blist, "%s; MSG_DONTWAIT", blist);
  }
#endif


  prn_call(pid, "recv(FD %d, %d, [%s])", s, len, blist);

  if(dynamicLink == 0)
    retval = recvfrom(s, buf, (int)len, flags, from, fromlen);
  else
    retval = realcall_recvfrom(s, buf, (int)len, flags, from, fromlen);

  if(retval != SOCKET_ERROR) {
    if(from != NULL) {
      sprintf(port, "SOME(Port %d)", ntohs(((struct sockaddr_in *)from)->sin_port));
      sprintf(ip, "SOME(IP %s)", formatIP(inet_ntoa(((struct sockaddr_in*)from)->sin_addr)));
      sprintf(ip_and_port, "SOME((%s, %s),T)", ip, port);
    }
    else {
      sprintf(ip_and_port, "NONE");
    }
    sprintf(str, "%sLh_return (TID %d, OK(\"",
            ns_getcurrenttime_first(currentTime, NS_TIME_SIZE), pid);
    print(str);

    //nsbuffer must be larger than retval to ensure there is enough
    //room to delimit special characters
    nsbuffer = malloc(retval*3);
    assert(nsbuffer);
    delimit_print(nsbuffer, retval*3, buf, retval);
    free(nsbuffer);

    print("\", ");
    print(ip_and_port);
    print("));\n");
  } else {
    NS_ERROR_CODE = ERRNO;
#ifdef WIN32
    if(NS_ERROR_CODE == WSAEMSGSIZE) { //EMSGSIZE on WinXP
      if(from != NULL) {
	sprintf(port, "SOME(Port %d)", ntohs(((struct sockaddr_in *)from)->sin_port));
	sprintf(ip, "SOME(IP %s)", formatIP(inet_ntoa(((struct sockaddr_in*)from)->sin_addr)));
	sprintf(ip_and_port, "SOME((%s, %s),F)", ip, port);
      }
      else {
	sprintf(ip_and_port, "NONE");
      }
      sprintf(str, "%sLh_return (TID %d, OK(\"",
	      ns_getcurrenttime_first(currentTime, NS_TIME_SIZE), pid);
      print(str);

      //nsbuffer must be larger than retval to ensure there is enough
      //room to delimit special characters
      nsbuffer = malloc(len*3);
      assert(nsbuffer);
      delimit_print(nsbuffer, len*3, buf, len);
      free(nsbuffer);

      print("\", ");
      print(ip_and_port);
      print("));\n");
    }
    else
      prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
#else
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
#endif
  }

  return retval;

}


#ifndef WIN32
/* ---------------------------------------- */
/* int ns_recvmsg(SOCKET s, struct ....)
 * Desc: Wrapper for standard UNIX style
 *       recvmsg() sockets call
 * Notes: SOME(Not supported on Windows)
 */
int ns_recvmsg(SOCKET s, struct msghdr *msg, int flags)
{
  int pid, retval, comma = 0;
  unsigned int len;
  char err[MEDSTR], blist[MEDSTR], str[MEDSTR], ip_and_port[MEDSTR];
  err[0] = blist[0] = str[0] = ip_and_port[0] = '\0';

  pid = getpid();

  if(flags & MSG_PEEK) {
    sprintf(blist, "MSG_PEEK");
    comma = 1;
  }

  if(flags & MSG_OOB) {
    if(comma == 0) {
      sprintf(blist, "MSG_OOB");
      comma = 1;
    } else
      sprintf(blist, "%s; MSG_OOB", blist);
  }

  if(flags & MSG_WAITALL) {
    if(comma == 0) {
      sprintf(blist, "MSG_WAITALL");
      comma = 1;
    } else
      sprintf(blist, "%s; MSG_WAITALL", blist);
  }

  if(msg->msg_name != NULL) {
    sprintf(ip_and_port, "SOME(SOME( IP %s),SOME( Port %d))", formatIP(inet_ntoa(((struct sockaddr_in *)msg)->sin_addr)),ntohs(((struct sockaddr_in *)msg)->sin_port));
  }
  else {
    sprintf(ip_and_port, "NONE");
  }

  print("(* Warning: using recvmsg *)");
  len = calc_iovec_len(msg->msg_iov, msg->msg_iovlen);
  prn_call(pid, "recv(FD %d, %d, [%s]);", s, len, blist);

  if(dynamicLink == 0)
    retval = recvmsg(s, msg, flags);
  else
    retval = recvmsg(s, msg, flags);

  if(retval != SOCKET_ERROR) {
    sprintf(str, "%sLh_return (TID %d, OK(\"",
            ns_getcurrenttime_first(currentTime, NS_TIME_SIZE), pid);
    print(str);

    //nsbuffer must be larger than iovlen to ensure there is enough
    //room to delimit special characters
    nsbuffer = malloc(msg->msg_iovlen*3);
    assert(nsbuffer);
    iovec_print(nsbuffer, msg->msg_iovlen*3, msg->msg_iov, msg->msg_iovlen);
    free(nsbuffer);

    print("\",");
    print(ip_and_port);
    print("));\n");
  } else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}
#endif //#ifndef WIN32



/* ---------------------------------------- */
/* int ns_select(SOCKET n, fd_set *readfds, ...)
 * Desc: Wrapper for standard UNIX style
 *       select() sockets call
 * Notes: SOME(Be warned -- large amounts of
 * textual list processing ;-)
 */
int ns_select (SOCKET n, fd_set *readfds, fd_set *writefds,
	       fd_set *exceptfds, struct timeval *timeout)
{
  int pid, retval, first = 1;
  unsigned int i;
  char str[MEDSTR], err[MEDSTR];
  str[0] = err[0] = '\0';

  pid = getpid();


  sprintf(str, "%sLh_call (TID %d, pselect([",
	  ns_getcurrenttime_last(currentTime, NS_TIME_SIZE), pid);
  print(str);

  for(i=0; i<n; i++) {
    if(FD_ISSET(i, readfds)) {
      sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
      print(str);
      first = 0;
    }
  }

  print("], [");
  first = 1;
  for(i=0; i<n; i++) {
    if(FD_ISSET(i, writefds)) {
      sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
      print(str);
      first = 0;
    }
  }

  print("], [");
  first = 1;
  for(i=0; i<n; i++) {
    if(FD_ISSET(i, exceptfds)) {
      sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
      print(str);
      first = 0;
    }
  }

  print("], ");

  if(timeout == NULL)
    print("NONE, ");
  else {
    sprintf(str, "SOME (%d, %d), ", (int)timeout->tv_sec, (int)timeout->tv_usec*1000);
    print(str);
  }
  print("NONE));\n");

  if(dynamicLink == 0)
    retval = select((int)n , readfds, writefds, exceptfds, timeout);
  else
    retval = realcall_select((int)n , readfds, writefds, exceptfds, timeout);

  if(retval != SOCKET_ERROR) {
    sprintf(str, "%sLh_return (TID %d, OK([",
    	    ns_getcurrenttime_first(currentTime, NS_TIME_SIZE), pid);
    print(str);

    first = 1;
    for(i=0; i<n; i++) {
      if(FD_ISSET(i, readfds)) {
	sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
	print(str);
	first = 0;
      }
    }

    print("], ([");
    first = 1;
    for(i=0; i<n; i++) {
      if(FD_ISSET(i, writefds)) {
	sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
	print(str);
	first = 0;
      }
    }

    print("], [");
    first = 1;
    for(i=0; i<n; i++) {
      if(FD_ISSET(i, exceptfds)) {
	sprintf(str, (first == 1) ? "FD %d" : "; FD %d", i);
	print(str);
	first = 0;
      }
    }
    print("])));\n");
  }
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


/* ---------------------------------------- */
/* int ns_send(SOCKET s, const void *msg, ...)
 * Desc: Wrapper for standard UNIX style
 *       send() sockets call
 * Notes: SOME(Following our TCP model, the
 * HOL return label contains tail of the buffer
 * if the whole buffer was not sent)
 */
int ns_send(SOCKET s, const void *msg, size_t len, int flags)
{
  int pid, retval, comma = 0;
  char err[MEDSTR], blist[MEDSTR], str[MEDSTR];
  err[0] = blist[0] = str[0] = '\0';

  pid = getpid();

  if(flags & MSG_OOB) {
    sprintf(blist, "MSG_OOB");
    comma = 1;
  }

  if(flags & MSG_PEEK) {
    if(comma == 0) {
      sprintf(blist, "MSG_PEEK");
    } else
      sprintf(blist, "%s; MSG_PEEK", blist);
  }

#ifndef WIN32
  if(flags & MSG_DONTWAIT) {
    if(comma == 0) {
      sprintf(blist, "MSG_DONTWAIT");
    } else
      sprintf(blist, "%s; MSG_DONTWAIT", blist);
  }

  if(flags & MSG_WAITALL) {
    if(comma == 0) {
      sprintf(blist, "MSG_WAITALL");
    } else
      sprintf(blist, "%s; MSG_WAITALL", blist);
  }
#endif

  sprintf(str, "%sLh_call (TID %d, send(FD %d, NONE ,\"",
	  ns_getcurrenttime_last(currentTime, NS_TIME_SIZE), pid, s);
  print(str);

  //nsbuffer must be larger than len to ensure there is enough
  //room to delimit special characters
  nsbuffer = malloc(len*3);
  assert(nsbuffer);
  delimit_print(nsbuffer, len*3, msg, len);
  free(nsbuffer);

  sprintf(str, "\", [%s]));\n", blist);
  print(str);

  if(dynamicLink == 0)
    retval = send(s, msg, (int)len, flags);
  else
    retval = realcall_send(s, msg, (int)len, flags);

  if(retval != SOCKET_ERROR) {
    sprintf(str, "%sLh_return (TID %d, OK(\"",
  	    ns_getcurrenttime_first(currentTime, NS_TIME_SIZE), pid);
    print(str);
    if(retval != len) {
      //nsbuffer must be larger than (len-retval) to ensure there is enough
      //room to delimit special characters
      nsbuffer = malloc((len-retval)*3);
      assert(nsbuffer);
      delimit_print(nsbuffer, (len-retval)*3, (unsigned char*)msg+retval, len-retval);
      free(nsbuffer);
    }
    print("\"));\n");
  } else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


/* ---------------------------------------- */
/* int ns_sendto(SOCKET s, const void *msg, ....)
 * Desc: Wrapper for standard UNIX style
 *       sendto() sockets call
 * Notes: SOME(Following our TCP model, the
 * HOL return label contains tail of the buffer
 * if the whole buffer was not sent)
 */
int ns_sendto(SOCKET s, const void *msg, size_t len, int flags,
	      const struct sockaddr *to, socklen_t tolen)
{
  int pid, retval, comma = 0;
  char err[MEDSTR], blist[MEDSTR], str[LARGESTR], ip_and_port[MEDSTR], ip[MEDSTR], port[MEDSTR];
  err[0] = blist[0] = str[0] = ip_and_port[0] = ip[0] = port[0] = '\0';

  /* if(to != NULL) {
    sprintf(str, "(* ASSERTION FAILED in sendto(): call made with specific TO address. *)\n");
    print(str);
    return EINVAL;
    }
  */

  pid = getpid();


    if(flags & MSG_OOB) {
    sprintf(blist, "MSG_OOB");
    comma = 1;
  }

#ifndef WIN32
  if(flags & MSG_DONTWAIT) {
    if(comma == 0) {
      sprintf(blist, "MSG_DONTWAIT");
    } else
      sprintf(blist, "%s; MSG_DONTWAIT", blist);
  }
#endif

  // first check if it is an internet address
  if(to->sa_family == AF_INET) {
    sprintf(ip, "SOME(IP %s,", formatIP(inet_ntoa(((struct sockaddr_in *)to)->sin_addr)));
    sprintf(port, "Port %d)", ntohs(((struct sockaddr_in *)to)->sin_port));
    sprintf(ip_and_port, "%s %s", ip, port);
  }
  else {
    sprintf(ip_and_port, "NONE");
  }


  //print("(* Warning: using sendto *)");
  sprintf(str, "%sLh_call(TID %d, send(FD %d, %s, \"",
    ns_getcurrenttime_last(currentTime, NS_TIME_SIZE), pid, s, ip_and_port);
  print(str);

  //nsbuffer must be larger than len to ensure there is enough
  //room to delimit special characters
  nsbuffer = malloc(len*3);
  assert(nsbuffer);
  delimit_print(nsbuffer, len*3, msg, len);
  free(nsbuffer);

  sprintf(str, "\", [%s]));\n", blist);
  print(str);

  if(dynamicLink == 0)
    retval = sendto(s, msg, (int)len, flags, to, tolen);
  else
    retval = realcall_sendto(s, msg, (int)len, flags, to, tolen);

  if(retval != SOCKET_ERROR) {
    sprintf(str, "%sLh_return (TID %d, OK(\"",
	    ns_getcurrenttime_first(currentTime, NS_TIME_SIZE), pid);
    print(str);
    if(retval != len) {
      //nsbuffer must be larger than (len-retval) to ensure there is enough
      //room to delimit special characters
      nsbuffer = malloc((len-retval)*3);
      assert(nsbuffer);
      delimit_print(nsbuffer, (len-retval)*3, (unsigned char*)msg+retval, len-retval);
      free(nsbuffer);
    }
    print("\"));\n");
  } else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }
  return retval;
}

#ifndef WIN32
/* ---------------------------------------- */
/* int ns_sendmsg(SOCKET s, const struct ....)
 * Desc: Wrapper for standard UNIX style
 *       sendmsg() sockets call
 * Notes: SOME(Following our TCP model, the
 * HOL return label contains tail of the buffer
 * if the whole buffer was not sent. Not
 * supported by Windows)
 */
int ns_sendmsg(SOCKET s, const struct msghdr *msg, int flags)
{
  int pid, retval, comma = 0;
  unsigned int len;
  char err[MEDSTR], blist[MEDSTR], str[MEDSTR], ip_and_port[MEDSTR];
  err[0] = blist[0] = str[0] = ip_and_port[0] = '\0';

  /* if(msg->msg_name != NULL) {
    sprintf(str, "(* ASSERTION FAILED in sendmsg(): call made with specific TO address. *)\n");
    print(str);
    return EINVAL;
    }
  */

  if(msg->msg_name != NULL) {
    sprintf(ip_and_port, "SOME(IP %s, Port %d)", formatIP(inet_ntoa(((struct sockaddr_in *)msg)->sin_addr)),ntohs(((struct sockaddr_in *)msg)->sin_port));
  }
  else {
    sprintf(ip_and_port, "NONE");
  }

  pid = getpid();

  if(flags & MSG_OOB) {
    sprintf(blist, "MSG_OOB");
    comma = 1;
  }

  if(flags & MSG_DONTWAIT) {
    if(comma == 0) {
      sprintf(blist, "MSG_DONTWAIT");
    } else
      sprintf(blist, "%s; MSG_DONTWAIT", blist);
  }

  print("(* Warning: using sendmsg *)");
  sprintf(str, "%sLh_call (TID %d, send(FD %d, %s, ",
          ns_getcurrenttime_last(currentTime, NS_TIME_SIZE), pid, s, ip_and_port);
  print(str);

  //nsbuffer must be larger than len to ensure there is enough
  //room to delimit special characters
  nsbuffer = malloc(msg->msg_iovlen*3);
  assert(nsbuffer);
  iovec_print(nsbuffer, msg->msg_iovlen*3, msg->msg_iov, msg->msg_iovlen);
  free(nsbuffer);

  sprintf(str, ", [%s]));\n", blist);
  print(str);
  len = calc_iovec_len(msg->msg_iov, msg->msg_iovlen);

  if(dynamicLink == 0)
    retval = sendmsg(s, msg, flags);
  else
    retval = realcall_sendmsg(s, msg, flags);

  if(retval != SOCKET_ERROR) {
     sprintf(str, "%sLh_return (TID %d, OK(\"",
	      ns_getcurrenttime_first(currentTime, NS_TIME_SIZE), pid);
    print(str);
    if(retval != len) {
      //nsbuffer must be larger than len to ensure there is enough
      //room to delimit special characters
      nsbuffer= malloc(msg->msg_iovlen*3);
      assert(nsbuffer);
      iovec_printtail(nsbuffer, msg->msg_iovlen*3, msg->msg_iov, msg->msg_iovlen, retval);
      free(nsbuffer);
    }
    print("\"));\n");
  } else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}
#endif //#ifndef WIN32


/* ---------------------------------------- */
/* int ns_setsockopt(SOCKET s, int level, ...)
 * Desc: Wrapper for standard UNIX style
 *       setsockopt() sockets call
 * Implements: setsockbopt(), setsocknopt(),
 *             setsocktopt()
 * Notes: SOME(The printing of the time arguments
 * in the HOL TCP call labels needs verification)
 */
int ns_setsockopt(SOCKET s, int level, int optname,
		  const void *optval, socklen_t optlen)
{
  int retval, pid;
  char err[MEDSTR];
  err[0] = '\0';

  pid = getpid();
  if(level != SOL_SOCKET) { //we're not interested
    if(dynamicLink == 0)
      return (setsockopt(s, level, optname, optval, optlen));
    else
      return (realcall_setsockopt(s, level, optname, optval, optlen));
  }

  switch(optname) {
    case SO_REUSEADDR:
      prn_call(pid, "setsockbopt(FD %d, SO_REUSEADDR, %s)", s,
	       *((int*)optval) != 0 ? "T" : "F");
      break;
    case SO_KEEPALIVE:
      prn_call(pid, "setsockbopt(FD %d, SO_KEEPALIVE, %s)", s,
	       *((int*)optval) != 0 ? "T" : "F");
      break;
    case SO_OOBINLINE:
      prn_call(pid, "setsockbopt(FD %d, SO_OOBINLINE, %s)", s,
	       *((int*)optval) != 0 ? "T" : "F");
      break;
    case SO_DONTROUTE:
      prn_call(pid, "setsockbopt(FD %d, SO_DONTROUTE, %s)", s,
	       *((int*)optval) != 0 ? "T" : "F");
      break;
    case SO_BROADCAST:
      prn_call(pid, "setsockbopt(FD %d, SO_BROADCAST, %s)", s,
	       *((int*)optval) != 0 ? "T" : "F");
      break;
    case SO_SNDBUF:
      prn_call(pid, "setsocknopt(FD %d, SO_SNDBUF, %d)", s,
	       *((int*)optval));
      break;
    case SO_RCVBUF:
      prn_call(pid, "setsocknopt(FD %d, SO_RCVBUF, %d)", s,
	       *((int*)optval));
      break;
    case SO_LINGER:
      if(((struct linger*)optval)->l_onoff == 0)
	prn_call(pid, "setsocktopt(FD %d, SO_LINGER, NONE)", s);
      else
	prn_call(pid, "setsocktopt(FD %d, SO_LINGER, SOME (%d, %d))", s,
		 ((struct linger*)optval)->l_linger, 0);
      break;

#ifdef LINUX
    case SO_BSDCOMPAT:
      prn_call(pid, "setsockbopt(FD %d, SO_BSDCOMPAT, %s)", s,
	       *((int*)optval) != 0 ? "T" : "F");
      break;
#endif

#ifndef WIN32
    case SO_SNDLOWAT:
      prn_call(pid, "setsocknopt(FD %d, SO_SNDLOWAT, %d)", s,
	       *((int*)optval));
      break;
    case SO_RCVLOWAT:
      prn_call(pid, "setsocknopt(FD %d, SO_RCVLOWAT, %d)", s,
	       *((int*)optval));
      break;
    case SO_SNDTIMEO:
      prn_call(pid, "setsocktopt(FD %d, SO_SNDTIMEO, SOME (%d, %d))", s,
	       ((struct timeval*)optval)->tv_sec,
		((struct timeval*)optval)->tv_usec);
      break;
    case SO_RCVTIMEO:
      prn_call(pid, "setsocktopt(FD %d, SO_RCVTIMEO, SOME (%d, %d))", s,
	       ((struct timeval*)optval)->tv_sec,
		((struct timeval*)optval)->tv_usec);
      break;
#endif
    default:
      //Not a call that we're interested in
      if(dynamicLink == 0)
	return (setsockopt(s, level, optname, optval, optlen));
      else
	return (realcall_setsockopt(s, level, optname, optval, optlen));
      break;
  }

  if(dynamicLink == 0)
    retval = setsockopt(s, level, optname, optval, optlen);
  else
    retval = realcall_setsockopt(s, level, optname, optval, optlen);

  if(retval != SOCKET_ERROR)
    prn_ret(pid, "OK()");
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


/* ---------------------------------------- */
/* int ns_shutdown(SOCKET s, int how)
 * Desc: Wrapper for standard UNIX style
 *       shutdown() sockets call
 * Notes: NONE
 */
int ns_shutdown(SOCKET s, int how)
{
  int retval, pid;
  char err[MEDSTR];
  err[0] = '\0';

  pid = getpid();
  prn_call(pid, "shutdown(FD %d, %s, %s)", s,
	   ((how == SD_RECEIVE) || (how == SD_BOTH)) ? "T" : "F",
	   ((how == SD_SEND) || (how == SD_BOTH)) ? "T" : "F");

  if(dynamicLink == 0)
    retval = shutdown(s, how);
  else
    retval = realcall_shutdown(s, how);

  if(retval != SOCKET_ERROR)
    prn_ret(pid, "OK()");
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


#ifndef WIN32
/* ---------------------------------------- */
/* int ns_sockatmark(SOCKET s)
 * Desc: Wrapper for standard POSIX style
 *       sockatmark() sockets call
 * Notes: SOME(Supported by Linux only. This
 * is just a wrapper around the ioctl() call
 * as per Stevens p574)
 */
int ns_sockatmark(SOCKET s)
{
  int retval;

  // We deliberately do not care about dynamicLink'ing here!
  if(ns_ioctl(s, SIOCATMARK, &retval))
    return SOCKET_ERROR;

  return (retval != 0 ? 1 : 0);
}
#else
int ns_sockatmark(SOCKET s)
{
  print("(* ns_sockatmark: not implemented. *)\n");
  return SOCKET_ERROR;
}
#endif //#ifndef WIN32


/* ---------------------------------------- */
/* SOCKET ns_socket(int domain, int type, ...)
 * Desc: Wrapper for standard UNIX style
 *       socket() sockets call
 * Notes: NONE
 */
SOCKET ns_socket(int domain, int type, int protocol)
{
  SOCKET retval;
  int pid;
  char err[MEDSTR];
  int dummy=1;

  err[0] = '\0';

  pid = getpid();
  if(type == SOCK_STREAM && (!protocol || protocol==6)) {
    prn_call(pid, "socket(SOCK_STREAM)");
  }
  else if(type == SOCK_DGRAM && (!protocol || protocol==17)) {
    prn_call(pid, "socket(SOCK_DGRAM)");
  }
  else {
    if(dynamicLink == 0)
      retval = socket(domain, type, protocol);
    else
      retval = realcall_socket(domain, type, protocol);
    return retval;  // silently do it without logging; we're not interested
  }

  if(dynamicLink == 0)
    retval = socket(domain, type, protocol);
  else
    retval = realcall_socket(domain, type, protocol);

  if(retval != INVALID_SOCKET) {
    prn_ret(pid, "OK(FD %d)", retval);

    if(debugf != 0)
      if(ns_setsockopt(retval, SOL_SOCKET, SO_DEBUG, &dummy, sizeof(dummy)) != 0)
	sock_err(ERRNO, "Debug mode requested but setting SO_DEBUG failed");
  }
  else {
    NS_ERROR_CODE = ERRNO;
    prn_ret(pid, "FAIL (%s)", geterrmsg(err, NS_ERROR_CODE));
  }

  return retval;
}


#ifndef WIN32
/* ---------------------------------------- */
/* int min(int a, int b)
 * Desc: Returns minimum of args
 */
int min(int a, int b)
{
  return (a<b) ? a : b;
}
#endif

/* ---------------------------------------- */
/* Stuff for testing purposes only          */
/* ---------------------------------------- */
#ifdef DEBUG
int main()
{
  /* Insert test code here */
  return 0;
}
#endif
