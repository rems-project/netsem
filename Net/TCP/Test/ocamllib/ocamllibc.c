#include "../nssock/ns_sockets.h"
#include "unixsupport.h"
#include "camlsupport.h"

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/misc.h>

#include <assert.h>
#include <stdlib.h>

#ifndef WIN32
#include <net/if.h>
#endif

#ifdef BSD
#include <ifaddrs.h>
#endif

/* should really come from ocaml/byterun/signals.h, but Xavier doesn't install that
   in $(PREFIX)/lib/ocaml/caml when he installs everything else.  Instead, we
   inline the (two) definitions we use here. */
CAMLextern void enter_blocking_section(void);
CAMLextern void leave_blocking_section(void);

#ifdef WIN32
#define MSG_WAITALL -1
#define MSG_DONTWAIT -1
CAMLprim value nssock_select(value rcv, value snd, value expn, value options);
#endif
#ifndef SO_BSDCOMPAT
#define SO_BSDCOMPAT -1
#endif
#ifndef SO_ACCEPTCONN
#ifdef SO_ACCEPTCON
#define SO_ACCEPTCONN SO_ACCEPTCON
#endif
#endif

//char buf[NS_MAX_BUFFER_SIZE];
int boptname[] = {SO_BSDCOMPAT, SO_REUSEADDR, SO_KEEPALIVE,
		  SO_OOBINLINE, SO_DONTROUTE, SO_BROADCAST};
int noptname[] = {SO_SNDBUF, SO_RCVBUF, SO_SNDLOWAT, SO_RCVLOWAT};
int toptname[] = {SO_LINGER, SO_SNDTIMEO, SO_RCVTIMEO};
//int filebflag[] = {O_NONBLOCK, O_ASYNC};
int msgbflag[] = {MSG_PEEK, MSG_OOB, MSG_WAITALL, MSG_DONTWAIT};


CAMLprim value nssock_value_list_of_array(value * vals) {
  CAMLparam0();
  CAMLlocal1(ret);

  if(vals == NULL) {
    CAMLreturn(Val_int(0));
  }
  else {
    ret = alloc(2,0);
    Begin_roots1(ret);
    Field(ret, 0) = *vals;
    Field(ret, 1) = nssock_value_list_of_array(vals++);
    End_roots();
    CAMLreturn(ret);
  }
}


CAMLprim value nssock_gettid()
{
  CAMLparam0();
  CAMLreturn(Val_int(ns_getpid()));
}


CAMLprim value nssock_int_of_tid(value tid)
{
  CAMLparam1(tid);
  CAMLreturn(tid);
}


CAMLprim value nssock_tid_of_int(value tid)
{
  CAMLparam1(tid);
  CAMLreturn(tid);
}


CAMLprim value nssock_accept(value sock)
{
  CAMLparam1(sock);
  CAMLlocal4(res,ip,port,ipport);

  int retcode;
  struct sockaddr addr;
  socklen_t addrlen = sizeof(struct sockaddr);

  enter_blocking_section();
  retcode = ns_accept(Int_val(sock), &addr, &addrlen);
  leave_blocking_section();

  if(retcode == SOCKET_ERROR)
    ns_uerror("accept", Nothing);

  Begin_roots4(ip, port, res, ipport);
  ip = alloc_string(sizeof(uint32));
  *((uint32*)ip) = ((struct sockaddr_in*)&addr)->sin_addr.s_addr;
  port = alloc_small(1, 0);
  Field(port, 0) = Val_int(ntohs(((struct sockaddr_in*)&addr)->sin_port));

  ipport = alloc_small(2, 0);
  Field(ipport, 0) = ip;
  Field(ipport, 1) = port;

  res = alloc_small(2, 0);
  Field(res, 0) = Val_int(retcode);
  Field(res, 1) = ipport;
  End_roots();

  CAMLreturn(res);
}


CAMLprim value nssock_bind(value fd, value ip, value port)
{
  CAMLparam3(fd,ip,port);

  int ret;
  struct sockaddr_in addr;
  socklen_t addrlen = sizeof(struct sockaddr_in);

#ifndef WIN32
  bzero(&addr, sizeof(addr));
#else
  ZeroMemory(&addr, sizeof(addr));
#endif

  addr.sin_family = AF_INET;
  if(Int_val(ip) == 0)
    addr.sin_addr.s_addr = inet_addr("0.0.0.0");
  else
    addr.sin_addr.s_addr = *((uint32*)Field(ip, 0));

  if(Int_val(port) == 0)
    addr.sin_port = 0;
  else
    addr.sin_port = htons(Int_val(Field(Field(port, 0), 0)));

  ret = ns_bind(Int_val(fd), (struct sockaddr*)&addr, addrlen);
  if(ret == SOCKET_ERROR)
    ns_uerror("bind", Nothing);

  CAMLreturn(Val_unit);
}


CAMLprim value nssock_close(value fd)
{
  CAMLparam1(fd);
  int ret;

  enter_blocking_section();
  ret = ns_close(Int_val(fd));
  leave_blocking_section();

  if(ret == SOCKET_ERROR)
    ns_uerror("close", Nothing);

  CAMLreturn(Val_unit);
}


CAMLprim value nssock_connect(value socket, value ip, value port)
{
  CAMLparam3(socket,ip,port);

  int retcode;
  struct sockaddr_in addr;
  socklen_t addrlen = sizeof(struct sockaddr_in);

#ifndef WIN32
  bzero(&addr, sizeof(addr));
#else
  ZeroMemory(&addr, sizeof(addr));
#endif

  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = *((uint32*)ip);

  if(Int_val(port) == 0)
    addr.sin_port = 0;
  else
    addr.sin_port = htons(Int_val(Field(Field(port,0),0)));

  enter_blocking_section();
  retcode = ns_connect(Int_val(socket), (struct sockaddr*)&addr, addrlen);
  leave_blocking_section();

  if(retcode == SOCKET_ERROR)
    ns_uerror("connect", Nothing);

  CAMLreturn(Val_unit);
}


CAMLprim value nssock_disconnect(value fd)
{
  CAMLparam1(fd);

  int retcode;
  struct sockaddr_in addr;
  socklen_t addrlen = sizeof(struct sockaddr_in);

#ifndef WIN32
  bzero(&addr, sizeof(addr));
#else
  ZeroMemory(&addr, sizeof(addr));
#endif
  addr.sin_family = AF_UNSPEC;

  enter_blocking_section();
  retcode = ns_connect(Int_val(fd), (struct sockaddr *)&addr, addrlen);
  leave_blocking_section();

  if(retcode == SOCKET_ERROR)
    ns_uerror("disconnect", Nothing);

  CAMLreturn(Val_unit);
}


#ifndef WIN32
CAMLprim value nssock_dup(value fd)
{
  CAMLparam1(fd);
  int ret;

  ret = ns_dup(Int_val(fd));
  if(ret == SOCKET_ERROR)
    ns_uerror("dup", Nothing);

  CAMLreturn(Val_int(ret));
}
#else
CAMLprim value nssock_dup(value fd)
{
  CAMLparam1(fd);
  ns_uerror("dup not supported on windows", Nothing);
  CAMLreturn(fd);
}
#endif


#ifndef WIN32
CAMLprim value nssock_dup2(value fd1, value fd2)
{
  CAMLparam2(fd1,fd2);
  if(ns_dup2(Int_val(fd1), Int_val(fd2)) == SOCKET_ERROR)
    ns_uerror("dup2", Nothing);
  CAMLreturn(fd2);
}
#else
CAMLprim value nssock_dup2(value fd1, value fd2)
{
  CAMLparam2(fd1,fd2);
  ns_uerror("dup2 not supported on Windows", Nothing);
  CAMLreturn(fd1);
}
#endif


CAMLprim value nssock_fdofint(value num)
{
  CAMLparam1(num);
  CAMLreturn(num);
}


CAMLprim value nssock_intoffd(value fd)
{
  CAMLparam1(fd);
  CAMLreturn(fd);
}

CAMLprim value nssock_intofnetmask(value nm)
{
  CAMLparam1(nm);
  CAMLreturn(nm);
}

CAMLprim value nssock_netmaskofint(value nm)
{
  CAMLparam1(nm);
  CAMLreturn(nm);
}


#ifdef WIN32
CAMLprim value nssock_getfileflags(value fd)
{
  CAMLparam1(fd);
  CAMLlocal1(flaglist);
  int retcode;
  u_long val;

  retcode = ns_ioctlsocket(Int_val(fd), FIONBIO, &val);
  if(retcode == SOCKET_ERROR)
    ns_uerror("getfileflags", Nothing);

  Begin_roots1(flaglist);
  if(retcode != 0) {
    flaglist = alloc_small(2, 0);
    Field(flaglist, 0) = Val_int(0); //constructor #0 O_NONBLOCK
    Field(flaglist, 1) = Val_int(0);
  } else {
    flaglist = Val_int(0);
  }

  End_roots();
  CAMLreturn(flaglist);
}
#else
CAMLprim value nssock_getfileflags(value fd)
{
  CAMLparam1(fd);
  CAMLlocal2(flaglist,x1);
  int retcode;

  flaglist = Val_unit;
  x1 = Val_unit;

  retcode = ns_fcntl(Int_val(fd), F_GETFL);
  if(retcode == SOCKET_ERROR)
    ns_uerror("getfilebfl", Nothing);

  Begin_roots2(flaglist, x1);

  if(retcode & O_NONBLOCK) {
    x1 = alloc_small(2, 0);
    Field(x1, 0) = Val_int(0); //constructor #0 O_NONBLOCK
    Field(x1, 1) = Val_int(0);
  } else {
    x1 = Val_int(0);
  }

  if(retcode & O_ASYNC) {
    flaglist = alloc_small(2, 0);
    Field(flaglist, 0) = Val_int(1); //constructor #1 O_ASYNC
    Field(flaglist, 1) = x1;
  } else {
    flaglist = x1;
  }

  End_roots();

  CAMLreturn(flaglist);
}
#endif


#ifndef WIN32
CAMLprim value nssock_getifaddrs() {
  CAMLparam0();

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

#ifdef BSD
  CAMLlocal5(netmask_val,ifid_val,iface_val,ip_val,result);
  CAMLlocal4(temp,tempip,tempother,otherips_val);
  int retval, pid, num_of_ifids, num_of_aliases, index, index_alias;
  struct ifaddrs  *ifad, *ifads;
  struct ifid_info * ifids_head, * ifids_free, *ifids_next_prn, **ifids;
  struct otherips_ll *otherips, *otherips_next;
  char ifid[SMSTR], ip[SMSTR], others[LARGESTR], netmask[SMSTR],output[10*LARGESTR], lastname[SMSTR];
  ifids_head = NULL;
  ifids = &ifids_head;
  ifid[0] = ip[0] = others[0] = netmask[0] = output[0] = lastname[0] = '\0';

  Begin_roots5(iface_val, ifid_val, ip_val, netmask_val, otherips_val);
  Begin_roots4(temp, result, tempip, tempother);

  retval = ns_getifaddrs(&ifad);

  if(retval == SOCKET_ERROR) {
    ns_uerror("getifaddrs", Nothing);
    CAMLreturn(Val_int(0));
  }

  ifads = ifad;

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
	strncpy((*ifids)->name, (ifads->ifa_name), sizeof(ifads->ifa_name));
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
  freeifaddrs(ifad);

#else // Linux
  CAMLlocal5(iface_val,ifid_val,ip_val,netmask_val,result);
  CAMLlocal4(temp,otherips_val,tempip,tempother);
  int sockfd, len, retval, lastlen, num_of_ifids, num_of_aliases, index, index_alias;
  char * buf, *ptr, lastname[SMSTR], *cptr, output[10*LARGESTR], ifid[SMSTR], ip[SMSTR], others[LARGESTR], netmask[SMSTR];
  struct ifconf ifc;
  struct ifid_info *ifids_head, *ifids_next_prn, *ifids_free, **ifids_next;
  struct ifreq *ifr, ifrcopy;
  struct sockaddr_in *sinptr;
  struct otherips_ll * otherips, *otherips_next;
  lastname[0] = output[0] = ifid[0] = ip[0] = others[0] = netmask[0] = '\0';

  Begin_roots5(iface_val, ifid_val, ip_val, netmask_val, tempother);
  Begin_roots4(temp, result, otherips_val, tempip);

  //we need to have a socket first
  sockfd = socket(AF_INET, SOCK_STREAM, 0);

  //allocate buffer space and make call
  lastlen = 0;
  len = 100 * sizeof(struct ifreq);
  buf = malloc(len);
  ifc.ifc_len = len;
  ifc.ifc_buf = buf;
  if((retval = ns_ioctl(sockfd, SIOCGIFCONF, &ifc)) < 0) {
    if(errno != EINVAL || lastlen != 0) {
      ns_uerror("getifaddrs", Nothing);
      CAMLreturn(Val_int(0));
    }
  }

  ifids_head = NULL;
  ifids_next = &ifids_head;

  for(ptr = buf; ptr < buf + ifc.ifc_len;) {
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
      ns_ioctl(sockfd, SIOCGIFNETMASK, &ifrcopy);
      memcpy(&(*ifids_next)->netmask, (struct sockaddr_in *)&ifrcopy.ifr_addr, sizeof(struct sockaddr_in));
     }
  }
  (*ifids_next)->next = NULL;

#endif //BSD

  //now do the return
  ifids_next_prn = ifids_head;
  result = Val_int(0);
  while(ifids_next_prn != NULL) {
    temp = result;
    result = alloc_small(2, 0);
    Field(result, 1) = temp;
    // now do the next element in the list
    iface_val = alloc_tuple(4);
    Field(iface_val, 0) = copy_string(ifids_next_prn->name);
    ip_val = alloc_string(sizeof(uint32));
    *((uint32*)ip_val) = (ifids_next_prn->primaryip.sin_addr.s_addr);
    Field(iface_val, 1) = ip_val;
    //now do the other ips
    otherips = ifids_next_prn->otherips;
    otherips_val = Val_int(0);
    while(otherips != NULL) {
      tempother = otherips;
      otherips_val = alloc_small(2,0);
      Field(otherips_val, 1) = tempother;
      tempip = alloc_string(sizeof(uint32));
      *((uint32*)tempip) = (otherips->addr).sin_addr.s_addr;
      Field(otherips_val, 0) = tempip;
      otherips = otherips->next;
    }
    Field(iface_val, 2) = otherips_val;
    netmask_val = alloc_string(sizeof(uint32));
    *((uint32*)netmask_val) = (ifids_next_prn->netmask.sin_addr.s_addr);
    Field(iface_val, 3) = netmask_val;
    Field(result, 0) = iface_val;
    ifids_next_prn = ifids_next_prn->next;
  }

  End_roots();
  End_roots();
  CAMLreturn(result);
}

#else // !WIN32

CAMLprim value nssock_getifaddrs()
{
  CAMLparam0();
  CAMLreturn(Val_int(0));
}
#endif // !WIN32


CAMLprim value nssock_getpeername(value fd)
{
  CAMLparam1(fd);
  CAMLlocal3(ip,port,res);
  int retval;
  struct sockaddr_in addr;
  socklen_t addrlen = sizeof(struct sockaddr_in);

  ip = Val_unit;
  port = Val_unit;
  res = Val_unit;

  retval = ns_getpeername(Int_val(fd), (struct sockaddr*)&addr, &addrlen);
  if(retval == SOCKET_ERROR)
    ns_uerror("getpeername", Nothing);

  Begin_roots3(ip, port, res);
  if(addr.sin_addr.s_addr != 0) {
    ip = alloc_string(sizeof(uint32));
    *((uint32*)ip) = addr.sin_addr.s_addr;
  }

  port = alloc_small(1,0);
  if(addr.sin_port != 0)
    Field(port,0) = Val_int(ntohs(addr.sin_port));
  else
    Field(port,0) = Val_int(0);

  res = alloc_small(2, 0);
  Field(res, 0) = ip;
  Field(res, 1) = port;
  End_roots();

  CAMLreturn(res);
}


CAMLprim value nssock_getsockerr(value fd)
{
  CAMLparam1(fd);
  int retval;
  int optval;
  socklen_t optlen = sizeof(int);

  retval = ns_getsockopt(Int_val(fd), SOL_SOCKET, SO_ERROR,
			 &optval, &optlen);

  if(retval == SOCKET_ERROR)
    ns_uerror("getsockerr", Nothing);

  if(NS_ERROR_CODE != 0)
    ns_uerror("error", Nothing);

  CAMLreturn(Val_unit);
}


CAMLprim value nssock_getsocklistening(value fd)
{
  CAMLparam1(fd);
  int retval;
  int optval;
  socklen_t optlen = sizeof(int);

  retval = ns_getsockopt(Int_val(fd), SOL_SOCKET,
			 SO_ACCEPTCONN, &optval, &optlen);
  if(retval == SOCKET_ERROR)
    ns_uerror("getsocklistening", Nothing);

  CAMLreturn(optval != 0 ? Val_int(1) : Val_int(0));
}


CAMLprim value nssock_getsockname(value fd)
{
  CAMLparam1(fd);
  CAMLlocal5(ip,port,res,res2,res3);
  CAMLlocal1(res4);
  int retval;
  struct sockaddr_in addr;
  socklen_t addrlen = sizeof(struct sockaddr_in);

  ip = port = res = res3 = Val_unit;
  res2 = res4 = Val_int(0);

  retval = ns_getsockname(Int_val(fd), (struct sockaddr*)&addr, &addrlen);
  if(retval == SOCKET_ERROR)
    ns_uerror("getsockname", Nothing);

  Begin_roots5(ip, port, res, res2, res3);

  if(addr.sin_addr.s_addr != 0) {
    ip = alloc_string(sizeof(uint32));
    *((uint32*)ip) = addr.sin_addr.s_addr;
    res2 = alloc_small(1, 0);
    Field(res2, 0) = ip;
  }
  if(addr.sin_port != 0) {
    port = Val_int(ntohs(addr.sin_port));
    res3 = alloc_small(1, 0);
    Field(res3, 0) = port;
    res4 = alloc_small(1, 0);
    Field(res4, 0) = res3;
  }

  res = alloc_small(2, 0);
  Field(res, 0) = res2;
  Field(res, 1) = res4;
  End_roots();

  CAMLreturn(res);
}


CAMLprim value nssock_getsockbopt(value fd, value sockbflag)
{
  CAMLparam2(fd,sockbflag);

  int retval, optval;
  socklen_t optvallen = sizeof(int);

  retval = ns_getsockopt(Int_val(fd), SOL_SOCKET, boptname[Int_val(sockbflag)],
			 &optval, &optvallen);
  if(retval == SOCKET_ERROR)
    ns_uerror("getsockbopt", Nothing);

  CAMLreturn(retval != 0 ? Val_int(1) : Val_int(0));
}


CAMLprim value nssock_getsocknopt(value fd, value socknflag)
{
  CAMLparam2(fd,socknflag);

  int retval, optval;
  socklen_t optvallen = sizeof(int);

  retval = ns_getsockopt(Int_val(fd), SOL_SOCKET, noptname[Int_val(socknflag)],
			 &optval, &optvallen);
  if(retval == SOCKET_ERROR)
    ns_uerror("getsocknopt", Nothing);

  CAMLreturn(Val_int(optval));
}


CAMLprim value nssock_getsocktopt(value fd, value socktflag)
{
  CAMLparam2(fd,socktflag);
  CAMLlocal4(res,res2,t1,t2);
  int retval;
  socklen_t optvallen;
  struct timeval timeoptval;
  struct linger lingeroptval;

  res = res2 = t1 = t2 = Val_unit;

  if(Int_val(socktflag) == 0) {  //SO_LINGER
    optvallen = sizeof(struct linger);
    retval = ns_getsockopt(Int_val(fd), SOL_SOCKET,
			   toptname[Int_val(socktflag)],
			   &lingeroptval, &optvallen);
  } else {
    optvallen = sizeof(struct timeval);
    retval = ns_getsockopt(Int_val(fd), SOL_SOCKET,
			   toptname[Int_val(socktflag)],
			   &timeoptval, &optvallen);
  }

  if(retval == SOCKET_ERROR)
    ns_uerror("getsocktopt", Nothing);

  if(Int_val(socktflag) == 0) { //SO_LINGER
    if(lingeroptval.l_onoff == 0) {
      res = Val_int(0);
      CAMLreturn(res);
    }
    t1 = Val_int(lingeroptval.l_linger);
    t2 = Val_int(0);
  } else {
    t1 = Val_int(timeoptval.tv_sec);
    t2 = Val_int(timeoptval.tv_usec);
  }

  Begin_roots4(t1, t2, res, res2);
  res2 = alloc_small(2, 0);
  Field(res2, 0) = t1;
  Field(res2, 1) = t2;
  res = alloc_small(1, 0);
  Field(res, 0) = res;
  End_roots();

  CAMLreturn(res);
}


CAMLprim value nssock_ipofstring(value string)
{
  CAMLparam1(string);
  CAMLlocal1(ip);

  Begin_roots1(ip);
  ip = alloc_string(sizeof(uint32));
  *((uint32*)ip) = inet_addr(String_val(string));

  if(*(uint32*)ip == 0)
    ns_uerror("ip_of_string", Nothing);
  End_roots();

  CAMLreturn(ip);
}


CAMLprim value nssock_stringofip(value ip)
{
  CAMLparam1(ip);
  CAMLreturn(copy_string(inet_ntoa(*(struct in_addr*)ip)));
}


CAMLprim value nssock_ifidofstring(value string)
{
  CAMLparam1(string);
  CAMLreturn(string);
}


CAMLprim value nssock_stringofifid(value ifid)
{
  CAMLparam1(ifid);
  CAMLreturn(ifid);
}


CAMLprim value nssock_portofint(value port)
{
  CAMLparam1(port);
  CAMLlocal1(p);

  Begin_roots1(p);
  p = alloc_small(1,0);
  Field(p, 0) = port;
  End_roots();

  CAMLreturn(p);
}


CAMLprim value nssock_intofport(value port)
{
  CAMLparam1(port);
  CAMLreturn(Field(port, 0));
}


CAMLprim value nssock_listen(value fd, value backlog)
{
  CAMLparam2(fd,backlog);
  int retval;

  retval = ns_listen(Int_val(fd), Int_val(backlog));
  if(retval == SOCKET_ERROR)
    ns_uerror("listen", Nothing);

  CAMLreturn(Val_unit);
}



CAMLprim value nssock_select(value rcv, value snd, value expn,
			     value options)
{
  CAMLparam4(rcv,snd,expn,options);
  CAMLlocal5(tempval,templist,resrcv,ressnd,resexpn);
  CAMLlocal3(r,result,result2);

  int retval, maxsock = 0, i;
  fd_set rcvset, sndset, expnset;
  struct timeval timeout, *to;

  FD_ZERO(&rcvset);
  FD_ZERO(&sndset);
  FD_ZERO(&expnset);


  templist = rcv;
  for( ; ; ) {
    if(Int_val(templist) != 0) {
      tempval = Field(templist, 0);
      FD_SET(Int_val(tempval), &rcvset);
      if(Int_val(tempval) > maxsock)
	 maxsock = Int_val(tempval);
      templist = Field(templist, 1);
    } else {
      break;
    }
  }

  templist = snd;
  for( ; ; ) {
    if(Int_val(templist) != 0) {
      tempval = Field(templist, 0);
      FD_SET(Int_val(tempval), &sndset);
      if(Int_val(tempval) > maxsock)
	 maxsock = Int_val(tempval);
      templist = Field(templist, 1);
    } else {
      break;
    }
  }

  templist = expn;
  for( ; ; ) {
    if(Int_val(templist) != 0) {
      tempval = Field(templist, 0);
      if(Int_val(tempval) > maxsock)
	 maxsock = Int_val(tempval);
      FD_SET(Int_val(tempval), &expnset);
      templist = Field(templist, 1);
    } else {
      break;
    }
  }

  if(Int_val(options) == 0) {
    to = NULL;
  } else {
    timeout.tv_sec = Int_val(Field(Field(options, 0), 0));
    timeout.tv_usec = Int_val(Field(Field(options, 0), 1)) / 1000;  //as pselect uses nanoseconds
    to = &timeout;
  }

  enter_blocking_section();
  retval = ns_select(maxsock+1, &rcvset, &sndset, &expnset,
		     to);
  leave_blocking_section();
  if(retval == SOCKET_ERROR)
    ns_uerror("select", Nothing);

  Begin_roots2(resrcv, r);
  resrcv = Val_int(0);
  for(i=0; i<maxsock+1; i++) {
    if(FD_ISSET(i, &rcvset)) {
      r = alloc(2, 0);
      Field(r, 0) = Val_int(i);
      Field(r, 1) = resrcv;
      resrcv = r;
    }
  }
  End_roots();

  Begin_roots2(ressnd, r);
  ressnd = Val_int(0);
  for(i=0; i<maxsock+1; i++) {
    if(FD_ISSET(i, &sndset)) {
      r = alloc(2, 0);
      Field(r, 0) = Val_int(i);
      Field(r, 1) = ressnd;
      ressnd = r;
    }
  }
  End_roots();

  Begin_roots2(resexpn, r);
  resexpn = Val_int(0);
  for(i=0; i<maxsock+1; i++) {
    if(FD_ISSET(i, &expnset)) {
      r = alloc(2, 0);
      Field(r, 0) = Val_int(i);
      Field(r, 1) = resexpn;
      resexpn = r;
    }
  }
  End_roots();

  Begin_roots2(result, result2);
  result2 = alloc(2, 0);
  Field(result2, 0) = ressnd;
  Field(result2, 1) = resexpn;
  result = alloc(2, 0);
  Field(result, 0) = resrcv;
  Field(result, 1) = result2;
  End_roots();

  CAMLreturn(result);
}


#ifndef LINUX
CAMLprim value nssock_pselect(value rcv, value snd, value expn,
			     value options, value signals)
{
  CAMLparam5(rcv,snd,expn,options,signals);
  CAMLreturn(nssock_select(rcv, snd, expn, options));
}
#else
CAMLprim value nssock_pselect(value rcv, value snd, value expn,
			     value options, value signals)
{
  CAMLparam5(rcv,snd,expn,options,signals);
  CAMLlocal5(tempval,templist,resrcv,ressnd,resexpn);
  CAMLlocal3(r,result,result2);

  int retval, maxsock = 0, i;
  sigset_t signalset, *sset;
  fd_set rcvset, sndset, expnset;
  struct timespec timeout, *to;

  FD_ZERO(&rcvset);
  FD_ZERO(&sndset);
  FD_ZERO(&expnset);

  templist = rcv;
  for( ; ; ) {
    if(Int_val(templist) != 0) {
      tempval = Field(templist, 0);
      FD_SET(Int_val(tempval), &rcvset);
      if(Int_val(tempval) > maxsock)
	 maxsock = Int_val(tempval);
      templist = Field(templist, 1);
    } else {
      break;
    }
  }

  templist = snd;
  for( ; ; ) {
    if(Int_val(templist) != 0) {
      tempval = Field(templist, 0);
      FD_SET(Int_val(tempval), &sndset);
      if(Int_val(tempval) > maxsock)
	 maxsock = Int_val(tempval);
      templist = Field(templist, 1);
    } else {
      break;
    }
  }

  templist = expn;
  for( ; ; ) {
    if(Int_val(templist) != 0) {
      tempval = Field(templist, 0);
      if(Int_val(tempval) > maxsock)
	 maxsock = Int_val(tempval);
      FD_SET(Int_val(tempval), &expnset);
      templist = Field(templist, 1);
    } else {
      break;
    }
  }

  if(Int_val(options) == 0) {
    timeout.tv_sec = 0;
    timeout.tv_nsec = 0;
  } else {
    timeout.tv_sec = Int_val(Field(Field(options, 0),0));
    timeout.tv_nsec = Int_val(Field(Field(options, 0),1));
  }

  sigemptyset(&signalset);
  if(Int_val(signals) == 0) {
    sset = NULL;
  } else {
    if(Int_val(Field(signal, 0)) == 0) {
      sset = &signalset;
    } else {
      templist = Field(signal, 0);
      for( ; ; ) {
	if(Int_val(templist) != 0) {
	  switch(Field(templist, 0)) {
	    case 0:
	      sigaddset(&signalset, SIGABRT);
	      break;
  	    case 1:
	      sigaddset(&signalset, SIGALRM);
	      break;
	    case 2:
	      sigaddset(&signalset, SIGBUS);
	      break;
  	    case 3:
	      sigaddset(&signalset, SIGCHLD);
	      break;
	    case 4:
	      sigaddset(&signalset, SIGCONT);
	      break;
	    case 5:
	      sigaddset(&signalset, SIGFPE);
	      break;
	    case 6:
	      sigaddset(&signalset, SIGHUP);
	      break;
	    case 7:
	      sigaddset(&signalset, SIGILL);
	      break;
	    case 8:
	      sigaddset(&signalset, SIGINT);
	      break;
	    case 9:
	      sigaddset(&signalset, SIGKILL);
	      break;
	    case 10:
	      sigaddset(&signalset, SIGPIPE);
	      break;
	    case 11:
	      sigaddset(&signalset, SIGQUIT);
	      break;
	    case 12:
	      sigaddset(&signalset, SIGSEGV);
	      break;
	    case 13:
	      sigaddset(&signalset, SIGSTOP);
	      break;
	    case 14:
	      sigaddset(&signalset, SIGTERM);
	      break;
	    case 15:
	      sigaddset(&signalset, SIGTSTP);
	      break;
	    case 16:
	      sigaddset(&signalset, SIGTTIN);
	      break;
	    case 17:
	      sigaddset(&signalset, SIGTTOU);
	      break;
	    case 18:
	      sigaddset(&signalset, SIGUSR1);
	      break;
 	    case 19:
	      sigaddset(&signalset, SIGUSR2);
	      break;
	    case 20:
	      sigaddset(&signalset, SIGPOLL);
	      break;
	    case 21:
	      sigaddset(&signalset, SIGPROF);
	      break;
	    case 22:
	      sigaddset(&signalset, SIGSYS);
	      break;
	    case 23:
	      sigaddset(&signalset, SIGTRAP);
	      break;
	    case 24:
	      sigaddset(&signalset, SIGURG);
	      break;
	    case 25:
	      sigaddset(&signalset, SIGVTALRM);
	      break;
	    case 26:
	      sigaddset(&signalset, SIGXCPU);
	      break;
	    case 27:
	      sigaddset(&signalset, SIGXFSZ);
	      break;
	    default:
	      ns_uerror("pselect: unknown signal", Nothing);
	      break;
	  }

	  templist = Field(templist, 1);
	} else
	  break;
      }
      sset = &signalset;
    }
  }

  enter_blocking_section();
  retval = ns_pselect(maxsock+1, &rcvset, &sndset, &expnset,
		      &timeout, sset);
  leave_blocking_section();

  if(retval == SOCKET_ERROR)
    ns_uerror("select", Nothing);

  Begin_roots2(resrcv, r);
  resrcv = Val_int(0);
  for(i=0; i<maxsock+1; i++) {
    if(FD_ISSET(i, &rcvset)) {
      r = alloc(2, 0);
      Field(r, 0) = Val_int(i);
      Field(r, 1) = resrcv;
      resrcv = r;
    }
  }
  End_roots();

  Begin_roots2(ressnd, r);
  ressnd = Val_int(0);
  for(i=0; i<maxsock+1; i++) {
    if(FD_ISSET(i, &sndset)) {
      r = alloc(2, 0);
      Field(r, 0) = Val_int(i);
      Field(r, 1) = ressnd;
      ressnd = r;
    }
  }
  End_roots();

  Begin_roots2(resexpn, r);
  resexpn = Val_int(0);
  for(i=0; i<maxsock+1; i++) {
    if(FD_ISSET(i, &expnset)) {
      r = alloc(2, 0);
      Field(r, 0) = Val_int(i);
      Field(r, 1) = resexpn;
      resexpn = r;
    }
  }
  End_roots();

  Begin_roots2(result, result2);
  result2 = alloc(2, 0);
  Field(result2, 0) = ressnd;
  Field(result2, 1) = resexpn;
  result = alloc(2, 0);
  Field(result, 0) = resrcv;
  Field(result, 1) = result2;
  End_roots();

  CAMLreturn(result);
}
#endif


CAMLprim value nssock_recv(value fd, value len, value flags)
{
  CAMLparam3(fd,len,flags);
  CAMLlocal5(tempflag,tempflag2,result,tempres,i);
  CAMLlocal5(p,pair,ipppair,ip,port);
  char *buf;

#ifndef WIN32
  int optval = 0;
#else
  char optval = 0;
#endif
  int retval;
  int realflags = 0;
  struct sockaddr_in from;
  socklen_t socklen = sizeof(struct sockaddr_in);
  socklen_t optvallen = sizeof(int);

  result = tempres = i = p = pair = ip = Val_unit;

#ifndef WIN32
  bzero(&from, sizeof(from));
#else
  ZeroMemory(&from, sizeof(from));
#endif

  tempflag = flags;
  for( ; ; ) {
    if(Int_val(tempflag) != 0) {
      tempflag2 = Field(tempflag, 0);
      realflags |= msgbflag[Int_val(tempflag2)];
      tempflag = Field(tempflag, 1);
    } else
      break;
  }

  retval = getsockopt(Int_val(fd), SOL_SOCKET, SO_TYPE, &optval, &optvallen);

  buf = malloc(Int_val(len));
  assert(buf);

  enter_blocking_section();
  if(retval != SOCKET_ERROR && optval == SOCK_DGRAM)
    retval = ns_recvfrom(Int_val(fd), buf, Int_val(len), realflags, (struct sockaddr *)&from, &socklen);
  else
    retval = ns_recv(Int_val(fd), buf, Int_val(len), realflags);
  leave_blocking_section();

  if(retval == SOCKET_ERROR) {
    ns_uerror("recv", Nothing);
    CAMLreturn(result);
  }

  Begin_roots5(result, tempres, pair, p, i);
  Begin_roots3(ip,port,ipppair);
  result = alloc_tuple(2);
  Field(result, 0) = copy_string_len(buf, retval);
  free(buf);

  if(&from != NULL) {
    tempres = alloc_small(1,0);
    ipppair = alloc_tuple(2);
    pair = alloc_tuple(2);
    if(from.sin_port != 0) {
      p = alloc_small(1,0);
      port = alloc_small(1,0);
      Field(p,0) = Val_int(ntohs(from.sin_port));
      Field(port,0) = p;
      Field(ipppair,1) = port;
    }
    else {
      Field(ipppair, 1) = Val_int(0);
    }
    if(from.sin_addr.s_addr != 0) {
      ip = alloc_small(1,0);
      i = alloc_string(sizeof(uint32));
      *((uint32*)i) = (from.sin_addr.s_addr);
      Field(ip, 0) = i;
      Field(ipppair,0) = ip;
    }
    else {
      Field(ipppair, 0) = Val_int(0);
    }
    Field(pair,0) = ipppair;
    Field(pair,1) = Val_int(1);
    Field(tempres, 0) = pair;
  }
  else {
    tempres = alloc_small(1,0);
    Field(tempres, 0) = Val_int(0);
  }

  Field(result,1) = tempres;
  End_roots();
  End_roots();

  CAMLreturn(result);
}

CAMLprim value nssock_send(value fd, value addr, value string, value flags)
{
  CAMLparam4(fd,addr,string,flags);
  CAMLlocal3(tempflag,tempflag2,ipport);

  int retval;
  int realflags = 0;
  char tempstr[] = "\0";
  int isAddr = 0;
  struct sockaddr_in sockAddr;
  socklen_t addrlen = sizeof(struct sockaddr_in);

  /*see if addr is filled in */
  if(Is_long(addr))
    isAddr = 0;
  else {
#ifndef WIN32
  bzero(&sockAddr, sizeof(struct sockaddr_in));
#else
  ZeroMemory(&sockAddr, sizeof(struct sockaddr_in));
#endif
  ipport = Field(addr, 0);
  sockAddr.sin_family = AF_INET;
  sockAddr.sin_addr.s_addr = *((uint32*)Field(ipport, 0));
  sockAddr.sin_port = htons(Int_val(Field(Field(ipport, 1),0)));
  isAddr = 1;
  }

 //sort out flags
  tempflag = flags;
  for( ; ; ) {
    if(Int_val(tempflag) != 0) {
      tempflag2 = Field(tempflag, 0);
      realflags |= msgbflag[Int_val(tempflag2)];
      tempflag = Field(tempflag, 1);
    } else
      break;
  }

  enter_blocking_section();
  if(isAddr == 0) {
    retval = ns_send(Int_val(fd), String_val(string),
		     string_length(string), realflags);
  }
  else if (isAddr == 1){
    retval = ns_sendto(Int_val(fd), String_val(string),
		       string_length(string), realflags,
		       (struct sockaddr*)&sockAddr, addrlen);
  }
  leave_blocking_section();

  if(retval == SOCKET_ERROR)
    ns_uerror("send", Nothing);

  if(retval == 0)
    CAMLreturn(string);
  else if(retval < (int)string_length(string))
    CAMLreturn(copy_string_len(String_val(string) + retval,
			      string_length(string) - retval));

  CAMLreturn(copy_string(tempstr));
}


CAMLprim value nssock_setfileflags(value fd, value options)
{
  CAMLparam2(fd,options);
  CAMLlocal1(f1);

  int retval;
  long flags = 0;

  f1 = options;
  while(Int_val(f1) != 0) {
#ifndef WIN32
    if(Int_val(Field(f1, 0)) == 0)
      flags |= O_NONBLOCK;
    else if(Int_val(Field(f1, 0)) == 1)
      flags |= O_ASYNC;
#else
    if(Int_val(Field(f1, 0)) == 0)
      flags = 1;
#endif
    else
      ns_uerror("setfileflags() -- unknown flag specified", Nothing);
    f1 = Field(f1, 1);
  }


#ifndef WIN32
  retval = ns_fcntl(Int_val(fd), F_SETFL, flags);
  if(retval == SOCKET_ERROR)
    ns_uerror("setfileflags", Nothing);
#else
  retval = ns_ioctlsocket(Int_val(fd), FIONBIO, &flags);
  if(retval == SOCKET_ERROR)
    ns_uerror("setfileflags", Nothing);
#endif

  CAMLreturn(Val_unit);
}


CAMLprim value nssock_setsockbopt(value fd, value sockbflag, value bool)
{
  CAMLparam3(fd,sockbflag,bool);

  int retval, optval;
  socklen_t optvallen = sizeof(int);
  optval = Int_val(bool);

  retval = ns_setsockopt(Int_val(fd), SOL_SOCKET, boptname[Int_val(sockbflag)],
			 &optval, optvallen);
  if(retval == SOCKET_ERROR)
    ns_uerror("getsockbopt", Nothing);

  CAMLreturn(Val_unit);
}


CAMLprim value nssock_setsocknopt(value fd, value socknflag, value num)
{
  CAMLparam3(fd,socknflag,num);

  int retval, optval;
  socklen_t optvallen = sizeof(int);
  optval = Int_val(num);

  retval = ns_setsockopt(Int_val(fd), SOL_SOCKET, noptname[Int_val(socknflag)],
			 &optval, optvallen);
  if(retval == SOCKET_ERROR)
    ns_uerror("setsocknopt", Nothing);

  CAMLreturn(Val_unit);
}


CAMLprim value nssock_setsocktopt(value fd, value socktflag, value time)
{
  CAMLparam3(fd,socktflag,time);

  int retval;
  socklen_t optvallen;
  struct timeval timeoptval;
  struct linger lingeroptval;

  if(Int_val(socktflag) == 0) {  //SO_LINGER
    optvallen = sizeof(struct linger);
    if(Int_val(time) == 0)
      lingeroptval.l_onoff = 0;
    else {
      lingeroptval.l_onoff = 1;
      lingeroptval.l_linger = Int_val(Field(Field(time, 0), 0));
    }
    retval = ns_setsockopt(Int_val(fd), SOL_SOCKET,
			   toptname[Int_val(socktflag)],
			   &lingeroptval, optvallen);
  } else {
    if(Int_val(time) == 0) {
      optvallen = sizeof(struct timeval);
      timeoptval.tv_sec = 0;
      timeoptval.tv_usec = 0;
    } else {
      optvallen = sizeof(struct timeval);
      timeoptval.tv_sec = Int_val(Field(Field(time, 0), 0));
      timeoptval.tv_usec = Int_val(Field(Field(time, 0), 1));
    }
    retval = ns_setsockopt(Int_val(fd), SOL_SOCKET,
			   toptname[Int_val(socktflag)],
			   &timeoptval, optvallen);
  }

  if(retval == SOCKET_ERROR)
    ns_uerror("setsocktopt", Nothing);

  CAMLreturn(Val_unit);
}


CAMLprim value nssock_shutdown(value fd, value dissrecv, value disssend)
{
  CAMLparam3(fd,dissrecv,disssend);

  int retval;
  int how;

  if((Int_val(dissrecv) != 0) && (Int_val(disssend) != 0))
    how = 2;
  else if(Int_val(dissrecv) != 0)
    how = 0;
  else if(Int_val(disssend) != 0)
    how = 1;
  else
    return Val_unit;  /* KW: said we should return success in this case */

  retval = ns_shutdown(Int_val(fd), how);
  if(retval == SOCKET_ERROR)
    ns_uerror("shutdown", Nothing);

  CAMLreturn(Val_unit);
}

#ifndef WIN32
CAMLprim value nssock_sockatmark(value fd)
{
  CAMLparam1(fd);
  int retval;

  retval = ns_sockatmark(Int_val(fd));
  if(retval == SOCKET_ERROR)
    ns_uerror("sockatmark", Nothing);

  CAMLreturn(retval != 0 ? Val_int(1) : Val_int(0));
}
#else
CAMLprim value nssock_sockatmark(value fd)
{
  CAMLparam1(fd);

  int retval;
  u_long res;

  retval = ns_ioctlsocket(Int_val(fd), SIOCATMARK, &res);
  if(retval == SOCKET_ERROR)
    ns_uerror("sockatmark", Nothing);

  CAMLreturn(res != 0 ? Val_int(1) : Val_int(0));
}
#endif


CAMLprim value nssock_socket(value type)
{
  CAMLparam1(type);

  int retcode;
  if(Int_val(type) == 0) {
    retcode = ns_socket(AF_INET, SOCK_DGRAM, 0);
  }
  else {
    retcode = ns_socket(AF_INET, SOCK_STREAM, 0);
  }
  if(retcode == SOCKET_ERROR)
    ns_uerror("socket", Nothing);

  CAMLreturn(Val_int(retcode));
}
