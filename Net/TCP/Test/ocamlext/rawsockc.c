#include <mlvalues.h>
#include "unixsupport.h"

#ifndef WIN32
#include <sys/types.h>
#include <sys/socket.h>
#include "socketaddr.h"
#define SOCKET_ERROR -1
#else
#include <winsock2.h>
#include <ws2tcpip.h>
#include <windows.h>
#endif

int socket_domain_table_raw[] = { PF_UNIX, AF_INET };

CAMLprim value raw_socket(value domain, value proto)
{
  int retcode;

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

  retcode = socket(socket_domain_table_raw[Int_val(domain)],
     SOCK_RAW, IPPROTO_IP);
#else
  retcode = socket(socket_domain_table_raw[Int_val(domain)],
     SOCK_RAW, 6);
#endif

  if(retcode == -1) uerror("raw_socket", Nothing);
  return Val_int(retcode);
}


CAMLprim value raw_sockopt_hdrincl(value socket)
{
  int optval = 1;

  if(setsockopt(Int_val(socket), IPPROTO_IP, IP_HDRINCL,
		(char*)&optval, sizeof(optval)) == -1)
    uerror("raw_sockoptset", Nothing);

  return Val_unit;
}

CAMLprim raw_sendto(value sock, value buff, value dest)
{
  int retval = 0, realflags = 0;
  struct sockaddr_in dest_dummy;

#ifdef WIN32
  ZeroMemory(&dest_dummy, sizeof(dest_dummy));
#else
  memset(&dest_dummy, 0, sizeof(dest_dummy));
#endif

  dest_dummy.sin_family = AF_INET;
  dest_dummy.sin_addr.s_addr = inet_addr(String_val(dest));
  dest_dummy.sin_port = htons(0);

  retval = sendto(Int_val(sock), String_val(buff),
		   string_length(buff), realflags, (struct sockaddr*)&dest_dummy, sizeof(dest_dummy) );
  if (retval == SOCKET_ERROR)
    uerror("ns_sendto_raw", Nothing);

  return Val_unit;
}

