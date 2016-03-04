#ifndef WIN32
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/errno.h>
#else
#include <winsock2.h>
#include <windows.h>
#endif

#include <stdio.h>
#include <stdlib.h>

void error(char *str)
{
  printf(str);
  exit(1);
}

int main(int argn, char **argv)
{
  int sd, sdconn;
  struct sockaddr_in laddr;
#ifdef WIN32
  char dummy = 1;
#else
  int dummy = 1;
#endif
  int retval;
  char str[16384];

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
#endif

  if(argn < 3) {
    printf("Too few arguments. Syntax: logger ipaddress port\n");
    exit(1);
  }

   sd = socket(PF_INET, SOCK_STREAM, 0);
  if(sd == -1)
    error("Unable to open a new socket.\n");

  if(setsockopt(sd, SOL_SOCKET, SO_REUSEADDR, &dummy, sizeof(dummy)) != 0)
    error("Unable to set socket options.\n");

#ifndef WIN32
  bzero(&laddr, sizeof(laddr));
#else
  ZeroMemory(&laddr, sizeof(laddr));
#endif

  laddr.sin_family = AF_INET;
  laddr.sin_addr.s_addr = inet_addr(argv[1]);
  laddr.sin_port = htons(atoi(argv[2]));

  if(bind(sd, (struct sockaddr *) &laddr, sizeof(laddr)) != 0)
    error("Unable to bind to socket.\n");

  if(listen(sd, 2) != 0)
    error("Unable to listen to socket.\n");

  if((sdconn = accept(sd, NULL, NULL)) == -1)
    error("Failed to accept a connecting socket");

  while(1) {
    retval = recv(sdconn, str, 8192, 0);
    if(retval == 0) {
      break;
    } else if(retval > 0) {
      str[retval] = '\0';
      printf("%s", str);
    }
  }

#ifndef WIN32
  close(sdconn);
  close(sd);
#else
  closesocket(sdconn);
  closesocket(sd);
#endif

  return 0;
}

