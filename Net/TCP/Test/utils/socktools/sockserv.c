#include <ns_sockets.h>

void sockerr(int err, char *str)
{
  perror(str);
  abort();
}

int main(int argn, char **argv)
{
  int sock, sdconn, retval, i;
  struct sockaddr_in sockaddr;
  socklen_t addrlen;
  char str[8192];
  int dummy = 1, dummy2 = sizeof(int);

  if(argn < 3) {
    printf("\nSyntax: sockserv ipaddress port\n");
    printf("  e.g. sockserv 192.168.1.1 2000\n");
    exit(1);
  }

  sock = ns_socket(PF_INET, SOCK_STREAM, 0);
  if(sock == INVALID_SOCKET) {
    sockerr(ERRNO, "ns_socket(): failed to create socket");
    abort();
  }

  if(ns_setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, &dummy, sizeof(int)) ==
     SOCKET_ERROR) {
    sockerr(ERRNO, "ns_setsockopt(): call failed\n");
  }

#ifndef WIN32
  bzero(&sockaddr, sizeof(sockaddr));
#else
  ZeroMemory(&sockaddr, sizeof(sockaddr));
#endif
  sockaddr.sin_family = AF_INET;
  sockaddr.sin_addr.s_addr = inet_addr(argv[1]);
  sockaddr.sin_port = htons(atoi(argv[2]));
  addrlen = sizeof(struct sockaddr);

  if(ns_bind(sock, (struct sockaddr*)&sockaddr, addrlen) == SOCKET_ERROR) {
    sockerr(ERRNO, "ns_bind(): failed to bind to local port 10000");
    abort();
  }

  if(ns_listen(sock, 0) == SOCKET_ERROR) {
    sockerr(ERRNO, "ns_listen(): failed to listen");
    abort();
  }

  if((sdconn = ns_accept(sock, NULL, NULL)) == INVALID_SOCKET) {
    sockerr(ERRNO, "ns_accept(): returned an invalid socket");
    abort();
  }

  if(ns_getsockopt(sock, SOL_SOCKET, SO_REUSEADDR, &dummy, &dummy2) ==
     SOCKET_ERROR) {
    sockerr(ERRNO, "ns_getsockopt(): call failed\n");
  }


  while(1) {
    retval = ns_recv(sdconn, str, 8192, 0);
    if(retval == 0)
      break;

    for(i=0; i<strlen(str); i++)
      fputc(str[i], stdout);
  }

  if(ns_close(sock) == SOCKET_ERROR) {
    sockerr(ERRNO, "ns_close(): failed to close socket");
    abort();
  }

  return 0;
}

