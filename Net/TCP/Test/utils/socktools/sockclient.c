#include <ns_sockets.h>

void sockerr(int err, char *str)
{
  perror(str);
  abort();
}

int main(int argn, char **argv)
{
  int sock, retval, i;
  struct sockaddr_in sockaddr;
  socklen_t addrlen;
  char str[8192];
  int dummy = 1, dummy2 = sizeof(int);

  if(argn < 3) {
    printf("\nSyntax: sockclient ipaddress port\n");
    printf("  e.g. sockclient 192.168.1.1 2000\n");
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

  if(ns_connect(sock, (struct sockaddr*)&sockaddr, addrlen) == SOCKET_ERROR) {
    sockerr(ERRNO, "ns_connect: failed to connect socket");
  }

  while(1) {
    for(i=0; i<8190; i++) {
      str[i] = getchar();
      if(str[i] == '\n') {
	str[i+1] = '\0';
	break;
      }
    }
      //scanf("%s", str);
    retval = ns_send(sock, str, strlen(str), 0);
    if(retval == 0)
      break;
    printf(str);
    if(strlen(str) > 1)
      if((str[0] == 'q') && (str[1] == '\n'))
	break;
  }

  if(ns_close(sock) == SOCKET_ERROR) {
    sockerr(ERRNO, "ns_close(): failed to close socket");
    abort();
  }

  return 0;
}

