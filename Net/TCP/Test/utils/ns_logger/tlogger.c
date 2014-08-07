#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#define MAX_CONNS 64
#define MAX_FDS 128

void error(char *str)
{
  printf(str);
  exit(1);
}

int main(int argn, char **argv)
{
  int sd, sdconn, dummy=1, retval, i, n;
  struct sockaddr_in laddr;
  char str[16384];
  fd_set rfds, rfds_master;

  if(argn < 3) {
    printf("Too few arguments. Syntax: logger ipaddress port\n");
    exit(1);
  }

  sd = socket(PF_INET, SOCK_STREAM, 0);
  if(sd == -1)
    error("Unable to open a new socket.\n");

   if(setsockopt(sd, SOL_SOCKET, SO_REUSEADDR, &dummy, sizeof(dummy)) != 0)
     error("Unable to set socket options.\n");

   bzero(&laddr, sizeof(laddr));
   laddr.sin_family = AF_INET;
   laddr.sin_addr.s_addr = inet_addr(argv[1]);
   laddr.sin_port = htons(atoi(argv[2]));

   if(bind(sd, (struct sockaddr *) &laddr, sizeof(laddr)) != 0)
     error("Unable to bind to socket.\n");

   if(listen(sd, 5) != 0)
     error("Unable to listen to socket.\n");

   FD_ZERO(&rfds);
   FD_ZERO(&rfds_master);
   FD_SET(sd, &rfds);
   FD_SET(sd, &rfds_master);

  while(1) {
    FD_ZERO(&rfds);

    for(i=0; i<MAX_FDS; i++)
      if(FD_ISSET(i, &rfds_master)) {
	n = i;
	FD_SET(i, &rfds);
      }

    n++;
    if(select(n, &rfds, NULL, NULL, NULL) == -1)
      continue;

    for(i=0; i<MAX_FDS; i++)
      if(FD_ISSET(i, &rfds)) {
	if(i==sd)
	  if((sdconn = accept(sd, NULL, NULL)) == -1)
	    error("Failed to accept a connecting socket");
	  else
	    FD_SET(sdconn, &rfds_master);
	else {
	  retval = recv(i, str, 16383, 0);
	  if(retval == 0) {
	    FD_CLR(i, &rfds_master);
	  } else if(retval > 0) {
	    str[retval] = '\0';
	    printf("%s", str);
	  }
	}
      }
  }

  for(i=0; i<MAX_FDS; i++)
    if(FD_ISSET(i, &rfds_master)) close(i);

  return 0;
}

