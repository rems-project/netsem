#include <sys/types.h>
#include <sys/socket.h>
#include <stdio.h>

int socket(int domain, int type, int protocol)
{
  fprintf(stderr, "Dynamically linked socket call\n");
  return ns_socket(domain,type,protocol);
}
