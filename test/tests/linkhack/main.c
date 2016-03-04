#include <sys/types.h>
#include <sys/socket.h>
#include <stdio.h>

int main()
{
  printf("Got a socket FD %d\n\n", socket(AF_INET, SOCK_STREAM, 0));
  return 0;
}
