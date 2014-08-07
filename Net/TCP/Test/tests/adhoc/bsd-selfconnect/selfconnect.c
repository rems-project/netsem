#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <assert.h>

int main()
{
  int sd;
  struct sockaddr_in addr;
  socklen_t addrlen = sizeof(struct sockaddr_in);
  int value = 1;

  struct linger lingeroptval;

  char sendb[] = "Hello, me!\n";
  char recvb[12];

  //socket
  sd = socket(AF_INET, SOCK_STREAM, 6);
  assert(sd != -1);

  //reuseaddr
  assert(setsockopt(sd, SOL_SOCKET, SO_REUSEADDR,
                     &value, sizeof(value)) != -1);


  //bind
  bzero(&addr, (size_t)addrlen);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = inet_addr("127.0.0.1");
  addr.sin_port = htons(5560);
  assert(bind(sd, (struct sockaddr*)&addr, addrlen) != -1);

  //connect
  if(connect(sd, (struct sockaddr*)&addr, addrlen) == -1) {
    printf("Connect failed!\n");
    close(sd);
    exit(1);
  }

  //send
  assert(send(sd, sendb, strlen(sendb), 0) != -1);

  //recv
  bzero(recvb, 12);
  assert(recv(sd, recvb, 12, 0) != -1);

  printf(recvb);

  //abortive close (otherwise future connects fail until !TIME_WAIT)
  bzero(&lingeroptval, sizeof(lingeroptval));
  lingeroptval.l_onoff = 1;
  lingeroptval.l_linger = 0;
  assert(setsockopt(sd, SOL_SOCKET, SO_LINGER,
                     &lingeroptval, sizeof(lingeroptval)) != -1);

  assert(close(sd) != -1);
  return 0;
}
