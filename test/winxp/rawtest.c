/**************************************************************/
/* Sending TCP segments using RAW sockets -- Proof of concept */
/* Steve Bishop - 20020730				      */
/**************************************************************/

#include <winsock2.h>
#include <ws2tcpip.h>
#include <windows.h>
#include <stdio.h>

void error(char *s)
{
  printf("%s\n", s);
  exit(1);
}

char packet[] = {
    0x45, 0x00, 0x00, 0x14, 0x06, 0x30, 0x00, 0x00, 0xff, 0x06,
    0x33, 0xfd, 0xc0, 0xa8, 0x00, 0x03, 0xc0, 0xa8, 0x00, 0x63
};

int main()
{
  SOCKET sd;
  int on=1;
  struct sockaddr_in local, remote;
  unsigned int result;
  char *sendpacket;

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

  //Open a RAW socket
  sd = socket(AF_INET, SOCK_RAW, IPPROTO_IP);    //IPPROTO_TCP ignored if IP_HDRINCL set as sock_opt below
  if(sd==INVALID_SOCKET)
    error("failed to open socket");



  //Set the socket options to state that *we're* creating the IP
  //header
  if(setsockopt(sd, IPPROTO_IP, IP_HDRINCL, (char*)&on, sizeof(on)) == SOCKET_ERROR) {
    printf("%u", WSAGetLastError());
    error("setting the socket options failed");
  }



  //Create socket sendto options
  memset(&remote,0,sizeof(remote));
  remote.sin_family = AF_INET;
  remote.sin_port = htons(0);
  remote.sin_addr.s_addr = inet_addr("192.168.0.12");

  if(!(sendpacket = malloc(20))) {
    error("malloc failed");
  }

  memcpy(sendpacket, packet, 20);

  //Send IP packet onto network
  result = sendto(sd, sendpacket, 20, 0, (struct sockaddr*)&remote, sizeof(remote));
  if(result == SOCKET_ERROR && (WSAGetLastError() != WSAEWOULDBLOCK)) {
    printf("%u", WSAGetLastError());
    error("send failed");
  }


  //Close the socket and quit
  close(sd);
  return 0;
}

