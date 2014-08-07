#ifndef WIN32
#include <sys/types.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#else
#include <winsock2.h>
#include <ws2tcpip.h>
#include <windows.h>
#endif

#include <stdio.h>

char *outputfile = NULL;

typedef struct _packet {
  unsigned int length;
  char data[65536];
} typacket;
typacket packet;

void printUsage()
{
  printf("Usage: fileinject filename\n");
  printf("    filename - raw packets to inject on network\n");
  printf("               in pcapslurp format\n\n");
}

void parseCmdLineArgs(int argc, char **argv)
{
  if (argc != 2) {
    printf("Invalid arguments.\n");
    printUsage();
    exit(1);
  }

  outputfile = argv[1];
}

void readNextPkt(FILE *out)
{
  char ch;
  char data[20];
  int i=0, d;

  //clear out previous packet
  packet.length = 0;

  while(!feof(out)) {
    fread(&ch, 1, 1, out);
    if(ch == '*')
      break;
  }

  fread(data, 1, 8, out);
  data[8] = '\0';
  if(strcmp(data, "Comment=") == 0) {
    while(!feof(out)) {
      fread(&ch, 1, 1, out);
      if(ch == '*')
	break;
    }

    fread(data, 1, 7, out);
    data[7] = '\0';
    if(strcmp(data, "Length=") == 0) {
      for(i=0; ; i++) {
	fread(&ch, 1, 1, out);
	if(ch == '\n') {
	  data[i] = '\0';
	  break;
	} else {
	  data[i] = ch;
	}
      }
      packet.length = atoi(data);

      while(!feof(out)) {
	fread(&ch, 1, 1, out);
	if(ch == '*')
	  break;
      }

      fread(data, 1, 5, out);
      data[5] = '\0';
      if(strcmp(data, "Data=") == 0) {
	for(i=0; i<packet.length; i++) {
	  if((i % 16) == 0) {
	    fread(data, 1, 1, out);
	  }

	  if((i % 2) == 0) {
	    fread(data, 1, 1, out);
	  }

	  data[2] = '\0';
	  fread(data, 1, 2, out);
	  sscanf(data, "%x", &d);
	  packet.data[i] = (char)d & 0xff;
	}
      }

      while(!feof(out)) {
	fread(&ch, 1, 1, out);
	if(ch == '*')
	  break;
      }
      fread(&ch, 1, 1, out);
    }
  }
}


void outputPkt(int sd)
{
  struct sockaddr_in mysocket;

  memset(&mysocket, '\0', sizeof(mysocket));
  mysocket.sin_family = AF_INET;
  mysocket.sin_port = htons(0);
  mysocket.sin_addr.s_addr = 0;

  if(sendto(sd, packet.data, packet.length, 0, (struct sockaddr*) &mysocket, sizeof(mysocket)) != packet.length){
    perror("Packet not sent successfully");
    exit(1);
  }
}

int main(int argc, char **argv)
{
  int i, sd;
  int on = 1;
  FILE *out;
  char temp;

  parseCmdLineArgs(argc, argv);
  out = fopen(outputfile, "r");
  if(out == NULL) {
    perror("Failed to open output file.");
    exit(1);
  }

  sd = socket(PF_INET, SOCK_RAW, 0);
  if(sd == -1) {
    perror("Failed to open RAW socket.");
    exit(1);
  }

  if(setsockopt(sd, IPPROTO_IP, IP_HDRINCL, (char *)&on, sizeof(on))) {
    perror("Failed to set socket option IP_HDRINCL.");
    exit(1);
    }

  while(!feof(out)) {
    readNextPkt(out);
    temp = packet.data[3];
    packet.data[3] = packet.data[2];
    packet.data[2] = temp;
    temp = packet.data[7];
    packet.data[7] = packet.data[6];
    packet.data[6] = temp;
    packet.data[10] = 0;
    packet.data[11] = 0;
    if(packet.length != 0)
      outputPkt(sd);

    /*printf("\nPacket len: %d\n", packet.length);
    for(i=0; i< packet.length; i++)
    printf("%2.2x ", packet.data[i] & 0xff);*/
  }

  fclose(out);
  return 0;
}
