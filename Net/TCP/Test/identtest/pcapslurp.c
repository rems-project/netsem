#ifdef WIN32
#include <winsock2.h>
#include <windows.h>
#endif

#include <pcap.h>
#include <stdio.h>

char *outputfile = NULL;
char *interfaces = NULL;
char *filterstr = NULL;
int numpackets = 0;

void print_usage()
{
  printf("Usage: pcapslurp -c num [options]\n");
  printf("         -o outputfile\n");
  printf("         -i interface e.g. eth0\n");
  printf("         -f pcap filter string e.g. tcp\n");
  printf("         -c number of packets to capture\n");
  printf("Example: pcapslurp -c 10 -o output -i eth0 -f \"tcp and icmp\"\n\n");
}

/* Command-line arguments
 * pcap slurp -c num [options]
 *   -o outputfile
 *   -i interface
 *   -f pcap filter string
 *   -c number of packets to capture
 */
int parseCmdLineArgs(int argc, char **argv)
{
  int i=0;

  if((argc < 3) || ((argc % 2) == 0)) {
    printf("Incorrect arguments.\n");
    print_usage();
    exit(1);
  }

  for(i=1; i<argc; i++) {
    if(strcmp(argv[i], "-f") == 0)
      filterstr = argv[++i];
    else if(strcmp(argv[i], "-o") == 0)
      outputfile = argv[++i];
    else if(strcmp(argv[i], "-i") == 0)
      interfaces = argv[++i];
    else if(strcmp(argv[i], "-c") == 0)
      numpackets = atoi(argv[++i]);
  }

  if(numpackets == 0) {
    printf("Incorrect arguments --- must specify number of packets with -c\n");
    print_usage();
    exit(1);
  }
  return 0;
}

void tidyup(pcap_t *handle, FILE *fd)
{
  if(handle != NULL)
    pcap_close(handle);
  if(fd != stdout)
    fclose(fd);
}

int main(int argc, char **argv)
{
  pcap_t *handle;
  char *dev;
  char errbuf[PCAP_ERRBUF_SIZE];
  struct bpf_program filter;
  bpf_u_int32 net, mask;
  struct pcap_pkthdr header;
  const u_char *packet;
  FILE *outputfd;
  unsigned int i, j, k;


  parseCmdLineArgs(argc, argv);

  /* Get default device if none specified */
  if(interfaces == NULL) {
    dev = pcap_lookupdev(errbuf);
    if(dev == NULL) {
      printf("Error: %s\n", errbuf);
      abort();
    }
  }
  else
    dev = interfaces;


  /* Get the device properties */
  if(pcap_lookupnet(dev, &net, &mask, errbuf) == -1) {
    printf("Error: %s\n", errbuf);
    abort();
  }


  /* Open the output file for writing
     or use stdout otherwise */
  if(outputfile == NULL)
    outputfd = stdout;
  else {
    outputfd = fopen(outputfile, "w+");
    if(outputfd == NULL) {
      perror("Error: opening output file failed");
      abort();
    }
  }


  /* Open the pcap sniffing session */
  handle = pcap_open_live(dev, 65535, 1, 1000, errbuf);
  if(handle == NULL) {
    printf("Error: %s\n", errbuf);
    tidyup(handle, outputfd);
    exit(1);
  }

  /* If a filter has been provided compile and apply it */
  if(filterstr != NULL) {
    printf("Applying filter: %s\n", filterstr);
    if(pcap_compile(handle, &filter, filterstr, 0, net) == -1) {
      printf("Error: invalid pcap filter\n");
      tidyup(handle, outputfd);
      exit(1);
    }
    if(pcap_setfilter(handle, &filter) == -1) {
      printf("Error: unable to apply pcap filter\n");
      tidyup(handle, outputfd);
      exit(1);
    }
  }

  if(outputfd != stdout)
    fprintf(stderr, "Working...");

  for(i=0; i<numpackets; i++) {
    //Get next packet
    packet = pcap_next(handle, &header);

    //Some sanity checks
    if(packet == NULL) {
      i--; //don't want to increment the packet counter
      continue; //if we don't get a packet ;-)
    }
    if(header.len != header.caplen) {
      printf("Error: whole packet not captured\n");
      tidyup(handle, outputfd);
      exit(1);
    }
    if(header.len < 14) {
      printf("Error: packet too short\n");
      tidyup(handle, outputfd);
      exit(1);
    }

    if(outputfd != stdout)
      fprintf(stderr, ".");

    //Output packet to file (or stdout)
    fprintf(outputfd, "*Comment=Packet %d\n", i);
    fprintf(outputfd, "*Length=%d\n", header.caplen-14);
    fprintf(outputfd, "*Data=");
    for(j=14, k=0; j<header.caplen; j++, k++) {
      if((k % 16) == 0)
	fprintf(outputfd, "\n");
      if((k % 2) == 0)
        fprintf(outputfd, " ");

      fprintf(outputfd, "%2.2x", packet[j]);
    }
    fprintf(outputfd, "\n*-\n");
    fflush(outputfd);
  }

  printf("\n");

  /* Tidy up */
  tidyup(handle, outputfd);

  return 0;
}













