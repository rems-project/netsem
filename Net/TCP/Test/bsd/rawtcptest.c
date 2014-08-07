/**************************************************************/
/* Sending TCP segments using RAW sockets -- Proof of concept */
/* Steve Bishop - 20020730				      */
/**************************************************************/

#include <sys/types.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <stdio.h>

typedef struct _IP {
  struct ip *hdr;
  char *options;
  char *data;
} IP;

typedef struct _TCP {
  struct tcphdr *hdr;
  char *options;
  char *data;
} TCP;

typedef struct _PSEUDO {
  in_addr_t ip_src;
  in_addr_t ip_dst;
  u_int8_t  mbz;
  u_int8_t  ip_p;
  u_int16_t tcp_len;
} PSEUDO;

/* ---------------------------------------- */
/* void error(int sd, char *str)
 * Arguments: sd - socket descriptor
 *	      str - pointer to a buffer
 * Returns:   void
 * Desc:      If an error occurs, close the open socket handle,
 *	      report the error and quit
 */
void error(int sd, char *str)
{
  printf("Error: %s\n", str);

  if(sd != -1)
    close(sd);

  exit(1);
}

/* ---------------------------------------- */
/* void dump_to_screen(char *data, int len)
 * Argument:  data - pointer to a buffer
 *	      len - length of buffer
 * Returns:   void
 * Desc:      Dump buffer contents to the console
 *	      in hex and decimal
 */
void dump_to_screen(char *data, int len)
{
  int i=0, width=0;
  char *d = data;

  for(i=0; i<len; i++)
  {
    printf("%0.2x(%0.3d) ", *d & 0xff, *d & 0xff);
    d++;
    width += 7;
    if(width == 70)
    {
      printf("\n");
      width=0;
    }
  }

  return;
}


/* ---------------------------------------- */
/* u_short calc_IPchecksum(char *header, ....)
 * Argument:  header - pointer to IP header buffer
 *	      options - pointer to IP options buffer
 *	      ip_hl - length of ip header (in 32-bit words)
 * Returns:   IP checksum (already inverted)
 * Desc:      Calculate the IP checksum over the IP header
 *	      and options. The IP checksum is 1's complement
 *	      arithmetic over the header and options split
 *	      into 16-bit words
 */
u_short calc_IPchecksum(char *header, const char *options, unsigned int ip_hl)
{
  u_short length = ip_hl & 0xFFFF;
  int acc = 0;
  u_short *currpos = (u_short*)header;
  int i = 0;

  if(ip_hl < 5)
    error(-1, "IP header too short");

  //Calculate IP checksum by adding each 16-bit word into
  //a 32-bit integer...
  for(i=0; i<10; i++)
  {
    acc += *currpos++;
  }
  currpos = (u_short *)options;
  for(i=0; i<(ip_hl*2 - 10); i++)
  {
    acc += *currpos++;
  }

  //...then add in all of the overflow
  acc = (acc >> 16) + (acc & 0xFFFF);
  acc += (acc >> 16);

  return(~acc);
}

/* ---------------------------------------- */
/* void create_iphdr(IP *ip, u_int8_t ip_v, ......)
 * Argument:  ip - pointer to ip structure
 *	      ip_v - IP version no
 *	      ip_hl - IP header length (in 32-bit words)
 *	      ip_tos - IP type-of-service
 *	      ip_len - length of IP packet (in bytes)
 *	      ip_id - identification value
 *	      ip_off - fragmentation offset & flags
 *	      ip_ttl - time-to-live
 *	      ip_p - protocol value (e.g. 6=TCP)
 *	      ip_sum - checksum (over header and options)
 *	      ip_src - 32-bit IP source address
 *	      ip_dst - 32-bit IP destination address
 * Returns:   void
 * Desc:      Creates an IP header in ip->hdr
 */
void create_iphdr(IP *ip, u_int8_t ip_v, u_int8_t ip_hl, u_int8_t ip_tos,
		    u_short ip_len, u_short ip_id, u_short ip_off, u_int8_t ip_ttl,
		      u_int8_t ip_p, u_int16_t ip_sum, in_addr_t ip_src, in_addr_t ip_dst)
{
  struct ip *iphdr;
  iphdr = (struct ip*)malloc(sizeof(struct ip));
  if(iphdr == NULL)
    error(-1, "failed to allocate memory for IP header");

  iphdr->ip_v = ip_v;
  iphdr->ip_hl = ip_hl;
  iphdr->ip_tos = ip_tos;
  iphdr->ip_len = ip_len;
  iphdr->ip_id = htons(ip_id);
  iphdr->ip_off = ip_off;
  iphdr->ip_ttl = ip_ttl;
  iphdr->ip_p = ip_p;
  iphdr->ip_src.s_addr = ip_src;
  iphdr->ip_dst.s_addr = ip_dst;

  //Calculate the checksum
  iphdr->ip_sum = htons(ip_sum);
  //if(ip_sum == 0)
    //    iphdr->ip_sum = calc_IPchecksum((char *)iphdr, NULL, ip_hl);

  ip->hdr = iphdr;

  return;
}

/* ---------------------------------------- */
/* u_int16_t calc_TCPchecksum(struct tcphdr *tcpheader, ...)
 * Arguments: tcpheader - tcp segment header structure
 *	      options - tcp segment options buffer
 *	      data - tcp segment data buffer
 *	      pheader - tcp pseudo header buffer
 *	      th_off - length of tcp header
 *	      datasize - length of tcp data buffer
 *	      optionsize - length of tcp options buffer
 * Returns:   TCP checksum (already inverted)
 * Desc:      Calculates a 1's-complement TCP header checksum
 *	      over the TCP header, pseudo header, options
 *	      and data.
 */
u_int16_t calc_TCPchecksum(struct tcphdr *tcpheader, char *options, char *data, PSEUDO *pheader,
			u_int16_t th_off, u_int16_t datasize, u_int16_t optionsize)
{
  int acc=0, i=0;
  u_short *d = (u_short *)data;

  //Calculate the checksum by adding each 16-bit word in the
  //data(payload), options and header into a 32-bit integer...
  for(i=datasize; i>1; i-=2)
    acc += *d++;

  //...being careful if the number of data bytes is
  //not even...
  if(i==1)
    acc += (*d << 8) & 0xFF00;

  d = (u_short *)options;
  for(i=optionsize; i>1; i-=2)
    acc += *d++;

  d = (u_short *)tcpheader;
  for(i=0; i < th_off*2; i++)
    acc += *d++;

  //...and add in all of the carry at the end
  acc = (acc >> 16) + (acc & 0xFFFF);
  acc += acc >> 16;

  return (~acc);
}

/* ---------------------------------------- */
/* void create_tcphdr(TCP *tcp, u_int16_t datasize, ....)
 * Arguments: tcp - tcp segment datastructure
 *	      datasize - size of tcp segment data(payload) buffer
 *	      optionsize - size of tcp segment options buffer
 *	      ip_src - source IP address (for pseudo header)
 *	      ip_dst - destination IP address (for pseudo header)
 *	      th_sport - source port
 *	      th_dport - destination port
 *	      th_seq - sequence number
 *	      th_ack - acknowledgment number
 *	      th_off - header length (in 32-bit words)
 *	      th_x2 - reserved (should be zero ??)
 *	      th_flags - flags (e.g. syn, ack, ...)
 *	      th_win - window size
 *	      th_sum - checksum
 *	      th_urp - urgent pointer
 * Returns:   void
 * Desc:      Creates a TCP header in tcp->hdr, creating a pseudo
 *	      header and a valid checksum
 */
void create_tcphdr(TCP *tcp, u_int16_t datasize, u_int16_t optionsize, in_addr_t ip_src,
		    in_addr_t ip_dst, u_int16_t th_sport, u_int16_t th_dport, tcp_seq th_seq,
		      tcp_seq th_ack, u_int8_t th_off, u_int8_t th_x2, u_int8_t th_flags,
			u_int16_t th_win,  u_int16_t th_sum, u_int16_t th_urp)
{
  struct tcphdr *tcpheader;
  PSEUDO *pheader;

  tcpheader = (struct tcphdr*)malloc(sizeof(struct tcphdr));
  if(tcpheader == NULL)
    error(-1, "failed to allocate memory for TCP header");
  pheader = (PSEUDO*)malloc(sizeof(PSEUDO));
  if(pheader == NULL)
    error(-1, "failed to allocate memory for pseudo header");

  tcpheader->th_sport = htons(th_sport);
  tcpheader->th_dport = htons(th_dport);
  tcpheader->th_seq = htonl(th_seq);
  tcpheader->th_ack = htonl(th_ack);
  tcpheader->th_off = th_off;
  tcpheader->th_x2 = th_x2;
  tcpheader->th_flags = th_flags;
  tcpheader->th_win = htons(th_win);
  tcpheader->th_urp = htons(th_urp);

  tcpheader->th_sum = htons(th_sum);

  //Create a TCP pseudo header
  pheader->ip_src = ip_src;
  pheader->ip_dst = ip_dst;
  pheader->mbz = 0;
  pheader->ip_p = IPPROTO_TCP;
  pheader->tcp_len = htons(datasize + optionsize + th_off*4);

  //Calculate a checksum
  if(th_sum == 0)
    tcpheader->th_sum = calc_TCPchecksum(tcpheader, tcp->options, tcp->data, pheader, th_off, datasize, optionsize);
  tcp->hdr = tcpheader;

  return;
}


/* ---------------------------------------- */
/* char *tcp_ip_encaps(char *dest, TCP *segment, ...)
 * Arguments: dest - pointer to a destination buffer
 *	      segment - pointer to a TCP segment datastructure
 *	      hdr - size of TCP header (in bytes)
 *	      opts - size of TCP options (in bytes)
 *	      data - size of TCP data (in bytes)
 * Returns:   a pointer to the destination buffer
 * Desc:      Creates a whole TCP segment linearly in a
 *	      buffer by concatenating the header, options
 *	      and data. This can be used to embed a TCP
 *	      segment in a IP packets data(payload) buffer
 */
char *tcp_ip_encaps(char *dest, TCP *segment, u_int16_t hdr, u_int16_t opts, u_int16_t data)
{
  dest = (char *)malloc(hdr+opts+data);
  if(dest == NULL)
    error(-1, "tcp_ip_encaps - failed to allocate memory for tcp packet encapsulation");

  //Concatenate the header, options and data(payload)
  memcpy(dest, (char *)segment->hdr, hdr);
  memcpy(dest+hdr, (char *)segment->options, opts);
  memcpy(dest+hdr+opts, (char *)segment->data, data);

  return dest;
}

/* ---------------------------------------- */
/* char *create_ip(char *dest, IP *packet)
 * Arguments: dest - pointer to a destination buffer
 *	      packet - pointer to a IP packet datastructure
 * Returns:   a pointer to the destination buffer
 * Desc:      Creates a whole IP packet by concatenating
 *	      the IP header, options and data(payload)
 */
char *create_ip(char *dest, IP *packet)
{
  dest = (char *)malloc(packet->hdr->ip_len);
  if(dest == NULL)
    error(-1, "failed to allocate memory to create final IP packet");

  //Concatenate the header, options and data(payload)
  memcpy(dest, (char *)packet->hdr, 20);
  memcpy(dest + 20, packet->options, (packet->hdr->ip_hl*4) - 20);
  memcpy(dest + packet->hdr->ip_hl*4, packet->data, packet->hdr->ip_len - packet->hdr->ip_hl*4);

  return dest;
}


/* ---------------------------------------- */
/* int main() - Main program
 * Arguments: none
 * Returns:   error flags
 * Desc:      Create a dummy TCP/IP packet
 *	      and outputs onto a raw socket
 */
int main()
{
  int sd, on=1;
  IP *packet;
  TCP *segment;
  char *ippacket, *tcpsegment;
  struct sockaddr_in mysocket;
  unsigned short sport, dport;
  in_addr_t saddr, daddr;

  packet = (IP *)malloc(sizeof(IP));
  if(packet == NULL)
    error(-1, "failed to allocate memory for packet");
  segment = (TCP *)malloc(sizeof(TCP));
  if(segment == NULL)
    error(-1, "failed to allocate memory for segment");

  //Open a RAW socket
  sd = socket(PF_INET, SOCK_RAW, IPPROTO_TCP /*TCP*/);    //IPPROTO_TCP ignored if IP_HDRINCL set as sock_opt below
  if(sd == -1)
    error(sd, "failed to open socket");

  //Set the socket options to state that *we're* creating the IP
  //header
  if(setsockopt(sd,IPPROTO_IP, IP_HDRINCL, (char *)&on, sizeof(on)) < 0)
    error(sd, "setting the socket options failed");

  saddr = inet_addr("192.168.0.12");
  daddr = inet_addr("192.168.0.13");
  sport = 0xFFF;
  dport = 0xFFF;

  //Create the TCP data
  /*.....*/
  segment->data = (char *)NULL;
  segment->options = (char *)NULL;

  //Create the TCP header
  create_tcphdr(segment, 0, 0, saddr, daddr, sport, dport, 10, 0, 5, 0, TH_SYN, 1, 0, 0);

  //Encapsulate TCP packet in IP data
   packet->data = tcp_ip_encaps(packet->data, segment, 20, 0, 0);

  //Create the IP header
  create_iphdr(packet, IPVERSION, 5, 0, 20,
		0, IP_DF, 255, 6, 0, saddr, daddr);

  //Create final IP packet
  ippacket = create_ip(ippacket, packet);

  //Print packet to screen for debug
  dump_to_screen((char*)ippacket, 20);

  //Create socket sendto options
  memset(&mysocket,'\0',sizeof(mysocket));
  mysocket.sin_family = AF_INET;
  mysocket.sin_port = htons(dport);
  mysocket.sin_addr.s_addr = daddr;

  //Send IP packet onto network
  if(sendto(sd, ippacket, 20, 0, (struct sockaddr*)&mysocket, sizeof(mysocket)) != 20)
    error(sd, "send failed");

  //Close the socket and quit
  close(sd);
  printf("\n");
  return 0;
}

