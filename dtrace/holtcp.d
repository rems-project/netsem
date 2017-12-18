#!/usr/sbin/dtrace -Cs

#pragma D option quiet

// -----------------------------------------------------------------------------
// BOILERPLATE for printing
// -----------------------------------------------------------------------------

inline string tcp_state_str[int32_t state] =
  state == TCPS_CLOSED ? "CLOSED" :
  state == TCPS_LISTEN ? "LISTEN" :
  state == TCPS_SYN_SENT ? "SYN_SENT" :
  state == TCPS_SYN_RECEIVED ? "SYN_RECEIVED" :
  state == TCPS_ESTABLISHED ? "ESTABLISHED" :
  state == TCPS_CLOSE_WAIT ? "CLOSE_WAIT" :
  state == TCPS_FIN_WAIT_1 ? "FIN_WAIT_1" :
  state == TCPS_CLOSING ? "CLOSING" :
  state == TCPS_LAST_ACK ? "LAST_ACK" :
  state == TCPS_FIN_WAIT_2 ? "FIN_WAIT_2" :
  state == TCPS_TIME_WAIT ? "TIME_WAIT" :
  "<unknown>";

inline string sock_str[int32_t sockt] =
  sockt == 1 ? "SOCK_STREAM" :
  sockt == 2 ? "SOCK_DGRAM" :
  sockt == 3 ? "SOCK_RAW" :
  "<unknown>" ;

inline string errno_str[int err] =
  err == EPERM ? "EPERM" :
  err == ENOENT ? "ENOENT" :
  err == ESRCH ? "ESRCH" :
  err == EINTR ? "EINTR" :
  err == EIO ? "EIO" :
  err == ENXIO ? "ENXIO" :
  err == E2BIG ? "E2BIG" :
  err == ENOEXEC ? "ENOEXEC" :
  err == EBADF ? "EBADF" :
  err == ECHILD ? "ECHILD" :
  err == EDEADLK ? "EDEADLK" :
  err == ENOMEM ? "ENOMEM" :
  err == EACCES ? "EACCES" :
  err == EFAULT ? "EFAULT" :
  err == ENOTBLK ? "ENOTBLK" :
  err == EBUSY ? "EBUSY" :
  err == EEXIST ? "EEXIST" :
  err == EXDEV ? "EXDEV" :
  err == ENODEV ? "ENODEV" :
  err == ENOTDIR ? "ENOTDIR" :
  err == EISDIR ? "EISDIR" :
  err == EINVAL ? "EINVAL" :
  err == ENFILE ? "ENFILE" :
  err == EMFILE ? "EMFILE" :
  err == ENOTTY ? "ENOTTY" :
  err == ETXTBSY ? "ETXTBSY" :
  err == EFBIG ? "EFBIG" :
  err == ENOSPC ? "ENOSPC" :
  err == ESPIPE ? "ESPIPE" :
  err == EROFS ? "EROFS" :
  err == EMLINK ? "EMLINK" :
  err == EPIPE ? "EPIPE" :
  err == EDOM ? "EDOM" :
  err == ERANGE ? "ERANGE" :
  err == EAGAIN ? "EAGAIN" :
  err == EWOULDBLOCK ? "EWOULDBLOCK" :
  err == EINPROGRESS ? "EINPROGRESS" :
  err == EALREADY ? "EALREADY" :
  err == ENOTSOCK ? "ENOTSOCK" :
  err == EDESTADDRREQ ? "EDESTADDRREQ" :
  err == EMSGSIZE ? "EMSGSIZE" :
  err == EPROTOTYPE ? "EPROTOTYPE" :
  err == ENOPROTOOPT ? "ENOPROTOOPT" :
  err == EPROTONOSUPPORT ? "EPROTONOSUPPORT" :
  err == ESOCKTNOSUPPORT ? "ESOCKTNOSUPPORT" :
  err == EOPNOTSUPP ? "EOPNOTSUPP" :
  err == ENOTSUP ? "ENOTSUP" :
  err == EPFNOSUPPORT ? "EPFNOSUPPORT" :
  err == EAFNOSUPPORT ? "EAFNOSUPPORT" :
  err == EADDRINUSE ? "EADDRINUSE" :
  err == EADDRNOTAVAIL ? "EADDRNOTAVAIL" :
  err == ENETDOWN ? "ENETDOWN" :
  err == ENETUNREACH ? "ENETUNREACH" :
  err == ENETRESET ? "ENETRESET" :
  err == ECONNABORTED ? "ECONNABORTED" :
  err == ECONNRESET ? "ECONNRESET" :
  err == ENOBUFS ? "ENOBUFS" :
  err == EISCONN ? "EISCONN" :
  err == ENOTCONN ? "ENOTCONN" :
  err == ESHUTDOWN ? "ESHUTDOWN" :
  err == ETOOMANYREFS ? "ETOOMANYREFS" :
  err == ETIMEDOUT ? "ETIMEDOUT" :
  err == ECONNREFUSED ? "ECONNREFUSED" :
  err == ELOOP ? "ELOOP" :
  err == ENAMETOOLONG ? "ENAMETOOLONG" :
  err == EHOSTDOWN ? "EHOSTDOWN" :
  err == EHOSTUNREACH ? "EHOSTUNREACH" :
  err == ENOTEMPTY ? "ENOTEMPTY" :
  err == EPROCLIM ? "EPROCLIM" :
  err == EUSERS ? "EUSERS" :
  err == EDQUOT ? "EDQUOT" :
  err == ESTALE ? "ESTALE" :
  err == EREMOTE ? "EREMOTE" :
  err == EBADRPC ? "EBADRPC" :
  err == ERPCMISMATCH ? "ERPCMISMATCH" :
  err == EPROGUNAVAIL ? "EPROGUNAVAIL" :
  err == EPROGMISMATCH ? "EPROGMISMATCH" :
  err == EPROCUNAVAIL ? "EPROCUNAVAIL" :
  err == ENOLCK ? "ENOLCK" :
  err == ENOSYS ? "ENOSYS" :
  err == EFTYPE ? "EFTYPE" :
  err == EAUTH ? "EAUTH" :
  err == ENEEDAUTH ? "ENEEDAUTH" :
  err == EIDRM ? "EIDRM" :
  err == ENOMSG ? "ENOMSG" :
  err == EOVERFLOW ? "EOVERFLOW" :
  err == ECANCELED ? "ECANCELED" :
  err == EILSEQ ? "EILSEQ" :
  err == ENOATTR ? "ENOATTR" :
  err == EDOOFUS ? "EDOOFUS" :
  err == EBADMSG ? "EBADMSG" :
  err == EMULTIHOP ? "EMULTIHOP" :
  err == ENOLINK ? "ENOLINK" :
  err == EPROTO ? "EPROTO" :
  err == ELAST ? "ELAST" :
  err == ERESTART ? "ERESTART" :
  err == EJUSTRETURN ? "EJUSTRETURN" :
  err == ENOIOCTL ? "ENOIOCTL" :
  err == EDIRIOCTL ? "EDIRIOCTL" :
  "<unknown>" ;

//some socket options (from sys/socket.h)
inline int SO_REUSEADDR = 0x0004;
inline int SO_LINGER    = 0x0080;
inline int SO_SNDBUF    = 0x1001;
inline int SO_RCVBUF    = 0x1002;

//from sys/fcntl.h
//inline int O_NONBLOCK   = 0x0004;
inline int O_ASYNC      = 0x0040;

//from sys/socket.h
inline int SHUT_RD = 0;
inline int SHUT_WR = 1;
inline int SHUT_RDWR = 2;

inline string fcntl_flag_str[int flags] =
  flags & (O_NONBLOCK | O_ASYNC) >= (O_NONBLOCK | O_ASYNC) ? "O_NONBLOCK; O_ASYNC" :
  flags & O_ASYNC                                          ? "O_ASYNC" :
  flags & O_NONBLOCK                                       ? "O_NONBLOCK" :
  "" ;

inline int F_GETFL      = 0x03;
inline int F_SETFL      = 0x04;
// -----------------------------------------------------------------------------
// GLOBALS (program name, duration printer, what does active mean?)
// -----------------------------------------------------------------------------

//clipped to 14 characters!!
//#define prog "local_tcptest.nativ"
#define prog "packetdrill"
//active defined for syscalls
#define act execname == prog && self->started == 1
//active defined for TCP kernel probes (no execname, only SO_DEBUG)
#define tr_act args[0]->tcps_debug == 1

int ts;
int step;

#define dur()                     \
  this->dur = timestamp - ts ;    \
  this->us  = this->dur / 1000;   \
  this->s   = this->us / 1000000; \
  this->us  = this->us % 1000000; \
  ts  = timestamp ;               \
  printf("(* Merge Index: %d *)\n", step); \
  step = step + 1 ;                        \
  printf("Lh_epsilon(duration %d %06d);\n", this->s, this->us); \
  printf("(* Merge Index: %d *)\n", step); \
  step = step + 1 ;

//start and stop of test is signalled by a sleep(0)
syscall::nanosleep:entry
/execname == prog && ((struct timespec *)copyin(arg0, 8))->tv_sec == 0/
{
  self->zzz = 1;
}

//this is packetdrill (which says START and STOP instead of sleep(0))
syscall::write:entry
/execname == prog && arg0 == 1 && copyinstr(arg1, 5) == "START"/
{
  //printf("ready for orders!\n");
  ts = timestamp;
  self->setsockopt = 0; //to avoid SO_DEBUG
  self->started = 1;
}

//syscall::write:entry
///copyinstr(arg1, 4) == "STOP"/
//{
//  printf("wrote STOP\n");
//}

syscall::write:entry
/act && arg0 == 1 && copyinstr(arg1, 4) == "STOP"/
{
  printf("will exit now\n");
  exit(0);
}

syscall::nanosleep:return
/execname == prog && self->zzz == 1 && self->started == 0/
{
  printf("nanosleep returned! ready for orders!\n");
  self->zzz = 0;
  ts = timestamp;
  self->setsockopt = 0; //to avoid SO_DEBUG
  self->started = 1;
}

syscall::nanosleep:return
/act && self->zzz == 1/
{
//  exit(0);
}

//flow filters
int sport;
int dport;
string src;
string dst;

int f_active;

dtrace:::BEGIN
{
  sport = 0;
  dport = 0;
  src = "";
  dst = "";
  f_active = 0;
  step = 0;
}

inline int of_hex[int8_t c] =
  c == '0' ? 0 :
  c == '1' ? 1 :
  c == '2' ? 2 :
  c == '3' ? 3 :
  c == '4' ? 4 :
  c == '5' ? 5 :
  c == '6' ? 6 :
  c == '7' ? 7 :
  c == '8' ? 8 :
  c == '9' ? 9 :
  c == 'A' ? 10 :
  c == 'B' ? 11 :
  c == 'C' ? 12 :
  c == 'D' ? 13 :
  c == 'E' ? 14 :
  c == 'F' ? 15 :
  0 ;

#define l_of_hex(s, off) of_hex[s[off]] * 16 + of_hex[s[off+1]]
#define p_of_hex(s, off) (of_hex[s[off]] * 16 + of_hex[s[off+1]]) * 256 + of_hex[s[off+2]] * 16 + of_hex[s[off+3]]

syscall::write:entry
/act && arg0 == 1 && copyinstr(arg1, 8) == "filter: "/
{
  self->s = (char *)copyin(arg1 + 8, arg2 - 9);
  self->slen = l_of_hex(self->s, 1) ;
  src = copyinstr(arg1 + 12, self->slen) ;
  sport = p_of_hex(self->s, 5 + self->slen) ;
  self->dlen = l_of_hex(self->s, 14 + self->slen) ;
  dst = copyinstr(arg1 + 25 + self->slen, self->dlen) ;
  dport = p_of_hex(self->s, self->slen + self->dlen + 18) ;
  f_active = 1 ;
  printf("filtering flow %s:%d -> %s:%d\n", src, sport, dst, dport) ;
}

#define ports(tcp) f_active && (sport == 0 || tcp->tcp_sport == sport) && (dport == 0 || tcp->tcp_dport == dport)
#define rports(tcp) f_active && (sport == 0 || tcp->tcp_dport == sport) && (dport == 0 || tcp->tcp_sport == dport)

#define thports(tcp) f_active && (sport == 0 || ntohs(tcp->th_sport) == sport) && ((dport == 0 && ((ntohs(tcp->th_dport) == 8080) || (ntohs(tcp->th_sport) == 8080))) || ntohs(tcp->th_dport) == dport)
#define thrports(tcp) f_active && (sport == 0 || ntohs(tcp->th_dport) == sport) && ((dport == 0 && ((ntohs(tcp->th_sport) == 8080) || (ntohs(tcp->th_dport) == 8080))) || ntohs(tcp->th_sport) == dport)

#define flow(ip) ip->ip_saddr != "127.0.0.1" && (src == "" || ip->ip_saddr == src) && (dst == "" || ip->ip_daddr == dst)
#define rflow(ip) ip->ip_daddr != "127.0.0.1" && (src == "" || ip->ip_daddr == src) && (dst == "" || ip->ip_saddr == dst)


// -----------------------------------------------------------------------------
// TCP DEBUG probes
// -----------------------------------------------------------------------------

//XXX: `t_rttseg` used to be NONE if rtttime = 0
//XXX: `ts_recent` used to be TimeWindowClosed if ts_recent is 0
#define print_tcb(tcb) \
 printf(" %s,\n", tcp_state_str[tcb->tcps_state]);                          \
 printf(" <|\n");                                                           \
 printf("   snd_una := tcp_seq_local(n2w %u);\n", tcb->tcps_suna);          \
 printf("   snd_max := tcp_seq_local(n2w %u);\n", tcb->tcps_smax);          \
 printf("   snd_nxt := tcp_seq_local(n2w %u);\n", tcb->tcps_snxt);          \
 printf("   snd_wl1 := tcp_seq_foreign(n2w %u);\n", tcb->tcps_swl1);        \
 printf("   snd_wl2 := tcp_seq_local(n2w %u);\n", tcb->tcps_swl2);          \
 printf("   iss := tcp_seq_local(n2w %u);\n", tcb->tcps_iss);               \
 printf("   snd_wnd := %u;\n", tcb->tcps_swnd);                             \
 printf("   snd_cwnd := %u;\n", tcb->tcps_cwnd);                            \
 printf("   snd_ssthresh := %u;\n", tcb->tcps_cwnd_ssthresh);               \
 printf("   rcv_wnd := %u;\n", tcb->tcps_rwnd);                             \
 printf("   rcv_nxt := tcp_seq_foreign(n2w %u);\n", tcb->tcps_rnxt);        \
 printf("   rcv_up := tcp_seq_foreign(n2w %u);\n", tcb->tcps_rup);          \
 printf("   irs := tcp_seq_foreign(n2w %u);\n", tcb->tcps_irs);             \
 printf("   rcv_adv := tcp_seq_foreign(n2w %u);\n", tcb->tcps_radv);        \
 printf("   snd_recover := tcp_seq_local(n2w %u);\n", tcb->tcps_srecover);  \
 printf("   t_maxseg := %u;\n", tcb->tcps_mss);                             \
 printf("   t_dupacks := %u;\n", tcb->tcps_dupacks);                        \
 printf("   t_rttseg := SOME(ts_seq(n2w %u), tcp_seq_local(n2w %u));\n",    \
        tcb->tcps_rtttime, tcb->tcps_rtseq);                                \
 printf("   snd_scale := %u;\n", tcb->tcps_snd_ws);                         \
 printf("   rcv_scale := %u;\n", tcb->tcps_rcv_ws);                         \
 printf("   ts_recent := TimeWindow(ts_seq(n2w %u), never_timer);\n",       \
        tcb->tcps_ts_recent);                                               \
 printf("   last_ack_sent := tcp_seq_foreign(n2w %u)\n", tcb->tcps_rack);   \
 printf(" |>);\n");

//there's a int64 used on the Caml side, which ranges to 2 ^ 63 - 1
#define sid (arg0 % 9223372036854775808ul)

tcp:kernel::debug-input
/tr_act/
{
  dur();
//  printf("flags: %x seq %u\n", args[1]->tcp_flags, args[1]->tcp_seq);
  printf("Lh_trace(\n TA_INPUT,\n SID %u,\n", sid);
  printf(" SOME(SOME(IP %s), SOME(Port %d), SOME(IP %s), SOME(Port %d)),\n",
         args[2]->ip_daddr, args[1]->tcp_dport, args[2]->ip_saddr, args[1]->tcp_sport);
  print_tcb(args[0])
}

tcp:kernel::debug-output
/tr_act/
{
  dur();
//  printf("flags: %x seq %u\n", args[1]->tcp_flags, args[1]->tcp_seq);
  printf("Lh_trace(\n TA_OUTPUT,\n SID %u,\n", sid);
  printf(" SOME(SOME(IP %s), SOME(Port %d), SOME(IP %s), SOME(Port %d)),\n",
         args[2]->ip_saddr, args[1]->tcp_sport, args[2]->ip_daddr, args[1]->tcp_dport);
  print_tcb(args[0])
}

tcp:kernel::debug-drop
/tr_act/
{
  dur();
  printf("Lh_trace(\n TA_DROP,\n SID %u,\n", sid);
  printf(" SOME(SOME(IP %s), SOME(Port %d), SOME(IP %s), SOME(Port %d)),\n",
         args[2]->ip_daddr, args[1]->tcp_dport, args[2]->ip_saddr, args[1]->tcp_sport);
  print_tcb(args[0])
}

tcp:kernel::debug-user
/tr_act/
{
  dur();
  printf("Lh_trace(\n TA_USER,\n SID %u,\n", sid);
  printf(" NONE,\n");
  print_tcb(args[0]);
}

//tcp:kernel::state-change
//{
//  printf("state change: %s -> %s\n", tcp_state_str[args[5]->tcps_state], tcp_state_str[args[3]->tcps_state]);
//}


// -----------------------------------------------------------------------------
// SYSCALL probes
// -----------------------------------------------------------------------------

syscall:::return
/act && errno != 0 &&
  (probefunc == "socket" || probefunc == "connect" || probefunc == "bind" ||
   probefunc == "getsockname" || probefunc == "getpeername" || probefunc == "close" ||
   probefunc == "listen" || probefunc == "shutdown")/
{
  dur();
  printf("Lh_return(TID %d, FAIL(%s));\n", pid, errno_str[errno]);
}

syscall:::return
/act && errno != 0 && probefunc == "setsockopt" && self->setsockopt == 1/
{
  dur();
  printf("Lh_return(TID %d, FAIL(%s));\n", pid, errno_str[errno]);
  self->setsockopt = 0;
}

syscall:::return
/act && probefunc == "setsockopt" && self->setsockopt == 1/
{
  dur();
  printf("Lh_return(TID %d, OK());\n", pid);
  self->setsockopt = 0;
}

syscall::shutdown:entry
/act && args[1] == SHUT_RD/
{
  dur();
  printf("Lh_call(TID %d, shutdown(FD %d, T, F));\n", pid, args[0]);
}
syscall::shutdown:entry
/act && args[1] == SHUT_WR/
{
  dur();
  printf("Lh_call(TID %d, shutdown(FD %d, F, T));\n", pid, args[0]);
}
syscall::shutdown:entry
/act && args[1] == SHUT_RDWR/
{
  dur();
  printf("Lh_call(TID %d, shutdown(FD %d, T, T));\n", pid, args[0]);
}


syscall::fcntl:entry
/act && args[1] == F_GETFL/
{
  self->getfl = 1;
  dur();
  printf("Lh_call(TID %d, getfileflags(FD %d));\n", pid, args[0]);
}

syscall::fcntl:entry
/act && args[1] == F_SETFL/
{
  self->setfl = 1;
  dur();
  printf("Lh_call(TID %d, setfileflags(FD %d, [%s]));\n", pid, args[0], fcntl_flag_str[args[2]]);
}

syscall::fcntl:return
/act && self->setfl == 1 && errno == 0/
{
  self->setfl = 0;
  dur();
  printf("Lh_return(TID %d, OK());\n", pid);
}

syscall::fcntl:return
/act && self->getfl == 1 && errno == 0/
{
  self->getfl = 0;
  dur();
  printf("Lh_return(TID %d, OK([%s]));\n", pid, fcntl_flag_str[args[0]]);
}

syscall::fcntl:return
/act && (self->getfl == 1 || self->setfl == 1) && errno != 0/
{
  self->getfl = 0;
  self->setfl = 0;
  dur();
  printf("Lh_return(TID %d, FAIL(%s));\n", pid, errno_str[errno]);
}

syscall::socket:entry
/act/
{
  dur();
  printf("Lh_call(TID %d, socket(%s));\n", pid, sock_str[args[1]]);
}

syscall::socket:return
/act && errno == 0/
{
  dur();
  printf("Lh_return(TID %d, OK(FD %d));\n", pid, args[0]);
}

syscall::accept:entry
/act/
{
  self->accsocket = arg1 ;
  dur();
  printf("Lh_call(TID %d, accept(FD %d));\n", pid, args[0]);
}

syscall::accept:return
/act && errno == 0/
{
  dur();
  self->sock = (struct sockaddr_in *)copyin(self->accsocket, 8) ;
  printf("Lh_return(TID %d, OK(FD %d, (IP %s, Port %u)));\n",
         pid,
         args[0],
         inet_ntoa(&(self->sock->sin_addr.s_addr)),
         ntohs(self->sock->sin_port));
}

syscall::listen:entry
/act/
{
  dur();
  printf("Lh_call(TID %d, listen(FD %d, %d));\n", pid, args[0], args[1]);
}

syscall::close:entry
/act/
{
  dur();
  printf("Lh_call(TID %d, close(FD %d));\n", pid, args[0]);
}

syscall::setsockopt:entry
/act && args[2] == SO_LINGER/
{
  dur();
  self->linger = (struct linger *)copyin(arg3, 16) ;
  printf("Lh_call(TID %d, setsocktopt(FD %d, SO_LINGER, SOME(%d, 0)));\n",
         pid, args[0],
         self->linger->l_onoff == 0 ? -42 : self->linger->l_linger);
  self->setsockopt = 1;
}

syscall::setsockopt:entry
/act && args[2] == SO_REUSEADDR/
{
  dur();
  self->bopt = copyin(arg3, 8) ;
  printf("Lh_call(TID %d, setsockbopt(FD %d, SO_REUSEADDR, %s));\n",
         pid, args[0],
         self->bopt == 0 ? "F" : "T");
  self->setsockopt = 1;
}

syscall::setsockopt:entry
/act && args[2] == SO_RCVBUF/
{
  dur();
  printf("Lh_call(TID %d, setsocknopt(FD %d, SO_RCVBUF, %d));\n",
         pid, args[0], arg3);
  self->setsockopt = 1;
}

syscall::setsockopt:entry
/act && args[2] == SO_SNDBUF/
{
  dur();
  printf("Lh_call(TID %d, setsocknopt(FD %d, SO_SNDBUF, %d));\n",
         pid, args[0], arg3);
  self->setsockopt = 1;
}

syscall::connect:entry
/act/
{
  dur();
  self->sock = (struct sockaddr_in *)copyin(arg1, 8) ;
  printf("Lh_call(TID %d, connect(FD %d, IP %s, SOME(Port %d)));\n",
         pid,
         args[0],
         inet_ntoa(&(self->sock->sin_addr.s_addr)),
         ntohs(self->sock->sin_port));
}

syscall:::return
/act && errno == 0 &&
  (probefunc == "connect" || probefunc == "bind" || probefunc == "close" || probefunc == "listen" || probefunc == "shutdown")/
{
  dur();
  printf("Lh_return(TID %d, OK());\n", pid);
}

syscall::bind:entry
/act/
{
  dur();
  self->sock = (struct sockaddr_in *)copyin(arg1, 8) ;
  printf("Lh_call(TID %d, bind(FD %d, SOME(IP %s), SOME(Port %d)));\n",
         pid,
         args[0],
         inet_ntoa(&(self->sock->sin_addr.s_addr)),
         ntohs(self->sock->sin_port));
}

syscall::getsockname:entry
/act/
{
  dur();
  self->peersock = arg1 ;
  printf("Lh_call(TID %d, %s(FD %d));\n", pid, probefunc, args[0]);
}

syscall::getsockname:return
/act && errno == 0/
{
  dur();
  self->sock = (struct sockaddr_in *)copyin(self->peersock, 8) ;
  printf("Lh_return(TID %d, OK(SOME(IP %s), SOME(Port %u)));\n",
         pid,
         inet_ntoa(&(self->sock->sin_addr.s_addr)),
         ntohs(self->sock->sin_port));
}

syscall::getpeername:entry
/act/
{
  dur();
  printf("Lh_call(TID %d, %s(FD %d));\n", pid, probefunc, args[0]);
}

// -----------------------------------------------------------------------------
// WIRE probes (actual TCP segments)
// -----------------------------------------------------------------------------

//some preprocessing for every incoming TCP frame
fbt:kernel:tcp_input:entry {
  self->m = *args[0];
  self->off = args[1];
  self->iphdr = (struct ip *)self->m->m_data;
  self->tcphdr = (struct tcphdr *)((caddr_t) self->iphdr  + *self->off);
}

//may need to filter for flow as well, not only port?
fbt:kernel:tcp_input:entry
/thports(self->tcphdr)/
{
  dur();
  printf("tcp_input\n");
  tracemem(copyoutmbuf(*args[0], 1500), 1500);
}

//fbt:kernel:tcp_do_segment:entry
///thports(self->tcphdr)/
//{
//  dur();
//  printf("tcp_do_segment drop_hdrlen %d tlen %d\n", args[4], args[5]);
//}
//
//fbt:kernel:tcp_reass:entry
///thports(self->tcphdr)/
//{
//  dur();
//  printf("tcp_reass\n");
//}
//
//fbt:kernel:tcp_reass:return
///thports(self->tcphdr)/
//{
//  dur();
//  printf("tcp_reass returned with %X (%x)\n", args[0], args[1]);
//}

//some preprocessing for every outgoing IP frame
fbt:kernel:ip_output:entry {
  self->m = args[0];
  self->iphdr = (struct ip *)self->m->m_data;
  //XXX: what about IP options!?
  self->tcphdr = (struct tcphdr *)((caddr_t) self->iphdr + 20);
}

//need to filter for flow + ports!?
fbt:kernel:ip_output:entry
/thrports(self->tcphdr)/
{
  dur();
  printf("ip_output\n");
  tracemem(copyoutmbuf(args[0], 1500), 1500);
}

/*
 * Dump TCB in format readable by HOL, as defined by NetSem.  Based on
 * the dtrace script tcpdebug distributed with FreeBSD.
 *
 * Copyright (c) 2015 George V. Neville-Neil
 * Copyright (c) 2016 Hannes Mehnert
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * NOTE: Only sockets with SO_DEBUG set will be shown.
 */
