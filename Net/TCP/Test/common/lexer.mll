{
open Parser
open Lexing
exception Eof

let debug str = ()
  (*let pid = Unix.getpid() in
  let tid = if(Platform.check_platform () != Platform.WIN32) then
      Thread.id (Thread.self ())
    else
      0 in
  let s = "(PID "^(string_of_int pid)^", TID "^(string_of_int tid)^") "^str in
  let _ = prerr_string (s^"\n") in
  flush Pervasives.stderr;;*)

let keyword_table = Hashtbl.create 200
        let _ =
          List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
                    [ (* Common tokens *)
		      "IP", IP;
                      "Port", PORT;
		      "IFID", IFID;
		      "NETMASK", NETMASK;
		      "NONE", NONE;
		      "SOME", SOME;
		      (* LIB tokens *)
                      "accept", ACCEPT;
		      "bind", BIND;
		      "close", CLOSE;
		      "connect", CONNECT;
		      "disconnect", DISCONNECT;
		      "dup", DUP;
		      "dupfd", DUPFD;
		      "getfileflags", GETFILEFLAGS;
		      "setfileflags", SETFILEFLAGS;
		      "getifaddrs", GETIFADDRS;
		      "getsockname", GETSOCKNAME;
		      "getpeername", GETPEERNAME;
		      "getsockbopt", GETSOCKBOPT;
		      "getsocknopt", GETSOCKNOPT;
		      "getsocktopt", GETSOCKTOPT;
		      "setsockbopt", SETSOCKBOPT;
		      "setsocknopt", SETSOCKNOPT;
		      "setsocktopt", SETSOCKTOPT;
		      "listen", LISTEN;
		      "pselect", PSELECT;
		      "recv", RECV;
		      "send", SEND;
		      "shutdown", SHUTDOWN;
		      "sockatmark", SOCKATMARK;
		      "socket", SOCKET;
		      "getsockerr", GETSOCKERR;
		      "getsocklistening", GETSOCKLISTENING;
		      "Lh_call", LHCALL;
		      "Lh_return", LHRETURN;
		      "OK", LHOK;
		      "FAIL", LHFAIL;
		      "TID", TID;
		      "FD", FD;
		      (* LIB flags *)
		      "O_NONBLOCK", TO_NONBLOCK;
		      "O_ASYNC", TO_ASYNC;
		      "SO_BSDCOMPAT", TSO_BSDCOMPAT;
		      "SO_REUSEADDR", TSO_REUSEADDR;
		      "SO_KEEPALIVE", TSO_KEEPALIVE;
		      "SO_OOBINLINE", TSO_OOBINLINE;
		      "SO_DONTROUTE", TSO_DONTROUTE;
		      "SO_SNDBUF", TSO_SNDBUF;
		      "SO_RCVBUF", TSO_RCVBUF;
		      "SO_SNDLOWAT", TSO_SNDLOWAT;
		      "SO_RCVLOWAT", TSO_RCVLOWAT;
		      "SO_LINGER", TSO_LINGER;
		      "SO_SNDTIMEO", TSO_SNDTIMEO;
		      "SO_RCVTIMEO", TSO_RCVTIMEO;
		      "SO_BROADCAST", TSO_BROADCAST;
		      "MSG_PEEK", TMSG_PEEK;
		      "MSG_OOB", TMSG_OOB;
		      "MSG_WAITALL", TMSG_WAITALL;
		      "MSG_DONTWAIT", TMSG_DONTWAIT;
		      "SIGABRT", TSIGABRT;
		      "SIGALRM", TSIGALRM;
		      "SIGBUS", TSIGBUS;
		      "SIGCHLD", TSIGCHLD;
		      "SIGCONT", TSIGCONT;
		      "SIGFPE", TSIGFPE;
		      "SIGHUP", TSIGHUP;
		      "SIGILL", TSIGILL;
		      "SIGINT", TSIGINT;
		      "SIGKILL", TSIGKILL;
		      "SIGPIPE", TSIGPIPE;
		      "SIGQUIT", TSIGQUIT;
		      "SIGSEGV", TSIGSEGV;
		      "SIGSTOP", TSIGSTOP;
		      "SIGTERM", TSIGTERM;
		      "SIGTSTP", TSIGTSTP;
		      "SIGTTIN", TSIGTTIN;
		      "SIGTTOU", TSIGTTOU;
		      "SIGUSR1", TSIGUSR1;
		      "SIGUSR2", TSIGUSR2;
		      "SIGPOLL", TSIGPOLL;
		      "SIGPROF", TSIGPROF;
		      "SIGSYS", TSIGSYS;
		      "SIGTRAP", TSIGTRAP;
		      "SIGURG", TSIGURG;
		      "SIGVTALRM", TSIGVTALRM;
		      "SIGXCPU", TSIGXCPU;
		      "SIGXFSZ", TSIGXFSZ;
		      (* Network datagram tokens *)
		      "is1", IS1;
		      "is2", IS2;
		      "is3", IS3;
		      "is4", IS4;
		      "ps1", PS1;
		      "ps2", PS2;
		      "ps3", PS3;
		      "ps4", PS4;
		      "seq", SEQNO;
		      "ack", ACKNO;
		      "URG", URG;
		      "ACK", ACK;
		      "PSH", PSH;
		      "RST", RST;
		      "SYN", SYN;
		      "FIN", FIN;
		      "win", WIN;
		      "ws", WS;
		      "urp", URP;
		      "mss", MSS;
		      "ts", TS;
		      "data", DATA;
		      "ICMP_UNREACH", ICMP_UNREACH;
		      "ICMP_PARAMPROB", ICMP_PARAMPROB;
		      "ICMP_SOURCE_QUENCH", ICMP_SOURCE_QUENCH;
		      "ICMP_TIME_EXCEEDED", ICMP_TIME_EXCEEDED;
		      "HOST", ICMP_HOST;
		      "PORT", ICMP_PORT;
		      "NET", ICMP_NET;
		      "SRCFAIL", ICMP_SRCFAIL;
		      "NET_UNKNOWN", ICMP_NET_UNKNOWN;
		      "HOST_UNKNOWN", ICMP_HOST_UNKNOWN;
		      "ISOLATED", ICMP_ISOLATED;
		      "TOSNET", ICMP_TOSNET;
		      "TOSHOST", ICMP_TOSHOST;
		      "PREC_VIOLATION", ICMP_PREC_VIOLATION;
		      "PREC_CUTOFF", ICMP_PREC_CUTOFF;
		      "NEEDFRAG", ICMP_NEEDFRAG;
		      "PROTOCOL", ICMP_PROTOCOL;
		      "NET_PROHIB", ICMP_NET_PROHIB;
		      "HOST_PROHIB", ICMP_HOST_PROHIB;
		      "FILTER_PROHIB", ICMP_FILTER_PROHIB;
		      "BADHDR", ICMP_BADHDR;
		      "NEEDOPT", ICMP_NEEDOPT;
		      "QUENCH", ICMP_QUENCH;
		      "INTRANS", ICMP_INTRANS;
		      "REASS", ICMP_REASS;
		      "PROTO_TCP", PROTO_TCP;
		      "PROTO_UDP", PROTO_UDP;
		      "proto", PROTO;
		      "TCP", TCP;
		      "UDP", UDP;
		      "ICMP", ICMP;
                      "n2w", WORD16;
		      "ts_seq", TSSEQ;
		      "tcp_seq_local", SEQLOCAL;
		      "tcp_seq_foreign", SEQFOREIGN;
		      "Lh_senddatagram", LHSEND;
		      "Lh_loopdatagram", LHLOOP;
		      "Lh_recvdatagram", LHRECV;
		      "t", TYPE;  (* icmp type *)
		      "CHR", BYTE;
		      (* TCP control block traces *)
		      "Lh_trace", TRACE;
		      "SID", SID;
		      "snd_una", T_SND_UNA;
		      "snd_max", T_SND_MAX;
		      "snd_nxt", T_SND_NXT;
		      "snd_wl1", T_SND_WL1;
		      "snd_wl2", T_SND_WL2;
		      "iss", T_ISS;
		      "snd_wnd", T_SND_WND;
		      "snd_cwnd", T_SND_CWND;
		      "snd_ssthresh", T_SND_SSTHRESH;
		      "rcv_wnd", T_RCV_WND;
		      "rcv_nxt", T_RCV_NXT;
		      "rcv_up", T_RCV_UP;
		      "irs", T_IRS;
		      "rcv_adv", T_RCV_ADV;
		      "snd_recover", T_SND_RECOVER;
		      "t_maxseg", T_T_MAXSEG;
		      "t_dupacks", T_T_DUPACKS;
		      "t_rttseg", T_T_RTTSEG;
		      "snd_scale", T_SND_SCALE;
		      "rcv_scale", T_RCV_SCALE;
		      "ts_recent", T_TS_RECENT;
		      "last_ack_sent", T_LAST_ACK_SENT;
		      "Timed", T_TIMED;
  	              "TimeWindowClosed", TIMEWINDOWCLOSED;
		      "TimeWindow", TIMEWINDOW;
		      "never_timer", NEVERTIMER;
		      (* TCP states (for tcpcb parsing) *)
		      "CLOSED", T_CLOSED;
		      "LISTEN", T_LISTEN;
		      "SYN_SENT", T_SYN_SENT;
		      "SYN_RECEIVED", T_SYN_RECEIVED;
		      "ESTABLISHED", T_ESTABLISHED;
		      "CLOSE_WAIT", T_CLOSE_WAIT;
		      "FIN_WAIT_1", T_FIN_WAIT_1;
		      "CLOSING", T_CLOSING;
		      "LAST_ACK", T_LAST_ACK;
		      "FIN_WAIT_2", T_FIN_WAIT_2;
		      "TIME_WAIT", T_TIME_WAIT;
		      (* TCP Trace actions *)
		      "TA_OUTPUT", T_TA_OUTPUT;
		      "TA_INPUT", T_TA_INPUT;
		      "TA_USER", T_TA_USER;
		      "TA_RESPOND", T_TA_RESPOND;
		      "TA_DROP", T_TA_DROP;
		      (* HOL epsilon transitions *)
		      "Lh_epsilon", T_LH_EPSILON;
		      "duration", T_DURATION;
                      "abstime", T_ABSTIME;
                      (* HOL Unix errors *)
                      "E2BIG", T_ERR_E2BIG;
                      "EACCES", T_ERR_EACCES;
                      "EADDRINUSE", T_ERR_EADDRINUSE;
                      "EADDRNOTAVAIL", T_ERR_EADDRNOTAVAIL;
                      "EAFNOSUPPORT", T_ERR_EAFNOSUPPORT;
                      "EAGAIN", T_ERR_EAGAIN;
                      "EWOULDBLOCK", T_ERR_EWOULDBLOCK;
                      "EALREADY", T_ERR_EALREADY;
                      "EBADF", T_ERR_EBADF;
                      "EBADMSG", T_ERR_EBADMSG;
                      "EBUSY", T_ERR_EBUSY;
                      "ECANCELED", T_ERR_ECANCELED;
                      "ECHILD", T_ERR_ECHILD;
                      "ECONNABORTED", T_ERR_ECONNABORTED;
                      "ECONNREFUSED", T_ERR_ECONNREFUSED;
                      "ECONNRESET", T_ERR_ECONNRESET;
                      "EDEADLK", T_ERR_EDEADLK;
                      "EDESTADDRREQ", T_ERR_EDESTADDRREQ;
                      "EDOM", T_ERR_EDOM;
                      "EDQUOT", T_ERR_EDQUOT;
                      "EEXIST", T_ERR_EEXIST;
                      "EFAULT", T_ERR_EFAULT;
                      "EFBIG", T_ERR_EFBIG;
                      "EHOSTUNREACH", T_ERR_EHOSTUNREACH;
                      "EIDRM", T_ERR_EIDRM;
                      "EILSEQ", T_ERR_EILSEQ;
                      "EINPROGRESS", T_ERR_EINPROGRESS;
                      "EINTR", T_ERR_EINTR;
                      "EINVAL", T_ERR_EINVAL;
                      "EIO", T_ERR_EIO;
                      "EISCONN", T_ERR_EISCONN;
                      "EISDIR", T_ERR_EISDIR;
                      "ELOOP", T_ERR_ELOOP;
                      "EMFILE", T_ERR_EMFILE;
                      "EMLINK", T_ERR_EMLINK;
                      "EMSGSIZE", T_ERR_EMSGSIZE;
                      "EMULTIHOP", T_ERR_EMULTIHOP;
                      "ENAMETOOLONG", T_ERR_ENAMETOOLONG;
                      "ENETDOWN", T_ERR_ENETDOWN;
                      "ENETRESET", T_ERR_ENETRESET;
                      "ENETUNREACH", T_ERR_ENETUNREACH;
                      "ENFILE", T_ERR_ENFILE;
                      "ENOBUFS", T_ERR_ENOBUFS;
                      "ENODATA", T_ERR_ENODATA;
                      "ENODEV", T_ERR_ENODEV;
                      "ENOENT", T_ERR_ENOENT;
                      "ENOEXEC", T_ERR_ENOEXEC;
                      "ENOLCK", T_ERR_ENOLCK;
                      "ENOLINK", T_ERR_ENOLINK;
                      "ENOMEM", T_ERR_ENOMEM;
                      "ENOMSG", T_ERR_ENOMSG;
                      "ENOPROTOOPT", T_ERR_ENOPROTOOPT;
                      "ENOSPC", T_ERR_ENOSPC;
                      "ENOSR", T_ERR_ENOSR;
                      "ENOSTR", T_ERR_ENOSTR;
                      "ENOSYS", T_ERR_ENOSYS;
                      "ENOTCONN", T_ERR_ENOTCONN;
                      "ENOTDIR", T_ERR_ENOTDIR;
                      "ENOTEMPTY", T_ERR_ENOTEMPTY;
                      "ENOTSOCK", T_ERR_ENOTSOCK;
                      "ENOTSUP", T_ERR_ENOTSUP;
                      "ENOTTY", T_ERR_ENOTTY;
                      "ENXIO", T_ERR_ENXIO;
                      "EOPNOTSUPP", T_ERR_EOPNOTSUPP;
                      "EOVERFLOW", T_ERR_EOVERFLOW;
                      "EPERM", T_ERR_EPERM;
                      "EPIPE", T_ERR_EPIPE;
                      "EPROTO", T_ERR_EPROTO;
                      "EPROTONOSUPPORT", T_ERR_EPROTONOSUPPORT;
                      "EPROTOTYPE", T_ERR_EPROTOTYPE;
                      "ERANGE", T_ERR_ERANGE;
                      "EROFS", T_ERR_EROFS;
                      "ESPIPE", T_ERR_ESPIPE;
                      "ESRCH", T_ERR_ESRCH;
                      "ESTALE", T_ERR_ESTALE;
                      "ETIME", T_ERR_ETIME;
                      "ETIMEDOUT", T_ERR_ETIMEDOUT;
                      "ETXTBSY", T_ERR_ETXTBSY;
                      "EXDEV", T_ERR_EXDEV;
		      "ESHUTDOWN", T_ERR_ESHUTDOWN;
		      "EHOSTDOWN", T_ERR_EHOSTDOWN;
                      "EUNKNOWN_UNIX_ERROR", T_ERR_EUNKNOWN_UNIX_ERROR;
		      "SOCK_DGRAM", SOCK_DGRAM;
		      "SOCK_STREAM", SOCK_STREAM;
		      (* Spec3 labels *)
		      "Ln1_host", LN1_HOST;
		      "Ln1_epsilon",LN1_EPSILON;
		    ]
}

rule token = parse
  [' ' '\t' '\n']  { token lexbuf }    (* skip blanks *)
| '('         { debug ("LPAREN: "^(Lexing.lexeme lexbuf)); LPAREN }
| ')'         { debug ("RPAREN: "^(Lexing.lexeme lexbuf)); RPAREN }
| "()"        { debug ("UNIT: "^(Lexing.lexeme lexbuf)); UNIT }
| "<|"        { debug ("RECSTART: "^(Lexing.lexeme lexbuf)); RECSTART }
| "|>"        { debug ("RECEND: "^(Lexing.lexeme lexbuf)); RECEND }
| ','         { debug ("COMMA: "^(Lexing.lexeme lexbuf)); COMMA }
| '.'         { debug ("DOT: "^(Lexing.lexeme lexbuf)); DOT }
| ';'         { debug ("SC: "^(Lexing.lexeme lexbuf)); SC }
| ":="        { debug ("ASSIGN: "^(Lexing.lexeme lexbuf)); ASSIGN }
| "-"         { debug ("MINUS: "^(Lexing.lexeme lexbuf)); MINUS }
| "~"         { debug ("MINUS: "^(Lexing.lexeme lexbuf)); MINUS }
| '#'         { debug ("HASH: "^(Lexing.lexeme lexbuf)); HASH }
| '['         { debug ("LSQBRKT: "^(Lexing.lexeme lexbuf)); LSQBRKT }
| ']'         { debug ("RSQBRKT: "^(Lexing.lexeme lexbuf)); RSQBRKT }
| "T"         { debug ("TRUE: "^(Lexing.lexeme lexbuf)); TRUE }
| "F"         { debug ("FALSE: "^(Lexing.lexeme lexbuf)); FALSE }
| eof         { debug ("EOF "); raise Eof }
| "(**"
    { debug ("SCOMMENTSTART: "^(Lexing.lexeme lexbuf)); SCOMMENTSTART }
| "**)"
    { debug ("SCOMMENTEND: "^(Lexing.lexeme lexbuf)); SCOMMENTEND }
| "(*"[^'*']([^'*']|('*'[^')']))*"*)"
    { debug ("COMMENT: "^(Lexing.lexeme lexbuf)); COMMENT(Lexing.lexeme lexbuf) }
| ['0'-'9']+
    { debug ("INT: "^(Lexing.lexeme lexbuf)); INT(Int64.of_string(Lexing.lexeme lexbuf)) }
| '"'([^'\\' '"']|('\\'_))*'"'
	   { let str = Lexing.lexeme lexbuf in
	     let len = String.length str in
	     let rem_quotes_str = String.sub str 1 (len-2) in
	     debug ("STRING: "^rem_quotes_str); STRING(rem_quotes_str) }
| "initial_host"[^'\n']* { debug("COMMENT: "^(Lexing.lexeme lexbuf)); COMMENT(Lexing.lexeme lexbuf) }
| "net_initial_host"[^'\n']* { debug("COMMENT: "^(Lexing.lexeme lexbuf)); COMMENT(Lexing.lexeme lexbuf) }
| ['A'-'Z' 'a'-'z']['A'-'Z' 'a'-'z' '0'-'9' '_']*
      { let id = Lexing.lexeme lexbuf in
        try
	  debug ("HASH_TABLE: "^(Lexing.lexeme lexbuf));
	  Hashtbl.find keyword_table id
	with Not_found ->
	  debug ("**NOT FOUND: "^(Lexing.lexeme lexbuf)^ "***");
	  IDENT id }
| _  { if String.length(Lexing.lexeme lexbuf) = 0 then
         raise Eof
       else
         (debug ("**LEXER ERROR: ["^(Lexing.lexeme lexbuf)^ "] " ^
		 (string_of_int (String.length(Lexing.lexeme lexbuf)))^ "***\n");

	  (*debug ("lex_buffer = " ^ lexbuf.lex_buffer);
	  debug ("lex_buffer_len = " ^ (string_of_int lexbuf.lex_buffer_len));
	  debug ("lex_abs_pos = " ^ (string_of_int lexbuf.lex_abs_pos));
	  debug ("lex_start_pos = " ^ (string_of_int lexbuf.lex_start_pos));
	  debug ("lex_curr_pos = " ^ (string_of_int lexbuf.lex_curr_pos));
	  debug ("lex_last_pos = " ^ (string_of_int lexbuf.lex_last_pos));
	  debug ("lex_last_action = " ^ (string_of_int lexbuf.lex_last_action));
	  debug ("lex_eof_reach = " ^ (if lexbuf.lex_eof_reached then "true" else "false"));

	  lexbuf.refill_buff lexbuf;
	  debug ("\n\n");
	  debug ("lex_buffer = " ^ lexbuf.lex_buffer);
	  debug ("lex_buffer_len = " ^ (string_of_int lexbuf.lex_buffer_len));
	  debug ("lex_abs_pos = " ^ (string_of_int lexbuf.lex_abs_pos));
	  debug ("lex_start_pos = " ^ (string_of_int lexbuf.lex_start_pos));
	  debug ("lex_curr_pos = " ^ (string_of_int lexbuf.lex_curr_pos));
	  debug ("lex_last_pos = " ^ (string_of_int lexbuf.lex_last_pos));
	  debug ("lex_last_action = " ^ (string_of_int lexbuf.lex_last_action));
	  debug ("lex_eof_reach = " ^ (if lexbuf.lex_eof_reached then "true" else "false"));*)

	  IDENT (Lexing.lexeme lexbuf)) }
