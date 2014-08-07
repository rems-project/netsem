open Nettypes;;

type tcpstate =
    TCPCB_CLOSED
  | TCPCB_LISTEN
  | TCPCB_SYN_SENT
  | TCPCB_SYN_RCVD
  | TCPCB_ESTABLISHED
  | TCPCB_CLOSE_WAIT
  | TCPCB_FIN_WAIT_1
  | TCPCB_CLOSING
  | TCPCB_LAST_ACK
  | TCPCB_FIN_WAIT_2
  | TCPCB_TIME_WAIT
;;

type tcpaction =
    TA_OUTPUT
  | TA_INPUT
  | TA_USER
  | TA_RESPOND
  | TA_DROP

type tracesid = uint;;

type traceaddr =
    TRACEADDR of (ip option * port option * ip option * port option) option
;;

type timers =
    NEVER_TIMER;;

type tswindow =
    TimeWindowClosed
  | TimeWindow of uint * timers;;

type tcpcb = {
    snd_una : uint;
    snd_max : uint;
    snd_nxt : uint;
    snd_wl1 : uint;
    snd_wl2 : uint;
    iss     : uint;
    snd_wnd : uint;
    snd_cwnd     : uint;
    snd_ssthresh : uint;
    rcv_wnd      : uint;
    rcv_nxt      : uint;
    rcv_up       : uint;
    irs          : uint;
    rcv_adv      : uint;
    snd_recover  : uint;
    t_maxseg     : uint;
    t_dupacks    : uint;
    t_rttseg     : (uint * uint) option;
    snd_scale    : uint;
    rcv_scale    : uint;
    ts_recent    : tswindow;
    last_ack_sent : uint;
  } ;;

