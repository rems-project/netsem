open Nettypes;;
open Netconv;;
open Tcpcbtypes;;
exception ParseWarning of string;;
exception ParseError of string;;

type tcpcb_partial =
    TCPCB_SND_UNA of uint
  | TCPCB_SND_MAX of uint
  | TCPCB_SND_NXT of uint
  | TCPCB_SND_WL1 of uint
  | TCPCB_SND_WL2 of uint
  | TCPCB_ISS of uint
  | TCPCB_SND_WND of uint
  | TCPCB_SND_CWND of uint
  | TCPCB_SND_SSTHRESH of uint
  | TCPCB_RCV_WND of uint
  | TCPCB_RCV_NXT of uint
  | TCPCB_RCV_UP of uint
  | TCPCB_IRS of uint
  | TCPCB_RCV_ADV of uint
  | TCPCB_SND_RECOVER of uint
  | TCPCB_T_MAXSEG of uint
  | TCPCB_T_DUPACKS of uint
  | TCPCB_T_RTTSEG of (uint * uint) option
  | TCPCB_SND_SCALE of uint
  | TCPCB_RCV_SCALE of uint
  | TCPCB_TS_RECENT of tswindow
  | TCPCB_LAST_ACK_SENT of uint
;;

type tcpcb_status = {
    snd_una_up : bool;
    snd_max_up : bool;
    snd_nxt_up : bool;
    snd_wl1_up : bool;
    snd_wl2_up : bool;
    iss_up     : bool;
    snd_wnd_up : bool;
    snd_cwnd_up     : bool;
    snd_ssthresh_up : bool;
    rcv_wnd_up      : bool;
    rcv_nxt_up      : bool;
    rcv_up_up       : bool;
    irs_up          : bool;
    rcv_adv_up      : bool;
    snd_recover_up  : bool;
    t_maxseg_up     : bool;
    t_dupacks_up    : bool;
    t_rttseg_up      : bool;
    snd_scale_up    : bool;
    rcv_scale_up    : bool;
    ts_recent_up    : bool;
    last_ack_sent_up : bool;
  } ;;

val clear_tcpcb_status : tcpcb_status

val clear_tcpcb : tcpcb

val chk_missing_tcpcb : tcpcb_status -> unit

val update_tcpcb : tcpcb_partial -> tcpcb_status -> tcpcb -> (tcpcb_status * tcpcb)
