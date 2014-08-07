open Nettypes;;
(*open Netconv;;*)
open Tcpcbtypes;;
exception ParseWarning of string;;
exception ParseError of string;;

let assertw x y = if x then (raise(ParseWarning(y));()) else ();;
let asserte x y = if x then (raise(ParseError(y));()) else ();;

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

let clear_tcpcb_status =
  { snd_una_up=false; snd_max_up=false; snd_nxt_up=false;
    snd_wl1_up=false; snd_wl2_up=false;
    iss_up=false; snd_wnd_up=false; snd_cwnd_up=false;
    snd_ssthresh_up=false; rcv_wnd_up=false; rcv_nxt_up=false;
    rcv_up_up=false; irs_up=false; rcv_adv_up=false;
    snd_recover_up=false; t_maxseg_up=false; t_dupacks_up=false;
    t_rttseg_up=false; snd_scale_up=false; rcv_scale_up=false;
    ts_recent_up=false; last_ack_sent_up=false;
  };;

let clear_tcpcb = {
    snd_una = uint 0; snd_max = uint 0; snd_nxt = uint 0;
    snd_wl1 = uint 0; snd_wl2 = uint 0;
    iss = uint 0; snd_wnd = uint 0; snd_cwnd = uint 0;
    snd_ssthresh = uint 0; rcv_wnd = uint 0; rcv_nxt = uint 0;
    rcv_up = uint 0; irs = uint 0; rcv_adv = uint 0;
    snd_recover = uint 0; t_maxseg = uint 0;
    t_dupacks = uint 0; t_rttseg = None; snd_scale = uint 0;
    rcv_scale = uint 0; ts_recent = TimeWindowClosed;
    last_ack_sent = uint 0;
  } ;;

let chk_missing_tcpcb x =
  asserte (not x.snd_una_up) "No tcpcb.snd_una specified";
  asserte (not x.snd_max_up) "No tcpcb.snd_max specified";
  asserte (not x.snd_nxt_up) "No tcpcb.snd_nxt specified";
  asserte (not x.snd_wl1_up) "No tcpcb.snd_wl1 specified";
  asserte (not x.snd_wl2_up) "No tcpcb.snd_wl2 specified";
  asserte (not x.iss_up) "No tcpcb.iss specified";
  asserte (not x.snd_wnd_up) "No tcpcb.snd_wnd specified";
  asserte (not x.snd_cwnd_up) "No tcpcb.snd_cwnd specified";
  asserte (not x.snd_ssthresh_up) "No tcpcb.snd_ssthresh specified";
  asserte (not x.rcv_wnd_up) "No tcpcb.rcv_wnd specified";
  asserte (not x.rcv_nxt_up) "No tcpcb.rcv_nxt specified";
  asserte (not x.rcv_up_up) "No tcpcb.rcv_up specified";
  asserte (not x.irs_up) "No tcpcb.irs specified";
  asserte (not x.rcv_adv_up) "No tcpcb.rcv_adv specified";
  asserte (not x.snd_recover_up) "No tcpcb.snd_recover specified";
  asserte (not x.t_maxseg_up) "No tcpcb.t_maxseg specified";
  asserte (not x.t_dupacks_up) "No tcpcb.t_dupacks specified";
  asserte (not x.t_rttseg_up) "No tcpcb.t_rttseg specified";
  asserte (not x.snd_scale_up) "No tcpcb.snd_scale specified";
  asserte (not x.rcv_scale_up) "No tcpcb.rcv_scale specified";
  asserte (not x.ts_recent_up) "No tcpcb.ts_recent specified";
  asserte (not x.last_ack_sent_up) "No tcpcb.last_ack_sent specified";;


let update_tcpcb update status oldrec =
  match update with
    TCPCB_SND_UNA(x) -> (assertw status.snd_una_up "Duplicate snd_una fields in record. Using most recent.";
			 { status with snd_una_up = true },
			 { oldrec with snd_una = x })
  | TCPCB_SND_MAX(x) -> (assertw status.snd_max_up "Duplicate snd_max fields in record. Using most recent.";
			 { status with snd_max_up = true },
			 { oldrec with snd_max = x })
  | TCPCB_SND_NXT(x) -> (assertw status.snd_nxt_up "Duplicate snd_nxt fields in record. Using most recent.";
			 { status with snd_nxt_up = true },
			 { oldrec with snd_nxt = x })
  | TCPCB_SND_WL1(x) -> (assertw status.snd_wl1_up "Duplicate snd_wl1 fields in record. Using most recent.";
			 { status with snd_wl1_up = true },
			 { oldrec with snd_wl1 = x })
  | TCPCB_SND_WL2(x) -> (assertw status.snd_wl2_up "Duplicate snd_wl2 fields in record. Using most recent.";
			 { status with snd_wl2_up = true },
			 { oldrec with snd_wl2 = x })
  | TCPCB_ISS(x) -> (assertw status.iss_up "Duplicate iss fields in record. Using most recent.";
			 { status with iss_up = true },
			 { oldrec with iss = x })
  | TCPCB_SND_WND(x) -> (assertw status.snd_wnd_up "Duplicate snd_wnd fields in record. Using most recent.";
			 { status with snd_wnd_up = true },
			 { oldrec with snd_wnd = x })
  | TCPCB_SND_CWND(x) -> (assertw status.snd_cwnd_up "Duplicate snd_cwnd fields in record. Using most recent.";
			 { status with snd_cwnd_up = true },
			 { oldrec with snd_cwnd = x })
  | TCPCB_SND_SSTHRESH(x) -> (assertw status.snd_ssthresh_up "Duplicate snd_ssthresh fields in record. Using most recent.";
			 { status with snd_ssthresh_up = true },
			 { oldrec with snd_ssthresh = x })
  | TCPCB_RCV_WND(x) -> (assertw status.rcv_wnd_up "Duplicate rcv_wnd fields in record. Using most recent.";
			 { status with rcv_wnd_up = true },
			 { oldrec with rcv_wnd = x })
  | TCPCB_RCV_NXT(x) -> (assertw status.rcv_nxt_up "Duplicate rcv_next fields in record. Using most recent.";
			 { status with rcv_nxt_up = true },
			 { oldrec with rcv_nxt = x })
  | TCPCB_RCV_UP(x) -> (assertw status.rcv_up_up "Duplicate rcv_up fields in record. Using most recent.";
			 { status with rcv_up_up = true },
			 { oldrec with rcv_up = x })
  | TCPCB_IRS(x) -> (assertw status.irs_up "Duplicate irs fields in record. Using most recent.";
			 { status with irs_up = true },
			 { oldrec with irs = x })
  | TCPCB_RCV_ADV(x) -> (assertw status.rcv_adv_up "Duplicate rcv_adv fields in record. Using most recent.";
			 { status with rcv_adv_up = true },
			 { oldrec with rcv_adv = x })
  | TCPCB_SND_RECOVER(x) -> (assertw status.snd_recover_up "Duplicate snd_recover fields in record. Using most recent.";
			 { status with snd_recover_up = true },
			 { oldrec with snd_recover = x })
  | TCPCB_T_MAXSEG(x) -> (assertw status.t_maxseg_up "Duplicate t_maxseg fields in record. Using most recent.";
			 { status with t_maxseg_up = true },
			 { oldrec with t_maxseg = x })
  | TCPCB_T_DUPACKS(x) -> (assertw status.t_dupacks_up "Duplicate t_dupacks fields in record. Using most recent.";
			 { status with t_dupacks_up = true },
			 { oldrec with t_dupacks = x })
  | TCPCB_T_RTTSEG(x) -> (assertw status.t_rttseg_up "Duplicate t_rttseg fields in record. Using most recent.";
			 { status with t_rttseg_up = true },
			 { oldrec with t_rttseg = x })
  | TCPCB_SND_SCALE(x) -> (assertw status.snd_scale_up "Duplicate snd_scale fields in record. Using most recent.";
			 { status with snd_scale_up = true },
			 { oldrec with snd_scale = x })
  | TCPCB_RCV_SCALE(x) -> (assertw status.rcv_scale_up "Duplicate rcv_scale fields in record. Using most recent.";
			 { status with rcv_scale_up = true },
			 { oldrec with rcv_scale = x })
  | TCPCB_TS_RECENT(x) -> (assertw status.ts_recent_up "Duplicate ts_recent fields in record. Using most recent.";
			 { status with ts_recent_up = true },
			 { oldrec with ts_recent = x })
  | TCPCB_LAST_ACK_SENT(x) -> (assertw status.last_ack_sent_up "Duplicate last_ack_sent fields in record. Using most recent.";
			 { status with last_ack_sent_up = true },
			 { oldrec with last_ack_sent = x })
;;













