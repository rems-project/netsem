open Printf;;
open Unix;;

open Nettypes;;
open Tcpcbtypes;;
(*open Parserlib;;*)
(*open Render;;*)
(*open ThreadUnix;;*)
(*open Sock;;*)

let taddr_render taddr =
  match taddr with
    TRACEADDR(None) -> "NONE"
  | TRACEADDR(Some(is1,ps1,is2,ps2)) ->
      sprintf "SOME(%s, %s, %s, %s)" (render_ip_option is1)
	(render_port_option ps1) (render_ip_option is2)
	(render_port_option ps2);;

let tsid_render tsid =
  sprintf "SID %s" (Int64.to_string tsid);;

let tstate_render tstate =
  match tstate with
    TCPCB_CLOSED -> "CLOSED"
  | TCPCB_LISTEN -> "LISTEN"
  | TCPCB_SYN_SENT -> "SYN_SENT"
  | TCPCB_SYN_RCVD -> "SYN_RECEIVED"
  | TCPCB_ESTABLISHED -> "ESTABLISHED"
  | TCPCB_CLOSE_WAIT -> "CLOSE_WAIT"
  | TCPCB_FIN_WAIT_1 -> "FIN_WAIT_1"
  | TCPCB_CLOSING -> "CLOSING"
  | TCPCB_LAST_ACK -> "LAST_ACK"
  | TCPCB_FIN_WAIT_2 -> "FIN_WAIT_2"
  | TCPCB_TIME_WAIT -> "TIME_WAIT";;

let tsact_render tact =
  match tact with
    TA_OUTPUT -> "TA_OUTPUT"
  | TA_INPUT -> "TA_INPUT"
  | TA_USER -> "TA_USER"
  | TA_RESPOND -> "TA_RESPOND"
  | TA_DROP -> "TA_DROP"

let render_ts_recent tsr =
  match tsr with
    TimeWindowClosed -> "TimeWindowClosed"
  | TimeWindow(x, NEVER_TIMER) ->
      sprintf "TimeWindow(ts_seq(n2w %s), never_timer)"
	(Int64.to_string x);;

let render_rttseq rttseq =
  match rttseq with
    None -> "NONE"
  | Some(x,y) -> sprintf "SOME(ts_seq(n2w %s), tcp_seq_local(n2w %s))"
	(Int64.to_string x) (Int64.to_string y);;

let tcpcb_render tcpcb =
  let s1 = "<|\n" in
  let s2 = s1^(sprintf "   snd_una := %s;\n"
		 (render_tcp_seq_local tcpcb.snd_una)) in
  let s3 = s2^(sprintf "   snd_max := %s;\n"
		 (render_tcp_seq_local tcpcb.snd_max)) in
  let s4 = s3^(sprintf "   snd_nxt := %s;\n"
		 (render_tcp_seq_local tcpcb.snd_nxt)) in
  let s6 = s4^(sprintf "   snd_wl1 := %s;\n"
		 (render_tcp_seq_foreign tcpcb.snd_wl1)) in
  let s7 = s6^(sprintf "   snd_wl2 := %s;\n"
		 (render_tcp_seq_local tcpcb.snd_wl2)) in
  let s8 = s7^(sprintf "   iss := %s;\n"
		 (render_tcp_seq_local tcpcb.iss)) in
  let s9 = s8^(sprintf "   snd_wnd := %s;\n"
		 (Int64.to_string tcpcb.snd_wnd)) in
  let s10 = s9^(sprintf "   snd_cwnd := %s;\n"
		  (Int64.to_string tcpcb.snd_cwnd)) in
  let s11 = s10^(sprintf "   snd_ssthresh := %s;\n"
		   (Int64.to_string tcpcb.snd_ssthresh)) in
  let s12 = s11^(sprintf "   rcv_wnd := %s;\n"
		   (Int64.to_string tcpcb.rcv_wnd)) in
  let s13 = s12^(sprintf "   rcv_nxt := %s;\n"
		   (render_tcp_seq_foreign tcpcb.rcv_nxt)) in
  let s14 = s13^(sprintf "   rcv_up := %s;\n"
		   (render_tcp_seq_foreign tcpcb.rcv_up)) in
  let s15 = s14^(sprintf "   irs := %s;\n"
		   (render_tcp_seq_foreign tcpcb.irs)) in
  let s16 = s15^(sprintf "   rcv_adv := %s;\n"
		   (render_tcp_seq_foreign tcpcb.rcv_adv)) in
  let s17 = s16^(sprintf "   snd_recover := %s;\n"
		   (render_tcp_seq_local tcpcb.snd_recover)) in
  let s18 = s17^(sprintf "   t_maxseg := %s;\n"
		   (Int64.to_string tcpcb.t_maxseg)) in
  let s19 = s18^(sprintf "   t_dupacks := %s;\n"
		   (Int64.to_string tcpcb.t_dupacks)) in
  let s20 = s19^(sprintf "   t_rttseg := %s;\n"
		   (render_rttseq tcpcb.t_rttseg)) in
  let s21 = s20^(sprintf "   snd_scale := %s;\n"
		   (Int64.to_string tcpcb.snd_scale)) in
  let s22 = s21^(sprintf "   rcv_scale := %s;\n"
		   (Int64.to_string tcpcb.rcv_scale)) in
  let s23 = s22^(sprintf "   ts_recent := %s;\n"
		   (render_ts_recent tcpcb.ts_recent)) in
  let s24 = s23^(sprintf "   last_ack_sent := %s\n"
		   (render_tcp_seq_foreign tcpcb.last_ack_sent)) in
  let s25 = s24^"  |>" in s25;;


let tcpcb_trace_to_string tact tsid taddr tstate tcpcb =
  sprintf "Lh_trace(%s, %s, %s,\n  %s,\n %s )"
    (tsact_render tact) (tsid_render tsid) (taddr_render taddr) (tstate_render tstate) (tcpcb_render tcpcb);;

let tcpcb_trace_render tact tsid taddr tstate tcpcb =
  tcpcb_trace_to_string tact tsid taddr tstate tcpcb ^ ";\n";;


(*
let tcpcb_trace_render_to_socket sd x =
  let s =
    match x with
      TCPTRACE(tact, tsid, taddr, tstate, tcpcb) ->
	tcpcb_trace_render tact tsid taddr tstate tcpcb
    | _ -> raise(Fatal("Not a TCPTRACE")) in
  Sock.write sd s;;
*)
