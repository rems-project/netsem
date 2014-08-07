open Printf;;
open Unix;;

open Nettypes;;
(*open Netconv;;*)
open Parserlib;;
(*open Holparselib;;*)
(*open Libcalls;;*)
(*open Render;;*)
open Holrender;;
open Librender;;
open Tcpcbrender;;
open Holtypes;;

let render_timestamp time offset =
  let real_time = time +. offset in
  let t1 = real_time /. (uint 1000000) in
  let t2 = real_time % (uint 1000000) in
  sprintf "%s.%s" (Int64.to_string t1) (lpad_numeric_string (Int64.to_string t2) 6)

let render_timecomment time str offset =
  let s = sprintf "(** %s \"%s\" **)\n" (render_timestamp time offset) str in
  (time +. offset,s);;

(* N.B. we follow the parser, not the logical structure. The parser
   expects abstime to be followed by a comment. abstime may be proceeded
   by multiple comments, but they are not available in the parse_data,
   they are located in the parse_return

   FIXME code linked with tthee.ml (search for EMITESAB)
*)
let abstime_to_string (sec,usec) =
  (sprintf "abstime %s %s\n"
     (Int64.to_string sec)
     (lpad_numeric_string (Int64.to_string usec) 6))
  ^ "(* EMITESAB *)"



let duration_to_string dur = match dur with
  | DURATION(sec,usec) -> sprintf "duration %s %s" (Int64.to_string sec) (lpad_numeric_string (Int64.to_string usec) 6);;

let lh_epsilon_to_string dur =
  "Lh_epsilon(" ^ (duration_to_string dur) ^ ")";;













let ns_parse_data_to_string pd = match pd with
  | HOLSNDMSG(sndmsg) ->
      (match sndmsg with
	   TCPMSG(tcp) -> render_tcp_inner_no_semicolon tcp SENDDGRAM
	 | UDPMSG(udp) -> render_udp_inner_no_semicolon udp SENDDGRAM
	 | ICMPMSG(icmp) -> render_icmp_inner_no_semicolon icmp SENDDGRAM)
  | HOLLOOPMSG(loopmsg) ->
      (match loopmsg with
	   TCPMSG(tcp) -> render_tcp_inner_no_semicolon tcp LOOPDGRAM
	 | UDPMSG(udp) -> render_udp_inner_no_semicolon udp LOOPDGRAM
	 | ICMPMSG(icmp) -> render_icmp_inner_no_semicolon icmp LOOPDGRAM)
  | HOLRCVMSG(rcvmsg) ->
      (match rcvmsg with
           TCPMSG(tcp) -> render_tcp_inner_no_semicolon tcp RECVDGRAM
         | UDPMSG(udp) -> render_udp_inner_no_semicolon udp RECVDGRAM
         | ICMPMSG(icmp) -> render_icmp_inner_no_semicolon icmp RECVDGRAM)
  | LIBCALL(tid, libcall) -> lh_call_to_string libcall tid
  | LIBRETURN (tid, libreturn) -> lh_return_to_string libreturn tid
  | TCPTRACE(act,sid,addr,state,tcpcb) -> tcpcb_trace_to_string act sid addr state tcpcb
  | HOLABSTIME(sec,usec) -> abstime_to_string (sec,usec)
  | HOLEPSILON(dur) -> lh_epsilon_to_string dur

let timecomment_option_to_string tco = match tco with
  | None -> ""
  | Some (TIMECOMMENT(time, str)) ->
      let offset = 0L in
      let (_, timestr) = render_timecomment time str offset in
	timestr;;

let comment_list_option_to_string commentso = match commentso with
  | None -> ""
  | Some xs -> String.concat "\n" (List.rev xs);; (* reverse because first comment is at end of list- see parser.mly *)

let ns_parse_return_to_string pr =
  let offset = 0L in
    match pr with PARSE_RETURN(times,commentl,parsedata) ->
      let times = timecomment_option_to_string times in
      let commentl = comment_list_option_to_string commentl in
      let parsedata = ns_parse_data_to_string parsedata in
	times
	^ commentl ^ "\n"
	^ parsedata;;

let spec3_parse_data_to_string pd = match pd with
  | HOLLN1_HOST (hostname,pd) -> "Ln1_host(" ^ hostname ^ ",\n"
      ^ (ns_parse_data_to_string pd) ^ "\n"
      ^ ")"
  | HOLLN1_EPSILON dur -> "Ln1_epsilon(" ^ (duration_to_string dur) ^ ")"
  | HOLLN1_ABSTIME (s,t) -> abstime_to_string (s,t)


let spec3_parse_return_to_string pr = match pr with
  | SPEC3_PARSE_RETURN(tco,cso,pd) ->
      (timecomment_option_to_string tco)
      ^ (comment_list_option_to_string cso) ^ "\n"
      ^ (spec3_parse_data_to_string pd);;


(* FIXME tjr render_nsparsemsg_to_chan

   identifier is left over from previous amgb changes, and is now no
   needed I think, so should be removed.

   scomment is redundant, since the comments can be included in the
   parsereturn/msg if required.

   offset is always used at 0, so looks unnecessary and should be
   removed (presumably intended for indenting... can't think when this
   would be useful).

   scomment must be altered in tthee.ml
*)

(* the following is not guaranteed to be equivalent to the previous version because of the relocation of the flush *)
let render_nsparsemsg_to_chan ch pr offset scomment identifier =
  let scomment = "(* " ^ scomment ^ " *) \n" in
  let pr = match pr with
    | PARSE_RETURN(times,commentl,parsedata) ->
	let commentl = match commentl with None -> [] | Some xs -> xs in (* FIXME no point having an option with a list *)
	  PARSE_RETURN(times,Some (scomment::commentl),parsedata) in
  let s = ns_parse_return_to_string pr ^ ";\n" in
  let _ = output_string ch s in
  let _ = flush ch in
    ();;
