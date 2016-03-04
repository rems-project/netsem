open Nettypes
open Parserlib
open Renderlib
open Holtypes
open Holparselib
open Tcpcbtypes
open Tcpcbrender
open Librender
(*open Render*)
open Unix
open Latexdiag
open Arg
open Printf
open Str

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)
let ypos = ref 20
let yinc = 50
let time_offset = ref (uint 0, uint 0)
let guessed_iss :
    (ip option * port option * ip option * port option * uint option) list ref  = ref []
let disc_diam = 4

let input_fname = ref ""
let output_fname = ref ""
let page_preamble = ref "templates/std_preamble.tex" (*default value*)
let page_postamble = ref "templates/std_postamble.tex" (*default value*)
let page_width = ref 480 (*default value*)
let page_height = ref 680 (*default value*)
let left_margin = ref 150 (*default value*)
let right_margin = ref 380 (*default value*)

let scale_opt_ref = ref (None : float option)
let unitlength_opt_ref = ref (None : float option)

let b_annotated = ref false
(* let read_labels_filename = ref None *)
(* let write_labels_filename = ref None *)

let b_withmergeindex = ref false
let b_socket_calls = ref true
let b_show_trace = ref false
let b_use_time_offsets = ref false
let b_use_seq_offsets = ref true

let b_dgram_address = ref false
let b_dgram_win = ref false
let b_dgram_ws = ref false
let b_dgram_urp = ref false
let b_dgram_mss = ref false
let b_dgram_ts = ref false
let b_dgram_datalen = ref false

let b_trace_sndseq = ref false
let b_trace_sndwnd = ref false
let b_trace_rcvseq = ref false
let b_trace_rcvwnd = ref false
let b_trace_maxseg = ref false
let b_trace_dupacks = ref false
let b_trace_time = ref false
let b_trace_scaling = ref false
let b_trace_misc = ref false

let b_all_on_left = ref false
let b_no_description = ref false

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

let render_ip_opt ips =
  match ips with
    None -> "*"
  | Some(ip) -> render_ip_dots ip

let render_port_opt ps =
  match ps with
    None -> "*"
  | Some(p) -> Int64.to_string p

let render_ts ts =
  if !b_use_time_offsets && ((fst !time_offset, snd !time_offset) <> (uint 0, uint 0)) then
    "+" ^ (render_timestamp (((fst !time_offset) *. (uint 1000000)) +. (snd !time_offset))
	     (uint 0)) ^ "s"
  else
    match ts with
      None -> ""
    | Some(TIMECOMMENT(t, _)) -> (render_timestamp t (uint 0)) ^ "s"


let update_guessed_iss is1 ps1 is2 ps2 iss =
  guessed_iss :=
    let rec update_iss iss_list =
      match iss_list with
	[] ->  (* not found, so add new entry *)
	  (is1,ps1,is2,ps2,Some(iss))::[]
      |	(a,b,c,d,i)::xs ->
	  if(a = is1 && b = ps1 && c = is2 && d = ps2) then
	    match i with (* found existing, so alter and concat rest *)
	      None -> (a,b,c,d,Some(iss))::xs
	    | Some(_) -> (a,b,c,d,i)::xs
	  else
	    (a,b,c,d,i)::(update_iss xs)
    in
    update_iss !guessed_iss

let find_guessed_iss is1 ps1 is2 ps2 =
  let rec find_iss iss_list =
    match iss_list with
      [] -> uint 0
    | (a,b,c,d,i)::xs ->
	if(a=is1 && b=ps1 && c=is2 && d=ps2) then
	  match i with
	    None -> uint 0
	  | Some(v) -> v
	else
	  find_iss xs
  in find_iss !guessed_iss

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

(* hackery taken from lts_to_latex to construct roman numerals *)

(* find first pair with key less than or equal to search key *)
let rec gassoc i = function
  | [] -> None
  | ((n,x)::nxs) ->
      if i >= n then
        Some (n,x)
      else
        gassoc i nxs

let rec roman_pos uc i =
  let letters =
    if uc then
      [(1000,"M"); (900,"CM"); (500,"D"); (400,"CD");
       (100,"C"); (90,"XC"); (50,"L"); (40,"XL");
       (10,"X"); (9,"IX"); (5,"V"); (4,"IV"); (1,"I")]
    else
      [(1000,"m"); (900,"cm"); (500,"d"); (400,"cd");
       (100,"c"); (90,"xc"); (50,"l"); (40,"xl");
       (10,"x"); (9,"ix"); (5,"v"); (4,"iv"); (1,"i")]
  in
  match gassoc i letters with
  | Some (n,s) ->
      s ^ roman_pos uc (i-n)
  | None ->
      if i = 0 then
        ""
      else
        raise (Failure ("roman: "^string_of_int i))

let roman uc i =
  if i < 0 then
    (if uc then "N" else "n")^roman_pos uc (-i)
  else if i > 0 then
    roman_pos uc i
  else
    (if uc then "Z" else "z")

let texify_index s =
  "\\labelstep" ^ roman true (int_of_string (s))

let texify_index_b s =
  "\\labelstep" ^ roman true (int_of_string (s)) ^ "b"

let stringify_index s =
  if !b_withmergeindex then s else ""


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

(* label rendering functions, pulled out from below so as to
parameterise on whether we're doing normal rendering or with-rule-name
rendering *)

(* aux for calls and returns *)
let mk_raw_ts_merge_str ts merge_index = (render_ts ts) ^ " (\\#" ^ merge_index ^ ")"


(* for datagrams *)
let mk_ts_merge_dgram_str ts merge_index =
  match !b_annotated with
    false ->  mk_raw_ts_merge_str ts merge_index ^ "\\newline "
  | true -> "\\labeldgram{" ^stringify_index merge_index ^"}{" ^ texify_index merge_index ^"}"


let mk_ts_merge_call_str ts merge_index libcall =
  let call_str = convert_string (lib_call_render_call libcall) in
  match !b_annotated with
    false ->
      let ts_merge_str = mk_raw_ts_merge_str ts merge_index ^ "\\newline " in
      ts_merge_str ^" \\bfseries " ^  call_str
  | true -> "\\labelcall{"  ^stringify_index merge_index ^"}{" ^ texify_index merge_index ^ "}{" ^  call_str ^"}"


let mk_ts_merge_ret_str ts merge_index libreturn =
  let return_str = convert_string (lib_return_render_return libreturn) in
  match !b_annotated with
    false ->
      let ts_merge_str = mk_raw_ts_merge_str ts merge_index ^ "\\newline " in
        ts_merge_str ^" \\bfseries " ^  return_str
  | true -> "\\labelret{"  ^stringify_index merge_index ^"}{" ^ texify_index merge_index ^ "}{" ^ return_str ^"}"

let mk_ts_merge_between merge_index  =
  match !b_annotated with
    false ->
      ""
  | true -> "\\labelbetween{"  ^stringify_index merge_index ^"}{" ^ texify_index_b merge_index ^ "}"


(* gizmo to add an inbetween label *)

let inbetween hnd merge_index =
  match !b_annotated with
    false ->
      ()
  | true ->
      (diaglib_add hnd
         (LABEL(0,!ypos + yinc/2,!left_margin-5,0,LEFT,mk_ts_merge_between merge_index)))

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

let render_next_call hnd ts libcall merge_index =
  if !b_socket_calls then
    let merge_call_str = mk_ts_merge_call_str ts merge_index libcall in
    (diaglib_add hnd
       (LABEL(0,!ypos,!left_margin-5,0,LEFT,merge_call_str));
     diaglib_add hnd (DISC(!left_margin,!ypos,disc_diam));
     inbetween hnd merge_index;
     ypos := !ypos + yinc)
  else ypos := !ypos + yinc/3

let render_next_return hnd ts libreturn merge_index =
  if !b_socket_calls then
    let merge_return_str = mk_ts_merge_ret_str ts merge_index libreturn in
    (diaglib_add hnd
       (LABEL(0,!ypos,!left_margin-5,0,LEFT,merge_return_str));
     inbetween hnd merge_index;
     diaglib_add hnd (DISC(!left_margin,!ypos,disc_diam));
     ypos := !ypos + yinc)
  else ypos := !ypos + yinc/3


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

let seq_num_subtract seq initial =
  let rec power x n =
    if n = 0 then uint 1
    else if n mod 2 = 0 then x *. power x (n/2)
    else x *. (power x (n-1)) in
  if seq >=. initial then
    seq -. initial
  else
    if (seq +. (Int64.neg initial)) >=. (uint 0) then
      seq +. (((power (uint 2) 32) -. (uint 1)) -. initial +. uint 1)
    else
      seq

let make_dgram_string dg =
  "TCP " ^
  let seq,ack =
    if !b_use_seq_offsets then
      let g1 = find_guessed_iss dg.is1 dg.ps1 dg.is2 dg.ps2 in
      let g2 = find_guessed_iss dg.is2 dg.ps2 dg.is1 dg.ps1 in
      seq_num_subtract dg.seq g1, seq_num_subtract dg.ack g2
    else
      dg.seq, dg.ack in
  (sprintf "%s:%s%s %s%s%s%s%s%s \\newline "
     (Int64.to_string dg.seq)  (Int64.to_string dg.ack)
     (if !b_use_seq_offsets then
       " (" ^ (Int64.to_string seq) ^ ":" ^ (Int64.to_string ack) ^ ") "
     else "")
     (if dg.uRG then "\\color{black}U" else "\\color{lightgray}U")
     (if dg.aCK then "\\color{black}A" else "\\color{lightgray}A")
     (if dg.pSH then "\\color{black}P" else "\\color{lightgray}P")
     (if dg.rST then "\\color{black}R" else "\\color{lightgray}R")
     (if dg.sYN then "\\color{black}S" else "\\color{lightgray}S")
     (if dg.fIN then "\\color{black}F" else "\\color{lightgray}F\\color{black}")) ^
  (if !b_dgram_address then
    sprintf "%s:%s$\\rightarrow$%s:%s "
      (render_ip_opt dg.is1) (render_port_opt dg.ps1)
      (render_ip_opt dg.is2) (render_port_opt dg.ps2)
  else "") ^
  (if !b_dgram_win then
    sprintf "win=%s " (Int64.to_string dg.win)
  else "") ^
  (if !b_dgram_ws then
    match dg.scale with
      None -> "ws=* "
    |	Some(v) -> sprintf "ws=%s " (Int64.to_string v)
  else "") ^
  (if !b_dgram_urp || dg.uRG then
    sprintf "urp=%s " (Int64.to_string dg.urp)
  else "") ^
  (if !b_dgram_mss || dg.sYN then
    match dg.mss with
      None -> "mss=* "
    |	Some(v) -> sprintf "mss=%s " (Int64.to_string v)
  else "") ^
  (if !b_dgram_ts then
    match dg.ts with
      None -> "ts=*,* "
    |	Some(t1,t2) -> sprintf "ts=%s,%s " (Int64.to_string t1) (Int64.to_string t2)
  else "") ^
  (if !b_dgram_datalen then
    sprintf "len=%s " (string_of_int (List.length dg.data))
  else "")

let make_udp_string udp =
  "UDP " ^
  (sprintf "%s:%s$\\rightarrow$%s:%s "
    (render_ip_opt udp.udp_hol_is1) (render_port_opt udp.udp_hol_ps1)
    (render_ip_opt udp.udp_hol_is2) (render_port_opt udp.udp_hol_ps2)) ^
  (sprintf "datalen=%d " (List.length udp.udp_hol_data))

let render_icmp_hol_type ty =
  match ty with
    ICMP_UNREACH(unreach_code) ->
      (match unreach_code with
	NET -> "NET "
      | HOST -> "HOST "
      | PROTOCOL -> "PROTOCOL "
      | PORT -> "PORT "
      | SRCFAIL -> "SRCFAIL "
      | NEEDFRAG(wordopt) ->
	  (match wordopt with
	    None -> "NEEDFRAG "
	  | Some(x) -> sprintf "NEEDFRAG(%s) " (Int64.to_string x))
      | NET_UNKNOWN -> "NET UNKNOWN "
      | HOST_UNKNOWN -> "HOST UNKNOWN "
      | ISOLATED -> "ISOLATED "
      | NET_PROHIB -> "NET PROHIBITED "
      | HOST_PROHIB -> "HOST PROHIBITED "
      | TOSNET -> "TOS NET "
      | TOSHOST -> "TOS HOST "
      | FILTER_PROHIB -> "FILTER PROHIBITED "
      | PREC_VIOLATION -> "PREC VIOLATION "
      | PREC_CUTOFF -> "PREC CUTOFF ") ^
      "UNREACHABLE"

  | ICMP_SOURCE_QUENCH(quench_code) ->
      (match quench_code with
	QUENCH -> ""
      | SQ_OTHER(b,w32) ->
	  sprintf "OTHER(%s,%s) " (Int64.to_string b) (Int64.to_string w32)) ^
      "SOURCE QUENCH"

  | ICMP_REDIRECT(redirect_code) ->
      (match redirect_code with
	RD_NET -> "NET "
      | RD_HOST -> "HOST "
      | RD_TOSNET -> "TOS NET "
      | RD_TOSHOST -> "TOS HOST "
      | RD_OTHER(b,w32) ->
	  sprintf "OTHER(%s,%s) " (Int64.to_string b) (Int64.to_string w32)) ^
      "REDIRECT"

  | ICMP_TIME_EXCEEDED(time_exceeded_code) ->
      (match time_exceeded_code with
	INTRANS -> "INTRANS "
      | REASS -> "REASS "
      | TX_OTHER(b,w32) ->
	  sprintf "OTHER(%s,%s) " (Int64.to_string b) (Int64.to_string w32)) ^
      "TIME EXCEEDED"

  | ICMP_PARAMPROB(icmp_paramprob_code) ->
      (match icmp_paramprob_code with
	BADHDR -> "BAD HEADER "
      | NEEDOPT -> "NEED OPT "
      | PP_OTHER(b,w32) ->
	  sprintf "OTHER(%s,%s) " (Int64.to_string b) (Int64.to_string w32)) ^
      "PARAM PROBLEM CODE"

  | ICMP_NONE -> "NONE"


let make_icmp_string icmp =
  "ICMP " ^
  (sprintf "%s$\\rightarrow$%s "
    (render_ip_opt icmp.icmp_hol_is1) (render_ip_opt icmp.icmp_hol_is2)) ^
  (sprintf "(%s:%s$\\rightarrow$%s:%s) "
    (render_ip_opt icmp.icmp_hol_is3) (render_port_opt icmp.icmp_hol_ps3)
    (render_ip_opt icmp.icmp_hol_is4) (render_port_opt icmp.icmp_hol_ps4)) ^
  (sprintf "pr=%s " (if icmp.icmp_hol_proto = PROTO_TCP then "TCP" else "UDP")) ^
  (match icmp.icmp_hol_seq with
    None -> ""
  | Some(seq) -> sprintf "seq=%s " (Int64.to_string seq)) ^
  (sprintf "type=%s " (render_icmp_hol_type icmp.icmp_hol_type))


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

let render_snd_dgram hnd ts dgram merge_index =
  let ts_merge_str = mk_ts_merge_dgram_str ts merge_index  in
  let inc = ref yinc in
  let label =
    match dgram with
      TCPMSG(tcp) ->
	update_guessed_iss tcp.is1 tcp.ps1 tcp.is2 tcp.ps2 tcp.seq;
	make_dgram_string tcp
    | UDPMSG(udp) -> make_udp_string udp
    | ICMPMSG(icmp) ->
	(if !ypos mod !page_height > 600 then ypos := !ypos + (!page_height - (!ypos mod !page_height) + yinc/2)
	else ypos := !ypos + yinc/2);
	inc := yinc + yinc/2;
	make_icmp_string icmp in
  diaglib_add hnd (DISC(!left_margin, !ypos, disc_diam));
  diaglib_add hnd (LABEL(0,!ypos,!left_margin-5,0,LEFT,ts_merge_str));
  inbetween hnd merge_index;
  diaglib_add hnd (ARROW(!left_margin,!ypos,!right_margin,!ypos+yinc/2,label,CENTRE));
  ypos := !ypos + !inc


let render_rcv_dgram hnd ts dgram merge_index =
  let ts_merge_str = mk_ts_merge_dgram_str ts merge_index  in
  let inc = ref yinc in
  let label =
    match dgram with
      TCPMSG(tcp) ->
	update_guessed_iss tcp.is1 tcp.ps1 tcp.is2 tcp.ps2 tcp.seq;
	make_dgram_string tcp
    | UDPMSG(udp) -> make_udp_string udp
    | ICMPMSG(icmp) ->
	(if !ypos mod !page_height > 600 then ypos := !ypos + (!page_height - (!ypos mod !page_height) + yinc/2)
	else ypos := !ypos + yinc/2);
	inc := yinc + yinc/2;
	make_icmp_string icmp in
  diaglib_add hnd (DISC(!right_margin, !ypos, disc_diam));
  (if !b_all_on_left  then  (
    diaglib_add hnd (LABEL(0,!ypos,!left_margin-5,0,LEFT,ts_merge_str));
    inbetween hnd merge_index)
  else
    diaglib_add hnd (LABEL(!right_margin+5,!ypos,!page_width- !right_margin,0,LEFT,ts_merge_str)));
  diaglib_add hnd (ARROW(!right_margin,!ypos,!left_margin,!ypos+yinc/2,label,ALL));
  ypos := !ypos + !inc


let render_loop_dgram hnd ts dgram merge_index =
  let ts_merge_str = mk_ts_merge_dgram_str ts merge_index  in
  let inc = ref yinc in
  let label =
    match dgram with
      TCPMSG(tcp) ->
	update_guessed_iss tcp.is1 tcp.ps1 tcp.is2 tcp.ps2 tcp.seq;
	make_dgram_string tcp
    | UDPMSG(udp) -> make_udp_string udp
    | ICMPMSG(icmp) ->
	(if !ypos mod !page_height > 600 then ypos := !ypos + (!page_height - (!ypos mod !page_height) + yinc/2)
	else ypos := !ypos + yinc/2);
	inc := yinc + yinc/2;
	make_icmp_string icmp in
  let midpointx, midpointy =
    !left_margin + ((!right_margin - !left_margin)*5)/6,
    !ypos + 3*(!inc)/4 in
  diaglib_add hnd (DISC(!left_margin, !ypos, disc_diam));
  diaglib_add hnd (LABEL(0,!ypos,!left_margin-5,0,LEFT,ts_merge_str));
  inbetween hnd merge_index;
  diaglib_add hnd (ARROW(!left_margin,!ypos,midpointx,midpointy,label,ALL));
  diaglib_add hnd (ARROW(midpointx,midpointy,!left_margin,!ypos+3*yinc/2,"",ALL));
  ypos := !ypos + 2*(!inc)


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

let make_trace_string action state tr =
  (sprintf "Action:%s $\\longrightarrow$ %s \\newline "
     (convert_string (tsact_render action))
     (convert_string (tstate_render state))) ^
  (if !b_trace_sndseq then
    sprintf "snd\\_una=%s, snd\\_max=%s, snd\\_nxt=%s, iss=%s "
      (if !b_use_seq_offsets then
	"+" ^ (Int64.to_string (seq_num_subtract tr.snd_una tr.iss))
      else
	(Int64.to_string tr.snd_una))
      (if !b_use_seq_offsets then
	"+" ^ (Int64.to_string (seq_num_subtract tr.snd_max tr.iss))
      else
	(Int64.to_string tr.snd_max))
      (if !b_use_seq_offsets then
	"+" ^ (Int64.to_string (seq_num_subtract tr.snd_nxt tr.iss))
      else
	(Int64.to_string tr.snd_nxt))
      (Int64.to_string tr.iss)
  else "") ^
  (if !b_trace_sndwnd then
    sprintf "snd\\_wl1=%s, snd\\_wl2=%s, snd\\_wnd=%s, snd\\_cwnd=%s, snd\\_thresh=%s, snd\\_recover=%s "
      (Int64.to_string tr.snd_wl1)
      (if !b_use_seq_offsets then
	"+" ^ (Int64.to_string (seq_num_subtract tr.snd_wl2 tr.iss))
      else
	(Int64.to_string tr.snd_wl2))
      (Int64.to_string tr.snd_wnd)
      (Int64.to_string tr.snd_cwnd)
      (Int64.to_string tr.snd_ssthresh)
      (if !b_use_seq_offsets then
	"+" ^ (Int64.to_string (seq_num_subtract tr.snd_recover tr.iss))
      else
	(Int64.to_string tr.snd_recover))
  else "") ^
  (if !b_trace_rcvseq then
    sprintf "rcv\\_nxt=%s, rcv\\_adv=%s, rcv\\_up=%s, irs=%s "
      (if !b_use_seq_offsets then
	"+" ^ (Int64.to_string (seq_num_subtract tr.rcv_nxt tr.irs))
      else
	(Int64.to_string tr.rcv_nxt))
      (if !b_use_seq_offsets then
	"+" ^ (Int64.to_string (seq_num_subtract tr.rcv_adv tr.irs))
      else
	(Int64.to_string tr.rcv_adv))
      (if !b_use_seq_offsets then
	"+" ^ (Int64.to_string (seq_num_subtract tr.rcv_up tr.irs))
      else
	(Int64.to_string tr.rcv_up))
      (Int64.to_string tr.irs)
  else "") ^
  (if !b_trace_rcvwnd then
    sprintf "rcv\\_wnd=%s "
      (Int64.to_string tr.rcv_wnd)
  else "") ^
  (if !b_trace_maxseg then
    sprintf "t\\_maxseg=%s " (Int64.to_string tr.t_maxseg)
  else "") ^
  (if !b_trace_dupacks then
    sprintf "t\\_dupacks=%s " (Int64.to_string tr.t_dupacks)
  else "") ^
  (if !b_trace_time then
    sprintf "t\\_rttseg=%s, ts\\_recent=%s "
      (match tr.t_rttseg with
	None -> "*"
      |	Some(t1,t2) -> (Int64.to_string t1) ^ "," ^ (Int64.to_string t2))
      (match tr.ts_recent with
	TimeWindowClosed -> "Closed"
      |	TimeWindow(x, NEVER_TIMER) -> Int64.to_string x)
  else "") ^
  (if !b_trace_scaling then
    sprintf "snd\\_scale=%s, rcv\\_scale=%s "
      (Int64.to_string tr.snd_scale) (Int64.to_string tr.rcv_scale)
  else "") ^
  (if !b_trace_misc then
    sprintf "last\\_ack\\_sent=%s" (Int64.to_string tr.last_ack_sent)
  else "")


let render_next_trace hnd ts action state tcpcb merge_index =
  if !b_show_trace then
    (ypos := !ypos + yinc/3; (* a small formatting bodge *)
     let label = "\\tiny " ^ (make_trace_string action state tcpcb) in
     let ts_merge = (render_ts ts) ^ " (\\#" ^ merge_index ^ ")" in
     diaglib_add hnd (DISC(!left_margin,!ypos,disc_diam));
     diaglib_add hnd (LABEL(0,!ypos,!left_margin-5,0,LEFT,ts_merge));
     diaglib_add hnd (LABEL(!left_margin+5,!ypos,!right_margin- !left_margin-10,0,LEFT,label));
     inbetween hnd merge_index;
     ypos := !ypos + yinc)


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)

let find_merge_index commentl =
  let regexp = regexp "(\\* Merge Index: \\([0-9]*\\)" in
  let rec find strlist =
    match strlist with
      [] -> ""
    | x::xs ->
	if string_match regexp x 0 then
	  matched_group 1 x
	else
	  find xs
  in find commentl

let parse_and_render_loop ch hnd =

(*
  match !b_annotated with
    false ->  ""
  | true -> "\\input{" ^ annotated ^ "}\n"
*)

  let env = Threadparsing.create_parse_env () in
  let headerend_y = ref 0 in
  try let lexbuf = Lexing.from_channel ch in
  while true do
    let result = Parser.main env Lexer.token lexbuf
    in
    match result with
      PARSE_RETURN(ts,commentlo,r) ->
	let commentlist =
	  match commentlo with
	    None -> []
	  | Some(l) -> l in
	(match r with
          HOLSNDMSG(holmsg) ->
	    render_snd_dgram hnd ts holmsg (find_merge_index commentlist)
        | HOLRCVMSG(holmsg) ->
	    render_rcv_dgram hnd ts holmsg (find_merge_index commentlist)
	| HOLLOOPMSG(holmsg) ->
	    render_loop_dgram hnd ts holmsg (find_merge_index commentlist)
	| LIBCALL(tid, libcall) ->
	    render_next_call hnd ts libcall (find_merge_index commentlist)
        | LIBRETURN(tid, libreturn) ->
	    render_next_return hnd ts libreturn (find_merge_index commentlist)
        | TCPTRACE(action, tracesid, addr, state, tcpcb) ->
	    render_next_trace hnd ts action state tcpcb (find_merge_index commentlist)
	| HOLEPSILON(DURATION(s,usec)) ->
	    time_offset := ((fst !time_offset) +. s,
			(snd !time_offset) +. usec)
	| HOLABSTIME(_) ->
	    (* The comment contains all the file headers that we require *)
	    match commentlo with
	      None -> ()
	    | Some(xs) ->
                if !b_no_description then () else
                (
		 (let head1, head2 =
		   let rec last2 xs a b =
		     match xs with
		       [] -> b,a
		     | x::xs -> last2 xs b x
		   in last2 xs "" ""
		 in

		 let host = convert_string (String.sub head1 3 ((String.length head1) - 6)) in
		 let desc = convert_string (String.sub head2 3 ((String.length head2) - 6)) in
		 diaglib_add hnd (LABEL(5,!ypos,!page_width - 5,
				        0,LEFT,"\\textnormal\\bfseries " ^ host
				        ^ "\\newline " ^ desc ^ " \\newline\\small " ^
				        !input_fname ));
		 ypos := !ypos + yinc;
		 headerend_y := !ypos - !ypos/4;
	         ) ) )
  done with Lexer.Eof ->
    (diaglib_add hnd (LINE(!left_margin,!headerend_y,!left_margin,!ypos,DARKGRAY));
     diaglib_add hnd (LINE(!right_margin,!headerend_y,!right_margin,!ypos,DARKGRAY)))


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)


let process_args =
  let args_list = [
    ("-o", String(function f -> output_fname := f),
     "Filename for latex output");
    ("-preamble", String(function f -> page_preamble := f),
     "Filename of latex preamble template");
    ("-postamble", String(function f -> page_postamble := f),
     "Filename of latex postamble template");
    ("-annotated", Set(b_annotated), "Output in rule-annotated mode");
(*    ("-read-labels", String(function f -> read_labels_filename := Some f), *)
(*      "Filename of overriding label definition file to read. The actual name is not yet used, but this turns on annotated-mode"); *)
(* filename from -read-labels is not yet used (plan was to include a latex include as specified, but not needed now *)
(* -write-labels is not yet used (plan was to write the mng part of the normal label, but not clear it's needed *)
(*    ("-write-labels", String(function f -> write_labels_filename := Some f), *)
(*     "Filename of overriding label definition file to write"); *)
    ("-width", Int(function i -> page_width := i),
     "Width of page (in \\unitlengths)");
    ("-height", Int(function i -> page_height := i),
     "Height of page (in \\unitlengths)");
    ("-scale", Float(function x -> scale_opt_ref := Some(x)),
     "Factor to scale resulting pages by");
    ("-unitlength", Float(function x -> unitlength_opt_ref := Some(x)),
     "unitlength setting (in pt)");
    ("-left-margin-offset", Int(function i -> left_margin := i),
     "Distance of left margin from left edge (in unitlengths)");
    ("-right-margin-offset", Int(function i -> right_margin := i),
     "Distance of right margin from left edge (in unitlengths)");
    ("-withmergeindex", Set(b_withmergeindex), "Show (calculated) merge indices");
    ("-no-socket", Clear(b_socket_calls), "Do not show socket calls");
    ("-dgram-addr", Set(b_dgram_address), "Show datagram address quad");
    ("-dgram-win", Set(b_dgram_win), "Show datagram window size");
    ("-dgram-ws", Set(b_dgram_ws), "Show datagram window scaling");
    ("-dgram-urp", Set(b_dgram_urp), "Show datagram urgent pointer");
    ("-dgram-mss", Set(b_dgram_mss), "Show datagram maximum segment size");
    ("-dgram-ts", Set(b_dgram_ts), "Show datagram timestamp");
    ("-dgram-datalen", Set(b_dgram_datalen), "Show length of datagram data");
    ("-trace-sndseq", Set(b_trace_sndseq), "Show TCP trace sender sequencing values");
    ("-trace-rcvseq", Set(b_trace_rcvseq), "Show TCP trace receiver sequencing value");
    ("-trace-sndwnd", Set(b_trace_sndwnd), "Show TCP trace sender window values");
    ("-trace-rcvwnd", Set(b_trace_rcvwnd), "Show TCP trace receiver window value");
    ("-trace-maxseg", Set(b_trace_maxseg), "Show TCP trace maximum segment size value");
    ("-trace-dupacks", Set(b_trace_dupacks), "Show TCP trace duplicate acknowledgements value");
    ("-trace-time", Set(b_trace_time), "Show TCP trace time-related values");
    ("-trace-scaling", Set(b_trace_scaling), "Show TCP trace scaling values");
    ("-trace-misc", Set(b_trace_misc), "Show TCP trace misc values");
    ("-time-offsets", Set(b_use_time_offsets), "Display times as an offset from the initial time");
    ("-no-seq-offsets", Clear(b_use_seq_offsets), "Displays sequence numbers as an offset from the initial sequence numbers");
    ("-all-on-left", Set(b_all_on_left), "Displays all time labels on the left");
    ("-no-description", Set(b_no_description), "Do not show description");
  ] in
  let usage_string = "Netsem Network Diagram Creator v0.1\n" ^
    "mkdiag -o output_file -width w -height h [options] input_file" in
  parse args_list (function f -> input_fname := f) usage_string;
  if !input_fname = "" || !output_fname = "" then
    (usage args_list usage_string; exit(1));
  if (!b_trace_sndseq || !b_trace_sndwnd || !b_trace_rcvseq || !b_trace_rcvwnd ||
  !b_trace_maxseg || !b_trace_dupacks || !b_trace_time || !b_trace_scaling ||
  !b_trace_misc) then
    b_show_trace := true


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)


let main  =
  let fd = Unix.openfile !input_fname [O_RDONLY] 0 in
  let ch = Unix.in_channel_of_descr fd in
  let hnd = diaglib_init !page_preamble !page_postamble !page_width
      !page_height !input_fname in
  parse_and_render_loop ch hnd;
  diaglib_emit hnd !output_fname !unitlength_opt_ref !scale_opt_ref;
  Unix.close fd


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)
(* ThE eNd *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)
