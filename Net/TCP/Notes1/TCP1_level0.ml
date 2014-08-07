#load "str.cma";;
(*
Sat Dec  4 12:42:53 GMT 2004

Picking out all the rules that affect the st field of a TCP socket,
and all the rules that have incoming or outgoing segments that match a
socket, noting:
  - the rule name (and, redundantly, the label form)
  - the initial state
  - the final state
  - the architecture, if relevant
  - any segments that might be added or removed from the queues, with
      constraints on their ACK, RST, SYN, FIN flags
  - whether this is a particularly pathological case

Sometimes also noting any conditions on cantsndmore/cantrcvmore, but
not sure whether I'm doing that for real.  Later: I rather suspect I'm
not, as it multiplies the states in the diagram too much.

The Stevens diagram scarcely mentions any RST cases, but there is one
SYN_RECEIVED -- recv:RST --> LISTEN transition.

A big diagram should have rule short descriptions aswell as rule names
- much more comprehensible what's going on.  Maybe pull these out
automatically from hostLTS - stupid to copy them.

Keith thinks that a few important dimensions have been missed: in
particular, retransmit state (None, RexmtSyn, Rexmt, Persist), but
also cantrcv/sndmore, tf_needfin, sndq<>[], etc.  Obviously simply
producting these in would yield an undrawable diagram, but
reclustering (slicing) in a different way might be useful.  For
example, most of the TCP code is independent of which state in
{ESTABLISHED, CLOSE_WAIT, LAST_ACK, FIN_WAIT_1, CLOSING, FIN_WAIT_2,
TIME_WAIT} is current; instead, the retransmit mode is of much more
interest.  It's possible that coalescing this class, and then
producting with the retransmit state, would yield a manageable set of
nodes.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Socket call rules                                         %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% close_2, close_4     Lh_call (tid,close(fd))
%
%      (st IN {ESTABLISHED;FIN_WAIT_1;CLOSING;FIN_WAIT_2;
%              TIME_WAIT;CLOSE_WAIT;LAST_ACK} \/
%       st = SYN_RECEIVED linux_arch h.arch)
%
%
%       st'=st
%       cantsndmore=T cantrcvmore=T

*)

type    tcpstate =  NONEXIST
             |  CLOSED
             | LISTEN
             | SYN_SENT
             | SYN_RECEIVED
             | ESTABLISHED
             | CLOSE_WAIT
             | FIN_WAIT_1
             | CLOSING
             | LAST_ACK
             | FIN_WAIT_2
             | TIME_WAIT

let linux_arch = false
let bsd_arch = true


let transitions =

[
("close_3", "close()",
         ([ESTABLISHED;FIN_WAIT_1;CLOSING;FIN_WAIT_2; TIME_WAIT;CLOSE_WAIT;LAST_ACK;]
           @ if linux_arch then [SYN_RECEIVED] else []),

         Some [CLOSED],
          "",
          "send:  ACK RST ~SYN",
          "");

("close_7",   "close()",

     ([CLOSED; SYN_SENT]
       @ if linux_arch then [] else [SYN_RECEIVED]),

      Some [NONEXIST],
      "",
      "",
      "");


("close_8",    "close())",
      [LISTEN],
      Some [NONEXIST],
      "",
      "",
      "");

("close_8",    "close()",
      [ESTABLISHED],
      Some [NONEXIST],
      "",
      "send: ACK RST ~SYN",
      "states on the complete connection queue");

("close_8",    "close()",
      [SYN_RECEIVED],
      Some [NONEXIST],
      "",
      "",
      "states on the incomplete connection queue");

("connect_1", "connect())",
      ([CLOSED] @ if bsd_arch then [TIME_WAIT] else []),
      Some [SYN_SENT],
      "",
      "send: ~ACK ~RST SYN ~FIN",
      "");

("connect_1", "connect()",
      ([CLOSED] @ if bsd_arch then [TIME_WAIT] else []),
      Some [CLOSED],
      "",
      "",
      " if the enqueue failed ");

("connect_4", "tau",
       [SYN_SENT],
       Some [SYN_SENT; CLOSED],
       "",
       "",
       "");

("disconnect_5",  "disconnect()",
     (if linux_arch then [SYN_RECEIVED; ESTABLISHED; FIN_WAIT_1;
                         FIN_WAIT_2; CLOSE_WAIT] else []),
     Some [CLOSED],
     "",
     "send: ACK RST ~SYN",
     "");

("listen_1",   "listen()",
     [CLOSED],
     Some [LISTEN],
     "",
     "",
     "");

("listen_1c",   "listen()",

     (if bsd_arch then
     [SYN_SENT;SYN_RECEIVED;ESTABLISHED;CLOSE_WAIT;FIN_WAIT_1;CLOSING;LAST_ACK;FIN_WAIT_2;TIME_WAIT;]
     else []),
     Some [LISTEN],
     "",
     "",
     "BSD pathology");

("shutdown_1",   "shutdown()",
     (if bsd_arch then [LISTEN] else []),
     Some [LISTEN],
     "",
     "",
     "");


("socket_1",  "socket()",
      [NONEXIST],
      Some [CLOSED],
      "",
      "",
      "");

(*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Deliver rules                                              %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
*)

("deliver_in_1",   "tau",
      [NONEXIST],
      Some [SYN_RECEIVED],
      "recv:  ~ACK ~RST SYN",
      "send:  ACK ~RST SYN ~FIN",
      "there is another socket in state LISTEN");

("deliver_in_1",   "tau",
      [TIME_WAIT],
      Some [CLOSED],
      "recv:  ~ACK ~RST SYN",
      "send:  ACK ~RST SYN ~FIN",
      "segments for new conn");
(*      "there is another is state LISTEN. The segments are for the new connection"); *)

("deliver_in_1b",  "tau",
      [LISTEN],
      None,
      "recv: ~RST",
      "send:  RST ~SYN",
      "bad recv segment");

("deliver_in_2",   "tau",
      [SYN_SENT],
      Some [ESTABLISHED;FIN_WAIT_2;FIN_WAIT_1;CLOSE_WAIT;LAST_ACK],
      "recv: ACK ~RST SYN",
      "send: ACK ~RST ~SYN",
      "");

("deliver_in_2",   "tau",
      [SYN_SENT],
      Some [SYN_RECEIVED; CLOSE_WAIT],
      "recv: ~ACK ~RST SYN",
      "send: ACK ~RST SYN ~FIN",
      "");


("deliver_in_2a", "tau",
      [SYN_SENT],
      Some [SYN_SENT],
      "recv: ~RST",
      "send: RST ~SYN",
      "bad recv segment"); ]

@


(* OCamlery to make the transitions for deliver_in_3 *)

(

let sts =  [SYN_RECEIVED;ESTABLISHED;CLOSE_WAIT;FIN_WAIT_1;FIN_WAIT_2;
                    CLOSING;LAST_ACK;TIME_WAIT;] in
let f st sts' fINreass=
  ("deliver_in_3",  "tau", [st], Some sts',
        (if fINreass then "recv: ~RST FIN" else "recv: ~RST ~FIN"),
        "send: di3out",
        "") in
let thecases = List.map (function st -> (st,false)) sts
              @List.map (function st -> (st,true)) sts  in
let finalsts (st,fINreass) =

(*
 look at the mlifts used below and see what they can output

      topstuff:  mlift_dropafterack_or_fail

      ackstuff:  mlift_tcp_output_perhaps_or_fail

        newackstuff:  mlift_tcp_output_perhaps_or_fail
                      mlift_dropafterack_or_fail
                      if st=LAST_ACK  then CLOSED; stop

      datastuff: sets tf_shouldacknow variously

      ststuff:

/        here we case-split on fINreass - so in the abstraction, either
        we pretend that is identical to the received FIN (false), or
        we just allow take fINreass unconstrained (will give a rather
        useless diagram), or...?   Think we go for the first.
*)
         match (st, fINreass) with

          (SYN_RECEIVED,false) -> [ESTABLISHED; FIN_WAIT_2;  FIN_WAIT_1]
         | (SYN_RECEIVED,true) -> [CLOSE_WAIT]

         | (ESTABLISHED,false)  -> [ESTABLISHED] (* Doing common-case data delivery and acks *)
         | (ESTABLISHED,true)  -> [CLOSE_WAIT]

         | (CLOSE_WAIT,_)   -> [CLOSE_WAIT]

         | (FIN_WAIT_1,false)   -> [FIN_WAIT_1;  FIN_WAIT_2]
         | (FIN_WAIT_1,true)   -> [TIME_WAIT; CLOSING]

         | (FIN_WAIT_2,false)   -> [FIN_WAIT_2]
         | (FIN_WAIT_2,true)   -> [TIME_WAIT]

         | (CLOSING,_)      -> [CLOSING; TIME_WAIT]

         | (LAST_ACK,false)     -> [LAST_ACK]
         | (LAST_ACK,true)     -> [CLOSED]
             (*: This transition is handled specially at the end of [[di3_newackstuff]] at which point
                 processing stops, thus this transition is not possible :*)


         | (TIME_WAIT,_)    -> [TIME_WAIT]
         | ((SYN_SENT|LISTEN|CLOSED|NONEXIST), _) -> raise (Failure "this cannot happen")

in List.map (function (st,fINreass) -> f st (finalsts (st,fINreass)) fINreass) thecases

)


@

[

("deliver_in_3b", "tau",
     [FIN_WAIT_1; CLOSING; LAST_ACK; FIN_WAIT_2; TIME_WAIT;],
     Some [CLOSED],
     "recv: ~RST ~SYN",
     "send: RST ~SYN",
     " process gone away");

("deliver_in_3c",  "tau",
     [SYN_RECEIVED],
     Some [SYN_RECEIVED],
     "recv: ACK",
     "send: RST ~SYN",
     "stupid ack, or LAND DoS");

("deliver_in_6",  "tau",
     [CLOSED],
     Some [CLOSED],
     "recv: unconstrained",
     "",
     "");

("deliver_in_7",  "tau",
     [ESTABLISHED; CLOSE_WAIT; FIN_WAIT_1; CLOSING; LAST_ACK; FIN_WAIT_2],
     Some [CLOSED],
     "recv: RST",
     "",
     "");

("deliver_in_7a",   "tau",
     [SYN_RECEIVED],
     Some [CLOSED],
     "recv: RST",
     "",
     "");

("deliver_in_7b"  , "tau",
     [LISTEN],
     Some [LISTEN],
     "recv: RST",
     "",
     "");

("deliver_in_7c"  , "tau",
     [SYN_SENT; TIME_WAIT],
     None,
     "recv: RST",
     "",
     "");

("deliver_in_7d"  , "tau",
     [SYN_SENT],
     Some [CLOSED],
     "recv: ACK RST",
     "",
     " except on WinXP");

("deliver_in_8" , "tau",
     [ SYN_RECEIVED; ESTABLISHED; CLOSE_WAIT; FIN_WAIT_1; CLOSING; LAST_ACK; FIN_WAIT_2],
     None,
     "recv: ~RST SYN",
     "send: ACK RST ~SYN",
     "");

("deliver_in_9" , "tau",
     [TIME_WAIT],
     None,
     "recv: ~RST SYN",
     "send:  RST ~SYN",
     "no listening socket");


("deliver_out_1", "tau",
     [SYN_SENT; SYN_RECEIVED; ESTABLISHED;CLOSE_WAIT;FIN_WAIT_1;FIN_WAIT_2;CLOSING;
              LAST_ACK;TIME_WAIT],
     None,
     "",
     "send: ~RST ~SYN ~FIN",
     "");


("deliver_out_1",  "tau",
     [SYN_SENT; SYN_RECEIVED;FIN_WAIT_1;CLOSING;
              LAST_ACK],
     None,
     "",
     "send: ~RST ~SYN FIN",
     "");

("deliver_out_1",  "tau",
     [ESTABLISHED],
     Some [FIN_WAIT_1],
     "",
     "send: ~RST ~SYN FIN",
     "");

("deliver_out_1",  "tau",
     [CLOSE_WAIT],
     Some [LAST_ACK],
     "",
     "send: ~RST ~SYN FIN",
     "");


(*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Timer rules                                                %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
*)

("timer_tt_rexmtsyn_1"  , "tau",
    [SYN_SENT],   (* TODO: as stated in a TODO, the rule is incomplete and in fact other states are possible in BSD *)
    Some [CLOSED],
    "",
    "",
    "maxrxtshift reached");

("timer_tt_rexmtsyn_1"  , "tau",
    [SYN_SENT],   (* TODO: as stated in a TODO, the rule is incomplete and in fact other states are possible in BSD *)
    None,
    "",
    "send: ~ACK ~RST SYN ~FIN",
    "");


("timer_tt_rexmt_1"  , "tau",
    (if bsd_arch then [LISTEN] else []),
    Some [CLOSED],
    "",
    "",
    "BSD pathology");

("timer_tt_rexmt_1"  , "tau",
    [SYN_RECEIVED; ESTABLISHED; FIN_WAIT_1; CLOSING; LAST_ACK],
    Some [CLOSED],
    "",
    "send: ACK RST ~SYN",
    "maxrxtshift reached");

("timer_tt_rexmt_1"  , "tau",
    [SYN_RECEIVED],
    None,
    "",
    "send: ACK ~RST SYN ~FIN",
    "");

("timer_tt_rexmt_1"  , "tau",
    (if bsd_arch then [LISTEN] else []),
    None,
    "",
    "send: ~ACK ~RST ~SYN",   (* pathological! *)
    "BSD pathology");

("timer_tt_rexmt_1"  , "tau",
    [ESTABLISHED; FIN_WAIT_1; CLOSING; LAST_ACK],
    None,
    "",
    "send: ACK ~RST ~SYN ~FIN",  (* tcp_output_really, normal case *)
    "");

("timer_tt_rexmt_1"  , "tau",
    [ESTABLISHED],
    Some [FIN_WAIT_1],
    "",
    "send: ACK ~RST ~SYN FIN",  (* tcp_output_really, application has closed in meantime so we emit FIN *)
    "");


("timer_tt_persist_1", "tau",
    [SYN_RECEIVED; ESTABLISHED; CLOSE_WAIT],  (* K believes these are only possible Persist states *)
    None,
    "",
    "send: ACK ~RST ~SYN ~FIN",  (* tcp_output_really, normal case *)
    "");

("timer_tt_persist_1", "tau",
    [ESTABLISHED],
    Some [FIN_WAIT_1],
    "",
    "send: ACK ~RST ~SYN FIN",  (* tcp_output_really, application has closed in meantime so we emit FIN *)
    "");

("timer_tt_persist_1", "tau",
    [CLOSE_WAIT],
    Some [LAST_ACK],
    "",
    "send: ACK ~RST ~SYN FIN",  (* tcp_output_really, application has closed in meantime so we emit FIN *)
    "");


("timer_tt_keep_1"  , "tau",
    [SYN_SENT (* BSD: even bad seg in SYN_SENT updates keep *); SYN_RECEIVED; ESTABLISHED; CLOSE_WAIT; LAST_ACK; FIN_WAIT_1; CLOSING; FIN_WAIT_2],
    None,
    "",
    "send: ACK ~RST ~SYN ~FIN",
    "");

("timer_tt_2msl_1"  , "tau",
    [TIME_WAIT],
    Some [CLOSED],
    "",
    "",
    "");

(* timer_tt_delack_1 is omitted, since it overlaps deliver_out_1 and invokes the same routine (tcp_output_really).
   Note that it can fire in (at most): [ESTABLISHED; CLOSE_WAIT; LAST_ACK; FIN_WAIT_1; CLOSING; FIN_WAIT_2] *)


("timer_tt_conn_est_1"  , "tau",
    [SYN_SENT],
    Some [CLOSED],
    "",
    "",
    "");

("timer_tt_fin_wait_2_1", "tau",
    [FIN_WAIT_2],
    Some [CLOSED],
    "",
    "",
    "");

(*

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ICMP rules                                                 %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



deliver_in_icmp_1

    recv: ICMP_...

    st=ESTABLISHED
    st'=st

    st IN {CLOSED; LISTEN;SYN_SENT;SYN_RECEIVED}
    st'=CLOSED
    send: ACK RST ~SYN

    st ... else
    st'=st

deliver_in_icmp_2  - 7

    TODO


*)

]


let stevens = (* care! conventions about NONEXIST not taken into account *)
[
("","",[NONEXIST    ],Some [],"","","");
("","",[CLOSED      ],Some [LISTEN;SYN_SENT],"","","");
("","",[LISTEN      ],Some [SYN_RECEIVED;SYN_SENT],"","","");
("","",[SYN_SENT    ],Some [SYN_RECEIVED;CLOSED;ESTABLISHED],"","","");
("","",[SYN_RECEIVED],Some [FIN_WAIT_1;CLOSED;ESTABLISHED],"","","");
("","",[ESTABLISHED ],Some [FIN_WAIT_1;CLOSE_WAIT],"","","");
("","",[CLOSE_WAIT  ],Some [LAST_ACK],"","","");
("","",[FIN_WAIT_1  ],Some [FIN_WAIT_2;TIME_WAIT;CLOSING],"","","");
("","",[CLOSING     ],Some [TIME_WAIT],"","","");
("","",[LAST_ACK    ],Some [CLOSED],"","","");
("","",[FIN_WAIT_2  ],Some [TIME_WAIT],"","","");
("","",[TIME_WAIT   ],Some [CLOSED],"","","");
("","",[SYN_RECEIVED],Some [SYN_RECEIVED],"","","");
]


let expand (rn,label,sts1,sts2option,recv,send,comment) =
   let f st1 =
     let sts2 = match sts2option with None -> [st1] | Some sts2 -> sts2 in
     List.map (function st2 -> (st1,st2)) sts2 in
   let sts = List.flatten (List.map f sts1) in
   let g (st1,st2) = (rn,label,st1,st2,recv,send,comment) in
   List.map g sts

let flat_transitions = List.flatten (List.map expand transitions)
let stevens_transitions = List.flatten (List.map expand stevens)

let pp_st st = match st with
               NONEXIST     -> "NONEXIST    "
             | CLOSED       -> "CLOSED      "
             | LISTEN       -> "LISTEN      "
             | SYN_SENT     -> "SYN_SENT    "
             | SYN_RECEIVED -> "SYN_RECEIVED"
             | ESTABLISHED  -> "ESTABLISHED "
             | CLOSE_WAIT   -> "CLOSE_WAIT  "
             | FIN_WAIT_1   -> "FIN_WAIT_1  "
             | CLOSING      -> "CLOSING     "
             | LAST_ACK     -> "LAST_ACK    "
             | FIN_WAIT_2   -> "FIN_WAIT_2  "
             | TIME_WAIT    -> "TIME_WAIT   "

let int_of_st st = match st with
               NONEXIST     -> 0
             | CLOSED       -> 1
             | LISTEN       -> 2
             | SYN_SENT     -> 3
             | SYN_RECEIVED -> 4
             | ESTABLISHED  -> 5
             | CLOSE_WAIT   -> 6
             | FIN_WAIT_1   -> 7
             | CLOSING      -> 8
             | LAST_ACK     -> 9
             | FIN_WAIT_2   -> 10
             | TIME_WAIT    -> 11

let st_of_int i = match i with
               0 ->  NONEXIST
             | 1 ->  CLOSED
             | 2 ->  LISTEN
             | 3 ->  SYN_SENT
             | 4 ->  SYN_RECEIVED
             | 5 ->  ESTABLISHED
             | 6 ->  CLOSE_WAIT
             | 7 ->  FIN_WAIT_1
             | 8 ->  CLOSING
             | 9 ->  LAST_ACK
             | 10->  FIN_WAIT_2
             | 11->  TIME_WAIT
             | _ -> raise (Failure "cannot happen")


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

let texify_command s =
  let f s = roman true (int_of_string (Str.matched_string s))
  in
   Str.global_replace    (Str.regexp "[^A-Za-z0-9]") "T"
  (Str.global_substitute (Str.regexp "[0-9]+"      )  f
                         s)

let texify_rn s =
  "\\" ^ texify_command s



(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= *)


let rules_used =
  let rec f acc ts = match ts with
    [] -> acc
  | (rn,label,st1,st2,recv,send,comment)::ts ->
      if List.mem rn acc then f acc ts
      else f (List.merge  (compare) acc [rn]) ts       (* not the most efficient! *)
  in f [] flat_transitions


let outchan = open_out "TCP1_level0_rules.tex"
let _ = List.iter (function s -> output_string outchan ((texify_rn s)^"\\\\\n")) rules_used
let _ = close_out outchan


let neatoglue nodefontsize x_scale_factor y_scale_factor =
(*   let neato_preamble = "{splines=\"compound\"};" in *)
  let neato_preamble = "" in
(*  let x_scale_factor = 400 in *)
(*   let y_scale_factor = 400 in *)
(*   let common = "height=\"1.0\" fontsize=\"30\" " in *)
  let common = "fontsize=\"" ^ nodefontsize ^ " \" fontname=\"Helvetica\" " in
  let ns =
 [
  ("NONEXIST    ",0,6);
  ("LISTEN      ",2,5);
  ("SYN_SENT    ",4,4);
  ("SYN_RECEIVED",0,4);
  ("ESTABLISHED ",2,3);
  ("FIN_WAIT_1  ",0,2);
  ("CLOSING     ",2,2);
  ("FIN_WAIT_2  ",0,1);
  ("TIME_WAIT   ",2,1);
  ("CLOSE_WAIT  ",4,2);
  ("LAST_ACK    ",4,1);
  ("CLOSED      ",2,0);
 ]
  in
  let rec scale ns = match ns with
    [] -> ""
(* let x,y=2,4 in "  ruledescrs [pos=\""^ string_of_int (x_scale_factor*x) ^","^string_of_int (y_scale_factor*y)^"\" " ^ common ^ "shape=\"plaintext\" ];\n" *)
  | (n,x,y)::ns' -> n ^ "[pos = \"" ^ string_of_int (x_scale_factor*x) ^","^string_of_int (y_scale_factor*y)^"\" " ^ common ^ " ];\n" ^ scale ns' in
  neato_preamble ^  scale ns





(* let nodes =                                         *)
(*   (* let s="height=\"1.0\" fontsize=\"50\" " in *)  *)
(*   let s="" in                                       *)
(*   "                                                 *)
(*   NONEXIST     [" ^ s ^ "];\n                       *)
(*   LISTEN       [" ^ s ^ "];\n                       *)
(*   SYN_SENT     [" ^ s ^ "];\n                       *)
(*   SYN_RECEIVED [" ^ s ^ "];\n                       *)
(*   ESTABLISHED  [" ^ s ^ "];\n                       *)
(*   FIN_WAIT_1   [" ^ s ^ "];\n                       *)
(*   CLOSING      [" ^ s ^ "];\n                       *)
(*   FIN_WAIT_2   [" ^ s ^ "];\n                       *)
(*   TIME_WAIT    [" ^ s ^ "];\n                       *)
(*   CLOSE_WAIT   [" ^ s ^ "];\n                       *)
(*   LAST_ACK     [" ^ s ^ "];\n                       *)
(*   CLOSED       [" ^ s ^ "];\n                       *)
(* "                                                   *)
(* let foo="                                           *)
(*   {SPLINEs = true };\n {fontsize=8};\n"             *)


let stevensish = (* NB no same-rank edges here, to avoid dot failures *)
 "
NONEXIST->SYN_RECEIVED[color=transparent minlen=2];
LISTEN->SYN_RECEIVED[color=transparent minlen=2];
LISTEN->SYN_SENT[color=transparent minlen=2];
SYN_RECEIVED->ESTABLISHED[color=transparent minlen=2];
SYN_SENT->ESTABLISHED[color=transparent minlen=2];
ESTABLISHED->FIN_WAIT_1[color=transparent];
FIN_WAIT_1->FIN_WAIT_2[color = transparent minlen=2];
FIN_WAIT_1->CLOSING[color=transparent];
FIN_WAIT_1->TIME_WAIT[color=transparent] ;
CLOSING->TIME_WAIT[color=transparent minlen=2];
ESTABLISHED -> CLOSE_WAIT[color=transparent minlen=2];
CLOSE_WAIT->LAST_ACK[color=transparent minlen=2];
FIN_WAIT_2->CLOSED[color=transparent minlen=1];
{rank=same; \"NONEXIST\"; \"LISTEN\"; }
{rank=same; \"SYN_RECEIVED\"; \"SYN_SENT\";}
{rank=same; \"FIN_WAIT_1\"; \"CLOSING\";}
{rank=same; \"FIN_WAIT_2\"; \"TIME_WAIT\";}
{rank=same; \"CLOSING\"; \"CLOSE_WAIT\";}
{rank=same; \"TIME_WAIT\"; \"LAST_ACK\";}
"

(*
CLOSED->LISTEN[color=transparent];
*)

(*
{rank=same; "ESTABLISHED"; "CLOSE_WAIT";}
ESTABLISHED->CLOSE_WAIT
*)




(* remove all labels *)

let t = List.map (function (rn,label,st1,st2,recv,send,comment) -> ("","",st1,st2,"","","") ) flat_transitions

(* quotient by same source and dest, discarding labels for later copies *)

let rec f acc ts = match ts with
  [] -> List.rev acc
| ((rn,label,st1,st2,recv,send,comment) as t)::ts ->
    if List.exists
        (function (rn',label',st1',st2',recv',send',comment') -> st1=st1' && st2=st2') acc
    then
      f acc ts
    else
      f (t::acc) ts

let t = f [] t


(* squidge segments *)

let squidge_seg s =
Str.global_replace (Str.regexp_string " ")  "" (
Str.global_replace (Str.regexp_string "recv:")  "" (
Str.global_replace (Str.regexp_string "send:")  "" (
Str.global_replace (Str.regexp_string "ACK")  "A" (
Str.global_replace (Str.regexp_string "SYN")  "S" (
Str.global_replace (Str.regexp_string "FIN")  "F" (
Str.global_replace (Str.regexp_string "RST")  "R" (
Str.global_replace (Str.regexp_string "~ACK")  "a" (
Str.global_replace (Str.regexp_string "~SYN")  "s" (
Str.global_replace (Str.regexp_string "~FIN")  "f" (
Str.global_replace (Str.regexp_string "~RST")  "r" (
s)))))))))))




(* colorize based on presence of R,S,F *)



(* was [orange/red] in two paces below *)
let colorize s =
      (if (String.contains s 'R') then "color=\"magenta\""  else
      (if (String.contains s 'S') then "color=\"green\""  else
      (if (String.contains s 'F') then "color=\"cyan\""  else "")))

let labelcolorize s =
      (if (String.contains s 'R') then "fontcolor=\"magenta\""  else
      (if (String.contains s 'S') then "fontcolor=\"green\""  else
      (if (String.contains s 'F') then "fontcolor=\"cyan\""  else "")))











(* construct transition matrices *)

let a = Array.make_matrix 12 12 false
let a_stevens = Array.make_matrix 12 12 false

let rec fillit a ts = match ts with [] -> () | ((rn,label,st1,st2,recv,send,comment) as t)::ts -> (a.(int_of_st st1).(int_of_st st2) <- true ; fillit a ts)

let _ = fillit a t
let _ = fillit a_stevens stevens_transitions

let _ = prerr_string "\nTransition matrix - Netsem\n\n"
let _ = for i = 0 to 11 do (prerr_string (pp_st (st_of_int i) ^ " ");(for j = 1 to 11 do if a.(i).(j) then prerr_string "X" else prerr_string "." done ; prerr_newline ())) done

let _ = prerr_string "\nTransition matrix - Stevens\n\n"
let _ = for i = 0 to 11 do (prerr_string (pp_st (st_of_int i) ^ " ");(for j = 1 to 11 do if a_stevens.(i).(j) then prerr_string "X" else prerr_string "." done ; prerr_newline ())) done

let _ = prerr_string "\nTransition matrix - difference\n\n"

let xor a b = ((not a) && b) || (a && (not b))

let _ =
  for i = 0 to 11 do
    (prerr_string (pp_st (st_of_int i) ^ " ");
     for j = 1 to 11 do
       match ( a.(i).(j),  a_stevens.(i).(j)) with
         (true,true) ->  prerr_string "X"
       | (true,false) -> prerr_string "n"
       | (false,true) -> prerr_string "s"
       | (false,false)-> prerr_string "."
     done;
     prerr_newline ()
    ) done




(* ************************************************** *)
(* construct quotiented graph *)
(* ************************************************** *)

let _ = prerr_string "This is a graph of all our transitions (except for certain timer transitions) with the BSD LISTEN pathology transitions removed and transitions with the same source/destination agglomerated.  Transitions involving segments with RST set (either sent or received) are coloured orange; others that have SYN set are coloured green; others that have FIN set are coloured blue; others are coloured black.\n\n"


let t1 = flat_transitions

(* remove BSD LISTEN pathology transitions *)
let t2 = List.filter (function (rn,label,st1,st2,recv,send,comment) -> comment <> "BSD pathology" ) t1


(* squidge labels *)

let t3 = List.map (function (rn,label,st1,st2,recv,send,comment) -> (rn ^ "\\n" ^ (squidge_seg recv) ^ "/" ^ (squidge_seg send),"",st1,st2,"","","") ) t2


(* quotient by same source and dest, glomming labels  *)

let rec f acc ts = match ts with
  [] -> List.rev acc
| ((rn,label,st1,st2,recv,send,comment) as t)::ts ->
    let ts1,ts2 = List.partition
        (function (rn',label',st1',st2',recv',send',comment') -> st1=st1' && st2=st2') acc
    in
    match ts1 with
      [] -> f ((rn,"",st1,st2,"","","") ::ts2) ts
    | (rn',label',st1',st2',recv',send',comment')::[] ->
        f ((rn ^ "\\n" ^rn',"",st1,st2,"","","")::ts2) ts
    | _ -> raise (Failure "cannot happen")


let t4 = f [] t3

let t = t4

(* variant for the glommed experiment *)
let pp_flat_transition_edge_glom (rn,label,st1,st2,recv,send,comment)
  = pp_st st1 ^ " -> " ^ pp_st st2 ^ " [label = \""
    ^ rn ^ "" ^ label ^ ""
 ^ recv ^   "" ^ send ^ "" ^ comment ^ "\""
 ^  colorize rn
(* ^  labelcolorize rn *)
  ^ " arrowsize=\"2.5\""
 ^ " fontsize=\"16\""
 ^ "];\n"        (* ^ "\" decorate =\"true\"" *)


(* let size = "rotate=90; margin=\"0.5,0.5\";  size=\"23.68,16.53!\"; ratio=\"fill\";" (* {bb=\"0,0,308,3371\"};"*) *)
let size = "rotate=90; margin=\"0.5,0.5\";  size=\"8.15,5.67!\"; ratio=\"fill\";" (* {bb=\"0,0,308,3371\"};"*)

(*
     mm          pt           in
A0 841 x 1189 2384 3371    33.11 46.81
A1 594 x 841  1684 2384    23.38
A2 420 x 594  1190 1684    16.53

figure, landsc,uslet        8.15  5.67

*)


let outchan = open_out "TCP1_level0_small.dot"

let _ = output_string outchan  ("digraph G {\n " ^ size ^ (neatoglue "20" 400 400 ) ^stevensish ) ; List.iter (function t-> (output_string outchan  (pp_flat_transition_edge_glom t); output_string outchan "\n")) t (* t4 *) (* t1' *) ; output_string outchan  "}\n"

let _ = close_out outchan


(* let g _  = print_string ("digraph G {\n " ^ size  ^ stevensish ) ; List.iter (function t-> (print_string (pp_flat_transition_edge_glom t); print_newline ())) [] (*t*) ; print_string "}\n" *)


(* let g _  = print_string ("digraph G {\n " ^ (neatoglue "30" 400 400)) ; List.iter (function t-> (print_string (pp_flat_transition_edge_glom t); print_newline ())) [] ; print_string "}\n" *)






(* ************************************************** *)
(* construct full graph, A1 *)
(* ************************************************** *)


let _ = prerr_string "This is a graph of all our transitions (except for certain timer transitions).  Transitions involving segments with RST set (either sent or received) are coloured orange; others that have SYN set are coloured green; others that have FIN set are coloured blue; others are coloured black.\n"

let t1' = flat_transitions

(* remove BSD LISTEN pathology transitions *)
let t2' = List.filter (function (rn,label,st1,st2,recv,send,comment) -> comment <> "BSD pathology" ) t1'


let pp_flat_transition_edge (rn,label,st1,st2,recv,send,comment)
  = let srecv= (squidge_seg recv) in
    let ssend= (squidge_seg send) in
    let label' = (if label="tau" then "" else label ^"\\n") in
  pp_st st1 ^ " -> " ^ pp_st st2 ^ " [label = \""
^ "\\n"
    ^ rn ^ "\\n" ^ label'
 ^ "recv: "^srecv ^   "\\n"
 ^ "send: "^ssend ^ "\\n"
 ^ comment
^ "\\n"
^"\""
 ^  colorize (srecv ^ ssend)
 ^  labelcolorize (srecv ^ ssend)
 ^ " fontsize =\"20\""
 ^ " arrowsize=\"3.5\""
 ^ " fontname=\"Helvetica\""
(* ^ (if st2<>NONEXIST && st1<>NONEXIST then " constraint=\"false\" " else "")  *)
 ^  "];"

let size = "fontname=\"Helvetica\"; rotate=90; margin=\"0.5,0.5\";  size=\"32.11,21.68!\"; ratio=\"fill\";" (* {bb=\"0,0,308,3371\"};"*)

let outchan = open_out "TCP1_level0_big.dot"
let _ = output_string outchan ("digraph G {\n " ^ size ^ (neatoglue "50" 400 400) ^stevensish ) ; List.iter (function t-> (output_string outchan (pp_flat_transition_edge t); output_string outchan "\n" )) t2' (* t4 *) (* t1' *) ; output_string outchan "}\n"
let _ = close_out outchan


















(* ************************************************** *)
(* older bits *)

(* remove transitions with a RST in *)
let is_not_rst (rn,label,st1,st2,recv,send,comment) = not
(
try (ignore(Str.search_forward (Str.regexp_string " RST") (recv ^ send) 0); true) with Not_found -> false
)
let no_rst_transitions = List.filter is_not_rst flat_transitions


(* remove self transitions *)
let no_rst_or_self_transitions = List.filter (function (rn,label,st1,st2,recv,send,comment) -> st1 <> st2 ) no_rst_transitions

(* remove BSD LISTEN pathology transitions *)
let no_rst_or_self_transitions' = List.filter (function (rn,label,st1,st2,recv,send,comment) -> comment <> "BSD pathology" ) no_rst_or_self_transitions




let pp_flat_transition (rn,label,st1,st2,recv,send,comment)
  = rn ^ " " ^ label ^ " " ^ pp_st st1 ^ " " ^ pp_st st2 ^ " " ^ recv ^
   " " ^ send ^ " " ^ comment




let dump () = List.iter (function t-> (print_string (pp_flat_transition t); print_newline ())) flat_transitions

(*let _ = dump () *)

(*
let t = flat_transitions (*no_rst_or_self_transitions' (* or flat_transitions for all of them *)*)
*)


(* end of older bits *)



(* this is like the Stevens layout

digraph G {

{rank=same; "SYN_RECEIVED"; "SYN_SENT";}
{rank=same; "FIN_WAIT_1"; "CLOSING";}
{rank=same; "FIN_WAIT_2"; "TIME_WAIT";}

{rank=same; "NONEXIST";"CLOSED";}

{rank=same; "ESTABLISHED"; "CLOSE_WAIT";}

CLOSED->LISTEN;
LISTEN->SYN_RECEIVED;
LISTEN->SYN_SENT;
SYN_RECEIVED->ESTABLISHED;
SYN_SENT->ESTABLISHED;
ESTABLISHED->CLOSE_WAIT;
ESTABLISHED->FIN_WAIT_1;
FIN_WAIT_1->FIN_WAIT_2;
FIN_WAIT_1->CLOSING;
FIN_WAIT_1->TIME_WAIT;
FIN_WAIT_2->TIME_WAIT;
CLOSING->TIME_WAIT;
CLOSE_WAIT->LAST_ACK;

}
*)


(*
{rank=same; "SYN_RECEIVED"; "SYN_SENT";}
{rank=same; "FIN_WAIT_1"; "CLOSING";}
{rank=same; "FIN_WAIT_2"; "TIME_WAIT";}

{rank=same; "NONEXIST";"CLOSED";}


CLOSED->LISTEN;
LISTEN->SYN_RECEIVED;
LISTEN->SYN_SENT;
SYN_RECEIVED->ESTABLISHED;
SYN_SENT->ESTABLISHED;
ESTABLISHED->CLOSE_WAIT;
ESTABLISHED->FIN_WAIT_1;


  NONEXIST     [pos = "0,0!"];
  CLOSED       [pos = "1,0!"];
  LISTEN       [pos = "1,1!"];
  SYN_SENT     [pos = "2,2!"];
  SYN_RECEIVED [pos = "0,2!"];
  ESTABLISHED  [pos = "1,3!"];
  CLOSE_WAIT   [pos = "2,3!"];
  FIN_WAIT_1   [pos = "0,4!"];
  CLOSING      [pos = "1,4!"];
  LAST_ACK     [pos = "2,4!"];
  FIN_WAIT_2   [pos = "0,5!"];
  TIME_WAIT    [pos = "1,5!"];


 *)
