(* A HOL98 specification of TCP *)

(* The core of the specification: the host labelled transition system *)

(*[ RCSID "$Id: TCP3_hostLTSScript.sml,v 1.39 2009/02/20 13:08:08 tjr22 Exp $" ]*)

(* === IMPORTANT NOTE ===
 *
 * White space and comments are significant to the typesetting code,
 * even though it is not significant to HOL.  When formatting a rule,
 * ensure that there are two blank lines before the final comment,
 * blank lines above and below the <==, and that the closing
 * parenthesis occurs after the final comment.  Otherwise you'll get
 * mysterious errors from HOLDoc.
 *
 *)

(* standard prefix *)
open HolKernel boolLib Parse

open bossLib containerTheory

open HolDoc

local open TCP1_ruleidsTheory
           TCP3_host0Theory
           TCP3_auxFnsTheory
	   TCP3_streamTheory
in end;

val Term = Parse.Term;

val _ = new_theory "TCP3_hostLTS";

val _ = Version.registerTheory "$RCSfile: TCP3_hostLTSScript.sml,v $" "$Revision: 1.39 $" "$Date: 2009/02/20 13:08:08 $";

(* make "generalising variables" warning (and others?) into an error, so we can see if
   we forget to generalise a variable in a clause, or mistype it, etc. *)
val _ = set_trace "inddef strict" 1;

(* -------------------------------------------------- *)
(*                Rule prep                           *)
(* -------------------------------------------------- *)

val _ = add_rule { block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   fixity = Infix(NONASSOC, 420),
                   pp_elements = [HardSpace 1, TOK "/*", HardSpace 1,
                                  TM (* proto *), TOK ",", HardSpace 1,
                                  TM (* cat *), HardSpace 1,
                                  TOK "*/", BreakSpace(1,0),
                                  TM, (* host0 *)
                                  BreakSpace(1,2), TOK "--", HardSpace 1,
                                  TM, (* label *)
                                  HardSpace 1, TOK "-->", BreakSpace(1,0)],
                   term_name = "host_redn0"
                   };

val _ = add_rule { block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   fixity = Infix(NONASSOC, 420),
                   pp_elements = [HardSpace 1, TOK "/*", HardSpace 1,
                                  TM (* proto *), TOK ",", HardSpace 1,
                                  TM (* cat *), HardSpace 1,
                                  TOK "*/", BreakSpace(1,0),
                                  TM, (* host0 *)
                                  BreakSpace(1,2), TOK "--", HardSpace 1,
                                  TM, (* label *)
                                  HardSpace 1, TOK "--=>", BreakSpace(1,0)],
                   term_name = "host_redn"
                   };

val _ = add_rule { block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   fixity = Infixl 199,
                   pp_elements = [BreakSpace(1,~2), TOK "<==", HardSpace 1],
                   term_name = "revimp" };

val revimp_def = xDefine "revimp" `(q <== p) = (p ==> q)` (*: @norender :*);


(*: @chapter [[host_lts_III]] Host labelled transition system.

@norender

:*)


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_segment_input_aux]] TCP Segment Input Processing Auxilliary Functions
    This text is ignored.
    @norender :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* these are typeset with deliver_in_3 *)

(* Here there are a number of checks which, if they fail, result in the segment being dropped *)
val di3_topstuff_def = Phase.phase 2 Define`
  (*: [[deliver_in_3]] initial checks :*)
  di3_topstuff sock sock' =
    ? tcp_sock.
    sock.pr = TCP_PROTO tcp_sock /\
    let cb = tcp_sock.cb in

    (*: Reset the socket's idle timer and keepalive timer to start counting from zero as
        activity is taking place on the socket: a segment is being processed. If the
        [[FIN_WAIT_2]] timer is enabled this may be reset upon processing this segment. See
        {@link [[update_idle]]} for further details :*)
    choose tt_keep' :: update_idle tcp_sock.

    sock' = sock with <| pr := TCP_PROTO (tcp_sock with
                                           <| cb := tcp_sock.cb with <| tt_keep := tt_keep' |> |>)
                      |>
`
(*: @description

TODO3

@toafter [[deliver_in_3]]


:*)
;

val di3_newackstuff_def = Phase.phase 2 Define`
  (*: [[deliver_in_3]] new ack processing, used in [[di3_ackstuff]]  :*)
  di3_newackstuff tcp_sock_0 ourfinisacked arch rttab ifds sock (sock',FIN,sto_p) =

    ? (sock'',FIN'',stop'') :: {(sock',FIN,sto_p) |
      ? t_dupacks :: (UNIV:num set).
      ? ack_lt_snd_recover :: {T;F}.
      (if ~TCP_DO_NEWRENO \/ t_dupacks < 3 then
         (sock',FIN,sto_p) = (sock,F,F)
       else if TCP_DO_NEWRENO /\ t_dupacks >= 3 /\ ack_lt_snd_recover then

         (*: Attempt to create a segment for output using the modified control block (this is a
             relational monad idiom) :*)
         stream_mlift_tcp_output_perhaps_or_fail arch rttab ifds sock (sock',FIN) /\
         sto_p = F

       else if TCP_DO_NEWRENO /\ t_dupacks >= 3 /\ ~ ack_lt_snd_recover then
         (*: The host supports NewReno-style Fast Recovery, the socket has received at least three
             duplicate [[ACK]] segments and the new [[ACK]] acknowledges at least everything upto
             [[snd_recover]], completing the recovery process. :*)
         (sock',FIN,sto_p) = (sock,F,F)

       else ASSERTION_FAILURE "di3_newackstuff" (*: impossible :*)

      )}.
   (* we never stop in the above, so always continue, but rebind sock *)
   let sock = sock'' in
   ? (sock''',FIN''',stop''') :: {(sock',FIN,sto_p) |

    (*: If the retransmit timer is set and the socket has done only one retransmit and it is still
        within the bad retransmit timer window, then because this is an [[ACK]] of new data the
        retransmission was done in error. Flag this so that the control block can be recovered
        from retransmission mode. This is known as a "bad retransmit". :*)
    ? IS_SOME_emission_time :: {T;F}.
    ? tcp_sock.
    (sock.pr = TCP_PROTO tcp_sock) /\
    (*: rebind sock in the process of updating :*)
    let sock = sock with <| pr := TCP_PROTO (tcp_sock with <| cb := tcp_sock.cb with
      <|

          (*: If the [[ACK]] segment allowed us to successfully time a segment (and update the
              round-trip time estimates) then clear the soft error flag and clear the segment
              round-trip timer in order that it can be used on a future segment. :*)
          t_softerror updated_by NONE onlywhen IS_SOME_emission_time
       |> |>) |> in

    ? ack_gt_snd_una :: {T;F}.
    ? tcp_sock.
    (sock.pr = TCP_PROTO tcp_sock) /\
    (if tcp_sock_0.st = LAST_ACK /\ ourfinisacked then
        (*: If the socket's [[FIN]] has been acknowledged and the socket is in the [[LAST_ACK]]
            state, close the socket and stop processing this segment :*)
        sock' = tcp_close arch sock /\
        FIN = F /\
        sto_p = T
     else
        (*: Otherwise, flag that [[deliver_in_3]] can continue processing the segment if need be :*)
        (sock',FIN,sto_p) = (sock,F,F))
   }.
   sock' = sock''' /\
   (FIN = (FIN'' \/ FIN''')) /\
   sto_p = stop'''


`
(*: @description

TODO3

@toafter [[deliver_in_3]]


  @internal

  note that ack > cb.snd_una here, so the ack <> cb.snd_una test is always T.  In the C source this
  is not the case, because we might have jumped into the middle of the function at process_ACK; we
  handle this (at present) with separate rules for connection establishment.

:*)
;


val di3_ackstuff_def = Define `
  (*: [[deliver_in_3]] ACK processing :*)
  di3_ackstuff tcp_sock_0 ourfinisacked arch rttab ifds sock (sock',FIN,sto_p) =
      ? ack_le_snd_una :: {T;F}.
      ? maybe_dup_ack :: {T;F}.
      if ack_le_snd_una /\ maybe_dup_ack then
        (*: Received a duplicate acknowledgement: it is an old acknowledgement (strictly less than
            [[snd_una]]) and it meets the duplicate acknowledgement conditions above.
            Do Fast Retransmit/Fast Recovery Congestion Control (RFC 2581 Ch3.2 Pg6) and
            NewReno-style Fast Recovery (RFC 2582, Ch3 Pg3), updating the control block variables
            and creating segments for transmission as appropriate. :*)

         ? t_dupacks' :: (UNIV DIFF {0:num}).
         ? ack_lt_snd_recover :: {T;F}.

          if t_dupacks' < 3  then
            (*: Fewer than three duplicate acks received so far. Just increment the duplicate ack
                counter.  We must continue processing, in case [[FIN]] is set. :*)
            (sock',FIN,sto_p) = (sock,F,F)


          else if t_dupacks' > 3 \/ (t_dupacks' = 3 /\ TCP_DO_NEWRENO /\ ack_lt_snd_recover) then
            (*: If this is the 4th or higher duplicate [[ACK]] then Fast Retransmit/Fast Recovery
                congestion control is already in progress. Increase the congestion window by another
                maximum segment size (as the duplicate [[ACK]] indicates another out-or-order
                segment has been received by the other end and is no longer consuming network
                resource), increment the duplicate [[ACK]] counter, and attempt to output another
                segment. :*)
            (*: If this is the 3rd duplicate [[ACK]], the host supports NewReno extensions and
                [[ack]] is strictly less than the fast recovery "recovered" sequence number
                [[snd_recover]], then the host is already doing NewReno-style fast recovery and has
                possibly falsely retransmitted a segment, the retransmitted segment has been lost or
                it has been delayed. Reset the duplicate [[ACK]] counter, increase the congestion
                window by a maximum segment size (for the same reason as before) and attempt to output
                another segment. NB: this will not cause a cycle to develop! The retransmission
                timer will eventually fire if recovery does not happen "fast". :*)
            stream_mlift_tcp_output_perhaps_or_fail arch rttab ifds sock (sock',FIN) /\
            sto_p = T (*: no need to process the segment any further :*)


          else if t_dupacks' = 3 /\ ~(TCP_DO_NEWRENO /\ ack_lt_snd_recover) then
           (*: If this is the 3rd duplicate segment and if the host supports NewReno extensions, a
               NewReno-style Fast Retransmit is not already in progress, then do a Fast Retransmit :*)

            (*: Attempt to create a segment for output using the modified control block (this is all
                a relational monad idiom) :*)
            stream_mlift_tcp_output_perhaps_or_fail arch rttab ifds sock (sock',FIN) /\

            sto_p = T (*: no need to process the segment any further :*)



          else ASSERTION_FAILURE "di3_ackstuff: Believed to be impossible---here for completion and safety"



        else if ack_le_snd_una /\ ~maybe_dup_ack then
          (*: Have received an old (would use the word "duplicate" if it did not have a special
              meaning) [[ACK]] and it is neither a duplicate [[ACK]] nor the [[ACK]] of a new
              sequence number thus just clear the duplicate [[ACK]] counter. :*)
          (sock',FIN,sto_p) = (sock,F,F)

        else (*: Must be: [[ack > cb.snd_una]] :*)
          (*: This is the [[ACK]] of a new sequence number---this case is handled by the auxiliary
              function {@link [[di3_newackstuff]]} :*)
          di3_newackstuff tcp_sock_0 ourfinisacked arch rttab ifds sock (sock',FIN,sto_p)
`
(*: @description

  TODO3

@toafter [[deliver_in_3]]

  @internal

  For a duplicate ack:

  amusingly, see rfc1122p94: (g) Check ACK field, ESTABLISHED state, p. 72: The ACK is a duplicate
  if SEG.ACK =< SND.UNA (the = was omitted).  Similarly, the window should be updated if: SND.UNA =<
  SEG.ACK =< SND.NXT, because SND.UNA = SEG.ACK may mean an out-of-order segment was received, which
  uses buffer space.

  the check that data = [] is necessary to avoid triggering the retransmit logic when multiple data
  segments are received while no data is being transmitted.  All the acks in this case will be the
  same, but they are not duplicates!

:*)
;

val di3_datastuff_def = Phase.phase 2 Define`
  (*: [[deliver_in_3]] data processing :*)
  (di3_datastuff (FIN_reass:bool) the_ststuff ourfinisacked sock (sock':socket,FIN:bool)):bool =

     let tcp_sock = tcp_sock_of sock in

    if tcp_sock.st = TIME_WAIT \/ (tcp_sock.st = CLOSING /\ ourfinisacked) then
        the_ststuff F sock (sock',FIN)
    else
        the_ststuff FIN_reass sock (sock',FIN)
`
(*: @description

TODO3

@toafter [[deliver_in_3]]

  @internal

  BSD Header Prediction - if the segment is either the next inorder data segment we are expecting,
                          or the pure ACK that we are expecting, then we do a fast-path processing
                          of the segment. This means that some things that usually happen later on
                          in tcp_input do not take place in this case, namely: 1) pulling rcv_up
                          along 2) send window updates (to snd_wnd, snd_wl1 etc.).
  MS: many of the conditions below may already be true due to other di3 stuff, but for now this is
      stated as per the BSD code in tcp_input.c::928-1039.

  On urgent data processing:

    FreeBSD 4.6 (and in fact Net/3) test if [[urp + LENGTH rcvq <= SB_MAX]] (which is 256K), and
    only accept an [[urp]] if this condition holds.  It's marked as a kludge, apparently to avoid
    crashing soreceive.

    Weird thing \#1: [[cb'.rcv_up]] is advanced to [[cb.rcv_nxt]] if there's no urgent pointer in
    this segment or we're not in the right state, but *NOT* if the test above fails; in that case,
    we just leave the [[rcv_up]] alone.  SB: agrees that our behaviour is correct. When the above
    test fails [[cb.rcv_up]] is pulled along with [[cb.rcv_nxt]] and [[cb.rcvurp]] is left alone
    until the new urgent pointer is within range.

    Weird thing \#2: we cannot see (on a very cursory look) why soreceive might crash.

    Weird thing \#3: [[urp]] can only be 64K, so it's highly unlikely the test would fail anyway.

    To make things a little bit less hairy, we ignore weird thing \#1 here.


  On data processing:

    is this data in-order or out-of-order or altogether out-of-window?

    does 'window' here mean the one we've currently advertised, or the space we actually have?
    arbitrarily, the former

    again, like URG, this only happens if not TCPS_HAVERCVDFIN, about which Keith and BSD have an
    ongoing debate

    Q: what happens if data arrives after a FIN?  Does the socket complain when TCP tries to add
    stuff to its receive queue?
    A: if we're in TIME_WAIT, then it gets ignored.  Dunno about other cases.

:*)
;

val di3_ststuff_def = Phase.phase 2 Define `
  (*: [[deliver_in_3]] TCP state change processing :*)
  di3_ststuff FIN_reass ourfinisacked sock (sock',stop') =

    (*: The entirety of this function is an encoding of the TCP State Transition Diagram (as it is, not as it is traditionally depicted)
        post-[[SYN_SENT]] state. It specifies for given start state and set of conditions (all or
        some of which are affected by the processing of the current segment), which state the TCP
        socket should be moved into next :*)

      (*: If the processing of the current segment has led to [[FIN_reass]] being asserted then the
          whole data stream from the other end has been received and reconstructed, including
          the final [[FIN]] flag. The socket should have its read-half flagged as shut down, \ie,
          [[cantrcvmore = T]], otherwise the socket is not modified. :*)
      let sock = (if FIN_reass then
         sock with <| cantrcvmore := T |>
       else sock) in
      let tcp_sock = tcp_sock_of sock in
      let cont = (sock' = sock /\ stop' = F) in
      let enter_TIME_WAIT = (sock' = sock with
              <| pr := TCP_PROTO (tcp_sock with
                  <| st := TIME_WAIT;
                     cb :=  tcp_sock.cb with <| tt_keep := NONE |>
                  |>)
              |> /\
        stop' = F) in

      (*: State Transition Diagram encoding: :*)
      (*: The state transition encoding, case-split on the current state and whether a [[FIN]] from
          the remote end has been reassembled :*)
      case ((tcp_sock_of sock).st, FIN_reass) of

          (* REMARK we are very loose here *)
       (SYN_RECEIVED,F) -> (*: In [[SYN_RECEIVED]] and have not received a [[FIN]] :*)
          (? ack_ge_suc_iss :: {T;F}.
          if ack_ge_suc_iss then
            (*: This socket's initial [[SYN]] has been acknowledged :*)
            sock' = sock with <| pr := TCP_PROTO (tcp_sock with
                <| st := if ~sock.cantsndmore then
                           ESTABLISHED (*: socket is now fully connected :*)
                         else
                           (*: The connecting socket had it's write-half shutdown by [[shutdown()]]
                               forcing a [[FIN]] to be emitted to the other end :*)
                           if ourfinisacked then
                             (*: The emitted [[FIN]] has been acknowledged :*)
                             FIN_WAIT_2
                           else
                             (*: Still waiting for the emitted [[FIN]] to be acknowledged :*)
                             FIN_WAIT_1
               |>) |> /\
            stop' = F
          else
            (*: Not a valid path :*)
            stop') ||

       (SYN_RECEIVED,T) ->  (*: In [[SYN_RECEIVED]] and have received a [[FIN]] :*)
          (*: Enter the [[CLOSE_WAIT]] state, missing out [[ESTABLISHED]] :*)
          sock' = sock with <| pr := TCP_PROTO (tcp_sock with <| st := CLOSE_WAIT |>) |> /\
          stop' = F ||

       (ESTABLISHED,F)  ->  (*: In [[ESTABLISHED]] and have not received a [[FIN]] :*)
          (*: Doing common-case data delivery and acknowledgements. Remain in [[ESTABLISHED]]. :*)
          cont ||


       (ESTABLISHED,T)  ->  (*: In [[ESTABLISHED]] and received a [[FIN]] :*)
          (*: Move into the [[CLOSE_WAIT]] state :*)
          sock' = sock with <| pr := TCP_PROTO (tcp_sock with <| st := CLOSE_WAIT |>) |> /\
          stop' = F ||


       (CLOSE_WAIT,F)   ->  (*: In [[CLOSE_WAIT]] and have not received a [[FIN]] :*)
         (*: Do nothing and remain in [[CLOSE_WAIT]]. The socket has its receive-side shut down due to
             the [[FIN]] it received previously from the remote end. It can continue to emit
             segments containing data and receive acknowledgements back until such a time that it
             closes down and emits a [[FIN]] :*)
         cont ||

       (CLOSE_WAIT,T)   ->  (*: In [[CLOSE_WAIT]] and received (another) [[FIN]] :*)
         (*: The duplicate [[FIN]] will have had a new sequence number to be valid and reach this
             point; RFC793 says "ignore" it so do not change state! If it were a duplicate with the
             same sequence number as the previously accepted [[FIN]], then the [[deliver_in_3]]
             acknowledgement processing function [[di3_ackstuff]] would have dropped it. :*)
         cont ||

       (FIN_WAIT_1,F)   ->  (*: In [[FIN_WAIT_1]] and have not received a [[FIN]] :*)
          (*: This socket will have emitted a [[FIN]] to enter [[FIN_WAIT_1]]. :*)
          if ourfinisacked then
            (*: If this socket's [[FIN]] has been acknowledged, enter state [[FIN_WAIT_2]] and start
                the [[FIN_WAIT_2]] timer. The timer ensures that if the other end has gone away
                without emitting a [[FIN]] and does not transmit any more data the socket is closed
                rather left dangling. :*)
            sock' = sock with <| pr := TCP_PROTO (tcp_sock with <| st := FIN_WAIT_2 |>) |> /\
            stop' = F

          else
            (*: If this socket's [[FIN]] has not been acknowledged then remain in [[FIN_WAIT_1]] :*)
            cont ||

       (FIN_WAIT_1,T)   ->  (*: In [[FIN_WAIT_1]] and received a [[FIN]] :*)
          if ourfinisacked then
            (*: ...and this socket's [[FIN]] has been acknowledged then the connection has been
                closed successfully so enter [[TIME_WAIT]]. Note: this differs slightly from the
                behaviour of BSD which momentarily enters the [[FIN_WAIT_2]] and after a little more
                processing enters [[TIME_WAIT]] :*)
            enter_TIME_WAIT
          else
            (*: If this socket's [[FIN]] has not been acknowledged then the other end is attempting
                to close the connection simultaneously (a simultaneous close). Move to the
                [[CLOSING]] state :*)
            sock' = sock with <| pr := TCP_PROTO (tcp_sock with <| st := CLOSING |>) |> /\
            stop' = F ||

       (FIN_WAIT_2,F)   ->  (*: In [[FIN_WAIT_2]] and have not received a [[FIN]] :*)
          (*: This socket has previously emitted a [[FIN]] which has already been acknowledged. It
              can continue to receive data from the other end which it must acknowledge. During
              this time the socket should remain in [[FIN_WAIT_2]] until such a time that it
              receives a valid [[FIN]] from the remote end, or if no activity occurs on the
              connection the [[FIN_WAIT_2]] timer will fire, eventually closing the socket :*)
         cont ||

       (FIN_WAIT_2,T)   ->  (*: In [[FIN_WAIT_2]] and have received a [[FIN]] :*)
          (*: Connection has been shutdown so enter [[TIME_WAIT]] :*)
          enter_TIME_WAIT ||

       (CLOSING,F)      ->   (*: In [[CLOSING]] and have not received a [[FIN]] :*)
          if ourfinisacked then
            (*: If this socket's [[FIN]] has been acknowledged (common-case), enter [[TIME_WAIT]] as
                the connection has been successfully closed :*)
            enter_TIME_WAIT
          else
            (*: Otherwise, the other end has not yet received or processed the [[FIN]] emitted by
                this socket. Remain in the [[CLOSING]] state until it does so. Note: if the
                previosuly emitted [[FIN]] is not acknowledged this socket's retransmit timer will
                eventually fire causing retransmission of the [[FIN]]. :*)
            cont ||

       (CLOSING,T)      ->  (*: In [[CLOSING]] and have received a [[FIN]] :*)
          (*: The received [[FIN]] is a duplicate [[FIN]] with a new sequence number so as per RFC793 is
              ignored -- if it were a duplicate with the same sequence number as the previously
              accepted [[FIN]], then the [[deliver_in_3]] acknowledgement processing function
              [[di3_ackstuff]] would have dropped it. :*)
           if ourfinisacked then
             (*: If this socket's [[FIN]] has been acknowledged then the connection is now
                 successfully closed, so enter [[TIME_WAIT]] state :*)
              enter_TIME_WAIT
           else
             (*: Otherwise, ignore the new [[FIN]] and remain in the same state :*)
             cont ||

       (LAST_ACK,F)     ->  (*: In [[LAST_ACK]] and have not received a [[FIN]] :*)
          (*: Remain in [[LAST_ACK]] until this socket's [[FIN]] is acknowledged. Note: eventually
              the retransmit timer will fire forcing the [[FIN]] to be retransmitted. :*)
          cont ||

       (LAST_ACK,T)     ->  (*: In [[LAST_ACK]] and have received a [[FIN]] :*)
          (*: This transition is handled specially at the end of [[di3_newackstuff]] at which point
              processing stops, thus this transition is not possible :*)
          ASSERTION_FAILURE "di3_ststuff" (*: impossible :*) ||

       (TIME_WAIT,F)    ->  (*: In [[TIME_WAIT]] and have not received a [[FIN]] :*)
          (*: Remaining in [[TIME_WAIT]] until the \wasverb{2MSL} timer expires :*)
          cont ||

       (TIME_WAIT,T)    ->  (*: In [[TIME_WAIT]] and have received a [[FIN]] :*)
          (*: Remaining in [[TIME_WAIT]] until the \wasverb{2MSL} timer expires :*)
          cont
`
(*: @description

TODO3

@toafter [[deliver_in_3]]

:*)
;

val di3_socks_update_def = Phase.phase 2 Define`
  (*: [[deliver_in_3]] socket update processing :*)
  di3_socks_update sid socks socks' =

   let sock_1 = socks ' sid in
   ?tcp_sock_1.
   TCP_PROTO(tcp_sock_1) = sock_1.pr /\

  (*: Socket [[sock_1]] referenced by identifier [[sid]] has just finished connection establishement
      and either there is another socket with [[sock_1]] on its pending connections queue and this
      is the completion of a passive open, or there is not another socket and this is the completion
      of a simultaneous open. See the inline comment in {@link [[deliver_in_3]]} for further
      details. :*)

   let interesting = \sid'.
         sid' <> sid /\
         case (socks ' sid').pr of
            UDP_PROTO udp_sock -> F
         || TCP_PROTO(tcp_sock') ->
              case tcp_sock'.lis of
                 NONE -> F
              || SOME lis ->
                   sid IN' lis.q0 in

   let interesting_sids = (FDOM socks) INTER interesting in

   if interesting_sids <> {} then
      (*: There exists another socket [[sock']] that is listening and has socket [[sock_1]] referenced by
          [[sid]] on its queue of incomplete connections [[lis.q0]]. :*)
      ?sid' sock' tcp_sock' lis q0L q0R.
      sid' IN interesting_sids /\
      sock' = socks ' sid' /\
      sock'.pr = TCP_PROTO tcp_sock' /\
      sid' <> sid /\
      tcp_sock'.lis = SOME lis /\
      lis.q0 = APPEND q0L (sid :: q0R) /\

      (*: Choose non-deterministically whether there is room on the queue of completed connections :*)
      choose ok :: accept_incoming_q lis.

      if ok then
        (*: If there is room, then remove socket [[sid]] from the queue of incomplete connections
            and add it to the queue of completed connections. :*)
        let lis' = lis with <| q0 := APPEND q0L q0R;
                               q := sid :: lis.q |> in
        let cb' = tcp_sock_1.cb in

        (*: Update both the newly connected socket and the listening socket :*)
        socks' = socks |++
                       [(sid, sock_1 with <| pr := TCP_PROTO(tcp_sock_1 with <| cb := cb' |>) |>);
                        (sid', sock' with <| pr := TCP_PROTO(tcp_sock' with <| lis := SOME lis' |>) |>)]
      else
        (*: ...otherwise there is no room on the listening socket's completed connections queue, so
           drop the newly connected socket and remove it from the listening socket's queue of
           incomplete connections. Note: the dropped connection is not sent a [[RST]] but a [[RST]]
           is sent upon receipt of further segments from the other end as the socket entry has gone
           away. :*)
        (* Note that the above note needs to be verified by testing. *)
        let lis' = lis with <| q0 := APPEND q0L q0R |> in
        socks' = socks |+ (sid', sock' with <| pr := TCP_PROTO(tcp_sock' with <| lis := SOME lis' |>) |>)

   else
     (*: There is no such socket with socket [[sid]] on its queue of incomplete connections, thus
         socket [[sid]] was involved in a simultaneous open. Do not update any socket. :*)
      socks' = socks

`
(*: @description

TODO3

@toafter [[deliver_in_3]]

:*)
;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[pselect_support]] ALL Some [[pselect()]] support functions
    This text is ignored.
    @norender :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* these are typeset with pselect *)

val soreadable_def = Phase.phase 1 Define`
(*: check whether a socket is readable :*)
  soreadable arch sock SS b =
    case sock.pr of
      TCP_PROTO(tcp) -> (
        ? rcvq.
        (if exists_quad_of sock then
            let (i1,p1,i2,p2) = quad_of sock in
            ? S0 s. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2), s)] /\
            ? peek inline flgs s'.
            read (i1,p1,i2,p2) peek inline (flgs,rcvq) s s'
        else
            rcvq = []) /\
        b = (
            (LENGTH rcvq >= sock.sf.n(SO_RCVLOWAT) \/
            sock.cantrcvmore \/
            (linux_arch arch /\ tcp.st = CLOSED) \/
            (tcp.st = LISTEN /\
             ?lis. tcp.lis = SOME lis /\
                   lis.q <> []) \/
            sock.es <> NONE))) ||
      UDP_PROTO(udp) ->
       b = (udp.rcvq <> [] \/ sock.es <> NONE \/ (sock.cantrcvmore /\ ~windows_arch arch))
`
(*:

@description

A TCP socket [[sock]] is readable if: (1) the length of its receive queue is greater than or equal
to the minimum number of bytes for socket input operations, [[sf.n(SO_RCVLOWAT)]]; (2) it has been
shut down for reading; (3) on Linux, it is in the [[CLOSED]] state; it is in the [[LISTEN]] state
and has at least one connection on its completed connection queue; or (4) it has a pending error.

A UDP socket [[sock]] is readable if its receive queue is not empty, it has a pending error, or it
has been shutdown for reading.

@variation Linux

On all OSes, attempting to read from a closed socket yields an immediate error.  Only on Linux,
however, does [[soreadable]] return [[T]] in this case.

@variation WinXP

The socket will not be readable if it has been shutdown for reading.

@toafter [[pselect_1]]

:*)
;

val sowriteable_def = Phase.phase 1 Define`
(*: check whether a socket is writable :*)
  sowriteable arch sock SS b=
    case sock.pr of
      TCP_PROTO(tcp) -> (
        ? sndq.
        (if exists_quad_of sock then
            let (i1,p1,i2,p2) = quad_of sock in
            ? S0 s. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2), s)] /\
            ? peek inline flgs s'.
            read (i2,p2,i1,p1) peek inline (flgs,sndq) s s'
        else
            sndq = []) /\
        b = (
        ((tcp.st IN {ESTABLISHED; CLOSE_WAIT} /\
          sock.sf.n(SO_SNDBUF) - LENGTH sndq  >= sock.sf.n(SO_SNDLOWAT)) \/ (* change to send_buffer_space *)
        (if linux_arch arch then ~sock.cantsndmore else sock.cantsndmore) \/
        (linux_arch arch /\ tcp.st = CLOSED) \/
        sock.es <> NONE))) ||
      UDP_PROTO(udp) -> T
`
(*:

@description

TODO3: document the correct version

@variation Linux

On all OSes, attempting to write to a closed socket yields an immediate error.  Only on Linux,
however, does [[sowriteable]] return [[T]] in this case.

On Linux, if the outgoing half of the connection has been closed by the application, the socket
becomes non-writeable, whereas on other OSes it becomes writeable (because an immediate error would
result from writing).

@internal

In our previous UDP specification, a UDP socket was writeable if the outqueue was not full; this is
not part of the host state in the present spec (TODO: really??), and so here we are simply always
writeable.  UNPp154 suggests that a UDP socket is always writable anyway.

@toafter [[pselect_1]]

:*)
;

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[socket_calls]] Host LTS: Socket Calls

TODO3

:*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* -------------------------------------------------- *)
(*                Host transition rules               *)
(* -------------------------------------------------- *)

(* The standard format for a rule is:

  (! universally-quantified variables.

  rule_name /* rule_proto, rule_category (* optional rule description *) */
    rule_lhs
  -- rule_label -->
    rule_rhs

  <==

    rule_side_condition


  (*:
  optional rule commentary
  :*)
  )

Note that blank lines are to be respected, and preferably indents also. NB: two blank lines should
appear after the last side condition and before the optional rule commentary.

LaTeX is permitted in comments, and Hol source can be enclosed in double square brackets like this:
[[Flags(T,F)]]. *)

open Net_Hol_reln;
val (host_redn0_rules, host_redn0_ind, host_redn0_cases) =
  Net_Hol_reln`

(*:

@section [[accept]] TCP [[accept()]]
 \[ <[accept: fd -> fd * (ip * port)]> \]

  [[accept(fd)]] returns the next connection available on the completed connections queue for the
  listening TCP socket referenced by file descriptor [[fd]].  The returned file descriptor [[fd]]
  refers to the newly-connected socket; the returned [[ip]] and [[port]] are its remote address.
  [[accept()]] blocks if the completed connections queue is empty and the socket does not have the
  [[O_NONBLOCK]] flag set.

  Any pending errors on the new connection are ignored, except for [[ECONNABORTED]] which causes
  [[accept()]] to fail with [[ECONNABORTED]].

  Calling [[accept()]] on a UDP socket fails: UDP is not a connection-oriented protocol.

@errors

  A call to [[accept()]] can fail with the errors below, in which case the corresponding exception
  is raised:

  @error [[EAGAIN]] The socket has the [[O_NONBLOCK]] flag set and no connections are available on
  the completed connections queue.

  @error [[ECONNABORTED]] The connection at the head of the completed connections queue has been
  aborted; the socket has been shutdown for reading; or the socket has been closed.

  @error [[EINVAL]] Ths socket is not accepting connections, \ie,  it is not in the [[LISTEN]] state,
  or is a UDP socket.

  @error [[EMFILE]] The maximum number of file descriptors allowed per process are already open for
  this process.

  @error [[EOPNOTSUPP]] The socket type of the specified socket does not support accepting
  connections. This error is raised if [[accept()]] is called on a UDP socket.

  @errorinclude [[misc]] [[ENFILE]]
  @errorinclude [[misc]] [[ENOBUFS]]
  @errorinclude [[misc]] [[ENOMEM]]
  @errorinclude [[misc]] [[EINTR]]
  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  [[accept()]] is called and immediately returns a connection: [[accept_1]]; [[return_1]]

  [[accept()]] is called and blocks; a connection is completed and the call returns: [[accept_2]];
  [[deliver_in_99]]; [[deliver_in_1]]; [[accept_1]]; [[return_1]]

@api

  \begin{tabular}{ll}
    Posix:  &  |int accept(int socket, struct sockaddr *restrict address,| \\
            &  |           socklen_t *restrict address_len);| \\
    FreeBSD:&  |int accept(int s, struct sockaddr *addr, socklen_t *addrlen);| \\
    Linux:  &  |int accept(int s, struct sockaddr *addr, socklen_t *addrlen);| \\
    WinXP:  &  |SOCKET accept(SOCKET s, struct sockaddr* addr, int* addrlen);| \\
  \end{tabular}\\

  In the Posix interface:
  \begin{itemize}

    \item |socket| is the listening socket's file descriptor, corresponding to the [[fd]]
     argument of the model;

    \item the returned |int| is either non-negative, \ie,  a file descriptor referring to the
     newly-connected socket, or |-1| to indicate an error, in which case the error code is
     in |errno|.  On WinXP an error is indicated by a return value of
     |INVALID_SOCKET|, not |-1|, with the actual error code available through a
     call to |WSAGetLastError()|.

    \item |address| is a pointer to a |sockaddr| structure of length
    |address_len| corresponding to the [[ip*port]] returned by the model [[accept()]]. If
    |address| is not a null pointer then it stores the address of the peer for the accepted
    connection. For the model [[accept()]] it will actually be a |sockaddr_in| structure;
    the peer IP address will be stored in the |sin_addr.s_addr| field, and the peer port
    will be stored in the |sin_port| field. If |address| is a null pointer then the
    peer address is ignored, but the model [[accept()]] always returns the peer address. On input
    the |address_len| is the length of the |address| structure, and on output it is
    the length of the stored address.

  \end{itemize}


@modeldetails

  If the [[accept()]] call blocks then state [[Accept2(sid)]] is entered, where [[sid]] is the index
  of the socket that [[accept()]] was called upon.

  The following errors are not included in the model:
  \begin{itemize}

    \item |EFAULT| signifies that the pointers passed as either the |address| or
     |address_len| arguments were inaccessible.  This is an artefact of the C interface to
     [[accept()]] that is excluded by the clean interface used in the model.

    \item |EPERM| is a Linux-specific error code described by the Linux man page as
     "Firewall rules forbid connection". This is outside the scope of what is modelled.

    \item |EPROTO| is a Linux-specific error code described by the man page as "Protocol
     error". Only TCP and UDP are modelled here; the only sockets that can exist in the model are
     bound to a known protocol.

    \item |WSAECONNRESET| is a WinXP-specific error code described in the MSDN page as "An
    incoming connection was indicated, but was subsequently terminated by the remote peer prior to
    accepting the call." This error has not been encountered in exhaustive testing.

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}


  From the Linux man page:
       Linux [[accept()]] passes already-pending network errors on the new socket as
       an error code from accept.  This behaviour differs from other BSD socket implementations.
       For reliable operation the application should detect the network errors defined for the
       protocol after accept and treat them like EAGAIN by retrying. In case of TCP/IP these are
       ENETDOWN, EPROTO, ENOPROTOOPT, EHOSTDOWN, ENONET, EHOSTUNREACH, EOPNOTSUPP, and
       ENETUNREACH.

       This is currently not modelled, but will be looked at when the Linux semantics are
       investigated.


:*)

   (!h lbl rc ts t files socks tid d fds fds'
     fd fid ff sid sf is1 i1' p1 i2 p2 es cb cb' q
     fd' fid' sid' sf' es'
     lis lis' cantsndmore cantrcvmore cantsndmore' cantrcvmore' SS MM.

   accept_1 /* rp_tcp, rc (*: Return new connection; either immediately or from a blocked state. :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(t,d));
               fds := fds;
               files := files;
               socks :=
                 socks |++
                   [(sid ,Sock(SOME fid,sf,is1,SOME p1,NONE,NONE,es,cantsndmore,cantrcvmore,
                               TCP_Sock(LISTEN,cb,SOME lis)));
                    (sid',Sock(NONE,sf',SOME i1',SOME p1,SOME i2,SOME p2,es',cantsndmore',cantrcvmore',
                               TCP_Sock(ESTABLISHED,cb',NONE)))] |>,
     SS,MM)
   -- lbl -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (fd',(i2,p2))),sched_timer));
               fds := fds';
               files := files |++ [(fid',File(FT_Socket(sid'),ff_default))];
               socks :=
                 socks |++
                   [(sid ,Sock(SOME fid,sf,is1,SOME p1,NONE,NONE,es,cantsndmore,cantrcvmore,
                               TCP_Sock(LISTEN,cb,SOME lis')));
                    (sid',Sock(SOME fid',sf',SOME i1',SOME p1,SOME i2,SOME p2,es',
                               cantsndmore',cantrcvmore', TCP_Sock(ESTABLISHED,cb',NONE)))] |>,
     SS,MM)

  <==

   $\/
     (t = Run /\
      lbl = Lh_call (tid,(accept fd)) /\
      rc = fast succeed /\
      fid = fds ' fd  /\
      fd IN FDOM fds /\
      FAPPLY files fid = File(FT_Socket(sid),ff)
      (* TODO: sid does not even have to be in the LISTEN state on FreeBSD :( *)
     )
     (t = Accept2(sid) /\
       lbl = Lh_tau /\
       rc = slow urgent succeed
     ) /\
   (* we add connections to the head of the queue, so want to take the new connection from the tail *)
   lis.q = APPEND q [sid'] /\
   lis'.q = q /\
   lis'.q0 = lis.q0 /\ lis'.qlimit = lis.qlimit /\ (* TODO: temporary measure for now, to avoid using
                                                      'with' with lis type, as per MN's comments *)
   (sid <> sid') /\ (* redundant? *)
   es' <> SOME ECONNABORTED /\ (* TODO: update this in light of accept_4 *)
   fid' NOTIN ((FDOM files) UNION {fid}) /\
   nextfd h.arch fds fd' /\
   fds' = fds |+ (fd', fid') /\
   (!i1. SOME i1 = is1 ==> i1 = i1') (* TODO: reorder to fit description *)


   (*:

   @description

   This rule covers two cases: (1) the completed connection queue is non-empty when [[accept(fd)]] is
   called from a thread [[tid]] in the [[Run]] state, where [[fd]] refers to a TCP socket [[sid]],
   and (2) a previous call to [[accept(fd)]] on socket [[sid]] blocked, leaving its calling thread
   [[tid]] in state [[Accept2(sid)]], and a new connection has become available.

   In either case the listening TCP socket [[sid]] has a connection [[sid']] at the head of its
   completed connections queue [[sid'::q]]. A socket entry for [[sid']] already exists in the host's
   finite map of sockets, [[socks]]$\oplus\dots$. The socket is [[ESTABLISHED]], is not shutdown for
   reading, and is only missing a file description association that would make it accessible via the
   sockets interface.

   A new file description record is created for connection [[sid']], indexed by a new [[fid']], and
   this is added to the host's finite map of file descriptions [[files]].  It is assigned a default
   set of file flags, [[ff_default]]. The socket entry [[sid']] is completed with its file
   association [[SOME fid']] and [[sid']] is removed from the head of the completed connections
   queue.

   When the listening socket [[sid]] is bound to a local IP address [[i1]], the accepted socket
   [[sid']] is also bound to it.

   Finally, the new file descriptor [[fd']] is created in an architecture-specific way using the
   auxiliary [[nextfd]], and an entry mapping [[fd']] to [[fid']] is added to the host's finite map
   of file descriptors.  If the calling thread was previously blocked in state [[Accept2(sid)]] it
   proceeds via a [[Lh_tau]] transition, otherwise by a [[Lh_call(tid, (accept fd))]] transition.
   The thread is left in state [[Ret (OK (fd',(i2,p2)))]] to return the file descriptor and remote
   address of the accepted connection in response to the original [[accept()]] call.

   If the new socket [[sid']] has error [[ECONNABORTED]] pending in its error field [[es']], this is
   handled by rule [[accept_5]]. All other pending errors on [[sid']] are ignored, but left as the
   socket's pending error.

   @internal

   If the queue of completed connections is non-empty and the user either calls [[accept()]] or has
   already made a blocking call to [[accept()]] (and is therefore now in state [[Accept2]]), then a
   new open file description is allocated for the socket, and a new file descriptor made to point to
   the open file description.  Pending errors are ignored, except for [[ECONNABORTED]], of the
   provenance of which the present writer is uncertain (see [[accept_5]]).

   Note that cantsndmore is not constrained, because e.g. under BSD's "can listen() anywhere" feature,
   could have a listening socket with cantsndmore set that can still accept limited connections.

   This rule is a combination of (the old) [[accept_1]] and [[accept_1a]].  DISCUSSION POINT: is it
   clear?

   Notice that we require that the source ip and port are the same for the listening socket and the
   accepted socket.  I cannot see this in POSIX; needs to be checked with BSD and/or Linux.

   POSIX: "shall extract...".
   POSIX: "until a connection is present...".

   slow version SHOULD BE URGENT.

   Michael points out that we should check if we actually can allocate a fresh fd.

   SB: The linux man page reads: "Linux accept passes already-pending network errors on the new
   socket as an error code fom accept. This behaviour differs from the other BSD socket
   implementations..."

   :*)

   )

/\

   (!h ts tid d
     fd fid ff sid cantrcvmore
     SS MM.

   accept_2 /* rp_tcp, block (*: Block waiting for connection :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,(accept fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Accept2(sid),never_timer)) |>,SS,MM)

   <==

   fd IN FDOM h.fds /\
   fid = h.fds ' fd /\
   FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
   ff.b(O_NONBLOCK) = F /\
   sid IN FDOM h.socks /\
   (?sf is1 p1 cb lis es.
       h.socks ' sid = Sock(SOME fid,sf,is1,SOME p1,NONE,NONE,es,F,cantrcvmore,
                            TCP_Sock(LISTEN,cb,SOME lis)) /\
       lis.q = [])


   (*:

   @description

   A blocking [[accept()]] call is performed on socket [[sid]] when no completed incoming
   connections are available. The calling thread blocks until a new connection attempt completes
   successfully, the call is interrupted, or the process runs out of file descriptors.

   From thread [[tid]], which is initially in the [[Run]] state, [[accept(fd)]] is called where
   [[fd]] refers to listening TCP socket [[sid]] which is bound to local port [[p1]], is not
   shutdown for reading and is in blocking mode: [[ff.b(O_NONBLOCK)=F]]. The socket's queue of
   completed connections is empty, [[q := []]], hence the [[accept()]] call blocks waiting for a
   successful new connection attempt, leaving the calling thread state [[Accept2(sid)]].

   Socket [[sid]] might not be bound to a local IP address, i.e. [[is1]] could be [[NONE]]. In this
   case the socket is listening for connection attempts on port [[p1]] for all local IP addresses.

   @internal

   If the queue of completed connections is empty and the user calls [[accept()]] without first
   setting the file flags to non-blocking, the call blocks until a connection arrives.

   POSIX: "shall block...".

   :*)
   )

/\

   (!h ts tid d
     fd fid ff sid cantsndmore cantrcvmore
     SS MM.

   accept_3 /* rp_tcp, fast fail (*: Fail with [[EAGAIN]]: no pending connections and non-blocking
     semantics set :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,(accept fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EAGAIN),sched_timer)) |>,SS,MM)

   <==

   fd IN FDOM h.fds /\
   h.fds ' fd = fid /\
   FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
   ff.b(O_NONBLOCK) = T /\
   sid IN FDOM h.socks /\
   (?sf is1 p1 cb lis es.
      h.socks ' sid = Sock(SOME fid,sf,is1,SOME p1,NONE,NONE,es,cantsndmore,cantrcvmore,
                           TCP_Sock(LISTEN,cb,SOME lis)) /\
      lis.q = [])


   (*:

   @description

   A non-blocking [[accept()]] call is performed on socket [[sid]] when no completed incoming
   connections are available. Error [[EAGAIN]] is returned to the calling thread.

   From thread [[tid]], which is initially in the [[Run]] state, [[accept(fd)]] is called where
   [[fd]] refers to a listening TCP socket [[sid]] which is bound to local port [[p1]], not shutdown
   for writing, and in non-blocking mode: [[ff.b(O_NONBLOCK) = T]]. The socket's queue of completed
   connections is empty, [[q := []]], hence the [[accept()]] call returns error [[EAGAIN]],
   leaving the calling thread state [[Ret (FAIL EAGAIN)]] after a [[Lh_call(tid,accept(fd))]]
   transition.

   Socket [[sid]] might not be bound to a local IP address, i.e. [[is1]] could be [[NONE]]. In this
   case the socket is listening for connection attempts on port [[p1]] for all local IP addresses.

   @internal

   If the queue of completed connections is empty and the user calls [[accept()]] with the file
   flags set to non-blocking, the call immmediately fails with the error [[EAGAIN]] (a POSIX alias
   of [[EWOULDBLOCK]]).

   POSIX: "shall fail...".

   :*)
   )

/\

   (!h ts socks tid d t lbl rc
     fd fid ff sid sf is1 p1 es st cb lis
     cantsndmore cantrcvmore
     SS MM.

   accept_4 /* rp_tcp, rc (*: Fail with [[ECONNABORTED]]: the listening socket has [[cantsndmore]] set
     or has become [[CLOSED]]. Returns either immediately or from a blocked state. :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(t,d));
               socks :=
                 socks |++
                   [(sid ,Sock(SOME fid,sf,is1,SOME p1,NONE,NONE,es,cantsndmore,cantrcvmore,
                               TCP_Sock(st,cb,SOME lis)))] |>,
     SS,MM)
   -- lbl -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ECONNABORTED),sched_timer));
               socks :=
                 socks |++
                   [(sid ,Sock(SOME fid,sf,is1,SOME p1,NONE,NONE,es,cantsndmore,cantrcvmore,
                               TCP_Sock(st,cb,SOME lis)))] |>,
     SS,MM)

   <==

   $\/
    (t = Run /\
     st = LISTEN /\
     cantsndmore = T /\
     lbl = Lh_call (tid,accept(fd)) /\
     rc = fast fail /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff)
    )
    (t = Accept2(sid) /\
     ((cantrcvmore = T /\ st = LISTEN) \/
      (st = CLOSED)) /\
     lbl = Lh_tau /\
     rc = slow urgent fail
    )


   (*:

   @description

   This rule covers two cases: (1) an [[accept(fd)]] call is made on a listening TCP socket [[sid]],
   referenced by [[fd]], with [[cantsndmore]] set, and (2) a previous call to [[accept()]] on socket
   [[sid]] blocked, leaving a thread [[tid]] in state [[Accept2(sid)]], but the socket has since
   either entered the [[CLOSED]] state, or had [[cantrcvmore]] set. In both cases, [[ECONNABORTED]]
   is returned.

   This situation will arise only when a thread calls [[close()]] on the listening socket while
   another thread is blocking on an [[accept()]] call, or if [[listen()]] was originally called on a
   socket which already had [[cantrcvmore]] set. The latter can occur in BSD, which allows
   [[listen()]] to be called in any (non [[CLOSED]] or [[LISTEN]]) state, though should never happen
   under typical use.

   If the calling thread was previously blocked in state [[Accept2(sid)]], it proceeds via an
   [[Lh_tau]] transition, otherwise by a [[Lh_call(tid,accept(fd))]] transition. The thread is
   left in state [[Ret (FAIL ECONNABORTED)]] to return the error [[ECONNABORTED]] in response to
   the initial [[accept()]] call.

   Note that this rule is not correct when dealing with the FreeBSD behaviour which allows any
   socket to be placed in the [[LISTEN]] state.

   @internal

   TODO: MF: I'm confused by this rule. (1) how does it interact with close_8 which closes a
   listening socket, and (2) if the socket is in state [[CLOSED]] how does it have a listen queue
   [[SOME lis]]?

   POSIX: "shall fail..." if "A connection has been aborted".  XSH2.10 says that this error is a
   pending error for a socket if a connection is *locally* aborted, but says no more than that.  See
   rationale.

   slow version SHOULD BE URGENT.

   http://archives.neohapsis.com/archives/postfix/2001-03/0125.html (and lots of other hits for
   googling "ECONNABORTED") gives a discussion: it's a bit weird, but can happen if remote end
   closes before the connection is accepted.  It could be wrong behaviour.  In any case, this is not
   "local" as POSIX says.  Also note that EPROTO is sometimes returned when ECONNABORTED is meant.

   MS: this discussion appears to be dated - in particular (1) it refers to BSD 4.2, where we are using
   4.6, and (2) the code that the discussion refers to is most certainly *not* in 4.6. The only
   circumstances under which accept() returns ECONNABORTED are if:
     (1) The listening socket has cantrcvmore set.
     (2) The listening socket has state SS_ISDISCONNECTED (equating to being in CLOSED state).
   (note the second condition is only applicable if the user was already blocking on an accept()).

   Should the CLOSED state really have SOME i1', SOME p1?  Are is2 and ps2 specified too?

   :*)
   )


/\

   (!h ts tid d t lbl rc
     fd fid ff sid tcp_sock
     SS MM.

   accept_5 /* rp_tcp, rc (*: Fail with [[EINVAL]]: socket not in LISTEN state :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(t,d)) |>,SS,MM)
   -- lbl -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINVAL),sched_timer)) |>,SS,MM)

   <==

   $\/
    (t = Run /\
     lbl = Lh_call (tid,accept(fd)) /\
     rc = fast fail /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff)
    )
    (t = Accept2(sid) /\
     lbl = Lh_tau /\
     rc = slow urgent fail
     ) /\
    sid IN FDOM h.socks /\
    TCP_PROTO(tcp_sock) = (h.socks ' sid).pr /\
    tcp_sock.st <> LISTEN


   (*:

   @description


   It is not valid to call [[accept()]] on a socket that is not in the
   [[LISTEN]] state.

   This rule covers two cases: (1) on the non-listening TCP socket [[sid]], [[accept()]] is called
   from a thread [[tid]], which is in the [[Run]] state, and (2) a previous call to [[accept()]] on
   TCP socket [[sid]] blocked because no completed connections were available, leaving thread
   [[tid]] in state [[Accept2(sid)]] and after the [[accept()]] call blocked the socket changed to a
   state other than [[LISTEN]].

   In the first case the [[accept(fd)]] call on socket [[sid]], referenced by file descriptor
   [[fd]], proceeds by a [[Lh_call(tid,accept(fd))]] transition and in the latter by a [[Lh_tau]]
   transition. In either case, the thread is left in state [[Ret (FAIL EINVAL)]] to return error
   [[EINVAL]] to the caller.

   The second case is subtle: a previous call to [[accept()]] may have blocked waiting for a new
   completed connection to arrive and an operation, such as a [[close()]] call, in another thread
   caused the socket to change from the [[LISTEN]] state.

   @internal

   If the user calls [[accept()]] on a socket that is not in the listening state, or the user has
   called this and is blocked in the [[Accept2]] state when the state of the socket changes out of
   the listening state, the error [[EINVAL]] is returned.

   POSIX: "shall fail...".

   TODO: The slow version is a bit speculative; it's also possible that it just blocks forever.  CHECK!

   slow version SHOULD BE URGENT.

   :*)
   )

/\

   (!h ts tid d t lbl rc fd fid ff sid sock
     SS MM.

   accept_6 /* rp_tcp, rc (*: Fail with [[EMFILE]]: out of file descriptors :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(t,d)) |>,SS,MM)
   -- lbl -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EMFILE),sched_timer)) |>,SS,MM)

   <==

   $\/
    (t = Run /\
     lbl = Lh_call (tid,accept(fd)) /\
     rc = fast fail /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sid IN FDOM h.socks /\
     sock = (h.socks ' sid) /\
     proto_of sock.pr = PROTO_TCP
    )
    (t = Accept2(sid) /\
     lbl = Lh_tau /\
     rc = slow nonurgent fail
    ) /\
    CARD (FDOM h.fds) >= OPEN_MAX


   (*:

   @description

   This rule covers two cases: (1) from thread [[tid]], which is in the [[Run]] state, an
   [[accept(fd)]] call is made where [[fd]] refers to a TCP socket [[sid]], and (2) a previous call
   to [[accept()]] blocked leaving thread [[tid]] in the [[Accept2(sid)]] state. In either case the
   [[accept()]] call fails with [[EMFILE]] as the process (see Model Details) already has open its
   maximum number of open file descriptors [[OPEN_MAX]].

   In the first case the error is returned immediately ([[fast fail]]) by performing an
   [[Lh_call(tid,accept(fd))]] transition, leaving the thread state [[Ret(FAIL EMFILE)]]. In the
   second, the thread is unblocked, also leaving the thread state [[Ret(FAIL EMFILE)]], by
   performing a [[Lh_tau]] transition.

   @modeldetails

   In real systems, error [[EMFILE]] indicates that the calling process already has [[OPEN_MAX]] file
   descriptors open and is not permitted to open any more. This specification only models one
   single-process host with multiple threads, thus [[EMFILE]] is generated when the host exceeds the
   [[OPEN_MAX]] limit in this model.

   @internal

   TODO: fix description.

   If the user calls [[accept()]] on a socket, or the user has called
   this and is blocked in the [[Accept2]] state, and there are not enough
   file descriptors available for the accepting socket, then [[EMFILE]]
   may occur.

   POSIX: "shall fail..." / "may fail...".

   Very nondeterministic, since we do not want to be too specific.
   Check.  Perhaps we should only do this if there is definitely a
   connection available?

   We're assuming, though, that buffers are only needed once we've
   found the socket, i.e., that [[EBADF]] and [[ENOTSOCK]] take
   priority over all this error.

   :*)
   )

/\

   (!h ts d fd fid sid ff tid err
     SS MM.

   accept_7 /* rp_udp, fast fail (*: Fail with [[EOPNOTSUPP]] or [[EINVAL]]: [[accept()]] called on
     a UDP socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,accept(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer)) |>,SS,MM)

   <==

   fd IN FDOM h.fds /\
   fid = h.fds ' fd /\
   FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
   sid IN FDOM h.socks /\
   proto_of (h.socks ' sid).pr = PROTO_UDP /\
   (if bsd_arch h.arch then err = EINVAL
    else err = EOPNOTSUPP)


   (*:

   @description

   Calling [[accept()]] on a socket for a connectionless protocol (such as UDP) has no defined
   behaviour and is thus an invalid ([[EINVAL]]) or unsupported ([[EOPNOTSUPP]]) operation.

   From thread [[tid]], which is in the [[Run]] state, an [[accept(fd)]] call is made where [[fd]]
   refers to a UDP socket identified by [[sid]]. The call proceeds by a [[Lh_call(tid,accept(fd))]]
   transition leaving the thread state [[Ret(FAIL err)]] to return error [[err]]. On FreeBSD
   [[err]] is [[EINVAL]]; on all other systems the error is [[EOPNOTSUPP]].


   @variation FreeBSD

   FreeBSD returns error [[EINVAL]] if [[accept()]] is called on a UDP socket.

   :*)

   )

/\


(*:

@section [[bind]] ALL [[bind()]]
 \[ <[bind: (fd * ip option * port option) -> unit]> \]

  [[bind(fd,is,ps)]] assigns a local address to the socket referenced by file descriptor [[fd]]. The
  local address, [[(is,ps)]], may consist of an IP address, a port or both an IP address and port.

  If [[bind()]] is called without specifying a port, [[bind(_,_,NONE)]], the socket's local port
  assignment is autobound, i.e. an unused port for the socket's protocol in the host's ephemeral
  port range is selected and assigned to the socket. Otherwise the port [[p]] specified in the bind
  call, [[bind(_,_,SOME p)]] forms part of the socket's local address.

  On some architectures a range of port values are designated to be privileged, e.g. 0-1023
  inclusive. If a call to [[bind()]] requests a port in this range and the caller does not have
  sufficient privileges the call will fail.

  A [[bind()]] call may or may not specify the IP address. If an IP address is not specified,
  [[bind(_,NONE,_)]], the socket's local IP address is set to [[NONE]] and it will receive segments
  or datagrams addressed to any of the host's local IP addresses and port [[p]]. Otherwise, the
  caller specifies a local IP address, [[bind(_,SOME i,_)]], the socket's local IP address is set
  to [[SOME i]], and it only receives segments or datagrams addressed to IP address [[i]] and port
  [[p]].

  A call to [[bind()]] may be unsuccessful if the requested IP address or port is unavailable to
  bind to, although in certain situations this can be overrriden by setting the socket option
  [[SO_REUSEADDR]] appropriately: see {@link [[bound_port_allowed]]}.

  A socket can only be bound once: it is not possible to rebind it to a different port later. A
  [[bind()]] call is not necessary for every socket: sockets may be autobound to an ephemeral port when a
  call requiring a port binding is made, e.g. [[connect()]].

@errors

  A call to [[bind()]] can fail with the errors below, in which case the corresponding exception
  is raised:

  @error [[EACCES]] The specified port is in the privileged port range of the host architecture and
  the current thread does not have the required privileges to bind to it.

  @error [[EADDRINUSE]] The specified address is in use by or conflicts with the address of another
  socket using the same protocol. The error may occur in the following situations only:
    \begin{itemize}

      \item [[bind(_,_,SOME p)]] will fail with [[EADDRINUSE]] if another socket is bound to port
       [[p]]. This error may be preventable by setting the [[SO_REUSEADDR]] socket option.

      \item [[bind(_,SOME i,SOME p)]] will fail with [[EADDRINUSE]] if another socket is bound to
       port [[p]] and IP address [[i]], or is bound to port [[p]] and wildcard IP. This error will
       not occur if the [[SO_REUSEADDR]] option is correctly used to allow multiple sockets to be
       bound to the same local port.

    \end{itemize}
  This error is never returned from a call [[bind(_,_,NONE)]] that requests an autobound port.

  @error [[EADDRNOTAVAIL]] The specified IP address cannot be bound as it is not local to the host.

  @error [[EINVAL]] The socket is already bound to an address and the socket's protocol does not
  support rebinding to a new address. Multiple calls to [[bind()]] are not permitted.

  @error [[EISCONN]] The socket is connected and rebinding to a new local address is not
  permitted (TCP ONLY).

  @error [[ENOBUFS]] A port was not specified in the [[bind()]] call and autobinding failed because
  no ephemeral ports for the socket's protocol are currently available. In addition, on WinXP the
  error can signal that the host has insufficient available buffers to complete the operation.

  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  A server application creates a TCP socket and binds it to its local address. It is then put in the
  [[LISTEN]] state to accept incoming connections to this address: [[socket_1]]; [[return_1]];
  [[bind_1]]; [[return_1]]; [[listen_1]]

  A UDP socket is created and bound to its local address. [[recv()]] is called and the socket
  blocks, waiting to receive datagrams sent to the local address: [[socket_1]]; [[return_1]];
  [[bind_1]]; [[return_1]]; [[recv_12]]

@api

  \begin{tabular}{ll}
    Posix:  &  |int bind(int socket, const struct sockaddr *address,| \\
            &  |           socklen_t address_len);| \\
    FreeBSD:&  |int bind(int s, struct sockaddr *addr, socklen_t addrlen);| \\
    Linux:  &  |int bind(int sockfd, struct sockaddr *addr, socklen_t addrlen);| \\
    WinXP:  &  |SOCKET bind(SOCKET s, const struct sockaddr* name, int namelen);| \\
  \end{tabular}\\

  In the Posix interface:
  \begin{itemize}

    \item |socket| is the socket's file descriptor, corresponding to the [[fd]] argument of
     the model.

    \item |address| is a pointer to a |sockaddr| structure of size
    |socklen_t| containing the local IP address and port to be assigned to the socket,
    corresponding to the [[is]] and [[ps]] arguments of the model. For the |AF_INET|
    sockets used in the model, a |sockaddr_in| structure stores the address. The
    |sin_addr.s_addr| field holds the IP address; if it is set to |0| then the IP
    address is wildcarded: [[is=NONE]]. The |sin_port| field stores the port to bind to; if
    it is set to |0| then the port is wildcarded: [[ps=NONE]]. On WinXP a wildcard IP is
    specified by the constant |INADDR_ANY|, not |0|

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual
     error code available through a call to |WSAGetLastError()|.

  \end{itemize}

  The FreeBSD, Linux and WinXP interfaces are similar modulo some argument renaming, except where
  noted above.

  On Windows Socket 2 the |name| parameter is not necessarily interpreted as a pointer to a
  |sockaddr| structure but is cast this way for compatilibity with Windows Socket 1.1 and
  the BSD sockets interface. The service provider implementing the functionality can choose to
  interpret the pointer as a pointer to any block of memory provided that the first two bytes of the
  block start with the address family used to create the socket. The default WinXP internet family
  provider expects a |sockaddr| structure here. This change is purely an interface design
  choice that ultimately achieves the same functionality of providing a name for the socket and is
  not modelled.

@modeldetails

  The specification only models the {AF,PF}\_INET address families thus the address family field of
  the |struct sockaddr| argument to [[bind()]] and those errors specific to other address
  familes, e.g. UNIX domain sockets, are not modelled here.

  In the Posix specification, [[ENOBUFS]] may have the additional meaning of "Insufficient resources
  were available to complete the call". This is more general than the use of [[ENOBUFS]] in the
  model.

  The following errors are not modelled:
  \begin{itemize}

    \item |EAGAIN| is BSD-specific and described in the man page as: "Kernel resources to
     complete the request are temporarily unavailable". This is not modelled here.


    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

    \item |EFAULT| signifies that the pointers passed as either the |address| or
     |address_len| arguments were inaccessible.  This is an artefact of the C interface to
     [[bind()]] that is excluded by the clean interface used in the model. On WinXP, the equivalent
     error |WSAEFAULT| in addition signifies that the name address format used in
     |name| may be incorrect or the address family in |name| does not match that of
     the socket.

    \item |ENOTDIR|, |ENAMETOOLONG|, |ENOENT|, |ELOOP|,
     |EIO| (BSD-only), |EROFS|, |EISDIR| (BSD-only), |ENOMEM|,
     |EAFNOTSUPPORT| (Posix-only) and |EOPNOTSUPP| (Posix-only) are errors specific
     to other address families and are not modelled here. None apply to WinXP as other address
     families are not available by default.

  \end{itemize}

:*)


   (!h h' h0 ts socks tid d
     fd fid ff sid sf cb es
     is1 ps1 p1 pr cantsndmore cantrcvmore bound
     SS MM.

   bind_1 /* rp_all, fast succeed (*: Successfully assign a local address to a socket (possibly by
     autobinding the port) :*) */
     (h0,SS,MM)
   -- Lh_call (tid,bind(fd,is1,ps1)) -->
     (h,SS,MM)

   <==

     h0 = h' with <| ts := FUPDATE ts (tid,Timed(Run,d));
                      socks := socks |++
                        [(sid ,Sock(SOME fid,sf,NONE,NONE,NONE,NONE,es,cantsndmore,cantrcvmore,pr))]
                  |> /\
     h  = h' with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
                     socks := socks |++
                        [(sid ,Sock(SOME fid,sf,is1,SOME p1,NONE,NONE,es,cantsndmore,cantrcvmore,pr))];
                     bound := bound |> /\
     fd IN FDOM h0.fds /\
     fid = h0.fds ' fd /\
     FAPPLY h0.files fid = File(FT_Socket(sid),ff) /\
     sid NOTIN (FDOM socks) /\
     (!i1. is1 = SOME i1 ==> i1 IN local_ips(h0.ifds)) /\
     p1 IN autobind(ps1,(proto_of pr),h0,socks) /\
     bound = sid::h0.bound /\
     (h0.privs \/ p1 NOTIN privileged_ports h0) /\
     bound_port_allowed pr (h0.socks \\ sid) sf h0.arch is1 p1 /\
     (case pr of
        TCP_PROTO(tcp_sock) -> tcp_sock = TCP_Sock0(CLOSED,cb,NONE) /\
	                       (bsd_arch h0.arch ==> cantsndmore=F (* X /\ cb.bsd_cantconnect = F X *)) ||
        UDP_PROTO(udp_sock) -> udp_sock = UDP_Sock0([]))


   (*:

   @description

   The call [[bind(fd,is1,ps1)]] is perfomed on the TCP or UDP socket [[sid]] referenced by file
   descriptor [[fd]] from a thread [[tid]] in the [[Run]] state. The socket [[sid]] is currently
   uninitialised, i.e. it has no local or remote address defined [[(NONE,NONE,NONE,NONE)]], and it
   contains an uninitialised TCP or UDP protocol block, [[tcp_sock]] and [[udp_sock]] as appropriate for the socket's protocol.

   If an IP address is specified in the [[bind()]] call, i.e. [[is1 = SOME i1]], the call can only succeed
   if the IP address [[i1]] is one of those belonging to an interface of host [[h]], [[i1 IN
   local_ips(h0.ifds)]].

   The port [[p1]] that the socket will be bound to is determined by the auxiliary function
   [[autobind]] that takes as argument the port option [[ps1]] from the [[bind()]] call. If [[ps1 =
   SOME p]] [[autobind]] simply returns the singleton set [[{p}]], constraining the local port
   binding [[p1]] by [[p1 = p]]. Otherwise, [[autobind]] returns a set of available ephemeral ports
   and [[p1]] is constrained to be a port within the set.

   If a port is specified in the [[bind()]] call, i.e. [[ps1 = SOME p1]], either the port is not a
   privileged port [[p1 NOTIN privileged_ports]] or the host (actually, process) must have
   sufficient privileges [[h0.priv = T]].

   Not all requested bindings are permissible because other sockets in the system may be bound to
   the chosen address or to a conflicting address. To check the binding [[is1, SOME p1]] is
   permitted the auxiliary function [[bound_port_allowed]] is used. [[bound_port_allowed]] is
   architecture dependent and checks not only the other sockets bound locally to port [[p1]] on the
   host, but also the status of the socket flag [[SO_REUSEADDR]] for socket [[sid]] and the
   conflicting sockets. The use of the socket flag [[SO_REUSEADDR]] can permit sockets to share
   bindings under some circumstances, resolving the binding conflict. See {@link [[bound_port_allowed]]} for further information.

   The call proceeds by performing a [[Lh_call(tid,bind(fd,is1,ps1))]] transition returning [[OK()]]
   to the calling thread. Socket [[sid]] is bound to local address [[(is1,SOME p1)]]and the host has
   an updated list of bound sockets [[bound]] with socket [[sid]] at its head.

   @variation FreeBSD

   If [[sid]] is a TCP socket then it cannot be shutdown for writing: [[cantsndmore=F]], and its
   [[bsd_cantconnect]] flag cannot be set.

   @modeldetails

   The list of bound sockets [[bound]] is used by the model to determine the order in which sockets
   are bound. This is required to model ICMP message and UDP datagram delivery on Linux.

   @internal

   If a socket is closed, then calling [[bind()]] on it sets its local port (possibly by
   autobinding), and possibly its local IP.  If the local IP is set, it must be one of the IPs of
   the local host.  The IP,port pair must not already be bound.  Notice that if the IP is not
   specified here, it is left unset in the socket until a later [[connect()]] is performed.

   POSIX "shall assign ... to a socket ... that has no local socket address assigned."

   I'm assuming that rebinding, even as incremental binding (specifying an IP address, for example,
   when port already assigned) is not permitted.

   Note that it's not [[bind]]ing but [[listen]]ing that puts a socket on the [[bound]] list.  So
   perhaps this is a misnomer.

   We are no longer assuming all sockets/callers are unprivileged -- instead, we use the [[h.privs]]
   field to determine if the process has privilege.

   :*)
   )

/\

   (!h ts tid d
     fd fid ff sid
     is1 p1 sock
     SS MM.

   bind_2 /* rp_all, fast fail (*: Fail with [[EADDRINUSE]]: the specified address is already in use :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,bind(fd,is1,SOME p1)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EADDRINUSE),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sock = (h.socks ' sid) /\
     ~(bound_port_allowed sock.pr (h.socks \\ sid) sock.sf h.arch is1 p1) /\
     (option_case T (\i1. i1 IN local_ips(h.ifds)) is1  \/ windows_arch h.arch)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[bind(fd,is1,SOME p1)]] call is performed
   on the socket [[sock]], which is identified by [[sid]] and referenced by [[fd]].

   If an IP address is specified in the call, [[is1 = SOME i1]], then [[i1]] must be an IP address
   for one of the host's interfaces. The requested local address binding, [[(is1,SOME p1)]], is not
   available as it is already in use: see {@link [[bound_port_allowed]]} for details.

   The call proceeds by a [[Lh_call(tid,bind(fd,is1,SOME p1))]] transition leaving the thread in
   state [[Ret(FAIL EADDRINUSE)]] to return error [[EADDRINUSE]] to the caller.

   @internal

   If the user calls [[bind()]], specifying a port or an IP,port pair that is already bound, the
   error [[EADDRINUSE]] is returned.

   POSIX "shall fail...".

   I'm assuming that the implementation checks that the fd points to a socket before it checks
   whether the address is in use; otherwise, error priority is *unspecified*, as it is in POSIX.
   [Checking this one thing is slightly tighter than POSIX, which would say that *any* error could
   happen].

   This error can only happen if port is specified, since unspecified port means autobinding occurs.
   POSIX specifies (by my interpretation!) that we get ENOBUFS if thre are no ports left.

   :*)
   )

/\

   (!h ts tid d
     fd fid ff sid
     i1 ps1
     SS MM.

   bind_3 /* rp_all, fast fail (*: Fail with [[EADDRNOTAVAIL]]: the specified IP address is not available on the host :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,bind(fd,SOME i1,ps1)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EADDRNOTAVAIL),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     i1 NOTIN local_ips(h.ifds)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[bind(fd,SOME i1,ps1)]] call is made where
   [[fd]] refers to a socket [[sid]].

   The IP address, [[i1]], to be assigned as part of the socket's local address does not belong to
   any of the interfaces on the host, [[i1 NOTIN local_ips(h.ifds)]], and therefore can not be
   assigned to the socket.

   The call proceeds by a [[Lh_call(tid,bind(fd,SOME i1,ps1))]] transition leaving the thread in
   state [[Ret(FAIL EADDRNOTAVAIL)]] to return error [[EADDRNOTAVAIL]] to the caller.

   @internal

   If the user calls [[bind()]], specifying an IP address that is not a local address of this host,
   the error [[EADDRNOTAVAIL]] is returned.

   POSIX "shall fail...".

   I'm assuming that the implementation checks that the fd points to a socket before it checks
   whether the address is available; otherwise, error priority is *unspecified*, as it is in POSIX.
   [Checking this one thing is slightly tighter than POSIX, which would say that *any* error could
   happen].

   This error can only happen if we specify an IP address.

   :*)
   )

/\

   (!h ts tid d
     fd fid ff sid
     is1 ps1 sock tcp_sock
     SS MM.

   bind_5 /* rp_all, fast fail (*: Fail with [[EINVAL]]: the socket is already bound to an address and does not support rebinding; or socket has been shutdown for writing on FreeBSD :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,bind(fd,is1,ps1)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINVAL),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     h.socks ' sid = sock /\
     (sock.ps1 <> NONE \/
      (bsd_arch h.arch /\ sock.pr = TCP_PROTO(tcp_sock) /\
       (sock.cantsndmore \/
        T ) ))


   (*:

   @description
   From thread [[tid]], which is in the [[Run]] state, a [[bind(fd,is1,ps1)]] call is made where
   [[fd]] refers to a socket [[sock]]. The socket already has a local port binding: [[sock.ps1 <>
   NONE]], and rebinding is not supported.

    A [[Lh_call(tid,bind(fd,is1,ps1))]] transition is made, leaving the thread state [[Ret (FAIL
    EINVAL)]].

    @variation FreeBSD

    This rule also applies if [[fd]] refers to a TCP socket which is either shut down for writing or
    has its [[bsd_cantconnect]] flag set.

   @internal

   If the user calls [[bind()]], but refers to a socket that already has a specified local port, the
   error [[EINVAL]] is returned, indicating that the socket is already bound.

   POSIX "shall fail...".

   I'm assuming that rebinding is never allowed by the protocol.

   POSIX also says "...or the socket has been shut down"?  We believe this means that if
   [[shutdown()]] has been called on the socket, [[bind()]] should fail.  However, in TCP this does
   not need a separate case - you cannot shut down without having made some kind of connection first,
   and in that case, the socket must already be bound.  We are prepared to be corrected by
   experiment, though. MF: yes on BSD you can call shutdown() on any socket so EINVAL can be returned.

   :*)
   )

/\

   (!h ts tid d
     fd fid ff sid
     is1 p1
     SS MM.

   bind_7 /* rp_all, fast fail (*: Fail with [[EACCES]]: the specified port is priveleged and the current process does not have permission to bind to it :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,bind(fd,is1,SOME p1)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EACCES),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     (~h.privs /\ p1 IN privileged_ports h)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[bind(fd,is1,SOME p1)]] call is made where
   [[fd]] refers to a socket [[sid]].  The port specified in the [[bind]] call, [[p1]], lies in the
   host's range of privileged ports, [[p1 IN privileged_ports]], and the current host (actually,
   process) does not have sufficient permissions to bind to it: [[~h.privs]].

   The call proceeds by a [[Lh_call(tid,bind(fd,is1,SOME p1))]] transition leaving the thread in
   state [[Ret(FAIL EACCES)]] to return the access violation error [[EACCES]] to the caller.

   @internal

   If the user calls [[bind()]], attempting to bind to a privileged port (usually one less than
   1024), the error [[EACCES]] is returned.

   POSIX "shall fail...".

   I'm assuming that the implementation checks that the fd points to a socket before it checks
   whether the address is protected; otherwise, error priority is *unspecified*, as it is in POSIX.
   [Checking this one thing is slightly tighter than POSIX, which would say that *any* error could
   happen].

   This error can only happen if port is specified, since unspecified port means autobinding occurs.

   We are no longer assuming all sockets/callers are unprivileged -- instead, we use the [[h.privs]]
   field to determine if the process has privilege.

   :*)
   )

/\

(*   (!h ts tid d
     fd fid ff sid
     is1 ps1 tcp_sock
     SS MM.

   bind_8 /* rp_tcp, fast fail (*: Fail with [[EISCONN]]: the socket is already connected :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,bind(fd,is1,ps1)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EISCONN),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     TCP_PROTO(tcp_sock) = (h.socks ' sid).pr /\
     tcp_sock.st = ESTABLISHED


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[bind(fd,is1,ps1)]] call is made where
   [[fd]] refers to a TCP socket [[sid]].

   The TCP socket is already connected, [[tcp_sock.st = ESTABLISHED]], so it therefore must already
   have a fully complete local address so it cannot be rebound to another address.

   The call proceeds by a [[Lh_call(tid,bind(fd,is1,ps1))]] transition leaving the thread state
   [[Ret(FAIL EISCONN)]] to return the error [[EISCONN]] to the caller.

   @internal

   If the user calls [[bind()]] on a socket that is in the established (connected) state, the error
   [[EISCONN]] is returned to indicate that the socket is already connected.

   POSIX "shall fail...".

   :*)
   )

/\ *)

   (!h ts tid d
     fd fid ff sid
     is1 ps1
     SS MM.

   bind_9 /* rp_all, fast badfail (*: Fail with [[ENOBUFS]]: no ephemeral ports free for autobinding or, on WinXP only, insufficient buffers available. :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,bind(fd,is1,ps1)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOBUFS),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     ps1 = NONE /\
     ((autobind(ps1,(proto_of (h.socks ' sid).pr),h,h.socks) = EMPTY) \/
      windows_arch h.arch)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[bind(fd,is1,ps1)]] call is made where
   [[fd]] refers to a socket [[sid]].

   A port is not specifed in the [[bind]] call, i.e. [[ps1 = NONE]], and calling [[autobind]] returns
   the [[EMPTY]] set rather than a set of free ephemeral ports that the socket could choose
   from. This occurs only when there are no remaining ephemeral ports available for autobinding.

   The call proceeds by a [[Lh_call(tid,bind(fd,is1,ps1))]] transition leaving the thread state
   [[Ret(FAIL ENOBUFS)]] to return the out of resources error [[ENOBUFS]] to the caller.

   @variation WinXP

   On WinXP this error can occur non-deterministically when insufficient buffers are available.

   @modeldetails

   Posix reports [[ENOBUFS]] to signify that "Insufficient resources were available to complete the
   call". This is not modelled here.

   @internal

   If the user calls [[bind()]] without specifying a particular port, but there are no ephemeral
   ports available, the bad (resource-related) error [[ENOBUFS]] is returned.

   WinXP may fail with [[ENOBUFS]] if there are too many connections.

   POSIX "may fail...".

   This is a bit of interpretation; if there are not any ports available then I think the
   implementation SHOULD fail with ENOBUFS, but POSIX does not say this.

   I'm assuming that the implementation checks that the fd points to a socket before it checks
   whether there is a port available; otherwise, error priority is *unspecified*, as it is in POSIX.
   [Checking this one thing is slightly tighter than POSIX, which would say that *any* error could
   happen].

   NB: This is NOT guarded by [[ ~INFINITE_RESOURCES ]], since we cannot have an infinite number of
   ephemeral ports - they are numbered in a fixed range.  This is probably the only badfail that is
   not switched off by turning on [[INFINITE_RESOURCES]].  (not true: EINTR is this also).

   :*)
   )

/\


(*:

@section [[close]] ALL [[close()]]
 \[ <[close: fd -> unit]> \]

  A call [[close(fd)]] closes file descriptor [[fd]] so that it no longer refers to a file
  description and associated socket. The closed file descriptor is made available for reuse by the
  process. If the file descriptor is the last file descriptor referencing a file description the
  file description itself is deleted and the underlying socket is closed. If the socket is a UDP
  socket it is removed.

  It is important to note the distinction drawn above: only closing the last file descriptor of a
  socket has an effect on the state of the file description and socket.

  The following behaviour may occur when closing the last file descriptor of a TCP socket:

  \begin{itemize}

   \item A TCP socket may have the [[SO_LINGER]] option set which specifies a maximum duration in
    seconds that a [[close(fd)]] call is permitted to block.
    \begin{itemize}

      \item In the normal case the [[SO_LINGER]] option is not set, the close call returns
       immediately and asynchronously sends any remaining data and gracefully closes the connection.

      \item If [[SO_LINGER]] is set to a non-zero duration, the [[close(fd)]] call will block while
       the TCP implementation attempts to successfully send any remaining data in the socket's send
       buffer and gracefully close the connection. If the sending of remaining data and the graceful
       close are successful within the set duration, [[close(fd)]] returns successfully, otherwise
       the linger timer expires, [[close(fd)]] returns an error [[EAGAIN]], and the close operation
       continues asychronously, attempting to send the remaining data.

      \item The [[SO_LINGER]] option may be set to zero to indicate that [[close(fd)]] should be
       abortive. A call to [[close(fd)]] tears down the connection by emitting a reset segment to
       the remote end (abandoning any data remaining in the socket's send queue) and returns
       successfully without blocking.


    \end{itemize}

   \item If [[close(fd)]] is called on a TCP socket in a pre-established state the file description
    and socket are simply closed and removed, regardless of how [[SO_LINGER]] is set, except on
    Linux platforms where [[SYN_RECEIVED]] is dealt with as an established state for the purposes of
    [[close(fd)]].

   \item Calling [[close(fd)]] on a listening TCP socket closes and removes the socket and aborts
    each of the connections on the socket's pending and completed connection queues.

  \end{itemize}

@errors

  A call to [[close()]] can fail with the errors below, in which case the corresponding exception is
  raised:

  @error [[EAGAIN]] The linger timer expired for a lingering [[close()]] call and the socket has not
  yet been successfully closed.

  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]
  @errorinclude [[misc]] [[EINTR]]

@commoncases

  A TCP socket is created and connected to a peer; other socket calls are made, most likely [[send()]] and
  [[recv()]], but the [[SO_LINGER]] option is not set. [[close()]] is then called and the connection
  is gracefully closed: [[socket_1]]; $\dots $; [[close_2]]

  A UDP socket is created and socket calls are made on it, mostly [[send()]] and [[recv()]] calls;
  the socket is then closed: [[socket_1]]; $\dots $; [[close_10]]

@api

  \begin{tabular}{ll}
    Posix:  &  |int close(int fildes);| \\
    FreeBSD:&  |int close(int d);| \\
    Linux:  &  |int close(int fd);| \\
    WinXP:  &  |int closesocket(SOCKET s);| \\
  \end{tabular}\\

  In the Posix interface:
  \begin{itemize}

    \item |fildes| is the file descriptor to close, corresponding to the [[fd]] argument of
    the model [[close()]].

    \item the returned |int| is either |0| to indicate success or |-1| to
    indicate an error, in which case the error code is in |errno|.  On WinXP an error is
    indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual
    error code available through a call to |WSAGetLastError()|.

  \end{itemize}

  The FreeBSD, Linux and WinXP interfaces are similar modulo argument renaming, except where
  noted above.

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item In Posix and on FreeBSD and Linux, |EIO| means an I/O error occurred while reading from or
    writing to the file system.  Since we model only sockets, not file systems, we do not model this
    error.

    \item On FreeBSD, |ENOSPC| means the underlying object did not fit, cached data was
    lost.

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)


   (!h ts tid d fds fds'
     fd fid
     SS MM.

   close_1 /* rp_all, fast succeed (*: Successfully close a file descriptor that is not the last file descriptor for a socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               fds := fds |>,
     SS,MM)
   -- Lh_call (tid,close(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               fds := fds' |>,
     SS,MM)

   <==

     fd IN FDOM fds /\
     fid = fds ' fd /\
     fid_ref_count(fds,fid) > 1 /\
     fds' = fds \\ fd


   (*:

    @description

    A [[close(fd)]] call is performed where [[fd]] refers to either a TCP or UDP socket. At least
    two file descriptors refer to file description [[fid]], [[fid_ref_count(fds,fid) > 1]], of which
    one is [[fd]], [[fid = fds ' fd]].

    The [[close(fd)]] call proceeds by a [[Lh_call(tid,close(fd))]] transition leaving the host in
    the successful return state [[Ret (OK())]]. In the final host state, the mapping of file
    descriptor [[fd]] to file descriptor index [[fid]] is removed from the file descriptors finite
    map [[fds' = fds \\ fd]] , effectively reducing the reference count of the file description by
    one. The [[close()]] call does not alter the socket's state as other file descriptors still
    refer to the socket through file description [[fid]].

    @internal

    If the user calls [[close()]], but there is more than one file descriptor for this open file
    description, the file descriptor is freed but no further action is taken.

    POSIX "shall deallocate...".

    UNPv1p191 table implies that even if this is not the last [[fd]], the flags [[cantsndmore]] and
    [[cantrcvmore]] should be set.  We have not verified whether or not this is the case.  A quick
    look at BSD source suggests that UNPv1 is bogus here, and nothing interesting happens until the
    last fd for a socket is closed.  (or else how could you renumber an fd for a socket safely??).
    SB: UNPv1p191 is incorrect.

   :*)
   )

/\

   (!h ts tid d fds fds'
     fd fid files socks
     sid ff sf es st
     i1 p1 i2 p2 cb cantsndmore cantrcvmore
     SS s s' peek inline flgs data
     MM.

   close_2 /* rp_tcp, fast succeed (*: Successfully perform a graceful close on the last file descriptor of a synchronised socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               fds := fds;
               files := files |++
                        [(fid,File(FT_Socket(sid),ff))];
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s)],MM)
   -- Lh_call (tid,close(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               fds := fds';
               files := files \\ fid;
               socks := socks |++
                        [(sid,Sock(NONE,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,T,T,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s')],MM)

   <==

     (st IN {ESTABLISHED;FIN_WAIT_1;CLOSING;FIN_WAIT_2;
             TIME_WAIT;CLOSE_WAIT;LAST_ACK} \/
      st = SYN_RECEIVED /\ linux_arch h.arch) /\ (* earlier states are treated specially *)
     (sf.t(SO_LINGER) = time_infty \/
      ff.b(O_NONBLOCK) = T /\ sf.t(SO_LINGER) <> time_zero /\ ~linux_arch h.arch) /\
     fd IN FDOM fds /\
     fid = fds ' fd /\
     fid_ref_count(fds,fid) = 1 /\
     fds' = fds \\ fd /\
     fid NOTIN (FDOM files) /\
     (peek,inline) = (F,T) /\
     read (i1,p1,i2,p2) peek inline (flgs,data) s s'


   (*:

    @description

    A [[close(fd)]] call is performed on the TCP socket [[sid]] referenced by file descriptor [[fd]]
    which is the only file descriptor referencing the socket's file description:
    [[fid_ref_count(fds,fid) = 1]]. The TCP socket [[sid]] is in a synchronised state, i.e. a state
    [[>= ESTABLISHED]], or on Linux it may be in the [[SYN_RECEIVED]] state.

    In the common case the socket's linger option is not set, [[sf.t(SO_LINGER) = time_infty]], and
    regardless of whether the socket is in non-blocking mode or not, i.e. [[ff.b(O_NONBLOCK)]] is
    unconstrained, the call to [[close()]] proceeds successfully without blocking.

    On all platforms except for Linux, if the socket is in non-blocking mode [[ff.b(O_NONBLOCK) =
    T]] the linger option may be set with a positive duration: [[sf.t(SO_LINGER) <> time_zero)]]. In
    this case the option is ignored giving precedence to the socket's non-blocking semantics. The
    [[close()]] call succeeds without blocking.

    The [[close(fd)]] call proceeds by a [[Lh_call(tid,close(fd))]] transition leaving the host in
    the successful return state [[Ret (OK())]]. The final socket is marked as unable to send and
    receive further data, [[cantsndmore = T /\ cantrcvmore = T]], eventually causing TCP to transmit
    all remaining data in the socket's send queue and perform a graceful close.

    In the final host state, the mapping of file descriptor [[fd]] to file descriptor index [[fid]]
    is removed from the file descriptors finite map [[fds' = fds \\ fd]] and the file description
    entry [[fid]] is removed from the finite map of file descriptors [[files \\ fid]]. The socket
    entry itself, [[(sid,Sock(SOME fid,]]$\dots $,[[))]] is not destroyed at this point; it remains
    until the TCP connection has been successfully closed.

    @variation Linux

    The socket can be in the [[SYN_RECEIVED]] state or in one of the synchronised states [[>=
    ESTABLISHED]].

    On Linux, non-blocking semantics do not take precedence over the [[SO_LINGER]] option, i.e. if
    the socket is non-blocking, [[ff.b(O_NONBLOCK) = T]] and a linger option is set to a non-zero
    value, [[sf.t(SO_LINGER) <> time_zero]], the socket may block on a call to [[close()]]. See also
    {@link [[close_4]]}.

    @internal

    If the user calls [[close()]], and this is the only file descriptor referring to the open file
    description, and that open file description refers to a socket that is connected (i.e., in the
    [[ESTABLISHED]] state), and either the linger option is not set, or is set to something nonzero
    and [[O_NONBLOCK]] is set, then we free the file descriptor and open file description, set the
    [[cantsndmore]] flag to indicate that the end of [[sndq]] is EOF (causing [[deliver_out_*]] to
    eventually send a [[FIN]]), strip everything from [[rcvq]], and set [[cantrcvmore]] to arrange
    that recv() returns 0 rather than blocks, and return.

    POSIX "When all file descriptors associated ... are closed, any data remaining in the pipe or
    FIFO special file shall be discarded.  ... the open file description shall be freed."

    (unclear whether the first sentence applies to sockets too).

    I'm assuming too that the XSR streams stuff in the POSIX page does not apply.

    "If [fd] refers to a socket ... the socket [shall be] destroyed.  If the socket is in
    connection-mode, and the [[SO_LINGER]] option is set for the socket with non-zero linger time,
    and the socket has untransmitted data, then close shall block for up to the current linger
    interval until all data is transmitted."

    !! TCPv2p473 says 0 linger time means wait forever.  TCPv2p1019 seems to disagree.

    Three cases in the C API: [[SO_LINGER]] may be (a) not set, (b) set to zero, (c) set to
    non-zero.  We model these respectively by setting the time value of the option as follows: (a)
    infinity, (b) zero, (c) non-zero.

    See UNPv1p187 for the semantics of [[SO_LINGER]]: sometimes we should immediately generate a
    RST.

    Keith observes: there's now no way to remove that sock from h.socks; no way to access it from
    the program.  Eventually it will move to TIME\_WAIT and then to CLOSED; should not it be made to
    evaporate?  Seems messy to accumulate garbage in this way.  OTOH, think it's probably not (very)
    observable.

   :*)
   )

/\

   (!h ts tid d fds fds'
     fd fid files socks oq oq'
     sid ff sf es sock sock'
     i1 p1 i2 p2 st cb cantsndmore cantrcvmore
     odata oflgs SS SS0 SS'' SS' s s' MM.

   close_3 /* rp_tcp, fast succeed (*: Successful abortive close of a synchronised socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               fds := fds;
               files := files |++
                        [(fid,File(FT_Socket(sid),ff))];
               socks := socks |++
                        [(sid,sock)];
               oq := oq |>,
     SS,MM)
   -- Lh_call (tid,close(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               fds := fds';
               files := files;
               socks := socks |++ [(sid,sock')];
               oq := oq' |>,
     SS'',MM)

   <==

     (st IN {ESTABLISHED;FIN_WAIT_1;CLOSING;FIN_WAIT_2;
            TIME_WAIT;CLOSE_WAIT;LAST_ACK} \/
      st = SYN_RECEIVED /\ linux_arch h.arch) /\ (* earlier states are treated specially *)
     sock = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                  TCP_Sock(st,cb,NONE)) /\
     sf.t(SO_LINGER) = time_zero /\  (* [[O_NONBLOCK]] is irrelevant here *)
     fd IN FDOM fds /\
     fid = fds ' fd /\
     fid_ref_count(fds,fid) = 1 /\
     fds' = fds \\ fd /\
     fid NOTIN (FDOM files) /\
     sid NOTIN FDOM socks /\
     sock' = (tcp_close h.arch sock) with <| fid := NONE |> /\
     oflgs = oflgs with <| SYN := F; SYNACK := F; RST := T |> /\
     odata IN UNIV /\
     SS = SS0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
     write (i1,p1,i2,p2) (oflgs,odata) s s' /\
     SS' = SS0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')] /\
     destroy (i1,p1,i2,p2) SS' SS''


   (*:

    @description

    A [[close(fd)]] call is performed on the TCP socket [[sid]] referenced by file descriptor [[fd]]
    which is the only file descriptor referencing the socket's file description:
    [[fid_ref_count(fds,fid) = 1]]. The TCP socket [[sid]] is in a synchronised state, i.e. a state >=
    [[ESTABLISHED]], except on Linux platforms where it may be in the [[SYN_RECEIVED]] state.

    The socket's linger option is set to a duration of zero, [[sf.t(SO_LINGER) = time_zero]], to signify
    that an abortive closure of socket [[sid]] is required.

    The [[close(fd)]] call proceeds by a [[Lh_call(tid,close(fd))]] transition leaving the host in
    the successful return state [[Ret (OK())]]. A reset segment [[seg]] is constructed from the
    socket's control block [[cb]] and address quad [[(i1,i2,p1,p2)]] and is appended to the host's
    output queue, [[oq]], by the function {@link [[enqueue_and_ignore_fail]]}, to create new output queue
    [[oq']]. The [[enqueue_and_ignore_fail]] function always succeeds; if it is not possible to add
    the reset segment [[seq]] to the output queue the corresponding error code is ignored and the
    reset segment is not queued for transmission.

    The mapping of file descriptor [[fd]] to index [[fid]] is removed from the file descriptors
    finite map [[fds' = fds \\ fd]] and the file description entry indexed by [[fid]] is removed
    from the finite map of file descriptions. The socket is put in the [[CLOSED]] state, shutdown
    for reading and writing, has its control block reset, and its send and receive queues emptied;
    this is done by the auxiliary function {@link [[tcp_close]]}. Additionally, its file description
    field is cleared.

    @variation Linux

    The socket can be in the [[SYN_RECEIVED]] state or in one of the synchronised states [[>=
    ESTABLISHED]].

    @internal

    ** If we were being more aggressive about API cleanup, we would make this a different call,
       since its behaviour is so different.  abortively close(fd) or something.

    If the user calls [[close()]], and this is the only file descriptor referring to the open file
    description, and that open file description refers to a socket that is connected (i.e., in the
    [[ESTABLISHED]] state or later), and the linger option is set to zero, abortively close the
    connection by sending a RST to the peer, and destroy the socket.  Return immediately.

    POSIX "When all file descriptors associated ... are closed, any data remaining in the pipe or
    FIFO special file shall be discarded.  ... the open file description shall be freed."

    (unclear whether the first sentence applies to sockets too).

    I'm assuming too that the XSR streams stuff in the POSIX page does not apply.

    "If [fd] refers to a socket ... the socket [shall be] destroyed.  If the socket is in
    connection-mode, and the [[SO_LINGER]] option is set for the socket with non-zero linger time,
    and the socket has untransmitted data, then close shall block for up to the current linger
    interval until all data is transmitted."

    !! TCPv2p473 says 0 linger time means wait forever.  TCPv2p1019 seems to disagree.

    See UNPv1p187 for the semantics of [[SO_LINGER]]: sometimes we should immediately generate a
    RST.

   :*)
   )

/\

   (!h ts tid d fds fds'
     fd fid files socks
     sid ff sf es
     i1 p1 i2 p2 st cb cantsndmore cantrcvmore
     SS MM.

   close_4 /* rp_tcp, block (*: Block on a lingering close on the last file descriptor of a synchronised socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               fds := fds;
               files := files |++
                        [(fid,File(FT_Socket(sid),ff))];
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS,MM)
   -- Lh_call (tid,close(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Close2(sid),slow_timer (sf.t(SO_LINGER))));
               fds := fds';
               files := files;
               socks := socks |++
                        [(sid,Sock(NONE,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,T,T,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS,MM)

   <==

     (st IN {ESTABLISHED;FIN_WAIT_1;CLOSING;FIN_WAIT_2;
            TIME_WAIT;CLOSE_WAIT;LAST_ACK} \/
      st = SYN_RECEIVED /\ linux_arch h.arch) /\ (* earlier states are treated specially *)
     sf.t(SO_LINGER) NOTIN {time_zero; time_infty} /\
     (ff.b(O_NONBLOCK) = F \/ (ff.b(O_NONBLOCK) = T /\ linux_arch h.arch)) /\
     fd IN FDOM fds /\
     fid = fds ' fd /\
     fid_ref_count(fds,fid) = 1 /\
     fds' = fds \\ fd /\
     fid NOTIN (FDOM files)


   (*:

    @description

    A [[close(fd)]] call is performed on the TCP socket [[sid]] referenced by file descriptor [[fd]]
    which is the only file descriptor referencing the socket's file description:
    [[fid_ref_count(fds,fid) = 1]]. The TCP socket [[sid]] has a blocking mode of operation,
    [[ff.b(O_NONBLOCK) = F]], and is in a synchronised state, i.e. a state [[>= ESTABLISHED]].

    On Linux, the socket is also permitted to be in the [[SYN_RECEIVED]] state and it may have
    non-blocking semantics [[ff.b(O_NONBLOCK) = T]], because the linger option takes precedence over
    non-blocking semantics.

    The socket's linger option is set to a positive duration and is neither zero (which signifies an
    immediate abortive close of the socket) nor infinity (which signifies that the linger option has
    not been set), [[sf.t(SO_LINGER) NOTIN {time_zero; time_infty}]]. The close call blocks for a
    maximum duration that is the linger option duration in seconds, during which time TCP attempts
    to send all remaining data in the socket's send buffer and gracefully close the connection.

    The [[close(fd)]] call proceeds by a [[Lh_call(tid,close(fd))]] transition leaving the host in
    the blocked state [[Close2(sid)]].  The socket is marked as unable to send and receive
    further data, [[cantsndmore = T /\ cantrcvmore = T]]; this eventually causes TCP to send all
    remaining data in the socket's send queue and perform a graceful close.

    In the final host state, the mapping of file descriptor [[fd]] to file descriptor index [[fid]]
    is removed from the file descriptors finite map [[fds' = fds \\ fd]] and file description entry
    [[fid]] is removed from the finite map of file descriptors. The socket entry itself,
    [[(sid,Sock(SOME fid,]]$\dots$[[))]], is not destroyed at this point; it remains until the TCP
    socket has been successfully closed by future asychronous events.

    @variation Linux

    The socket can be in the [[SYN_RECEIVED]] state or in one of the synchronised states [[>=
    ESTABLISHED]].

    On Linux, non-blocking semantics do not take precedence over the [[SO_LINGER]] option, i.e. if
    the socket is non-blocking, [[ff.b(O_NONBLOCK) = T]] and a linger option is set to a non-zero
    value, [[sf.t(SO_LINGER) <> time_zero]] the socket may block on a call to [[close()]].

    @internal

    If the user calls [[close()]], and this is the only file descriptor referring to the open file
    description, and that open file description refers to a socket that is connected (i.e., in the
    [[ESTABLISHED]] state), and the linger option is set to a nonzero time and [[O_NONBLOCK]] is not
    set, then we free the file descriptor and open file description, set the [[cantsndmore]] flag to
    indicate that the end of [[sndq]] is EOF (causing [[deliver_out_*]] to eventually send a
    [[FIN]]), strip everything from [[rcvq]], and set [[cantrcvmore]] to arrange that recv() returns
    0 rather than blocks, and block until either all of the data is sent and acked, or the linger
    time expires.

    POSIX "When all file descriptors associated ... are closed, any data remaining in the pipe or
    FIFO special file shall be discarded.  ... the open file description shall be freed."

    (unclear whether the first sentence applies to sockets too).

    I'm assuming too that the XSR streams stuff in the POSIX page does not apply.

    "If [fd] refers to a socket ... the socket [shall be] destroyed.  If the socket is in
    connection-mode, and the [[SO_LINGER]] option is set for the socket with non-zero linger time,
    and the socket has untransmitted data, then close shall block for up to the current linger
    interval until all data is transmitted."

    !! TCPv2p473 says 0 linger time means wait forever.  TCPv2p1019 seems to disagree.

    See UNPv1p187 for the semantics of [[SO_LINGER]]: sometimes we should immediately generate a
    RST.

   :*)
   )

/\

   (!h ts tid d
     socks
     sid sf es
     i1 p1 i2 p2 st cb
     SS MM.

   close_5 /* rp_tcp, slow urgent succeed (*: Successful completion of a lingering close on a synchronised socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Close2(sid),d));
               socks := socks |++
                        [(sid,Sock(NONE,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,T,T,
                              TCP_Sock(st,cb,NONE)))] |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               socks := socks |++
                        [(sid,Sock(NONE,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,T,T,
                              TCP_Sock(st,cb,NONE)))] |>,
     SS,MM)

   <==

     st IN {TIME_WAIT;CLOSED;FIN_WAIT_2}
     (* SB: sndq and rcvq should now both be empty *)


   (*:

    @description

    A previous call to [[close()]] with the linger option set on the socket blocked leaving thread
    [[tid]] in the [[Close2(sid)]] state. The socket [[sid]] has successfully transmitted all the
    data in its send queue, [[sndq = []]], and has completed a graceful close of the connection: [[st
    IN {TIME_WAIT; CLOSED; FIN_WAIT_2}]].

    The rule proceeds via a [[Lh_tau]] transition leaving thread [[tid]] in the [[Ret(OK ())]]
    state to return successfully from the blocked [[close()]] call. The socket remains in a closed state.

    Note that the asychronous sending of any remaining data in the send queue and graceful closing of
    the connection is handled by other rules. This rule applies once these events have reached a
    successful conclusion.

    @internal

    (Originally thought naïvely: if [[sndq=[] /\ cantsndmore=T]] then we must have sent a FIN to the
    peer (we depend on this in the close rule that returns from a lingering close).  Hmm.  Not at
    all sure about this.  We do not want to return from a lingering close until we receive the ACK of
    the FIN we sent (K thinks this is the Right Way, it remains to be seen if UCB agreed with him.
    Alternative is to return from lingering close when received ACK of last data byte, as UNPv1p187.
    Looking at the BSD source for soclose etc suggests we check SS\_ISCONNECTED, which presumably
    has something to do TCP state rather than data emission); it's hard to see if this has happened
    from the socket state we have.  K thinks that soisdisconnected is called whenever we move to
    [[FIN_WAIT_2]] or [[TIME_WAIT]], and this clears SS\_ISCONNECTED.)

    SB: added the [[CLOSED]] state as this is entered after a succussful close from [[LAST_ACK]].

    If the data is successfully transmitted, as indicated by reaching a final state, return from the
    [[close()]] call.

    "If [fd] refers to a socket ... the socket [shall be] destroyed.  If the socket is in
    connection-mode, and the [[SO_LINGER]] option is set for the socket with non-zero linger time,
    and the socket has untransmitted data, then close shall block for up to the current linger
    interval until all data is transmitted."

    THIS RULE IS URGENT.

   :*)
   )

/\

   (!h ts tid
     sock socks
     sid sf es
     i1 p1 i2 p2 st cb d
     SS MM.

   close_6 /* rp_tcp, slow nonurgent fail (*: Fail with [[EAGAIN]]: unsuccessful completion of a lingering close on a synchronised socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Close2(sid),d));
               socks := socks |++ [(sid,sock)]
             |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EAGAIN),sched_timer));
               socks := socks |++ [(sid,sock)]
             |>,
     SS,MM)

   <==

     sock = Sock(NONE,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,T,T,
                 TCP_Sock(st,cb,NONE)) /\
     timer_expires d /\
     st NOTIN {TIME_WAIT; CLOSED}


   (*:

    @description

    A previous call to [[close()]] with the linger option set on the socket blocked, leaving thread
    [[tid]] in the [[Close2(sid)]] state. The linger timer has expired, [[timer_expires d]], before
    the socket has been successfully closed: [[st NOTIN {TIME_WAIT; CLOSED}]].

    The rule proceeds via a [[Lh_tau]] transition leaving thread [[tid]] in the [[Ret(FAIL EAGAIN)]]
    state to return error [[EAGAIN]] from the blocked [[close()]] call. The socket remains in a
    synchronised state and is not destroyed until the socket has been successfully closed by future
    asychronous events.


    The asychronous transmission of any remaining data in the send queue and the graceful closing of
    the connection is handled by other rules. This rule is only predicated on the unsuccessfulness
    of these operations, i.e. [[st NOTIN {TIME_WAIT; CLOSED}]]. When the linger timer expires the
    socket could be (a) still attempting to successfully transmit the data in the send queue, or (b)
    be someway through the graceful close operation. The exact state of the socket is not important
    here, explaining the relatively unconstrained socket state in the rule.

    @internal

    If the data is not successfully transmitted by the time the linger timer expires, return an
    error from the [[close()]] call.  We throw away any remaining data at this point (thus sending a
    FIN to the remote end, rather than a RST, even though we have not done a normal close - !!).
    This is the implication of UNPv1p188, but it seems unlikely.

    TODO: Hmm, in several of these, I should not be so strict on the Sock state.  For example, does
    it need to have an attached [[fid]] at this point?

   :*)
   )

/\

   (!h ts tid d fds fds'
     fd fid files socks
     sid ff sock tcp_sock
     SS SS' MM.

   close_7 /* rp_tcp, fast succeed (*: Successfully close the last file descriptor for a socket in the [[CLOSED]], [[SYN_SENT]] or [[SYN_RECEIVED]] states. :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               fds := fds;
               files := files |++ [(fid,File(FT_Socket(sid),ff))];
               socks := socks |++ [(sid,sock)] |>,
     SS,MM)
   -- Lh_call(tid,close(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()), sched_timer));
               fds := fds';
               files := files;
               socks := socks|>,
     SS',MM)

   <==

     (tcp_sock.st IN {CLOSED; SYN_SENT} \/
      tcp_sock.st = SYN_RECEIVED /\ ~linux_arch h.arch) /\
     TCP_PROTO(tcp_sock) = sock.pr /\
     fid NOTIN (FDOM files) /\
     sid NOTIN (FDOM socks) /\
     fd IN FDOM fds /\
     fid = fds ' fd /\
     fid_ref_count(fds,fid) = 1 /\
     fds' = fds \\ fd /\

     case tcp_sock.st IN {CLOSED;LISTEN} of
         T -> SS' = SS
         || F -> if exists_quad_of sock then
                 destroy (quad_of sock) SS SS'
             else SS' = SS


   (*:

    @description

    A [[close(fd)]] call is performed on the TCP socket [[sock]], identified by [[sid]] and
    referenced by file descriptor [[fd]] which is the only file descriptor referencing the socket's
    file description: [[fid_ref_count(fds,fid) = 1]]. The TCP socket [[sock]] is not in a
    synchronised state: [[st IN {CLOSED; SYN_SENT}]].

    The [[close(fd)]] call proceeds by a [[Lh_call(tid,close(fd))]] transition leaving the host in
    the successful return state [[Ret (OK ())]].

    The mapping of file descriptor [[fd]] to file descriptor index [[fid]] is removed from the
    host's finite map of file descriptors; the file description entry for [[fid]] is removed from
    the host's finite map of file descriptors; and the socket entry [[(sid,sock)]] is removed from
    the host's finite map of sockets.

    @variation Linux

    The rule does not apply if the socket is in state [[SYN_RECEIVED]]: for the purposes of
    [[close()]] this is treated as a synchronised state on Linux.


    Note that the socket [[sock]] is not in a synchronised state and thus has no data in its send queue ready
    for transmission. Closing an unsynchronised socket simply involves deleting the socket entry and
    removing all references to it. These operations are performed immediately by the rule, hence the
    socket's [[SO_LINGER]] option is not constrained because it has no effect regardless of how it
    may be set.

    @internal

    If the user calls [[close()]] on a socket that is in the closed state, we free the socket, open
    file description, and file descriptor.  We do the same for [[SYN_SENT]], as one can easily see
    by reading the BSD source code.

    SB believes closing a [[SYN_RECEIVED]] socket has the same behaviour, except on Linux.

    Easy case; have not opened a connection anyway.

    Keith at one time thought, in a POSIXy fashion, that this was sensible:

    If the user calls [[close()]] on a socket in the [[SYN_SENT]] state (i.e., it has asked TCP to
    initiate a connection but not yet received a response), we free the open file description and
    file descriptor, and move to the [[Close1]] state to send the FIN and free the socket (see
    [[close_2a]]).

    REMARK presumably sockets should also die if the quad is altered

   :*)
   )

/\

   (!h ts tid d fds fds'
     fd fid files socks socks' listen listen' oq oq'
     sid ff sock lis sf is1 p1 es cb
     socks_to_rst cantsndmore cantrcvmore
     SS SS' SS'' MM.

   close_8 /* rp_tcp, fast succeed (*: Successfully close the last file descriptor for a listening TCP socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               fds := fds;
               files := files |++ [(fid,File(FT_Socket(sid),ff))];
               socks := socks |++ [(sid,sock)];
               listen := listen;
               oq    := oq |>,
     SS,MM)
   -- Lh_call (tid,close(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()), sched_timer));
               fds := fds';
               files := files;
               socks := socks';
               listen := listen';
               oq    := oq' |>,
     SS'',MM)

   <==

     sock = Sock(SOME fid,sf,is1,SOME p1,NONE,NONE,es,cantsndmore,cantrcvmore,
                 TCP_Sock(LISTEN,cb,SOME lis)) /\
     fd IN FDOM fds /\
     fid = fds ' fd /\
     fid_ref_count(fds,fid) = 1 /\
     fid NOTIN (FDOM files) /\
     sid NOTIN (FDOM socks) /\

     (*: cantrcvmore/cantsndmore unconstrained under BSD, as may have previously called shutdown :*)
     (*: MS: this is more of an assertion than a condition, so we could get away without it :*)
     (bsd_arch h.arch \/ (cantsndmore = F /\ cantrcvmore = F)) /\

     (*: BSD and Linux do not send RSTs to sockets on [[lis.q0]]. :*)
     socks_to_rst = { sock' | ?sid' tcp_sock'. sid' IN' lis.q /\
                                                       (* previously: APPEND lis.q0 lis.q *)
                                                 sock' = socks ' sid' /\
                                                 TCP_PROTO(tcp_sock') = sock'.pr /\
                                                 tcp_sock'.st NOTIN {CLOSED;LISTEN;SYN_SENT} } /\

     FDOM SS' = FDOM SS /\

     (! sock'. sock' IN socks_to_rst ==>
         let (i1,p1,i2,p2) = quad_of sock' in
         let streamid = streamid_of_quad (i1,p1,i2,p2) in
         ? oflgs odata.
         oflgs = oflgs with <| SYN := F; SYNACK := F; RST := T |> /\
         odata IN UNIV /\
         write (i1,p1,i2,p2) (oflgs,odata) (SS ' streamid) (SS' ' streamid)) /\

     (! streamid :: FDOM SS.
         ~ (streamid IN (IMAGE (streamid_of_quad o quad_of) socks_to_rst)) ==>
         SS' ' streamid = SS ' streamid) /\

     fds' = fds \\ fd /\
     listen' = FILTER (\sid'. sid' <> sid) listen /\
     socks' = DRESTRICT socks { sid' |  sid' NOTIN APPEND lis.q0 lis.q} /\

     (*: [[removed_sids]] does not include sid :*)
     let removed_sids = { sid' |  sid' IN' APPEND lis.q0 lis.q} in
     let removed_socks = {sock} UNION {sock'| ? sid'. sid' IN removed_sids /\
                                              socks ' sid' = sock'} in
     let destroyed = { (i1,p1,i2,p2) | ? sock. sock IN removed_socks /\
                      (sock.is1,sock.ps1,sock.is2,sock.ps2) = (SOME i1,SOME p1,SOME i2,SOME p2) } in

     (*: Some streams are destroyed :*)
     destroy_quads destroyed SS' SS''


   (*:

    @description

    A [[close(fd)]] call is performed on the TCP socket [[sock]] referenced by file descriptor
    [[fd]] which is the only file descriptor referencing the socket's file description [[fid]],
    [[fid_ref_count(fds,fid) = 1]]. Socket [[sock]] is locally bound to port [[p1]] and one or more
    local IP addresses [[is1]], and is in the [[LISTEN]] state.

    The listening socket [[sock]] may have [[ESTABLISHED]] incoming connections on its connection
    queue [[lis.q]] and incomplete incoming connection attempts on queue [[lis.q0]]. Each
    connection, regardless of whether it is complete or not, is represented by a [[socket]]
    entry in [[h.socks]] and its corresponding index [[sid]] is on the respective queue. These
    connections have not been accepted by any thread through a call to [[accept()]] and are dropped
    on the closure of socket [[sock]].

    A set of reset seqments [[rsts_to_go]] is created for each of the sockets referenced by both queues. This is
    performed by looking up each socket [[sock']] for every [[sid']] in the concatentation of both
    queues, [[APPEND lis.q0 lis.q]], and extracting their address quads
    [[(sock'.is1,sock'.is2,sock'.ps1,sock'.ps2)]] and control blocks [[cb]].

    The [[close(fd)]] call proceeds by a [[Lh_call(tid,close(fd))]] transition leaving the host in
    the successful return state [[Ret (OK ())]].

    @modeldetails

    The local IP address option [[is1]] of the socket [[sock]] is not constrained in this
    rule. Instead it is constrained by other rules for [[bind()]] and [[listen()]] prior to the
    socket entering the [[LISTEN]] state.

    @internal

    If the user calls [[close()]] on a socket in the listening state, we free the socket, open file
    description, and file descriptor, and remove the socket from the list of listening sockets.
    Further, abort each lis.q0 entry and each lis.q entry: for each, do [[tcp_drop_and_close]],
    i.e., RST if [[SYN_RECEIVED]] or later (else nothing), and drop the tcpcb.

    On checking the BSD code: BSD sockets layer calls [[soabort()]] on each socket in each of the
    two queues.  [[tcp_usr_abort()]] is the protocol routine; it calls [[tcp_drop()]] with
    [[ECONNABORTED]].  This function is just our [[tcp_drop_and_close]].  The code above has the
    same effect; most of what [[tcp_drop_and_close]] does is invisible for these sockets, because
    they truly go away.

   :*)
   )


/\


   (!h ts d fds files fid sid ff fds' tid
     socks sf is1 ps1 is2 ps2 es udp fd cantsndmore cantrcvmore
     SS MM.

   close_10 /* rp_udp, fast succeed (*: Successfully close the last file descriptor of a UDP socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               fds := fds;
               files := files |++ [(fid,File(FT_Socket(sid),ff))];
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,cantsndmore,cantrcvmore,
                                   UDP_PROTO(udp)))] |>,
     SS,MM)
   -- Lh_call (tid,close(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               fds := fds';
               files := files;
               socks := socks |>,
     SS,MM)

  <==

    fd IN FDOM fds /\
    fid = fds ' fd /\
    fid_ref_count(fds,fid) = 1 /\
    fds' = fds \\ fd /\
    fid NOTIN (FDOM files) /\
    sid NOTIN (FDOM socks)


   (*:

    @description

    Consider a UDP socket [[sid]], referenced by [[fd]], with a file description record indexed by
    [[fid]]. [[fd]] is the only open file descriptor referring to the file description record
    indexed by [[fid]], [[fid_ref_count(fds,fid) = 1]]. From thread [[tid]], which is in the [[Run]]
    state, a [[close(fd)]] call is made and succeeds.

    A [[Lh_call(tid,close(fd))]] transition is made, leaving the thread state [[Ret (OK())]]. The
    socket [[sid]] is removed from the host's finite map of sockets [[socks]]$\oplus\dots$, the
    file description record indexed by [[fid]] is removed from the host's finite map of file
    descriptions [[files]]$\oplus\dots$, and [[fd]] is removed from the host's finite map of file
    descriptors [[fds' = fds \\ fd]].

    @internal

    What about threads blocked in Recv2, Send2, PSelect2 on this socket?

    :*)

   )


/\

(*:

@section [[connect]] ALL [[connect()]]
 \[ <[connect: fd * ip * port option -> unit]> \]

  A call to [[connect(fd,ip,port)]] attempts to connect a TCP socket to a peer, or to set the peer
  address of a UDP socket.
  Here [[fd]] is a file descriptor referring to a socket,
  [[ip]] is the peer IP address to connect to, and [[port]] is the peer port.

  If [[fd]] refers to a TCP socket then TCP's connection establishment protocol, often called the
  \textit{three-way handshake}, will be used to connect the socket to the peer specified by
  [[(ip,port)]]. A peer port must be specified: [[port]] cannot be set to [[NONE]]. There must be a
  listening TCP socket at the peer address, otherwise the connection attempt will fail with an
  [[ECONNRESET]] or [[ECONNREFUSED]] error. The local socket must be in the [[CLOSED]] state: attempts to
  [[connect()]] to a peer when already synchronised with another peer will fail. To start
  the connection establishment attempt, a [[SYN]] segment will be constructed, specifying the
  initial sequeunce number and window size for the connection, and possibly the maximum segment
  size, window scaling, and timestamping.  The segment is then
  enqueued on the host's out-queue; if this fails then the [[connect()]] call fails, otherwise
  connection establishment proceeds.

  If the socket is a blocking one (the [[O_NONBLOCK]] flag for [[fd]] is not set), then the call
  will block until the connection is established, or a timeout expires in which case the error
  [[ETIMEDOUT]] is returned.

  If the socket is non-blocking (the [[O_NONBLOCK]] flag is set for [[fd]]), then the [[connect()]]
  call will fail with an [[EINPROGRESS]] error (or [[EALREADY]] on WinXP), and connection
  establishment will proceed asynchronously.

  Calling [[connect()]] again will indicate the current status of the connection establishment in
  the returned error: it will fail with [[EALREADY]] if the connection has not been established,
  [[EISCONN]] once the connection has been established, or if the connection establishment failed,
  an error describing why. Alternatively, [[pselect([],[fd],[],NONE,_)]] can be used; it will return
  when [[fd]] is ready for writing which will be when connection establishment is complete, either
  successfully or not. On Linux, unsetting the [[O_NONBLOCK]] flag for [[fd]] and then calling
  [[connect()]] will block until the connection is established or fails; for WinXP the call will
  fail with [[EALREADY]] and the connection establishment will be performed asynchronously still;
  for FreeBSD the call will fail with [[EISCONN]] even if the connection has not been established.

  Upon completion of connection establishment the socket will be in state [[ESTABLISHED]], ready to
  send and receive data, or [[CLOSE_WAIT]] if it received a FIN segment during connection
  establishment.

  On FreeBSD, if connection establishment fails having sent a [[SYN]] then further connection
  establishment attempts are not allowed; on Linux and WinXP further attempts are possible.

  If [[fd]] refers to a UDP socket then the peer address of the socket is set, but no connection is
  made. The peer address is then the default destination address for subsequent [[send()]] calls
  (and the only possible destination address on FreeBSD), and only datagrams with this source
  address will be delivered to the socket. On FreeBSD the peer port must be specified: a call to
  [[connect(fd,ip,NONE)]] will fail with an [[EADDRNOTAVAIL]] error; on Linux and WinXP such a call
  succeeds: datagrams from any port on the host with IP address [[ip]] will be delivered to the
  socket. Calling [[connect()]] on a UDP socket that already has a peer address set is allowed: the
  peer address will be replaced with the one specified in the call. On FreeBSD if the socket has a
  pending error, that may be returned when the call is made, and the peer address will also be set.

  In order for a socket to connect to a peer or have its peer address set, it must be bound to a
  local IP and port. If it is not bound to a local port when the [[connect()]] call is made, then it
  will be autobound: an unused port for the socket's protocol in the host's ephemeral port range is
  selected and assigned to the socket. If the socket does not have its local IP address set then it
  will be bound to the primary IP address of an interface which has a route to the peer. If the
  socket does have a local IP address set then the interface that this IP address will be the
  one used to connect to the peer; if this interface does not have a route to the peer then for a
  TCP socket the [[connect()]] call will fail when the SYN is enqueued on the host's outqueue; for a
  UDP socket the call will  fail on FreeBSD, whereas on Linux and WinXP the [[connect()]] call will
  succeed but later [[send()]] calls to the peer will fail.

  For a TCP socket, its binding quad must be unique: there can be no other socket in the host's
  finite map of sockets with the same binding quad. If the [[connect()]] call would result in two
  sockets having the same binding quad then it will fail with an [[EADDRINUSE]] error. For UDP
  sockets the same is true on FreeBSD, but on Linux and WinXP multiple sockets may have the same
  address quad. The socket that matching datagrams are delivered to is architecture-dependent: see
  {[[lookup]]}.


@errors

  A call to [[connect()]] can fail with the errors below, in which case the corresponding exception
  is raised:

  @error [[EADDRNOTAVAIL]] There is no route to the peer; a port must be specified ([[port <> NONE]]); or
  there are no ephemeral ports left.

  @error [[EADDRINUSE]] The address quad that would result if the connection was successful is in
  use by another socket of the same protocol.

  @error [[EAGAIN]] On WinXP, the socket is non-blocking and the connection cannot be established
  immediately: it will be established asynchronously. [TCP ONLY]

  @error [[EALREADY]] A connection attempt is already in progress on the socket but not
  yet complete: it is in state [[SYN_SENT]] or [[SYN_RECEIVED]]. [TCP ONLY]

  @error [[ECONNREFUSED]] Connection rejected by peer. [TCP ONLY]

  @error [[ECONNRESET]] Connection rejected by peer. [TCP ONLY]

  @error [[EHOSTUNREACH]] No route to the peer.

  @error [[EINPROGRESS]] The socket is non-blocking and the connection cannot be established
  immediately: it will be established asynchronously. [TCP ONLY]

  @error [[EINVAL]] On WinXP, socket is listening. [TCP ONLY]

  @error [[EISCONN]] Socket already connected. [TCP ONLY]

  @error [[ENETDOWN]] The interface used to reach the peer is down.

  @error [[ENETUNREACH]] No route to the peer.

  @error [[EOPNOTSUPP]] On FreeBSD, socket is listening. [TCP ONLY]

  @error [[ETIMEDOUT]]  The connection attempt timed out before a connection was established for a socket. [TCP ONLY]

  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]
  @errorinclude [[misc]] [[EINTR]]
  @errorinclude [[misc]] [[ENOBUFS]]

@commoncases

  TCP: [[socket_1]]; [[connect_1]]; $\dots$

  UDP: [[socket_1]]; [[bind_1]]; [[connect_8]]; $\dots$


@api

  \begin{tabular}{ll}
    Posix:  &  |int connect(int socket, const struct sockaddr *address, socklen_t address_len);| \\
    FreeBSD:&  |int connect(int s, const struct sockaddr *name, socklen_t namelen);| \\
    Linux:  &  |int connect(int sockfd, constr struct sockaddr *serv_addr, socklen_t addrlen);| \\
    WinXP:  &  |int connect(SOCKET s, const struct sockaddr* name, int namelen);| \\
  \end{tabular}\\

  In the Posix interface:

  \begin{itemize}

    \item |socket| is a file descriptor referring to the socket to make a connection on,
    corresponding to the [[fd]] argument of the model [[connect()]].

    \item |address| is a pointer to a |sockaddr| structure of length
    |address_len| specifying the peer to connect to. |sockaddr| is a generic socket
    address structure: what is used for the model [[connect()]] is an internet socket
    address structure |sockaddr_in|. The |sin_family| member is set to
    |AF_INET|; the |sin_port| is the port to connect to, corresponding to the
    [[port]] argument of the model [[connect()]]: |sin_port = 0| corresponds to
    [[port=NONE]] and |sin_port=p| corresponds to [[port = SOME p]]; the
    |sin_addr.s_addr| member of the structure corresponds to the [[ip]] argument of the
    model [[connect()]].

   \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual
     error code available through a call to |WSAGetLastError()|.

  \end{itemize}

  The FreeBSD, Linux and WinXP interfaces are similar modulo argument renaming, except where
  noted above.

  Note: For UDP sockets, the Winsock Reference says "The default destination can be changed by
  simply calling connect again, even if the socket is already connected. Any datagrams queued for
  receipt are discarded if name is different from the previous connect." This is not the
  case.

@modeldetails

  If the call blocks then the thread enters state [[Connect2(sid)]] where [[sid]] is the identifier
  of the socket attempting to establish a connection.

  The following errors are not modelled:

  \begin{itemize}

    \item |EAFNOSUPPORT| means that the specified address is not a valid address for the
    address family of the specified socket. The model [[connect()]] only models the
    |AF_INET| family of addresses so this error cannot occur.

    \item |EFAULT| signifies that the pointers passed as either the |address| or
     |address_len| arguments were inaccessible.  This is an artefact of the C interface to
     [[connect()]] that is excluded by the clean interface used in the model.

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

    \item |EINVAL| is a Posix-specific error signifying that the |address_len|
    argument is not a valid length for the socket's address family or invalid address family in the
    |sockaddr| structure. The length of the address to connect to is implicit in the model
    [[connect()]], and only the |AF_INET| family of addresses is modelled so this error
    cannot occur.

   \item |EPROTOTYPE| is a Posix-specific error meaning that the specified address has a
   different type than the socket bound to the specified peer address. This error does not occur in
   any of the implementations as TCP and UDP sockets are dealt with seperately.

   \item |EACCES|, |ELOOP|, and |ENAMETOOLONG| are errors dealing with Unix
   domain sockets which are not modelled here.

  \end{itemize}

:*)

   (!h h0 h' ts_ socks tid d oq oq' cb' cb'' cb''' es es' es'' t'
     fd fid ff sid sf st cantsndmore cantrcvmore bound
     cb is1 ps1 i2 p2 i1' p1' is2 ps2 err rc is2' ps2'
     st'
     queued oflgs odata SS SS' s s' MM.
   connect_1 /* rp_tcp, rc (*: Begin connection establishment by creating a SYN and trying to enqueue it on host's outqueue :*) */
     (h,SS,MM)
   -- Lh_call (tid,connect(fd,i2,SOME p2)) -->
     (h',SS',MM)

   <==

     (* note that we must write ts_ for the h.ts variable, because ts is used for timestamps *)
     (* we presume sock.es is NONE both before and after this rule *)

     (* REMARK this rule has been split into two to cope with BSD specific behaviour *)

     (*: Thread [[tid]] is in state [[Run]] and TCP socket [[sid]] has binding quad [[(is1,ps1,is2,ps2)]].  :*)
     h  = h0 with <| ts := FUPDATE ts_ (tid,Timed(Run,d));
                     socks := socks |++
                             [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,cantsndmore,cantrcvmore,
                               TCP_Sock(st,cb,NONE)))] ;
                     oq := oq |> /\

     (*: Thread [[tid]] ends in state [[t']] with updated host sockets and output queue :*)
     h' = h0 with <| ts := FUPDATE ts_ (tid,t');
                     socks := socks |++
                              [(sid,Sock(SOME fid,sf,SOME i1',SOME p1',is2',ps2',es'',F,F,
                                TCP_Sock(st',cb''',NONE)))] ;
                     bound := bound;
                     oq := oq' |> /\

     (*: File descriptor [[fd]] refers to TCP socket [[sid]] :*)
     fd IN FDOM h0.fds /\
     fid = h0.fds ' fd /\
     h0.files ' fid = File(FT_Socket(sid),ff) /\

     (*: Either [[sid]] is bound to a local IP address or one of the host's interface has a route to
     [[i2]] and [[i1']] is one of its IP addresses.  If it is not routable, then we will fail below,
     when we try to enqueue the segment. :*)

     i1' IN auto_outroute(i2,is1,h.rttab,h.ifds) /\
       (*: Notice that [[auto_outroute]] never fails if [[is1<>NONE]] (i.e., is specified in the socket). :*)

     (*: The socket is either bound to a local port [[p1']] or can be autobound to an ephemeral port [[p1']] :*)
     p1' IN autobind(ps1,PROTO_TCP,h,h.socks) /\
     (*: If autobinding occurs then [[sid]] is added to the head of the host's list of bound sockets. :*)
     (if ps1 = NONE then bound = sid::h.bound else bound = h.bound) /\

     (*: The socket can be in one of two states: (1) it is in state [[CLOSED]] in which case its
         peer address is not set; it has no pending error; it is not shutdown for writing; and it is
         not shutdown for reading on non-FreeBSD architectures. Otherwise, (2) on FreeBSD the socket
         is in state [[TIME_WAIT]], and either [[is2]] and [[ps2]] are both set or both are not set.
       The fact that BSD allows a [[TIME_WAIT]] socket to be reconnected means that some
       fields may contain old data, so we leave them unconstrained here. This is particularly
       important in the [[cb]].
     :*)

     (st = CLOSED /\ is2 = NONE /\ ps2 = NONE /\
       es = NONE /\ cantsndmore = F /\ (cantrcvmore = F \/ bsd_arch h.arch)) /\

     (*: No other TCP sockets on the host have the address quad [[(SOME i1',SOME p1',SOME i2,SOME p2)]]. :*)
     ~(? (sid', s) :: (h.socks \\ sid).
                  s.is1 = SOME i1' /\ s.ps1 = SOME p1' /\
                  s.is2 = SOME i2  /\ s.ps2 = SOME p2  /\
                  proto_of s.pr = PROTO_TCP) /\

     cb' = cb /\

     (*: now build the segment (using an auxiliary, since we might have to retransmit it) :*)

     (*: Make a [[SYN]] segment based on the updated control block and the socket's address quad;
     see {@link [[make_syn_flgs_data]]} for details. :*)
     (oflgs,odata) IN make_syn_flgs_data /\

     (*: and send it out... :*)

     (*: If possible, enqueue the segment [[seg]] on the host's outqueue. The auxiliary function
     {@link [[stream_rollback_tcp_output]]} is used for this; if the segment is a well-formed segment,
     there is a route to the peer from [[i1']], and there are no buffer allocation failures,
     [[outsegs' <> []]], then the segment is enqueued on the host's outqueue, [[oq]], resulting in a
     new outqueue, [[oq']]. The socket's control block is left as [[cb']] which is described
     above. Otherwise an error may have occurred; possible errors are: (1) [[ENOBUFS]] indicating a
     buffer allocation failure; (2) a routing error; or (3) [[EADDRNOTAVAIL]] on FreeBSD or
     [[EINVAL]] on Linux indicating that the segment would cause a loopback packet to appear on the
     wire (on WINXP the segment is silently dropped with no error in this case). If an error does
     occur then the socket's control block reverts to [[cb]], the control block when the call was
     made. :*)
     ?outsegs'.  (* inline enqueue_or_fail because we need the error code *)
     stream_rollback_tcp_output F (SOME i1', SOME i2) h.arch h.rttab h.ifds cb' (cb'',es',outsegs') /\
     cb''' = (if (outsegs' \/ windows_arch h.arch) then cb'' else cb) /\
     (INFINITE_RESOURCES ==> queued) /\

      (* if nonblocking requested and no prior pending error, "fail" but keep going in background.
        NB. it seems valid to either fail with EAGAIN (or equivalent) or return any fast error
        generated by tcp_output (due to unrouteable destination etc, etc)
        Otherwise, block until connection complete. *)
     (*: If the socket is a blocking one, its [[O_NONBLOCK]] flag is not set, then the call will
         block, entering state [[Connect2(sid)]] and leaving the socket in state [[SYN_SENT]] with
         peer address [[(SOME i2,SOME p2)]] and, if the segment could not be enqueued, its pending
         error set to the error resulting from the attempt to enqueue the segment.

	 If the socket is non-blocking, its [[O_NONBLOCK]] flag is set, and the segment was enqueued
	 on the host's outqueue, then the call will fail with an [[EINPROGRESS]] error (or [[EAGAIN]]
	 on WinXP). The socket will be left in state [[SYN_SENT]] with peer address [[(SOME i2,SOME
	 p2)]]. Otherwise, if the segment was not enqueued, then the call will fail with the error
	 resulting from attempting to enqueue it, [[SOME err]]; the socket will be left in state
	 [[CLOSED]] with no peer address set.
     :*)

      (*: In the case of BSD, if we connect via the loopback interface, then the segment exchange
         occurs so fast that the socket has connected before the connect-calling thread regains control.
         When it does, it sees that the socket has been connected, and therefore returns with success
         rather than [[EINPROGRESS]]. Since this behaviour is due to timing, however, it may be possible
         for the connect call to return before all the segments have been sent, for example if there
         was an artificially imposed delay on the loopback interface. This behaviour is therefore
         made nondeterministic, for a BSD non-blocking socket connecting via loopback, in that it may
         either fail immediately, or be blocked for a short time.
         Linux does not exhibit this behaviour.:*)

     ((*: blocking socket, or BSD and using loopback interface :*)
      ((~ff.b(O_NONBLOCK) \/ (bsd_arch h.arch /\ i2 IN local_ips h.ifds)) /\
          t' = Timed(Connect2(sid),never_timer) /\ rc = block /\
	  es''=es' /\ st' = SYN_SENT /\ is2' = SOME i2 /\ ps2' = SOME p2 /\
            s = initial_streams (i1',p1',i2,p2) /\
            write (i1',p1',i2,p2) (oflgs,odata) s s' /\
            SS' = SS |++ [(streamid_of_quad (i1',p1',i2,p2),s')]) \/
      (*: non-blocking socket :*)
      (ff.b(O_NONBLOCK) /\
          es = NONE /\
          (err = (if windows_arch h.arch then EAGAIN else EINPROGRESS) \/ SOME err = es') /\
          t' = Timed(Ret(FAIL err),sched_timer) /\ rc = fast fail /\ es''=NONE /\
	  if ~queued then
	      st' = CLOSED /\ is2' = NONE /\ ps2' = NONE /\
              (*: under BSD [[st]] could be [[TIME_WAIT]] :*)
              (*: REMARK this fail quick behaviour breaks abstraction boundaries :*)
              SS' = SS
	  else
	      st' = SYN_SENT /\ is2' = SOME i2 /\ ps2' = SOME p2 /\
                s = initial_streams (i1',p1',i2,p2) /\
                write (i1',p1',i2,p2) (oflgs,odata) s s' /\
                SS' = SS |++ [(streamid_of_quad (i1',p1',i2,p2),s')])
     )


   (*:

   @description

   From thread [[tid]], a [[connect(fd,i2,SOME p2)]] call is made where [[fd]] refers to a TCP
   socket. The socket is in state [[CLOSED]] with no peer address set, no pending error, and not
   shutdown for reading or writing. A [[SYN]] segment is created to being connection establishment,
   and is enqueued on the host's out-queue.

   If the socket is a blocking one (its [[O_NONBLOCK]] flag is not set) then the call will block: a
   [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition is made, leaving the thread state
   [[Connect2(sid)]]. If the socket is non-blocking (its [[O_NONBLOCK]] flag is set) and the segment
   enqueuing was successful then the call will fail: a [[Lh_call(tid,connect(fd,i2,SOME p2))]]
   transition is made, leaving the thread state [[Ret (FAIL EINPROGRESS)]] (or [[Ret (FAIL
   EAGAIN)]] on WinXP); connection establishment will proceed asynchronously. Otherwise, if the enqueueing did not succeed, the call will fail with an
   error [[err]]: a [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition is made, leaving the thread
   in state [[Ret (FAIL err)]].

   For further details see the in-line comments above.


   @variation FreeBSD

   The socket may also be in state [[TIME_WAIT]] when the [[connect()]] call is made, with either
   both its peer IP and port set, or neither set.

   The socket may be shutdown for reading when the [[connect()]] call is made.

   @variation WinXP

   If there is an early buffer allocation failure when enqueuing the segment, then it will not be
   placed on the host's out-queue and [[es' = ENOBUFS]]; the socket's control block will be [[cb']]
   with its [[snd_nxt]] and [[snd_max]] fields set to the intial sequence number, its
   [[last_ack_seen]] and [[rcv_adv]] fields set to [[0]], its [[tt_delack]] option set to [[NONE]],
   its [[tt_rexmt]] timer stopped, and its [[tf_rxwin0sent]] and [[t_rttseg]] fields reset.

   If there is no route from an interface specified by the local IP address [[i1]] to the foreign IP
   address [[i2]] then the socket's control block will be [[cb']] with its [[snd_next]] field set to the
   initial sequence number, its [[last_ack_sent]] and [[rcv_adv]] fields set to [[0]], and its
   [[tt_delack]] option set to [[NONE]].

   If the segment would case a loopback packet to be sent on the wire then the socket's control
   block will be [[cb']].

   @internal

   If the user calls [[connect()]] on a socket in the closed state, the socket is autobound if no
   local port was specified before, and if no local IP was specified before then an IP is chosen
   that belongs to the interface from which packets for the given destination will be sent.  Then
   the socket moves to the [[SYN_SENT]] state, and we move to the [[Connect2]] state to wait for the
   connection request to succeed or fail.


   POSIX: "If the socket has not already been bound... shall bind it...".

   POSIX: we consider particularly the "If the initiating socket is connection-mode" paragraph.

   So if [[is1]] is NONE, where exactly does it get filled in?  I'm assuming here, for now.

   We go into [[SYN_SENT]] immediately, to avoid a race between the actual connection initiation and
   another thread doing a [[connect()]].

   This is a kind-of blocking rule, except that the timer on the intermediate state is zero,
   requiring it to happen immediately (but not necessarily at the next transition!!).

   --comments from connect\_1a--

   The connection initiation continues by sending a request to the network to create a
   [[tcpInitiator]] object.

   POSIX: we consider particularly the "If the initiating socket is connection-mode" paragraph.

   POSIX: "[[connect()]] shall block for up to an unspecified timeout interval...".

   --comments from connect\_1b--

   TCP is incapable of establishing the connection immediately (ever!), so if the connect() call was
   nonblocking, we send the request to the network to create a [[tcpInitiator]] object, but then
   fail immediately, with the "error" indicating that the connection request is in progress.

   POSIX: "If the connection cannot be established immediately and O\_NONBLOCK is
   set... [[connect()]] shall fail ... [[EINPROGRESS]], but the connection request shall not be
   aborted, and the connection shall be established asynchronously.


   --OLD DESCRIPTION--

   From thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i2,SOME p2)]] call is
   made. [[fd]] refers to a TCP socket identified by [[sid]] with address quad
   [[(is1,ps1,is2,ps2)]]. The socket is uninitialised: it is in state [[CLOSED]] with control block
   [[cb]], empty send and receive queues, no urgent pointers set, no out-of-band data, does not have
   a peer address set, [[is2=NONE /\ ps2=NONE]], has no pending error, and is not shutdown for
   reading or writing.

   The socket either has its local IP address set to [[i1']], or there is an IP address [[i1']] for
   one of the host's interfaces that has a route to the host with IP address [[i2]]. If the socket
   is not bound to a local port [[p1']] then it can be autobound to a local port [[p1']] using
   {@link [[autobind]]}.There are no other TCP sockets in the host's finite map of sockets,
   [[h.socks]], with the binding quad [[(SOME i1',SOME p1',SOME i2, SOME p2)]].

   [[seg]] is a [[SYN]] segment to initiate connection establishment with:

   \begin{itemize}

   \item source address (i1',p1') and destination address (i2,p2);

   \item an initial sequence number for the connection, [[iss]];

   \item the [[SYN]] flag set;

   \item the receive window set to [[rcv_wnd]]. [[rcv_wnd0]] is a window value between [[0]] and
   [[TCP_MAXWIN]]. If the window scale option is to be requested for the connection
   ([[request_r_scale=SOME n]]) then [[rcv_wnd]] is [[rcv_wnd0]] scaled by the window scale value
   specified by [[request_r_scale]] and clipped to a 16-bit value; if window scaling is not to be
   requested ([[request_r_scale=NONE]]) then [[rcv_wnd = rcv_wnd0]]. Additionally, [[rcv_wnd]] is
   not greater than the size of the socket's receive buffer: [[rcv_wnd <= sf.n(SO_RCVBUF)]].

   \item If [[advmss'=SOME v]] then the maximum segment size, [[v]] will be sent with the [[SYN]];

   \item if time-stamping is to be requested for the connection, [[tf_req_tstmp'=T]], then a
   timestamp will be included in the TCP options, specifying the current time and, as this is a
   [[SYN]], an echo reply value of [[0]].

   \item The [[URG]], [[ACK]], [[PSH]], [[RST]], and [[FIN]] flags are not set, and the
   acknowledgement number and urgent pointer are set to arbitrary values.

   \end{itemize}

   If there is not a segment currently being timed for this socket then the [[SYN]] segment will be
   timed with [[t_rttseg']] set to the current time and the initial sequence number for the
   connection.

   The socket's control block will be updated:

   \begin{itemize}

   \item the retransmit and connection establishment timers will be started;

   \item the [[snd_una]] field will be set to the initial sequence number;

   \item the [[snd_max]] and [[snd_nxt]] fields will be set to the initial sequence number plus one;

   \item the [[iss]] field will be set to the initial sequence number;

   \item the [[rcv_wnd]] field will be set to the opening receive window for the connection;

   \item the [[rcv_adv]] field will be set to [[cb.rcv_nxt + rcv_wnd]];

   \item the [[tf_rxwin0sent]] field will be set to [[T]] if a zero length receive window was set or
   [[F]] otherwise;

   \item the [[request_r_scale]] field will record if window scaling was requested and, if so, the
   scale requested;

   \item the [[t_maxseg]] will be set to the maximum segment size for the connection, whether or not
   it is transmitted in the [[SYN]] segment;

   \item the [[t_advmss]] field will be set to [[SOME v]] if the MSS [[v]] was sent with the [[SYN]]
   or [[NONE]] otherwise;

   \item the [[tf_req_tstmp]] field will be set to [[T]] if time-stamping was requested, or [[F]] otherwise;

   \item the [[last_ack_sent]] field will be set to [[0]];

   \item and if the [[SYN]] segment will be timed then the [[t_rttseg]] field will be updated to
   record the time and sequence number of the segment.

   \end{itemize}

   The new control block is [[cb']].

   The [[SYN]] segment [[seg]] shall be placed on the host's outqueue if possible. If there is a
   buffer allocation failure during this then the segment cannot be placed on the host's outqueue:
   [[outsegs' = []]] and [[es' = ENOBUFS]]. If there is no route from an interface specified by the
   local IP address [[i1]] to the peer IP address [[i2]] then the segment cannot be placed on the
   host's outqueue: [[outsegs'=[]]] and [[es']] will be the routing error. If the segment would
   cause the a loopback packet to appear on the wire (something prohibited by RFC 1122), then the
   segment cannot be placed on the host's outqueue; additionally on FreeBSD the [[es'=SOME
   EADDRNOTAVAIL]], on Linux [[es'=SOME EINVAL]], and on WinXP there is no error: the segment is
   silently dropped. All of the above failures result in the socket's control block being reset to
   [[cb]], the control block when the [[connect()]] call was made.

   Otherwise the segment can be placed on the host's outqueue, [[outsegs'=[(seg,queued)]]], using
   {@link [[enqueue_oq_list_qinfo]]} to create new outqueue [[oq']]. If this now fails due to a
   buffer allocation failure, [[queued = F]], then [[es'=ENOBUFS]], [[oq'=h.oq]], and the socket's
   control block is updated to set the [[snd_nxt]] field to the initial sequence number, the
   [[rcv_adv]] and [[last_ack_sent]] fields to [[0]], the [[tt_delack]] option to [[NONE]], and to
   stop the retransmit timer. If the segment is successfully enqueued on the host's outqueue then
   [[es'=NONE]] to create new outqueue [[oq']].

   If the call is made with non-blocking semantics, the [[O_NONBLOCK]] flag of the file description
   for the socket is set, and the socket does not have a pending error then the call will fail with
   either the error [[es']] resulting from a failed attempt to enqueue the [[SYN]] segment [[seg]];
   or an [[EINPROGRESS]] error on FreeBSD and Linux; or an [[EAGAIN]] error on WinXP. The
   [[EINPROGRESS]] and [[EAGAIN]] errors mean that connection establishment is proceeding
   asynchronously and [[connect()]] should be called again to see the result. A
   [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition will be made, leaving the thread state
   [[Ret (FAIL err)]]. If the call failed without enqueueing a [[SYN]] segment then the socket will
   be in state [[CLOSED]] with address quad [[(SOME i1',SOME p1',NONE,NONE)]]; otherwise it will be
   in state [[SYN_SENT]] with address quad [[(SOME i1',SOME p1',SOME i2,SOME p2)]]. In either case
   the pending error will be cleared.

   If the call is made with blocking semantics then it shall block, entering state
   [[Connect2(sid)]]. A [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition will be made leaving the
   thread state [[Connect2(sid)]]. The socket will be in state [[SYN_SENT]] with address quad
   [[(SOME i1',SOME p1',SOME i2,SOME p2)]] and pending error set to [[es']].

   In either case the host's out-queue will be [[oq']] and its list of bound sockets will be
   [[bound]], which shall have [[sid]] appended to its head if the socket was autobound to an
   ephemeral port.

   :*)
   )

/\

   (!h h0 h' ts_ socks tid d oq oq' cb' cb'' cb''' es es' es'' t'
     fd fid ff sid sf st cantsndmore cantrcvmore bound
     cb is1 ps1 i2 p2 i1' p1' is2 ps2 err rc is2' ps2'
     st'
     lbl
     queued oflgs odata
     SS MM SS' SS0 s s' .
   connect_1a /* rp_tcp, rc (*: Begin connection establishment by creating a SYN and trying to enqueue it on host's outqueue :*) */
     (h,SS,MM)
   -- lbl -->
     (h',SS',MM)

   <==

     (* note that we must write ts_ for the h.ts variable, because ts is used for timestamps *)
     (* we presume sock.es is NONE both before and after this rule *)

     (*: Thread [[tid]] is in state [[Run]] and TCP socket [[sid]] has binding quad [[(is1,ps1,is2,ps2)]].  :*)
     h  = h0 with <| ts := FUPDATE ts_ (tid,Timed(Run,d));
                     socks := socks |++
                             [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,cantsndmore,cantrcvmore,
                               TCP_Sock(st,cb,NONE)))] ;
                     oq := oq |> /\

     (*: Thread [[tid]] ends in state [[t']] with updated host sockets and output queue :*)
     h' = h0 with <| ts := FUPDATE ts_ (tid,t');
                     socks := socks |++
                              [(sid,Sock(SOME fid,sf,SOME i1',SOME p1',is2',ps2',es'',F,F,
                                TCP_Sock(st',cb''',NONE)))] ;
                     bound := bound;
                     oq := oq' |> /\

     (*: File descriptor [[fd]] refers to TCP socket [[sid]] :*)
     fd IN FDOM h0.fds /\
     fid = h0.fds ' fd /\
     h0.files ' fid = File(FT_Socket(sid),ff) /\

     (*: Either [[sid]] is bound to a local IP address or one of the host's interface has a route to
     [[i2]] and [[i1']] is one of its IP addresses.  If it is not routable, then we will fail below,
     when we try to enqueue the segment. :*)

     i1' IN auto_outroute(i2,is1,h.rttab,h.ifds) /\
       (*: Notice that [[auto_outroute]] never fails if [[is1<>NONE]] (i.e., is specified in the socket). :*)

     (*: The socket is either bound to a local port [[p1']] or can be autobound to an ephemeral port [[p1']] :*)
     p1' IN autobind(ps1,PROTO_TCP,h,h.socks) /\
     (*: If autobinding occurs then [[sid]] is added to the head of the host's list of bound sockets. :*)
     (if ps1 = NONE then bound = sid::h.bound else bound = h.bound) /\

     (*: The socket can be in one of two states: (1) it is in state [[CLOSED]] in which case its
         peer address is not set; it has no pending error; it is not shutdown for writing; and it is
         not shutdown for reading on non-FreeBSD architectures. Otherwise, (2) on FreeBSD the socket
         is in state [[TIME_WAIT]], and either [[is2]] and [[ps2]] are both set or both are not set.
       The fact that BSD allows a [[TIME_WAIT]] socket to be reconnected means that some
       fields may contain old data, so we leave them unconstrained here. This is particularly
       important in the [[cb]].
     :*)

     (bsd_arch h.arch /\ st = TIME_WAIT /\
       (is2 <> NONE ==> ps2 <> NONE) /\
         (ps2 <> NONE ==> is2 <> NONE)) /\

     (*: No other TCP sockets on the host have the address quad [[(SOME i1',SOME p1',SOME i2,SOME p2)]]. :*)
     ~(? (sid', s) :: (h.socks \\ sid).
                  s.is1 = SOME i1' /\ s.ps1 = SOME p1' /\
                  s.is2 = SOME i2  /\ s.ps2 = SOME p2  /\
                  proto_of s.pr = PROTO_TCP) /\

     cb' = cb /\

     (*: now build the segment (using an auxiliary, since we might have to retransmit it) :*)

     (*: Make a [[SYN]] segment based on the updated control block and the socket's address quad;
     see {@link [[make_syn_flgs_data]]} for details. :*)
     (oflgs,odata) IN make_syn_flgs_data /\

     (*: and send it out... :*)

     (*: If possible, enqueue the segment [[seg]] on the host's outqueue. The auxiliary function
     {@link [[rollback_tcp_output]]} is used for this; if the segment is a well-formed segment,
     there is a route to the peer from [[i1']], and there are no buffer allocation failures,
     [[outsegs' <> []]], then the segment is enqueued on the host's outqueue, [[oq]], resulting in a
     new outqueue, [[oq']]. The socket's control block is left as [[cb']] which is described
     above. Otherwise an error may have occurred; possible errors are: (1) [[ENOBUFS]] indicating a
     buffer allocation failure; (2) a routing error; or (3) [[EADDRNOTAVAIL]] on FreeBSD or
     [[EINVAL]] on Linux indicating that the segment would cause a loopback packet to appear on the
     wire (on WINXP the segment is silently dropped with no error in this case). If an error does
     occur then the socket's control block reverts to [[cb]], the control block when the call was
     made. :*)
     ?outsegs'.  (* inline enqueue_or_fail because we need the error code *)
     stream_rollback_tcp_output F (SOME i1', SOME i2) h.arch h.rttab h.ifds cb' (cb'',es',outsegs') /\
     cb''' = (if (outsegs' \/ windows_arch h.arch) then cb'' else cb) /\
     (INFINITE_RESOURCES ==> queued) /\

      (* if nonblocking requested and no prior pending error, "fail" but keep going in background.
        NB. it seems valid to either fail with EAGAIN (or equivalent) or return any fast error
        generated by tcp_output (due to unrouteable destination etc, etc)
        Otherwise, block until connection complete. *)
     (*: If the socket is a blocking one, its [[O_NONBLOCK]] flag is not set, then the call will
         block, entering state [[Connect2(sid)]] and leaving the socket in state [[SYN_SENT]] with
         peer address [[(SOME i2,SOME p2)]] and, if the segment could not be enqueued, its pending
         error set to the error resulting from the attempt to enqueue the segment.

	 If the socket is non-blocking, its [[O_NONBLOCK]] flag is set, and the segment was enqueued
	 on the host's outqueue, then the call will fail with an [[EINPROGRESS]] error (or [[EAGAIN]]
	 on WinXP). The socket will be left in state [[SYN_SENT]] with peer address [[(SOME i2,SOME
	 p2)]]. Otherwise, if the segment was not enqueued, then the call will fail with the error
	 resulting from attempting to enqueue it, [[SOME err]]; the socket will be left in state
	 [[CLOSED]] with no peer address set.
     :*)

      (*: In the case of BSD, if we connect via the loopback interface, then the segment exchange
         occurs so fast that the socket has connected before the connect-calling thread regains control.
         When it does, it sees that the socket has been connected, and therefore returns with success
         rather than [[EINPROGRESS]]. Since this behaviour is due to timing, however, it may be possible
         for the connect call to return before all the segments have been sent, for example if there
         was an artificially imposed delay on the loopback interface. This behaviour is therefore
         made nondeterministic, for a BSD non-blocking socket connecting via loopback, in that it may
         either fail immediately, or be blocked for a short time.
         Linux does not exhibit this behaviour.:*)

     ((*: blocking socket, or BSD and using loopback interface :*)
      ((~ff.b(O_NONBLOCK) \/ (bsd_arch h.arch /\ i2 IN local_ips h.ifds)) /\
          t' = Timed(Connect2(sid),never_timer) /\ rc = block /\
	  es''=es' /\ st' = SYN_SENT /\ is2' = SOME i2 /\ ps2' = SOME p2 /\
            (*: BSD and [[st=TIME_WAIT]], so new new stream created :*)
            lbl = Lh_call (tid,connect(fd,i2,SOME p2)) /\
            SS = SS0 |++ [(streamid_of_quad (i1',p1',i2,p2), s)]  /\
            write (i1',p1',i2,p2) (oflgs,odata) s s' /\
            SS' = SS0 |++ [(streamid_of_quad (i1',p1',i2,p2), s)]) \/
      (*: non-blocking socket :*)
      (ff.b(O_NONBLOCK) /\
          es = NONE /\
          (err = (if windows_arch h.arch then EAGAIN else EINPROGRESS) \/ SOME err = es') /\
          t' = Timed(Ret(FAIL err),sched_timer) /\ rc = fast fail /\ es''=NONE /\
	  if ~queued then
	      st' = CLOSED /\ is2' = NONE /\ ps2' = NONE /\
              (*: under BSD [[st=TIME_WAIT]], and we destroy a stream :*)
              (*: REMARK this fail quick behaviour breaks abstraction boundaries :*)
              (* REMARK what if is1 and ps1 are not set? *)
              ? i1 p1. (SOME i1,SOME p1) = (is1,ps1) /\
              destroy (i1',p1,i2,p2) SS SS' /\
              lbl = Lh_call (tid,connect(fd,i2,SOME p2))
	  else
	      st' = SYN_SENT /\ is2' = SOME i2 /\ ps2' = SOME p2 /\
                lbl = Lh_call (tid,connect(fd,i2,SOME p2)) /\
                SS = SS0 |++ [(streamid_of_quad (i1',p1',i2,p2), s)]  /\
                write (i1',p1',i2,p2) (oflgs,odata) s s' /\
                SS' = SS0 |++ [(streamid_of_quad (i1',p1',i2,p2), s')])

     )


   (*:

   @description

   From thread [[tid]], a [[connect(fd,i2,SOME p2)]] call is made where [[fd]] refers to a TCP
   socket. The socket is in state [[CLOSED]] with no peer address set, no pending error, and not
   shutdown for reading or writing. A [[SYN]] segment is created to being connection establishment,
   and is enqueued on the host's out-queue.

   If the socket is a blocking one (its [[O_NONBLOCK]] flag is not set) then the call will block: a
   [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition is made, leaving the thread state
   [[Connect2(sid)]]. If the socket is non-blocking (its [[O_NONBLOCK]] flag is set) and the segment
   enqueuing was successful then the call will fail: a [[Lh_call(tid,connect(fd,i2,SOME p2))]]
   transition is made, leaving the thread state [[Ret (FAIL EINPROGRESS)]] (or [[Ret (FAIL
   EAGAIN)]] on WinXP); connection establishment will proceed asynchronously. Otherwise, if the enqueueing did not succeed, the call will fail with an
   error [[err]]: a [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition is made, leaving the thread
   in state [[Ret (FAIL err)]].

   For further details see the in-line comments above.


   @variation FreeBSD

   The socket may also be in state [[TIME_WAIT]] when the [[connect()]] call is made, with either
   both its peer IP and port set, or neither set.

   The socket may be shutdown for reading when the [[connect()]] call is made.

   @variation WinXP

   If there is an early buffer allocation failure when enqueuing the segment, then it will not be
   placed on the host's out-queue and [[es' = ENOBUFS]]; the socket's control block will be [[cb']]
   with its [[snd_nxt]] and [[snd_max]] fields set to the intial sequence number, its
   [[last_ack_seen]] and [[rcv_adv]] fields set to [[0]], its [[tt_delack]] option set to [[NONE]],
   its [[tt_rexmt]] timer stopped, and its [[tf_rxwin0sent]] and [[t_rttseg]] fields reset.

   If there is no route from an interface specified by the local IP address [[i1]] to the foreign IP
   address [[i2]] then the socket's control block will be [[cb']] with its [[snd_next]] field set to the
   initial sequence number, its [[last_ack_sent]] and [[rcv_adv]] fields set to [[0]], and its
   [[tt_delack]] option set to [[NONE]].

   If the segment would case a loopback packet to be sent on the wire then the socket's control
   block will be [[cb']].

   @internal

   If the user calls [[connect()]] on a socket in the closed state, the socket is autobound if no
   local port was specified before, and if no local IP was specified before then an IP is chosen
   that belongs to the interface from which packets for the given destination will be sent.  Then
   the socket moves to the [[SYN_SENT]] state, and we move to the [[Connect2]] state to wait for the
   connection request to succeed or fail.


   POSIX: "If the socket has not already been bound... shall bind it...".

   POSIX: we consider particularly the "If the initiating socket is connection-mode" paragraph.

   So if [[is1]] is NONE, where exactly does it get filled in?  I'm assuming here, for now.

   We go into [[SYN_SENT]] immediately, to avoid a race between the actual connection initiation and
   another thread doing a [[connect()]].

   This is a kind-of blocking rule, except that the timer on the intermediate state is zero,
   requiring it to happen immediately (but not necessarily at the next transition!!).

   --comments from connect\_1a--

   The connection initiation continues by sending a request to the network to create a
   [[tcpInitiator]] object.

   POSIX: we consider particularly the "If the initiating socket is connection-mode" paragraph.

   POSIX: "[[connect()]] shall block for up to an unspecified timeout interval...".

   --comments from connect\_1b--

   TCP is incapable of establishing the connection immediately (ever!), so if the connect() call was
   nonblocking, we send the request to the network to create a [[tcpInitiator]] object, but then
   fail immediately, with the "error" indicating that the connection request is in progress.

   POSIX: "If the connection cannot be established immediately and O\_NONBLOCK is
   set... [[connect()]] shall fail ... [[EINPROGRESS]], but the connection request shall not be
   aborted, and the connection shall be established asynchronously.


   --OLD DESCRIPTION--

   From thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i2,SOME p2)]] call is
   made. [[fd]] refers to a TCP socket identified by [[sid]] with address quad
   [[(is1,ps1,is2,ps2)]]. The socket is uninitialised: it is in state [[CLOSED]] with control block
   [[cb]], empty send and receive queues, no urgent pointers set, no out-of-band data, does not have
   a peer address set, [[is2=NONE /\ ps2=NONE]], has no pending error, and is not shutdown for
   reading or writing.

   The socket either has its local IP address set to [[i1']], or there is an IP address [[i1']] for
   one of the host's interfaces that has a route to the host with IP address [[i2]]. If the socket
   is not bound to a local port [[p1']] then it can be autobound to a local port [[p1']] using
   {@link [[autobind]]}.There are no other TCP sockets in the host's finite map of sockets,
   [[h.socks]], with the binding quad [[(SOME i1',SOME p1',SOME i2, SOME p2)]].

   [[seg]] is a [[SYN]] segment to initiate connection establishment with:

   \begin{itemize}

   \item source address (i1',p1') and destination address (i2,p2);

   \item an initial sequence number for the connection, [[iss]];

   \item the [[SYN]] flag set;

   \item the receive window set to [[rcv_wnd]]. [[rcv_wnd0]] is a window value between [[0]] and
   [[TCP_MAXWIN]]. If the window scale option is to be requested for the connection
   ([[request_r_scale=SOME n]]) then [[rcv_wnd]] is [[rcv_wnd0]] scaled by the window scale value
   specified by [[request_r_scale]] and clipped to a 16-bit value; if window scaling is not to be
   requested ([[request_r_scale=NONE]]) then [[rcv_wnd = rcv_wnd0]]. Additionally, [[rcv_wnd]] is
   not greater than the size of the socket's receive buffer: [[rcv_wnd <= sf.n(SO_RCVBUF)]].

   \item If [[advmss'=SOME v]] then the maximum segment size, [[v]] will be sent with the [[SYN]];

   \item if time-stamping is to be requested for the connection, [[tf_req_tstmp'=T]], then a
   timestamp will be included in the TCP options, specifying the current time and, as this is a
   [[SYN]], an echo reply value of [[0]].

   \item The [[URG]], [[ACK]], [[PSH]], [[RST]], and [[FIN]] flags are not set, and the
   acknowledgement number and urgent pointer are set to arbitrary values.

   \end{itemize}

   If there is not a segment currently being timed for this socket then the [[SYN]] segment will be
   timed with [[t_rttseg']] set to the current time and the initial sequence number for the
   connection.

   The socket's control block will be updated:

   \begin{itemize}

   \item the retransmit and connection establishment timers will be started;

   \item the [[snd_una]] field will be set to the initial sequence number;

   \item the [[snd_max]] and [[snd_nxt]] fields will be set to the initial sequence number plus one;

   \item the [[iss]] field will be set to the initial sequence number;

   \item the [[rcv_wnd]] field will be set to the opening receive window for the connection;

   \item the [[rcv_adv]] field will be set to [[cb.rcv_nxt + rcv_wnd]];

   \item the [[tf_rxwin0sent]] field will be set to [[T]] if a zero length receive window was set or
   [[F]] otherwise;

   \item the [[request_r_scale]] field will record if window scaling was requested and, if so, the
   scale requested;

   \item the [[t_maxseg]] will be set to the maximum segment size for the connection, whether or not
   it is transmitted in the [[SYN]] segment;

   \item the [[t_advmss]] field will be set to [[SOME v]] if the MSS [[v]] was sent with the [[SYN]]
   or [[NONE]] otherwise;

   \item the [[tf_req_tstmp]] field will be set to [[T]] if time-stamping was requested, or [[F]] otherwise;

   \item the [[last_ack_sent]] field will be set to [[0]];

   \item and if the [[SYN]] segment will be timed then the [[t_rttseg]] field will be updated to
   record the time and sequence number of the segment.

   \end{itemize}

   The new control block is [[cb']].

   The [[SYN]] segment [[seg]] shall be placed on the host's outqueue if possible. If there is a
   buffer allocation failure during this then the segment cannot be placed on the host's outqueue:
   [[outsegs' = []]] and [[es' = ENOBUFS]]. If there is no route from an interface specified by the
   local IP address [[i1]] to the peer IP address [[i2]] then the segment cannot be placed on the
   host's outqueue: [[outsegs'=[]]] and [[es']] will be the routing error. If the segment would
   cause the a loopback packet to appear on the wire (something prohibited by RFC 1122), then the
   segment cannot be placed on the host's outqueue; additionally on FreeBSD the [[es'=SOME
   EADDRNOTAVAIL]], on Linux [[es'=SOME EINVAL]], and on WinXP there is no error: the segment is
   silently dropped. All of the above failures result in the socket's control block being reset to
   [[cb]], the control block when the [[connect()]] call was made.

   Otherwise the segment can be placed on the host's outqueue, [[outsegs'=[(seg,queued)]]], using
   {@link [[enqueue_oq_list_qinfo]]} to create new outqueue [[oq']]. If this now fails due to a
   buffer allocation failure, [[queued = F]], then [[es'=ENOBUFS]], [[oq'=h.oq]], and the socket's
   control block is updated to set the [[snd_nxt]] field to the initial sequence number, the
   [[rcv_adv]] and [[last_ack_sent]] fields to [[0]], the [[tt_delack]] option to [[NONE]], and to
   stop the retransmit timer. If the segment is successfully enqueued on the host's outqueue then
   [[es'=NONE]] to create new outqueue [[oq']].

   If the call is made with non-blocking semantics, the [[O_NONBLOCK]] flag of the file description
   for the socket is set, and the socket does not have a pending error then the call will fail with
   either the error [[es']] resulting from a failed attempt to enqueue the [[SYN]] segment [[seg]];
   or an [[EINPROGRESS]] error on FreeBSD and Linux; or an [[EAGAIN]] error on WinXP. The
   [[EINPROGRESS]] and [[EAGAIN]] errors mean that connection establishment is proceeding
   asynchronously and [[connect()]] should be called again to see the result. A
   [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition will be made, leaving the thread state
   [[Ret (FAIL err)]]. If the call failed without enqueueing a [[SYN]] segment then the socket will
   be in state [[CLOSED]] with address quad [[(SOME i1',SOME p1',NONE,NONE)]]; otherwise it will be
   in state [[SYN_SENT]] with address quad [[(SOME i1',SOME p1',SOME i2,SOME p2)]]. In either case
   the pending error will be cleared.

   If the call is made with blocking semantics then it shall block, entering state
   [[Connect2(sid)]]. A [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition will be made leaving the
   thread state [[Connect2(sid)]]. The socket will be in state [[SYN_SENT]] with address quad
   [[(SOME i1',SOME p1',SOME i2,SOME p2)]] and pending error set to [[es']].

   In either case the host's out-queue will be [[oq']] and its list of bound sockets will be
   [[bound]], which shall have [[sid]] appended to its head if the socket was autobound to an
   ephemeral port.

   :*)
   )

/\

   (!h ts tid d sid tcp_sock
    SS MM.

   connect_2 /* rp_tcp, slow urgent succeed (*: Successfully return from blocking state after connection is successfully established :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Connect2 sid,d)) |>,SS,MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer)) |>,SS,MM)

   <==

     TCP_PROTO(tcp_sock) = (h.socks ' sid).pr /\
     tcp_sock.st IN {ESTABLISHED;CLOSE_WAIT} /\
     (~?tid' d'. (tid' IN FDOM ts) /\ (tid' <> tid) /\
                 ts ' tid' = Timed(Connect2 sid,d'))



   (*:

   @description

   Thread [[tid]] is blocked in state [[Connect2(sid)]] where [[sid]] identifies a TCP socket which
   is in state [[ESTABLISHED]]: the connection establishment has been successfully completed; or
   [[CLOSE_WAIT]]: connection establishment successfully completed but a [[FIN]] was received during
   establishment. [[tid]] is the only thread which is blocked waiting for the socket [[sid]] to
   establish a connection. As connection establishment has now completed, the thread can
   successfully return from the blocked state.

   A [[Lh_tau]] transition is made, leaving the thread state [[Ret (OK ())]].

   @internal

   When a connection is successfully established, the blocked [[connect()]] returns successfully.

   POSIX: we consider particularly the "If the initiating socket is connection-mode" paragraph.

   I think we want to allow [[CLOSE_WAIT]] as well as [[ESTABLISHED]], in case we receive a [[FIN]]
   during the handshake.

   The side condition states that this is the unique thread blocked on this [[connect()]]; if not,
   then something *weird* has gone wrong.  I could have put the condition into the invariant
   instead, but we're less likely to miss it here (the usual "in any state exactly one rule applies"
   is not strong enough to catch this nondeterminism otherwise).

   :*)
   )

/\

   (!h ts socks sock tid d sid e tcp_sock
    SS MM.

   connect_3 /* rp_tcp, slow urgent fail (*: Fail with the pending error on a socket in the [[CLOSED]] state :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Connect2 sid,d));
               socks := socks |++
                        [(sid,sock with <| es := SOME e |>)] |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer));
               socks := socks |++
                        [(sid,sock with <| es := NONE |>)] |>,
     SS,MM)

   <==

     TCP_PROTO(tcp_sock) = sock.pr /\
     tcp_sock.st = CLOSED


   (*:

   @description

   Thread [[tid]] is blocked in the [[Connect2(sid)]] state where [[sid]] identifies a TCP socket
   [[sock]] that is in the [[CLOSED]] state: connection establishment has failed, leaving the socket
   in a pending error state [[SOME e]]. Usually this occurs when there is no listening TCP socket at
   the peer address, giving an error of [[ECONNREFUSED]] or [[ECONNRESET]]; or when the connection
   establishment timer expired, giving an error of [[ETIMEDOUT]]. The call now returns, failing with
   the error [[e]], and clearing the pending error field of the socket.

   A [[Lh_tau]] transition is made, leaving the thread state [[Ret (FAIL e)]].

   @variation FreeBSD

   When connection establishment failed, the [[bsd_cantconnect]] flag in the control block would
   have been set, the socket's [[cantsndmore]] and [[cantrcvmore]] flags would have been set and its
   local address binding would have been removed. This renders the sockets useless: call to
   [[bind()]], [[connect()]], and [[listen()]] will all fail.

   @internal

   This rule was previously used to return [[ECONNREFUSED]] or [[ECONNRESET]] only, however this did
   not take into account failure through connection establishment timeout ([[timer_tt_conn_est_1]] closes
   the socket asynchronously). We now rely on the asynchronous socket closure to set the socket's error
   field correctly, so that this rule may now apply generally to any error that caused the socket to
   become [[CLOSED]] during a [[connect()]] call.

   ===
   OLD DESCRIPTION:

   Thread [[tid]] is blocked in the [[Connect2(sid)]] state where [[sid]] identifies a TCP socket
   [[sock]] that is in the [[CLOSED]] state: connection establishment has failed, receiving a
   [[RST]] segment from its peer during connection establishment: usually this occurs when there is
   not a listening TCP socket at the peer address. The call now returns, failing with error [[e]]
   where [[e]] which is either [[ECONNREFUSED]] or [[ECONNRESET]].

   A [[Lh_tau]] transition is made, leaving the thread state [[Ret (FAIL e)]].
   ===

   When a connection establishment attempt fails (signalled by the state returning to [[CLOSED]]),
   the blocked [[connect()]] returns failure.

   POSIX: we consider particularly the "If the initiating socket is connection-mode" paragraph.

   POSIX implies we must do the autobind anyway.

   OLD COMMENT: Not clear whether we should really return to closed, thus allowing another
   [[connect()]]; I assume it does.  Anyway, does it leave [[SOME i1]] there?  CHECK!

   OLD COMMENT: **POSIX: says, in the *INFORMATIVE* section *APPLICATION USAGE*, that the state of
   the socket is unspecified if connect() fails.  Perhaps we should model this accurately.

   Is it vaguely possible that [[es]] at some point becomes [[SOME ECONNREFUSED]]?

   Not sure if [[ECONNRESET]] belongs here or not; original intention was [[ECONNREFUSED]], but it
   looks to me like [[ECONNRESET]] should also be allowed.  Is this the case?  How are the two
   distinguished?

   :*)
   )

/\

   (!h ts socks sock sock' tid d sid fid sf i1 ps1 i2 p2 err cb cb'
   SS SS' MM.

   connect_4 /* rp_tcp, slow urgent fail (*: Fail: socket has pending error :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Connect2 sid,d));
               socks := socks |++
                        [(sid,sock)] |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer));
               socks := socks |++
                        [(sid,sock')] |>,
     SS',MM)


   <==

     sock = Sock(SOME fid,sf,SOME i1,ps1,SOME i2,SOME p2,SOME err,F,F,
                TCP_Sock(SYN_SENT,cb,NONE)) /\

    (*: On WinXP if the error is from routing to an unavailable address,
       the error is not returned and the socket is left alone. The
       rexmtsyn timer will retry the SYN transmission and eventually fail. :*)
    ~(windows_arch h.arch /\ err = EINVAL) /\
    if bsd_arch h.arch then
        if (err = EADDRNOTAVAIL) then
            (* On BSD if the error is from routing to an unavailable address,
                the error is returned. The socket is left alone so that
                the rexmtsyn timer can retry the SYN transmission (needlessly). *)
            sock' = Sock(SOME fid,sf,SOME i1,ps1,SOME i2,SOME p2,NONE,F,F,
                TCP_Sock(SYN_SENT,cb,NONE)) /\
            SS' = SS
        else
            sock' = Sock(SOME fid,sf,SOME i1,ps1,NONE,NONE,NONE,F,F,
                TCP_Sock(CLOSED,initial_cb,NONE)) /\
            case ps1 of SOME p1 -> destroy (i1,p1,i2,p2) SS SS'
                || NONE -> SS' = SS
    else
        (*: close the socket, but do not shutdown for reading/writing :*)
        sock' = Sock(SOME fid,sf,SOME i1,ps1,NONE,NONE,NONE,F,F,
            TCP_Sock(CLOSED,cb',NONE)) /\
        cb' = initial_cb /\
        case ps1 of SOME p1 -> destroy (i1,p1,i2,p2) SS SS'
            || NONE -> SS' = SS



   (*:

   @description

   Thread [[tid]] is blocked in the [[Connect2(sid)]] state waiting for a connection to be
   established. [[sid]] identifies a TCP socket [[sock]] that has not been shutdown for reading or
   writing, and has binding quad [[(SOME i1,ps1,SOME i2,SOME p2)]] and pending error [[err]]. The
   socket is in state [[SYN_SENT]], is not listening, has empty send and receive queues, and no
   urgent marks set. The call fails, returning the pending error.

   A [[Lh_tau]] transition is made, leaving the thread state [[Ret (FAIL err)]]. The socket is
   left in state [[CLOSED]] with its peer address not set, its pending error cleared, and its control
   block reset to the initial control block, [[initial_cb]].

   @variation FreeBSD

   If the pending error is [[EADDRNOTAVAIL]] then the error is cleared and returned but the rest of
   the socket stays the same: it is in state [[SYN_SENT]] so the [[SYN]] will be retransmitted until
   it times out.

   If the pending error is not [[EADDRNOTAVAIL]] then the socket is reset as above except that the
   the socket's local ip and port are cleared

   @variation WinXP

   If the error is [[EINVAL]] then this rule does not apply.

   @internal

   If the socket has a pending error then return it, closing the connection. This occurs on an
   output failure (e.g. attempting to connect to a remote host if we're bound to a local IP address)

   TODO: it is unclear how much cleaning up of the socket's state occurs after a connect
   failure. The BSD code suggests that the control block is left in an untidy state. To be
   investigated.

   :*)
   )

/\

  (!h ts tid d socks sid sock err fd i2 p2 fid ff tcp_sock
    SS MM.

   connect_4a /* rp_tcp, fast fail (*: Fail with pending error :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
	                [(sid,sock with <| es := SOME err |>)] |>,
     SS,MM)
   -- Lh_call (tid,connect(fd,i2,SOME p2)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer)) ;
               socks := socks |++
	                [(sid,sock with <| es := NONE |>)] |>,
     SS,MM)

   <==


     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     TCP_PROTO(tcp_sock) = sock.pr /\
     tcp_sock.st IN {CLOSED (* any others? *) }


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i2,SOME p2)]] call is
    made. [[fd]] refers to a TCP socket [[sock]], identified by [[sid]], with pending error [[err]]
    and in state [[CLOSED]]. The call fails with the pending error.

    A [[Lh_call(tid,connect(fd,ip,port))]] transition is made, leaving the thread state [[Ret
    (FAIL err)]] and the socket's pending error clear.

    The most likely cause of this behaviour is for a non-blocking [[connect(fd,_,_)]] call to have
    previously been made. The call fails, setting the pending error on the socket, and when
    [[connect()]] is called to check the status of connection establishment the error is
    returned. In such a case [[err]] is most likely to be [[ECONNREFUSED]], [[ECONNRESET]], or
    [[ETIMEDOUT]].


    @internal

    Non-blocking [[connect()]] was called, but got a RST or a timeout to set the pending
    error? Call fails with pending error. Need to investigate more: not sure what other pending errors are possible



   :*)

 )

/\

   (!h ts tid d
     fd fid ff sid
     i2 p2 err tcp_sock
     SS MM.

   connect_5 /* rp_tcp, fast fail (*: Fail with [[EALREADY]], [[EINVAL]], [[EISCONN]], [[EOPNOTSUPP]]: socket already in use :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,connect(fd,i2,SOME p2)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     TCP_PROTO(tcp_sock) = (h.socks ' sid).pr /\
     case tcp_sock.st of
         SYN_SENT     -> if     ff.b(O_NONBLOCK) = T then err = EALREADY (*: connection already in progress :*)
                         else if windows_arch h.arch then err = EALREADY (*: connection already in progress :*)
                         else if bsd_arch     h.arch then err = EISCONN  (*: connection being established :*)
                         else ASSERTION_FAILURE "connect_5:1" || (*: never happen :*)
         SYN_RECEIVED -> if     ff.b(O_NONBLOCK) = T then err = EALREADY (*: connection already in progress :*)
                         else if windows_arch h.arch then err = EALREADY
                         else if bsd_arch     h.arch then err = EISCONN  (*: connection being established :*)
                         else ASSERTION_FAILURE "connect_5:2" || (*: never happen :*)
         LISTEN      -> if      windows_arch h.arch then err = EINVAL  (*: socket is listening :*)
                        else if bsd_arch     h.arch then err = EOPNOTSUPP
                        else if linux_arch   h.arch then err = EISCONN
                        else ASSERTION_FAILURE "connect_5:3" || (*: never happen :*)
         ESTABLISHED -> err = EISCONN ||  (*: socket already connected :*)
         FIN_WAIT_1 -> err = EISCONN ||   (*: socket already connected :*)
         FIN_WAIT_2 -> err = EISCONN ||   (*: socket already connected :*)
         CLOSING -> err = EISCONN ||      (*: socket already connected :*)
         CLOSE_WAIT -> err = EISCONN ||   (*: socket already connected :*)
         LAST_ACK -> err = EISCONN ||     (*: socket already connected; seems that fd is valid in this state :*)
         TIME_WAIT -> (windows_arch h.arch \/ linux_arch h.arch) /\ err = EISCONN ||
                     (*: BSD allows a [[TIME_WAIT]] socket to be reconnected :*)
         CLOSED -> err = EINVAL /\ bsd_arch h.arch


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i2,SOME p2)]] call is made
   where [[fd]] refers to a TCP socket identified by [[sid]]. The call fails with an error [[err]]:
   if the socket is in state [[SYN_SENT]] or [[SYN_RECEIVED]] and the socket is non-blocking or the
   host is a WinXP architecture then [[err=EALREADY]] ([[EISCONN]] on FreeBSD); if it is in state [[LISTEN]] then on WinXP
   [[err=EINVAL]], on FreeBSD [[err=EOPNOTSUPP]], and on Linux [[err=EISCONN]]; if it is in state
   [[ESTABLISHED]], [[FIN_WAIT_1]], [[FIN_WAIT_2]], [[CLOSING]], [[CLOSE_WAIT]], or [[TIME_WAIT]] on
   Linux and WinXP, [[err=EISCONN]]; if it is in state [[CLOSED]] on FreeBSD and has its
   [[bsd_cantconnect]] flag set then [[err=EINVAL]].

   A [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition is made, leaving the thread state [[Ret
   (FAIL err)]].

   @variation FreeBSD

   If the socket is in state [[TIME_WAIT]] then the call does not fail: the socket may be
   reconnected by {@link [[connect_1]]}.

   @internal

   If the user calls [[connect()]] on a socket that is already (asynchronously) connecting, we
   return an appropriate error.

   POSIX: "...shall fail and set errno to [[EALREADY]]".

   If [[tcp_sock.st IN {ESTABLISHED, FIN_WAIT_1, FIN_WAIT_2, CLOSING, CLOSE_WAIT}]] then error is
   [[EISCONN]] as the socket is already connected.

   TODO: Not sure what happens if [[tcp_sock.st = LAST_ACK]]....

   If [[tcp_sock.st IN {CLOSED; TIME_WAIT}]] then we are allowed to call connect(), so this rule
   does not apply.

   If [[tcp_sock.st = LISTEN]], error is architecture dependent.

   If [[tcp_sock.st IN {SYN_SENT; SYN_RECEIVED}]] return error [[EALREADY]] if socket is in
   non-blocking mode or the platform is WinXP. If we are already connecting, new connect requests
   are treated as errors.  NOTE: It is possible that the socket's file flags could be changed to
   blocking mode before this call to connect. BSD and WinXP always get it right and fail if there is a
   pending request. Linux is broken: see rule [[connect_5d]].

   --

   If the user calls [[connect()]] on a socket that is already connected, we return an appropriate
   error.

   --

   If the user calls [[connect()]] on a socket that is currently listening for connections, we
   return an appropriate error.

   :*)
   )

/\

   (!h ts tid d ps1 p1'
     fd fid ff sid ps1'
     i2 p2 err sock socks bound is1' i1'
     SS MM.

   connect_5a /* rp_all, fast fail (*: Fail: no route to host :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
	       socks := socks |++
			[(sid,sock with <| is1 := NONE; ps1 := ps1 |>)] |>,
     SS,MM)
   -- Lh_call (tid,connect(fd,i2,SOME p2)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer));
               socks := socks |++
			[(sid,sock with <| is1 := is1'; ps1 := ps1' |>)];
	       bound := bound |>,
     SS,MM)

   <==

     (*: REMARK although this rule may result in a quad becoming bound, we assume [[(i2,p2)]] not bound :*)
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     h.files ' fid = File(FT_Socket(sid),ff) /\
     (if bsd_arch h.arch /\ proto_of sock.pr = PROTO_TCP then
	  is1' = SOME i1' /\ i1' IN local_primary_ips h.ifds /\
          ps1' = SOME p1' /\ p1' IN autobind(ps1,PROTO_TCP,h,h.socks) /\
	  (if ps1 = NONE then bound = sid::h.bound else bound = h.bound)
     else is1' = NONE /\ ps1' = ps1 /\ bound = h.bound) /\
     case test_outroute_ip(i2,h.rttab,h.ifds,h.arch) of
	 SOME e   -> err = e
     ||  _other29 -> F  (* other cases not considered in this rule *) /\
     (proto_of sock.pr = PROTO_UDP ==> ~bsd_arch h.arch)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i2,SOME p2)]] call is
   made. [[fd]] refers to a socket identified by [[sid]] which does not have a local IP address
   set. The { [[test_outroute_ip]]} function is used to check if there is a route from the host
   to [[i2]]. There is no route so the call will fail with a routing error [[err]]. If there is no
   interface with a route to the host then on Linux the call fails with [[ENETUNREACH]] and on
   FreeBSD and WinXP it fails with [[EHOSTUNREACH]]. If there are interfaces with a route to the
   host but none of these are up then the call fails with [[ENETDOWN]].

   A [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition is made, leaving the thread state [[Ret
   (FAIL err)]], where [[err]] is one of the above errors.

   @variation FreeBSD

   This rule does not apply to UDP sockets on FreeBSD. Additionally, if the socket is not bound to a
   local port then it will be autobound to one and [[sid]] will be appended to the head of the
   host's list of bound sockets, [[bound]]. The socket's local IP address may be set to [[SOME i1]]
   even though there is no route from [[i1]] to [[i2]].

   @internal

   If we cannot route to the destination address, and there's not already a source address specified
   in the socket, we give the appropriate error.

   :*)
   )

/\

   (!h ts tid d
     fd fid ff sid sock socks is1' is2' ps2'
     i2 p2 i1' p1' bound bound'
     SS MM.
   connect_5b /* rp_all, fast fail (*: Fail with [[EADDRINUSE]]: address already in use :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock)];
               bound := bound |>,
     SS,MM)
   -- Lh_call (tid,connect(fd,i2,SOME p2)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EADDRINUSE),sched_timer));
               socks := socks |++
                        [(sid,sock with <| is1 := is1'; ps1 := SOME p1'; is2 := is2'; ps2 := ps2' |> )];
               bound := bound' |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     i1' IN auto_outroute(i2,sock.is1,h.rttab,h.ifds) /\
     p1' IN autobind(sock.ps1,(proto_of sock.pr),h,h.socks) /\
     (if sock.ps1 = NONE then bound' = sid::bound else bound' = bound) /\
     (proto_of sock.pr = PROTO_UDP ==> ~(linux_arch h.arch \/ windows_arch h.arch)) /\
     (?(sid',s) :: socks \\ sid.
        s.is1 = SOME i1' /\ s.ps1 = SOME p1' /\
        s.is2 = SOME i2  /\ s.ps2 = SOME p2  /\
        proto_eq sock.pr s.pr) /\
     (if proto_of sock.pr = PROTO_UDP then
	  if sock.is2 = NONE then is1' = sock.is1 /\ is2' = NONE /\ ps2' = NONE
          else                    is1' = NONE  /\ is2' = NONE /\ ps2' = NONE
      else is1' = sock.is1 /\ is2' = sock.is2 /\ ps2' = sock.ps2) (* TCP case still to be tested *)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i2,SOME p2)]] call is made
   where [[fd]] refers to a socket [[sock]] identified by [[sid]]. The socket is either bound to
   local port [[SOME p1']], or can be autobound to port [[SOME p1']]. The socket either has its
   local IP address set to [[SOME i1']] or else its local IP address is unset but there exists an IP
   address [[i1']] for one of the host's interfaces which has a route to [[i2]]. There exists
   another socket [[s]] in the host's finite map of sockets, identified by [[sid']], that has as its
   binding quad [[(SOME i1',SOME p1',SOME i2,SOME p2)]].

   A [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition is made, leaving the thread state [[Ret
   (FAIL EADDRINUSE)]]: there is already another socket with the same local address connected to the
   peer address [[(SOME i2,SOME p2)]]. The socket's local port is set to [[SOME p1']]; if this was
   accomplished by autobinding then [[sid]] is appended to the head of [[bound]], the host's list of
   bound sockets, to create a new list [[bound']]. If [[sock]] is a TCP socket then its [[is1]],
   [[is2]], and [[ps2]] fields are unchanged. If [[sock]] is a UDP socket on FreeBSD then if its
   peer IP address was set, its local IP address will be unset: [[is1'=NONE]], otherwise its local
   IP address will stay as it was: [[is1'=sock.is1]]; its peer IP address and port will both be
   unset: [[is2'=NONE /\ ps2'=NONE]].

   @variation Linux

   This rule does not apply to UDP sockets: Linux allows two UDP sockets to have the same binding quad.

   @variation WinXP

   This rule does not apply to UDP sockets: WinXP allows two UDP sockets to have the same binding quad.

   @internal

   If the user calls [[connect()]] on a socket so as to result in two sockets with the same
   quadruple of IP/port/IP/port, return [[EADDRINUSE]]. BSD unconnects the UDP socket in this case,
   such that the local IP and remote IP/port are cleared.

   From BSD.  Not in POSIX.

   :*)
   )

/\

   (!h ts tid d
     fd fid ff sid
     i2 p2
     SS MM.

   connect_5c /* rp_all, fast fail (*: Fail with [[EADDRNOTAVAIL]]: no ephemeral ports left :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,connect(fd,i2,SOME p2)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EADDRNOTAVAIL),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     (h.socks ' sid).ps1 = NONE /\
     autobind(NONE,(proto_of (h.socks ' sid).pr),h,h.socks) = EMPTY


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i2,SOME p2)]] is made. [[fd]]
   refers to a socket identified by [[sid]] which is not bound to a local port. There are no
   ephemeral ports available to autobind to so the call fails with an [[EADDRNOTAVAIL]] error.

   A [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition is made, leaving the thread state [[Ret
   (FAIL EADDRNOTAVAIL)]].

   @internal

   If there are no more ephemeral ports available, return [[EADDRNOTAVAIL]].

   From BSD.  Not in POSIX.

   :*)
   )


/\

   (!h ts tid d
     fd fid ff sid
     i2 p2 tcp_sock
     SS MM.

   connect_5d /* rp_tcp, block (*: Block, entering state [[Connect2]]: connection attempt already in progress and connect called with blocking semantics :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,connect(fd,i2,SOME p2)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Connect2(sid),never_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     TCP_PROTO(tcp_sock) = (h.socks ' sid).pr /\
     ff.b(O_NONBLOCK) = F /\
     linux_arch h.arch /\
     tcp_sock.st IN {SYN_SENT; SYN_RECEIVED}


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i2,SOME p2)]] call is
   made. [[fd]] refers to a TCP socket identified by [[sid]] which is in state [[SYN_SENT]] or
   [[SYN_RECEIVED]]: in other words, a connection attempt is already in progress for the socket
   (this could be an asynchronous connection attempt or one in another thread). The open file
   description referred to by [[fd]] does not have its [[O_NONBLOCK]] flag set so the call blocks,
   awaiting completion of the original connection attempt.

   A [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition is made, leaving the thread state
   [[Connect2(sid)]].

   @variation FreeBSD

   This rule does not apply.

   @variation WinXP

   This rule does not apply.

   @internal

   If we are already connecting asychronously (or in another thread) and another call to connect is made with the socket
   now in blocking mode, block until the completion of the previous connection attempt. NOTE: if the
   new connect() specifies a different remote address ([[i2]],[[p2]]), the new address is simply
   ignored and the original connection attempt procedes.

   This only applies to Linux. BSD and WinXP get it right and fail with EALREADY, cf [[connect_5]].

   :*)
   )

/\

   (!h ts tid d socks sid sock tcp fd i2 p2 fid ff
    SS MM.

   connect_6 /* rp_tcp, fast fail (*: Fail with [[EINVAL]]: socket has been shutdown for writing :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| cantsndmore := T; pr := TCP_PROTO(tcp with <| st := CLOSED |>) |>)] |>,
     SS,MM)
   -- Lh_call (tid,connect(fd,i2,SOME p2)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINVAL),sched_timer));
               socks := socks |++
                        [(sid,sock with <| cantsndmore := T; pr := TCP_PROTO(tcp with <| st := CLOSED |>) |> )] |>,
     SS,MM)

   <==

     bsd_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     h.files ' fid = File(FT_Socket(sid),ff)


   (*:

     @description

     On FreeBSD, from thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i2,SOME p2)]]
     call is made. [[fd]] refers to a TCP socket [[sock]] identified by [[sid]] which is in state
     [[CLOSED]] and has been shutdown for writing.

     A [[Lh_call(tid,connect(fd,i2,SOME p2))]] transition is made, leaving the thread state [[Ret
     (FAIL EINVAL)]].

     @variation Posix

     This rule does not apply.

     @variation Linux

     This rule does not apply.

     @variation WinXP

     This rule does not apply.

   :*)

   )

/\

   (!h h0 ts tid d sid fid sf es ff socks bound
     udp ps1 fd i2 ps2 i1' p1' cantsndmore cantrcvmore cantsndmore'
     SS MM.

   connect_7 /* rp_udp, fast succeed (*: Set peer address on socket with binding quad [[NONE,ps1,NONE,NONE]] :*) */
     (h0,SS,MM)
   -- Lh_call (tid,connect(fd,i2,ps2)) -->
     (h0 with <| ts := FUPDATE ts (tid, Timed(Ret (OK ()),sched_timer));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1',SOME p1',SOME i2,ps2,es,cantsndmore',cantrcvmore,UDP_PROTO(udp)))];
               bound := bound
            |>,
      SS,MM)

   <==

     h0 = h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                    socks := socks |++
                               [(sid,Sock(SOME fid,sf,NONE,ps1,NONE,NONE,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))]
          |> /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     h0.files ' fid = File(FT_Socket(sid),ff) /\
     p1' IN autobind(ps1,PROTO_UDP,h0,h0.socks) /\
     (if ps1 = NONE then bound = sid::h0.bound else bound = h0.bound) /\
     i1' IN auto_outroute(i2,NONE,h0.rttab,h0.ifds) /\
     ~(? (sid', s) :: (h0.socks \\ sid).
              s.is1 = SOME i1' /\ s.ps1 = SOME p1' /\
              s.is2 = SOME i2  /\ s.ps2 = ps2 /\
              proto_of s.pr = PROTO_UDP /\
              bsd_arch h.arch) /\
     (bsd_arch h.arch ==> ps2 <> NONE /\ es = NONE) /\
     (if windows_arch h.arch then cantsndmore' = F
      else                        cantsndmore' = cantsndmore)


     (*:

      @description

      Consider a UDP socket [[sid]], referenced by [[fd]], with no local IP or peer address
      set. From thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i2,ps2)]] call is
      made. The socket's local port is either set to [[p1']], or it is unset and can be autobound to
      a local ephemeral port [[p1']]. The local IP address can be set to [[i1']] which is the
      primary IP address for an interface with a route to [[i2]].

      A [[Lh_call(tid,connect(fd,i2,ps2))]] transition is made, leaving the thread state [[Ret
      (OK())]]. The socket's local address is set to [[(SOME i1',SOME p1')]], and its peer address
      is set to [[(SOME i2,ps2)]]. If the socket's local port was autobound then [[sid]] is placed
      at the head of the host's list of bound sockets: [[bound = sid::h0.bound]].

      @variation FreeBSD

      As above, with the additional conditions that a foreign port is specified in the [[connect()]]
      call: [[ps2 <> NONE]], and there are no pending errors on the socket. Furthermore, there may
      be no other sockets in the host's finite map of sockets with the binding quad [[(SOME i1',SOME
      p1',SOME i2,ps2)]].

      @variation WinXP

      As above, except that the socket will not be shutdown for writing after the [[connect()]] call
      has been made.

      :*)

   )

/\

   (!h ts tid d sid fid sf es ff socks h0
     udp i1 p1 is2 ps2 fd i ps cantsndmore cantrcvmore cantsndmore'
     SS MM.

   connect_8 /* rp_udp, fast succeed (*: Set peer address on socket with local address set :*) */
     (h0,SS,MM)
   -- Lh_call (tid,connect(fd,i,ps)) -->
     (h with <| ts := FUPDATE ts (tid, Timed(Ret (OK ()),sched_timer));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i,ps,es,cantsndmore',cantrcvmore,UDP_PROTO(udp)))] |>,
     SS,MM)

   <==

     h0 =  h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                     socks := socks |++
                              [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,is2,ps2,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))] |> /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     (bsd_arch h.arch ==> ps <> NONE /\ es = NONE) /\
     (if windows_arch h.arch then cantsndmore' = F
      else                        cantsndmore' = cantsndmore) /\
     ~(? (sid',s) :: (h0.socks \\ sid).
              s.is1 = SOME i1 /\ s.ps1 = SOME p1 /\
              s.is2 = SOME i  /\ s.ps2 = ps /\
              proto_of s.pr = PROTO_UDP /\
	      bsd_arch h.arch)


    (*:

     @description

     Consider a UDP socket [[sid]], referenced by [[fd]], with local address set to [[(SOME i1,SOME
     p1)]]. Its peer address may or may not be set. From thread [[tid]], which is in the [[Run]]
     state, a [[connect(fd,i,ps)]] call is made.

     The call succeeds: a [[Lh_call(tid,connect(fd,i,ps))]] transition is made, leaving the thread
     in state [[Ret (OK())]]. The socket has its peer address set to [[(SOME i,ps)]].

     @variation FreeBSD

     As above, with the additional conditions that a foreign port is specified in the [[connect()]]
     call, [[ps <> NONE]], and there are no pending errors on the socket. Furthermore, there may be
     no other sockets in the host's finite map of sockets with the binding quad [[(SOME i1',SOME
     p1',SOME i,ps)]].

     @variation WinXP

     As above, with the additional effect that if the socket was shutdown for writing when the
     [[connect()]] call was made, it will no longer be shutdown for writing.

     @internal

     Note: Winsock Reference says "The default destination can be changed by simply calling connect
     again, even if the socket is already connected. Any datagrams queued for receipt are discarded
     if name is different from the previous connect." This is NOT true.

     :*)


   )

/\

   (!h ts tid d socks sid
     sock udp fd i fid ff is1
     SS MM.

   connect_9 /* rp_udp, fast fail (*: Fail with [[EADDRNOTAVAIL]]: port must be specified in [[connect()]] call on FreeBSD :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| pr := UDP_PROTO(udp) |>)] |>,
     SS,MM)
   -- Lh_call (tid,connect(fd,i,NONE)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EADDRNOTAVAIL),sched_timer));
               socks := socks |++
                        [(sid,sock with <| is1 := is1; is2 := NONE; ps2 := NONE; pr := UDP_PROTO(udp) |> )] |>,
     SS,MM)

   <==

     bsd_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     (if sock.is2 <> NONE then is1 = NONE else is1 = sock.is1)



   (*:

    @description

    On FreeBSD, consider a UDP socket [[sid]] referenced by [[fd]]. From thread [[tid]], which is in
    the [[Run]] state, a [[connect(fd,i,NONE)]] call is made. Because no port is specified, the call
    fails with an [[EADDRNOTAVAIL]] error.

    A [[Lh_call(tid,connect(fd,i,NONE))]] transition is made, leaving the thread state [[Ret
    (FAIL EADDRNOTAVAIL)]]. The socket's peer address is cleared: [[is2 := NONE]] and [[ps2 :=
    NONE]]. Additionally, if the socket had its peer IP address set, [[sock.is2 <> NONE]], then its
    local IP address will be cleared: [[is1 = NONE]]; otherwise it remains the same: [[is1 =
    sock.is1]].

    @variation Posix

    This rule does not apply.

    @variation Linux

    This rule does not apply.

    @variation WinXP

    This rule does not apply.

    @internal

    On BSD, calling [[connect]] without specifying the port results in an [[EADDRNOTAVAIL]] error. On
    Linux and XP, the call does not fail: see rule [[connect_7]].

   :*)

   )

/\

  (!h ts tid d socks sid sock err udp fd i ps fid ff h0
    SS MM.

  connect_10 /* rp_udp, fast fail (*: Fail with pending error on FreeBSD, but still set peer address :*) */
    (h0,SS,MM)
  -- Lh_call (tid,connect(fd,i,ps)) -->
    (h0 with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer));
              socks := socks |++
                       [(sid,sock with <| is2 := SOME i; ps2 := ps; es := NONE; pr := UDP_PROTO(udp) |>)] |>,
    SS,MM)

  <==

    bsd_arch h.arch /\
    h0 =  h with <| ts := FUPDATE ts (tid,Timed(Run,d));
                    socks := socks |++
                             [(sid,sock with <| es := SOME err; pr := UDP_PROTO(udp) |>)] |> /\
    fd IN FDOM h.fds /\
    fid = h.fds ' fd /\
    FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
    ps <> NONE /\
    ~(?(sid',s) :: (h0.socks \\ sid).
              s.is1 = sock.is1 /\ s.ps1 = sock.ps1 /\
              s.is2 = SOME i  /\ s.ps2 = ps /\
              proto_of s.pr = PROTO_UDP)


    (*:

     @description

     On FreeBSD, consider a UDP socket [[sid]], referenced by [[fd]], with pending error
     [[err]]. From thread [[tid]], which is in the [[Run]] state, a [[connect(fd,i,ps)]] call is
     made with [[ps <> NONE]]. There is no other UDP socket on the host which has the same local
     address [[sock.is1,sock.ps1]] as [[sid]], and its peer address set to [[SOME i, ps]]. The call
     fails, returning the pending error [[err]].

     A [[Lh_call(tid,connect(fd,i,ps))]] transition is made, leaving the thread state [[Ret (FAIL
     err)]]. The socket's peer address is set to [[(SOME i,ps)]], and the error is cleared from the
     socket.

     @variation Linux

     This rule does not apply.

     @variation WinXP

     This rule does not apply.

     :*)
  )

/\

(*:

@section [[disconnect]] ALL [[disconnect()]]
  \[ <[disconnect: fd -> unit]> \]

   A call to [[disconnect(fd)]], where [[fd]] is a file descriptor referring to a socket, removes
   the peer address for a UDP socket. If a UDP socket has peer address set to [[(SOME i2, SOME p2)]]
   then it can only receive datagrams with source address [[(i2,p2)]]. Calling [[disconnect()]] on
   the socket resets its peer address to [[(NONE,NONE)]], and so it will be able to receive
   datagrams with any source address.

   It does not make sense to disconnect a TCP socket in this way.  Most supported architectures
   simply disallow [[disconnect]] on such a socket; however, Linux implements it as an abortive
   close (see {@link [[close_3]]}).

 @errors

   A call to [[disconnect()]] can fail with the errors below, in which case the corresponding
   exception is raised:

   @error [[EADDRNOTAVAIL]] There are no ephemeral ports left for autobinding to.

   @error [[EAFNOSUPPORT]] The address family |AF_UNSPEC| is not supported. This can be the
   result for a successful [[disconnect()]] for a UDP socket.

   @error [[EAGAIN]] There are no ephemeral ports left for autobinding to.

   @error [[EALREADY]] A connection is already in progress.

   @error [[EBADF]] The file descriptor [[fd]] is an invalid file descriptor.

   @error [[EISCONN]] The socket is already connected.

   @error [[ENOBUFS]] No buffer space is available.

   @error [[EOPNOTSUPP]] The socket is listening and cannot be connected.

   @errorinclude [[misc]] [[EBADF]]
   @errorinclude [[misc]] [[ENOTSOCK]]

 @commoncases

   [[disconnect_1]]; [[return_1]]

 @api

  [[disconnect()]] is a Posix [[connect()]] call with the address family set to
  |AF_UNSPEC|.

  \begin{tabular}{ll}
    Posix:   & |int connect(int socket, const struct sockaddr *address,|\\
             & |            socklen_t address_len);| \\
    FreeBSD: & |int connect(int s, const struct sockaddr *name, |\\
             & |            socklen_t namelen);| \\
    Linux:   & |int connect(int  sockfd,  const  struct sockaddr *serv_addr,|\\
               |            socklen_t addrlen);| \\
    WinXP:   & |int connect(SOCKET s, const struct sockaddr* name,| \\
             & |            int namelen);|\\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

  \item |socket| is a file descriptor referring to a socket. This corresponds to the [[fd]]
   argument of the model [[disconnect()]].

  \item |address| is a pointer to a location of size |address_len| containing a
   |sockaddr| structure which specifies the address to connect to. For a [[disconnect()]]
   call, the |sin_family| field of the |sockaddr| family must be set to
   |AF_UNSPEC|; other fields can be set to anything.

  \item the returned |int| is either |0| to indicate success or |-1| to
   indicate an error, in which case the error code is in |errno|.  On WinXP an error is
   indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
   code available through a call to |WSAGetLastError()|.

   \end{itemize}

  The Linux man-page states: "Unconnecting a socket by calling connect with a AF\_UNSPEC address is
  not yet implemented." As a result, a [[disconnect()]] call always returns successfully on Linux.

  The WinXP documentation states: "The default destination can be changed by simply calling
  |connect| again, even if the socket is already connected. Any datagrams queued for receipt
  are discarded if |name| is different from the previous |connect|." This implies
  that calling [[disconnect()]] will result in all datagrams on the socket's receive queue; however,
  this is not the case: no datagrams are discarded.

:*)

   (!h ts tid d fd fid sid ff tcp_sock err
     SS MM.

   disconnect_4 /* rp_tcp, fast fail (*: Fail with [[EAFNOSUPPORT]]: address family not supported; [[EOPNOTSUPP]]: operation not supported; [[EALREADY]]: connection already in progress; or [[EISCONN]]: socket already connected :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,disconnect(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     TCP_PROTO(tcp_sock) = (h.socks ' sid).pr /\
     ~(linux_arch h.arch) /\
     case tcp_sock.st of
         CLOSED      -> if bsd_arch h.arch then err = EINVAL \/ err = EAFNOSUPPORT
                        else err = EAFNOSUPPORT ||
         LISTEN      -> if      windows_arch h.arch then err = EAFNOSUPPORT  (*: socket is listening :*)
                        else if bsd_arch     h.arch then err = EOPNOTSUPP
                        else ASSERTION_FAILURE "disconnect_4:1" || (*: never happen :*)
         SYN_SENT    -> err = EALREADY || (*: connection already in progress :*)
         SYN_RECEIVED -> err = EALREADY || (*: connection already in progress :*)
         ESTABLISHED  -> err = EISCONN ||  (*: socket already connected :*)
         TIME_WAIT    -> if windows_arch h.arch then err = EISCONN
                         else if bsd_arch h.arch then err = EAFNOSUPPORT
                         else ASSERTION_FAILURE "disconnect_4:2" || (*: never happen :*)
         _1           -> err = EISCONN (*: all other states :*)


   (*:

    @description

    Consider a TCP socket [[sid]] referenced by [[fd]] on a non-Linux architecture. From thread [[tid]], which is in the [[Run]]
    state, a [[disconnect(fd)]] call is made. The call fails with an error [[err]] which depends on
    the the state of the socket: If the socket is in the [[CLOSED]] state then it fails with
    [[EAFNOSUPPORT]], except if on FreeBSD its [[bsd_cantconnect]] flag is set, in which case it
    fails with [[EINVAL]];if it is in the [[LISTEN]] state the error is [[EAFNOSUPPORT]] on WinXP
    and [[EOPNOTSUPP]] on FreeBSD; if it is in the [[SYN_SENT]] or [[SYN_RECEIVED]] state the error
    is [[EALREADY]]; if it is in the [[ESTABLISHED]] state the error is [[EISCONN]]; if it is in the
    [[TIME_WAIT]] state the error is [[EISCONN]] on WinXP and [[EAFNOSUPPORT]] on FreeBSD; in all
    other states the error is [[EISCONN]].

    A [[Lh_call(tid,disconnect(fd))]] transition is made, leaving the thread state [[Ret (FAIL
    err)]] where [[err]] is one of the above errors.

    @variation Linux

    This rule does not apply.

    @internal

    A [[disconnect()]] call is just a [[connect()]] call with the family set to
    |AF_UNSPEC|, so for a TCP connected socket, we get the appropriate error.

   :*)

   )

/\

   (!h ts tid d sid fd fid ff socks sock sock' oq oq' tcp_sock
    oflgs odata SS SS' MM.

   disconnect_5 /* rp_tcp, fast fail (*: Succeed on Linux, possibly dropping the connection :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++ [(sid, sock)];
               oq := oq  |>,
     SS,MM)
   -- Lh_call (tid,disconnect(fd))  -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK()), sched_timer));
               socks := socks |++ [(sid, sock')];
               oq := oq' |>,
     SS',MM)

   <==

     linux_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     TCP_PROTO(tcp_sock) = sock.pr /\
     (if tcp_sock.st IN {SYN_RECEIVED; ESTABLISHED; FIN_WAIT_1; FIN_WAIT_2; CLOSE_WAIT} then
         tcp_drop_and_close h.arch NONE sock (sock',(oflgs,odata)) /\
         if exists_quad_of sock then
             ? S0 s s'. SS = S0 |++ [(streamid_of_quad (quad_of sock),s)] /\
             write (quad_of sock) (oflgs,odata) s s' /\
             destroy (quad_of sock) (S0 |++ [(streamid_of_quad (quad_of sock),s')]) SS'
         else
             SS' = SS
     else
         sock = sock' /\
         oq = oq' /\
         SS' = SS
     )


   (*:

    @description

    On Linux, consider a TCP socket [[sid]], referenced by [[fd]]. From thread [[tid]], which is in
    the [[Run]] state, a [[disconnect(fd)]] call is made and succeeds.

    A [[Lh_call(tid,disconnect(fd))]] transition is made, leaving the thread state [[Ret
    (OK())]]. If the socket is in the [[SYN_RECEIVED]], [[ESTABLISHED]], [[FIN_WAIT_1]],
    [[FIN_WAIT_2]], or [[CLOSE_WAIT]] state then the connection is dropped, a RST segment is
    constructed, [[outsegs]], which may be placed on the host's outqueue, [[oq]], resulting in new
    outqueue [[oq']]. If the socket is in any other state then it remains unchanged, as does the
    host's outqueue.

    @variation Posix

    This rule does not apply.

    @variation FreeBSD

    This rule does not apply.

    @variation WinXP

    This rule does not apply.

    @modeldetails

    Note that [[disconnect()]] has not been properly implemented on Linux yet so it will always succeed.

    @internal

    A [[disconnect()]] call on a Linux TCP socket always generates OK. If the socket is in
    [[SYN_RECEIVED]], [[ESTABLISHED]], [[FIN_WAIT_1]], [[FIN_WAIT_2]] or [[CLOSE_WAIT]] it drops the
    connection.

   :*)

   )

/\

  (!h ts_ tid d sid fid sf is1 ff ret
    p1 is2 ps2 es udp fd socks cantsndmore cantrcvmore
    SS MM.

   disconnect_1 /* rp_udp, fast succeed (*: Unset socket's peer address :*) */
     (h with <| ts := FUPDATE ts_ (tid, Timed(Run,d));
               socks := socks |++
                        [(sid, Sock(SOME fid,sf,is1,SOME p1,is2,ps2,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))]
            |>,
     SS,MM)
   -- Lh_call (tid,disconnect(fd)) -->
     (h with <| ts := FUPDATE ts_ (tid,Timed(Ret (ret),sched_timer));
               socks := socks |++
                        [(sid, Sock(SOME fid,sf,NONE,SOME p1,NONE,NONE,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))]
            |>,
     SS,MM)

   <==

    fd IN FDOM h.fds /\
    fid = h.fds ' fd /\
    FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
    (if linux_arch h.arch then ret = OK()
     else if windows_arch h.arch /\ ?i2'.is2=SOME i2' then ret = OK()
     else                      ret = FAIL EAFNOSUPPORT)


   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]] with [[(is1,SOME p1,is2,ps2)]] as its binding
    quad. From thread [[tid]], which is in the [[Run]] state, a [[disconnect(fd)]] call is made. On
    Linux the call succeeds; on WinXP if the socket had its peer IP address set then the call
    succeeds, otherwise it fails with an [[EAFNOSUPPORT]] error; on FreeBSD the call fails with an
    [[EAFNOSUPPORT]] error.

    A [[Lh_call(tid,disconnect(fd))]] transition is made, leaving the thread state [[Ret (OK())]]
    or [[Ret (FAIL EAFNOSUPPORT)]]. The socket has its peer address set to [[(NONE,NONE)]], and its
    local IP address set to [[NONE]]. The local port, [[p1]], is left in place.

    @variation FreeBSD

    As above: the call fails with an [[EAFNOSUPPORT]] error.

    @variation Linux

    As above: the call succeeds.

    @variation WinXP

    As above: the call succeeds if the socket had a peer IP address set, or fails with an
    [[EAFNOSUPPORT]] error otherwise.

    @internal

    A [[disconnect()]] is a [[connect()]] with |AF_UNSPEC| as the family. UNPp226 says a
    successful [[disconnect]] may give an error, [[EAFNOSUPPORT]].

    Note that this leaves the local port in place, perhaps surprisingly.

   :*)

   )

/\

   (!h ts_ tid d sid fid ff ret h0
     sf es udp p1 fd socks cantsndmore cantrcvmore
     SS MM.

   disconnect_2 /* rp_udp, fast succeed (*: Unset socket's peer address and autobind local port :*) */
     (h0,SS,MM)
   -- Lh_call (tid,disconnect fd) -->
     (h0 with <| ts := FUPDATE ts_ (tid, Timed(Ret (ret), sched_timer));
                socks := socks |++
                         [(sid, Sock(SOME fid,sf,NONE,SOME p1,NONE,NONE,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))];
                bound := sid::h0.bound |>,
     SS,MM)

   <==

     h0 = h with <| ts := FUPDATE ts_ (tid, Timed(Run,d));
                    socks := socks |++
                             [(sid, Sock(SOME fid,sf,NONE,NONE,NONE,NONE,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))] |> /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     p1 IN autobind(NONE,PROTO_UDP,h0,h0.socks) /\
     (if linux_arch h.arch then ret = OK()
      else                      ret = (FAIL EAFNOSUPPORT))


   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]] and with binding quad
    [[(NONE,NONE,NONE,NONE)]]. From thread [[tid]], which is in the [[Run]] state, a
    [[disconnect(fd)]] call is made. The call succeeds on Linux and fails with an [[EAFNOSUPPORT]]
    error on FreeBSD and WinXP.

    A [[Lh_call(tid,disconnect(fd))]] transition is made, leaving the thread either in state [[Ret
    (OK())]], or in state [[Ret (FAIL EAFNOSUPPORT)]]. The socket is autobound to a local ephemeral
    port [[p1']], and [[sid]] is placed on the head of the host's list of bound sockets.

    @variation FreeBSD

    As above: the call fails with an [[EAFNOSUPPORT]] error.

    @variation Linux

    As above: the call succeeds.

    @variation WinXP

    As above: the call fails with an [[EAFNOSUPPORT]] error.

    @internal

    A [[disconnect()]] is a [[connect()]] with |AF_UNSPEC| as the family. UNPp226 says a
    successful [[disconnect]] may give an error, [[EAFNOSUPPORT]].

    This autobind may be surprising, but the resulting state \emph{can} receive msgs on [[*,p1]].

   :*)

   )

/\

   (!h ts tid d socks fid ff h0
     sf es udp fd e sid cantsndmore cantrcvmore
     SS MM.

   disconnect_3 /* rp_udp, fast fail (*: Fail with [[EAGAIN]], [[EADDRNOTAVAIL]], or [[ENOBUFS]]: there are no ephemeral ports left :*) */
     (h0,SS,MM)
   -- Lh_call (tid,disconnect fd) -->
     (h0 with <| ts := FUPDATE ts (tid, Timed(Ret (FAIL e),sched_timer)) |>,SS,MM)

   <==

     h0 = h with <| ts := FUPDATE ts (tid,Timed(Run,d));
                    socks := socks |++
                             [(sid,Sock(SOME fid,sf,NONE,NONE,NONE,NONE,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))] |> /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     autobind(NONE,PROTO_UDP,h0,h0.socks) = EMPTY /\
     e IN {EAGAIN; EADDRNOTAVAIL; ENOBUFS}


   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]] and with binding quad
    [[NONE,NONE,NONE,NONE]]. From thread [[tid]], which is in the [[Run]] state, a
    [[disconnect(fd)]] call is made. There are no ephemeral ports left, so the socket cannot be
    autobound to a local port. The call fails with an error: [[EAGAIN]], [[EADDRNOTAVAIL]], or
    [[ENOBUFS]].

    A [[Lh_call(tid,disconnect(fd))]] transition is made, leaving the thread state [[Ret (FAIL
    e)]] where [[e]] is one of the above errors.

    @internal

    According to the UDP Calculus paper, the error should be in [[{EAGAIN,EADDRINUSE}]], according
    to [[bind_9]] in this spec, when doing autobinding with no ephemeral ports available [[ENOBUFS]]
    is returned, and according to [[connect_5c]], if there are no ephemeral ports available, return
    [[EADDRNOTAVAIL]].

    :*)

   )



/\

(*:

@section [[dup]] ALL [[dup()]]
  \[ <[dup: fd -> fd]> \]

  A call to [[dup(fd)]] creates and returns a new file descriptor referring to the open file
  description referred to by the file descriptor [[fd]].
  A successful [[dup()]] call will return the least numbered free file descriptor. The call will
  only fail if there are no more free file descriptors, or [[fd]] is not a valid file descriptor.

@errors

  A call to [[dup()]] can fail with the errors below, in which case the corresponding exception is
  raised:

  @error [[EMFILE]] There are no more file descriptors available.
  @errorinclude [[misc]] [[EBADF]]

@commoncases

  [[dup_1]]; [[return_1]]

@api

  \begin{tabular}{ll}
    Posix:   & |int dup(int fildes);| \\
    FreeBSD: & |int dup(int oldd);| \\
    Linux:   & |int dup(int oldfd);| \\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}
    \item |fildes| is a file descriptor referring to the open file description for which
     another file descriptor is to be created for. This corresponds to the [[fd]] argument of the
     model [[dup()]].

    \item The returned |int| is either non-negative to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|. If the call is
     successful then the returned |int| is the new file descriptor corresponding to the
     [[fd]] return type of the model [[dup()]].

  \end{itemize}

  The FreeBSD and Linux interfaces are similar. This call does not exist on WinXP.

:*)

   (!h ts tid d
     fd fid fd' fds fds'
     SS MM.

   dup_1  /* rp_all, fast succeed (*: Successfully duplicate file descriptor :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               fds := fds |>,
     SS,MM)
   -- Lh_call (tid,dup(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK fd'),sched_timer));
               fds := fds' |>,
     SS,MM)

   <==

     unix_arch h.arch /\
     fd IN FDOM fds /\
     fid = fds ' fd /\
     nextfd h.arch fds fd' /\
     fd' < OPEN_MAX_FD /\
     fds' = fds |+ (fd', fid)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[dup(fd)]] call is made where [[fd]] is a
   file descriptor referring to an open file description identified by [[fid]]. A new file
   descriptor, [[fd']] can be created in an architecture-specific way according to the { [[nextfd]]}
   function. [[fd']] is less than the maximum open file descriptor, [[OPEN_MAX_FD]]. The call
   succeeds returning [[fd']].

   A [[Lh_call(tid,dup(fd))]] transition is made, leaving the thread state [[Ret (OK fd')]]. The
   host's finite map of file descriptors, [[fds]], is extended to map the new file descriptor
   [[fd']] to the file identifier [[fid]], which results in a new finite map of file descriptors
   [[fds']] for the host.

   @variation WinXP

   This rule does not apply: there is no [[dup()]] call on WinXP.

   @internal

   Creates a duplicate file descriptor for the open file description referenced by [[fd]].  Chooses
   the least-numbered free file descriptor.

   This call does not exist in Windows.

   :*)
   )

/\

   (!h ts tid d fd
     SS MM.

   dup_2 /* rp_all, fast fail (*: Fail with [[EMFILE]]: no more file descriptors available :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,dup(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EMFILE),sched_timer)) |>,SS,MM)

   <==

     unix_arch h.arch /\
     fd IN FDOM h.fds /\
     (CARD (FDOM h.fds) + 1) >= OPEN_MAX


  (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[dup(fd)]] call is made where [[fd]] is
    a valid file descriptor: it has an entry in the host's finite map of file descriptors,
    [[h.fds]]. Creating another file descriptor would cause the number of open file descriptors to
    be greater than or equal to the maximum number of open file descriptors, [[OPEN_MAX]]. The call
    fails with an [[EMFILE]] error.

    A [[Lh_call(tid,dup(fd))]] transition is made, leaving the thread state [[Ret (FAIL EMFILE)]].

    @variation WinXP

    This rule does not apply: there is no [[dup()]] call on WinXP.

    @internal

    Fails if no more file descriptors are available.

  :*)
  )

/\

(*:

@section [[dupfd]] ALL [[dupfd()]]
  \[ <[dupfd: fd * int -> fd]> \]

  A call to [[dupfd(fd,n)]] creates and returns a new file desciptor referring to the open file
  description referred to by the file descriptor [[fd]].

  A successful [[dupfd()]] call will return the least free file descriptor greater than or equal to
  [[n]]. The call will fail if [[n]] is negative or greater than the maximum allowed file
  descriptor, [[OPEN_MAX]]; if the file descriptor [[fd]] is not a valid file descriptor; or if
  there are no more file descriptors available.

@errors

  A call to [[dupfd()]] can fail with the errors below, in which case the corresponding exception is
  raised:

  @error [[EINVAL]] The requested file descriptor is invalid: it is negative or greater than the maximum allowed.

  @error [[EMFILE]] There are no more file descriptors available.

  @errorinclude [[misc]] [[EBADF]]

@commoncases

  [[dupfd_1]]; [[return_1]]

@api

  [[dupfd()]] is Posix [[fcntl()]] using the |F_DUPFD| command:

  \begin{tabular}{ll}
  Posix:   & |int fcntl(int fildes, int cmd, int arg);| \\
  FreeBSD: & |int fcntl(int fd, int cmd, int arg);| \\
  Linux:   & |int fcntl(int fd, int cmd, long arg);| \\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}
    \item |fildes| is a file descriptor referring to the open file description for which
     another file descriptor is to be created for. This corresponds to the [[fd]] argument of the
     model [[dupfd()]].

    \item |cmd| is the command to run on the specified file descriptor. For the model
     [[dupfd()]] this command is set to |F_DUPFD|.

    \item The returned |int| is either non-negative to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|. If the call was
     successful then the returned |int| is the new file descriptor.
  \end{itemize}

  The FreeBSD and Linux interfaces are similar. This call does not exist on WinXP.

@modeldetails

  Note that [[dupfd()]] is |fcntl()| with |F_DUPFD| rather than the similar but
  different |dup2()|.

:*)

   (!h ts tid d
     fd fid n fd' fds fds'
     SS MM.

   dupfd_1  /* rp_all, fast succeed (*: Successfully create a duplicate file descriptor greater than or equal to [[n]] :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               fds := fds |>,
     SS,MM)
   -- Lh_call (tid,dupfd(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK fd'),sched_timer));
               fds := fds' |>,
     SS,MM)

   <==

     unix_arch h.arch /\
     fd IN FDOM fds /\
     fid = fds ' fd /\
     n >= 0 /\
     FD (Num n) < OPEN_MAX_FD /\  (* attempt to save doing a LEAST if n is out of range *)
     fd' = FD (LEAST n'. Num n <= n' /\ FD n' < OPEN_MAX_FD /\ FD n' NOTIN FDOM fds) /\
     fds' = fds |+ (fd', fid)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[dupfd(fd,n)]] call is made. The host's
   finite map of file descriptors is [[fds]], and [[fd]] is a valid file descriptor in [[fds]],
   referring to an open file description identified by [[fid]]. [[n]] is non-negative. A file
   descriptor [[fd']] can be created, where it is the least free file descriptor greater than or
   equal to [[n]], and less than the maximum allowed file descriptor, [[OPEN_MAX_FD]]. The call
   succeeds, returning this new file descriptor [[fd']].

   A [[Lh_call(tid,dupfd(fd,n))]] transition is made, leaving the thread state [[Ret (OK
   fd')]]. An entry mapping [[fd']] to the open file description [[fid]] is added to [[fds]],
   resulting in a new finite map of file descriptors for the host, [[fds']].

   @variation WinXP

   This rule does not apply: there is no [[dupfd()]] call on WinXP.

   @internal

   Creates a duplicate file descriptor for the open file description referenced by [[fd]].  Chooses
   the least-numbered free file descriptor greater than or equal to the second argument [[fd']].

   Note that this function models POSIX [[fcntl(fd,F_DUPFD,fd')]] not [[dup2(fd,fd')]].

   This call is the only way to construct an fd of a specific number; there is no free constructor
   for fds, in order to preserve the abstraction.

   This call does not exist in Windows.

   :*)
   )

/\

   (!h ts tid d
     fd n err
     SS MM.

   dupfd_3 /* rp_all, fast fail (*: Fail with [[EINVAL]]: [[n]] is negative or greater than the maximum allowed file descriptor :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,dupfd(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer)) |>,SS,MM)

   <==

     unix_arch h.arch /\
     n < 0 \/ Num n >= OPEN_MAX /\
     err = (if bsd_arch h.arch then EBADF else EINVAL)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[dupfd(fd,n)]] call is made. [[n]] is
   either negative or greater than the maximum number of open file descriptors, [[OPEN_MAX]]. The
   call fails with an [[EINVAL]] error.

   A [[Lh_call(tid,dupfd(fd,n))]] transition is made, leaving the thread state [[Ret (FAIL
   EINVAL)]].

   @variation WinXP

   This call does not apply: there is no [[dupfd()]] call on WinXP.

   @variation FreeBSD

   On BSD the error [[EBADF]] is returned.

   @internal

   Fails if the requested file descriptor (second argument) is
   negative or greater than the maximum.

   Note that this function models POSIX [[fcntl(fd,F_DUPFD,fd')]] not [[dup2(fd,fd')]].

   :*)
   )

/\

   (!h ts tid d
     fd fid n fd'
     SS MM.

   dupfd_4 /* rp_all, fast fail (*: Fail with [[EMFILE]]: no more file descriptors available :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,dupfd(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EMFILE),sched_timer)) |>,SS,MM)

   <==

     unix_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     n >= 0 /\
     fd' = FD (LEAST n'. Num n <= n' /\ OPEN_MAX_FD <= FD n' /\ FD n' NOTIN FDOM h.fds)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[dupfd(fd,n)]] call is made. [[fd]] is a
   file descriptor referring to open file description [[fid]] and [[n]] is non-negative. The least
   file descriptor [[fd']] that is greater than or equal to [[n]] is greater than or equal to the
   maximum open file descriptor, [[OPEN_MAX_FD]]. The call fails with an [[EMFILE]] error.

   A [[Lh_call(tid,dupfd(fd,n))]] transition is made, leaving the thread state [[Ret (FAIL
   EMFILE)]].

   @variation WinXP

   This rule does not apply: there is no [[dupfd()]] call on WinXP.

   @internal

   No file descriptors greater than or equal to that specified are available.

   :*)
   )

/\

(*:

@section [[getfileflags]] ALL [[getfileflags()]]
 \[ <[getfileflags: fd -> filebflag list]> \]

   A call to [[getfileflags(fd)]] returns a list of the file flags currently set for the file which
   [[fd]] refers to.

   The possible file flags are:
   \begin{itemize}
     \item [[O_ASYNC]] Reports whether signal driven I/O is enabled.
     \item [[O_NONBLOCK]] Reports whether a socket is non-blocking.
   \end{itemize}

@errors

   A call to [[getfileflags()]] can fail with the error below, in which case the corresponding
   exception is raised:

   @errorinclude [[misc]] [[EBADF]]

@commoncases

  A call to [[getfileflags()]] is made, returning the flags set: [[getfileflags_1]]; [[return_1]]

@api

  [[getfileflags()]] is Posix |fcntl(fd,F_GETFL)|. On WinXP it is |ioctlsocket()|
  with the |FIONBIO| command.

  \begin{tabular}{ll}
    Posix:   & |int fcntl(int fildes, int cmd, ...);|\\
    FreeBSD: & |int fcntl(int fd, int cmd, ...);|\\
    Linux:   & |int fcntl(int fd, int cmd);|\\
    WinXP:   & |int ioctlsocket(SOCKET s, long cmd, u_long* argp)|
  \end{tabular}

   In the Posix interface:

   \begin{itemize}
     \item |fildes| is a file descriptor for the file to retrieve flags from. It corresponds
      to the [[fd]] argument of the model [[getfileflags()]]. On WinXP the |s| is a socket
      descriptor corresponding to the [[fd]] argument of the model [[getfileflags()]].

     \item |cmd| is a command to perform an operation on the file. This is set to
      |F_GETFL| for the model [[getfileflags()]]. On WinXP, |cmd| is set to
      |FIONBIO| to get the [[O_NONBLOCK]] flag; there is no [[O_ASYNC]] flag on WinXP.

     \item The call takes a variable number of arguments. For the model [[getfileflags()]] only the
      two arguments described above are needed.

     \item If the call succeeds the returned |int| represents the file flags that are set
      corresponding to the [[filebflag list]] return type of the model [[getfileflags()]]. If the
      returned |int| is |-1| then an error has occurred in which case the error code
      is in |errno|. On WinXP an error is indicated by a return value of
      |SOCKET_ERROR| with the actual error code available through a call to
      |WSAGetLastError()|.
   \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}
    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

    \item |WSAENOTSOCK| is a possible error on WinXP as the |ioctlsocket()| call is
     specific to a socket. In the model the [[getfileflags()]] call is performed on a file.
  \end{itemize}

:*)

   (!h ts tid d
     fd flags fid ft ff
     SS MM.

   getfileflags_1 /* rp_all, fast succeed (*: Return list of file flags currently set for an open file description :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getfileflags(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK flags),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(ft,ff) /\
     flags IN ORDERINGS ff.b


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[getfileflags(fd)]] call is made. [[fd]]
    refers to a file description [[File(ft,ff)]] where [[ff]] is the file flags that are set. The
    call succeeds, returning [[flags]] which is a list representing some ordering of the boolean
    file flags [[ff.b]] in [[ff]].

    A [[Lh_call(tid,getfileflags(fd))]] transition is made, leaving the thread state [[Ret
    (OK(flags))]].

    @internal

    Read the file flags from the open file description named.  Flags that are set will appear in the
    resulting list; flags that are clear will not.

    Models POSIX's [[fcntl()]] with [[F_GETFL]].

   :*)

   )

/\

(*:

@section [[getifaddrs]] ALL [[getifaddrs()]]
 \[ <[getifaddrs: unit -> (ifid * ip * ip list * netmask) list]> \]

  A call to [[getifaddrs()]] returns the interface information for a host. For each interface a
  tuple is constructed consisting of: the interface name, the primary IP address for the interface,
  the auxiliary IP addresses for the interface, and the subnet mask for the interface. A list is
  constructed with one tuple for each interface, and this is the return value of the call to
  [[getifaddrs()]].

@errors

  @errorinclude [[misc]] [[EINTR]]
  @errorinclude [[misc]] [[EBADF]]

@commoncases

  [[getifaddrs_1]]; [[return_1]]

@api

  [[getifaddrs()]] is two calls to Posix |ioctl()|: one with the |SIOCGIFCONF|
  request and one with the |SIOCGIFNETMASK| request. On FreeBSD there is a specific
  |getifaddrs()| call. On WinXP the [[getifaddrs()]] call does not exist.

  \begin{tabular}{ll}
    Posix:   & |int ioctl(int fildes, int request, ... /* arg */);| \\
    FreeBSD: & |int getifaddrs(struct ifaddrs **ifap);| \\
    Linux:   & |int ioctl(int d, int request, ...);|
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |fildes| is a file descriptor. There is no corresponding argument in the model
     [[getifaddrs()]].

    \item |request| is the operation to perform on the file. When |request| is
     |SIOCGIFCONF| the list of all interfaces is returned; when it is |SIOCNETMASK|
     the subnet mask is returned for an interface.

    \item The function takes a variable number of arguments. When |request| is
     |SIOCGIFCONF| there is a third argument: a pointer to a location to store a linked-list
     of the interfaces; when it is |SIOCGIFNETMASK| it is a pointer to a structure
     containing the interface and it is filled in with the subnet mask for that interface.

    \item The returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.

  \end{itemize}

  To construct the return value of type [[(ifid * ip * ip list * netmask) list]], the interface name
  and the IP addresses associated with it are obtained from the call to |ioctl()| using
  |SIOCGIFCONF|, and then the subnet mask for each interface is obtained from a call to
  |ioctl()| using |SIOCGIFNETMASK|.

  On FreeBSD the |ifap| argument to |getifaddrs()| is a pointer to a location to store
  a linked list of the interface information in, corresponding to the return type of the model
  [[getifaddrs()]].

@modeldetails

  Any of the errors possible when making an |ioctl()| call are possible: [[EIO]], [[ENOTTY]],
  [[ENXIO]], and [[ENODEV]]. None of these are modelled.

  Note that the Posix interface admits the possibility that the interfaces will change between the
  two calls, whereas in the model interface the [[getifaddrs()]] call is atomic.

:*)

    (!h ts tid d iflist ifidset ifidlist
      SS MM.

    getifaddrs_1 /* rp_all, fast succeed (*: Successfully return host interface information :*) */
      (h with ts := FUPDATE ts (tid, Timed(Run,d)),SS,MM)
    -- Lh_call (tid,getifaddrs ()) -->
      (h with ts := FUPDATE ts (tid, Timed(Ret (OK iflist),sched_timer)),SS,MM)

    <==

      ifidlist IN ORDERINGS ifidset /\
      LENGTH ifidlist = LENGTH iflist /\

      ifidset = { (ifid, hifd) |
                  ifid IN FDOM h.ifds /\
                  hifd = h.ifds ' ifid } /\

      EVERY I (MAP2 (\ (ifid,hifd) (ifid',primary,ipslist,netmask). (ifid' = ifid /\
                                                                     primary = hifd.primary /\
                                                                     ipslist IN ORDERINGS hifd.ipset /\
                                                                     netmask = hifd.netmask))
                    ifidlist iflist)


    (*:

     @description

     On a Unix architecture, from thread [[tid]], which is in the [[Run]] state, a [[getifaddrs()]]
     call is made. The call succeeds, returning [[iflist]] which is a list of tuples: one for each
     interface on the host. Each tuple consists of: the interface name; the primary IP address for
     the interface; a list of the other IP addresses for the interface; and the netmask for the
     interface.

     A [[Lh_call(tid,getifaddrs())]] transition is made, leaving the thread state [[Ret (OK
     iflist)]].

     @variation WinXP

     This call does not exist on WinXP.

     @internal

     Note this returns the interfaces  in any arbitrary order each time;
     likewise the aliases within each interface. If one
     wanted otherwise,  [[ifds]] and [[iset]] should be lists.
     :*)

    )

/\

(*:

@section [[getpeername]] ALL [[getpeername()]]
  \[ <[getpeername: fd -> (ip * port)]> \]

  A call to [[getpeername(fd)]] returns the peer address of the socket referred to by file
  descriptor [[fd]]. If the file descriptor refers to a socket [[sock]] then a successful call will
  return [[(i2,p2)]] where [[sock.is2 = SOME i2]], and [[sock.ps2 = SOME p2]].

@errors

  A call to [[getpeername()]] can fail with the errors below, in which case the corresponding
  exception is raised:

  @error [[ENOTCONN]] Socket not connected to a peer.
  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  [[getpeername_1]]; [[return_1]]

@api

  \begin{tabular}{ll}
    Posix:    & |int getpeername(int socket, struct sockaddr *restrict address,| \\
              & |                socklen_t *restrict address_len);| \\
    FreeBSD:  & |int getpeername(int s, struct sockaddr *name, | \\
              & |                socklen_t *namelen);| \\
    Linux:    & |int getpeername(int s, struct sockaddr *name, | \\
              & |                socklen_t *namelen);| \\
    WinXP:    & |int getpeername(SOCKET s,struct sockaddr* name,| \\
              & |                int* namelen);| \\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |socket| is a file descriptor referring to the socket to get the peer address of,
     corresponding to the [[fd]] argument in the model [[getpeername()]].

    \item |address| is a pointer to a |sockaddr| structure of length
     |address_len|, which contains the peer address of the socket upon return. These two
     correspond to the [[(ip * port)]] return type of the model [[getpeername()]]. The
     |sin_addr.s_addr| field of the |address| structure holds the peer IP address,
     corresponding to the [[ip]] in the return tuple; the |sin_port| field of the
     |address| structure holds the peer port, corresponding to the [[port]] in the return
     tuple.

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item According to the FreeBSD man page for [[getpeername()]], [[ECONNRESET]] can be returned if
     the connection has been reset by the peer. This behaviour has not been observed in any tests.

    \item On FreeBSD, Linux, and WinXP, [[EFAULT]] can be returned if the |name| parameter
     points to memory not in a valid part of the process address space. This is an artefact of the C
     interface to |getpeername()| that is excluded by the clean interface used in the model
     [[getpeername()]].

    \item In Posix, [[EINVAL]] can be returned if the socket has been shutdown; none of the
    implementations in the model return this error from a [[getpeername()]] call.

    \item In Posix, [[EOPNOTSUPP]] is returned if the [[getpeername()]] operation is not supported
     by the protocol. Both TCP and UDP support this operation.

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)

   (!h ts tid d
     fd fid sid ff i2 p2 sock
     SS MM.

   getpeername_1 /* rp_all, fast succeed (*: Successfully return socket's peer address :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getpeername(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (i2,p2)),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sock = h.socks ' sid /\
     sock.is2 = SOME i2 /\
     (sock.ps2 = SOME p2 \/ (windows_arch h.arch /\ sock.ps2 = NONE /\
                             (p2 = Port 0) /\ proto_of sock.pr = PROTO_UDP) (* on XP, can do a connect(SOME i1,NONE) and then getpeername returns with OK(i2,Port 0) *)) /\
     ((!tcp_sock. sock.pr = TCP_PROTO(tcp_sock) ==>
                  tcp_sock.st IN {ESTABLISHED; CLOSE_WAIT; LAST_ACK;
                                  FIN_WAIT_1; CLOSING} \/
                  (~sock.cantrcvmore /\ tcp_sock.st = FIN_WAIT_2) \/
                  (linux_arch h.arch /\ tcp_sock.st = SYN_RECEIVED) \/
                  (*: BSD listen bug :*)
                  (bsd_arch h.arch /\ tcp_sock.st = LISTEN) ) \/
      windows_arch h.arch)
     (* BSD actually tests the socket-layer flag |SS_ISCONNECTED|, which is set on entering
        [[ESTABLISHED]] (or [[FIN_WAIT_1]] etc.~if [[needfin]]), and cleared on entering [[TIME_WAIT]], or
        [[FIN_WAIT_2]] if the socket is not closed for reading.
       Further to this, if [[listen()]] was called on the socket, then BSD does not clear either
        the peer's IP and port, or |SS_ISCONNECTED|. Thus we may in this circumstance return
        successfully from [[getpeername()]] in the [[LISTEN]] state. MS thinks that it is an invariant
        that (in state [[LISTEN]]) peer IP/port set <=> |SS_ISCONNECTED|, so this should be
        sufficient to check.
        MS now realises that this is wrong - in SYN_SENT or SYN_RCVD, SS_ISCONNECTED is not set,
        but peer IP/port are.
        The solution to this (without cluttering the model with SS_ISCONNECTED is to make getpeername
        nondeterministic - either getpeername_1 or getpeername_2 may fire for BSD listening sockets. *)
     (* Windows just returns in all states, without checking *)
     (* TODO: does it really?  Or only in some states?  Check!  The autotests to confirm
        or deny this were not available at the time of writing. *)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[getpeername(fd)]] call is made. [[fd]]
    refers to a socket [[sock]], identified by [[sid]], which has its peer IP address set to [[SOME
    i2]] and its peer port address set to [[SOME p2]]. If [[sock]] is a TCP socket then either it is
    in state [[ESTABLISHED]], [[CLOSE_WAIT]], [[LAST_ACK]], [[FIN_WAIT_1]], or [[CLOSING]]; or it is
    in state [[FIN_WAIT_2]] and is not shutdown for reading. The call succeeds, returning
    [[(i2,p2)]], the socket's peer address.

    A [[Lh_call(tid,getpeername(fd))]] transition is made, leaving the thread state [[Ret( OK
    (i2,p2))]].

    @variation FreeBSD

    If [[sock]] is a TCP socket then it may be in state [[LISTEN]]; this is due to the FreeBSD bug
    that allows [[listen()]] to be called on a synchronised socket.

    @variation Linux

    If [[sock]] is a TCP socket then it may also be in state [[SYN_RECEIVED]].

    @variation WinXP

    If [[sock]] is a UDP socket and has no peer port set, [[sock.ps2 = NONE]] then the call may
    still succeed with [[p2 = Port 0]]. Additionally, if [[sock]] is a TCP socket then it may be in
    any state.

    @internal

    Ask for the remote IP address and port of this connection, if available.

    POSIX claims [[EINVAL]] is possible "if the socket has been shut down".  We have not modelled
    this either; not clear exactly what point it is referring to, or that this makes sense.

    Note that on Windows XP, we return [[OK(i2,Port 0)]] if we made a [[connect(SOME i2,NONE)]] call
    previously, whereas BSD and Linux adhere to rule [[getpeername_2]].

   :*)
   )

/\

   (!h ts tid d
     fd fid sid ff sock
     SS MM.

   getpeername_2 /* rp_all, fast fail (*: Fail with [[ENOTCONN]]: socket not connected to a peer :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getpeername(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOTCONN),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sock = h.socks ' sid /\
     ~(sock.is2 <> NONE /\
       (sock.ps2 <> NONE \/ (windows_arch h.arch /\ proto_of sock.pr = PROTO_UDP)) /\
       (!tcp_sock. sock.pr = TCP_PROTO(tcp_sock) ==>
            tcp_sock.st IN {ESTABLISHED; CLOSE_WAIT; LAST_ACK; FIN_WAIT_1; CLOSING (* SYN_RECEIVED ??*)} \/
            (~sock.cantrcvmore /\ tcp_sock.st = FIN_WAIT_2) \/
            (linux_arch h.arch /\ tcp_sock.st = SYN_RECEIVED) \/
	    (* MS: note that we deliberately do not have the condition that
                   bsd sock.st <> LISTEN, as the return of getpeername depends
                   on SS_ISCONNECTED which is (a) not modelled, and (b) has
                   no derivable expression from other sock vars. So, to account
                   for the possibility of bsd_listen_bug, we make getpeername
                   non-deterministic. See comment in getpeername_1. *)
            windows_arch h.arch))


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[getpeername(fd)]] call is made where
    [[fd]] refers to a socket [[sock]] identified by [[sid]]. The socket does not have both its peer
    IP and port set, If it is a TCP socket then it is not in state [[ESTABLISHED]], [[CLOSE_WAIT]],
    [[LAST_ACK]], [[FIN_WAIT_1]] or [[CLOSING]]; or in state [[FIN_WAIT_2]] and not shutdown for
    reading. The call fails with an [[ENOTCONN]] error.

    A [[Lh_call(tid,getpeername(fd))]] transition is made, leaving the thread state [[Ret (FAIL
    ENOTCONN)]].

    @variation Linux

    As above, with the additional condition that if [[sock]] is a TCP socket then it is not in state
    [[SYN_RECEIVED]].

    @variation WinXP

    As above, except that if [[sock]] is a TCP socket then it does not matter what state it is in
    and if it is a UDP socket then the state of its peer port, whether it is set or unset, does not
    matter.

    @internal

    If the socket is not connected, this request does not make sense.

    Note that we can do a [[connect(SOME i1, NONE)]] which succeeds on Linux, yet when we then call
    [[getpeername]] we fail.

   :*)
   )

/\

(*:

@section [[getsockbopt]] ALL [[getsockbopt()]]
  \[ <[getsockbopt: (fd * sockbflag) -> bool]> \]

  A call to [[getsockbopt(fd,flag)]] returns the value of one of the socket's boolean-valued flags.

  The [[fd]] argument is a file descriptor referring to the socket to retrieve a flag's value from,
  and the [[flag]] argument is the boolean-valued socket flag to get. Possible flags are:

  \begin{itemize}

    \item [[SO_BSDCOMPAT]] Reports whether the BSD semantics for delivery of ICMPs to UDP sockets
     with no peer address set is enabled.

    \item [[SO_DONTROUTE]] Reports whether outgoing messages bypass the standard routing facilities.

    \item [[SO_KEEPALIVE]] Reports whether connections are kept active with periodic transmission of
     messages, if this is supported by the protocol.

    \item [[SO_OOBINLINE]] Reports whether the socket leaves received out-of-band data (data marked
     urgent) inline.

    \item [[SO_REUSEADDR]] Reports whether the rules used in validating addresses supplied to
     [[bind()]] should allow reuse of local ports, if this is supported by the protocol.

  \end{itemize}

  The return value of the [[getsockbopt()]] call is the boolean-value of the specified socket flag.

@errors

  A call to [[getsockbopt()]] can fail with the errors below, in which case the corresponding
  exception is raised:

  @error [[ENOPROTOOPT]] The specified flag is not supported by the protocol.

  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  [[getsockbopt_1]]; [[return_1]]

@api

  [[getsockbopt()]] is Posix |getsockopt()| for boolean-valued socket flags.

  \begin{tabular}{ll}
    Posix:   & |int getsockopt(int socket, int level, int option_name,|\\
             & |               void *restrict option_value, | \\
             & |               socklen_t *restrict option_len);| \\
    FreeBSD: & |int getsockopt(int s, int level, int optname, | \\
             & |               void *optval, socklen_t *optlen); | \\
    Linux:   & |int getsockopt(int  s, int level, int optname, | \\
             & |               void *optval, socklen_t *optlen);| \\
    WinXP:   & |int getsockopt(SOCKET s,int level,int optname, | \\
             & |               char* optval, int* optlen); | \\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |socket| is the file descriptor of the socket on which to get the flag,
     corresponding to the [[fd]] argument of the model [[getsockbopt()]].

    \item |level| is the protocol level at which the flag resides: |SOL_SOCKET| for
     the socket level options, and |option_name| is the flag to be retrieved. These two
     correspond to the [[flag]] argument to the model [[getsockbopt()]] where the possible values of
     |option_name| are limited to: [[SO_BSDCOMPAT]], [[SO_DONTROUTE]], [[SO_KEEPALIVE]],
     [[SO_OOBINLINE]], and [[SO_REUSEADDR]].

    \item |option_value| is a pointer to a location of size |option_len| to store
     the value retrieved by |getsockopt()|. These two correspond to the [[bool]] return type
     of the model [[getsockbopt()]].

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item |EFAULT| signifies the pointer passed as |option_value| was
     inaccessible. On WinXP, the error |WSAEFAULT| may also signify that the
     |optlen| parameter was too small.

    \item |EINVAL| signifies the |option_name| was invalid at the specified socket
     |level|. In the model, typing prevents an invalid flag from being specified in a call
     to [[getsockbopt()]].

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)

   (!h ts tid d
     fd f fid sid ff sf
     SS MM.

   getsockbopt_1 /* rp_all, fast succeed (*: Successfully retrieve value of boolean socket flag :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getsockbopt(fd,f)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (sf.b(f))),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sf = (h.socks ' sid).sf /\
     (windows_arch h.arch /\ proto_of (h.socks ' sid).pr = PROTO_UDP
        ==> f NOTIN {SO_KEEPALIVE})


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[getsockbopt(fd,f)]] call is made. [[fd]]
    refers to a socket [[sid]] with boolean socket flags [[sf.b]], and [[f]] is a boolean socket
    flag. The call succeeds, returning the value of [[f]]: [[T]] if [[f]] is set, and [[F]] if [[f]]
    is not set in [[sf.b]].

    A [[Lh_call(tid,getsockbopt(fd,f))]] transition is made, leaving the thread state [[Ret
    (OK(sf.b(f)))]] where [[sf.b(f)]] is the boolean value of the socket's flag [[f]].

    @variation WinXP

    As above, except that if [[sid]] is a UDP socket, then [[f]] cannot be [[SO_KEEPALIVE]] or
    [[SO_OOBINLINE]].

    @internal

    Read the named boolean flag on the socket description named.

    Models POSIX's |getsockopt()| for boolean flags.

    Typing ensures [[f]] is valid and is a boolean flag.

    I have not done any [[EISCONN]] errors.

    :*)
   )

/\

   (!h ts tid d socks sid sock udp fd f fid ff
     SS MM.

    getsockbopt_2 /* rp_udp, fast succeed (*: Fail with [[ENOPROTOOPT]]: option not valid on WinXP UDP socket :*) */
      (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
                socks := socks |++
                         [(sid, sock with <| pr := UDP_PROTO(udp) |>)] |>,
      SS,MM)
    -- Lh_call (tid,getsockbopt(fd,f)) -->
      (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOPROTOOPT),sched_timer));
                socks := socks |++
                         [(sid,sock with <| pr := UDP_PROTO(udp) |>)] |>,
      SS,MM)

    <==

      windows_arch h.arch /\
      fd IN FDOM h.fds /\
      fid = h.fds ' fd /\
      FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
      f IN {SO_KEEPALIVE}


   (*:

    @description

    On WinXP, consider a UDP socket [[sid]] referenced by [[fd]]. From thread [[tid]], which is in
    the [[Run]] state, a [[getsockbopt(fd,f)]] call is made, where [[f]] is either [[SO_KEEPALIVE]]
    or [[SO_OOBINLINE]]. The call fails with an [[ENOPROTOOPT]] error.

    A [[Lh_call(tid,getsockbopt(fd,f))]] transition is made, leaving the thread state [[Ret (FAIL
    ENOPROTOOPT)]].

    @variation FreeBSD

    This rule does not apply.

    @variation Linux

    This rule does not apply.

    :*)

   )

/\

(*:

@section [[getsockerr]] ALL [[getsockerr()]]
  \[ <[getsockerr: fd -> unit]> \]

  A call [[getsockerr(fd)]] returns the pending error of a socket, clearing it, if there is one.

  [[fd]] is a file descriptor referring to a socket. If the socket has a pending error then the
  [[getsockerr()]] call will fail with that error, otherwise it will return successfully.

@errors

  In addition to failing with the pending error, a call to [[getsockerr()]] can fail with the errors
  below, in which case the corresponding exception is raised:

  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  [[getsockerr_1]]; [[return_1]]

  [[getsockerr_2]]; [[return_1]]

@api

  [[getsockerr()]] is Posix |getsockopt()| for the |SO_ERROR| socket option.

  \begin{tabular}{ll}
     Posix:   & |int getsockopt(int socket, int level, int option_name,|\\
              & |               void *restrict option_value, | \\
              & |               socklen_t *restrict option_len);| \\
     FreeBSD: & |int getsockopt(int s, int level, int optname, | \\
              & |               void *optval, socklen_t *optlen); | \\
     Linux:   & |int getsockopt(int  s, int level, int optname, | \\
              & |               void *optval, socklen_t *optlen);| \\
     WinXP:   & |int getsockopt(SOCKET s,int level,int optname, | \\
              & |               char* optval, int* optlen); | \\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |socket| is the file descriptor of the socket to get the option on, corresponding
     to the [[fd]] argument of the model [[getsockerr()]].

    \item |level| is the protocol level at which the option resides: |SOL_SOCKET|
     for the socket level options, and |option_name| is the option to be retrieved. For
     [[getsockerr()]] |option_name| is set to |SO_ERROR|.

    \item |option_value| is a pointer to a location of size |option_len| to store
     the value retrieved by |getsockopt()|. When |option_name| is
     |SO_ERROR| these fields are not used.

    \item the returned |int| is either |0| to indicate the socket has no pending
     error or |-1| to indicate a pending error, in which case the error code is in
     |errno|.  On WinXP an error is indicated by a return value of |SOCKET_ERROR|,
     not |-1|, with the actual error code available through a call to
     |WSAGetLastError()|.

  \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item |EFAULT| signifies the pointer passed as |option_value| was
     inaccessible. On WinXP, the error |WSAEFAULT| may also signify that the
     |optlen| parameter was too small.

    \item |EINVAL| signifies the |option_name| was invalid at the specified socket
     |level|. In the model, the flag for [[getsockerr()]] is always |SO_ERROR| so
     this error cannot occur.

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)

   (!h ts tid d
     fd fid sid ff
     SS MM.

   getsockerr_1 /* rp_all, fast succeed (*: Return successfully: no pending error :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getsockerr(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     (h.socks ' sid).es = NONE


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[getsockerr(fd)]] call is made. [[fd]]
    refers to a socket [[sid]] which has no pending errors. The call succeeds.

    A [[Lh_call(tid,getsockerr(fd))]] transition is made, leaving the thread state [[Ret
    (OK())]].

    @internal

    Attempt to read the socket's pending error, if any.  If there is no pending error, return OK.

    This models POSIX [[getsockopt(SOL_SOCKET,SO_ERROR)]].

   :*)
   )

/\

   (!h ts tid d
     fd fid sid socks ff sock sock' e
     SS MM.

   getsockerr_2 /* rp_all, fast fail (*: Fail with pending error and clear the error :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++ [(sid,sock)] |>,
     SS,MM)
   -- Lh_call (tid,getsockerr(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer));
               socks := socks |++ [(sid,sock')] |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     SOME e = sock.es /\
     sock' = sock with <| es := NONE |>


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[getsockerr(fd)]] call is made. [[fd]]
    refers to a socket [[sid]] which has pending error [[e]]. The call fails, returning [[e]].

    A [[Lh_call(tid,getsockerr(fd))]] transition is made, leaving the thread state [[Ret (FAIL
    e)]] and cleaing the error [[e]] from the socket.

    @internal

    Attempt to read the socket's pending error, if any.  If there is a pending error on the socket,
    fail with that error and clear the error from the socket.

    This models POSIX [[getsockopt(SOL_SOCKET,SO_ERROR)]] (with a slightly different interface; this
    seemed good to us at the time).

    :*)
   )

/\

(*:

@section [[getsocklistening]] ALL [[getsocklistening()]]
 \[ <[getsocklistening: fd -> bool]> \]

  A call to [[getsocklistening(fd)]] returns [[T]] if the socket referenced by [[fd]] is listening,
  or [[F]] otherwise. For TCP a socket is listening if it is in the [[LISTEN]] state. For UDP, which
  is not a connection-oriented protocol, a socket can never be listening.

@errors

  A call to [[getsocklistening()]] can fail with the errors below, in which case the corresponding
  exception is raised:

  @error [[ENOPROTOOPT]] FreeBSD does not support this socket option, and on Linux and WinXP this
  option is not supported for UDP sockets.

  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  [[getsocklistening_1]]; [[return_1]]

@api

  [[getsocklistening()]] is Posix |getsockopt()| for the |SO_ACCEPTCONN| socket
  option.

  \begin{tabular}{ll}
     Posix:   & |int getsockopt(int socket, int level, int option_name,|\\
              & |               void *restrict option_value, | \\
              & |               socklen_t *restrict option_len);| \\
     FreeBSD: & |int getsockopt(int s, int level, int optname, | \\
              & |               void *optval, socklen_t *optlen); | \\
     Linux:   & |int getsockopt(int  s, int level, int optname, | \\
              & |               void *optval, socklen_t *optlen);| \\
     WinXP:   & |int getsockopt(SOCKET s,int level,int optname, | \\
              & |               char* optval, int* optlen); | \\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |socket| is the file descriptor of the socket to get the option on, corresponding
     to the [[fd]] argument of the model [[getsocklistening()]].

    \item |level| is the protocol level at which the option resides: |SOL_SOCKET|
     for the socket level options, and |option_name| is the option to be retrieved. For
     [[getsocklistening()]] |option_name| is set to |SO_ACCEPTCONN|.

    \item |option_value| is a pointer to a location of size |option_len| to store
     the value retrieved by |getsockopt()|. The value stored in the location corresponds to
     the [[bool]] return value of the model [[getsocklistening()]].

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

  The Linux and WinXP interfaces are similar except where noted. FreeBSD does not support the
  |SO_ACCEPTCONN| socket option.

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item |EFAULT| signifies the pointer passed as |option_value| was
     inaccessible. On WinXP, the error |WSAEFAULT| may also signify that the
     |optlen| parameter was too small.

    \item |EINVAL| signifies the |option_name| was invalid at the specified socket
     |level|. In the model, the flag for [[getsocklistening()]] is always
     |SO_ACCEPTCONN| so this error cannot occur.

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)

   (!h ts tid d
     fd fid sid ff b tcp_sock
     SS MM.

   getsocklistening_1 /* rp_tcp, fast succeed (*: Return successfully: [[T]] if socket is listening, [[F]] otherwise :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getsocklistening(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK b),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     TCP_PROTO(tcp_sock) = (h.socks ' sid).pr /\
     b = (tcp_sock.st = LISTEN) /\
     ~(bsd_arch h.arch)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[getsocklistening(fd)]] call is
    made where [[fd]] refers to a TCP socket [[sid]].

    A [[Lh_call(tid,getsocklistening(fd))]] transition is made, leaving the thread state [[Ret
    (OK b)]] where [[b=T]] if the socket is in the [[LISTEN]] state, and [[b=F]] otherwise.

    @variation FreeBSD

    This rule does not apply: see [[getsocklistening_3]].

    @internal

    Return [[T]] if the socket is listening, else [[F]].  BSD does not support
    [[SO_ACCEPTCONN]]. This models POSIX [[getsockopt(SOL_SOCKET,SO_ACCEPTCONN)]].

   :*)
   )

/\

   (!h ts tid d
     fd fid sid ff tcp_sock SS MM.

   getsocklistening_3 /* rp_tcp, fast fail (*: Fail with [[ENOPROTOOPT]]: on FreeBSD operation not supported :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getsocklistening(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOPROTOOPT),sched_timer)) |>,SS,MM)

   <==

     bsd_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     TCP_PROTO(tcp_sock) = (h.socks ' sid).pr


   (*:

    @description

    On FreeBSD, a [[getsocklistening(fd)]] call is made from thread [[tid]] which is in the [[Run]]
    state where[[fd]] refers to a TCP socket [[sid]]. The call fails with an [[ENOPROTOOPT]] error.

    A [[Lh_call(tid,getsocklistening(fd))]] transition is made, leaving the thread state [[Ret
    (FAIL ENOPROTOOPT)]].

    @variation Linux

    This rule does not apply: see [[getsocklistening_1]].

    @variation WinXP

    This rule does not apply: see [[getsocklistening_1]].

    @internal

    BSD does not support [[SO_ACCEPTCONN]].
    This models POSIX [[getsockopt(SOL_SOCKET,SO_ACCEPTCONN)]].

   :*)
   )

/\

   (!h ts tid d fd fid sid ff rc ret
     SS MM.

   getsocklistening_2 /* rp_udp, rc (*: Return [[F]] or fail with [[ENOPROTOOPT]]: a UDP socket cannot be listening :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getsocklistening(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (ret), sched_timer)) |>,SS,MM)

   <==

     proto_of (h.socks ' sid).pr = PROTO_UDP /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     if linux_arch h.arch then rc = fast succeed /\ ret = OK F
     else                      rc = fast fail    /\ ret = FAIL ENOPROTOOPT


   (*:

    @description

    Consider a UDP socket [[sid]], referenced by [[fd]]. From thread [[tid]], which is in the
    [[Run]] state, a [[getsocklistening(fd)]] call is made. On Linux the call succeeds, returning
    [[F]]; on FreeBSD and WinXP the call fails with an [[ENOPROTOOPT]] error.

    A [[Lh_call(tid,getsocklistening(fd))]] transition is made, leaving the thread state [[Ret
    (OK(F))]] on Linux, and [[Ret (FAIL ENOPROTOOPT)]] on FreeBSD and Linux.

    @variation Posix

    As above: the call fails with an [[ENOPROTOOPT]] error.

    @variation FreeBSD

    As above: the call fails with an [[ENOPROTOOPT]] error.

    @variation Linux

    As above: the call succeeds, returning [[F]].

    @variation WinXP

    As above: the call fails with an [[ENOPROTOOPT]] error.

    @internal

    Despite [[listen]] not making sense for a UDP socket, this call does not return an error such as
    [[EINVAL]] but instead returns [[F]].

    This models POSIX [[getsockopt(SOL_SOCKET,SO_ACCEPTCONN)]].

    :*)

   )

/\

(*:

@section [[getsockname]] ALL [[getsockname()]]
  \[ <[getsockname: fd -> (ip option * port option)]> \]

  A call to [[getsockname(fd)]] returns the local address pair of a socket. If the file descriptor
  [[fd]] refers to the socket [[sock]] then the return value of a successfull call will be
  [[(sock.is1, sock.ps1)]].

@errors

  A call to [[getsockname()]] can fail with the errors below, in which case the corresponding
  exception is raised:

  @error [[ECONNRESET]] On FreeBSD, TCP socket has its [[cb.bsd_cantconnect]] flag set due to previous connection establishment attempt.
  @error [[EINVAL]] Socket not bound to local address on WinXP.
  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]
  @errorinclude [[misc]] [[ENOBUFS]]

@commoncases

  [[getsockname_1]]; [[return_1]]

@api

  \begin{tabular}{ll}
    Posix:   & |int getsockname(int socket, struct sockaddr *restrict address,| \\
             & |                socklen_t *restrict address_len);| \\
    FreeBSD: & |int getsockname(int s, struct sockaddr *name, | \\
             & |                socklen_t *namelen);| \\
    Linux:   & |int getsockname(int s, struct sockaddr *name, | \\
             & |                socklen_t *namelen);| \\
    WinXP:   & |int getsockname(SOCKET s, struct sockaddr* name, |\\
             & |                int* namelen);| \\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |socket| is a file descriptor referring to the socket to get the local address of,
     corresponding to the [[fd]] argument in the model [[getsockname()]].

    \item |address| is a pointer to a |sockaddr| structure of length
     |address_len|, which contains the local address of the socket upon return. These two
     correspond to the [[(ip option, port option)]] return type of the model [[getsockname()]]. If
     the |sin_addr.s_addr| field of the |name| structure is set to |0| on
     return, then the socket's local IP address is not set: the [[ip option]] member of the return
     tuple is set to [[NONE]]; otherwise, if it is set to |i| then it corresponds to the
     socket having local IP address and so the [[ip option]] member of the return tuple is[[SOME
     i]]. If the |sin_port| field of the |name| structure is set to |0| on
     return then the socket does not have a local port set, corresponding to the [[port option]] in
     the return tuple being [[NONE]]; otherwise the |sin_port| field is set to |p|
     corresponding to the socket having its local port set: the [[port option]] in the return tuple
     is [[SOME p]].

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item On FreeBSD, Linux, and WinXP, [[EFAULT]] can be returned if the |name| parameter
     points to memory not in a valid part of the process address space. This is an artefact of the C
     interface to |getsockname()| that is excluded by the clean interface used in the model
     [[getsockname()]].

    \item in Posix, [[EINVAL]] can be returned if the socket has been shutdown. None of the
    implementations return [[EINVAL]] in this case.

    \item in Posix, [[EOPNOTSUPP]] is returned if the [[getsockname()]] operation is not supported
     by the protocol. Both UDP and TCP support this operation.

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)

   (!h ts tid d
     fd fid sid ff sock
     SS MM.

   getsockname_1 /* rp_all, fast succeed (*: Successfully return socket's local address :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getsockname(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (sock.is1,sock.ps1)),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sock = h.socks ' sid /\
     (case sock.pr of
        TCP_PROTO(tcp_sock) ->
          bsd_arch h.arch ==> T ||
        UDP_PROTO(_444) -> T) /\
     (windows_arch h.arch ==> sock.is1 <> NONE \/ sock.ps1 <> NONE)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[getsockname(fd)]] call is made where
    [[fd]] refers to socket [[sock]], identified by [[sid]]. The socket's local address is returned:
    [[(sock.is1,sock.ps1)]].

    A [[Lh_call(tid,getsockname(fd))]] transition is made, leaving the thread state [[Ret (OK
    (sock.is1, sock.ps1))]].

    @variation FreeBSD

    This rule does not apply if the socket's [[bsd_cantconnect]] flag is set in its control block
    and its local port is not set.

    @variation WinXP

    As above with the additional condition that either the socket's local IP address or local port
    must be set.

    @internal

    Ask for the local IP address and port of the connection.

    BSD's man page claims we can get an [[ECONNRESET]] from this call.  We have not modelled this
    here, pending experiment (e.g., why not [[ENETUNREACH]] as well?).

    POSIX: if socket is unbound, the return value is \emph{unspecified}.  We give it as
    [[(NONE,NONE)]] instead.  (what about [[(NONE,SOME p1)]]?).

    POSIX claims [[EINVAL]] is possible "if the socket has been shut down".  We have not modelled
    this either; not clear exactly what point it is referring to, or that this makes sense.

   :*)

   )

/\

   (!h ts tid d socks sid sock tcp_sock fd fid ff SS MM.

   getsockname_2 /* rp_tcp, fast fail (*: Fail with [[ECONNRESET]]: previous connection attempt has failed on FreeBSD :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++ [(sid,sock)] |>,
     SS,MM)
   -- Lh_call (tid,getsockname(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ECONNRESET),sched_timer));
               socks := socks |++ [(sid,sock)] |>,
     SS,MM)

   <==

     bsd_arch h.arch /\
     sock.pr = TCP_PROTO(tcp_sock) /\
     ( sock.ps1 = NONE) /\
      (* TJR: note that getsockname_1 and 2 are essentially cases on the above conjunction. However, there is a loss of coherence because we no longer have info on bsdcantconnect *)
      (* MS: ps1 = NONE is implied by bsd_cantconnect, so not really needed *)
      (* BSD returns ECONNRESET if we shutdown the socket for writing while in [[CLOSED]] or [[LISTEN]] *)
      (* MS: no longer include test "sock.cantsndmore = T /\ tcp_sock.st IN {CLOSED;LISTEN}" as a possible
             condition for rule firing, as we could have arrived in LISTEN due to the user calling listen()
             from e.g. FIN_WAIT_2, in which case we want getsockname_1 to fire. Calling shutdown()
             from a socket in LISTEN/CLOSED is now handled correctly by tcp_close in shutdown_1, so the
             above condition will catch this case. *)
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     h.files ' fid = File(FT_Socket(sid),ff)


   (*:

    @description

    On FreeBSD, from thread [[tid]], which is in the [[Run]] state, a [[getsockname(fd)]] call is
    made where [[fd]] refers to a TCP socket [[sock]], identified by [[sid]], which has its
    [[bsd_cantconnect]] flag set and is not bound to a local port.

    A [[Lh_call(tid,getsockname(fd))]] transition is made, leaving the thread state [[Ret (FAIL
    ECONNRESET)]].

    @variation Linux

    This rule does not apply.

    @variation WinXP

    This rule does not apply.

   :*)


   )

/\

   (!h ts tid d sid
     socks sock fd fid ff
     SS MM.

   getsockname_3 /* rp_all, fast fail (*: Fail with [[EINVAL]]: socket not bound on WinXP :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| is1 := NONE; ps1 := NONE |>)] |>,
     SS,MM)
   -- Lh_call (tid,getsockname(fd)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINVAL),sched_timer));
               socks := socks |++
                        [(sid,sock with <| is1 := NONE; ps1 := NONE |>)] |>,
     SS,MM)

   <==

     windows_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff)


   (*:

    @description

    On WinXP, a [[getsockname(fd)]] call is made from thread [[tid]] which is in the [[Run]]
    state. [[fd]] refers to a socket [[sid]] which has neither its local IP address nor its local
    port set. The call fails with an [[EINVAL]] error.

    A [[Lh_call(tid,getsockname(fd))]] transition is made, leaving the thread state [[Ret (FAIL
    EINVAL)]].

    @variation Posix

    This rule does not apply.

    @variation FreeBSD

    This rule does not apply.

    @variation Linux

    This rule does not apply.

    @internal

    On XP, calling [[getsockname]] on an unbound socket fails with an [[EINVAL]] error. For Linux
    and BSD behaviour see rule [[getsockname_1]].

   :*)

   )

/\

(*:

@section [[getsocknopt]] ALL [[getsocknopt()]]
 \[ <[getsocknopt: (fd * socknflag) -> int]> \]

  A call to [[getsocknopt(fd,flag)]] returns the value of one of the socket's numeric flags.  The
  [[fd]] argument is a file descriptor referring to the socket to retrieve a flag's value from. The
  [[flag]] argument is a numeric socket flag. Possible flags are:

  \begin{itemize}
    \item [[SO_RCVBUF]] Reports receive buffer size information.
    \item [[SO_RCVLOWAT]] Reports the minimum number of bytes to process for socket input
     operations.
    \item [[SO_SNDBUF]] Reports send buffer size information.
    \item [[SO_SNDLOWAT]] Reports the minimum number of bytes to process for socket output
     operations.
  \end{itemize}

  The return value of the [[getsocknopt()]] call is the numeric-value of the specified [[flag]].

@errors

  A call to [[getsocknopt()]] can fail with the errors below, in which case the corresponding
  exception is raised:

  @error [[ENOPROTOOPT]] The specified flag is not supported by the protocol.
  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  [[getsocknopt_1]]; [[return_1]]

@api

  [[getsocknopt()]] is Posix |getsockopt()| for numeric socket flags.

  \begin{tabular}{ll}
    Posix:   & |int getsockopt(int socket, int level, int option_name,|\\
             & |               void *restrict option_value, | \\
             & |               socklen_t *restrict option_len);| \\
    FreeBSD: & |int getsockopt(int s, int level, int optname, | \\
             & |               void *optval, socklen_t *optlen); | \\
    Linux:   & |int getsockopt(int  s, int level, int optname, | \\
             & |               void *optval, socklen_t *optlen);| \\
    WinXP:   & |int getsockopt(SOCKET s,int level,int optname, | \\
             & |               char* optval, int* optlen); | \\
  \end{tabular}

  In the Posix interface:
  \begin{itemize}

    \item |socket| is the file descriptor of the socket to set the option on, corresponding
     to the [[fd]] argument of the model [[getsocknopt()]].

    \item |level| is the protocol level at which the option resides: |SOL_SOCKET|
     for the socket level options, and |option_name| is the option to be retrieved. These
     two correspond to the [[flag]] argument to the model [[getsocknopt()]] where the possible
     values of |option_name| are limited to [[SO_RCVBUF]], [[SO_RCVLOWAT]], [[SO_SNDBUF]]
     and [[SO_SNDLOWAT]].

    \item |option_value| is a pointer to a location of size |option_len| to store
     the value retrieved by |getsockopt()|. They correspond to the [[int]] return type of
     the model [[getsocknopt()]].

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item |EFAULT| signifies the pointer passed as |option_value| was
     inaccessible. On WinXP, the error |WSAEFAULT| may also signify that the
     |optlen| parameter was too small.

    \item |EINVAL| signifies the |option_name| was invalid at the specified socket
     |level|. In the model, typing prevents an invalid flag from being specified in a call
     to [[getsocknopt()]].

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)

   (!h ts tid d
     fd f fid sid ff sf
     SS MM.

   getsocknopt_1 /* rp_all, fast succeed (*: Successfully retrieve value of a numeric socket flag :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getsocknopt(fd,f)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (int_of_num (sf.n(f)))),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sf = (h.socks ' sid).sf /\
     (windows_arch h.arch ==> f NOTIN {SO_RCVLOWAT; SO_SNDLOWAT})


   (*:

    @description

    Consider the socket [[sid]], referenced by [[fd]], with socket flags [[sf]]. From thread
    [[tid]], which is in the [[Run]] state, a [[getsocknopt(fd,f)]] call is made. [[f]] is a numeric
    socket flag whose value is to be returned. The call succeeds, returning [[sf.n(f)]], the numeric
    value of flag [[f]] for socket [[sid]].

    A [[Lh_call(tid,getsocknopt(fd,f))]] transition is made, leaving the thread state [[Ret (OK
    (int_of_num (sf.n(f))))]].

    @variation WinXP

    The flag [[f]] is not [[SO_RCVLOWAT]] or [[SO_SNDLOWAT]].

    @internal

    Read the named numeric flag on the socket description named.

    Models POSIX's |getsockopt()| for numeric flags.

    Typing ensures [[f]] is valid and is a numeric flag.

   :*)
   )

/\

   (!h ts tid d fd f
     SS MM.

   getsocknopt_4 /* rp_all, fast fail (*: Fail with [[ENOPROTOOPT]]: value of [[SO_RCVLOWAT]] and [[SO_SNDLOWAT]] not retrievable :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getsocknopt(fd,f)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOPROTOOPT),sched_timer)) |>,SS,MM)

   <==

     windows_arch h.arch /\
     f IN {SO_RCVLOWAT; SO_SNDLOWAT}


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[getsocknopt(fd,f)]] call is made where
    [[fd]] is a file descriptor. [[f]] is a numeric socket flag: either [[SO_RCVLOWAT]] or
    [[SO_SNDLOWAT]], both flags whose value is non-retrievable. The call fails with an
    [[ENOPROTOOPT]] error.

    A [[Lh_call(tid,getsocknopt(fd,f))]] transition is made, leaving the thread state [[Ret (FAIL ENOPROTOOPT)]].

    @variation FreeBSD

    This rule does not apply.

    @variation Linux

    This rule does not apply.

    @internal

    If the user requests an option that is not retrievable, the error [[ENOPROTOOPT]] is returned.

    This is currently nondeterministic for those options POSIX permits to be nonretrievable.  We
    should sharpen this up.

    POSIX: "shall fail...".

    :*)

   )

/\

(*:

@section [[getsocktopt]] ALL [[getsocktopt()]]
 \[ <[getsocktopt: (fd * socktflag) -> (int * int) option]> \]

  A call to [[getsocktopt(fd,flag)]] returns the value of one of the socket's time-option flags.

  The [[fd]] argument is a file descriptor referring to the socket to retrieve a flag's value
  from. The [[flag]] argument is a time option socket flag. Possible flags are:

  \begin{itemize}
    \item [[SO_RCVTIMEO]] Reports the timeout value for input operations.

    \item [[SO_SNDTIMEO]] Reports the timeout value specifying the amount of time that an output
     function blocks because flow control prevents data from being sent.
  \end{itemize}

  The return value of the [[getsocktopt()]] call is the time-value of the specified [[flag]]. A
  return value of [[NONE]] means the timeout is disabled. A return value of [[SOME(s,ns)]] means the
  timeout value is [[s]] seconds and [[ns]] nano-seconds.

@errors

  A call to [[getsocktopt()]] can fail with the errors below, in which case the corresponding
  exception is raised:

  @error [[ENOPROTOOPT]] The specified flag is not supported by the protocol.
  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  [[getsocktopt_1]]; [[return_1]]

@api

  [[getsocktopt()]] is Posix |getsockopt()| for time-valued socket options.

  \begin{tabular}{ll}
     Posix:   & |int getsockopt(int socket, int level, int option_name,|\\
              & |               void *restrict option_value, | \\
              & |               socklen_t *restrict option_len);| \\
     FreeBSD: & |int getsockopt(int s, int level, int optname, | \\
              & |               void *optval, socklen_t *optlen); | \\
     Linux:   & |int getsockopt(int  s, int level, int optname, | \\
              & |               void *optval, socklen_t *optlen);| \\
     WinXP:   & |int getsockopt(SOCKET s,int level,int optname, | \\
              & |               char* optval, int* optlen); | \\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |socket| is the file descriptor of the socket to set the option on, corresponding
     to the [[fd]] argument of the model [[getsocktopt()]].

    \item |level| is the protocol level at which the option resides: |SOL_SOCKET|
     for the socket level options, and |option_name| is the option to be retrieved. These
     two correspond to the [[flag]] argument to the model [[getsocktopt()]] where the possible
     values of |option_name| are limited to [[SO_RCVTIMEO]] and [[SO_SNDTIMEO]].

    \item |option_value| is a pointer to a location of size |option_len| to store
     the value retrieved by |getsockopt()|. They correspond to the [[(int * int) option]]
     return type of the model [[getsocktopt()]].

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item |EFAULT| signifies the pointer passed as |option_value| was
     inaccessible. On WinXP, the error |WSAEFAULT| may also signify that the
     |optlen| parameter was too small.

    \item |EINVAL| signifies the |option_name| was invalid at the specified socket
     |level|. In the model, typing prevents an invalid flag from being specified in a call
     to [[getsocktopt()]].

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)

   (!h ts tid d
     fd f fid sid ff sf t
     SS MM.

   getsocktopt_1 /* rp_all, fast succeed (*: Successfully retrieve value of time-option socket flag :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getsocktopt(fd,f)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK t),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sf = (h.socks ' sid).sf /\
     t = tltimeopt_of_time (sf.t(f)) /\
     ~(windows_arch h.arch /\ proto_of (h.socks ' sid).pr = PROTO_UDP /\
       f = SO_LINGER)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[getsocktopt(fd,f)]] call is made. [[fd]]
    is a file descriptor referring to the socket [[sid]] which has socket flags [[sf]], and [[f]] is
    a time-option flag. The call succeeds, returning [[OK (t)]] where [[t]] is the value of the
    socket's flag [[f]].

    A [[Lh_call(tid,getsocktopt(fd,f))]] transition is made, leaving the thread state [[Ret (OK
    t)]].

    @variation WinXP

    As above but in addition if [[fd]] refers to a UDP socket then the flag is not [[SO_LINGER]].

    @modeldetails

    The return type is [[(int * int) option]], but the type of a time-option socket flag is
    [[time]]. The auxiliary function [[tltimeopt_of_time]] is used to do the conversion.

    @internal

    Read the named time-option flag on the socket description named.

    Models POSIX's |getsockopt()| for time-option flags.

    Typing ensures [[f]] is valid and is a time-option flag.

    Note that the returned type is an optional pair of integers, as defined by
    [[tltimeopt_of_time]]: absence denotes infinity, pair is seconds and nanoseconds respectively.

    :*)
   )

/\

   (!h ts tid d fd f sid ff fid
     SS MM.

   getsocktopt_4 /* rp_all, fast fail (*: Fail with [[ENOPROTOOPT]]: on WinXP [[SO_LINGER]] not retrievable for UDP sockets :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,getsocktopt(fd,f)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOPROTOOPT),sched_timer)) |>,SS,MM)

   <==

     windows_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     proto_of (h.socks ' sid).pr = PROTO_UDP /\
     f = SO_LINGER


   (*:

    @description

    On WinXP, from thread [[tid]] which is in the [[Run]] state, a [[getsocktopt(fd,f)]] call is
    made. [[fd]] is a file descriptor referring to a UDP socket [[sid]] and [[f]] is the socket flag
    [[SO_LINGER]].  The flag [[f]] is not retrievable so the call fails with an [[ENOPROTOOPT]]
    error.

    A [[Lh_call(tid,getsocktopt(fd,f))]] transition is made, leaving the thread state [[Ret
    (ENOPROTOOPT)]].

    @variation FreeBSD

    This rule does not apply.

    @variation Linux

    This rule does not apply.

    @internal

    If the user requests an option that is not retrievable, the error [[ENOPROTOOPT]] is returned.

    WinXP does not support [[SO_LINGER]] for UDP sockets. BSD/Linux support set/getting
    [[SO_LINGER]] but do not use it.

    This is currently nondeterministic for those options POSIX permits to be nonretrievable.  We
    should sharpen this up.

    POSIX: "shall fail...".

    :*)
   )

/\

(*:

@section [[listen]] TCP [[listen()]]
  \[ <[listen: fd * int -> unit ]> \]

   A call to [[listen(fd,n)]] puts a TCP socket that is in the [[CLOSED]] state into the [[LISTEN]]
   state, making it a passive socket, so that incoming connections for the socket will be accepted
   by the host and placed on its listen queue.  Here [[fd]] is a file descriptor referring to the
   socket to put into the [[LISTEN]] state and [[n]] is the \textit{backlog} used to calculate the
   maximum lengths of the two components of the socket's listen queue: its pending connections
   queue, [[lis.q0]], and its complete connection queue, [[lis.q]].  The details of this calculation
   very between architectures.  The maximum useful value of [[n]] is [[SOMAXCONN]]: if [[n]] is
   greater than this then it will be truncated without generating an error. The minimum value of
   [[n]] is [[0]]: if it a negative integer then it will be set to [[0]].

   Once a socket is in the [[LISTEN]] state, [[listen()]] can be called again to change the backlog
   value.

 @errors

   A call to [[listen()]] can fail with the errors below, in which case the corresponding exception
   is raised:

   @error [[EADDRINUSE]] Another socket is listening on this local port.

   @error [[EINVAL]] On FreeBSD the socket has been shutdown for writing; on Linux the socket is not
   in the [[CLOSED]] or [[LISTEN]] state; or on WinXP the socket is not bound,

   @error [[EISCONN]] On WinXP the socket is already connected: it is not in the [[CLOSED]] or
   [[LISTEN]] state.

   @error [[EOPNOTSUPP]] The [[listen()]] operation is not supported for UDP.

   @errorinclude [[misc]] [[EBADF]]
   @errorinclude [[misc]] [[ENOTSOCK]]

 @commoncases

   A TCP socket is created, has its local address and port set by [[bind()]], and then is put into
   the [[LISTEN]] state which can accept new incoming connections: [[socket_1]]; [[return_1]];
   [[bind_1]] [[return_1]]; [[listen_1]]; [[return_1]]; $\dots$

 @api

   \begin{tabular}{ll}
     Posix:   & |int listen(int socket, int backlog);| \\
     FreeBSD: & |int listen(int s, int backlog);| \\
     Linux:   & |int listen(int s, int backlog);| \\
     WinXP:   & |int listen(SOCKET s, int backlog);| \\
   \end{tabular}

   In the Posix interface:

   \begin{itemize}

     \item |socket| is a file descriptor referring to the socket to put into the [[LISTEN]]
      state, corresponding to the [[fd]] argument of the model [[listen()]].

     \item |backlog| is an |int| on which the maximum permitted length of the
      socket's listen queue depends. It corresponds to the [[n]] argument of the model [[listen()]].

     \item the returned |int| is either |0| to indicate success or |-1| to
      indicate an error, in which case the error code is in |errno|.  On WinXP an error is
      indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual
      error code available through a call to |WSAGetLastError()|.

    \end{itemize}

 @modeldetails

   The following errors are not modelled:

   \begin{itemize}

     \item In Posix, [[EACCES]] may be returned if the calling process does not have the appropriate
      privileges. This is not modelled here.

     \item In Posix, [[EDESTADDRREQ]] shall be returned if the socket is not bound to a local
      address and the protocol does not support listening on an unbound socket. WinXP returns an
      [[EINVAL]] error in this case; FreeBSD and Linux autobind the socket if [[listen()]] is called
      on an unbound socket.

     \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
      Windows Sockets 1.1 call is in progress, or the service provider is still processing a
      callback function". This is not modelled here.

   \end{itemize}

:*)

   (!h ts socks listen0 tid d
     fd n fid ff sid sf es cb lis cantrcvmore
     is1 ps1 p1 is2 ps2 bound SS MM.

   listen_1 /* rp_tcp, fast succeed (*: Successfully put socket in [[LISTEN]] state :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,F,cantrcvmore,
				   TCP_Sock(CLOSED,cb,NONE)))] ;
               listen := listen0 |>,
     SS,MM)
   -- Lh_call (tid,listen(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,SOME p1,is2,ps2,es,F,cantrcvmore,
                              TCP_Sock(LISTEN,cb,SOME lis)))] ;
               listen := sid :: listen0;
               bound := bound |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     (bsd_arch h.arch \/ cantrcvmore = F) /\
     ~(windows_arch h.arch /\ IS_NONE ps1) /\
     (bsd_arch h.arch ==> T) /\
     p1 IN autobind(ps1,PROTO_TCP,h,socks \\ sid) /\
     (if ps1 = NONE then bound = sid::h.bound else bound = h.bound) /\
     lis = <| q0 := [];
              q  := [];
              qlimit := n |>


   (*:

  @description

   From thread [[tid]], which is currently in the [[Run]] state, a [[listen(fd,n)]] call is
   made. [[fd]] is a file descriptor referring to a TCP socket identified by [[sid]] which is not
   shutdown for writing, is in the [[CLOSED]] state, has an empty send and receive queue, and does
   not have its send or receive urgent pointers set. The host's list of listening sockets is
   [[listen0]]. Either the socket is bound to a local port [[p1]], or it can be autobound to a local
   port [[p1]].

   The call succeeds: a [[Lh_call(tid,listen(fd,n))]] transition is made, leaving the thread in
   state [[Ret (OK())]]. The socket is put in the [[LISTEN]] state, with an empty listen queue,
   [[lis]], with [[n]] as its backlog. [[sid]] is added to the host's list of listening sockets,
   [[listen := sid::listen0]], and if autobinding occurred, it is also added to the host's list of
   bound sockets, [[h.bound]], to create a new list [[bound]].

   @variation FreeBSD

   The [[bsd_cantconnect]] flag in the control block must not be set to [[T]] (from an earlier
   connection establishment attempt).

   @variation WinXP

   As above, except that the socket must be bound to a local port [[p1]]. If it is not bound then
   autobinding will not occur: the call will fail with an [[EINVAL]] error. See also {@link [[listen_2]]}.

   @internal

   Places the specified socket on [[listen]], the queue of listening sockets, and moves it into
   state [[LISTEN]].  The maximum permitted queue length depends on this parameter, although not
   necessarily directly (see [[accept_incoming_q0]], [[accept_incoming_q]], [[drop_from_q0]]).

   Here we put sockets on the listen queue in order of [[listen()]], rather than in order of
   [[bind()]].  We're not sure which is correct.

   On Windows, it is illegal not to specify the bound port; on other architectures, we autobind one
   if required.

   On BSD, listen() may be called on a socket that is shutdown for reading (but not writing), whereas
   other architectures require cantrcvmore = F.

   On most OSs, the socket must be [[CLOSED]]; BSD incorrectly omits this check. If a connected socket
   enters the [[LISTEN]] state, then it retains its full quad, thus only enabling it to accept
   connections from the same remote IP/port. A connect may occur in the usual way if this is the
   case. Despite having a full quad, and the SS_ISCONNECTED flag set, the socket cannot send any
   data, since BSD checks its actual state (and tries unsuccessfully to call connect()). The other
   behaviour is as expected for a listening socket, except that getpeername() will return successfully.

   :*)
   )


/\

   (!h ts socks listen0 tid d
     fd n fid ff sid sf es cb lis lis'
     is1 ps1 is2 ps2 cantrcvmore
     SS MM.

   listen_1b /* rp_tcp, fast succeed (*: Successfully update backlog value :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,F,cantrcvmore,
                                   TCP_Sock(LISTEN,cb,SOME lis)))] ;
               listen := listen0 |>,
     SS,MM)
   -- Lh_call (tid,listen(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,F,cantrcvmore,
                                   TCP_Sock(LISTEN,cb,SOME lis')))] ;
               listen := sid :: listen0 |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     (bsd_arch h.arch \/ cantrcvmore = F) /\
     lis' = lis with <| qlimit := n |>


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[listen(fd,n)]] call is made. [[fd]]
   refers to a TCP socket identified by [[sid]] which is currently in the [[LISTEN]] state. The host
   has a list of listening sockets, [[listen0]]. The call succeeds.

   A [[Lh_call(tid,listen(fd,n))]] transition is made, leaving the thread state [[Ret
   (OK())]]. The backlog value of the socket's listen queue, [[lis.qlimit]] is updated to be [[n]],
   resulting in a new listen queue [[lis']] for the socket. [[sid]] is added to the head of the
   host's listen queue, [[listen := sid::listen0]].

   @internal

   If [[listen()]] is called on a socket in the [[LISTEN]] state the maximum queue length parameter
   is updated. This does not necessarily alter the maximum queue length directly (see
   [[accept_incoming_q0]], [[accept_incoming_q]], [[drop_from_q0]]).

   TODO: we are unsure what the actual behaviour is of calling [[listen()]] on a listening socket on
   most architectures. We know the call succeeds but it is currently unclear whether the queue
   length parameter is updated or not. Trace checking should help resolve this.

   HISTORY: Is it legal to call [[listen()]] multiple times?  <3E15D94A.D7B7507C@webmaster.com> on
   comp.protocols.tcp-ip suggests that this can be used to alter the size of the backlog queue.  Our
   investigations show this is indeed the case - it's fine.

   :*)
   )


/\

   (!h ts socks tid d
     fd n fid ff sid sf es lis sock sock' tcp_sock
     i1 p1 i2 p2 listen0 cantrcvmore cantsndmore
     SS SS' MM.

   listen_1c /* rp_tcp, fast succeed (*: Successfully put socket in the [[LISTEN]] state from any non-[[{CLOSED;LISTEN}]] state on FreeBSD :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock)];
               listen := listen0 |>,
     SS,MM)
   -- Lh_call (tid,listen(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               socks := socks |++
                        [(sid,sock')];
               listen := sid :: listen0 |>,
     SS',MM)

   <==

     bsd_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sock = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,TCP_PROTO(tcp_sock)) /\
     tcp_sock.st NOTIN {CLOSED; LISTEN} /\
     sock' = sock with <| pr := TCP_PROTO(tcp_sock with <| st := LISTEN; lis := SOME lis |>) |> /\
     destroy (i1,p1,i2,p2) SS SS' /\
     lis = <| q0 := [];
              q  := [];
              qlimit := n |>


   (*:

   @description

   On BSD, calling [[listen()]] always succeeds on a socket regardless of its state: the state of the
   socket is just changed to [[LISTEN]].

   From thread [[tid]], which is in the [[Run]] state, a [[listen(fd,n)]] call is made. [[fd]]
   refers to a TCP socket identified by [[sid]] which is currently in any non-[[{CLOSED;LISTEN}]]
   state. The call succeeds.

   A [[Lh_call(tid,listen(fd,n))]] transition is made, leaving the thread state [[Ret
   (OK())]]. The socket state is updated to [[LISTEN]], with empty listen queues.

   :*)
   )


/\
   (!h ts tid d
     fd n fid ff sid sock
     SS MM.

   listen_2 /* rp_tcp, fast fail (*: Fail with [[EINVAL]] on WinXP: socket not bound to local port :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,listen(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINVAL),sched_timer)) |>,SS,MM)

   <==

     windows_arch h.arch /\  (* this is only an error on Windows *)
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     FAPPLY h.socks sid = sock /\
     proto_of sock.pr = PROTO_TCP /\
     sock.ps1 = NONE


   (*:

   @description

   On WinXP, from thread [[tid]], which is in the [[Run]] state, a [[listen(fd,n)]] call is
   made. [[fd]] refers to a TCP socket [[sock]], identified by [[sid]], which is not bound to a
   local port: [[sock.ps1 = NONE]]. The call fails with an [[EINVAL]] error.

   A [[Lh_call(tid,listen(fd,n))]] transition is made, leaving the thread state [[Ret (FAIL EINVAL)]].

   @variation FreeBSD

   This rule does not apply.

   @variation Linux

   This rule does not apply.

   @internal

   To listen on a socket, on Windows, at least its local port must have been specified.  On other
   architectures, an autobind is performed.

   Worried about the [[CLOSED]] state from [[close_2a]], wrt POSIX saying may EINVAL if "socket has
   been shut down".  We believe this means that if [[shutdown()]] has been called on the socket,
   [[listen()]] should fail with [[EINVAL]].  However, in TCP this does not need a separate case -
   it is visible in the state of the socket, and that is caught by [[listen_3]].

   :*)
   )

/\

   (!h ts tid d
     fd n fid ff sid sock err tcp_sock
     SS MM.

   listen_3 /* rp_tcp, fast fail (*: Fail with [[EINVAL]] on Linux or [[EISCONN]] on WinXP: socket not in [[CLOSED]] or [[LISTEN]] state :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,listen(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     FAPPLY h.socks sid = sock /\
     sock.pr = TCP_PROTO(tcp_sock) /\
     tcp_sock.st NOTIN {CLOSED; LISTEN} /\
     ~(bsd_arch h.arch) /\  (* this is not an error on BSD! *)
     (if windows_arch h.arch then
        err = EISCONN
      else if linux_arch h.arch then
        err = EINVAL
      else
        F)


   (*:

   @description

   From thread [[tid]], which is in the [[Run]] state, a [[listen(fd,n)]] call is made. [[fd]]
   refers to a TCP socket [[sock]], identified by [[sid]], which is not in the [[CLOSED]] or
   [[LISTEN]] state. On Linux the call fails with an [[EINVAL]] error; on WinXP it fails with an
   [[EISCONN]] error.

   A [[Lh_call(tid,listen(fd,n))]] transition is made, leaving the thread state [[Ret (FAIL
   err)]] where [[err]] is one of the above errors.

   @variation FreeBSD

   This rule does not apply: [[listen()]] can be called from any state.

   @variation Linux

   As above: the call fails with an [[EINVAL]] error.

   @variation WinXP

   As above: the call fails with an [[EISCONN]] error.

   @internal

   To listen on a socket, that socket must be in the [[CLOSED]] state or the [[LISTEN]] state (the
   latter permits alteration of the backlog value).

   Note that BSD gets this wrong, and you can call [[listen()]] from any state!

   :*)
   )

/\

   (!h ts d fd fid sid ff n tid sock tcp_sock p1
     SS MM.

   listen_4 /* rp_tcp, fast fail (*: Fail with [[EADDRINUSE]] on Linux: another socket already listening on local port :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,listen(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EADDRINUSE), sched_timer)) |>,SS,MM)

   <==

     linux_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     h.socks ' sid = sock /\
     sock.pr = TCP_PROTO(tcp_sock) /\
     tcp_sock.st = CLOSED /\
     sock.ps1 = SOME p1 /\
     (?sid' sock' tcp_sock'. h.socks ' sid' = sock' /\ sock'.pr = TCP_PROTO(tcp_sock') /\
      	                     tcp_sock'.st = LISTEN /\ sock'.ps1 = sock.ps1 /\
                             ~(?i1 i1'. i1 <> i1' /\ sock.is1 = SOME i1 /\ sock'.is1 = SOME i1'))


    (*:

     @description

     On Linux, from thread [[tid]], which is in the [[Run]] state, a [[listen(fd,n)]] call is
     made. [[fd]] refers to a TCP socket [[sock]], identified by [[sid]], in state [[CLOSED]] and
     bound to local port [[p1]]. There is another TCP socket, [[sock']], in the host's finite map of
     sockets, [[h.socks]] that is also bound to local port [[p1]], and is in the [[LISTEN]]
     state. The two sockets, [[sock]] and [[sock']], are not bound to different IP addresses: either
     they are both bound to the same IP address, one is bound to an IP address and the other is not
     bound to an IP address, or neither is bound to an IP address. The call fails with an
     [[EADDRINUSE]] error.

     A [[Lh_call(tid,listen(fd,n))]] transition is made, leaving the thread state [[Ret (FAIL
     EADDRINUSE)]].

     @variation FreeBSD

     This rule does not apply.

     @variation WinXP

     This rule does not apply.

     @internal

     Calling [[listen()]] on a socket bound to a port [[p1]] when there is already another socket
     listening on port [[p1]] is an [[EADDRINUSE]] error on Linux, unless the IP addresses are
     different.

    :*)

  )

/\

   (!h ts d socks sid sock tcp_sock fd n fid ff tid cantsndmore st
     SS MM.

   listen_5 /* rp_tcp, fast fail (*: Fail with [[EINVAL]] on BSD: socket shutdown for writing or [[bsd_cantconnect]] flag set :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
	                [(sid,sock with <| cantsndmore := cantsndmore; pr := TCP_PROTO(tcp_sock with <| st := st |>) |>)] |>,
     SS,MM)
   -- Lh_call (tid,listen(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINVAL), sched_timer));
               socks := socks |++
                        [(sid,sock with <| cantsndmore := cantsndmore; pr := TCP_PROTO(tcp_sock with <| st := st |>) |>)] |>,
     SS,MM)

   <==

     bsd_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     st IN {CLOSED; LISTEN} /\ (* fails the same if socket was listening + other conditions*)
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     (cantsndmore = T \/ T )


   (*:

    @description

    On FreeBSD, from thread [[tid]], which is in the [[Run]] state, a [[listen(fd,n)]] call is
    made. [[fd]] refers to a TCP socket [[sock]], identified by [[sid]], which is in the [[CLOSED]]
    or [[LISTEN]] state. The socket is either shutdown for writing or has its [[bsd_cantconnect]]
    flag set due to an earlier connection-establishment attempt. The call fails with an [[EINVAL]] error.

    A [[Lh_call(tid,listen(fd,n))]] transition is made, leaving the thread state [[Ret (FAIL
    EINVAL)]].

    @variation Linux

    This rule does not apply.

    @variation WinXP

    This rule does not apply.

    @internal

    Calling [[listen()]] on a socket that has been shutdown for writing on FreeBSD is an [[EINVAL]]
    error.

    MS: this rule is not a load of rubbish - you can call shutdown() on a closed socket under BSD, which
    sets cantsndmore, but does nothing else. listen() returns EINVAL.

   :*)

  )


/\

   (!h ts d fd fid sid ff n tid
     SS MM.

   listen_7 /* rp_udp, fast fail (*: Fail with [[EOPNOTSUPP]]: [[listen()]] called on UDP socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,listen(fd,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EOPNOTSUPP),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     proto_of (h.socks ' sid).pr = PROTO_UDP


   (*:

    @description

    Consider a UDP socket [[sid]], referenced by [[fd]]. From thread [[tid]], which is in the
    [[Run]] state, a [[listen(fd,n)]] call is made. The call fails with an [[EOPNOTSUPP]] error.

    A [[Lh_call(tid,listen(fd,n))]] transition is made, leaving the thread state [[Ret (FAIL
    EOPNOTSUPP)]].

    Calling [[listen()]] on a socket for a connectionless protocol (such as UDP) is meaningless
    and is thus an unsupported ([[EOPNOTSUPP]]) operation.

    @internal

    Calling [[listen]] on a UDP socket does not make any sense as the operation is not supported.

   :*)

   )

/\ (*

(*:

@section [[pselect]] ALL [[pselect()]]
  \[ <[pselect: (fd list * fd list * fd list * (int * int) option * signal list option) -> (fd list * (fd list * fd list))]> \]

  A call to [[pselect(readfds,writefds,exceptfds,timeout,sigmask)]] waits for one of the file
  descriptors in [[readfds]] to be ready for reading, [[writefds]] to be ready for writing,
  [[exceptfds]] to have a pending error, or for [[timeout]] to expire.

  The [[readfds]] argument is a set of file descriptors to be checked for being ready to read. Broadly, a
  file descriptor [[fd]] is ready for reading if a [[recv(fd,_,_)]] call on the socket would not
  block, i.e.~if there is data present or a pending error.

  The [[writefds]] argument is a set of file descriptors to be checked for being ready to write. Broadly, a
  file descriptor [[fd]] is ready for writing if a [[send(fd,_,_,_)]] call would not block.

  The [[exceptfds]] argument is a set of file descriptors to be checked for exception conditions
  pending. A file descriptor [[fd]] has an exception condition pending if there exists out-of-band
  data for the socket it refers to or the socket is still at the out-of-band mark.

  The [[timeout]] argument specifies how long the [[pselect()]] call should block waiting for a file
  descriptor to be ready. If [[timeout=NONE]] then the call should block until one of the file
  descriptors in the [[readfds]], [[writefds]], or [[exceptfds]] becomes ready. If
  [[timeout=SOME(s,ns)]] then the call should block for at most [[s]] seconds and [[ns]]
  nanoseconds. However, system activity can lengthen the timeout interval by an indeterminate
  amount.

  The [[sigmask]] argument is used to set the signal mask, the set of signals to be blocked. In the
  implementations, if [[sigmask=SOME(siglist)]] then [[pselect()]] first replaces the current signal
  mask by [[siglist]] before proceeding with the call, and then restores the original signal mask
  upon return.  This specification does not model the dynamic behaviour of signals, however, and so
  we specify the behaviour of [[pselect()]] only for an empty signal mask.

  A return value of [[(readfds',(writefds',exceptfds'))]] from a [[pselect()]] call signifies that:
  the file descriptors in [[readfds']] are ready for reading; the file descriptors in [[writefds']]
  are reading for writing; and the file descriptors in [[exceptfds']] have exceptional conditions
  pending.

  If a [[pselect([],[],[],Some(s,ns),sigmask)]] call is made then the call will block for [[s]]
  seconds and [[ns]] nano-seconds or until a signal occurs.

  To perform a poll, a [[pselect(readfds,writefds,exceptfds,Some(0,0),sigmask)]] call should be
  made.

@errors

  A call to [[pselect()]] can fail with the errors below, in which case the corresponding exception
  is raised:

  @error [[EBADF]] One or more of the file descriptors in a set is not a valid file descriptor.

  @error [[EINVAL]] Time-out not well-formed, file descriptor out of range, or on WinXP all file descriptor sets are empty.

  @error [[ENOTSOCK]] One or more of the file descriptors in a set is not a valid socket.

  @errorinclude [[misc]] [[EINTR]]

@commoncases

\

[[pselect()]] is called and returns immediately:
  [[pselect_1]]; [[return_1]]

[[pselect()]] blocks and then times out before any of the file descriptors become ready:
  [[pselect_2]]; [[pselect_3]]; [[return_1]]

[[pselect()]] blocks, TCP data is received from the network and processed, making a file descriptor ready for reading, and then [[pselect()]] returns:
  [[pselect_1]]; [[deliver_in_99]]; [[deliver_in_3]]; [[pselect_2]]; [[return_1]]

[[pselect()]] blocks, UDP data is received from the network and processed, making a file descriptor ready for reading, and then [[pselect()]] returns:
  [[pselect_1]]; [[deliver_in_99]]; [[deliver_in_udp_1]]; [[pselect_2]]; [[return_1]]

[[pselect()]] blocks, TCP data is sent to the network, an acknowledgement is received and processed, making a file descriptor ready for writing, and then [[pselect()]] returns:
  [[pselect_1]]; [[deliver_out_1]]; [[deliver_out_99]]; [[deliver_in_99]]; [[deliver_in_3]];
  [[pselect_2]]; [[return_1]]

@api

  \begin{tabular}{ll}
    Posix:   &|int pselect(int nfds, fd_set *restrict readfds,| \\
             &|            fd_set *restrict writefds, fd_set *restrict errorfds,| \\
             &|            const struct timespec *restrict timeout,| \\
             &|            const sigset_t *restrict sigmask);| \\
    FreeBSD: &|int select(int nfds, fd_set *readfds, fd_set *writefds,| \\
             &|           fd_set *exceptfds, struct timeval *timeout);| \\
    Linux:   &|int pselect(int n, fd_set *readfds, fd_set *writefds,|\\
             &|            fd_set *exceptfds, const struct timespec *timeout,| \\
             &|            const sigset_t *sigmask);| \\
    WinXP:   &|int select(int nfds, fd_set* readfds, fd_set* writefds,| \\
             &|           fd_set* exceptfds, const struct timeval* timeout);|\\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |nfds| specifies the range of file descriptors to be tested. The first
     |nfds| file descriptors shall be checked in each set. This is not necessary in the
     model [[pselect()]] as the file descriptor sets are implemented as a [[list]] rather than the
     integer arrays in Posix |pselect()|.

    \item |readfds| on input specifies the file descriptors to be checked for being ready to
     read, corresponding to the [[readfds]] argument of the model [[pselect()]]. On output
     |readfds| indicates which of the file descriptors specified on input are ready to read,
     corresponding to the first [[fd list]] in the return type of the model [[pselect()]]. An
     |fd_set| is an integer array, where each bit of each integer corresponds to a file
     descriptor. If that bit is set then that file descriptor should be
     checked. |FD_CLR()|, |FD_ISSET()|, |FD_SET()|, and
     |FD_ZERO()| are provided to set bits in an |fd_set|.

    \item |writefds| on input specifies the file descriptors to be checked for being ready
     to write, corresponding to the [[writefds]] argument of the model [[pselect()]]. On output
     |writefds| indicates which of the file descriptors specified on input are ready to
     write, corresponding to the second [[fd list]] in the return type of the model [[pselect()]].

    \item |errorfds| on input specifies the file descriptors to be checked for pending error
     conditions, corresponding to the [[exceptfds]] argument of the model [[pselect()]]. On output
     |exceptfds| indicated which of the file descriptors specified on input have pending
     error conditions, corresponding to the third [[fd list]] in the return type of the model
     [[pselect()]].

    \item |timeout| specifies how long the |pselect()| call shall block before
     timing out, corresponding to the [[timeout]] argument of the model [[pselect()]]. If the
     |timeout| parameter is a null pointer this corresponds to [[timeout=NONE]]; if the
     |timeout| parameter is not a null pointer, then its two fields,
     |timeout.tv_sec| (the number of seconds) and |timeout.tv_nsec| (the number of
     nano-seconds), correspond to [[timeout=SOME(s,ns)]] where [[s]] is the number of seconds, and
     [[ns]] is the number of nano-seconds.

    \item |sigmask| is the signal-mask to be used when examining the file descriptors,
     corresponding to the [[sigmask]] argument of the model [[pselect()]]. If |sigmask| is a
     null pointer then [[sigmask = NONE]] in the model; if |sigmask| is not a null pointer
     then [[sigmask = SOME sigs]] in the model where [[sigs]] is the signal-mask to use.

    \item if the call is successful then the returned |int| is the number of bits set in the
     three |fd_set| arguments: the total number of file descriptors ready for reading,
     writing, or having exceptional conditions pending. Otherwise, the returned |int| is
     |-1| to indicate an error, in which case the error code is in |errno|.  On
     WinXP an error is indicated by a return value of |SOCKET_ERROR|, not |-1|,
     with the actual error code available through a call to |WSAGetLastError()|.

  \end{itemize}

  The Linux interface is similar. On FreeBSD and WinXP there is no |pselect()| call, only a
  |select()| call which is the same as the interface described above, except without the
  |sigmask| argument. The |select()| call corresponds to calling the model
  [[pselect()]] with [[sigmask=NONE]]. Additionally, the |timeout| argument is a pointer to
  a |timeval| structure which has two members |tv_sec| and |tv_usec|,
  specifying the seconds and micro-seconds to block for, rather than seconds and nano-seconds.

  The FreeBSD man page for |select()| warns of the following bug: "Version 2 of the Single
  UNIX Specification ("SUSv2") allows systems to modify the original timeout in place.  Thus, it is
  unwise to assume that the timeout value will be unmodified by the select() call."

@modeldetails

  If the [[pselect()]] call blocks then the thread enters state [[PSelect2(readfds,writefds,exceptfds)]] where:

  \begin{itemize}

  \item [[readfds : fd list]] is the list of file descriptors to be checked for being ready to read.

  \item [[writefds : fd list]] is the list of file descriptors to be checked for being ready to
  write.

  \item [[exceptfds : fd list]] is the list of file descriptors to be checked for pending
  exceptional conditions.

  \end{itemize}

  The following errors are not modelled:

  \begin{itemize}

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)



   (!h ts tid readfds writefds exceptfds timeout sigmask readfds' writefds' exceptfds' d
     readfds'' writefds'' exceptfds'' badreadfds badwritefds badexceptfds
     SS MM.

   pselect_1 /* rp_all, fast succeed (*: One or more file descriptors immediately ready, or no timeout set :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,pselect(readfds,writefds,exceptfds,timeout,sigmask)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK(readfds'',writefds'',exceptfds'')), sched_timer)) |>,SS,MM)

   <==

     (tltimeopt_wf timeout \/ windows_arch h.arch)/\
     sigmask = NONE /\
     ~(?fd n. (fd IN' readfds \/ fd IN' writefds \/ fd IN' exceptfds) /\
              if windows_arch h.arch
	      then n = (MAX (LENGTH readfds) (MAX (LENGTH writefds) (LENGTH exceptfds))) /\
                   n >= (FD_SETSIZE h.arch)
	      else
              fd = FD n /\
	      n >= FD_SETSIZE h.arch) /\
     badreadfds = FILTER (\fd. fd NOTIN FDOM  h.fds) readfds /\
     badwritefds = FILTER (\fd. fd NOTIN FDOM h.fds) writefds /\
     badexceptfds = FILTER (\fd. fd NOTIN FDOM h.fds) exceptfds /\
     (bsd_arch h.arch \/ (* BSD bug - allows bad fds to return in pselect output, and not cause call to fail *)
      (badreadfds = [] /\ badwritefds = [] /\ badexceptfds = [])) /\
      ~(?fd.   (fd IN' readfds \/ fd IN' writefds \/ fd IN' exceptfds) /\
               fd NOTIN FDOM h.fds) /\
     readfds' = FILTER (\fd. ?fid ff sid sock.
       fd IN FDOM h.fds /\
       fid = h.fds ' fd /\
       FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
       sock = h.socks ' sid /\
       T IN soreadable h.arch sock SS) readfds /\
     writefds' = FILTER (\fd. ?fid ff sid sock.
       fd IN FDOM h.fds /\
       fid = h.fds ' fd /\
       FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
       sock = h.socks ' sid /\
       T IN sowriteable h.arch sock SS) writefds /\
     exceptfds' = FILTER (\fd. ?fid ff sid sock.
       fd IN FDOM h.fds /\
       fid = h.fds ' fd /\
       FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
       sock = h.socks ' sid /\
       soexceptional h.arch sock) exceptfds /\
     (windows_arch h.arch ==> readfds <> [] /\ writefds <> [] /\ exceptfds <> []) /\
     (readfds' <> [] \/ writefds' <> [] \/ exceptfds' <> [] \/ timeout=SOME(0,0)) /\
     if windows_arch  h.arch then
	 readfds''=readfds' /\ writefds''=writefds' /\ exceptfds''=exceptfds'
     else
	 readfds'' = INSERT_ORDERED readfds' readfds badreadfds /\
	 writefds'' = INSERT_ORDERED writefds' writefds badwritefds /\
	 exceptfds'' = INSERT_ORDERED exceptfds' exceptfds badexceptfds


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a
    [[pselect(readfds,writefds,exceptfds,timeout,sigmask)]] call is made. The time-out is
    well-formed and no signal mask was set: [[sigmask=NONE]]. All of the file descriptors in the
    sets [[readfds]], [[writefds]], and [[exceptfds]] are greater than the maximum allowed file
    descriptor in a set for the architecure, [[FD_SETSIZE]], and all of them are valid file
    descriptors: they are in the host's finite map of file descriptors, [[h.fds]].

    The call returns, without blocking, three sets: [[readfds'']], [[writefds'']], and
    [[exceptfds'']]. [[readfds'']] is the set of valid file descriptors in [[readfds]] that are
    ready for reading: a blocking [[recv(fd,_,_)]] call would not block; see {@link [[soreadable]]}
    for details. [[writefds'']] is the set of valid file descriptors in [[writefds]] that are ready
    for writing: a blocking [[send(fd,_,_)]] call would not block; see {@link [[sowriteable]]} for
    details. [[exceptfds'']] is the set of valid file descriptors in [[exceptfds]] that have pending
    exceptional conditions; see {@link [[soexceptional]]} for details.

    One of these three sets must be non-empty or else a zero timeout was specified, [[timeout=SOME(0,0)]]. A
    [[Lh_call(tid,pselect(readfds,writefds,exceptfds,timeout,sigmask))]] transition is made, leaving
    the thread state [[Ret (OK(readfds'',writefds'',exceptfds''))]].

    @variation FreeBSD

    Invalid file descriptors (ones not in the host's finite map of file descriptors, [[h.fds]]) may
    be present in the sets [[readfds]], [[writefds]], and [[exceptfds]], and all such file
    descriptors will then be included in the return sets [[readfds'']], [[writefds'']], and
    [[exceptfds'']].

    @variation WinXP

    On WinXP [[FD_SETSIZE]] is the maximum number of file descriptors in a set, so none of the sets
    [[readfds]], [[writefds]], and [[exceptfds]] has more than [[FD_SETSIZE]] members. Additionally,
    all three sets may not be empty.

    The time-out need not be well-formed because one or more file descriptors is immediately ready.


   :*)

   )

/\


   (!h ts tid d
     readfds writefds exceptfds timeout sigmask d'
     SS MM.

   pselect_2 /* rp_all, block (*: Normal case :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,pselect(readfds,writefds,exceptfds,timeout,sigmask)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(PSelect2(readfds,writefds,exceptfds),kern_timer d')) |>,SS,MM)

   <==

     tltimeopt_wf timeout /\
     d' = MIN (time_of_tltimeopt timeout) pselect_timeo_t_max /\
     sigmask = NONE /\
     ~(?fd n. (fd IN' readfds \/ fd IN' writefds \/ fd IN' exceptfds) /\
              if windows_arch h.arch
	      then n = MAX (LENGTH readfds) (MAX (LENGTH writefds) (LENGTH exceptfds)) /\
                   n >= FD_SETSIZE h.arch
	      else
              fd = FD n /\
	      n >= FD_SETSIZE h.arch) /\
     ~(?fd.   (fd IN' readfds \/ fd IN' writefds \/ fd IN' exceptfds) /\
              fd NOTIN FDOM h.fds) /\
     (windows_arch h.arch ==> readfds <> [] /\ writefds <> [] /\ exceptfds <> [])


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a
    [[pselect(readfds,writefds,exceptfds,timeout,sigmask)]] call is made. The time-out is
    well-formed and no signal mask was set: [[sigmask=NONE]]. All of the file descriptors in the
    sets [[readfds]], [[writefds]], and [[exceptfds]] are greater than the maximum allowed file
    descriptor in a set for the architecure, [[FD_SETSIZE]], and all of them are valid file
    descriptors: they are in the host's finite map of file descriptors, [[h.fds]].

    The call blocks: a [[Lh_call(tid,pselect(readfds,writefds,exceptfds,timeout,sigmask))]]
    transition is made, leaving the thread state [[PSelect2(readfds,writefds,exceptfds)]].

    @variation WinXP

    On WinXP [[FD_SETSIZE]] is the maximum number of file descriptors in a set, so none of the sets
    [[readfds]], [[writefds]], and [[exceptfds]] has more than [[FD_SETSIZE]] members. Additionally,
    all three sets may not be empty.

    @internal

    The user gives three sets of file descriptors to be observed for readability, writeability, and
    exceptional conditions respectively.  The OS will wait until (at least) one of the fds develops
    the state required, or up until the timeout specified.  While waiting, certain signals are
    ignored (??).  We simply check the validity of all the fds given, set a timer, and then block;
    other rules deal with success and failure.

    The POSIX spec describes this in terms like "returns if a call to send() would not block"; but
    that is of course rather ambiguous... how many bytes?  what flags are set? etc.  So we write
    down here exactly what we mean, and then we will prove some lemmas about the relationship
    between the behaviour of select and the behaviour of send() recv() etc.

    [[sigmask]] unimplemented at present.

    What if someone closes an [[fd]] while we're blocked in select?  (I think the close() should be
    an event noticed by the select()).

   :*)
   )

/\

   (!h ts tid d
     readfds writefds exceptfds readfds' writefds' exceptfds' writefds'' readfds'' exceptfds''
     badreadfds badwritefds badexceptfds
     SS MM.

   pselect_3 /* rp_all, slow nonurgent succeed (*: Something becomes ready or pselect times out :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(PSelect2(readfds,writefds,exceptfds),d)) |>,SS,MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (readfds'',writefds'',exceptfds'')),sched_timer)) |>,SS,MM)

   <==

     readfds' = FILTER (\fd. ?fid ff sid sock.
       fd IN FDOM h.fds /\
       fid = h.fds ' fd /\
       FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
       sock = h.socks ' sid /\
       T IN soreadable h.arch sock SS) readfds /\
     writefds' = FILTER (\fd. ?fid ff sid sock.
       fd IN FDOM h.fds /\
       fid = h.fds ' fd /\
       FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
       sock = h.socks ' sid /\
       T IN sowriteable h.arch sock SS) writefds /\
     exceptfds' = FILTER (\fd. ?fid ff sid sock.
       fd IN FDOM h.fds /\
       fid = h.fds ' fd /\
       FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
       sock = h.socks ' sid /\
       soexceptional h.arch sock) exceptfds /\
     (readfds' <> [] \/ writefds' <> [] \/ exceptfds' <> [] \/ timer_expires d) /\
     badreadfds = FILTER (\fd. fd NOTIN FDOM h.fds) readfds /\
     badwritefds = FILTER (\fd. fd NOTIN FDOM h.fds) writefds /\
     badexceptfds = FILTER (\fd. fd NOTIN FDOM h.fds) exceptfds /\
     if windows_arch h.arch then
	 readfds''=readfds' /\ writefds''=writefds' /\ exceptfds''=exceptfds'
     else
	 readfds'' = INSERT_ORDERED readfds' readfds badreadfds /\
	 writefds'' = INSERT_ORDERED writefds' writefds badwritefds /\
	 exceptfds'' = INSERT_ORDERED exceptfds' exceptfds badexceptfds


   (*:

    @description

    Thread [[tid]] is blocked in state [[PSelect2(readfds,writefds,exceptfds)]]. The call now
    returns three sets: [[readfds'']], [[writefds'']], and [[exceptfds'']]. [[readfds'']] is the set
    of valid file descriptors in [[readfds]] that are ready for reading: a blocking [[recv(fd,_,_)]]
    call would not block; see {@link [[soreadable]]} for details. [[writefds'']] is the set of valid
    file descriptors in [[writefds]] that are ready for writing: a blocking [[send(fd,_,_)]] call
    would not block; see {@link [[sowriteable]]} for details. [[exceptfds'']] is the set of valid
    file descriptors in [[exceptfds]] that have pending exceptional conditions; see {@link
    [[soexceptional]]} for details.

    Either one of these three sets is not empty or the timer [[d]], which was set to the timeout value
    specified when the [[pselect()]] call was made, has expired.

    A [[Lh_tau]] transition is made, leaving the thread state [[Ret
    (OK(readfds'',writefds'',exceptfds''))]].

    @variation FreeBSD

    Invalid file descriptors (ones not in the host's finite map of file descriptors, [[h.fds]]) may
    be present in the sets [[readfds]], [[writefds]], and [[exceptfds]], and all such file
    descriptors will then be included in the return sets [[readfds'']], [[writefds'']], and
    [[exceptfds'']].

    @internal

    If a file descriptor becomes ready, or the timer reaches zero, we return the sets of file
    descriptors that have the desired conditions.

    In order from UNPv1p153.  We should check for sanity against send() and recv().  Amusingly, UNP
    says the "purpose" of the lowat marks is to control when select() returns.

    We believe this implements the required semantics of connect() (by POSIX), that when a connect()
    succeeds, the socket becomes writeable for the purposes of select().  (simply because the socket
    *is* then writeable).

    Note that the available space on the send queue may be negative.

    have not done any semantics for non-socket fds yet.

    URGENT

    From FreeBSD man page: "Version 2 of the Single UNIX Specification ("SUSv2") allows systems to
    modify the original timeout in place.  Thus, it is unwise to assume that the timeout value will
    be unmodified by the select() call." This does happen on FreeBSD.

   :*)

  )

/\

   (!h ts tid d
     readfds writefds exceptfds timeout sigmask
     SS MM.

   pselect_4 /* rp_all, fast fail (*: Fail with [[EINVAL]]: Timeout not well-formed :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,pselect(readfds,writefds,exceptfds,timeout,sigmask)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINVAL),sched_timer)) |>,SS,MM)

   <==

     ~(tltimeopt_wf timeout)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a
    [[pselect(readfds,writefds,exceptfds,timeout,sigmask)]] call is made. The [[timeout]] value is
    not well-formed: [[timeout=SOME(s,ns)]] where either [[s]] is negative; [[ns]] is negative; or
    [[ns > 1000000000]]. The call fails with an [[EINVAL]] error.

    A [[Lh_call(tid,pselect(readfds,writefds,exceptfds,timeout,sigmask))]] transition is made,
    leaving the thread state [[Ret (FAIL EINVAL)]].

    @modeldetails

    Such negative values are not admitted by the POSIX interface type but are by the model interface
    type (with [[(int * int) option]] timeouts), so we check and generate [[EINVAL]] in the wrapper.

    @internal

    If the user specifies an ill-formed timeout, we give [[EINVAL]].

    This is really a thin-layer thing; our thin layer allows negative sec and nsec values even
    though POSIX doens't.  So we make up this error return.

   :*)
   )

/\

   (!h ts tid d
     readfds writefds exceptfds timeout sigmask
     SS MM.

   pselect_5 /* rp_all, fast fail (*: Fail with [[EINVAL]]: File descriptor out of range :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,pselect(readfds,writefds,exceptfds,timeout,sigmask)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINVAL),sched_timer)) |>,SS,MM)

   <==

     (?fd n. (fd IN' readfds \/ fd IN' writefds \/ fd IN' exceptfds) /\
             if windows_arch h.arch
	     then n = MAX (LENGTH readfds) (MAX (LENGTH writefds) (LENGTH exceptfds)) /\
                  n >= FD_SETSIZE h.arch
	     else
             fd = FD n /\
	     n >= FD_SETSIZE h.arch) \/
     (windows_arch h.arch /\ readfds = [] /\ writefds = [] /\ exceptfds = [])


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a
    [[pselect(readfds,writefds,exceptfds,timeout,sigmask)]] call is made. One or more of the file
    descriptors in [[readfds]], [[writefds]], or [[exceptfds]] is greater than the architecure
    dependent [[FD_SETSIZE]], the maximum file descriptor that can be specified in a [[pselect()]]
    call. The call fails with an [[EINVAL]] error.

    A [[Lh_call(tid,pselect(readfds,writefds,exceptfds,timeout,sigmask))]] transition is made,
    leaving the thread state [[Ret (FAIL EINVAL)]].

    @variation WinXP

    On WinXP [[FD_SETSIZE]] is the maximum number of file descriptors in a set, so one of the sets
    [[readfds]], [[writefds]], or [[exceptfds]] has more than [[FD_SETSIZE]] members.

    Also, the call will fail with [[EINVAL]] if the sets [[readfds]], [[writefds]], and
    [[exceptfds]] are all empty.

    @internal

    If the user gives a file descriptor that is too big to fit in the bit-mapped set used internally
    by most implementations, we give an error.

    This roughly corresponds to (in POSIX) the [[n]] parameter being too big.

   :*)
   )

/\

   (!h ts tid d err
     readfds writefds exceptfds timeout sigmask
     SS MM.

   pselect_6 /* rp_all, fast fail (*: Fail with [[EBADF]] or [[ENOTSOCK]]: Bad file descriptor :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,pselect(readfds,writefds,exceptfds,timeout,sigmask)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer)) |>,SS,MM)

   <==

     ~bsd_arch h.arch /\ (* BSD bug - allows bad fds to return in pselect output, and not cause call to fail *)
     (?fd. (fd IN' readfds \/ fd IN' writefds \/ fd IN' exceptfds) /\
           fd NOTIN FDOM h.fds) /\
     (if windows_arch h.arch then err=ENOTSOCK
      else                        err=EBADF)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a
    [[pselect(readfds,writefds,exceptfds,timeout,sigmask)]] call is made. There exists a file
    descriptor [[fd]] in [[readfds]], [[writefds]], or [[exceptfds]] that is not a valid file
    descriptor. The call fails with an [[EBADF]] error on FreeBSD and Linux and an [[ENOTSOCK]] error
    on WinXP.

    A [[Lh_call(tid,pselect(readfds,writefds,exceptfds,timeout,sigmask))]] transition is made,
    leaving the thread state [[Ret (FAIL err)]] where [[err]] is one of the above errors.

    @variation FreeBSD

    This rule does not apply.

    @variation Linux

    As above: the call fails with an [[EBADF]] error.

    @variation WinXP

    As above: the call fails with an [[ENOTSOCK]] error.

    @internal

    If one of the file descriptors given does not correspond to a valid open file description, we
    return an error.

   :*)
   )

/\ *)

(*:

@section [[tcp_recv]] TCP [[recv()]]
 \[ <[recv: fd * int * msgbflag list -> (string * ((ip * port) * bool) option) ]> \]

  A call to [[recv(fd,n,opts)]] reads data from a socket's receive queue.  This section describes
  the behaviour for TCP sockets.
  Here
  [[fd]] is a file descriptor referring to a TCP socket to read data from,
  [[n]] is the number of bytes of data to read, and
  [[opts]] is a list of message flags. Possible flags are:

  \begin{itemize}

  \item [[MSG_DONTWAIT]]: Do not block if there is no data available.

  \item [[MSG_OOB]]: Return out-of-band data.

  \item [[MSG_PEEK]]: Read data but do not remove it from the socket's receive queue.

  \item [[MSG_WAITALL]]: Block until all [[n]] bytes of data are available.

  \end{itemize}

  The returned [[string]] is the data read from the socket's receive queue. The [[((ip * port) *
  bool) option]] is always returned as [[NONE]] for a TCP socket.

  In order to receive data, a TCP socket must be connected to a peer; otherwise, the [[recv()]] call
  will fail with an [[ENOTCONN]] error.  If the socket has a pending error then the [[recv()]] call
  will fail with this error even if there is data available.

  If there is no data available and non-blocking behaviour is not enabled (the socket's
  [[O_NONBLOCK]] flag is not set and the [[MSG_DONTWAIT]] flag was not used) then the [[recv()]] call
  will block until data arrives or an error occurs. If non-blocking behaviour is enabled and there is no
  data or error then the call will fail with an [[EAGAIN]] error.

  The [[MSG_OOB]] flag can be set in order to receive out-of-band data; for this,
the socket's [[SO_OOBINLINE]] cannot be set (i.e.~out-of-band data must not be being returned inline).

@errors

  A call to [[recv()]] can fail with the errors below, in which case the corresponding exception
  is raised:

  @error [[EAGAIN]] Non-blocking [[recv()]] call made and no data available; or out-of-band data
  requested and none is available.

  @error [[EINVAL]] Out-of-band data requested and [[SO_OOBINLINE]] flag set or the out-of-band
  data has already been read.

  @error [[ENOTCONN]] Socket not connected.

  @errorinclude [[misc]] [[ENOTSOCK]]
  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[EINTR]]
  @errorinclude [[misc]] [[ENOBUFS]]
  @errorinclude [[misc]] [[ENOMEM]]

@commoncases

  A TCP socket is created and then connected to a peer; a [[recv()]] call is made to receive data
  from that peer: [[socket_1]]; [[return_1]]; [[connect_1]]; [[return_1]]; [[recv_1]]; $\dots $

@api

  \begin{tabular}{ll}
    Posix:  &  |ssize_t recv(int socket, void *buffer, size_t length, int flags); | \\
    FreeBSD:&  |ssize_t recv(int s, void *buf, size_t len, int flags);| \\
    Linux:  &  |int recv(int s, void *buf, size_t len, int flags);| \\
    WinXP:  &  |int recv(SOCKET s, char* buf, int len, int flags);| \\
  \end{tabular}\\

  In the Posix interface:

  \begin{itemize}

    \item |socket| is the file descriptor of the socket to receive from, corresponding to
     the [[fd]] argument of the model [[recv()]].

    \item |buffer| is a pointer to a buffer to place the received data in, which upon return
     contains the data received on the socket. This corresponds to the [[string]] return value of
     the model [[recv()]].

    \item |length| is the amount of data to be read from the socket, corresponding to the [[int]]
     argument of the model [[recv()]]; it should be at most the length of |buffer|.

    \item |flags| is a disjunction of the message flags that are set for the call, corresponding to
     the [[msgbflag]] [[list]] argument of the model [[recv()]].

    \item the returned |ssize_t| is either non-negative, in which case it is the the amount
     of data that was received by the socket, or it is |-1| to indicate an error, in which
     case the error code is in |errno|. On WinXP an error is indicated by a return value of
     |SOCKET_ERROR|, not |-1|, with the actual error code available through a
     call to |WSAGetLastError()|.

  \end{itemize}

  The FreeBSD, Linux and WinXP interfaces are similar modulo argument renaming, except where
  noted above.

  There are other functions used to receive data on a socket. |recvfrom()| is similar to
  |recv()| except it returns the source address of the data; this is used for UDP but is not
  necessary for TCP as the source address will always be the peer the socket has connected
  to. |recvmsg()|, another input function, is a more general form of |recv()|.


@modeldetails

  If the call blocks then the thread enters state [[Recv2(sid,n,opts)]] where:

  \begin{itemize}

    \item [[sid : sid]] is the identifier of the socket that the [[recv()]] call was made on,

    \item [[n : num]] is the number of bytes to be read, and

    \item [[opts : msgbflag list]] is the list of message flags.

  \end{itemize}

  The following errors are not modelled:

  \begin{itemize}

   \item On FreeBSD, Linux, and WinXP, [[EFAULT]] can be returned if the |buffer|
    parameter points to memory not in a valid part of the process address space. This is an artefact
    of the C interface to |ioctl()| that is excluded by the clean interface used in the
    model [[recv()]].

    \item In Posix, |EIO| may be returned to indicated that an I/O error occurred while
    reading from or writing to the file system; this is not modelled here.

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

  The following Linux message flags are not modelled: |MSG_NOSIGNAL|, |MSG_TRUNC|, and
  |MSG_ERRQUEUE|.

:*)

   (* REMARK [[rcvq]] and [[sndq]] should be removed from Spec3 *)
   (!h ts tid d
     fd n0 n opts0 opts fid sid socks ff sf i1 p1 cb st
     i2 p2 cantrcvmore cantsndmore
     str is1 ps1 is2 ps2 es
     flgs peek inline
     SS s s' MM.

   recv_1 /* rp_tcp, fast succeed (*: Successfully return data from the socket without blocking :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,cantsndmore,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s)],MM)
   -- Lh_call (tid,recv(fd,n0,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (IMPLODE str,NONE)),sched_timer));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,cantsndmore,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s')],MM)

   <==

     ((st IN {ESTABLISHED; FIN_WAIT_1; FIN_WAIT_2; CLOSING;
       TIME_WAIT; CLOSE_WAIT; LAST_ACK} /\
       is1 = SOME i1 /\ ps1 = SOME p1 /\ is2=SOME i2 /\ ps2=SOME p2) \/
      (st = CLOSED) ) /\
     n = clip_int_to_num n0 /\
     opts = LIST_TO_SET opts0 /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\

     (*: We return now if we can fill the buffer, or we can reach the low-water mark (usually
         ignored if [[MSG_WAITALL]] is set), or we can reach EOF or the next urgent-message boundary.
         Pending errors are not checked. :*)
     ? rcvq.
     let have_all_data     = (LENGTH rcvq >= n) in (* BSD only compares against SO_RCVLOWAT if buffer contains less data than requested *)
     let have_enough_data  = (LENGTH rcvq >= sf.n(SO_RCVLOWAT)) in
     let partial_data_ok   = (MSG_WAITALL NOTIN opts \/ n > sf.n(SO_RCVBUF) \/
                             (~(bsd_arch h.arch) /\ MSG_PEEK IN opts)) in
     (have_all_data \/ (have_enough_data /\ partial_data_ok) \/ cantrcvmore) /\
     (* NB: pending errors are only checked if we are going to block *)

     str = rcvq /\

     peek = (MSG_PEEK IN opts) /\
     inline = T /\
     read (i1,p1,i2,p2) peek inline (flgs,rcvq) s s' /\
     LENGTH rcvq <= n


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[recv(fd,n0,opts0)]] call is made where
    out-of-band data is not requested. [[fd]] refers to a synchronised TCP socket [[sid]] with
    binding quad [[(SOME i1,SOME p1,SOME i2,SOME p2)]] and no pending error. Alternatively the
    socket is uninitialised and in state [[CLOSED]].

    The call can return immediately because either: (1) there are at least [[n]] bytes of data in
    the socket's receive queue (the [[have_all_data]] case above); (2) the length of the socket's
    receive queue is greater than or equal to the minimum number of bytes for socket [[recv()]]
    operations, [[sf.n(SO_RCVLOWAT)]], and the call does not have to return all [[n]] bytes of data;
    either because (i) the [[MSG_WAITALL]] flag is not set in [[opts0]], (ii) the number of bytes requested
    is greater than the number of bytes in the socket's receive queue, or (iii) on non-FreeBSD
    architectures the [[MSG_PEEK]] flag is set in [[opts0]] (the [[have_enough_data /\
    partial_data_ok]] case above); (3) there is urgent data available in the socket's receive queue
    (the [[urgent_data_ahead]] case above); or (4) the socket has been shutdown for reading.

    The call succeeds, returning a string, [[IMPLODE str]], which is either: (5) the smaller of the first
    [[n]] bytes of the socket's receive queue or its entire receive queue, if the urgent pointer is
    not set or the socket is at the urgent mark; or (6) the smaller of the first [[n]] bytes of the
    the socket's receive queue, the data in its receive queue up to the urgent mark, and its entire
    receive queue, if the urgent mark is set and the socket is not at the urgent mark.

    A [[Lh_call(tid,recv(fd,n0,opts0))]] transition is made leaving the thread state [[Ret
    (OK(IMPLODE str,NONE))]]. If the [[MSG_PEEK]] flag was set in [[opts0]] then the socket's
    receive queue remains unchanged; otherwise, the data [[str]] is removed from the head of the
    socket's receive queue, [[rcvq]], to leave the socket with new receive queue [[rcvq']]. If the
    receive urgent pointer was not set or was set to [[SOME 0]] then it will be set to [[NONE]]; if it
    was set to [[SOME om]] and  [[om]] is less than the length of the returned string then it will be
    set to [[SOME 0]] (because the returned string was the data in the receive queue up to the
    urgent mark); otherwise it will be set to [[SOME(om-LENGTH str)]].

    @modeldetails

    The amount of data requested, [[n0]], is clipped to a natural number from an integer, using
    [[clip_int_to_num]]. POSIX specifies an unsigned type for [[n0]] and this is one possible model
    thereof.

    The [[opts0]] argument to [[recv()]] is of type [[msgbflag list]], but it is converted to a set,
    [[opts]], using [[LIST_TO_SET]].

    The data itself is represented as a [[byte list]] in the datagram but is returned a [[string]]:
    the [[IMPLODE]] function is used to do the conversion.

    @internal

    Attempt to receive data from the socket receive queue.  If the caller wants ordinary data and
    is not peeking, and either there is pending data on the receive queue or the caller wants 0 bytes
    (and if [[MSG_WAITALL]] is set, *all* desired bytes are present), then return the appropriate
    prefix of the receive queue, and leave the remainder on the queue.

    Note that we only need to check for nonblocking (in socket or flags) if we might block, which we
    cannot here.

    We *think* from POSIX that [[MSG_PEEK]] means that the [[MSG_WAITALL]] behaviour should not
    apply.  It's not clear, though; a straightforward reading would make this semantics a MAY not a
    MUST. In fact, under BSD, [[MSG_PEEK]] does not affect [[MSG_WAITALL]] behaviour, and the call
    still requires n bytes of data to be returned.

    We also think that if [[MSG_PEEK]] is set (and [[MSG_WAITALL]] is not set), that the call will not
    return until at least [[SO_RCVLOWAT]] bytes are available.

    The [[clip_int_to_num]] represents one possible implementation.  POSIX specifies an unsigned
    type for [[n0]], so negative values cannot arise.

    Does the [[rcvurp]] evaporate whenever we read up to the mark?  If so, the test should be [[om
    <= LENGTH str]].  If not, it should be [[<]].  (But note that [[om]] is never less than [[LENGTH
    str]], because we never read *past* the mark, only up to it).

    We should allow this to be interrupted *in the middle* by an interrupt, in which case we return
    the number of bytes transferred.  But this does it atomically, so there's no middle!  Oops!

    CHANGE TO MEM AND NOTMEM and do clever typesetting for them.

    TODO: for this and other recv rules, should deliver in any [[st >= ESTABLISHED]], not just in
    [[ESTABLISHED]].  Note that even if data arrives before [[ESTABLISHED]], it should not be
    delivered until then.

   :*)
   )

/\

   (!h ts tid d
     fd n0 n opts0 opts fid sid ff sf i1 p1 cb st es
     i2 p2 cantrcvmore cantsndmore
     inline peek flgs
     SS s s' MM.

   recv_2 /* rp_tcp, block (*: Block, entering state [[Recv2]] as not enough data is available :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s)],MM)
   -- Lh_call (tid,recv(fd,n0,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Recv2(sid,n,opts),never_timer)) |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s')],MM)

   <==

     n = clip_int_to_num n0 /\
     opts = LIST_TO_SET opts0 /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     FAPPLY h.socks sid = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                               TCP_Sock(st,cb,NONE)) /\
     st IN {ESTABLISHED; SYN_SENT; SYN_RECEIVED; FIN_WAIT_1; FIN_WAIT_2} /\

     (*: We block if not enough (see {@link [[recv_1]]}) data is available and there is no pending error. :*)
     ? rcvq.
     let blocking          = ~(MSG_DONTWAIT IN opts \/ ff.b(O_NONBLOCK)) in
     let have_all_data     = (LENGTH rcvq >= n) in (* BSD only compares against SO_RCVLOWAT if buffer contains less data than requested *)
     let have_enough_data  = (LENGTH rcvq >= sf.n(SO_RCVLOWAT)) in
     let partial_data_ok   = (MSG_WAITALL NOTIN opts \/ n > sf.n(SO_RCVBUF) \/
                              (~(bsd_arch h.arch) /\ MSG_PEEK IN opts)) in
     blocking /\
     ~(have_all_data \/ (have_enough_data /\ partial_data_ok) \/ cantrcvmore) /\
     es = NONE  (* NB: pending errors are checked, since we are going to block *) /\

     peek = T /\
     inline = T /\
     read (i1,p1,i2,p2) peek inline (flgs,rcvq) s s'


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[recv(fd,n0,opts0)]] call is made where
    out-of-band data is not requested. [[fd]] refers to a TCP socket [[sid]] in state
    [[ESTABLISHED]], [[SYN_SENT]], [[SYN_RECEIVED]], [[FIN_WAIT_1]], or [[FIN_WAIT_2]], with binding
    quad [[(SOME i1,SOME p1,SOME i2,SOME p2)]] and no pending error. The call is blocking: the
    [[MSG_DONTWAIT]] flag is not set in [[opts0]] and the socket's [[O_NONBLOCK]] flag is not set.

    The call cannot return immediately because: (1) there are less than [[n]] bytes of data in the
    socket's receive queue; (2) there are less than [[sf.n(SO_RVCLOWAT)]] (the minimum number of
    bytes for socket [[recv()]] operations) bytes of data in the socket's receive queue or the call
    must return all [[n]] bytes of data: (i) the [[MSG_WAITALL]] flag is set in [[opts0]], (ii) the
    number of bytes requested is greater than the length of the socket's receive queue, and (iii)
    the [[MSG_PEEK]] flag is not set in [[opts0]]; (3) there is no urgent data ahead in the socket's
    receive queue; and (4) the socket is not shutdown for reading.

    The call blocks in state [[Recv2]] waiting for data; a [[Lh_call(tid,recv(fd,n0,opts0))]]
    transition is made, leaving the thread state [[Recv2(sid,n,opts)]].

    @variation FreeBSD

    In case (iii) above, the [[MSG_PEEK]] flag may be set in [[opts0]].

    @modeldetails

    The amount of data requested, [[n0]], is clipped to a natural number from an integer, using
    [[clip_int_to_num]]. POSIX specifies an unsigned type for [[n0]], whereas the model uses [[int]].

    The [[opts0]] argument to [[recv()]] is of type [[msgbflag list]], but it is converted to a set,
    [[opts]], using [[LIST_TO_SET]].

    @internal

    Attempt to read data from the socket receive queue.  If the receive queue is empty (and the
    caller wants more than 0 bytes), or the caller wants all the bytes and the receive queue does not
    contain them, *and* nonblocking behaviour is not requested, and the caller does not want OOB
    data, then we block until the data arrives.

    We can try to block (and therefore fail to block) in any connecting/connected state, however we
    never try to block after receiving a FIN, since we know we'll never get any more data!

    Worried about [[SO_RCVTIMEO]] here when [[MSG_WAITALL]] is set.  Need to (a) maintain that timer
    in the protocol layer, and (b) add a rule to cause [[Recv2]] to drop out when it runs out.

   :*)
   )

/\
   (!h ts tid d
     n opts fid sid socks sf i1 p1 st cb is1 ps1 is2 ps2
     i2 p2 es cantrcvmore cantsndmore
     str
     flgs peek inline SS s s' MM.

   recv_3 /* rp_tcp, slow nonurgent succeed (*: Blocked call returns from [[Recv2]] state :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Recv2(sid,n,opts),d));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,cantsndmore,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s)],MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (IMPLODE str, NONE)),sched_timer));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,cantsndmore,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s')],MM)

   <==

     ((st IN {ESTABLISHED; FIN_WAIT_1; FIN_WAIT_2; CLOSING;
              TIME_WAIT; CLOSE_WAIT; LAST_ACK} /\ (* normal case *)
       is1 = SOME i1 /\ ps1 = SOME p1 /\ is2 = SOME i2 /\ ps2 = SOME p2) \/
      st = CLOSED) /\

     ? rcvq.
     (*: We return at last if we now have enough (see {@link [[recv_1]]}) data available.  Pending errors are not checked. :*)
     let have_all_data     = (LENGTH rcvq >= n) in (* BSD only compares against SO_RCVLOWAT if buffer contains less data than requested *)
     let have_enough_data  = (LENGTH rcvq >= sf.n(SO_RCVLOWAT)) in
     let partial_data_ok   = (MSG_WAITALL NOTIN opts \/ n > sf.n(SO_RCVBUF) \/
                              (~(bsd_arch h.arch) /\ MSG_PEEK IN opts)) in
     (have_all_data \/ (have_enough_data /\ partial_data_ok) \/ cantrcvmore) /\
     (* NB: pending errors are not checked *)

     str = (rcvq:char list) /\

     peek = (MSG_PEEK IN opts) /\
     inline = T /\
     read (i1,p1,i2,p2) peek inline (flgs,rcvq) s s' /\
     LENGTH rcvq <= n


   (*:

    @description

    Thread [[tid]] is in the [[Recv2(sid,n,opts)]] state after a previous [[recv()]] call
    blocked. [[sid]] refers either to a synchronised TCP socket with binding quad [[(SOME i1,SOME
    p1,SOME i2,SOME p2)]]; or to a TCP socket in state [[CLOSED]].

    Sufficient data is not available on the socket for the call to return: either (1) there is at
    least [[n]] bytes of data in the socket's receive queue (the [[have_all_data]] case above); (2)
    the length of the socket's receive queue is greater than or equal to the minimum number of bytes
    for socket [[recv()]] operations, [[sf.n(SO_RCVLOWAT)]], and the call does not have to return
    all [[n]] bytes of data (the [[partial_data_ok]] case): either (i) the [[MSG_WAITALL]] flag is
    not set in [[opts]], (ii) the number of bytes requested is greater than the number of bytes in
    the socket's receive queue, or (iii) on non-FreeBSD architectures the [[MSG_PEEK]] flag is set
    in [[opts]] (the [[have_enough_data /\ partial_data_ok]] case above); (3) there is urgent data
    available in the socket's receive queue (the [[urgent_data_ahead]] cae above); or (4) the socket
    has been shutdown for reading.

    The data returned, [[str]], is either: (1) the smaller of the first [[n]] bytes of the socket's
    receive queue or its entire receive queue, if the urgent pointer is not set or the socket is at
    the urgent mark; or (2) the smaller of the first [[n]] bytes of the the socket's receive queue,
    the data in its receive queue up to the urgent mark, and its entire receive queue, if the urgent
    mark is set and the socket is not at the urgent mark.

    A [[Lh_tau]] transition is made leaving the thread state [[Ret (OK(IMPLODE str,NONE))]]. If
    the [[MSG_PEEK]] flag was set in [[opts]] then the socket's receive queue remains unchanged;
    otherwise, the data [[str]] is removed from the head of the socket's receive queue, [[rcvq]], to
    leave the socket with new receive queue [[rcvq']]. If the receive urgent pointer was not set or was
    set to [[SOME 0]] then it will be set to [[NONE]]; if it was set to [[SOME om]] and [[om]] is
    less than the length of the returned string then it will be set to [[SOME 0]] (because the
    returned string was the data in the receive queue up to the urgent mark); otherwise it will be
    set to [[SOME(om-LENGTH str)]].

    @modeldetails

    The data itself is represented as a [[byte list]] in the datagram but is returned a [[string]]:
    the [[IMPLODE]] function is used to do the conversion.

    @internal

    If the receive queue is nonempty or we've received a FIN, then we do just the same as
    [[recv_1]], and return from the call.

    Do we really know that the [[fid]] argument of the socket is [[SOME fid]]?  What if the caller
    closes the socket after a blocking [[recv()]]?

    This allows for the case that recv() has been called under BSD with the [[MSG_WAITALL]] option.
    soreceive() (see lines 899-929 in kern/uipc_socket.c) returns ok in the case of its sbwait being
    interrupted by an error iff [[MSG_WAITALL]] is set, causing the recv() to return with the data currently
    in the receive buffer. [[deliver_in_7]] checks to see if an RST is received during an recv(MSG_WAITALL),
    and if so calls a special version of [[tcp_output]] ([[tcp_output_bsd_recv2]]) to close the socket without
    clearing [[rcvq]]. Thus [[recv_3]] is able to access the data currently in the buffer (which is cleared
    in the process of being passed to the user).

    The case of [[MSG_PEEK]] being set is also considered, given that a combination of this and the above
    could cause a closed socket to exist with a non-empty receive queue. We therefore clear [[rcvq]] regardless
    of whether [[MSG_PEEK]] has been set, if the socket is in the [[CLOSED]] state.

   :*)
   )

/\

   (!h ts tid d
     fd n0 n opts0 opts fid sid ff sf i1 p1 cb st es
     i2 p2 cantrcvmore cantsndmore
     inline peek flgs SS s s' MM.

   recv_4 /* rp_tcp, fast fail (*: Fail with [[EAGAIN]]: non-blocking call would block waiting for data :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s)],MM)
   -- Lh_call (tid,recv(fd,n0,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EAGAIN),sched_timer)) |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s')],MM)

   <==

     n = clip_int_to_num n0 /\
     opts = LIST_TO_SET opts0 /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     FAPPLY h.socks sid = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                               TCP_Sock(st,cb,NONE)) /\
     st IN {ESTABLISHED; SYN_SENT; SYN_RECEIVED; FIN_WAIT_1; FIN_WAIT_2} /\

     ? rcvq.
     (*: We fail if we would otherwise block (see {@link [[recv_2]]}; these conditions are identical). :*)
     let blocking          = ~(MSG_DONTWAIT IN opts \/ ff.b(O_NONBLOCK)) in
     let have_all_data     = (LENGTH rcvq >= n) in (* BSD only compares against SO_RCVLOWAT if buffer contains less data than requested *)
     let have_enough_data  = (LENGTH rcvq >= sf.n(SO_RCVLOWAT)) in
     let partial_data_ok   = (MSG_WAITALL NOTIN opts \/ n > sf.n(SO_RCVBUF) \/
                              (~(bsd_arch h.arch) /\ MSG_PEEK IN opts)) in
     ~blocking /\
     ~(have_all_data \/ (have_enough_data /\ partial_data_ok) \/ cantrcvmore) /\
     (rcvq = [] ==> es = NONE) /\ (* pending errors are checked if we have no data at all (uipc_socket.c:726) (??) *)
     (* NB: pending errors are not normally checked, since we will not block *)

     peek = T /\
     inline = T /\
     read (i1,p1,i2,p2) peek inline (flgs,rcvq) s s'


   (*:

    @description

    From thead [[tid]], which is in the [[Run]] state, a [[recv(fd,n0,opts0)]] call is made where
    out-of-band data is not requested. [[fd]] refers to a TCP socket [[sid]] with binding quad
    [[(SOME i1,SOME p1,SOME i2,SOME p2)]] and no pending error, which is in state [[ESTABLISHED]],
    [[SYN_SENT]], [[SYN_RECEIVED]], [[FIN_WAIT_1]], or [[FIN_WAIT_2]]. The [[recv()]] call is
    non-blocking: either the [[MSG_DONTWAIT]] flag was set in [[opts0]] or the socket's
    [[O_NONBLOCK]] flag is set.

    The call would block because: (1) there are less than [[n]] bytes of data in the socket's
    receive queue; (2) there are less than [[sf.n(SO_RVCLOWAT)]] (the minimum number of bytes for
    socket [[recv()]] operations) bytes of data in the socket's receive queue or the call must
    return all [[n]] bytes of data: (i) the [[MSG_WAITALL]] flag is set in [[opts0]], (ii) the
    number of bytes requested is greater than the length of the socket's receive queue, and (iii)
    the [[MSG_PEEK]] flag is not set in [[opts0]]; (3) there is no urgent data ahead in the socket's
    receive queue; (4) the socket is not shutdown for reading; and (5) if the socket's receive queue
    is empty then it has no pending error.

    The call fails with an [[EAGAIN]] error. A [[Lh_call(tid,recv(fd,n0,opts0))]] transition is
    made, leaving the thread state [[Ret (FAIL EAGAIN)]].


    @variation FreeBSD

    In case (iii) above, the [[MSG_PEEK]] flag may be set in [[opts0]].

    @modeldetails

    The amount of data requested, [[n0]], is clipped to a natural number from an integer, using
    [[clip_int_to_num]]. POSIX specifies an unsigned type for [[n0]] and this is one possible model
    thereof.

    The [[opts0]] argument to [[recv()]] is of type [[msgbflag list]], but it is converted to a set,
    [[opts]], using [[LIST_TO_SET]].

    @internal

    If the receive queue is empty (and the caller wants more than 0 bytes), or the caller wants all
    the bytes and the receive queue does not contain them, *and* nonblocking behaviour is requested,
    and the caller does not want OOB data, then we fail with [[EAGAIN]] indicating that we would have
    blocked.

    We can try to block (and therefore fail to block) in any connecting/connected state, however we
    never try to block after receiving a FIN, since we know we'll never get any more data!

    Can we merge this rule with [[recv_2]] while maintaining clarity?

    FIX COMMENTS (first paras) on [[recv_1]] through [[recv_4]].

    MORE STUFF TO DO:

    In both states, we need to deal with pending errors arriving causing an early return.  Need to
    deal with connecction termination.  Need to deal with signals arriving.  (in these cases, we
    cannot necessarily return an error because the kernel may already have copied some bytes to the
    user process).

    ==> After discussion, we think that this does not mean the copy from kernel to user space can be
    interrupted, only that when the thread blocks waiting for enough data ([[WAITALL|RCVLOWAT]]) it can
    be interrupted (by EINTR or signal or pending error).  But we do not know.

    ==> But when that interrupt arrives, we have two possibilities: (i) return the error
    immediately, or (ii) copy as much as we have so far, and allow the error to be returned at the
    next call.  Option (ii) does make sense in at least one case: if the kernel copies data directly
    from the NIC to user space, without going via kernel space.

    ==> We need to determine if this happens significantly in the OSs we care about.  If it does, we
    need to do a substantial rewrite, because for us now the operation is atomic (and so nothing can
    happen during the copy).

    ==> There is an easy case, though: if we're blocked with some stuff in rcvq and an
    interrupt/error arrives, at present we just return that error, but we could simply return the
    contents of rcvq (if nonempty) to the user successfully (and not touch the error flag).

    ==> The worst case is that we can get an interrupt *during* a fast succeed or slow succeed,
    i.e., something that is at present atomic.

    We need to deal with all the error conditions.

    We need to implement the [[SO_RCVTIMEO]] timer.

    We need to do all the protocol-layer stuff.

   :*)
   )

/\

   (!h ts tid d
     fd n0 opts0 fid sid ff tcp_sock sock
     SS MM.

   recv_7 /* rp_tcp, fast fail (*: Fail with [[ENOTCONN]]: socket not connected :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,recv(fd,n0,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOTCONN),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sock = h.socks ' sid /\
     TCP_PROTO(tcp_sock) = sock.pr /\
     (tcp_sock.st = LISTEN \/ (* note: can call recv() in SYN_RCVD and TIME_WAIT *)
      (tcp_sock.st = CLOSED /\ sock.cantrcvmore=F)
      (*(tcp_sock.st = FIN_WAIT_2 /\ sock.cantrcvmore = T) \/*) (* BSD extension *) (* MS: hmmm... dubious *)
(*      F (* Placeholder for: if tcp_disconnect or tcp_usrclose has been invoked *) (* see K log p2178 *) *)
     )


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[recv(fd,n0,opts0)]] call is made. [[fd]]
    refers to a TCP socket [[sock]] identified by [[sid]] which is either in the [[LISTEN]] state or
    is not shutdown for reading in the [[CLOSED]] state. The call fails with an [[ENOTCONN]] error.

    A [[Lh_call(tid,recv(fd,n0,opts0))]] transition is made, leaving the thread state [[Ret
    (FAIL ENOTCONN)]].

    @internal

    Attempt to read data from a socket that is not connected: return [[ENOTCONN]].

   :*)
   )

/\

   (!h ts tid d is2
     fd n0 n opts0 opts fid sid socks ff
     sf is1 ps1 i2 p2 e es tcp_sock cantsndmore cantrcvmore ps2
     SS MM.

   recv_8 /* rp_tcp, fast fail (*: Fail with pending error :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,SOME e,cantsndmore,cantrcvmore,TCP_PROTO(tcp_sock)))] |>,
     SS,MM)
   -- Lh_call (tid,recv(fd,n0,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,cantsndmore,cantrcvmore,TCP_PROTO(tcp_sock)))] |>,
     SS,MM)

   <==

     opts = LIST_TO_SET opts0 /\
     n = clip_int_to_num n0 /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     ((tcp_sock.st NOTIN {CLOSED; LISTEN} /\ is2 = SOME i2 /\ ps2 = SOME p2) \/
      tcp_sock.st = CLOSED) /\

     (*: We fail immediately if there is a pending error and we could not otherwise return data (see {@link [[recv_1]]}). :*)
     let rcvq = ([]: char list) in
     let blocking          = ~(MSG_DONTWAIT IN opts \/ ff.b(O_NONBLOCK)) in
     let have_all_data     = (LENGTH rcvq >= n) in (* BSD only compares against SO_RCVLOWAT if buffer contains less data than requested *)
     let have_enough_data  = (LENGTH rcvq >= sf.n(SO_RCVLOWAT)) in
     let partial_data_ok   = (MSG_WAITALL NOTIN opts \/ n > sf.n(SO_RCVBUF) \/
                              (~(bsd_arch h.arch) /\ MSG_PEEK IN opts)) in
     ~(have_all_data \/ (have_enough_data /\ partial_data_ok)) /\
     (blocking \/ rcvq = []) /\ (* NB: pending errors are only checked if we are going to block, or if we're nonblocking and the receive queue is completely empty *)

     es = if MSG_PEEK IN opts then SOME e else NONE


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[recv(fd,n0,opts0)]] call is made. [[fd]]
    refers to a TCP socket that either is in state [[CLOSED]] or is in state other than [[CLOSED]]
    or [[LISTEN]] with peer address set to [[(SOME i2,SOME p2)]]. The socket has a pending error
    [[e]].

    The call cannot immediately return data because: (1) there are less than [[n]] bytes of data in
    the socket's receive queue; (2) there are less than [[sf.n(SO_RVCLOWAT)]] (the minimum number of
    bytes for socket [[recv()]] operations) bytes of data in the socket's receive queue or the call
    must return all [[n]] bytes of data: (i) the [[MSG_WAITALL]] flag is set in [[opts0]], (ii) the
    number of bytes requested is greater than the length of the socket's receive queue, and (iii)
    the [[MSG_PEEK]] flag is not set in [[opts0]]; (3) there is no urgent data ahead in the socket's
    receive queue; and (4) either the call is a blocking
    one: the [[MSG_DONTWAIT]] flag is set in [[opts0]] or the socket's [[O_NONBLOCK]] flag is set,
    or the socket's receive queue is empty.

    The call fails, returning the pending error. A [[Lh_call(tid,recv(fd,n0,opts0))]] transition is
    made, leaving the thread state [[Ret (FAIL e)]]. If the [[MSG_PEEK]] flag was set in
    [[opts0]] then the socket's pending error remains, otherwise it is cleared.

    @variation FreeBSD

    In case (iii) above, the [[MSG_PEEK]] flag may be set in [[opts0]].

    @modeldetails

    The [[opts0]] argument to [[recv()]] is of type [[msgbflag list]], but it is converted to a
    set, [[opts]], using [[LIST_TO_SET]].

    @internal

    Attempt to read data from a socket that has a pending error: return the error instead, and clear
    it so that (unless the condition is reasserted in the meantime) the next call will succeed.

    TCPv2p515 - only return the error if the socket is *empty*. If [[MSG_PEEK]] is set, do not clear the error
                state (as [[MSG_PEEK]] should never change the state of the socket).

    QUESTION: do we insist we're [[ESTABLISHED]] first, as here?

    POSIX: has only [[ECONNRESET]] and [[ETIMEDOUT]] here.

    Maybe we sometimes do a partial return from [[recv()]] here, and allow the actual error to be
    returned *next*.

    WHAT ABOUT THE SLOW VERSION OF THIS?

   :*)
   )

/\

    (!h ts tid sid n opts d
      socks sock e es tcp_sock
      rcvq
      SS MM.

    recv_8a /* rp_tcp, slow urgent fail (*: Fail with pending error from blocked state :*) */
      (h with <| ts := FUPDATE ts (tid, Timed(Recv2(sid,n,opts),d));
                socks := socks |++
                         [(sid, sock with <| es := SOME e; pr := TCP_PROTO(tcp_sock) |>)] |>,
      SS,MM)
    -- Lh_tau -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (FAIL e),sched_timer));
                socks := socks |++
                         [(sid, sock with <| es := es; pr := TCP_PROTO(tcp_sock) |>)] |>,
      SS,MM)

    <==

     rcvq = ([]:char list) /\
     (* MS: previously, sock was constrained with 'ps1 := SOME p1', but do not believe this is correct.
            there are no other rules to handle failing due to socket closing, in which case ps1 = NONE,
            so we should handle that here. *)

     (*: We fail now if there is a pending error and we could not otherwise return data (see {@link [[recv_1]]}). :*)
     let have_all_data     = (LENGTH rcvq >= n) in (* BSD only compares against SO_RCVLOWAT if buffer contains less data than requested *)
     let have_enough_data  = (LENGTH rcvq >= sock.sf.n(SO_RCVLOWAT)) in
     let partial_data_ok   = (MSG_WAITALL NOTIN opts \/ n > sock.sf.n(SO_RCVBUF) \/
                              (~(bsd_arch h.arch) /\ MSG_PEEK IN opts)) in
     ~(have_all_data \/ (have_enough_data /\ partial_data_ok)) /\

     (es = if MSG_PEEK IN opts then SOME e else NONE)


   (*:

    @description

    Thread [[tid]] is blocked in state [[Recv2(sid,n,opts)]] where [[sid]] identifies a socket with
    pending error [[SOME e]]. The call fails, returning the pending error. Data cannot be returned
    because: (1) there are less than [[n]] bytes of data in the socket's receive queue; (2) there
    are less than [[sf.n(SO_RVCLOWAT)]] (the minimum number of bytes for socket [[recv()]]
    operations) bytes of data in the socket's receive queue or the call must return all [[n]] bytes
    of data: (i) the [[MSG_WAITALL]] flag is set in [[opts]], (ii) the number of bytes requested is
    greater than the length of the socket's receive queue, and (iii) the [[MSG_PEEK]] flag is not
    set in [[opts]]; and (3) there is no urgent data ahead in the socket's receive queue.

    The thread returns from the blocked state, returning the pending error. A [[Lh_tau]] transition
    is made, leaving the thread state [[Ret (FAIL e)]]. If the [[MSG_PEEK]] flag was set in
    [[opts]] then the socket's pending error remains, otherwise it is cleared.

    @variation FreeBSD

    In case (iii) above, the [[MSG_PEEK]] flag may be set in [[opts]].

    @internal

    This was a rule in the UDP spec. Comments above question whether it should be here.  TCPv2 p516
    says that if the call has blocked and an error occurs, then that would be returned.

    p515 also says that MSG_PEEK should not clear the socket's error state.

   :*)

   )

/\

    (!h ts tid d socks sid sock tcp_sock fd n opts fid ff
      SS MM.

    recv_9 /* rp_tcp, fast fail (*: Fail with [[ESHUTDOWN]]: socket shut down for reading on WinXP :*) */
      (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
                socks := socks |++
		         [(sid,sock with <| cantrcvmore := T; pr := TCP_PROTO(tcp_sock) |>)] |>,
      SS,MM)
    -- Lh_call(tid,recv(fd,n,opts)) -->
      (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ESHUTDOWN),sched_timer));
                socks := socks |++
		         [(sid,sock with <| cantrcvmore := T; pr := TCP_PROTO(tcp_sock) |>)] |>,
      SS,MM)

    <==

      windows_arch h.arch /\
      fd IN FDOM h.fds /\
      fid = h.fds ' fd /\
      FAPPLY h.files fid = File(FT_Socket(sid),ff)


    (*:

     @description

     On WinXP, from thread [[tid]], which is in the [[Run]] state, a [[recv(fd,n,opts)]] call is
     made where [[fd]] refers to a TCP socket [[sid]] which is shut down for reading. The call fails
     with an [[ESHUTDOWN]] error.

     A [[Lh_call(tid,recv(fd,n0,opts0))]] transition is made, leaving the thread state [[Ret
     (FAIL ESHUTDOWN)]].

     @variation FreeBSD

     This rule does not apply.

     @variation Linux

     This rule does not apply.

    :*)

  )


/\


(*:

@section [[udp_recv]] UDP [[recv()]]
 \[ <[recv: (fd * int * msgbflag list) -> (string * ((ip * port) * bool) option)]> \]

  A call to [[recv(fd,n,opts)]] returns data from the datagram on the head of a socket's receive
  queue.
   This section describes
  the behaviour for UDP sockets.
  Here the [[fd]] argument is a file descriptor referring to the socket to receive data from,   [[n]] specifies the number of
  bytes of data to read from that socket, and the [[opts]] argument is a list of flags for the [[recv()]] call.  The possible flags are:

  \begin{itemize}

    \item [[MSG_DONTWAIT]]: non-blocking behaviour is requested for this call. This flag only has
     effect on Linux. FreeBSD and WinXP ignore it. See rules [[recv_12]] and [[recv_13]].

    \item [[MSG_PEEK]]: return data from the datagram on the head of the receive queue, without
     removing that datagram from the receive queue.

    \item [[MSG_WAITALL]]: do not return until all [[n]] bytes of data have been read. Linux and
     FreeBSD ignore this flag. WinXP fails with [[EOPNOTSUPP]] as this is not meaningful for UDP
     sockets: the returned data is from only one datagram.

    \item [[MSG_OOB]]: return out-of-band data. This flag is ignored on Linux. On WinXP and FreeBSD
     the call fails with [[EOPNOTSUPP]] as out-of-band data is not meaningful for UDP sockets.

  \end{itemize}

  The returned value of the [[recv()]] call, [[(string * ((ip * port) * bool) option)]], consists of
  the data read from the socket (the [[string]]), the source address of the data (the [[ip *
  port]]), and a flag specifying whether or not all of the datagram's data was read (the
  [[bool]]). The latter two components are wrapped in an [[option]] type (for type compatibility with the TCP [[recv()]]) but are always returned for UDP. The
  flag only has meaning on WinXP and should be ignored on FreeBSD and Linux.

  For a socket to receive data, it must be bound to a local port. On Linux and FreeBSD, if the
  socket is not bound to a local port, then it is autobound to an ephemeral port when the [[recv()]]
  call is made. On WinXP, calling [[recv()]] on a socket that is not bound to a local port is an
  [[EINVAL]] error.

  If a non-blocking [[recv()]] call is made (the socket's [[O_NONBLOCK]] flag is set) and there are
  no datagrams on the socket's receive queue, then the call will fail with [[EAGAIN]]. If the call
  is a blocking one and the socket's receive queue is empty then the call will block, returning when
  a datagram arrives or an error occurs.

  If the socket has a pending error then on FreeBSD and Linux, the call will fail with that
  error. On WinXP, errors from ICMP messages are placed on the socket's receive queue, and so the
  error will only be returned when that message is at the head of the receive queue.

@errors

  A call to [[recv()]] can fail with the errors below, in which case the corresponding exception is
  raised.

  @error [[EAGAIN]] The call would block and non-blocking behaviour is requested. This is done
   either via the [[MSG_DONTWAIT]] flag being set in the [[recv()]] flags or the socket's
   [[O_NONBLOCK]] flag being set.

  @error [[EMSGSIZE]] The amount of data requested in the [[recv()]] call on WinXP is less than the
   amount of data in the datagram on the head of the receive queue.

  @error [[EOPNOTSUPP]] Operation not supported: out-of-band data is requested on FreeBSD and WinXP,
   or the [[MSG_WAITALL]] flag is set on a [[recv()]] call on WinXP.

  @error [[ESHUTDOWN]] On WinXP, a [[recv()]] call is made on a socket that has been shutdown for
   reading.

  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]
  @errorinclude [[misc]] [[EINTR]]
  @errorinclude [[misc]] [[ENOBUFS]]
  @errorinclude [[misc]] [[ENOMEM]]

@commoncases

   \

  A UDP socket is created and bound to a local address. Other calls are made and datagrams are
  delivered to the socket; [[recv()]] is called to read from a datagram: [[socket_1]]; [[return_1]];
  [[bind_1]]; $ \ldots $ [[recv_11]]; [[return_1]];

  A UDP socket is created and bound to a local address. [[recv()]] is called and blocks; a datagram
  arrives addressed to the socket's local address and is placed on its receive queue; the call
  returns: [[socket_1]]; [[return_1]]; [[bind_1]]; $ \ldots $ [[recv_12]]; [[deliver_in_99]];
  [[deliver_in_udp_1]]; [[recv_15]]; [[return_1]];

@api

  \begin{tabular}{ll}
    Posix:   & |ssize_t recvfrom(int socket, void *restrict buffer, size_t length,|\\
             & |                  int flags, struct sockaddr *restrict address,|\\
             & |                 socklen_t *restrict address_len);|\\
    FreeBSD: & |ssize_t recvfrom(int s, void *buf, size_t len, int flags,| \\
             & |                 struct sockaddr *from, socklen_t *fromlen);| \\
    Linux:   & |int  recvfrom(int  s, void *buf, size_t len, int flags,| \\
             & |              struct sockaddr *from, socklen_t *fromlen);| \\
    WinXP:   & |int recvfrom(SOCKET s, char* buf, int len, int flags,| \\
             & |             struct sockaddr* from, int* fromlen);| \\
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |socket| is the file descriptor of the socket to receive from, corresponding to
     the [[fd]] argument of the model [[recv()]].

    \item |buffer| is a pointer to a buffer to place the received data in, which upon return
     contains the data received on the socket. This corresponds to the [[string]] return value of
     the model [[recv()]].


    \item |length| is the amount of data to be read from the socket, corresponding to the [[int]]
     argument of the model [[recv()]]; it should be at most the length of |buffer|.

    \item |flags| is a disjunction of the message flags that are set for the call, corresponding to
     the [[msgbflag]] [[list]] argument of the model [[recv()]].

    \item |address| is a pointer to a |sockaddr| structure of length
     |address_len|, which upon return contains the source address of the data received by
     the socket corresponding to the [[(ip * port)]] in the return value of the model
     [[recv()]]. For the |AF_INET| sockets used in the model, it is actually a
     |sockaddr_in| that is used: the |in_addr.s_addr| field corresponds to the
     [[ip]] and the |sin_port| field corresponds to the [[port]].

    \item the returned |ssize_t| is either non-negative, in which case it is the the amount
     of data that was received by the socket, or it is |-1| to indicate an error, in which
     case the error code is in |errno|. On WinXP an error is indicated by a return value of
     |SOCKET_ERROR|, not |-1|, with the actual error code available through a
     call to |WSAGetLastError()|.

  \end{itemize}

  On WinXP, if the data from a datagram is not all read then the call fails with [[EMSGSIZE]],
  but still fills the |buffer| with data. This is modelled by the [[bool]] flag in the model
  [[recv()]]: if it is set to [[T]] then the call succeeded and read all of the datagrams's data; if
  it is set to [[F]] then the call failed with [[EMSGSIZE]] but still returned data.

  There are other functions used to receive data on a socket. |recv()| is similar to
  |recvfrom()| except it does not have the |address| and |address_len|
  arguments. It is used when the source address of the data does not need to be returned from the
  call. |recvmsg()|, another input function, is a more general form of |recvfrom()|.

@modeldetails

  If the call blocks then the thread enters state [[Recv2(sid,n,opts)]] where:

  \begin{itemize}

    \item [[sid : sid]] is the identifier of the socket that the [[recv()]] call was made on,

    \item [[n : num]] is the number of bytes to be read, and

    \item [[opts : msgbflag list]] is the set of message flags.

  \end{itemize}

  The following errors are not modelled:

  \begin{itemize}

    \item On FreeBSD, Linux, and WinXP, [[EFAULT]] can be returned if the |buffer|
    parameter points to memory not in a valid part of the process address space. This is an artefact
    of the C interface to |ioctl()| that is excluded by the clean interface used in the
    model [[recv()]].

    \item In Posix, |EIO| may be returned to indicated that an I/O error occurred while
    reading from or writing to the file system; this is not modelled here.

    \item |EINVAL| may be returned if the [[MSG_OOB]] flag is set and no out-of-band data is
    available; out-of-band data does not exist for UDP so this does not apply.

    \item |ENOTCONN| may be returned if the socket is not connected; this does not apply for
    UDP as the socket need not have a peer specified to receive datagrams.

    \item |ETIMEDOUT| can be returned due to a transmission timeout on a connection; UDP is
    not connection-oriented so this does not apply.

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

   The following Linx message flags are not modelled: |MSG_NOSIGNAL|, |MSG_TRUNC|, and
  |MSG_ERRQUEUE|.

:*)

    (!h ts tid d socks sid sock n
      rcvq fd n0 opts0 data i3 ps3 opts rcvq'' data'
      fid ff sf is1 p1 is2 ps2 rcvq' cantsndmore b cantrcvmore
      SS MM.

    recv_11 /* rp_udp, fast succeed (*: Receive data successfully without blocking :*) */
      (h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                socks := socks |++
                         [(sid,sock with <| pr := UDP_Sock(rcvq) |>)] |>,
      SS,MM)
    -- Lh_call (tid, recv(fd,n0,opts0)) -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (OK(IMPLODE data',SOME((i3,ps3),b))),sched_timer));
                socks := socks |++
                         [(sid,sock)] |>,
      SS,MM)

    <==

       fd IN FDOM h.fds /\
       fid = h.fds ' fd /\
       FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
       sock = Sock(SOME fid,sf,is1,SOME p1,is2,ps2,NONE,cantsndmore,cantrcvmore,UDP_Sock(rcvq')) /\
       (~(linux_arch h.arch) ==> cantrcvmore = F) /\
       rcvq = (Dgram_msg(<| is := i3; ps := ps3; data := data |>))::rcvq'' /\
       n = clip_int_to_num n0 /\
       ((LENGTH data <= n /\ data = data') \/
         (LENGTH data > n /\ data' = TAKE n data /\ LENGTH data' = n /\ ~(windows_arch h.arch))) /\
       (windows_arch h.arch ==> b = T) /\
       opts = LIST_TO_SET opts0 /\
       rcvq' = (if MSG_PEEK IN opts then rcvq else rcvq'')


   (*:


    @description

    Consider a UDP socket [[sid]], referenced by [[fd]]. It is not shutdown for reading, has no
    pending errors, and is bound to local port [[p1]]. Thread [[tid]] is in the [[Run]] state.

    The socket's receive queue has a datagram at its head with data [[data]] and source address
    [[i3,ps3]]. A call [[recv(fd,n0,opts0)]], from thread [[tid]], succeeds.

    A [[Lh_call(tid,recv(fd,n0,opts0))]] transition is made. The thread is left in state [[Ret
    (OK(IMPLODE data',SOME(i3,ps3)))]], where [[data']] is either:

    \begin{itemize}

      \item all of the data in the datagram, [[data]], if the amount of data requested [[n0]] is
       greater than or equal to the amount of data in the datagram, or

      \item the first [[n0]] bytes of [[data]] if [[n0]] is less than the amount of data in the
       datagram, unless the architecture is WinXP (see below).

    \end{itemize}

    If the [[MSG_PEEK]] option is set in [[opts0]] then the entire datagram stays on the receive
    queue; the next call to [[recv()]] will be able to access this datagram. Otherwise, the entire
    datagram is discarded from the receive queue, even if all of its data has not been read.

    @variation WinXP

    The amount of data in bytes requested, [[n0]], must be greater than or equal to the number of
    bytes of data in the datagram on the head of the receive queue. The boolean [[b]] equals [[T]],
    indicating that all of the datagram's data has been read. Otherwise refer to rule [[recv_20]].

    @modeldetails

    The amount of data requested, [[n0]], is clipped to a natural number from an integer, using
    [[clip_int_to_num]]. POSIX specifies an unsigned type for [[n0]] and this is one possible model
    thereof.

    The [[opts0]] argument to [[recv()]] is of type [[msgbflag list]], but it is converted to a set,
    [[opts]], using [[LIST_TO_SET]].

    The data itself is represented as a [[byte list]] in the datagram but is returned a [[string]]:
    the [[IMPLODE]] function is used to do the conversion.

    @internal

    When a [[recv]] call is made on a UDP socket with data on the receive queue, data will be
    returned. If the amount of data requested, [[n]], is less than the amount of data in the
    datagram on the head of the receive queue, then on Linux and BSD, this amount of data is
    returned. On Windows, all of the data in the datagram is returned, but only when the amount of
    requested data is equal to or greater than the amount of data in the first datagram.

    If the [[MSG_PEEK]] flag is set then the datagram is left on the receive queue, otherwise it is
    removed, even if only some of the data it contains has been read.

   :*)

    )

/\

    (!h ts tid d socks sid sock
      fd n0 opts0 n opts fid ff h0
      sf is1 is2 ps1 ps2 p1' cantsndmore bound
      SS MM.

    recv_12 /* rp_udp, block (*: Block, entering [[Recv2]] state as no datagrams available on socket :*) */
      (h0,SS,MM)
    -- Lh_call (tid,recv(fd,n0,opts0)) -->
      (h0 with <| ts := FUPDATE ts (tid,Timed(Recv2(sid,n,opts),never_timer));
                 socks := h0.socks |++
                          [(sid,sock with <| ps1 := SOME p1' |>)];
                 bound := bound |>,
      SS,MM)

    <==

      h0 = h with <| ts := FUPDATE ts (tid,Timed(Run,d));
                     socks := socks |++
                              [(sid,sock)] |>  /\
      fd IN FDOM h0.fds /\
      fid = h0.fds ' fd /\
      FAPPLY h0.files fid = File(FT_Socket(sid),ff) /\
      sock = Sock(SOME fid,sf,is1,ps1,is2,ps2,NONE,cantsndmore,F,UDP_Sock([])) /\
      p1' IN autobind(sock.ps1,PROTO_UDP,h0,h0.socks) /\
      (if sock.ps1 = NONE then bound = sid::h0.bound else bound = h0.bound) /\
      ~((MSG_DONTWAIT IN opts /\ linux_arch h.arch) \/ ff.b(O_NONBLOCK)) /\
      (bsd_arch h.arch ==> ~(n=0)) /\
      n = clip_int_to_num n0 /\
      opts = LIST_TO_SET opts0



    (*:

     @description

     Consider a UDP socket [[sid]], referenced by [[fd]], that has no pending errors, is not
     shutdown for reading, has an empty receive queue, and does not have its [[O_NONBLOCK]] flag
     set. The socket is either bound to a local port [[SOME p1']] or can be autobound to a local
     port [[SOME p1']]. From thread [[tid]], which in the [[Run]] state, a [[recv(fd,n0,opts0)]] call
     is made. Because there are no datagrams on the socket's receive queue, the call will block.

     A [[Lh_call(tid,recv(fd,n0,opts0))]] transition will be made, leaving the thread state
     [[Recv2(sid,n,opts)]]. If autobinding occurred then [[sid]] will be placed on the head of the
     host's list of bound sockets: [[bound = sid::h0.bound]].

     @variation FreeBSD

     As above, with the added condition that the number of bytes requested to be read is not zero.

     @variation Linux

     As above, with the added condition that the [[MSG_DONTWAIT]] flag is not set in [[opts0]].

     @modeldetails

     The amount of data requested, [[n0]], is clipped to a natural number [[n]] from an integer, using
     [[clip_int_to_num]]. POSIX specifies an unsigned type for [[n0]] and this is one possible model
     thereof.

     The [[opts0]] argument to [[recv()]] is of type [[msgbflag list]], but it is converted to a
     set, [[opts]], using [[LIST_TO_SET]].

     @internal

     The autobinding can be observed by guessing the next ephemeral port.

     :*)

    )

/\

    (!h ts tid d socks sid s h0
      n opts0 opts ff fd fid
      SS MM.

    recv_13 /* rp_udp, fast fail (*: Fail with [[EAGAIN]]: call would block and socket is non-blocking or, on Linux, non-blocking behaviour has been requested with the [[MSG_DONTWAIT]] flag :*) */
      (h0,SS,MM)
    -- Lh_call (tid,recv(fd,n,opts0)) -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (FAIL EAGAIN),sched_timer));
                socks := socks |++
                         [(sid,s with <| es := NONE; pr := UDP_Sock([]) |>)] |>,
      SS,MM)

    <==

      h0 = h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                     socks := socks |++
                              [(sid,s with <| es := NONE; pr := UDP_Sock([]) |>)] |> /\
      fd IN FDOM h0.fds /\
      fid = h0.fds ' fd /\
      FAPPLY h0.files fid = File(FT_Socket(sid),ff) /\
      opts = LIST_TO_SET opts0 /\
      ((MSG_DONTWAIT IN opts /\ linux_arch h.arch) \/ ff.b(O_NONBLOCK))



    (*:


     @description

     Consider a UDP socket [[sid]] referenced by [[fd]]. It has no pending errors, and an empty
     receive queue. The socket is non-blocking: its [[O_NONBLOCK]] flag has been set. From thread
     [[tid]], in the [[Run]] state, a [[recv(fd,n,opts0)]] call is made. The call would block
     because the socket has an empty receive queue, so the call fails with an [[EAGAIN]] error.

     A [[Lh_call(tid,recv(fd,n,opts0))]] transition is made, leaving the thread state [[Ret
     (FAIL EAGAIN)]].

     @variation Linux

     As above, but the rule also applies if the socket's [[O_NONBLOCK]] flag is not set but the
     [[MSG_DONTWAIT]] flag is set in [[opts0]]. Also, note that [[EWOULDBLOCK]] and [[EAGAIN]] are
     aliased on Linux.

     @modeldetails

     The [[opts0]] argument is of type [[list]]. In the model it is converted to a [[set]] [[opts]]
     using [[LIST_TO_SET]].

     @internal

     Note that in Linux [[ \tscon{EWOULDBLOCK}]] and [[EAGAIN ]] are aliased.

     Note that in Linux we can set the [[MSG_DONTWAIT]] flag if we would like non-blocking behaviour
     for our [[recv]] call, but on BSD and Windows this flag is ignored.  :*)

    )

/\

    (!h ts tid d socks h0
      sid fid sf n opts e fd ff cantsndmore cantrcvmore
      SS MM.

    recv_14 /* rp_udp, fast fail (*: Fail with [[EAGAIN]], [[EADDRNOTAVAIL]], or [[ENOBUFS]]: there are no ephemeral ports left :*) */
      (h0,SS,MM)
    -- Lh_call (tid,recv(fd,n,opts)) -->
      (h0 with <| ts := FUPDATE ts (tid, Timed(Ret (FAIL e),sched_timer)) |>,SS,MM)

    <==

      h0 = h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                     socks := socks |++
                              [(sid, Sock(SOME fid,sf,NONE,NONE,NONE,NONE,NONE,cantsndmore,cantrcvmore,UDP_Sock([])))] |> /\
      autobind(NONE,PROTO_UDP,h0,h0.socks) = EMPTY /\
      e IN {EAGAIN; EADDRNOTAVAIL; ENOBUFS} /\
      fd IN FDOM h0.fds /\
      fid = h0.fds ' fd /\
      FAPPLY h0.files fid = File(FT_Socket(sid),ff)


    (*:

     @description

     Consider a UDP socket [[sid]], referenced by [[fd]]. The socket has no pending errors, an empty
     receive queue, and binding quad [[NONE,NONE,NONE,NONE]]. From thread [[tid]], which is in the
     [[Run]] state, a [[recv(fd,n,opts)]] call is made. There is no ephemeral port to autobind the
     socket to, so the call fails with either [[EAGAIN]], [[EADDRNOTAVAIL]] or [[ENOBUFS]].

     A [[Lh_call(tid,recv(fd,n,opts))]] transition is made, leaving the thread state [[Ret (FAIL
     e)]] where e is one of the above errors.

     @internal

     See remark for [[connect_5c]].

     :*)

    )

/\

    (!h ts tid sid n opts d socks sock data'
      p1 rcvq rcvq' i3 ps3 data rcvq'' b
      SS MM.

    recv_15 /* rp_udp, slow urgent succeed (*: Blocked call returns from [[Recv2]] state with data :*) */
      (h with <| ts := FUPDATE ts (tid, Timed(Recv2(sid,n,opts),d));
                socks := socks |++
                         [(sid,sock with <| ps1 := SOME p1; es := NONE; pr := UDP_Sock(rcvq) |>)] |>,
      SS,MM)
    -- Lh_tau -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (OK(IMPLODE data',SOME ((i3,ps3),b))),sched_timer));
                socks := socks |++
                         [(sid, sock with <| ps1 := SOME p1; es := NONE; pr := UDP_Sock(rcvq') |>)] |>,
      SS,MM)

    <==

      rcvq = (Dgram_msg(<| is := i3; ps := ps3; data := data |>))::rcvq'' /\
      (rcvq' = if MSG_PEEK IN opts then rcvq else rcvq'') /\
      ((LENGTH data <= n /\ data=data') \/
       (LENGTH data > n /\ ~(windows_arch h.arch) /\ data' = TAKE n data' /\ LENGTH data' = n (* Is this needed given some info about what TAKE does? *))) /\
      (windows_arch h.arch ==> b=T)


    (*:

     @description

     Consider a UDP socket [[sid]] with no pending errors and bound to local port [[p1]]. At the
     head of the socket's receive queue, [[rcvq]], is a UDP datagram with source address
     [[(i3,ps3)]] and data [[data]]. Thread [[tid]] is blocked in state [[Recv2(sid,n,opts)]].

     The blocked call successfully returns [[(IMPLODE data',SOME((i3,ps3,b)))]]. If the number of
     bytes requested, [[n]], is greater than or equal to the number of bytes of data in the
     datagram, [[data]], then all of [[data]] is returned. If [[n]] is less than the number of bytes
     in the datagram, then the first [[n]] bytes of data are returned.

     A [[Lh_tau]] transition is made, leaving the thread state [[Ret (OK(IMPLODE
     data',SOME((i3,ps3),b)))]]. If the [[MSG_PEEK]] flag was set in [[opts]] then the datagram
     stays on the head of the socket's receive queue; otherwise, it is discarded from the receive
     queue.

     @variation WinXP

     As above, except the number of bytes of data requested [[n]], must be greater than or equal to
     the length in bytes of [[data]]. The boolean [[b]] equals [[T]], indicating that all of the
     datagram's data was read.

     @internal

     Note that the [[Recv2]] state can only be entered by the [[recv_12]] rule, so we have [[ps1=
     SOME p1]].  :*)

    )

/\

   (!h ts tid d socks sid sock
     udp fd n0 opts0 opts fid ff
     SS MM.

   recv_16 /* rp_udp, fast fail (*: Fail with [[EOPNOTSUPP]]: [[MSG_WAITALL]] flag not supported on WinXP, or [[MSG_OOB]] flag not supported on FreeBSD and WinXP :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| pr := UDP_PROTO(udp) |>)] |>,
     SS,MM)
   -- Lh_call (tid,recv(fd,n0,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EOPNOTSUPP),sched_timer));
               socks := socks |++
                        [(sid,sock with <| pr := UDP_PROTO(udp) |>)] |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     opts = LIST_TO_SET opts0 /\
     (MSG_WAITALL IN opts /\ windows_arch h.arch)


   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]]. From thread [[tid]], in the [[Run]] state, a
    [[recv(fd,n0,opts0)]] call is made. The [[MSG_OOB]] or [[MSG_WAITALL]] flags are set in
    [[opts0]]. The call fails with an [[EOPNOTSUPP]] error.

    A [[Lh_call(tid,recv(fd,n0,opts0))]] transition is made, leaving the thread state [[Ret (FAIL
    EOPNOTSUPP)]].

    @variation Posix

    As above, except the rule only applies when [[MSG_OOB]] is set in [[opts0]].

    @variation FreeBSD

    As above, except the rule only applies when [[MSG_OOB]] is set in [[opts0]].

    @variation Linux

    This rule does not apply.

    @modeldetails

    The [[opts0]] argument is of type [[list]]. In the model it is converted to a [[set]] [[opts]]
    using [[LIST_TO_SET]].

    @internal

    Out-of-band data is not supported with UDP on BSD and XP. On Linux the [[MSG_OOB]] flag is
    ignored and the call is treated as a normal [[recv()]].

   :*)

   )

/\

  (!h ts tid d socks sid sock rcvq
    fd n0 opts0 fid ff ret rc b
    SS MM.

  recv_17 /* rp_udp, rc (*: Socket shutdown for reading: fail with [[ESHUTDOWN]] on WinXP or succeed on Linux and FreeBSD :*) */
    (h with <| ts:= FUPDATE ts (tid, Timed(Run,d));
              socks := socks |++
                       [(sid,sock with <| cantrcvmore := T; pr := UDP_Sock(rcvq) |>)] |>,
    SS,MM)
    -- Lh_call (tid, recv(fd,n0,opts0)) -->
    (h with <| ts := FUPDATE ts (tid, Timed(Ret (ret),sched_timer));
              socks := socks |++
                       [(sid,sock with <| cantrcvmore := T; pr := UDP_Sock(rcvq) |>)] |>,
    SS,MM)

  <==

    fd IN FDOM h.fds /\
    fid = h.fds ' fd /\
    FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
    if      windows_arch h.arch then ret = FAIL(ESHUTDOWN) /\ rc = fast fail
    else if bsd_arch     h.arch then ret = OK("",SOME((NONE,NONE),b)) /\ rc = fast succeed /\
    sock.es = NONE
    else if linux_arch   h.arch then
        rcvq = [] /\ ret = OK("",SOME((NONE,NONE),b)) /\ rc = fast succeed /\ sock.es = NONE
    else ASSERTION_FAILURE "recv_17" (* never happens *)


  (*:

   @description

   Consider a UDP socket [[sid]], referenced by [[fd]], that has been shutdown for reading. From
   thread [[tid]], which is in the [[Run]] state, a [[recv(fd,n0,opts0)]] call is made. On FreeBSD
   and Linux, if the socket has no pending error the call is successfully, returning
   [[("",SOME((NONE,NONE),b))]]; on WinXP the call fails with an [[ESHUTDOWN]] error.

   A [[Lh_call(tid,recv(fd,n0,opts0))]] transition is made, leaving the thread state [[Ret
   (OK("",SOME((NONE,NONE),b)))]] on FreeBSD and Linux, or [[Ret (FAIL ESHUTDOWN)]] on WinXP.

   @variation FreeBSD

   As above: the call succeeds.

   @variation Linux

   As above: the call succeeds with the additional condition that the socket has an empty receive
   queue.

   @variation WinXP

   As above: the call fails with an [[ESHUTDOWN]] error.

   @internal

   If a UDP socket has been shutdown for reading, then calling [[recv]] will return an empty string
   on BSD with no address returned. On Windows it will fail with the [[ESHUTDOWN]] error. On Linux
   it will succeed by returning the empty string. If there is a datagram on the receive queue, it
   will return the source address of it.

  :*)

  )

/\

   (!h ts tid d socks sid sock data' lbl rc t
     rcvq fid sf is1 p1 is2 ps2
     cantsndmore cantrcvmore rcvq' i3 ps3 data rcvq''
     SS MM.

   recv_20 /* rp_udp, rc (*: Successful partial read of datagram on head of socket's receive queue on WinXP :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(t,d));
               socks := socks |++
                        [(sid,sock with <| pr := UDP_Sock(rcvq) |>)] |>,
     SS,MM)
   -- lbl -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK(IMPLODE data',SOME((i3,ps3),F))), sched_timer));
               socks := socks |++
                        [(sid,sock)] |>,
     SS,MM)

   <==

     windows_arch h.arch /\
     rcvq = (Dgram_msg(<| is := i3; ps := ps3; data := data |>))::rcvq'' /\
     sock = Sock(SOME fid,sf,is1,SOME p1,is2,ps2,NONE,cantsndmore,cantrcvmore,UDP_Sock(rcvq')) /\
     ((?fd ff n n0 opts0.
          fd IN FDOM h.fds /\
          fid = h.fds ' fd /\
          FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
          (rcvq' = if MSG_PEEK IN (LIST_TO_SET opts0) then rcvq else rcvq'') /\
          n = clip_int_to_num n0 /\
          n < LENGTH data /\
          data' = TAKE n data /\
          t = Run /\
          rc = fast succeed /\
          lbl = Lh_call (tid,recv(fd,n0,opts0))) \/
      (?n opts.
          lbl = Lh_tau  /\
          t = Recv2(sid,n,opts) /\
          rc = slow urgent succeed /\
          data' = TAKE n data /\
          n < LENGTH data /\
          rcvq' = if MSG_PEEK IN opts then rcvq else rcvq''))


   (*:

   @description

   On WinXP, consider a UDP socket [[sid]] bound to a local port [[p1]] and with no pending
   errors. At the head of the socket's receive queue is a datagram with source address [[is := i3;
   ps := ps3]] and data [[data]]. This rule covers two cases:

   In the first, from thread [[tid]], which is in the [[Run]] state, a [[recv(fd,n0,opts0)]] call is
   made where [[fd]] refers to the socket [[sid]]. The amount of data to be read, [[n0]] bytes, is
   less than the number of bytes of data in the datagram, [[data]]. The call successfully returns
   the first [[n0]] bytes of data from the datagram, [[data']]. A [[Lh_call(tid,recv(fd,n0,opts0))]]
   transition is made leaving the thread state [[Ret (OK(IMPLODE data',SOME((i3,ps3),F)))]] where
   the [[F]] indicates that not all of the datagram's data was read. The datagram is discarded from
   the socket's receive queue unless the [[MSG_PEEK]] flag was set in [[opts0]], in which case the
   whole datagram remains on the socket's receive queue.

   In the second case, thread [[tid]] is blocked in state [[Recv2(sid,n,opts)]] where the number of
   bytes to be read, [[n]], is less than the number of bytes of data in the datagram. There is now
   data to be read so a [[Lh_tau]] transition is made, leaving the thread state [[Ret (OK(IMPLODE
   data',SOME((i3,ps3),F)))]] where the [[F]] indicated that not all of the datagram's data was
   read. The datagram is discarded from the socket's receive queue unless the [[MSG_PEEK]] flag was
   set in [[opts]], in which case the whole datagram remains on the socket's receive queue.

   @variation Posix

   This rule does not apply.

   @variation FreeBSD

   This rule does not apply.

   @variation Linux

   This rule does not apply.

   @modeldetails

   The amount of data requested, [[n0]], is clipped to a natural number from an integer, using
   [[clip_int_to_num]]. POSIX specifies an unsigned type for [[n0]] and this is one possible model
   thereof.

   The data itself is represented as a [[byte list]] in the datagram but is returned a [[string]],
   so the [[IMPLODE]] function is used to do the conversion.

   In the model the return value is [[OK(IMPLODE data',SOME((i3,p3),F))]] where the [[F]] represents
   not all the data in the datagram at the head of the socket's receive queue being read. What
   actually happens is that an [[EMSGSIZE]] error is returned, and the data is put into the read
   buffer specified when the [[recv()]] call was made.

   @internal

   On Windows, calling [[recv]] on a UDP socket with the amount of data requested less than the
   amount of data in the first datagram on the socket's receive queue fails with an [[EMSGSIZE]]
   error. However, the data is still placed in the buffer passed in the [[recv()]] call. The
   datagram is discarded from the socket's receive queue.

   :*)

   )

/\

   (!h ts tid d socks sid sock b
     fd n0 opts0 fid ff
     SS MM.

   recv_21 /* rp_udp, fast succeed (*: Read zero bytes of data from an empty receive queue on FreeBSD :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| pr := UDP_Sock([]) |>)] |>,
     SS,MM)
   -- Lh_call (tid,recv(fd,n0,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK("",SOME((NONE,NONE),b))),sched_timer));
               socks := socks |++
                        [(sid,sock with <| pr := UDP_Sock([]) |>)] |>,
     SS,MM)

   <==

     bsd_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     0 = clip_int_to_num n0


   (*:

    @description

    On FreeBSD, consider a UDP socket [[sid]], referenced by [[fd]], with an empty receive
    queue. From thread [[tid]], which is in the [[Run]] state, a [[recv(fd,n0,opts0)]] call is made
    where [[n0 = 0]]. The call succeeds, returning the empty string and not specifying an address:
    [[OK("",SOME((NONE,NONE),b))]].

    A [[Lh_call(tid,recv(fd,n0,opts0))]] transition is made, leaving the thread  state
    [[Ret (OK("",SOME((NONE,NONE),b)))]].

    @variation Posix

    This rule does not apply: see rules [[recv_12]] and [[recv_13]].

    @variation Linux

    This rule does not apply: see rules [[recv_12]] and [[recv_13]].

    @variation WinXP

    This rule does not apply: see rules [[recv_12]] and [[recv_13]].

    @internal

    On BSD, calling [[recv]] requesting zero bytes on a UDP socket with no datagrams in the receive
    queue succeeds with an empty string and no address specified. On Linux and Windows this call
    would block waiting for a datagram to arrive: see rule [[recv_12]].

   :*)

   )

/\

   (!h ts tid d socks sid sock udp fd n0 opts0 fid ff
     SS MM.

   recv_22 /* rp_udp, fast fail (*: Fail with [[EINVAL]] on WinXP: socket is unbound :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| ps1 := NONE; pr := UDP_PROTO(udp) |> )] |>,
     SS,MM)
   -- Lh_call (tid,recv(fd,n0,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINVAL),sched_timer));
               socks := socks |++
                        [(sid,sock with <| ps1 := NONE; pr := UDP_PROTO(udp) |> )] |>,
     SS,MM)

   <==

     windows_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff)


   (*:

    @description

    On WinXP, consider a UDP socket [[sid]] referenced by [[fd]] that is not bound to a local
    port. A [[recv(fd,n0,opts0]] call is made from thread [[tid]] which is in the [[Run]] state. The
    call fails with an [[EINVAL]] error.

    A [[Lh_call(tid,recv(fd,n0,opts0))]] transition is made, leaving the thread state
    [[Ret (FAIL EINVAL)]].

    @variation Posix

    This rule does not apply.

    @variation FreeBSD

    This rule does not apply.

    @variation Linux

    This rule does not apply.

   :*)


   )

/\

   (!h ts tid d socks sid sock rcvq err rcvq' t lbl rc
     SS MM.

   recv_23 /* rp_udp, rc (*: Read ICMP error from receive queue and fail with that error on WinXP :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(t,d));
               socks := socks |++
                        [(sid,sock with <| pr := UDP_Sock(rcvq) |>)] |>,
     SS,MM)
   -- lbl -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err), sched_timer));
               socks := socks |++
                        [(sid,sock with <| pr := UDP_Sock(rcvq') |>)] |>,
     SS,MM)

   <==

     windows_arch h.arch /\
     rcvq = (Dgram_error(<| e := err |>))::rcvq' /\
    ((?fd n0 opts0 fid ff. t = Run /\
                           lbl = Lh_call(tid,recv(fd,n0,opts0)) /\
                           rc = fast fail /\
                           fd IN FDOM h.fds /\
                           fid = h.fds ' fd /\
                           FAPPLY h.files fid = File(FT_Socket(sid),ff)) \/
     (?n opts. t = Recv2(sid,n,opts) /\
               lbl = Lh_tau /\
               rc = slow urgent fail))


   (*:

    @description

    On WinXP, consider a UDP socket [[sid]] referenced by [[fd]]. At the head of the socket's
    receive queue, [[rcvq]], is an ICMP message with error [[err]]. This rule covers two cases.

    In the first, thread [[tid]] is in the [[Run]] state and a [[recv(fd,n0,opts0)]] call is
    made. The call fails with error [[err]], making a [[Lh_call(tid,recv(fd,n0,opts0))]] transition.
    This leaves the thread state [[Ret (FAIL err)]], and the socket with the ICMP message removed
    from its receive queue.

    In the second case, thread [[tid]] is blocked in state [[Recv2(sid,n0,opts0)]]. A [[Lh_tau]]
    transition is made, leaving the thread state [[Ret (FAIL err)]], and the socket with the ICMP
    message removed from its receive queue.

    @variation Posix

    This rule does not apply.

    @variation FreeBSD

    This rule does not apply.

    @variation Linux

    This rule does not apply.

   :*)


   )

/\

   (!h ts tid d socks sid fid i1 p1 is2 ps2 e cantsndmore cantrcvmore udp fd n0 opts0 es ff opts sf
     SS MM.

    recv_24 /* rp_udp, fast fail (*: Fail with pending error :*) */
      (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
                socks := socks |++
                 [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,is2,ps2,SOME e,cantsndmore,cantrcvmore,UDP_PROTO(udp)))] |>,
      SS,MM)
    -- Lh_call (tid,recv(fd,n0,opts0)) -->
      (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer));
                socks := socks |++
                 [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,is2,ps2,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))] |>,
      SS,MM)

    <==

      fd IN FDOM h.fds /\
      fid = h.fds ' fd /\
      FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
      opts = LIST_TO_SET opts0 /\
      (~linux_arch h.arch ==> ?p2.ps2 = SOME p2) /\
      es = if MSG_PEEK IN opts then SOME e else NONE


    (*:

     @description

     From thread [[tid]], which is in the [[Run]] state, a [[recv(fd,n0,opts0)]] call is made.
     [[fd]] refers to a UDP socket that has local address [[(SOME i1,SOME p1)]], has its peer port
     set: [[ps2 = SOME p2]], and has pending error [[SOME e]].

     The call fails returning the pending error: a [[Lh_call(tid,recv(fd,n0,opts0))]] transition is
     made leaving the thread state [[Ret (FAIL EAGAIN)]]. If the [[MSG_PEEK]] flag was set in
     [[opts0]] then the socket's pending error remains, otherwise it is cleared.

     @variation Linux

     The socket need not have its peer port set.

     @modeldetails

     The [[opts0]] argument to [[recv()]] is of type [[msgbflag list]], but it is converted to a
     set, [[opts]], using [[LIST_TO_SET]].


    :*)

)

/\

(*:

@section [[tcp_send]] TCP [[send()]]
 \[ <[send: fd * (ip * port) option * string * msgbflag list -> string ]> \]

  This section describes
  the behaviour of [[send()]] for TCP sockets.
  A call to [[send(fd,NONE,data,flags)]] enqueues data on the TCP socket's send queue.
  Here
  [[fd]] is a file descriptor referring to the TCP socket to enqueue data on.
  The second argument, of type [[(ip * port) option]], is the destination address of the data for UDP, but for
  a TCP socket it should be set to [[NONE]] (the socket must be
  connected to a peer before [[send()]] can be called).
  The   [[data]] is the data to be sent.
  Finally, [[flags]] is a list of flags for the [[send()]] call; possible flags are: [[MSG_OOB]], specifying
  that the data to be sent is out-of-band data, and [[MSG_DONTWAIT]], specifying that non-blocking
  behaviour is to be used for this call. The [[MSG_WAITALL]] and [[MSG_PEEK]] flags may also be set,
  but as they are meaningless for [[send()]] calls, FreeBSD ignores them, and Linux and WinXP fail
  with [[EOPNOTSUPP]].
  The returned [[string]] is any data that was not sent.

  For a successful [[send()]] call, the socket must be in a synchronised state, must not be shutdown
  for writing, and must not have a pending error.

  If there is not enough room on a socket's send queue then a [[send()]] call may block until space
  becomes available. For a successful blocking [[send()]] call on FreeBSD the entire string will be
  enqueued on the socket's send queue.

@errors

  In addition to errors returned via ICMP (see {@link [[deliver_in_icmp_3]]}), a call to [[send()]]
  can fail with the errors below, in which case the corresponding exception is raised:

  @error [[EAGAIN]] Non-blocking [[send()]] call would block.

  @errorinclude [[misc]] [[EBADF]]

  @errorinclude [[misc]] [[EINTR]]

  @error [[ENOTCONN]] Socket not connected on FreeBSD and WinXP.

  @errorinclude [[misc]] [[ENOTSOCK]]

  @error [[EOPNOTSUPP]] Message flags [[MSG_PEEK]] and [[MSG_WAITALL]] not supported. Linux and WinXP.

  @error [[EPIPE]] Socket not connected on Linux; or socket shutdown for writing on FreeBSD and Linux.

  @error [[ESHUTDOWN]] Socket shutdown for writing on WinXP.

@commoncases

  A TCP socket is created and successfully connects with a peer; data is then sent to the peer:
  [[socket_1]]; [[return_1]]; [[connect_1]]; [[return_1]]; $\dots $ [[connect_2]]; [[return_1]];
  [[send_1]]; $\dots $

@api

  \begin{tabular}{ll}
    Posix:  &  |ssize_t send(int socket, const void *buffer, size_t length, int flags);| \\
    FreeBSD:&  |ssize_t send(int s, const void *msg, size_t len, int flags);| \\
    Linux:  &  |int send(int s, const void *msg, size_t len, int flags);| \\
    WinXP:  &  |int send(SOCKET s, const char *buf, int len, int flags);| \\
  \end{tabular}\\

  In the Posix interface:
  \begin{itemize}

    \item |socket| is the file descriptor of the socket to send from, corresponding to the
     [[fd]] argument of the model [[send()]].

    \item |message| is a pointer to the data to be sent of length |length|. The two
     together correspond to the [[string]] argument of the model [[send()]].

    \item |flags| is a disjunction of the message flags for the [[send()]] call, corresponding to
     the [[msgbflag]] [[list]] in the model [[send()]].

     \item the returned |ssize_t| is either non-negative or |-1|. If it is
     non-negative then it is the amount of data from |message| that was sent. If it is
     |-1| then it indicates an error, in which case the error is stored in
     |errno|. This corresponds to the model [[send()]]'s return value of type [[string]]
     which is the data that was not sent. On WinXP an error is indicated by a return value of
     |SOCKET_ERROR|, not |-1|, with the actual error code available through a
     call to |WSAGetLastError()|.

  \end{itemize}

  The FreeBSD, Linux and WinXP interfaces are similar modulo argument renaming, except where
  noted above.

@modeldetails

  If the call blocks then the thread enters state [[Send2(sid,NONE,str,opts)]] (the optional
  parameter is used for UDP only), where

  \begin{itemize}

    \item [[sid : sid]] is the identifier of the socket that made the [[send()]] call,

    \item [[str : string]] is the data to be sent, and

    \item [[opts : msgbflag list]] is the set of options for the [[send()]] call.

  \end{itemize}

  The following errors are not modelled:

  \begin{itemize}

    \item In Posix and on all three architectures, |EDESTADDRREQ| indicates that the socket is not
    connection-mode and no peer address is set.  This doesn't apply to TCP, which is a
    connection-mode protocol.

   \item In Posix, |EACCES| signifies that write access to the socket is denied. This is not
   modelled here.

   \item On FreeBSD and Linux, |EFAULT| signifies that the pointers passed as either the |address| or
   |address_len| arguments were inaccessible.  This is an artefact of the C interface to
   [[accept()]] that is excluded by the clean interface used in the model.

    \item In Posix and on Linux, |EINVAL| signifies that an invalid argument was passed. The typing
     of the model interface prevents this from happening.

    \item In Posix, |EIO| signifies that an I/O error occurred while reading from or writing to the
    file system. This is not modelled.

    \item On Linux, |EMSGSIZE| indicates that the message is too large to be sent all at once, as
    the socket requires; this is not a requirement for TCP sockets.

    \item In Posix, |ENETDOWN| signifies that the local network interface used to reach the
    destination is down. This is not modelled.

  \end{itemize}

  The following flags are not modelled:

  \begin{itemize}

  \item On Linux, |MSG_CONFIRM| is used to tell the link layer not to probe the neighbour.

  \item On Linux, |MSG_NOSIGNAL| requests not to send |SIGPIPE| errors on stream-oriented sockets
  when the other end breaks the connection.

  \item On FreeBSD and WinXP, |MSG_DONTROUTE| is used by routing programs.

  \item On FreeBSD, |MSG_EOR| is used to indicate the end of a record for protocols that support
   this. It is not modelled because TCP does not support records.

   \item On FreeBSD, |MSG_EOF| is used to implement Transaction TCP which is not modelled here.

  \end{itemize}

:*)


   (!h ts tid d
     fd opts0 opts fid sid socks ff sf i1 p1 cb
     i2 p2 cantrcvmore
     str str' str'' space st
     flgs SS s s' MM.

   send_1 /* rp_tcp, fast succeed (*: Successfully send data without blocking :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,NONE,F,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s)],MM)
   -- Lh_call (tid,send(fd,NONE,IMPLODE str,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (IMPLODE str'')),sched_timer));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,NONE,F,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2), s')],MM)

   <==

     st IN {ESTABLISHED; CLOSE_WAIT} /\
     opts = LIST_TO_SET opts0 /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\

     space IN UNIV /\ (* REMARK perhaps remove [[send_queue_space]] from Spec3 *)

     ({MSG_PEEK; MSG_WAITALL} INTER opts = EMPTY \/ bsd_arch h.arch) /\

     (if space >= LENGTH str then
	 str'=str /\ str''=[]
     else
	 (ff.b(O_NONBLOCK) \/ (MSG_DONTWAIT IN opts /\ ~bsd_arch h.arch)) /\
	 (if bsd_arch h.arch then space >= sf.n(SO_SNDLOWAT)
	  else                    space >  0) /\
	 (str',str'') = SPLIT space str
     ) /\

     flgs = flgs with <| SYN := F; SYNACK := F; FIN := F; RST := F |> /\
     write (i1,p1,i2,p2) (flgs,str') s s'


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[send(fd,NONE,IMPLODE str,opts0)]] call
    is made. [[fd]] refers to a TCP socket [[sid]] that has binding quad [[(SOME i1,SOME p1,SOME
    i2,SOME p2)]], has no pending error, is not shutdown for writing, and is in state
    [[ESTABLISHED]] or [[CLOSE_WAIT]]. The [[MSG_PEEK]] and [[MSG_WAITALL]] flags are not set in
    [[opts0]]. [[space]] is the space in the socket's send queue, calculated using {@link
    [[send_queue_space]]}.

    This rule covers two cases: (1) there is space in the socket's send queue for all the data; and
    (2) there is not space for all the data but the call is non-blocking (the [[MSG_DONTWAIT]] flag
    is set in [[opts]] or the socket's [[O_NONBLOCK]] flag is set), and the space is greater than
    zero, or, on FreeBSD, greater than the minimum number of bytes for [[send()]] operations on the
    socket, [[sf.n(SO_SNDLOWAT)]].

    In (1) all of the data [[str]] is appended to the socket's send queue and the returned
    string, [[str'']], is the empty string. In (2), the first [[space]] bytes of data, [[str']], are
    appended to the socket's send queue and the remaining data, [[str'']], is returned.

    In both cases a [[Lh_call(tid,send(fd,NONE,IMPLODE str,opts0))]] transition is made,
    leaving the thread state [[Ret (OK (IMPLODE str''))]]. If the data was marked as out-of-band,
    [[MSG_OOB IN opts]], then the socket's send urgent pointer will point to the end of the send
    queue.

    @variation FreeBSD

    The [[MSG_PEEK]] and [[MSG_WAITALL]] flags may be set in [[opts0]] but for the call to be
    non-blocking the socket's [[O_NONBLOCK]] flag must be set: the [[MSG_DONTWAIT]] flag has no
    effect.

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.

    The [[opts0]] argument is of type [[list]]. In the model it is converted to a [[set]] [[opts]]
    using [[LIST_TO_SET]]. The presence of [[MSG_PEEK]] is checked for in [[opts]] rather than in
    [[opts0]].

    @internal

    TODO: if MSG\_OOB in opts, should invoke tcp\_output with force\_output=T immediately

    Attempt to send data through a socket.  The socket must be connected, and only valid message
    options may be used.  We must not have already shut down this half of the connection.  There
    must be space remaining in the queue; note that out-of-band data gets special treatment here.
    We decide on [[n]], the number of bytes to accept onto the queue (at least [[SO_SNDLOWAT]] and
    at most the remaining space), and then append the first [[n]] bytes to the queue, returning the
    remainder.  We also set the send urgent pointer if necessary.

    Notice that in the rule above, if we send everything, we store / advance the OOB pointer.

    Our internal representation of the OOB pointer is akin to that of BSD, in that we point to the
    byte after the OOB byte (rather than the OOB byte itself).

    We really do not know when the OOB gets set.  Consider:

    [[send("ABCD",MSG_OOB)]]  returns 2
    [[send("XY",MSG_OOB)]] returns 2.... OOPS!!

    or, worse,

    [[send("ABCD",MSG_OOB)]] returns 2
    [[send("XY",0)]] returns 2..... !!!!!

    It seems reasonable only to set the OOB pointer when the D is written to the queue, but who
    knows if that is what is really done.

   :*)

   )

/\

   (!h ts tid d
     fd opts0 opts fid sid ff sf i1 p1 cb
     i2 p2 cantrcvmore
     str space st socks
     SS MM.

   send_2 /* rp_tcp, block (*: Block waiting for space in socket's send queue :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
	                [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,NONE,F,cantrcvmore,
		              TCP_Sock(st,cb,NONE)))] |>,
     SS,MM)
   -- Lh_call (tid,send(fd,NONE,IMPLODE str,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Send2(sid,NONE,str,opts),never_timer));
               socks := socks |++
	                [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,NONE,F,cantrcvmore,
		                   TCP_Sock(st,cb,NONE)))] |>,
     SS,MM)

   <==

     opts = LIST_TO_SET opts0 /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     ~((~bsd_arch h.arch /\  MSG_DONTWAIT IN opts) \/ ff.b(O_NONBLOCK)) /\

     space IN UNIV /\

     ({MSG_PEEK; MSG_WAITALL} INTER opts = EMPTY \/ bsd_arch h.arch)/\

     ((st IN {ESTABLISHED; CLOSE_WAIT} /\
       space < LENGTH str) \/
      (linux_arch h.arch /\ st IN {SYN_SENT; SYN_RECEIVED}))


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[send(fd,NONE,IMPLODE str,opts0)]] call
    is made. [[fd]] refers to a TCP socket [[sid]] that has binding quad [[(SOME i1,SOME p1,SOME
    i2,SOME p2)]], has no pending error, is not shutdown for writing, and is in state
    [[ESTABLISHED]] or [[CLOSE_WAIT]]. The call is a blocking one: the socket's [[O_NONBLOCK]] flag
    is not set and the [[MSG_DONTWAIT]] flag is not set in [[opts0]]. The [[MSG_PEEK]] and
    [[MSG_WAITALL]] flags are not set in [[opts0]].

    The space in the socket's send queue, [[space]] (calculated using {@link
    [[send_queue_space]]}), is less than the length in bytes of the data to be sent, [[str]].

    The call blocks, leaving the thread state [[Send2(sid,NONE,str,opts)]] via a
    [[Lh_call(tid,send(fd,NONE,IMPLODE str,opts0))]] transition.

    @variation FreeBSD

    The [[MSG_PEEK]], [[MSG_WAITALL]], and [[MSG_DONTWAIT]] flags may all be set in [[opts0]]: all
    three are ignored by FreeBSD.

    @variation Linux

    In addition to the above, the rule also applies if connection establishment is still taking
    place for the socket: it is in state [[SYN_SENT]] or [[SYN_RECEIVED]].

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.


    @internal

    Attempt to send data through a socket, but there is not sufficient space remaining in the queue
    or on Linux, the socket is still connecting.  Block until space appears (possibly forever).

   :*)

   )

/\

   (!h ts tid d
     opts socks fid sid sf i1 p1 cb
     i2 p2 cantrcvmore
     str str' str'' space st
     flgs SS s s' MM.

   send_3 /* rp_tcp, slow nonurgent succeed (*: Successfully return from blocked state having sent data :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Send2(sid,NONE,str,opts),d));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,NONE,F,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (IMPLODE str'')),sched_timer));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,NONE,F,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s')],MM)

   <==

     st IN {ESTABLISHED; CLOSE_WAIT} /\

     space IN UNIV /\

     space >= LENGTH str /\
     str'=str /\ str''=[] /\

     flgs = flgs with <| SYN := F; SYNACK := F; FIN := F; RST := F |> /\
     write (i1,p1,i2,p2) (flgs,str') s s'


   (*:

    @description

    Thread [[tid]] is blocked in state [[Send2(sid,NONE,str,opts)]] where the TCP socket [[sid]] has
    binding quad [[(SOME i1,SOME p1,SOME i2,SOME p2)]], has no pending error, is not shutdown for
    writing, and is in state [[ESTABLISHED]] or [[CLOSE_WAIT]].

    The space in the socket's send queue, [[space]] (calculated using {@link [[send_queue_space]]}),
    is greater than or equal to the length of the data to be sent, [[str]]. The data is appended to
    the socket's send queue and the call successfully returns the empty string. A [[Lh_tau]]
    transition is made, leaving the thread state [[Ret (OK "")]]. If the data was marked as
    out-of-band, [[MSG_OOB IN opts]], then the socket's urgent pointer will be updated to point to
    the end of the socket's send queue.

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.


    @internal

    If we're blocked waiting for space to appear in the send queue, and it does, then we do
    essentially the same as [[send_1]] to add the data to the send queue and return.

    SB: one may wonder what happens it we're not in [[ESTABLISHED]] or [[CLOSE_WAIT]] any longer and
    space becomes available in the send queue. After some thought I think this is impossible.

   :*)

   )

/\

   (!h ts tid sid str opts d socks fid i1 p1 i2 p2 sf
     cantrcvmore st cb
     str'' str' space
     flgs SS s s' MM.

    send_3a /* rp_tcp, block (*: From blocked state, transfer some data to the send queue and remain blocked :*) */
      (h with <| ts := FUPDATE ts (tid,Timed(Send2(sid,NONE,str,opts),d));
                socks := socks |++
		         [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,NONE,F,cantrcvmore,
				    TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
    -- Lh_tau -->
      (h with <| ts := FUPDATE ts (tid,Timed(Send2(sid,NONE,str'',opts),never_timer));
                socks := socks |++
		         [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,NONE,F,cantrcvmore,
				    TCP_Sock(st,cb,NONE)))] |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s')],MM)

    <==

      st IN {ESTABLISHED; CLOSE_WAIT} /\
      space IN UNIV /\
      space < LENGTH str /\ space > 0 /\
      (str',str'') = SPLIT space str /\

      flgs = flgs with <| SYN := F; SYNACK := F; FIN := F; RST := F |> /\
      write (i1,p1,i2,p2) (flgs,str') s s'


   (*:

    @description

    Thread [[tid]] is blocked in state [[Send2(sid,NONE,str,opts)]] where TCP socket [[sid]] has
    binding quad [[(SOME i1,SOME p1,SOME i2,SOME p2)]], has no pending error, is not shutdown for
    writing, and is in state [[ESTABLISHED]] or [[CLOSE_WAIT]]. The amount of space in the socket's
    send queue, [[space]] (calculated using {@link [[send_queue_space]]}), is less than the length
    of the remaining data to be sent, [[str]], and greater than [[0]]. The socket's send queue is
    filled by appending the first [[space]] bytes of [[str]], [[str']], to it.

    A [[Lh_tau]] transition is made, leaving the thread state [[Send2(sid,NONE,str'',opts)]]
    where [[str'']] is the remaining data to be sent. If the data in [[str]] is out-of-band,
    [[MSG_OOB]] is set in [[opts]], then the socket's urgent pointer is updated to point to the end
    of the socket's send queue.

    Note it is unclear whether or not [[MSG_OOB]] should be removed from [[opts]] in the state.

   :*)

 )

/\

   (!h ts tid d
     fd opts0 opts fid sid ff sf i1 p1 cb
     i2 p2 cantrcvmore
     str space st
     SS MM.

   send_4 /* rp_tcp, fast fail (*: Fail with [[EAGAIN]]: non-blocking semantics requested and call would block :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,send(fd,NONE,IMPLODE str,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EAGAIN),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     FAPPLY h.socks sid = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,NONE,F,cantrcvmore,
                               TCP_Sock(st,cb,NONE)) /\
     opts = LIST_TO_SET opts0 /\

     ({MSG_PEEK;MSG_WAITALL} INTER opts = EMPTY \/ bsd_arch h.arch) /\

     ((~bsd_arch h.arch /\ MSG_DONTWAIT IN opts) \/ ff.b(O_NONBLOCK)) /\

     ((st IN {ESTABLISHED; CLOSE_WAIT} /\ (* we're either established and out of queue space *)
       space IN UNIV /\
       ~(space >= LENGTH str \/ (if bsd_arch h.arch then space >= sf.n(SO_SNDLOWAT) else space > 0))) \/
      (st IN {SYN_SENT; SYN_RECEIVED} /\ (* or we're a connecting linux *)
       linux_arch h.arch))


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[send(fd,NONE,IMPLODE str,opts0)]] call
    is made. [[fd]] refers to a TCP socket that has binding quad [[(SOME i1,SOME p1,SOME i2,SOME
    p2)]], has no pending error, is not shutdown for writing, and is in state [[ESTABLISHED]] or
    [[CLOSE_WAIT]]. The call is a non-blocking one: either the socket's [[O_NONBLOCK]] flag is set
    or the [[MSG_DONTWAIT]] flag is set in [[opts0]]. The [[MSG_PEEK]] and [[MSG_WAITALL]] flags are
    not set in [[opts0]].

    The space in the socket's send queue, [[space]] (calculated using {@link [[send_queue_space]]}),
    is less than both the length of the data to send [[str]]; and on FreeBSD is less than the
    minimum number of bytes for socket send operations, [[sf.n(SO_SNDLOWAT)]], or on Linux and WinXP
    is equal to zero. The call would have to block, but because it is non-blocking, it fails with an
    [[EAGAIN]] error.

    A [[Lh_call(tid,send(fd,NONE,IMPLODE str,opts0))]] transition is made, leaving the thread in
    state [[Ret (FAIL EAGAIN)]].

    @variation FreeBSD

    For the call to be non-blocking, the socket's [[O_NONBLOCK]] flag must be set; the
    [[MSG_DONTWAIT]] flag is ignored. Additionally, the [[MSG_PEEK]] and [[MSG_WAITALL]] flags may
    be set in [[opts0]] as they are also ignored.

    @variation Linux

    This rule also applies if the socket is in state [[SYN_SENT]] or [[SYN_RECEIVED]], in which case
    the send queue size does not matter.

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.

    The [[opts0]] argument is of type [[list]]. In the model it is converted to a [[set]] [[opts]]
    using [[LIST_TO_SET]]. The presence of [[MSG_PEEK]] is checked for in [[opts]] rather than in
    [[opts0]].

    @internal

    Attempt to send data through a socket, but there's not enough space or the socket is still
    connecting (Linux).  If we requested non-blocking behaviour, return [[EAGAIN]].

   :*)

   )

/\

   (!h ts tid d
     fd str opts0 socks sock sid fid e ff addr
     SS MM.

   send_5 /* rp_tcp, fast fail (*: Fail with pending error :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| es := SOME e |>)] |>,
     SS,MM)
   -- Lh_call (tid,send(fd,addr,IMPLODE str,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer));
               socks := socks |++
                        [(sid,sock with <| es := NONE |>)] |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     proto_of sock.pr = PROTO_TCP


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[send(fd,addr,IMPLODE str,opts0)]] call
    is made. [[fd]] refers to a socket [[sock]] identified by [[sid]] with pending error [[SOME
    e]]. The call fails, returning the pending error.

    A [[Lh_call(tid,send(fd,addr,IMPLODE str,opts))]] transition is made, leaving the thread in
    state [[Ret (FAIL e)]].

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.


    @internal

    Attempt to send data through a socket, but that socket has a pending error.  Return that error
    instead, and clear the error so that (unless another error arrives in the meantime) the next
    call will succeed.

    This covers the POSIX [[ECONNRESET]] case (we intend), and also [[ENETDOWN]] and
    [[ENETUNREACH]].  The latter, because [[send()]] does no sending itself; TCP does that.  Of
    course, a smart implementation might be able to return [[ENETDOWN]] immediately.  But should it?
    Or should it treat it as a soft error and wait for the user to plug it back in?  (note that we
    already have an established connection at this point).

    Why is this only dependent on [[es]], whereas the [[recv]] analogue requires [[st =
    ESTABLISHED]] also?

   :*)

   )

/\

   (!h ts tid d
     str opts socks sock sid e
     SS MM.

   send_5a /* rp_tcp, slow urgent fail (*: Fail from blocked state with pending error :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Send2(sid,NONE,str,opts),d));
               socks := socks |++
                        [(sid,sock with <| es := SOME e |>)] |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer));
               socks := socks |++
                        [(sid,sock with <| es := NONE |>)] |>,
     SS,MM)

   <==

     proto_of sock.pr = PROTO_TCP


   (*:

    @description

    Thread [[tid]] is blocked in state [[Send2(sid,NONE,str,opts)]] from an earlier [[send()]]
    call. The TCP socket [[sid]] has pending error [[SOME e]] so the call can now return, failing
    with the error.

    A [[Lh_tau]] transition is made, leaving the thread state [[Ret (FAIL e)]].


    @internal

    A socket on which there is a blocked send() call has a pending error, causing the send() call
    to fail with that error, and the socket error to be cleared. For example, a socket under Linux
    may be still connecting and have send() called on it, in which case the call will block, but
    the connection establishment timer may expire, in which case we need to be able to fail with
    ETIMEDOUT.

    This is the TCP analogue of send_16.

    TODO: under WinXP, all pending errors on a UDP socket are ignored for a send() call - is this
          also true for TCP sockets?

   :*)

   )

/\

   (!h ts tid d
     fd str opts0 sock sid fid ff tcp_sock err
     SS MM.

   send_6 /* rp_tcp, fast fail (*: Fail with [[ENOTCONN]] or [[EPIPE]]: socket not connected :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,send(fd,NONE,IMPLODE str,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sock = (h.socks ' sid) /\
     TCP_PROTO(tcp_sock) = sock.pr /\
     sock.es = NONE /\
     (tcp_sock.st IN {CLOSED; LISTEN} \/
       (* (tcp_sock.st = FIN_WAIT_2 /\ sock.cantrcvmore = T) \/ *) (* BSD extension: SB thinks this is redundant *)
                                                                   (*                MS thinks this is crazytalk *)
       (tcp_sock.st IN {SYN_SENT; SYN_RECEIVED} /\ ~(linux_arch h.arch)) \/
        F (*: Placeholder for: if |tcp_disconnect| or |tcp_usrclose| has been invoked :*) (*... see K log p2179 *)
      ) /\
     err = (if linux_arch h.arch then EPIPE else ENOTCONN)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[send(fd,NONE,IMPLODE str,opts0)]] call
    is made. [[fd]] refers to a TCP socket [[sock]] identified by [[sid]] that does not have a
    pending error. The socket is not synchronised: it is in state [[CLOSED]], [[LISTEN]],
    [[SYN_SENT]], or [[SYN_RECEIVED]]. The call fails with an [[ENOTCONN]] error, or [[EPIPE]] on
    Linux.

    A [[Lh_call(tid,send(fd,NONE,IMPLODE str,opts0))]] transition is made, leaving the thread in
    state [[Ret (FAIL err)]] where [[err]] is one of the above errors.

    @variation Linux

    The rule does not apply if the socket is in state [[SYN_RECEIVED]] or [[SYN_SENT]].

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.


    @internal

    Attempt to send data (even if 0 bytes) through a socket that's not connected.  This is an error.

    We do not want a slow one of this: if the connection goes away, it was either aborted or cleanly
    shut down, so either [[ECONNRESET]] or [[EPIPE]].  It cannot suddenly be not ever opened.

    SB: except on Linux. Linux gives [[EPIPE]] for a send on fresh unconnected socket.  Linux also
    does not treat [[SYN_SENT]] and [[SYN_RECEIVED]]; it returns [[EAGAIN]] or blocks, whichever
    behaviour is appropriate

    SB: deals with pre-established states

    MS: no longer deals with [[TIME_WAIT]] as [[send_7]] behaviour is correct in this case (e.g. BSD returns
    [[EPIPE]])

    but the socket does not change...

   :*)
   )

/\

   (!h ts tid d
     socks sid sf is1 ps1
     is2 ps2 cantrcvmore err es rc t lbl tcp fid
     SS MM.

   send_7 /* rp_tcp, rc (*: Fail with [[EPIPE]] or [[ESHUTDOWN]]: socket shut down for writing :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(t,d));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,T,cantrcvmore,TCP_PROTO(tcp)))] |>,
     SS,MM)
   -- lbl -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer));
               socks := socks |++
                        [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,T,cantrcvmore,TCP_PROTO(tcp)))] |>,
     SS,MM)


   <==

     $\/
       (?fd ff str opts0 i2 p2.   (* fast fail case *)
	fd IN FDOM h.fds /\
	fid = h.fds ' fd /\
	FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
	t = Run /\
	lbl = Lh_call(tid,send(fd,NONE,IMPLODE str,opts0)) /\
	rc = fast fail /\
	is2 = SOME i2 /\ ps2 = SOME p2 /\
        (if tcp.st <> CLOSED then
           ?i1 p1.is1 = SOME i1 /\ ps1 = SOME p1
         else T)
       )
       (?opts str.  (* slow fail case *)
	t = Send2(sid,NONE,str,opts) /\
	lbl = Lh_tau /\
	rc = slow urgent fail
       ) /\
     (if windows_arch h.arch then err = ESHUTDOWN
      else                        err = EPIPE)


   (*:

    @description

    This rule covers two cases: (1) from thread [[tid]], which is in the [[Run]] state, a
    [[send(fd,NONE,IMPLODE str,opts0)]] call is made; and (2) thread [[tid]] is blocked in state
    [[Send2(sid,NONE,str,opts)]]. In (1), fd refers to a TCP socket [[sid]] that has binding quad
    [[(is1,ps1,SOME i2,SOME p2)]]. In both cases the socket is shutdown for writing. The call fails
    with an [[EPIPE]] error.

    The thread is left in state [[Ret (FAIL EPIPE)]], via a [[Lh_call(tid,send(fd,NONE,IMPLODE str,opts0))]] transition in (1) or a [[Lh_tau]] transition in (2).

    @variation WinXP

    The call fails with an [[ESHUTDOWN]] error instead of [[EPIPE]].

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.

    @internal

    Attempt to send data through a socket that has been shut down (for writing at least).  This is
    an error; a signal should also be generated we think.

    but the socket does not change... (?? K does not understand import of this comment).

    POSIX: This covers the first case ("The socket is shut down for writing", but not the second
    half necessariily: "the socket is connection mode and is now longer connected. In the latter
    case, and if the socket is of type [[sock_stream]] the sigpipe signal is generated to the
    calling thread.

    need a slow version of this.

    MS: This rule should be covering states [[FIN_WAIT_1]], [[FIN_WAIT_2]], [[LAST_ACK]], [[TIME_WAIT]]
    and [[CLOSING]], but could also apply if user shut down the socket for writing and the FIN has not
    been sent yet, so the condition 'cantsndmore = T' is sufficient.

   :*)
   )

/\

   (!h ts tid d
     fd str opts0 opts fid sid ff
     SS MM.

   send_8 /* rp_tcp, fast fail (*: Fail with [[EOPNOTSUPP]]:  message flag not valid :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,send(fd,NONE,IMPLODE str,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EOPNOTSUPP),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     proto_of (h.socks ' sid).pr = PROTO_TCP /\
     opts = LIST_TO_SET opts0 /\
     (MSG_PEEK IN opts \/ MSG_WAITALL IN opts) /\
     ~bsd_arch h.arch


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[send(fd,NONE,IMPLODE str,opts0)]] call
    is made. [[fd]] refers to a TCP socket identified by [[sid]]. Either the [[MSG_PEEK]] or
    [[MSG_WAITALL]] flag is set in [[opts0]]. These flags are not supported so the call fails with
    an [[EOPNOTSUPP]] error.

    A [[Lh_call(tid,send(fd,NONE,IMPLODE str,opts0))]] transition is made, leaving the thread in
    state [[Ret (FAIL EOPNOTSUPP)]].

    @variation FreeBSD

    This rule does not apply.

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.

    The [[opts0]] argument is of type [[list]]. In the model it is converted to a [[set]] [[opts]]
    using [[LIST_TO_SET]]. The presence of [[MSG_PEEK]] is checked for in [[opts]] rather than in
    [[opts0]].

    @internal

    Attempt to send data through a socket, but specifying an invalid option.  This is an error.

    Could avoid this by having two types of message options, one for send and one for recv, but
    seems overkill.  THINK ABOUT THIS.

   :*)
   )

/\

(*:

@section [[udp_send]] UDP [[send()]]
 \[ <[send: (fd * (ip * port) option * string * msgbflag list) -> string]> \]

  This section describes
  the behaviour of [[send()]] for UDP sockets.
  A call to [[send(fd,addr,data,flags)]] enqueues a UDP datagram to send to a peer.
  Here the [[fd]] argument is a file descriptor referring to a UDP socket from which to send data.
  The destination address of the data can be specified either by the [[addr]] argument, which can be
  [[SOME(i3,p3)]] or [[NONE]], or by the socket's peer address (its [[is2]] and [[ps2]] fields) if set. For a successful [[send()]], at least one of these two must be specified. If the socket
  has a peer address set and [[addr]] is set to [[SOME(i3,p3)]], then the address used is
  architecture-dependent: on FreeBSD the [[send()]] call will fail with an [[EISCONN]] error; on
  Linux and WinXP [[i3,p3]] will be used.

  The [[string]], [[data]], is the data to be sent. The length in bytes of [[data]] must be less
  than the architecture-dependent maximum payload for a UDP datagram. Sending a [[string]] of length
  zero bytes is acceptable.

  The [[msgbflag]] [[list]] is the list of message flags for the [[send()]] call. The possible flags
  are [[MSG_DONTWAIT]] and [[MSG_OOB]]. [[MSG_DONTWAIT]] specifies that non-blocking behaviour
  should be used for this call: see rules [[send_10]] and [[send_11]].  [[MSG_OOB]] specifies that
  the data to be sent is out-of-band data, which is not meaningful for UDP sockets.  FreeBSD ignores
  this flag, but on Linux and WinXP the [[send()]] call will fail: see rule [[send_20]].

  The return value of the [[send()]] call is a [[string]] of the data which was not sent. A partial
  send may occur when the call is interrupted by a signal after having sent some data.

  For a datagram to be sent, the socket must be bound to a local port. When a [[send()]] call is
  made, the socket is autobound to an ephemeral port if it does not have its local port bound.

  A successful [[send()]] call only guarantees that the datagram has been placed on the host's out
  queue. It does not imply that the datagram has left the host, let alone been successfully
  delivered to its destination.

  A call to [[send()]] may block if there is no room on the socket's send buffer and non-blocking
  behaviour has not been requested.

@errors

  In addition to errors returned via ICMP (see {@link [[deliver_in_icmp_3]]}), a call to [[send()]]
  can fail with the errors below, in which case the corresponding exception is raised:

  @error [[EADDRINUSE]] The socket's peer address is not set and the destination address specified
   would give the socket a binding quad [[i1,p1,i2,p2]] which is already in use by another
   socket.

  @error [[EADDRNOTAVAIL]] There are no ephemeral ports left for autobinding to.

  @error [[EAGAIN]] The [[send()]] call would block and non-blocking behaviour is requested. This
   may have been done either via the [[MSG_DONTWAIT]] flag being set in the [[send()]] flags or the
   socket's [[O_NONBLOCK]] flag being set.

  @error [[EDESTADDRREQ]] The socket does not have its peer address set, and no destination address
   was specified.

  @error [[EINTR]] A signal interrupted [[send()]] before any data was transmitted.

  @error [[EISCONN]] On FreeBSD, a destination address was specified and the socket has a peer
   address set.

  @error [[EMSGSIZE]] The message is too large to be sent in one datagram.

  @error [[ENOTCONN]] The socket does not have its peer address set, and no destination address was
   specified. This can occur either when the call is first made, or if it blocks and if the peer
   address is unset by a call to [[disconnect()]] whilst blocked.

  @error [[EOPNOTSUPP]] The [[MSG_OOB]] flag is set on Linux or WinXP.

  @error [[EPIPE]] Socket shut down for writing.

  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]
  @errorinclude [[misc]] [[ENOBUFS]]
  @errorinclude [[misc]] [[ENOMEM]]

@commoncases

  [[send_9]]; [[return_1]];

@api

  \begin{tabular}{ll}
    Posix:   & |ssize_t sendto(int socket, const void *message, size_t length,|\\
             & |               int flags, const struct sockaddr *dest_addr|\\
             & |               socklen_t dest_len);|\\
    FreeBSD: & |ssize_t sendto(int s, const void *msg, size_t len, int flags,|\\
             & |               const struct sockaddr *to, socklen_t tolen);| \\
    Linux:   & |int sendto(int s, const void *msg, size_t len, int flags,|\\
             & |           const struct sockaddr *to, socklen_t tolen);| \\
    WinXP:   & |int sendto(SOCKET s, const char* buf, int len, int flags,| \\
             & |           const struct sockaddr* to, int tolen);| \\
  \end{tabular}

  In the Posix interface:
  \begin{itemize}

    \item |socket| is the file descriptor of the socket to send from, corresponding to the
     [[fd]] argument of the model [[send()]].

    \item |message| is a pointer to the data to be sent of length |length|. The two
     together correspond to the [[string]] argument of the model [[send()]].

    \item |flags| is an OR of the message flags for the [[send()]] call, corresponding to
     the [[msgbflag]] [[list]] in the model [[send()]].

    \item |dest_addr| and |dest_len| correspond to the [[addr]] argument of the
     model [[send()]]. |dest_addr| is either null or a pointer to a sockaddr structure
     containing the destination address for the data. If it is null it corresponds to [[addr =
     NONE]]. If it contains an address, then it corresponds to [[addr = SOME(i3,p3)]] where [[i3]]
     and [[p3]] are the IP address and port specified in the sockaddr structure.

    \item the returned |ssize_t| is either non-negative or |-1|. If it is
     non-negative then it is the amount of data from |message| that was sent. If it is
     |-1| then it indicates an error, in which case the error is stored in
     |errno|. This is different to the model [[send()]]'s return value of type [[string]]
     which is the data that was not sent. On WinXP an error is indicated by a return value of
     |SOCKET_ERROR|, not |-1|, with the actual error code available through a
     call to |WSAGetLastError()|.

  \end{itemize}

  There are other functions used to send data on a socket. |send()| is similar to
  |sendto()| except it does not have the |address| and |address_len|
  arguments. It is used when the destination address of the data does not need to be
  specified. |sendmsg()|, another output function, is a more general form of
  |sendto()|.

@modeldetails

  If the call blocks then the thread enters state [[Send2(sid,SOME(addr,is1,ps1,is2,ps2),str,opts)]] where

  \begin{itemize}

    \item [[sid : sid]] is the identifier of the socket that made the [[send()]] call,

    \item [[addr : (ip * port) option]] is the destination address specified in the [[send()]] call,

    \item [[is1 : ip option]] is the socket's local IP address, possibly [[NONE]],

    \item [[ps1 : port option]] is the socket's local port, possibly [[NONE]],

    \item [[is2 : ip option]] is the IP address of the socket's peer, possibly [[NONE]],

    \item [[ps2 : ip option]] is the port of the socket's peer, possibly [[NONE]],

    \item [[str : string]] is the data to be sent, and

    \item [[opts : msgbflag list]] is the set of options for the [[send()]] call.

  \end{itemize}

  The following errors are not modelled:

  \begin{itemize}

   \item On FreeBSD, |EACCES| signifies that the destination address is a broadcast address and the
   |SO_BROADCAST| flag has not been set on the socket. Broadcast is not modelled here.

   \item In Posix, |EACCES| signifies that write access to the socket is denied. This is not
   modelled here.

   \item On FreeBSD and Linux, |EFAULT| signifies that the pointers passed as either the |address| or
   |address_len| arguments were inaccessible.  This is an artefact of the C interface to
   [[accept()]] that is excluded by the clean interface used in the model.

    \item In Posix and on Linux, |EINVAL| signifies that an invalid argument was passed. The typing
     of the model interface prevents this from happening.

    \item In Posix, |EIO| signifies that an I/O error occurred while reading from or writing to the
    file system. This is not modelled.

    \item In Posix, |ENETDOWN| signifies that the local network interface used to reach the
    destination is down. This is not modelled.

  \end{itemize}

  The following flags are not modelled:

  \begin{itemize}

  \item On Linux, |MSG_CONFIRM| is used to tell the link layer not to probe the neighbour.

  \item On Linux, |MSG_NOSIGNAL| requests not to send |SIGPIPE| errors on stream-oriented sockets
  when the other end breaks the connection. UDP is not stream-oriented.

  \item On FreeBSD and WinXP, |MSG_DONTROUTE| is used by routing programs.

  \item On FreeBSD, |MSG_EOR| is used to indicate the end of a record for protocols that support
   this. It is not modelled because UDP does not support records.

   \item On FreeBSD, |MSG_EOF| is used to implement Transaction TCP.

  \end{itemize}


:*)
   (!h ts tid d socks sid sock fd udp h0 bound
     addr str opts0 p1' oq' fid ff es
     SS MM.

   send_9 /* rp_udp, fast succeed (*: Enqueue datagram and return successfully :*) */
      (h0,SS,MM)
    -- Lh_call (tid,send(fd,addr,IMPLODE str,opts0)) -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (OK ("")),sched_timer));
                socks := socks |++
                         [(sid,sock with <| es := es; ps1 := SOME p1'; pr:= UDP_PROTO(udp) |>)];
                bound := bound;
                oq := oq' |>,
      SS,MM)


    <==

      h0 = h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                     socks := socks |++
                              [(sid,sock with <| es := es; pr := UDP_PROTO(udp) |>)] |> /\
      fd IN FDOM h0.fds /\
      fid = h0.fds ' fd /\
      FAPPLY h0.files fid = File(FT_Socket(sid),ff) /\
      sock.cantsndmore = F /\
      STRLEN (IMPLODE str) <= UDPpayloadMax h0.arch /\
      ((addr <> NONE) \/ (sock.is2 <> NONE)) /\
      p1' IN autobind(sock.ps1,PROTO_UDP,h0,h0.socks) /\
      (if sock.ps1 = NONE then bound = sid::h0.bound else bound = h0.bound) /\
      dosend(h.ifds,h.rttab,(addr,str),(sock.is1,SOME p1',sock.is2,sock.ps2),h0.oq,oq',T) /\
      (if bsd_arch h.arch then (h0.socks ' sid).sf.n(SO_SNDBUF) >= STRLEN (IMPLODE str)
       else T) /\
      (~(windows_arch h.arch) ==> es = NONE)


   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]] that is not shutdown for writing and has no
    pending errors. From thread [[tid]], which is in the [[Run]] state, a call
    [[send(fd,addr,IMPLODE str,opts0)]] succeeds if:

    \begin{itemize}

      \item the length of [[str]] is less than { [[UDPpayloadMax]]}, the architecture-dependent
       maximum payload for a UDP datagram.

      \item The socket has a peer IP address set in its [[is2]] field or the [[addr]] argument is
       [[SOME(i3,p3)]], specifying a destination address.

      \item The socket is bound to a local port [[p1']], or it can be autobound to [[p1']] and
       [[sid]] added to the list of bound sockets.

      \item A UDP datagram is constructed from the socket's binding quad [[(sock.is1,SOME
       p1',sock.is2,sock.ps2)]], the destination address argument [[addr]], and the data
       [[str]]. This datagram is successfully enqueued on the outqueue of the host, [[oq]] to form
       outqueue [[oq']] using auxiliary function {@link [[dosend]]}.

    \end{itemize}

    A [[Lh_call(tid,send(fd,addr,IMPLODE str,opts0))]] transition is made, leaving the thread in
    state [[Ret (OK(""))]] and the host with new outqueue [[oq']]. If the socket was autobound to a
    port then [[sid]] is appended to the host's list of bound sockets.

    @variation Posix

    The [[MSG_OOB]] flag is not set in [[opts0]].

    @variation FreeBSD

    On FreeBSD there is an additional condition for a successful [[send()]]: the amount of data to
    be sent must be less than or equal to the size of the socket's send buffer.

    @variation Linux

    The [[MSG_OOB]] flag is not set in [[opts0]].

    @variation WinXP

    The [[MSG_OOB]] flag is not set in [[opts0]] and any pending errors are ignored.

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.



    :*)
    )

/\

    (!h ts tid d socks sid udp fd addr sock bound
      str opts0 p1' oq' fid ff opts h0 es
      SS MM.

    send_10 /* rp_udp, block (*: Block waiting to enqueue datagram :*) */
      (h0,SS,MM)
    -- Lh_call (tid,send(fd,addr,IMPLODE str,opts0)) -->
      (h with <| ts :=
                 FUPDATE ts (tid,
			     Timed(Send2(sid,SOME (addr,sock.is1,SOME p1',sock.is2,sock.ps2), str,opts), never_timer));
                socks := socks |++
                         [(sid,sock with <| es := es; ps1 := SOME p1'; pr := UDP_PROTO(udp) |>)];
                bound := bound;
                oq := oq' |>,
       SS,MM)

    <==

      h0 = h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                     socks := socks |++
                              [(sid,sock with <| es := es; pr := UDP_PROTO(udp) |>)] |> /\
      fd IN FDOM h0.fds /\
      fid = h0.fds ' fd /\
      FAPPLY h0.files fid = File(FT_Socket(sid),ff) /\
      sock.cantsndmore = F /\
      (~(windows_arch h.arch) ==> es = NONE) /\
      opts = LIST_TO_SET opts0 /\
      ~((~bsd_arch h.arch /\MSG_DONTWAIT IN opts) \/ ff.b(O_NONBLOCK)) /\
      ((linux_arch h.arch \/ windows_arch h.arch) ==> T ) /\

      p1' IN autobind(sock.ps1,PROTO_UDP,h0,h0.socks) /\
      (if sock.ps1 = NONE then bound = sid::h0.bound else bound = h0.bound) /\
      dosend(h0.ifds,h0.rttab,(addr,str),(sock.is1,SOME p1',sock.is2,sock.ps2),h0.oq,oq',F) /\
      ((addr <> NONE) \/ (sock.is2 <> NONE))


   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]] that is not shutdown for writing and has no
    pending errors. A [[send(fd,addr,IMPLODE str,opts0)]] call is made from thread [[tid]] which is
    in the [[Run]] state.

    Either the socket is a blocking one: its [[O_NONBLOCK]] flag is not set, or the call is a
    blocking one: the [[MSG_DONTWAIT]] flag is not set in [[opts0]].

    The socket is either bound to local port [[p1']] or can be autobound to a port [[p1']].  Either
    the socket has its peer IP address set, or the destination address of the [[send()]] call is
    set: [[addr<>NONE]].

    A UDP datagram, constructed from the socket's binding quad [[sock.is1,SOME
    p1',sock.is2,sock.ps2]], the destination address argument [[addr]], and the data [[str]], cannot
    be placed on the outqueue of the host [[oq]].

    The call blocks, waiting for the datagram to be enqueued on the host's outqueue. The thread is
    left in state [[Send2(sid,SOME(addr,sock.is1,SOME p1',sock.is2,sock.ps2),str,opts)]]. If the
    socket was autobound to a port then [[sid]] is appended to the head of the host's list of bound
    sockets.

    @variation FreeBSD

    The [[MSG_DONTWAIT]] flag may be set in [[opts0]]: it is ignored by FreeBSD.

    @variation Linux

    The [[MSG_OOB]] flag must not be set in [[opts0]].

    @variation WinXP

    The [[MSG_OOB]] flag must not be set in [[opts0]], and any pending error on the socket is
    ignored.

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.

    The [[opts0]] argument is of type [[list]]. In the model it is converted to a [[set]] [[opts]]
    using [[LIST_TO_SET]]. The presence of [[MSG_PEEK]] is checked for in [[opts]] rather than in
    [[opts0]].

   :*)
   )

/\

    (!h ts tid d socks sid sock udp fd addr
      str opts0 p1' oq' fid ff opts h0 es bound
      SS MM.

    send_11 /* rp_udp, fast fail (*: Fail with [[EAGAIN]]: call would block and non-blocking behaviour has been requested :*) */
      (h0,SS,MM)
    -- Lh_call (tid,send(fd,addr,IMPLODE str,opts0)) -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (FAIL EAGAIN),sched_timer));
                socks := socks |++
                         [(sid,sock with <| es := es; ps1 := SOME p1'; pr := UDP_PROTO(udp) |>)];
                bound := bound;
                oq := oq' |>,
      SS,MM)

    <==

      h0 = h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                     socks := socks |++
                              [(sid,sock with <| es := es; pr := UDP_PROTO(udp) |>)] |> /\
      fd IN FDOM h0.fds /\
      fid = h0.fds ' fd /\
      FAPPLY h0.files fid = File(FT_Socket(sid),ff) /\
      sock.cantsndmore = F /\
      (~(windows_arch h.arch) ==> es = NONE) /\
      p1' IN autobind(sock.ps1,PROTO_UDP,h0,h0.socks) /\
      (if sock.ps1 = NONE then bound = sid::h0.bound else bound = h0.bound) /\
      ((addr <> NONE) \/ (sock.is2 <> NONE)) /\
      opts = LIST_TO_SET opts0 /\
      ((~bsd_arch h.arch /\ MSG_DONTWAIT IN opts) \/ ff.b(O_NONBLOCK)) /\
      dosend(h0.ifds,h0.rttab,(addr,str),(sock.is1,sock.ps1,sock.is2,sock.ps2),h0.oq,oq',F)


   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]] that is not shutdown for writing and has no
    pending errors. The thread [[tid]] is in the [[Run]] state and a call [[send(fd,addr,IMPLODE
    str,opts0]] is made.

    The socket is either locally bound to a port [[p1']] or can be autobound to a port [[p1']].
    Either the socket has a peer IP address set, or a destination address was provided in the
    [[send()]] call: [[addr<>NONE]].

    Either the socket is non-blocking: its [[O_NONBLOCK]] flag is set, or the call is non-blocking:
    [[MSG_DONTWAIT]] flag was set in the [[opts0]] argument of [[send()]].

    A UDP datagram (constructed from the socket's binding quad
    [[(sock.is1,sock.ps1,sock.is2,sock.ps2)]], the destination address argument [[addr]], and the data
    [[str]]) cannot be placed on the outqueue of the host [[oq]].

    The [[send()]] call fails with an [[EAGAIN]] error. A [[Lh_call(tid,send(fd,addr,IMPLODE str,opts0))]] transition is made, leaving the thread state [[FAIL (EAGAIN)]], and the host
    with outqueue [[oq']]. If the socket was autobound to a port, [[sid]] is appended to the host's
    list of bound sockets.

    @variation FreeBSD

    The socket's [[O_NONBLOCK]] flag must be set for the rule to apply; the [[MSG_DONTWAIT]] flag is
    ignored by FreeBSD.

    @variation WinXP

    Pending errors on the socket are ignored.

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte]] [[list]] when
    the datagram is constructed. Here the data, [[str]] is of type [[byte]] [[list]] and in the
    transition [[IMPLODE str]] is used to convert it into a string.

    The [[opts0]] argument is of type [[list]]. In the model it is converted to a [[set]] [[opts]]
    using [[LIST_TO_SET]]. The presence of [[MSG_PEEK]] is checked for in [[opts]] rather than in
    [[opts0]].

    Note that on Linux [[EWOULDBLOCK]] and [[EAGAIN]] are aliased.


   :*)
   )

/\

    (!h ts tid d socks sid fid ff h0 err bound
      sf is1 ps1 udp fd str opts0 ps1' cantsndmore cantrcvmore es
      SS MM.

    send_12 /* rp_udp, fast fail (*: Fail with [[ENOTCONN]]: no peer address set in socket and no destination address provided :*) */
      (h0,SS,MM)
    -- Lh_call (tid,send(fd,NONE,IMPLODE str,opts0)) -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (FAIL err), sched_timer));
                socks := socks |++
                         [(sid,Sock(SOME fid,sf,is1,ps1',NONE,NONE,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))];
                bound := bound |>,
      SS,MM)

    <==

      h0 = h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                     socks := socks |++
                              [(sid,Sock(SOME fid,sf,is1,ps1,NONE,NONE,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))] |> /\
      fd IN FDOM h.fds /\
      fid = h.fds ' fd /\
      FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
      (if bsd_arch h.arch then err=EDESTADDRREQ(* /\ cantsndmore=F*)
       else                    err=ENOTCONN) /\
      (~(windows_arch h.arch) ==> es = NONE) /\
      (if linux_arch h.arch then
           ?p1'. p1' IN autobind(ps1,PROTO_UDP,h0,h0.socks) /\ ps1' = SOME p1' /\
           (if ps1 = NONE then bound = sid::h0.bound else bound = h0.bound)
       else bound = h0.bound /\ ps1' = ps1)



   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]] that has no pending errors.

    A call [[send(fd,addr,IMPLODE str,opts0]] is made from thread [[tid]] which is in the [[Run]]
    state. The socket is either locally bound to a port [[p1']] or it can be autobound to a port
    [[p1']].

    The socket does not have a peer address set, and no destination address is specified in the
    [[send()]] call: [[addr = NONE]]. The call will fail with an [[ENOTCONN]] error.

    A [[Lh_call(tid,send(fd,NONE,IMPLODE str,opts0))]] transition will be made, leaving the thread
    in state [[Ret (FAIL ENOTCONN]]. If the socket was autobound then [[sid]] is appended to the
    head of the host's list of bound sockets, [[h0.bound]], resulting in the new list [[bound]].

    @variation FreeBSD

    On FreeBSD the error returned is [[EDESTADDRREQ]], the socket must not be shut down for writing,
    and if it is not bound to a local port it will not be autobound.

    @variation WinXP

    Any pending error on the socket is ignored, and if the socket's local port is not bound, [[ps1 =
    NONE]], then it will not be autobound.

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte list]] when the
    datagram is constructed. Here the data, [[str]] is of type [[byte list]] and in the transition
    [[IMPLODE str]] is used to convert it into a string.

    @internal

    \cite{stevens1998a} states this should give [[\tscon{EDESTADDRREQ}]], not [[ENOTCONN]].

   :*)
   )

/\

    (!h ts tid d socks sid fid ff h0
      sock fd addr str opts0 ps1' udp bound
      SS MM.

    send_13 /* rp_udp, fast fail (*: Fail with [[EMSGSIZE]]: string to be sent is bigger than [[UDPpayloadMax]] :*) */
      (h0,SS,MM)
    -- Lh_call (tid,send(fd,addr,IMPLODE str,opts0)) -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (FAIL EMSGSIZE), sched_timer));
                socks := socks |++
                         [(sid,sock with <| ps1 := ps1'; pr := UDP_PROTO(udp) |>)];
                bound := bound |>,
      SS,MM)

    <==

      h0 = h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                     socks := socks |++
                              [(sid,sock with <| pr := UDP_PROTO(udp) |>)] |> /\
      fd IN FDOM h0.fds /\
      fid = h0.fds ' fd /\
      FAPPLY h0.files fid = File(FT_Socket(sid),ff) /\
      (STRLEN (IMPLODE str) > UDPpayloadMax h0.arch \/
         (bsd_arch h.arch /\ STRLEN (IMPLODE str) > (h0.socks ' sid).sf.n(SO_SNDBUF))) /\
      ps1' IN {sock.ps1} UNION (IMAGE (SOME) (autobind(sock.ps1,PROTO_UDP,h0,h0.socks))) /\
      (if sock.ps1 = NONE /\ ps1' <> NONE then bound = sid::h0.bound else bound = h0.bound)


   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]]. A call [[send(fd,addr,IMPLODE str,opts0)]] is
    made from thread [[tid]] which is in the [[Run]] state.

    The length in bytes of [[str]] is greater than [[UDPpayloadMax]], the architecture-dependent
    maximum payload size for a UDP datagram. The [[send()]] call fails with an [[EMSGSIZE]] error.

    A [[Lh_call(tid,send(fd,addr,IMPLODE str,opts0))]] transition is made leaving the thread in
    state [[Ret (FAIL EMSGSIZE)]].  Additionally, the socket's local port [[ps1]] may be autobound
    if it was not bound to a local port when the [[send()]] call was made. If the autobinding
    occurs, then the socket's [[sid]] is added to the list of bound sockets [[h0.bound]], leaving
    the host's list of bound sockets as [[bound]].

    @variation FreeBSD

    On FreeBSD, the [[send()]] call may also fail with [[EMSGSIZE]] if the size of [[str]] is
    greater than the value of the socket's [[SO_SNDBUF]] option.

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte list]] when the
    datagram is constructed. Here the data, [[str]] is of type [[byte list]] and in the transition
    [[IMPLODE str]] is used to convert it into a string.

    @internal

    In Linux, [[send_5]] takes precedence over this, so [[EMSGSIZE]] cannot happen in an error
    state. In a normal state, it does not set the error flag. What happens on a [[Send2]] if an
    error flag is set is open.

    Note that we let [[ps1'=ps1]] nondeterministically, as the size check may be before or after the
    autobind.  On Linux this is unnecessary as the autobind is performed before the [[EMSGSIZE]]
    check.

    Note that we nondeterministically allow the message size check to fail either on entry to
    [[Send2]] or on exit.

   :*)
   )

/\

    (!h ts tid d socks sid ff
      fid sf udp fd addr str opts0 e cantsndmore cantrcvmore es
      SS MM.

    send_14 /* rp_udp, fast fail (*: Fail with [[EAGAIN]], [[EADDRNOTAVAIL]] or [[ENOBUFS]]: there are no ephemeral ports left :*) */
      (h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                socks := socks |++
                         [(sid,Sock(SOME fid,sf,NONE,NONE,NONE,NONE,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))] |>,
      SS,MM)
    -- Lh_call (tid,send(fd,addr,IMPLODE str,opts0)) -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (FAIL e), sched_timer));
                socks := socks |++
                         [(sid,Sock(SOME fid,sf,NONE,NONE,NONE,NONE,es,cantsndmore,cantrcvmore,UDP_PROTO(udp)))] |>,
      SS,MM)

    <==

      fd IN FDOM h.fds /\
      fid = h.fds ' fd /\
      FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
      cantsndmore = F /\
      (~(windows_arch h.arch) ==> es = NONE) /\
      autobind(NONE,PROTO_UDP,h,h.socks) = EMPTY /\
      e IN {EAGAIN; EADDRNOTAVAIL; ENOBUFS}



   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]] that is not shutdown for writing and has no
    pending errors. The socket has no peer address set, and is not bound to a local IP address or
    port.

    From the [[Run]] state, thread [[tid]] makes a [[send(fd,addr,IMPLODE str,opts0)]] call.  The
    socket cannot be auto-bound to an ephemeral port so the call fails. The error returned will be
    [[EAGAIN]], [[EADDRNOTAVAIL]], or [[ENOBUFS]].

    A [[Lh_call(tid,send(fd,addr,IMPLODE str,opts0))]] transition will be made. The thread will be
    left in state [[RET (FAIL e)]] where [[e]] is one of the above errors.

    @variation WinXP

    Any pending error on the socket is ignored.

    @modeldetails

    The data to be sent is of type [[string]] in the [[send()]] call but is a [[byte list]] when the
    datagram is constructed. Here the data, [[str]] is of type [[byte list]] and in the transition
    [[IMPLODE str]] is used to convert it into a string.

   :*)
   )

/\

    (!h ts addr is1 ps1 is2 ps2 es
      d socks sock udp oq' str opts sid tid
      SS MM.

    send_15 /* rp_udp, slow urgent succeed (*: Return from blocked state after datagram enqueued :*) */
      (h with <| ts := FUPDATE ts (tid, Timed(Send2(sid,SOME (addr,is1,ps1,is2,ps2),str,opts),d));
                socks := socks |++
                         [(sid,sock with <| es := es; pr := UDP_PROTO(udp) |>)] |>,
      SS,MM)
    -- Lh_tau -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (OK ("")),sched_timer));
                socks := socks |++
                         [(sid,sock with <| es := es; pr := UDP_PROTO(udp) |>)];
                oq := oq' |>,
      SS,MM)

    <==

      sock.cantsndmore = F /\
      (~(windows_arch h.arch) ==> es = NONE) /\
      STRLEN (IMPLODE str) <= UDPpayloadMax h.arch /\
      (dosend(h.ifds,h.rttab,(addr,str),(is1,ps1,is2,ps2),h.oq,oq',T) \/
       dosend(h.ifds,h.rttab,(addr,str),(sock.is1,sock.ps1,sock.is2,sock.ps2),h.oq,oq',T)) /\
      (addr <> NONE \/ sock.is2 <> NONE \/ is2 <> NONE)



   (*:

    @description

    Consider a UDP socket [[sid]] that is not shutdown for writing and has no pending errors. The
    thread [[tid]] is blocked in state [[Send2(sid,SOME(addr,is1,ps1,is2,ps2),str)]].

    A datagram can be constructed using [[str]] as its data. The length in bytes of [[str]] is less
    than or equal to [[UDPpayloadMax]], the architecture-dependent maximum payload size for a UDP
    datagram. There are three possible destination addresses:

    \begin{itemize}
      \item [[addr]], the destination address specified in the [[send()]] call.
      \item [[is2,ps2]], the socket's peer address when the [[send()]] call was made.
      \item [[sock.is2,sock.ps2]], the socket's current peer address.
    \end{itemize}

    At least one of [[addr]], [[is2]], and [[sock.is2]] must specify an IP address: they are not all
    set to [[NONE]]. One of the three addresses will be used as the destination address of the
    datagram.  The datagram can be successfully enqueued on the host's outqueue, [[h.oq]], resulting
    in a new outqueue [[oq']].

    An [[Lh_tau]] transition is made, leaving the thread state [[Ret (OK(""))]], and the host
    with new outqueue [[oq']].

    @internal

    Note that the [[Send2]] state can only be entered by the [[send_10]] rule (in the UDP case).
    Unfortunately, this does not guarantee that the socket's [[is2]] and [[ps2]] will be present,
    because a call to [[disconnect]] may have removed them.  We allow for a successful send to occur
    based on the values in the socket when the call was made however.

   :*)
   )

/\

    (!h ts tid addr is1 ps1 is2 ps2
      str d socks sid sock e udp
      SS MM.

    send_16 /* rp_udp, slow urgent fail (*: Fail: blocked socket has entered an error state :*) */
      (h with <| ts := FUPDATE ts (tid, Timed(Send2(sid,SOME (addr,is1,ps1,is2,ps2),str),d));
                socks := socks |++
                         [(sid,sock with <| es := SOME e; pr := UDP_PROTO(udp) |>)] |>,
      SS,MM)
    -- Lh_tau -->
      (h with <| ts := FUPDATE ts (tid, Timed(Ret (FAIL e),sched_timer));
                socks := socks |++
                [(sid,sock with <| es := NONE; pr := UDP_PROTO(udp) |>)] |>,
      SS,MM)

    <==

      ~(windows_arch h.arch)


   (*:

    @description

    Consider a UDP socket [[sid]] that has pending error [[SOME e]]. The thread [[tid]] is blocked
    in state [[Send2(sid,SOME (addr,is1,ps1,is2,ps2),str)]]. The error, [[e]], will be returned to
    the caller.

    At [[Lh_tau]] transition is made, leaving the thread state [[RET (FAIL e)]].

    Note that the error has occurred after the thread entered the [[Send2]] state: rule [[send_11]]
    specifies that the call cannot block if there is a pending error.

    @variation WinXP

    This rule does not apply: all pending errors on a socket are ignored for a [[send()]] call.

   :*)


    )

/\

    (!h ts tid addr is1 ps1 is2 ps2
      str d socks sock udp e sid opts sf es
      SS MM.

    send_17 /* rp_udp, slow urgent fail (*: Fail with [[EMSGSIZE]] or [[ENOTCONN]]: blocked socket has had peer address unset or string to be sent is too big :*) */
      (h with <| ts := FUPDATE ts (tid,Timed(Send2(sid,SOME(addr,is1,ps1,is2,ps2),str,opts),d));
                socks := socks |++
                         [(sid,sock with <| sf := sf; es := es; pr := UDP_PROTO(udp) |>)] |>,
      SS,MM)
    -- Lh_tau -->
      (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer));
                socks := socks |++
                         [(sid,sock with <| sf := sf; es := es; pr := UDP_PROTO(udp) |>)] |>,
      SS,MM)

    <==

      (~(windows_arch h.arch) ==> es = NONE) /\
      (?oq'. dosend(h.ifds,h.rttab,(addr,str),(is1,ps1,is2,ps2),h.oq,oq',T)) /\
      ((STRLEN (IMPLODE str) > UDPpayloadMax h.arch /\ (e = EMSGSIZE)) \/
       (bsd_arch h.arch /\ STRLEN (IMPLODE str) > sf.n(SO_SNDBUF) /\ (e = EMSGSIZE)) \/
       ((sock.is2 = NONE) /\ (addr = NONE) /\ (e = ENOTCONN)))


   (*:

    @description

    Consider a UDP socket [[sid]] with no pending errors. The thread [[tid]] is blocked in state
    [[Send2(sid,SOME(addr,is1,ps1,is2,ps2),str)]].

    A datagram is constructed with [[str]] as its payload. Its destination address is taken from
    [[addr]], the destination address specified when the [[send()]] call was made, or
    [[(is2,ps2)]], the socket's peer address when the [[send()]] call was made. It is possible to
    enqueue the datagram on the host's outqueue, [[h.oq]].

    This rule covers two cases. In the first, the length in bytes of [[str]] is greater than
    [[UDPpayloadMax]], the architecture-dependent maximum payload size for a UDP datagram. The error
    [[EMSGSIZE]] is returned.

    In the second case, the original [[send()]] call did not have a destination address specified:
    [[addr = NONE]], and the socket has had the IP address of its peer address unset:
    [[sock.is2=NONE]].  The peer address of the socket when the [[send()]] call was made,
    [[(is2,ps2)]], is ignored, and an [[ENOTCONN]] error is returned.

    In either case, a [[Lh_tau]] transition is made, leaving the thread state [[Ret (FAIL e)]]
    where [[e]] is either [[EMSGSIZE]] or [[ENOTCONN]].

    @variation FreeBSD

    An [[EMSGSIZE]] error can also be returned if the size of [[str]] is greater than the value of
    the socket's [[SO_SNDBUF]] option.

    @variation WinXP

    Any pending error on the socket is ignored.

    @internal

    This rule nondeterministically competes with rules [[send_15]] which allows a message to be
    enqueued using [[(is2,ps2)]], the socket's peer address when the [[send()]] call was made.

    This case non-deterministically competes with rule [[send_13]]: the [[EMSGSIZE]] error can be
    returned either when the [[send()]] call is first made, or when the datagram is enqueued on the
    host's outqueue.

    The condition ensures it fires only when we try to put the message onto the outqueue, modelling
    the discovery at that point that the message is too large, or that the socket has become
    disconnected.  (This rule nondeterministically competes with [[send_13]], which would catch an
    outsize message earlier, and with [[send_15]], which would allow the delivery of a message on a
    now-disconnected socket based on the values of [[sock.is2]] and [[sock.ps2]] when the call was
    made.)

    This rule leaves the socket state unchanged.  One might wish to allow it to have been disturbed,
    nondeterministically.

   :*)
   )

/\

   (!h ts tid d socks sid sock udp fd addr str opts0 fid ff opts h0 ps1 ps1' bound
     SS MM.

   send_18 /* rp_udp, fast fail (*: Fail with [[EOPNOTSUPP]]: [[MSG_PEEK]] flag not supported for [[send()]] calls on WinXP; or [[MSG_OOB]] flag not supported on WinXP and Linux  :*) */
    (h0,SS,MM)
   -- Lh_call (tid,send(fd,addr,IMPLODE str,opts0)) -->
    (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EOPNOTSUPP),sched_timer));
              socks := socks |++
                       [(sid,sock with <| ps1 := ps1'; pr := UDP_PROTO(udp) |>)];
              bound := bound |>,
    SS,MM)

   <==

    h0 = h with <| ts := FUPDATE ts (tid,Timed(Run,d));
              socks := socks |++
                       [(sid,sock with <| ps1 := ps1; pr := UDP_PROTO(udp) |> )] |> /\
    fd IN FDOM h.fds /\
    fid = h.fds ' fd /\
    FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
    opts = LIST_TO_SET opts0 /\
    (MSG_PEEK IN opts /\ windows_arch h.arch) /\
    (if linux_arch h.arch then
         ?p1'. p1' IN autobind(ps1,PROTO_UDP,h0,h0.socks) /\ ps1' = SOME p1' /\
         (if ps1 = NONE then bound = sid::h0.bound else bound = h0.bound)
     else
         ps1 = ps1' /\ bound = h0.bound)


   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]]. From thread [[tid]], which is in the [[Run]]
    state, a [[send(fd,addr,IMPLODE str,opts0)]] call is made.

    This rule covers two cases. In the first, on WinXP, the [[MSG_PEEK]] flag is set in
    [[opts0]]. In the second case, on Linux and WinXP, the socket has not been shut down for
    writing, and the [[MSG_OOB]] flag is set in [[opts0]]. In either case, the [[send()]] call fail
    with an [[EOPNOTSUPP]] error.

    A [[Lh_call(tid,send(fd,addr,IMPLODE str,opts0))]] transition is made, leaving the thread in
    state [[Ret (FAIL EOPNOTSUPP)]].

    @variation FreeBSD

    FreeBSD ignores the [[MSG_PEEK]] and [[MSG_OOB]] flags for [[send()]].

    @variation Linux

    Linux ignores the [[MSG_PEEK]] flag for [[send()]].

    @modeldetails

    The [[opts0]] argument is of type [[list]]. In the model it is converted to a [[set]] [[opts]]
    using [[LIST_TO_SET]]. The presence of [[MSG_PEEK]] is checked for in [[opts]] rather than in
    [[opts0]].


   :*)


   )


/\

   (!h ts tid d socks sid sock
     fd i2 p2 str opts0
     p1' i1' fid ff h0 bound
     SS MM.

   send_19 /* rp_udp, fast fail (*: Fail with [[EADDRINUSE]]: on FreeBSD, local and destination address quad in use by another socket :*) */
     (h0,SS,MM)
   -- Lh_call (tid,send(fd,SOME (i2,p2),IMPLODE str,opts0)) -->
     (h with <| ts := FUPDATE ts (tid, Timed(Ret (FAIL EADDRINUSE),sched_timer));
               socks := socks |++
                        [(sid,sock)];
               bound := bound |>,
     SS,MM)

   <==

    bsd_arch h.arch /\
    h0 = h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                   socks := socks |++
                            [(sid,sock)] |> /\
    sock.cantsndmore = F /\
    (~(windows_arch h.arch) ==> sock.es = NONE) /\
    p1' IN autobind(sock.ps1,PROTO_UDP,h0,h0.socks) /\
    (if sock.ps1 = NONE then bound = sid::h0.bound else bound = h0.bound) /\
    i1' IN auto_outroute(i2,sock.is1,h0.rttab,h0.ifds) /\
    fd IN FDOM h0.fds /\
    fid = h0.fds ' fd /\
    FAPPLY h0.files fid = File(FT_Socket(sid),ff) /\
    sock = (h0.socks ' sid) /\
    proto_of sock.pr = PROTO_UDP /\
    (?sid'.
       sid' IN FDOM h0.socks /\
       let s = h0.socks ' sid' in
       s.is1 = SOME i1' /\ s.ps1 = SOME p1' /\
       s.is2 = SOME i2  /\ s.ps2 = SOME p2  /\
       proto_of s.pr = PROTO_UDP)


   (*:

    @description

    On FreeBSD, consider a UDP socket [[sid]] referenced by [[fd]] that is not shutdown for
    writing. From thread [[tid]], which is in the [[Run]] state, a [[send(fd,SOME(i2,p2),IMPLODE
    str,opts0)]] call is made. The socket is bound to local port [[p1']] or it can be autobound to
    port [[p1']]. The socket can be bound to a local IP address [[i1']] which has a route to
    [[i2]]. Another socket, [[sid']], is locally bound to [[(i1',p1')]] and has its peer address set
    to [[(i2,p2)]]. The [[send()]] call will fail with an [[EADDRINUSE]] error.

    A [[Lh_call(tid,send(fd,SOME(i2,p2),IMPLODE str,opts0))]] transition will be made, leaving the
    thread state [[Ret (FAIL EADDRINUSE)]].

    @variation Linux

    This rule does not apply.

    @variation WinXP

    This rule does not apply.

    @internal

    When a UDP send call is made on an unconnected socket with an (ip,port) pair specified in the
    call, three calls are made: [[connect()]], [[send()]], [[disconnect()]]. If another socket has
    already called [[connect()]] to obtain the IP/port/IP/port quadruple that this socket is trying
    to use then [[EADDRINUSE]] is returned.

    See remark for [[connect_5b]].

   :*)

   )

/\

   (!h ts tid d socks sid sock i2 p2 udp
     fd i3 p3 str opts0 fid ff
     SS MM.

   send_21 /* rp_udp, fast fail (*: Fail with [[EISCONN]]: socket has peer address set and destination address is specified in call on FreeBSD :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| es := NONE; is2 := SOME i2; ps2 := SOME p2; pr := UDP_PROTO(udp)  |>)] |>,
     SS,MM)
   -- Lh_call (tid,send(fd,SOME(i3,p3),IMPLODE str,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EISCONN),sched_timer));
               socks := socks |++
                        [(sid,sock with <| es := NONE; is2 := SOME i2; ps2 := SOME p2; pr := UDP_PROTO(udp)  |>)] |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     bsd_arch h.arch


   (*:

    @description

    Consider a UDP socket [[sid]] referenced by [[fd]] that has its peer address set: [[is2 = SOME
    i2]], and [[ps2 = SOME p2]]. From thread [[tid]], which is in the [[Run]] state, a
    [[send(fd,SOME(i3,p3),IMPLODE str,opts0)]] call is made. On FreeBSD, the call will fail with the
    [[EISCONN]] error, as the call specified a destination address even though the socket has a peer
    address set.

    A [[Lh_call(tid,send(fd,SOME(i3,p3),IMPLODE str,opts0))]] transition will be made, leaving the
    thread state [[Ret (FAIL EISCONN)]].

    @variation Posix

    If the socket is connectionless-mode, the message shall be sent to the address specified by
    [[SOME(i3,p3)]]. See the above [[send()]] rules.

    @variation Linux

    This rule does not apply. Linux allows the [[send()]] call to occur. See the above [[send()]]
    rules.

    @variation WinXP

    This rule does not apply. WinXP allows the [[send()]] call to occur. See the above [[send()]]
    rules.

    @internal

    When calling [[send]] on a connected UDP socket, with an address specified in the call,
    [[EISCONN]] is returned.

    The UDP paper does not specify this for some reason, despite noting that Posix says this should
    be the result. UNPv1 p225 says that Solaris would allow this send to occur, and testing also
    shows that Linux allows it, but BSD does not.

   :*)

   )

/\

   (!h ts tid d socks sid fid sf is1 ps1 is2 ps2 es cantrcvmore udp
    fd addr str opts0 err ff
    SS MM.

    send_22 /* rp_udp, fast fail (*: Fail with [[EPIPE]] or [[ESHUTDOWN]]: socket shut down for writing :*) */
      (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
                socks := socks |++
                         [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,T,cantrcvmore,UDP_PROTO(udp)))] |>,
      SS,MM)
    -- Lh_call(tid,send(fd,addr,IMPLODE str,opts0)) -->
      (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL err),sched_timer));
                socks := socks |++
                         [(sid,Sock(SOME fid,sf,is1,ps1,is2,ps2,es,T,cantrcvmore,UDP_PROTO(udp)))] |>,
      SS,MM)

    <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     if windows_arch h.arch then err = ESHUTDOWN
     else                        err = EPIPE


    (*:

     @description

     From thread [[tid]], which is in the [[Run]] state, a [[send(fd,addr,IMPLODE str,opts0)]] call
     is made where [[fd]] refers to a UDP socket [[sid]] that is shut down for writing. The call
     fails with an [[EPIPE]] error.

     A [[Lh_call(tid,send(fd,addr,IMPLODE str,opts0))]] transition is made, leaving the thread in
     state [[Ret (FAIL EPIPE)]].

     @variation WinXP

     The call fails with an [[ESHUTDOWN]] error rather than [[EPIPE]].

    :*)

 )


/\

   (!h ts tid d
     fd str opts0 socks sock sid fid e ff addr
     SS MM.

   send_23 /* rp_udp, fast fail (*: Fail with pending error :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| es := SOME e |>)] |>,
     SS,MM)
   -- Lh_call (tid,send(fd,addr,IMPLODE str,opts0)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer));
               socks := socks |++
                        [(sid,sock with <| es := NONE |>)] |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     proto_of sock.pr = PROTO_UDP /\
     ~(windows_arch h.arch)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[send(fd,addr,IMPLODE str,opts0)]] call
    is made where [[fd]] refers to a UDP socket [[sid]] that has pending error [[SOME e]].  The call
    fails, returning the pending error.

    A [[Lh_call(tid,send(fd,addr,IMPLODE str,opts0))]] transition is made, leaving the thread in
    state [[Ret (FAIL e)]].

    @variation WinXP

    This rule does not apply: all pending errors are ignored for [[send()]] calls on WinXP.

   :*)


  )

/\

(*:
@section [[setfileflags]] ALL [[setfileflags()]]
 \[ <[setfileflags: (fd * filebflag list) -> unit]> \]

  A call to [[setfileflags(fd,flags)]] sets the flags on a file referred to by [[fd]]. [[flags]] is
  the list of file flags to set. The possible flags are:

  \begin{itemize}
    \item [[O_ASYNC]] Specifies whether signal driven I/O is enabled.
    \item [[O_NONBLOCK]] Specifies whether a socket is non-blocking.
  \end{itemize}

  The call returns successfully if the flags were set, or fails with an error otherwise.

@errors

  A call to [[setfileflags()]] can fail with the errors below, in which case the corresponding
  exception is raised:

  @errorinclude [[misc]] [[EBADF]]

@commoncases

  [[setfileflags_1]]; [[return_1]]

@api

  [[setfileflags()]] is Posix |fcntl(fd,F_GETFL,flags)|. On WinXP it is
  |ioctlsocket()| with the |FIONBIO| command.

  \begin{tabular}{ll}
    Posix:   & |int fcntl(int fildes, int cmd, ...);|\\
    FreeBSD: & |int fcntl(int fd, int cmd, ...);|\\
    Linux:   & |int fcntl(int fd, int cmd);|\\
    WinXP:   & |int ioctlsocket(SOCKET s, long cmd, u_long* argp)|
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |fildes| is a file descriptor for the file to retrieve flags from. It corresponds
     to the [[fd]] argument of the model [[setfileflags()]]. On WinXP the |s| is a socket
     descriptor corresponding to the [[fd]] argument of the model [[setfileflags()]].

    \item |cmd| is a command to perform an operation on the file. This is set to
     |F_GETFL| for the model [[setfileflags()]]. On WinXP, |cmd| is set to
     |FIONBIO| to get the [[O_NONBLOCK]] flag; there is no [[O_ASYNC]] flag on WinXP.

    \item The call takes a variable number of arguments. For the model [[setfileflags()]] it takes
     three arguments: the two described above and a third of type |long| which represents
     the list of flags to set, corresponding to the [[flags]] argument of the model
     [[setfileflags()]]. On WinXP this is the |argp| argument.

    \item The returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

    \item |WSAENOTSOCK| is a possible error on WinXP as the |ioctlsocket()| call is
     specific to a socket. In the model the [[setfileflags()]] call is performed on a file.

  \end{itemize}

:*)

   (!h ts tid d
     fd flags files fid ft ff ffb ffb'
     SS MM.

   setfileflags_1 /* rp_all, fast succeed (*: Update all the file flags for an open file description :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               files := files |++ [(fid,File(ft,ff with <| b:=ffb |>))] |>,
     SS,MM)
   -- Lh_call (tid,setfileflags(fd,flags)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               files := files |++ [(fid,File(ft,ff with <| b:=ffb' |>))] |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     ffb' = \x. x IN' flags


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[setfileflags(fd,flags)]] call is
    made. [[fd]] refers to the open file description [[(fid,File(ft,ff with <| b := ffb |>))]] where
    [[ffb]] is the set of boolean file flags currently set. [[flags]] is a list of boolean file
    flags, possibly containing duplicates.

    All of the boolean file flags for the file description will be updated. The flags in [[flags]]
    will all be set to [[T]], and all other flags will be set to [[F]], resulting in a new set of
    boolean file flags, [[ffb']].

    A [[Lh_call(tid,setfileflags(fd,flags))]] transition is made, leaving the thread state [[Ret
    (OK())]].


     Note this is not exactly the same as [[getfileflags_1]]:
         [[getfileflags]] never returns duplicates, but duplicates may be
         passed to [[setfileflags]].

    @internal

    Update \emph{all} the file flags on the open file description named, setting those in the given
    list to [[T]] and the others to [[F]].

    Models POSIX's [[fcntl()]] with [[F_SETFL]].

    Typing ensures [[flags]] are valid and is a boolean.

   :*)

   )
/\

(*:

@section [[setsockbopt]] ALL [[setsockbopt()]]
  \[ <[setsockbopt: (fd * sockbflag * bool) -> unit]> \]

  A call [[setsockbopt(fd,f,b)]] sets the value of one of a socket's boolean flags.

  Here the [[fd]] argument is a file descriptor referring to a socket on which to set a flag, [[f]] is
  the boolean socket flag to set, and [[b]] is the value to set it to. Possible boolean flags are:

  \begin{itemize}

    \item [[SO_BSDCOMPAT]] Specifies whether the BSD semantics for delivery of ICMPs to UDP sockets
     with no peer address set is enabled.

    \item [[SO_DONTROUTE]] Requests that outgoing messages bypass the standard routing
     facilities. The destination shall be on a directly-connected network, and messages are directed
     to the appropriate network interface according to the destination address.

    \item [[SO_KEEPALIVE]] Keeps connections active by enabling the periodic transmission of
     messages, if this is supported by the protocol.

    \item [[SO_OOBINLINE]] Leaves received out-of-band data (data marked urgent) inline.

    \item [[SO_REUSEADDR]] Specifies that the rules used in validating addresses supplied to
     [[bind()]] should allow reuse of local ports, if this is supported by the protocol.

  \end{itemize}

@errors

  A call to [[setsockbopt()]] can fail with the errors below, in which case the corresponding
  exception is raised:

  @error [[ENOPROTOOPT]] The option is not supported by the protocol.

  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  [[setsockbopt_1]]; [[return_1]]

@api

  [[setsockbopt()]] is Posix |setsockopt()| for boolean-valued socket flags.

  \begin{tabular}{ll}
    Posix:   & |int setsockopt(int socket, int level, int option_name,| \\
             & |               const void *option_value,|\\
             & |               socklen_t option_len);|\\
    FreeBSD: & |int setsockopt(int s, int level, int optname, | \\
             & |               const void *optval, socklen_t optlen);| \\
    Linux:   & |int setsockopt(int s, int  level,  int  optname,| \\
             & |               const  void  *optval, socklen_t optlen);| \\
    WinXP:   & |int setsockopt(SOCKET s, int level, int optname,| \\
             & |               const char* optval,int optlen);|
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |socket| is the file descriptor of the socket to set the option on, corresponding
     to the [[fd]] argument of the model [[setsockbopt()]].

    \item |level| is the protocol level at which the flag resides: |SOL_SOCKET| for
     the socket level options, and |option_name| is the flag to be set. These two
     correspond to the [[flag]] argument of the model [[setsockbopt()]] where the possible values of
     |option_name| are limited to: [[SO_BSDCOMPAT]], [[SO_DONTROUTE]], [[SO_KEEPALIVE]],
     [[SO_OOBINLINE]], and [[SO_REUSEADDR]].

    \item |option_value| is a pointer to a location of size |option_len|
     containing the value to set the flag to. These two correspond to the [[b]] argument of type
     [[bool]] in the model [[setsockbopt()]].

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item |EFAULT| signifies the pointer passed as |option_value| was
     inaccessible. On WinXP, the error |WSAEFAULT| may also signify that the
     |optlen| parameter was too small. Note this error is not specified by Posix.

    \item |EINVAL| signifies the |option_name| was invalid at the specified socket
     |level|. In the model, typing prevents an invalid flag from being specified in a call
     to [[setsockbopt()]].

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)

   (!h ts tid d
     fd f b socks fid ff
     sid sock sock'
     SS MM.

   setsockbopt_1 /* rp_all, fast succeed (*: Successfully set a boolean socket flag :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++ [(sid,sock)] |>,
     SS,MM)
   -- Lh_call (tid,setsockbopt(fd,f,b)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               socks := socks |++ [(sid,sock')] |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     sock' = sock with <| sf := sock.sf with <| b := funupd sock.sf.b f b |> |>
       (* this idiom seems better than the old one using Sock(...sf with <| b := sfb |>...) to left
          and right of the arrow, at least when Sock() has so many fields. *) /\
     (* On WinXP for UDP, setting these socket options fails *)
     (windows_arch h.arch /\ proto_of sock.pr = PROTO_UDP
         ==> f NOTIN {SO_KEEPALIVE})


   (*:

    @description

    Consider a socket [[sid]], referenced by [[fd]], and with socket flags [[sock.sf]]. From thread
    [[tid]], which is in the [[Run]] state, a [[setsockbopt(fd,f,b)]] call is made. [[f]] is the
    boolean socket flag to be set, and [[b]] is the boolean value to set it to. The call succeeds.

    A [[Lh_call(tid,setsockbopt(fd,f,b))]] is made, leaving the thread state [[Ret (OK())]]. The
    socket's boolean flags, [[sock.sf.b]], are updated such that [[f]] has the value [[b]].

    @variation WinXP

    As above, except that if [[sid]] is a UDP socket, then [[f]] cannot be [[SO_KEEPALIVE]] or
    [[SO_OOBINLINE]].

    @internal

    Update the named boolean flag on the open file description named.

    Models POSIX's [[fcntl()]] with [[F_SETFL]].

    Typing ensures [[f]] is valid and is a boolean flag.

   :*)

   )

/\

   (!h ts tid d socks sid sock fd f b fid ff udp
     SS MM.

   setsockbopt_2 /* rp_udp, fast fail (*: Fail with [[ENOPROTOOPT]]: [[SO_KEEPALIVE]] and [[SO_OOBINLINE]] options not supported for a UDP socket on WinXP :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| pr := UDP_PROTO(udp) |>)] |>,
     SS,MM)
   -- Lh_call (tid,setsockbopt(fd,f,b)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOPROTOOPT),sched_timer));
               socks := socks |++
                        [(sid,sock with <| pr := UDP_PROTO(udp) |>)] |>,
     SS,MM)

   <==

     windows_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     f IN {SO_KEEPALIVE}


   (*:

    @description

    On WinXP, consider a UDP socket [[sid]] referenced by [[fd]]. From thread [[tid]], which is in
    the [[Run]] state, a [[setsockbopt(fd,f,b)]] call is made, where [[f]] is either
    [[SO_KEEPALIVE]] or [[SO_OOBINLINE]]. The call fails with an [[ENOPROTOOPT]] error.

    A [[Lh_call(tid,setsockbopt(fd,f,b))]] transition is made, leaving the thread state [[Ret
    (FAIL ENOPROTOOPT)]].

    @variation FreeBSD

    This rule does not apply.

    @variation Linux

    This rule does not apply.

    @internal

    On Windows, trying to set the [[SO_KEEPALIVE]] and [[SO_OOBINLINE]] flags fails with an
    [[ENOPROTOOPT]] error.

   :*)

   )

/\

(*:

@section [[setsocknopt]] ALL [[setsocknopt()]]
  \[ <[setsocknopt: (fd * socknflag * int) -> unit]> \]

  A call [[setsocknopt(fd,f,n)]] sets the value of one of a socket's numeric flags. The [[fd]]
  argument is a file descriptor referring to a socket to set a flag on, [[f]] is the numeric socket
  flag to set, and [[n]] is the value to set it to. Possible numeric flags are:

  \begin{itemize}
    \item [[SO_RCVBUF]] Specifies the receive buffer size.

    \item [[SO_RCVLOWAT]] Specifies the minimum number of bytes to process for socket input
     operations.

     \item [[SO_SNDBUF]] Specifies the send buffer size.

     \item [[SO_SNDLOWAT]] Specifies the minimum number of bytes to process for socket output
      operations.
  \end{itemize}

@errors

  A call to [[setsocknopt()]] can fail with the errors below, in which case the corresponding
  exception is raised:

  @error [[EINVAL]] On FreeBSD, attempting to set a numeric flag to zero.
  @error [[ENOPROTOOPT]] The option is not supported by the protocol.
  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  [[setsocknopt_1]]; [[return_1]]

@api

  [[setsocknopt()]] is Posix |setsockopt()| for numeric-valued socket flags.

  \begin{tabular}{ll}
    Posix:   & |int setsockopt(int socket, int level, int option_name,| \\
             & |               const void *option_value,|\\
             & |               socklen_t option_len);|\\
    FreeBSD: & |int setsockopt(int s, int level, int optname, | \\
             & |               const void *optval, socklen_t optlen);| \\
    Linux:   & |int setsockopt(int s, int  level,  int  optname,| \\
             & |               const  void  *optval, socklen_t optlen);| \\
    WinXP:   & |int setsockopt(SOCKET s, int level, int optname,| \\
             & |               const char* optval,int optlen);|
  \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |socket| is the file descriptor of the socket to set the option on, corresponding
     to the [[fd]] argument of the model [[setsocknopt()]].

    \item |level| is the protocol level at which the flag resides: |SOL_SOCKET| for
     the socket level options, and |option_name| is the flag to be set. These two
     correspond to the [[flag]] argument of the model [[setsocknopt()]] where the possible values of
     |option_name| are limited to: [[SO_RCVBUF]], [[SO_RCVLOWAT]], [[SO_SNDBUF]], and
     [[SO_SNDLOWAT]].

    \item |option_value| is a pointer to a location of size |option_len|
     containing the value to set the flag to. These two correspond to the [[n]] argument of type
     [[int]] in the model [[setsocknopt()]].

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item |EFAULT| signifies the pointer passed as |option_value| was
     inaccessible. On WinXP, the error |WSAEFAULT| may also signify that the
     |optlen| parameter was too small. Note this error is not specified by Posix.

    \item |EINVAL| signifies the |option_name| was invalid at the specified socket
     |level|. In the model, typing prevents an invalid flag from being specified in a call
     to [[setsocknopt()]].

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)

   (!h ts tid d
     fd f n n' socks fid ff
     sid sock sock' ns
     SS MM.

   setsocknopt_1 /* rp_all, fast succeed (*: Successfully set a numeric socket flag :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++ [(sid,sock)] |>,
     SS,MM)
   -- Lh_call (tid,setsocknopt(fd,f,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               socks := socks |++ [(sid,sock')] |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     n' = MAX (sf_min_n h.arch f) (MIN (sf_max_n h.arch f) (clip_int_to_num n)) /\
     ns = (if bsd_arch h.arch /\ f = SO_SNDBUF /\ n' < sock.sf.n(SO_SNDLOWAT) then
               funupd (funupd sock.sf.n f n') SO_SNDLOWAT n'
	  else funupd sock.sf.n f n') /\
     sock' = sock with <| sf := sock.sf with <| n := ns |> |>


   (*:

    @description

    Consider the socket [[sid]], referenced by [[fd]], with numeric socket flags [[sock.sf.n]]. From
    the thread [[tid]], which is in the [[Run]] state, a [[setsocknopt(fd,f,n)]] call is made where
    [[f]] is a numeric socket flag to be updated, and [[n]] is the integer value to set it to. The
    call succeeds.

    A [[Lh_call(tid,setsocknopt(fd,f,n))]] transition is made, leaving the thread state [[Ret
    (OK())]]. The socket's numeric flag [[f]] is updated to be the value [[n']] which is: the
    architecture-specific minimum value for [[f]] [[sf_min_n h.arch f]], if [[n]] is less than this
    value; the architecture-specific maximum value for [[f]], i.e.~[[sf_max_n h.arch f]], if [[n]] is
    greater than this value, or [[n]] otherwise.

    @variation FreeBSD

    If the flag to be set is [[SO_SNDBUF]] and the new value [[n]] is less than the value of the
    socket's [[SO_SNDLOWAT]] flag then the [[SO_SNDLOWAT]] flag is also set to [[n]].

    @internal

    Update the named numeric flag on the open file description named.  Appropriate coercions are
    applied to the value to keep it in the desired range.

    Note that [[SO_RCVLOWAT]] can be set to anything on Linux. Models POSIX's [[fcntl()]] with
    [[F_SETFL]]. Typing ensures [[f]] is valid and is a numeric flag.

    Notice that clipping to zero and to the appropriate minimum and maximum values occurs
    \emph{silently}; no [[EINVAL]] is raised.

    I have not done any [[EISCONN]] errors, or out-of-memory / [[ENOBUFS]].

   :*)
   )

/\

   (!h ts tid d fd f n
     SS MM.

   setsocknopt_2 /* rp_all, fast fail (*: Fail with [[EINVAL]]: on FreeBSD numeric socket flags cannot be set to zero :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,setsocknopt(fd,f,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINVAL),sched_timer)) |>,SS,MM)

   <==

     clip_int_to_num n = 0 /\
     bsd_arch h.arch


   (*:

    @description

    On FreeBSD, from thread [[tid]], which is in the [[Run]] state, a [[setsocknopt(fd,f,n)]] call
    is made where [[fd]] is a file descriptor, [[f]] is a numeric socket flag, and [[n]] is an
    integer value to set [[f]] to. Because the numeric value of [[n]] equals [[0]], the call fails
    with an [[EINVAL]] error.

    A [[Lh_call(tid,setsocknopt(fd,f,n))]] transition is made, leaving the thread state [[Ret
    (FAIL EINVAL)]].

    @variation Posix

    This rule does not apply.

    @variation Linux

    This rule does not apply.

    @variation WinXP

    This rule does not apply.

    @internal

    On BSD, trying to set [[SO_SNDBUF]], [[SO_RCVBUF]], [[SO_SNDLOWAT]], or [[SO_RCVLOWAT]] to 0 is
    an [[EINVAL]] error.

    :*)
   )

/\

   (!h ts tid d fd f n
     SS MM.

   setsocknopt_4 /* rp_all, fast fail (*: Fail with [[ENOPROTOOPT]]: [[SO_SNDLOWAT]] not settable on Linux :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,setsocknopt(fd,f,n)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOPROTOOPT),sched_timer)) |>,SS,MM)

   <==

      linux_arch h.arch /\
      f = SO_SNDLOWAT


   (*:

    @description

    On Linux, from thread [[tid]], which is in the [[Run]] state, a [[setsocknopt(fd,f,n)]] call is
    made. [[f = SO_SNDLOWAT]], which is not settable, so the call fails with an [[ENOPROTOOPT]]
    error.

    A [[Lh_call(tid,setsocknopt(fd,f,n))]] transition is made, leaving the thread state [[Ret
    (FAIL ENOPROTOOPT)]].

    @variation FreeBSD

    This rule does not apply.

    @variation WinXP

    This rule does not apply. Note the warning from the Win32 docs (at MSDN setsockopt):

    "If the setsockopt function is called before the bind function,
    TCP/IP options will not be checked with TCP/IP until the bind
    occurs. In this case, the setsockopt function call will always
    succeed, but the bind function call may fail because of an early
    setsockopt failing."

    This is currently unimplemented.

    @internal

    If the user attempts to set an option that is not settable, the
    error [[ENOPROTOOPT]] is returned.

    This is currently nondeterministic for those options POSIX permits
    to be nonsettable.  We should sharpen this up.

    POSIX: "shall fail...".

    Note the warning from the Win32 docs (at MSDN setsockopt):

    "If the setsockopt function is called before the bind function,
    TCP/IP options will not be checked with TCP/IP until the bind
    occurs. In this case, the setsockopt function call will always
    succeed, but the bind function call may fail because of an early
    setsockopt failing."

    We do not yet implement this, but will probably have to one day.

   :*)
   )

/\

(*:

@section [[setsocktopt]] ALL [[setsocktopt()]]
 \[ <[setsocktopt: (fd * socktflag * (int * int) option) -> unit]> \]

  A call [[setsocktopt(fd,f,t)]] sets the value of one of a socket's time-option flags.

  The [[fd]] argument is a file descriptor referring to a socket to set a flag on, [[f]] is the
  time-option socket flag to set, and [[t]] is the value to set it to. Possible time-option flags
  are:

  \begin{itemize}
    \item [[SO_RCVTIMEO]] Specifies the timeout value for input operations.

    \item [[SO_SNDTIMEO]] Specifies the timeout value that an output function blocks because flow
     control prevents data from being sent.
  \end{itemize}

  If [[t=NONE]] then the timeout is disabled. If [[t=SOME(s,ns)]] then the timeout is set to [[s]]
  seconds and [[ns]] nanoseconds.

@errors

  A call to [[setsocktopt()]] can fail with the errors below, in which case the corresponding
  exception is raised:

  @error [[EBADF]] The file descriptor [[fd]] does not refer to a valid file descriptor.
  @error [[EDOM]] The timeout value is too big to fit in the socket structure.
  @error [[ENOPROTOOPT]] The option is not supported by the protocol.
  @error [[ENOTSOCK]] The file descriptor [[fd]] does not refer to a socket.
  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]

@commoncases

  [[setsocktopt_1]]; [[return_1]]

@api

  [[setsocktopt()]] is Posix |setsockopt()| for time-option socket flags.

  \begin{tabular}{ll}
    Posix:   & |int setsockopt(int socket, int level, int option_name,| \\
             & |               const void *option_value,|\\
             & |               socklen_t option_len);|\\
    FreeBSD: & |int setsockopt(int s, int level, int optname, | \\
             & |               const void *optval, socklen_t optlen);| \\
    Linux:   & |int setsockopt(int s, int  level,  int  optname,| \\
             & |               const  void  *optval, socklen_t optlen);| \\
    WinXP:   & |int setsockopt(SOCKET s, int level, int optname,| \\
             & |               const char* optval,int optlen);|
   \end{tabular}

  In the Posix interface:

  \begin{itemize}

    \item |socket| is the file descriptor of the socket to set the option on, corresponding
     to the [[fd]] argument of the model [[setsocktopt()]].

    \item |level| is the protocol level at which the flag resides: |SOL_SOCKET| for
     the socket level options, and |option_name| is the flag to be set. These two
     correspond to the [[flag]] argument of the model [[setsocktopt()]] where the possible values of
     |option_name| are limited to: [[SO_RCVTIMEO]] and [[SO_SNDTIMEO]].

    \item |option_value| is a pointer to a location of size |option_len|
     containing the value to set the flag to. These two correspond to the [[t]] argument of type
     [[(int * int) option]] in the model [[setsocktopt()]].

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item |EFAULT| signifies the pointer passed as |option_value| was
     inaccessible. On WinXP, the error |WSAEFAULT| may also signify that the
     |optlen| parameter was too small. Note this error is not specified by Posix.

    \item |EINVAL| signifies the |option_name| was invalid at the specified socket
     |level|. In the model, typing prevents an invalid flag from being specified in a call
     to [[setsocknopt()]].

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

  \end{itemize}

:*)

   (!h ts tid d
     fd f t t' t'' socks fid ff
     sid sock sock' s ns
     SS MM.

   setsocktopt_1 /* rp_all, fast succeed (*: Successfully set a time-option socket flag :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++ [(sid,sock)] |>,
     SS,MM)
   -- Lh_call (tid,setsocktopt(fd,f,t)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               socks := socks |++ [(sid,sock')] |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     tltimeopt_wf t /\  (* time option is well-formed *)
     t' = time_of_tltimeopt t /\
     t' >= time_zero /\
     (if f IN {SO_RCVTIMEO; SO_SNDTIMEO} /\ t' = time_zero
      then t'' = time_infty
      else t'' = t') /\
     (if f = SO_LINGER /\  t = SOME(s,ns) then ns = 0 else T) /\
     (f IN {SO_RCVTIMEO; SO_SNDTIMEO} ==> t'' = time_infty \/ t'' <= sndrcv_timeo_t_max) /\
     sock' = sock with <| sf := sock.sf with <| t := funupd sock.sf.t f t'' |> |>



   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[setsocktopt(fd,f,t)]] call is
    made. [[fd]] refers to a socket [[sid]] which has time-option socket flags [[sock.sf.t]]; [[f]]
    is a time-option socket flag: either [[SO_RCVTIMEO]] or [[SO_SNDTIMEO]]; and [[t]] is the
    well formed time-option value to set [[f]] to. The call succeeds.

    A [[Lh_call(tid,setsocktopt(fd,f,t))]] transition is made, leaving the thread state [[Ret
    (OK())]]. If [[t=NONE]] or [[t=SOME (0,0)]] then the socket's time-option flags are updated such
    that [[sock.sf.t(f)=NONE]], representing [[time_infty]]; otherwise the socket's time-option
    flags are updated such that [[f]] has the time value represented by [[t]], which must be less
    than [[snd_rcv_timeo_t_max]].

    @modeldetails

    The type of [[t]] is [[(int * int) option]], but the type of a time-option socket flag is
    [[time]]. The auxiliary function [[time_of_tltimeopt]] is used to do the conversion.

    @internal

    Update the named time-option flag on the open file description named.  The time is given in
    microseconds.

    Models POSIX's [[fcntl()]] with [[F_SETFL]].

    Typing ensures [[f]] is valid and is a time-option flag.

    Note that the type of the argument is an optional pair of integers, as defined by
    [[time_of_tltimeopt]]: absence denotes infinity, pair is seconds and nanoseconds respectively.

    We only accept nonnegative times.  This cannot be enforced by typing, because we do not have
    unsigned types in TL.  Not clear what error we should raise if this fails.

    There's a bit of a hack here (an irregularity in our LIB API); [[0]] means [[NONE]] as a
    timeout; this means that [[SOME 0]] and [[NONE]] have the same effect.

    I have not done any [[EISCONN]] errors.

   :*)
   )

/\

   (!h ts tid d fd f t fid sid ff
     SS MM.

   setsocktopt_4 /* rp_all, fast fail (*: Fail with [[ENOPROTOOPT]]: on WinXP [[SO_LINGER]] not settable for a UDP socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,setsocktopt(fd,f,t)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOPROTOOPT),sched_timer)) |>,SS,MM)

   <==

     windows_arch h.arch /\
     fd IN FDOM h.fds /\ fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     proto_of (h.socks ' sid).pr = PROTO_UDP /\
     f = SO_LINGER


   (*:

    @description

    On WinXP, from thread [[tid]], which is in the [[Run]] state, a [[setsocktopt(fd,f,t)]] call is
    made. [[fd]] is a file descriptor referring to a UDP socket [[sid]], [[f]] is the time-option
    socket [[SO_LINGER]]. The flag [[f]] is not settable, so the call fails with an [[ENOPROTOOPT]]
    error.

    A [[Lh_call(tid,setsocktopt(fd,f,t))]] transition is made, leaving the thread state [[Ret
    (FAIL ENOPROTOOPT)]].

    @variation FreeBSD

    This rule does not apply.

    @variation Linux

    This rule does not apply.

    @internal

    If the user attempts to set an option that is not settable, the error [[ENOPROTOOPT]] is
    returned.

    NB: On BSD/LINUX you can get/set [[SO_LINGER]] on a UDP socket. On WinXP this fails.

    This is currently nondeterministic for those options POSIX permits to be nonsettable.  We should
    sharpen this up.

    POSIX: "shall fail...".

    :*)
   )

/\

   (!h ts tid d fd f t t' t''
     SS MM.

   setsocktopt_5 /* rp_all, fast fail (*: Fail with [[EDOM]]:  timeout value too long to fit in socket structure :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,setsocktopt(fd,f,t)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EDOM),sched_timer)) |>,SS,MM)

   <==

     f IN {SO_RCVTIMEO; SO_SNDTIMEO} /\
     tltimeopt_wf t /\  (* time option is well-formed *)
     t' = time_of_tltimeopt t /\
     (if t' = time_zero
      then t'' = time_infty
      else t'' = t') /\
     ~(t'' = time_infty \/ t'' <= sndrcv_timeo_t_max)


   (*:

    @description

    From thread [[tid]], which is currently in the [[Run]] state, a [[setsocktopt(fd,f,t)]] call is
    made. [[f]] is a time-option socket flag that is either [[SO_RCVTIMEO]] or [[SO_SNDTIMEO]], and
    [[t]] is the time value to set [[f]] to. The call fails with an [[EDOM]] error because the value
    [[t]] is too large to fit in the socket structure: it is not zero and it is greater than
    [[sndrcv_timeo_t_max]].

    A [[Lh_call(tid,setsocktopt(fd,f,t))]] call is made, leaving the thread state [[Ret (FAIL
    EDOM)]].

    @modeldetails

    The type of [[t]] is [[(int * int) option]], but the type of a time-option socket flag is
    [[time]]. The auxiliary function [[time_of_tltimeopt]] is used to do the conversion.

    @internal

    If the user attempts to set a timer value that is too large to fit in the socket structure, the
    error [[EDOM]] is returned.

    Note TCPv2p544 that BSD has/had a bug here.

    POSIX: "shall fail...".

   :*)
   )

/\

(*:

@section [[shutdown]] ALL [[shutdown()]]
  \[ <[shutdown: (fd * bool * bool) -> unit]> \]

  A call of [[shutdown(fd,r,w)]] shuts down either the read-half of a connection, the write-half of
  a connection, or both. The [[fd]] is a file descriptor referring to the socket to shutdown; the [[r]] and [[w]] indicate whether the socket should be shut down for reading and writing respectively.

  For a TCP socket, shutting down the read-half empties the socket's receive queue, but data will
  still be delivered to it and subsequent [[recv()]] calls will return data. Shutting down the
  write-half of a TCP connection causes the remaining data in the socket's send queue to be sent and
  then TCP's connection termination to occur.

  For Linux and WinXP, a TCP socket may only be shut down if it is in the [[ESTABLISHED]] state; on
  FreeBSD a socket may be shut down in any state.

  For a UDP socket, if the socket is shutdown for reading, data may still be read from the socket's
  receive queue on Linux, but on FreeBSD and WinXP this is not the case. Shutting down the socket
  for writing causes subsequent [[send()]] calls to fail.


@errors

  A call to [[shutdown()]] can fail with the errors below, in which case the corresponding exception
  is raised:

  @error [[ENOTCONN]] The socket is not connected and so cannot be shut down.
  @errorinclude [[misc]] [[EBADF]]
  @errorinclude [[misc]] [[ENOTSOCK]]
  @errorinclude [[misc]] [[ENOBUFS]]

@commoncases

 A TCP socket is created and connects to a peer; data is transferred between the two; the socket has
 no more data to send so calls [[shutdown()]] to inform the peer of this: [[socket_1]]; $\dots $;
 [[connect_1]]; $\dots $; [[shutdown_1]]; [[return_1]]

@api

  \begin{tabular}{ll}
    Posix:   & |int shutdown(int socket, int how);| \\
    FreeBSD: & |int shutdown(int s, int how);| \\
    Linux:   & |int shutdown(int s, int how);| \\
    WinXP:   & |int shutdown(SOCKET s, int how);|
  \end{tabular}

  In the Posix interface:
  \begin{itemize}

    \item |socket| is a file descriptor referring to the socket to shut down. This
     corresponds to the [[fd]] argument of the model [[shutdown()]].

    \item |how| is an integer specifying the type of shutdown corresponding to the [[(r,w)]]
     arguments in the model [[shutdown()]]. If |how| is set to |SHUT_RD| then the
     read half of the connection is to be shut down, corresponding to a [[shutdown(fd,T,F)]] call in
     the model; if it is set to |SHUT_WR| then the write half of the connection is to be
     shut down, corresponding to a [[shutdown(fd,F,T)]] call in the model; if it is set to
     |SHUT_RDWR| then both the read and write halves of the connection are to be shut down,
     corresponding to a [[shutdown(fd,T,T)]] call in the model.

    \item the returned |int| is either |0| to indicate success or |-1| to
     indicate an error, in which case the error code is in |errno|.  On WinXP an error is
     indicated by a return value of |SOCKET_ERROR|, not |-1|, with the actual error
     code available through a call to |WSAGetLastError()|.

  \end{itemize}

  The FreeBSD, Linux, and WinXP interfaces are similar, except where noted.

@modeldetails

  The following errors are not modelled:
  \begin{itemize}

    \item |EINVAL| signifies that the |how| argument is invalid. In the model the
     |how| argument is represented by the two boolean flags [[r]] and [[w]] which guarantees
     that the only values allowed are [[(T,T)]], [[(T,F)]], [[(F,T)]], and [[(F,F)]]. The first
     three correspond to the allowed values of |how|: |SHUT_RD|,
     |SHUT_WR|, and |SHUT_RDWR|. The last possible value, [[(F,F)]], is not
     allowed by Posix, but the model allows a [[shutdown(fd,F,F)]] call,
     which has no effect on the socket.

    \item |WSAEINPROGRESS| is WinXP-specific and described in the MSDN page as "A blocking
     Windows Sockets 1.1 call is in progress, or the service provider is still processing a callback
     function". This is not modelled here.

   \end{itemize}
:*)


   (!h ts tid d
     fd r w fid sid socks ff sf is1 ps1 es pr pr'
     is2 ps2 cantrcvmore cantsndmore tcp_sock sock sock'
     SS MM.

   shutdown_1 /* rp_tcp, fast succeed (*: Shut down read or write half of TCP connection :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock)] |>,
     SS,MM)
   -- Lh_call (tid,shutdown(fd,r,w)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK ()),sched_timer));
               socks := socks |++
                        [(sid,sock')] |>,
     SS,MM)

   <==

     sock = Sock(SOME fid,sf,is1,ps1,is2,ps2,es,cantsndmore,cantrcvmore,pr) /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     pr = TCP_PROTO tcp_sock /\
     if bsd_arch h.arch /\ tcp_sock.st IN {CLOSED;LISTEN} /\ w (* note only when shutdown for writing! *) then
        (* If shutdown is called on a BSD socket in states CLOSED or LISTEN, then tcp_close() is called,
           which kills the socket. However, the cantsndmore and cantrcvmore flags are set by the
           socket layer in the same way. *)
        (* Note that the effect of tcp_close being called on a CLOSED/LISTENing socket is to clear its
           protocol and control blocks, so that it looks like a freshly created socket from the point
           of view of subsequent calls. Thus bsd_cantconnect is not set. However, the tests done by
           connect_ rules etc, just look at the bsd_cantconnect flag, so we set it here to the value
           of sock'.cantsndmore. *)
        (* This call does not destroy a stream. *)
        let sock'' = (tcp_close h.arch sock) in
        sock' = sock'' with <| cantsndmore := (w\/cantsndmore);
                               cantrcvmore := (r\/cantrcvmore);
                               pr := TCP_PROTO(tcp_sock_of sock'' with
                                            <| lis := NONE |>)
                            |>
     else
        (~bsd_arch h.arch ==> ?i1 p1 i2 p2. tcp_sock.st = ESTABLISHED /\ is1=SOME i1 /\
	                        ps1=SOME p1 /\ is2=SOME i2 /\ ps2=SOME p2 /\ tcp_sock.lis = NONE) /\
        pr' = pr /\
        sock' = Sock(SOME fid,sf,is1,ps1,is2,ps2,es,w \/ cantsndmore,r \/cantrcvmore,pr')


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[shutdown(fd,r,w)]] call is made. [[fd]]
    refers to a TCP socket [[sid]] which is in the [[ESTABLISHED]] state and has binding quad
    [[(SOME i1,SOME p1,SOME i2,SOME p2)]].

    The call suceeds: a [[Lh_call(tid,shutdown(fd,r,w))]] transition is made, leaving the thread in
    state [[Ret (OK())]]. If [[r=T]] then the read-half of the connection is shut down, setting
    [[cantrcvmore=T]] and emptying the socket's receive queue; if [[w=T]] then the write-half of the
    connection is shut down, setting [[cantsndmore=T]]; otherwise, the socket is unchanged.

    @variation FreeBSD

    The TCP socket can be in any state, not just [[ESTABLISHED]]. If the socket is in the [[CLOSED]]
    or [[LISTEN]] and is to be shutdown for writing, [[w=T]], then the socket is closed, see {@link
    [[tcp_close]]}.

    Note that testing has shown the socket's listen queue is not always set to [[NONE]] after a
    [[shutdown()]] call. The precise condition for this being done needs to be investigated.

    @internal

    Close the read half of the connection (if requested), by setting the appropriate bit in the
    socket state and emptying the [[rcvq]]; close the write half (if requested), by setting the
    appropriate bit in the socket state.

    I'm pretty sure (but do not have the POSIX ref to prove it, CHECK!)  that [[shutdown()]] does not
    check the pending error flag.

    It's a LIB API decision here that [[shutdown(fd,F,F)]] is legal, and simply does nothing (after
    checking that [[fd]] refers to a socket).

    Note that we do not send a FIN here; that is left to the protocol layer.  (perhaps it should be
    in [[close_2a]] also?).

    UNPv1p160 says that if we shut down the read half, TCP should still ACK data it receives, and
    just silently drop it on the floor.  TODO: do we do this?

   :*)
   )

/\

   (!h ts d tid sid sock socks cantrcvmore
     cantsndmore udp_pr fd r w fid ff
     SS MM.

   shutdown_2 /* rp_udp, fast succeed (*: Shutdown UDP socket for reading, writing, or both :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| cantrcvmore := cantrcvmore;
                                           cantsndmore := cantsndmore;
                                           pr := UDP_PROTO(udp_pr) |> )] |>,
     SS,MM)
   -- Lh_call(tid,shutdown(fd,r,w)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK()),sched_timer));
               socks := socks |++
                        [(sid,sock with <| cantrcvmore := (r \/ cantrcvmore);
                                           cantsndmore := (w \/ cantsndmore);
                                           pr := UDP_PROTO(udp_pr) |> )] |>,
     SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     (linux_arch h.arch ==> sock.is2 <> NONE)


   (*:

    @description

    Consider a UDP socket [[sid]], referenced by [[fd]]. From thread [[tid]], which is in the
    [[Run]] state, a [[shutdown(fd,r,w)]] call is made and succeeds.

    A [[Lh_call(tid,shutdown(fd,r,w))]] transition is made, leaving the thread state [[Ret
    (OK())]]. If the socket was shutdown for reading when the call was made or [[r = T]] then the
    socket is shutdown for reading. If the socket was shutdown for writing when the call was made or
    [[w = T]] then the socket is shutdown for writing.

    @variation Linux

    As above, with the added condition that the socket's peer IP address must be set: [[sock.is2 <>
    NONE]].

    :*)

  )


/\

   (!h ts tid d
     fd r w fid sid ff tcp_sock
     SS MM.

   shutdown_3 /* rp_tcp, fast fail (*: Fail with [[ENOTCONN]]: cannot shutdown a socket that is not connected on Linux and WinXP :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,shutdown(fd,r,w)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOTCONN),sched_timer)) |>,SS,MM)

   <==

     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
     TCP_PROTO(tcp_sock) = (h.socks ' sid).pr /\
     tcp_sock.st <> ESTABLISHED /\
     ~(bsd_arch h.arch)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[shutdown(fd,r,w)]] call is made where
    [[fd]] refers to a TCP socket [[sid]] which is not in the [[ESTABLISHED]] state. The call fails
    with an [[ENOTCONN]] error.

    A [[Lh_call(tid,shutdown(fd,r,w))]] transition is made, leaving the thread state [[Ret (FAIL
    ENOTCONN)]].

    @variation FreeBSD

    This rule does not apply.

    @internal

    If the socket is not connected, it is an error to attempt to shut it down.

    Note that for a UDP socket this only holds on Linux. On BSD and Windows the call succeeds.

    API decision: ... even if it would be a NOP.

    Have not modelled [[ENOBUFS]] yet.

   :*)

   )

/\

   (!h ts tid d socks sid sock udp fd r w fid ff
     SS MM.

   shutdown_4 /* rp_udp, fast fail (*: Fail with [[ENOTCONN]]: socket's peer address not set on Linux :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               socks := socks |++
                        [(sid,sock with <| is2 := NONE; pr := UDP_PROTO(udp) |> ) ] |>,
     SS,MM)
   -- Lh_call (tid,shutdown(fd,r,w)) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOTCONN),sched_timer));
               socks := socks |++
                        [(sid,sock with <| is2 := NONE;
                                           cantsndmore := (w \/ sock.cantsndmore);
                                           cantrcvmore := (r \/ sock.cantrcvmore);
                                           pr := UDP_PROTO(udp) |>)] |>,
     SS,MM)


   <==

     linux_arch h.arch /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(FT_Socket(sid),ff)


   (*:

    @description

    On Linux, consider a UDP socket [[sid]] referenced by [[fd]] with no peer IP address set: [[is2
    := NONE]]. From thread [[tid]], which is in the [[Run]] state, a [[shutdown(fd,r,w)]] call is
    made, and fails with an [[ENOTCONN]] error.

    A [[Lh_call(tid,shutdown(fd,r,w))]] transition is made, leaving the thread state [[Ret (FAIL
    ENOTCONN)]]. If the socket was shutdown for reading when the call was made or [[r = T]] then the
    socket is shutdown for reading. If the socket was shutdown for writing when the call was made or
    [[w = T]] then the socket is shutdown for writing.

    @variation FreeBSD

    This rule does not apply: see rule [[shutdown_2]].

    @variation WinXP

    This rule does not apply: see rule [[shutdown_2]].

    :*)


   )

/\

(*:

@section [[socket]] ALL [[socket()]]
 \[ <[socket: sock_type -> fd]> \]

  A call to [[socket(type)]] creates a new socket. Here [[type]] is the type of socket to create:
  [[SOCK_STREAM]] for TCP and [[SOCK_DGRAM]] for UDP. The returned [[fd]] is the file descriptor of
  the new socket.

@errors

  A call to [[socket()]] can fail with the errors below, in which case the corresponding exception
  is raised:

  @error [[EMFILE]] No more file descriptors for this process.
  @errorinclude [[misc]] [[ENOBUFS]]
  @errorinclude [[misc]] [[ENOMEM]]
  @errorinclude [[misc]] [[ENFILE]]


 @commoncases

  TCP: [[socket_1]]; [[return_1]]; [[connect_1]]; $\dots$
  UDP: [[socket_1]]; [[return_1]]; [[bind_1]]; [[return_1]]; [[send_9]]; $\dots$

@api

  \begin{tabular}{ll}
    Posix:  &  |int socket(int domain, int type, int protocol);| \\
    FreeBSD:&  |int socket(int domain, int type, int protocol);| \\
    Linux:  &  |int socket(int doamin, int type, int protocol);| \\
    WinXP:  &  |SOCKET socket(int af, int type, int protocol);| \\
  \end{tabular}\\

  In the Posix interface:

  \begin{itemize}

    \item |domain| specifies the communication domain in which the socket is to be created,
    specifying the protocol family to be used. Only IPv4 sockets are modelled here, so
    |domain| is set to |AF_INET| or |PF_INET|.

    \item |type| specifies the communication semantics: |SOCK_STREAM| provides
          sequenced, reliable, two-way, connection-based byte streams; |SOCK_DGRAM|
          supports datagrams (connectionless, unreliable messages of a fixed maximum length). This
          corresponds to the [[sock_type]] argument of the model [[socket()]].

    \item |protocol| specifies the particular protocol to be used for the socket. A
    |protocol| of |0| requests to use the default for the appropriate socket
    |type|: TCP for |SOCK_STREAM| and UDP for |SOCK_DGRAM|. Alternatively
    a specific protocol number can be used: |6| for TCP and |17| for UDP. In the
    model, [[SOCK_STREAM]] refers to a TCP socket and [[SOCK_DGRAM]] to a UDP socket so the
    |protocol| argument is not necessary.

  \end{itemize}

  A call to [[socket(SOCK_STREAMM)]] in the model interface, would be a
  |socket(AF_INET,SOCK_STREAM,0)| call in Posix; a call to [[socket(SOCK_DGRAMM)]] in the
  model interface would be a |socket(AF_INET,SOCK_DGRAM,0)| call in Posix.

  The FreeBSD, Linux and WinXP interfaces are similar modulo argument renaming, except where noted
  above.


@modeldetails

  The following errors are not modelled:

  \begin{itemize}

    \item In Posix and on Linux, |EACCES| specifies that the process does not have appropriate
    privileges.  We do not model a privilege state in which socket creation would be disallowed.

    \item In Posix and  on Linux, |EAFNOSUPPORT|, specifies that the implementation does not
    support the address |domain|. FreeBSD, Linux, and WinXP all support |AF_INET|
    sockets.

    \item On Linux, |EINVAL| means unknown protocol, or protocol domain not available. Both
    TCP and UDP are known protocols for Linux, and |AF_INET| is a known domain on Linux.

    \item In Posix and on Linux, |EPROTONOTSUPPORT| specifies that the protocol is not
    supported by the address family, or the protocol is not supported by the
    implementation. FreeBSD, Linux, and WinXP all support the TCP and UDP protocols.

    \item In Posix, |EPROTOTYPE| signifies that the socket type is not supported by the
    protocol. Both |SOCK_STREAM| and |SOCK_DGRAM| are supported by TCP and UDP
    respectively.

    \item On WinXP, |WSAESOCKTNOSUPPORT| means the specified socket type is not supported in
    this address family. The |AF_INET| family supports both |SOCK_STREAM| and
    |SOCK_DGRAM| sockets.

  \end{itemize}

  The |AF_INET6|, |AF_LOCAL|, |AF_ROUTE|, and |AF_KEY| address
  families; |SOCK_RAW| socket type; and all protocols other than TCP and UDP are not modelled.

:*)

   (!h ts tid d fid sid fd fds fds' files socks
     sock socktype
     SS MM.

   socket_1 /* rp_all, fast succeed (*: Successfully return a new file descriptor for a fresh socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d));
               fds := fds;
               files := files;
               socks := socks |>,
     SS,MM)
   -- Lh_call (tid,(socket (socktype))) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (OK fd),sched_timer));
               fds := fds';
               files := files |++ [(fid,File(FT_Socket(sid),ff_default))];
               socks := socks |++ [(sid,sock)] |>,
     SS,MM)

   <==

     CARD (FDOM fds) < OPEN_MAX /\
     fid NOTIN (FDOM files) /\
     sid NOTIN (FDOM socks) /\
     nextfd h.arch fds fd /\
     fds' = fds |+ (fd, fid) /\
     (case socktype of
       SOCK_DGRAM -> (sock =
         Sock(SOME fid,sf_default h.arch socktype,NONE,NONE,NONE,NONE,NONE,F,F,UDP_Sock([]))) ||
       SOCK_STREAM -> (sock =
         Sock(SOME fid,sf_default h.arch socktype,NONE,NONE,NONE,NONE,NONE,F,F,
              TCP_Sock(CLOSED,initial_cb,NONE))))
     (* an alternative would be to set them to default values here,
     rather than in (e.g.) connect_1.  But then - when exactly *are*
     they set, if they depend on the value of a sysctl for instance?
     Investigate. *)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[socket(socktype)]] call is made. The
    number of open file descriptors is less than the maximum permitted, [[OPEN_MAX]].

    If [[socktype=SOCK_STREAM]] then a new TCP socket [[sock]] is created, in the [[CLOSED]] state,
    with {@link [[initial_cb]]} as its control block, and all other fields uninitialised; if
    [[socktype=SOCK_DGRAM]] then a new, unitialised UDP socket [[sock]] is created. A new open file
    description is created pointing to the socket, and a new file descriptor, [[fd]], is allocated
    in an architecture specific way (see { [[nextfd]]}) to point to the open file
    description. The host's finite map of sockets is updated to include an entry mapping the socket
    identifier [[sid]] to the socket; its finite map of file descriptions is updated to add an entry
    mapping the file descriptor [[fid]] to the file description of the socket; and its finite map of
    file descriptors is updated, adding a mapping from [[fd]] to [[fid]].

    A [[Lh_call(tid,socket(sock_type))]] transition is made, leaving the thread state [[Ret (OK
    fd)]] to return the new file descriptor.

    @internal

    If the user calls [[socket()]], a new socket is allocated in the closed state, a new open file
    description is allocated pointing to it, and a new file descriptor is allocated pointing to the
    open file description.

   :*)
   )

/\

   (!h ts tid d s
     SS MM.

   socket_2 /* rp_all, fast fail (*: Fail with [[EMFILE]]: out of file descriptors for this process :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,(socket (s))) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EMFILE),sched_timer)) |>,SS,MM)

   <==

     CARD (FDOM h.fds) >= OPEN_MAX


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a [[socket(s)]] call is made. The number of
    open file descriptors is greater than the maximum allowed number, [[OPEN_MAX]], and so the call
    fails with an [[EMFILE]] error.

    A [[Lh_call(tid,socket(s))]] transition is made, leaving the thread state [[Ret (FAIL
    EMFILE)]].

    @internal

    If there are already the maximum number of open file descriptors, we cannot create any more.

   :*)
   )


/\

(*:

@section [[misc]] ALL Miscellaneous

  This section collects the remaining Sockets API rules:
  \begin{itemize}

  \item The rule [[return_1]] characterising how the the results of system calls
  are returned to the caller, with transitions from the thread state [[Timed(Ret v,d)]].

  \item Rules [[badf_1]] and [[notsock_1]] deal with all the Sockets API calls that take a file descriptor
  argument, dealing uniformly with the error cases in which that file descriptor is not valid or
  does not refer to a socket.

  \item Rule [[intr_1]] applies to all the thread states for blocked calls, [[Accept2(sid)]] etc.,
  characterising the behaviour in the case where the call is interrupted by a signal.

  \item Rules [[resourcefail_1]] and [[resourcefail_2]] deal with the cases where calls fail due to a lack
  of system resources.
  \end{itemize}

@errors

Common errors.

@error [[EBADF]]  The file descriptor passed is not a valid file descriptor.

@error [[ENOTSOCK]] The file descriptor passed does not refer to a socket.

@error [[EINTR]] The system was interrupted by a caught signal.

@error [[ENOMEM]] Out of resources.

@error [[ENOBUFS]] Out of resources.

@error [[ENFILE]] Out of resources.

:*)

  (!h ts tid v d
    SS MM.

   return_1 /* rp_all, misc nonurgent (*: Return result of system call to caller :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Ret v,d)) |>,SS,MM)
   -- Lh_return (tid,v) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Run,never_timer)) |>,SS,MM)

   <==

     T


   (*:

    @description

    A system call from thread [[tid]] has completed, leaving the thread state [[Timed(Ret v,d)]].  The value [[v]] (which may be of the form [[OK v']] or [[FAIL v']], for success or failure respectively) is returned to the caller before the timer [[d]] expires.  The thread continues its execution, indicated by the resulting thread state [[Timed(Run,never_timer)]].

    @internal

    Return result (success or failure) to caller, and revert to [[Run]] state.

   :*)
   )

/\

   (!h ts tid d
     fd opn e
     SS MM.

   badf_1 /* rp_all, fast fail (*: Fail with [[EBADF]]: not a valid file descriptor :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,opn) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer)) |>,SS,MM)

   <==

     fd_op fd opn /\
     fd NOTIN FDOM h.fds /\
     (if windows_arch h.arch then e = ENOTSOCK else e = EBADF)


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a system call [[opn]] is made. The call
    requires a single valid file descriptor, but the descriptor passed, [[fd]] is not valid: it does
    not refer to an open file description. The call fails with an [[EBADF]] error, or an
    [[ENOTSOCK]] error on WinXP.

    A [[Lh_call(tid,opn)]] transition is made, leaving the thread state [[Ret (FAIL e)]] where
    [[e]] is one of the above errors.

    The system calls this rule applies to are: [[accept()]], [[bind()]], [[close()]], [[connect()]],
    [[disconnect()]], [[dup()]], [[dupfd()]], [[getfileflags()]], [[setfileflags()]],
    [[getsockname()]], [[getpeername()]], [[getsockbopt()]], [[getsockerr()]],
    [[getsocklistening()]], [[getsocknopt()]], [[getsocktopt()]], [[listen()]], [[recv()]],
    [[send()]], [[setsockbopt()]], [[setsocknopt()]], [[setsocktopt()]], [[shutdown()]], and
    [[sockatmark()]].  See the definition of { [[fd_op]]}.

    @variation FreeBSD

    As above: the call fails with an [[EBADF]] error.

    @variation Linux

    As above: the call fails with an [[EBADF]] error.

    @variation WinXP

    As above: the call fails with an [[ENOTSOCK]] error.

    @internal

    If the user passes an invalid file descriptor to any system call that requires a single valid
    file descriptor, , i.e., one that does refers to an open file description, the call fails with
    [[EBADF]] on BSD or Linux and [[ENOTSOCK]] on WindowsXP.

    POSIX: "shall fail...".

   :*)
   )

/\

   (!h ts tid d
     fd opn fid ft ff
     SS MM.

   notsock_1 /* rp_all, fast fail (*: Fail with [[ENOTSOCK]]: file descriptor not a valid socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call (tid,opn) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL ENOTSOCK),sched_timer)) |>,SS,MM)

   <==

     fd_sockop fd opn /\
     fd IN FDOM h.fds /\
     fid = h.fds ' fd /\
     FAPPLY h.files fid = File(ft,ff) /\
     ~(?sid. ft = FT_Socket(sid))


   (*:

    @description

    From thread [[tid]], which is in the [[Run]] state, a system call [[opn]] is made. The call
    requires a single file descriptor referring to a socket. The file descriptor [[fd]] that the
    user passes refers to an open file description [[File(ft,ff)]] that does not refer to a
    socket. The call fails with an [[ENOTSOCK]] error.

    A [[Lh_call(tid,opn)]] transition is made, leaving the thread state [[Ret (FAIL ENOTSOCK)]].

    The system calls this rule applies to are: [[accept()]], [[bind()]], [[connect()]],
    [[disconnect()]], [[getpeername()]], [[getsockbopt()]], [[getsockerr()]],
    [[getsocklistening()]], [[getsockname()]], [[getsocknopt()]], [[getsocktopt()]], [[listen()]],
    [[recv()]], [[send()]], [[setsockbopt()]], [[setsocknopt()]], [[setsocktopt()]], [[shutdown()]],
    and [[sockatmark()]].  See the definition of { [[fd_sockop]]}.

    @internal

    If the user passes a file descriptor that refers to an open file description that does not refer
    to a socket to any system call that requires a single socket, the error [[ENOTSOCK]] is
    returned.

    POSIX: "shall fail...".

   :*)
   )

/\

   (!h ts tid st d sid sock n opts addr str readfds writefds exceptfds
     SS MM.

   intr_1 /* rp_all, slow nonurgent fail (*: Fail with [[EINTR]]: blocked system call interrupted by
     signal :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(st,d)) |>,SS,MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL EINTR),sched_timer)) |>,SS,MM)


   <==

   sock = (h.socks ' sid) /\
   (st = Close2(sid) \/
    st = Connect2(sid) \/
    st = Recv2(sid,n,opts) \/
    st = Send2(sid,addr,str,opts) \/
    st = PSelect2(readfds,writefds,exceptfds) \/
    st = Accept2(sid))


   (*:

    @description

    If on socket [[sid]] as user call blocked leaving a thread in one of the states:
    [[Close2(sid)]], [[Connect2(sid)]], [[Recv2(sid)]], [[Send2(sid)]], [[PSelect2(sid)]] or
    [[Accept2(sid)]] and a signal is caught, the calls fails returning error [[EINTR]].

    @modeldetails

    This rule is non-deterministic, allowing blocked calls to be interrupted at any point, as the specification does not model the dynamics of signals.

    @variation POSIX

    POSIX says that a system call "shall fail" if "interrupted by a signal".

    @internal

    SB: Have rolled all the individual EINTR rules into this one rule

    If a user call to [[accept()]] is blocked, i.e., is in the [[Accept2]] state, and a signal is
    caught (and handled), the call SHALL fail with error [[EINTR]].  (If the signal is not caught,
    control does not return and so the behaviour is irrelevant).

    Similarly for [[connect()]] and [[Connect2]], [[close()]] and [[Close2()]]

    POSIX: "shall fail..." if "interrupted by a signal that was caught before a valid connection
    arrived".  NOTE: we'd better make [[accept_1a]] urgent, so this is not invalid.

    This is purely nondeterministic here since we do not yet model signals.

    -=-=- from old [[close_9]]:

    WRONG: POSIX: "the state of fildes is unspecified"... we give one
    possible behaviour here, not all possible ones.

    -=-=- from old [[pselect_6]]:

    A strict reading of POSIX suggests that this only happens if none of the fds are ready and the
    timer is nonzero, but we allow the (zero-time) race for simplicity (and pessimism).

   :*)
   )

/\

   (!h ts tid d call fd fid ff sid e sock is1 ps1 i2 p2 n opts socktype r w
     SS MM.

   resourcefail_1 /* rp_all, fast badfail (*: Fail with [[ENFILE]], [[ENOBUFS]] or [[ENOMEM]]: out
     of resources :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(Run,d)) |>,SS,MM)
   -- Lh_call(tid, call) -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer)) |>,SS,MM)

   <==

   ~INFINITE_RESOURCES /\
   fd IN FDOM h.fds /\
   fid = h.fds ' fd /\
   FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
   sock = (h.socks ' sid) /\
   ((call = socket(socktype) /\ e IN {ENFILE; ENOBUFS; ENOMEM}) \/
    (call = bind(fd,is1,ps1) /\ e = ENOBUFS) \/
    (call = connect(fd,i2,SOME p2) /\ e = ENOBUFS) \/
    (call = listen(fd,n) /\ e = ENOBUFS) \/
    (call = recv(fd,n,opts) /\ e IN {ENOMEM;ENOBUFS}) \/
    (call = getsockname(fd) /\ e = ENOBUFS) \/
    (call = getpeername(fd) /\ e = ENOBUFS) \/
    (call = shutdown(fd,r,w) /\ e = ENOBUFS) \/
    (call = accept(fd) /\ e IN {ENFILE; ENOBUFS; ENOMEM}
     /\  proto_of sock.pr = PROTO_TCP))


   (*:

    @description

    Thread [[tid]] performs a [[socket()]], [[bind()]], [[connect()]], [[listen()]], [[recv()]],
    [[getsockname()]], [[getpeername()]], [[shutdown()]] or [[accept()]] system call on socket
    [[sid]], referred to by [[fd]], when insufficient system-wide resources are available to
    complete the request. Return a failure of [[ENFILE]], [[ENOBUFS]] or [[ENOMEM]] immediately to
    the calling thread.

    This rule applies only when it is assumed that the host being modelled does not have
    [[INFINITE_RESOURCES]], i.e. the host does not have unlimited memory, mbufs, file descriptors,
    etc.

    @modeldetails

    The modelling of failure is deliberately non-deterministic because the cause of errors such as
    [[ENFILE]] are determined by more than is modelled in this specification. In order to be more
    precise, the model would need to describe the whole system to determine when such error
    conditions could and should arise.

    @internal

    Merged together several rule comments. Have omitted the comments that said nothing interesting.

    -=-=- From old [[accept_6]]:

    If the user calls [[accept()]] on a socket, or the user has called this and is blocked in the
    [[Accept2]] state, then any of these bad (resource-related) errors may nondeterministically
    occur: [[ENFILE]], [[ENOBUFS]], [[ENOMEM]].

    POSIX: "shall fail..." / "may fail...".  Very nondeterministic, since we do not want to be too
    specific.  Check.

    We're assuming, though, that buffers are only needed once we've found the socket, i.e., that
    [[EBADF]] and [[ENOTSOCK]] take priority over all the named errors.

    -=-=- From old [[connect_6]]:

    At any point, the kernel may run out of resources (buffer space) and return [[ENOBUFS]].

    This is very nondeterministic.  Notice that we \emph{do not} allow this to happen from the
    [[Connect1]] state, because that is an artifact of the LTS construction - we really want to have
    two labels on a single transition, but instead have two successive transitions.  Allowing
    interruption between the two would dramatically weaken the host invariant (we conjecture).

    **POSIX: says, in the *INFORMATIVE* section *APPLICATION USAGE*, that the state of the socket is
    unspecified if connect() fails.  Perhaps we should model this accurately.

   :*)
   )

/\

   (!h ts tid d t sid e sock n opts
     SS MM.

   resourcefail_2 /* rp_all, slow nonurgent badfail (*: Fail with [[ENFILE]], [[ENOBUFS]] or
     [[ENOMEM]]: from a blocked state with out of resources :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(t,d)) |>,SS,MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(Ret (FAIL e),sched_timer)) |>,SS,MM)

   <==

   ~INFINITE_RESOURCES /\
   sock = (h.socks ' sid) /\
   ((t = Accept2(sid) /\ e IN {ENFILE; ENOBUFS; ENOMEM}) \/
    (t = Connect2(sid) /\ e = ENOBUFS) \/
    (t = Recv2(sid,n,opts) /\ e IN {ENOBUFS; ENOMEM}))


   (*:

    @description

    If thread [[tid]] of host [[h]] is in state [[Accept2(sid)]], [[Connect2(sid)]] or
    [[Recv2(sid)]] following an [[accept()]], [[connect()]] or [[recv()]] system call that blocked,
    and the host has subsequently exhausted its system-wide resources, fail with [[ENFILE]],
    [[ENOBUFS]] or [[ENOMEM]]. The error is immediately returned to the thread that made the system
    call.

    Calls to [[connect()]] only return [[ENOBUFS]] when resources are exhausted and calls to
    [[recv()]] only return [[ENOBUFS]] or [[ENOMEM]].

    This rule applies only when it is assumed that the host being modelled does not have
    [[INFINITE_RESOURCES]], i.e. the host does not have unlimited memory, mbufs, file descriptors,
    etc.

    @modeldetails

    The modelling of failure is deliberately non-deterministic because the cause of errors such as
    [[ENFILE]] are determined by more than is modelled in this specification. In order to be more
    precise, the model would need to describe the whole system to determine when such error
    conditions could and should arise.

    @internal

    Merged together several rule comments. Have omitted the comments that said nothing interesting.

    -=-=- From old [[accept_6]]:

    If the user calls [[accept()]] on a socket, or the user has called this and is blocked in the
    [[Accept2]] state, then any of these bad (resource-related) errors may nondeterministically
    occur: [[ENFILE]], [[ENOBUFS]], [[ENOMEM]].

    POSIX: "shall fail..." / "may fail...".  Very nondeterministic, since we do not want to be too
    specific.  Check.

    We're assuming, though, that buffers are only needed once we've found the socket, i.e., that
    [[EBADF]] and [[ENOTSOCK]] take priority over all the named errors.

    -=-=- From old [[connect_6]]:

    At any point, the kernel may run out of resources (buffer space) and return [[ENOBUFS]].

    This is very nondeterministic.  Notice that we \emph{do not} allow this to happen from the
    [[Connect1]] state, because that is an artifact of the LTS construction - we really want to have
    two labels on a single transition, but instead have two successive transitions.  Allowing
    interruption between the two would dramatically weaken the host invariant (we conjecture).

    **POSIX: says, in the *INFORMATIVE* section *APPLICATION USAGE*, that the state of the socket is
    unspecified if connect() fails.  Perhaps we should model this accurately.

  :*)
  )

/\

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[tcp_input_processing]] Host LTS: TCP Input Processing

TODO3

:*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(*: @section [[tcp_input_processing]] TCP Input Processing

These rules deal with the processing of TCP segments from the host's input queue.
The most important are [[deliver_in_1]], [[deliver_in_2]], and [[deliver_in_3]].

[[deliver_in_1]] deals with a passive open: a socket in [[LISTEN]] state that receives a [[SYN]] and sends a [[SYN,ACK]].

[[deliver_in_2]] deals with the completion of an active open: a socket in [[SYN_SENT]] state (that has previously sent a [[SYN]] with the [[connect_1]] rule) that receives a [[SYN,ACK]] and sends an [[ACK]].  It also deals with simultaneous opens.

[[deliver_in_3]] deals with the common cases of TCP data exchange and connection close: sockets in connected states that receive data, [[ACK]]s, and [[FIN]]s.
This rule is structured using the relational monad, combining auxiliaries
[[di3_topstuff]], [[di3_ackstuff]], [[di3_datastuff]] etc., to factor out many of the imperative effects of the code.

The other rules deal with [[RST]]s and a variety of pathological situations.

:*)


    (!h socks socks'
    fid sid sf es is1 is2 ps2 p1 cb lis seg iq iq' oq oq' cantsndmore cantrcvmore
    i1 i2 p2
    lis' sid' cb' cb'' sf'
    rcvbufsize' sndbufsize'
    q0' sock
    iflgs idata oflgs odata SS s s' s'' MM.

  deliver_in_1 /* rp_tcp, network nonurgent (*: Passive open: receive SYN, send SYN,ACK :*) */
     (h with <| socks := socks |++ [(sid,sock)];
               iq := iq ;
               oq := oq |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
   -- Lh_tau -->
     (h with <| socks := socks' |++
                  (*: Listening socket :*)
                 [(sid,Sock(SOME fid,sf,is1,SOME p1,is2,ps2,es,cantsndmore,cantrcvmore,
                             TCP_Sock(LISTEN,cb,SOME lis')));
                  (*: New socket formed by the incoming SYN :*)
                  (sid',Sock(NONE,sf',SOME i1,SOME p1,SOME i2,SOME p2,NONE,cantsndmore,cantrcvmore,
                             TCP_Sock(SYN_RECEIVED,cb'',NONE)))] ;
               iq := iq' ;
               oq := oq' |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s'')],MM)

   <==

    (*: \textbf{Summary:} A host [[h]] with listening socket [[sock]] referenced by index [[sid]] receives a valid and
    well-formed [[SYN]] segment [[seg]] addressed to socket [[sock]]. A new socket in the
    [[SYN_RECEIVED]] state is constructed, referenced by [[sid' (<> sid)]], is added to the queue of
    incomplete incoming connection attempts [[q]], and a [[SYN]],[[ACK]] segment is generated in
    reply with some field values being chosen or negotiated. The reply segment is finally queued on
    the host's output queue for transmission, ignoring any errors upon queueing failure.
    :*)

    sid NOTIN (FDOM socks) /\
    sid' NOTIN (FDOM socks) /\
    sid <> sid' /\

    (*: The segment must be of an acceptable form :*)
    (*: Note: some segment fields are ignored during TCP connection establishment and as such may
        contain arbitrary values. These are equal to the identifiers postfixed with
        [[_discard]] below, which are otherwise unconstrained. :*)
    read (i1,p1,i2,p2) T F (iflgs,idata) s s' /\
    iflgs = iflgs with <| SYN := T; SYNACK := F; RST := F |> /\
    idata IN UNIV /\

    (*: The segment is addressed to an [[IP]] address belonging to one of the interfaces of host
        [[h]] and is not addressed from or to a link-layer multicast or an IP-layer broadcast
        address :*)
    i1 IN local_ips h.ifds /\
    ~(is_broadormulticast h.ifds i1) /\
    ~(is_broadormulticast h.ifds i2) /\

    (*: Find the socket [[sock]] that has the best match for the address quad in segment
        [[seg]], see {@link [[tcp_socket_best_match]]}. Socket [[sock]] must have a form matching the patten [[Sock]](\dots). :*)
    tcp_socket_best_match socks (sid,sock) seg h.arch /\
    sock = Sock(SOME fid,sf,is1,SOME p1,is2,ps2,es,cantsndmore,cantrcvmore,
                TCP_Sock(LISTEN,cb,SOME lis)) /\

    (* BSD listen bug *)
    (*: A BSD socket in the [[LISTEN]] state may have its peer's [[IP]] address [[is2]] and port
        [[ps2]] set because [[listen()]] can be called from any TCP state. On other architectures
        they are both constrained to [[NONE]]. :*)
    ((is2 = NONE /\ ps2 = NONE) \/
     (bsd_arch h.arch /\ is2 = SOME i2 /\ ps2 = SOME p2)) /\

    (*: If socket [[sid]] has a local [[IP]] address specified it should be the same as the
        destination [[IP]] address of the segment [[seg]], otherwise the [[seg]] is not
        addressed to this socket. If the socket does not have a local [[IP]] address the segment is
        acceptable because the socket is listening on all local [[IP]] addresses. The segment must
        not have been sent by socket [[sock]].  Note: a socket is permitted to connect to itself by
        a simultaneous open. This is handled by {@link [[deliver_in_2]]} and not here. :*)
    (case is1 of SOME i1' -> i1' = i1 || NONE -> T) /\
    ~(i1 = i2 /\ p1 = p2) /\

    (*: If another socket in the [[TIME_WAIT]] state matches the address quad of the SYN segment
        then only proceed with the new incoming connection attempt if the sequence number of the
        segment [[seq]] is strictly greater than the next expected sequence number on the
        [[TIME_WAIT]] socket, [[rcv_nxt]]. This prevents old or duplicate SYN segments from previous
        incarnations of the connection from inadvertently creating new connections. :*)
     ~(? (sid, sock) :: socks.
       ? tcp_sock.
        sock.pr = TCP_PROTO(tcp_sock) /\
        tcp_sock.st = TIME_WAIT /\
        sock.is1 = SOME i1 /\ sock.ps1 = SOME p1 /\ sock.is2 = SOME i2 /\ sock.ps2 = SOME p2 /\
        F ) /\

    (*: Otherwise, the [[TIME_WAIT]] sock is completely defunct because there is a new connection
        attempt from the same remote end-point. Close it completely. :*)
    (*: Note: this models the behaviour in RFC1122 Section 4.2.2.13 which states that a new [[SYN]]
        with a sequence number larger than the maximum seen in the last incarnation may reopen the
        connection, \ie, reuse the socket for the new connection changing out of the [[TIME_WAIT]]
        state. This is modelled by closing the existing [[TIME_WAIT]] socket and creating the new
        socket from scratch. :*)
    socks' = $o_f (\sock.
        if ?tcp_sock. sock.pr = TCP_PROTO(tcp_sock) /\
           tcp_sock.st = TIME_WAIT /\
           sock.is1 = SOME i1 /\ sock.ps1 = SOME p1 /\
           sock.is2 = SOME i2 /\ sock.ps2 = SOME p2
        then
	    tcp_close h.arch sock
	else
	    sock
    ) socks /\

    (*: Accept the new connection attempt to the incomplete connection queue if the queue of
        completed (established) connections is not already full :*)
    (*  REMARK this forces accept; should be looser? *)
    accept_incoming_q0 lis T /\

    (*: Possibly drop an arbitrary connection from the queue of incomplete connection
        attempts -- this covers the behaviour of FreeBSD when the oldest connection in the SYN bucket
        or in the whole SYN cache is dropped, depending upon which became full. :*)
    (choose drop :: drop_from_q0 lis.
       if drop then
         ?q0L sid'' q0R.
           lis.q0 = APPEND q0L (sid'' :: q0R) /\
           q0' = APPEND q0L q0R
       else
         q0' = lis.q0
     ) /\

    (*: Put the new incomplete connection on the (possibly pruned) incomplete connections queue. :*)
    lis' = lis with <| q0 := sid' :: q0' |> /\

    (*: Create a SYN,ACK segment in reply: :*)
    rcvbufsize' IN UNIV /\ sndbufsize' IN UNIV /\

    (*: Store the new receive and send buffer sizes :*)
    sf' = sf with <| n := funupd_list sf.n [(SO_RCVBUF,rcvbufsize'); (SO_SNDBUF,sndbufsize')] |> /\

    (*: Update the new connection's control block in light of above. :*)
    cb' = cb with <|
              (* guessing here (with aid of TCPv2), 'cos BSD does it all with syncaches *)
              tt_keep           := SOME (Timed((),slow_timer TCPTV_KEEP_IDLE))
      |> /\

     (*: Construct the SYN,ACK segment using the values stored in the updated control block for the
         new connection. :*)
     oflgs = oflgs with <| SYN := F; SYNACK := T; FIN := F; RST := F |> /\
     odata IN UNIV /\
     write (i1,p1,i2,p2) (oflgs,odata) s' s''

  (*

    description

    ---- Alternative (BUT INCOMPLETE) text ----

    <insert some short overview paragraph here>

    The segment [[seg]] at the head of the host's input queue is addressed to the [[IP]] address
    [[i1]] assigned to one of the interfaces of host [[h]]. Address [[i1]] is not a link-layer
    broadcast or IP-multicast address. The TCP socket referenced by [[sid]] is the socket that has
    the most specific address quad matching the segment's address quad and is in the [[LISTEN]]
    state. The socket's remote address pair [[is2]] and [[ps2]] most both be [[NONE]].

    If the socket's local address [[is1]] is not a wildcard ([[NONE]]), the local address of the
    socket must be the [[IP]] address the segment was destined for, \ie, [[i1]]. Also, the segment
    must not have been sent from the socket itself as no sequence of socket calls exists to achieve
    a self-connect on a socket once in the [[LISTEN]] state. (Note: self-connects are possible and
    these are modelled through the simultaneous open behaviour of {@link [[deliver_in_2]]}).

    If another socket also matches the incoming segment and this socket is in the [[TIME_WAIT]]
    state, the new connection is only permitted to proceed if the new [[SYN]]'s sequence number is
    greater than the highest sequence number seen on the [[TIME_WAIT]] socket, [[rcv_nxt]], in which
    case the [[TIME_WAIT]] socket is closed and the new connection is allowed to proceed.

    The connection is allowed to proceed only if the socket's completed connections queue [[q0]] is
    not full and is added to the end of the socket's incomplete connection queue. On FreeBSD the
    incomplete connection queue is modelled by a SYN cache which itself, or one of its buckets, may
    be full, in which case the oldest connection is dropped from either the bucket or cache,
    whichever was full. This is modelled by allowing any single arbitrary connection to be dropped
    from the incomplete connections queue.

    At this stage the received segment is valid and a new connection attempt proceeds, \ie, this rule
    matches.  A [[SYN]],[[ACK]] segment is created in reply to the initial [[SYN]] segment, the
    socket's control........

    <Meta-comment: Steve got bored at this point>
*)


(*:
    @description

    TODO3

    @variation FreeBSD

    On FreeBSD, the [[listen()]] socket call can be called on a TCP socket in any state, thus it is
    possible for a listening TCP socket to have a peer address, \ie, [[is2]] and [[ps2]] pair,
    specified. This in turn affects the behaviour of connection establishment because an incoming
    [[SYN]] segment only matches this type of listening socket if its address quad matches the
    socket's entire address quad, heavily restricting the usefulness of such a socket.

    Such a restrictive peer address binding is permitted by the model for FreeBSD only.


    @modeldetails

    During TCP connection establishment, BSD uses syn-caches and syn-buckets to protect against some
    types of denial-of-service attack. These techniques delay the memory allocation for a socket's
    data structures until connection establishment is complete. They are not modelled directly in
    this specification, which instead favours the use of the full socket structure for clarity. The
    behaviour is observationally equivalent provided correct bounds are applied to the lengths of
    the incoming connection queues.

    When a socket completes connection establishment, \ie, enters the [[ESTABLISHED]] state, BSD
    updates the socket's control block [[t_maxseg]] field to the minimum of the maximum segment size
    it advertised in the emitted SYN,ACK segment and that received in the SYN segment from the
    remote end. This update is later than perhaps it need be. This model updates the [[t_maxseg]] at
    the moment both the maximum segment values are known. As a consequence the initial maximum
    segment value advertised by the host must be stored just in case the SYN,ACK segment need be
    retransmitted.


    @internal

    We're not bothering with syncaches or syncookies at the moment, assuming that observationally
    they're the same as doing the obvious thing.

    any seq OK; ack probably zero but we should be permissive
    URG,PSH presumably OK if we're sending data in SYN packet (unusual but permitted)

    observe: FIN and data are OK, but we ignore it.  This models the BSD syncache behaviour.
    Essentially, it means that we'll only ACK the SYN, and the other end will have to retransmit any
    data and FIN once we're in a state capable of dealing with it.

    old comment follows:
    FIN means: need to set cantrcvmore or whatever, and maybe move to CLOSE\_WAIT??
    T allowed by TCP but never sent by BSD so do not try it just now
    FIN is in fact OK too: see RFC1025 and TCPv1p230; that would be a lamp-test packet

    data OK, although it looks like BSD's syncachey impl just drops it silently: should allow
    (nondet) anything between dropping and accepting, including accepting only n bytes (recall that
    we have not been able yet to advertise a window, so the remote end is guessing (unless it's less
    than 536 bytes? 235 bytes? which it has a right to expect is OK if you're doing that) (OTOH,
    what about a syncache that stores only say 16 bytes?? it's at least conceivable)

    scaling: if seg.scale is NONE then we cannot do scaling ourselves either.  Note that fact.
    Otherwise, we should log their preferred scale and we should set and send our own; or we could
    say seg'.scale is NONE too, in which case we are saying that neither of us is allowed to do
    scaling ("I do not understand that option").

    TCPv2pp933ff: tcp\_dooptions this implies that in a passive open, we do not need to remember
    either requested\_s\_scale or request\_r\_scale; in an active open, we'd need to remember what
    we said (i.e., request\_r\_scale) in fact, observe that in our model we only save
    request\_r\_scale, not requested\_s\_scale, and we initialise snd\_scale and rcv\_scale earlier
    than in BSD (i.e., at LISTEN -> SYN\_RECEIVED rather than at SYN\_RECEIVED->ESTABLISHED), simply
    not using their values if we're in SYN\_RECEIVED.  This is a nice simplification, but it is one
    thing that will make white-box testing a little less convenient (rcv\_adv is another)

    urp unconstrained

    now need to nondet decide if we will advertise or not?  Can we only make this choice if
    t\_maxseg' = 536, or is it an inequality?  see also RFC1122 4.2.2.6: RFC791 says that not
    sending it means any segment size is OK, but RFC1122 says impls SHOULD send it if it's not 536,
    and MAY send it if it is this suggests that we should nondet allow not sending an MSS option,
    irrespective of t\_maxseg'

    OK, based on TCPv2p903 we're all of a sudden very confused as to whether we need to *agree* on
    an MSS, or store independent MSSs for each direction (i.e., just store our send mss but do not
    require the other end to obey any particular mss), or if there are some weirder constraints.
    Also TCPv1p237 has something.

    and then, what about path MTU?? Highly amusing(?): ip\_icmp.c:791 has a list of all path MTUs
    possible

    ISS picking: note that the magic that creates this number should be sensitive to the special
    magic performed when receiving a SYN while in TIME\_WAIT; search for "iss = " in tcp\_input, or
    TCPv2p945.

    Reconnection of TIME\_WAIT sockets - BSD tcp\_input.c:1486 allows certain reconnections in
    TIME\_WAIT, but not \_these\_ ones

    BSD tcp_input.c:1486 says that if a new connection request comes in, and there happens to be an
    old connection still in TIME_WAIT, the old connection can be disregarded (as far as making a new
    connection goes) and is closed.

   :*)
   )

/\

   (!h socks iq iq' oq oq' sid fid sf i1 p1 i2 p2 cb es cantsndmore cantrcvmore
    sf' st' cb' cb''
    rcvbufsize' sndbufsize'
    data' tcp_sock FIN' cantrcvmore'
    t_softerror' iflgs idata oflgs odata SS s s' s'' MM.

   deliver_in_2 /* rp_tcp, network nonurgent (*: Completion of active open (in [[SYN_SENT]] receive SYN,ACK and send ACK) or simultaneous open (in [[SYN_SENT]] receive SYN and send SYN,ACK) :*) */
     (h with <| socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,
				   cantsndmore,cantrcvmore,TCP_PROTO tcp_sock))] ;
               iq := iq ;
               oq := oq |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,Sock(SOME fid,sf',SOME i1,SOME p1,SOME i2,SOME p2,es,
				   cantsndmore,cantrcvmore',
				   TCP_Sock(st',cb'',NONE)))] ;
               iq := iq' ;
               oq := oq' |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s'')],MM)

  <==

    tcp_sock = TCP_Sock0(SYN_SENT,cb,NONE) /\

    read (i1,p1,i2,p2) T F (iflgs,idata) s s' /\

    (iflgs.RST = F /\ (iflgs.SYN = T \/ iflgs.SYNACK = T)) /\

     rcvbufsize' IN UNIV /\ sndbufsize' IN UNIV /\
     sf' = sf with <| n := funupd_list sf.n [(SO_RCVBUF,rcvbufsize');
                                             (SO_SNDBUF,sndbufsize')] |> /\

     (*: softerror may be cleared during an active open :*)
     (if iflgs.SYNACK then t_softerror' = NONE \/ t_softerror' = cb.t_softerror
     else t_softerror' = cb.t_softerror) /\

     (*: data processing is much simpler here than in [[deliver_in_3]] because we know
     we will only ever receive the one [[SYN,ACK]] datagram (duplicates will
     be rejected, and there's only one datagram and so cannot be
     reordered). :*)
     data' = idata /\
     FIN' = iflgs.FIN /\

     cb' = cb with <|
              tt_keep     := SOME (Timed((),slow_timer TCPTV_KEEP_IDLE));  (* 2 hours *)
              t_softerror   := t_softerror'
           |> /\

     (oflgs,odata) IN (if iflgs.SYNACK then null_flgs_data
                       else (if bsd_arch h.arch then null_flgs_data
                             else make_syn_ack_flgs_data)) /\
     write (i1,p1,i2,p2) (oflgs,odata) s' s'' /\

     stream_enqueue_or_fail T h.arch h.rttab h.ifds (SOME i1,SOME i2) cb' cb'' /\

     (*: N.B. the flags are already written to the stream during the sync :*)

     (*: Note that we change state even if enqueuing or routing returned an error,
            trusting to retransmit to solve our problem. :*)
     (if iflgs.SYNACK then
          (*: completion of active open :*)
          (if ~FIN' then
              (cantrcvmore' = cantrcvmore /\
               st' IN
                (if cantsndmore = F then
  		   {ESTABLISHED}  (* MS: BSD only sets to F if received a FIN *)
                 else {FIN_WAIT_2;FIN_WAIT_1})) (*: we were trying to send a FIN from [[SYN_SENT]], so move straight
                                                  to [[FIN_WAIT_2]]. Definitely the case with BSD; should also be
                                                  true for other archs. :*)
           else
              (cantrcvmore' = T /\
               st' =
                 (if cantsndmore = F then
                    CLOSE_WAIT
                  else
                    LAST_ACK)))         (*: we were trying to send a FIN from [[SYN_SENT]] and also receive a
                                                  FIN, so we move straight into [[LAST_ACK]]. :*)
      else
          (*: simultaneous open :*)
          (if ~FIN' then
             (st' = SYN_RECEIVED /\
              cantrcvmore' = cantrcvmore)
            else
              (* should go to "SYN_RECEIVED*", i.e., remember we want to go to CLOSE_WAIT not ESTABLISHED later *)
             (st' = CLOSE_WAIT /\  (*: yes, really! (in BSD) even though we've not yet had our initial SYN acknowledged! See |tcp_input.c:2065 +/-2000| :*)
                                    (* MS: incorrect behaviour; we think this could be exploited as a BSD DoS attack *)
              cantrcvmore' = T))
     )


  (*:
    @description

    TODO3

    @internal

    Under BSD, there is a bug in |tcp_input()|, in that it does not call tcp_mss() to set t_maxseg and
    the buffer sizes, if the received SYN segment did not have the mss option set. Note that this
    only occurs in the case of active/sim opens, since the code in tcp_syncache.c for passive opens
    calls tcp_mss() correctly.

    ** SB: NEGOTIATED options on BSD **

    On the completion of an active open or during a simultaneous open the behavior below for
    timestamping and window scaling is correct (as per RFC1323 Section 1.4). Unfortunately not all
    architectures are fully RFC1323 compliant it seems.

    RFC1323 Section 1.4: "Therefore, for each of the extensions defined below, TCP options will be
    sent on non-SYN segments only when an exchange of options on the SYN segments has indicated that
    both sides understand the extension. Furthermore, an extension option will be sent in a
    <SYN,ACK> segment only if the corresponding option was received in the initial <SYN> segment."

    Linux breaks the condition stated in the second sentence quoted from RFC1323 above. During a
    simultaneous open, on receipt of the remote-ends SYN, a host emits a SYN,ACK segment. Linux adds
    timestamping options to this segment if it has timestamping enabled, regardless of whether the
    received SYN had a timestamp option or not. This is faked up below when we emit the SYN,ACK
    segment and we do not model it here (as the final state is the same once a SYN,ACK has been
    received by this host).

    TODO: is Linux Window Scaling also broken (wrt RFC1323) during a simultaneous open?

    Keith thinks: BSD always listens to a timestamp option, whether or not it was negotiated (i.e.,
    records in cb'), but only generates a reply if it was negotiated and agreed.

  :*)

)

/\

   (!h socks socks' iq iq' oq oq' sid sock sock' bndlm bndlm'
    i1 p1 i2 p2 tcp_sock tcp_sock'
    wesentafin wercvdafin ourfinisacked
    iflgs idata oflgs SS s s' s'' MM sock''
    .

   deliver_in_3 /* rp_tcp, network nonurgent (*: Receive data, FINs, and ACKs in a connected state :*) */
     (h with <| socks := socks |++ [(sid, sock)];
               iq := iq ;
               oq := oq ;
               bndlm := bndlm |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
   -- Lh_tau -->
     (h with <| socks := socks';
               iq := iq' ;
               oq := oq' ;
               bndlm := bndlm' |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s'')],MM)

   <==

    sid NOTIN (FDOM socks) /\
    sock.pr = TCP_PROTO(tcp_sock)  /\

    (*: Assert that the socket meets some sanity properties. This is logically superfluous  but
        aids semi-automatic model checking. See {@link [[sane_socket]]} for further details. :*)
    sane_socket sock /\

    (*: Take TCP segment [[seg]] from the head of the host's input queue :*)
    read (i1,p1,i2,p2) T F (iflgs,idata) s s' /\

    (*: The segment must be of an acceptable form :*)
    (*: Note: some segment fields (namely TCP options [[ws]] and [[mss]]), are only used during
        connection establishment and any values assigned to them in segments during a connection are
        simply ignored. They are equal to the identifiers [[ws_discard]] and
        [[mss_discard]] respectively, which are otherwise unconstrained. :*)
    iflgs.RST = F /\

    (*: The socket is fully connected so its complete address quad must match the address
        quad of the segment [[seg]]. By definition, [[sock]] is the socket with the best address
        match thus the auxiliary function [[tcp_socket_best_match]] is not required here. :*)
    sock.is1 = SOME i1 /\ sock.ps1 = SOME p1 /\
    sock.is2 = SOME i2 /\ sock.ps2 = SOME p2 /\

    (*: The socket must be in a connected state, or is in the [[SYN_RECEIVED]] state and
        [[seg]] is the final segment completing a passive or simultaneous open. :*)
    tcp_sock.st NOTIN {CLOSED;LISTEN;SYN_SENT} /\
    tcp_sock.st IN {SYN_RECEIVED;ESTABLISHED;CLOSE_WAIT;FIN_WAIT_1;FIN_WAIT_2;
                    CLOSING;LAST_ACK;TIME_WAIT} /\

    (*: If socket [[sock]] has previously emitted a [[FIN]] segment check that a thread is still
        associated with the socket, i.e.~check that the socket still has a valid file identifier
        [[fid <> NONE]]. If not, and the segment contains new data, the segment should not be
        processed by this rule as there is no thread to read the data from the socket after
        processing.  Query: how does this [[st]] condition relate to [[wesentafin]] below? :*)
    (? cond. ~(tcp_sock.st IN {FIN_WAIT_1; CLOSING; LAST_ACK; FIN_WAIT_2; TIME_WAIT} /\
      cond)) /\

    (*: A [[SYN]] should be received only in the [[SYN_RECEIVED]] state. :*)
    (iflgs.SYN ==> tcp_sock.st = SYN_RECEIVED) /\

    (*: If the socket [[sock]] has previously sent a [[FIN]] segment it has been acknowledged by
        segment [[seg]] if the segment has the [[ACK]] flag set and an acknowledgment number [[ack
        >= cb.snd_max]]. :*)

    (ourfinisacked ==> (*oflgs.*)wesentafin) /\

    (*: [[wercvdafin]] approximated by [[iflgs.FIN]] :*)
    (wercvdafin = iflgs.FIN) /\

    (*: Process the segment and return an updated socket state :*)

    (
        (* topstuff *)
        ? sock0. di3_topstuff sock sock0 /\

        (* ackstuff *)
        ? sock1 FIN1 stop1. di3_ackstuff tcp_sock ourfinisacked h.arch h.rttab h.ifds sock0 (sock1,FIN1,stop1) /\
        if stop1 = T
        then
            (sock',oflgs.FIN) = (sock1,FIN1)
        else

        (* datastuff *)
        let datastuff theststuff =
            (*: Extract and reassemble data (including urgent data). See {@link [[di3_datastuff]]}. :*)
            di3_datastuff (*iflgs.*)wercvdafin (* really FIN_reass *) theststuff ourfinisacked
        and ststuff FIN_reass =
            (*: Possibly change the socket's state (especially on receipt of a valid [[FIN]]). See
                {@link [[di3_ststuff]]}. :*)
            di3_ststuff (*iflgs.*)wercvdafin (* FIN_reass *) ourfinisacked
        in
        ?sock2 FIN2. datastuff ststuff sock1 (sock2,FIN2) /\
        (sock',oflgs.FIN) = (sock2, FIN2 \/ FIN1)
    ) /\

    sock'.pr = TCP_PROTO(tcp_sock') /\
    sock'' = sock' /\

    (*: If socket [[sock]] was initially in the [[SYN_RECEIVED]] state and after processing [[seg]]
        is in the [[ESTABLISHED]] state (or if the segment contained a [[FIN]] and the socket is in one of the
        [[FIN_WAIT_1]], [[FIN_WAIT_2]] or [[CLOSE_WAIT]] states), the socket is probably on some
        other socket's incomplete connections queue and [[seg]] is the final segment in a passive
        open. If it is on some other socket's incomplete connections queue the other socket is
        updated to move the newly connected socket's reference from the incomplete to the complete
        connections queue (unless the complete connection queue is full, in which case the new
        connection is dropped and all references to it are removed).  If not, [[seg]] is the final
        segment in a simultaneous open in which case no other sockets are updated.  The auxiliary
        function {@link [[di3_socks_update]]} does all the hard work, updating the relevant
        sockets in the finite map [[socks]] to yield [[socks']]. :*)
    (if tcp_sock.st = SYN_RECEIVED /\
        tcp_sock'.st IN {ESTABLISHED; FIN_WAIT_1; FIN_WAIT_2; CLOSE_WAIT} then
          di3_socks_update sid (socks |+ (sid,sock'')) socks'
     else
        (*: If the socket was not initially in the [[SYN_RECEIVED]] state, \ie [[seg]] was processed
            by an already connected socket, ensure the updated socket is in the final finite
            maps of sockets. :*)
        socks' = socks |+ (sid,sock'')) /\
    write (i1,p1,i2,p2) (oflgs,[]) s' s''



 (*:
    @description

    TODO3

    @internal

    rule is defined by several relations.  Each relates a (before-)socket and a triple:
    (after-)socket, segment list to output, flag.  The flag is T if we should continue and apply the
    remaining relations, and F if we should stop now.  Sorry for the temporality of this
    explanation.

    ((sock',outsegs),continue) is: new socket, segments to output, keep going flag

    No sock with [[sock]] on the listen queue:

    there is no corresponding listening socket, which means that we must have entered SYN_RECEIVED
    due to a simultaneous open, so we want to allow the rule to fire, without updating any listen
    queues.  MS: point of note here; we do NOT test for simultaneous open in this case on the basis
    of whether SYN was set in the segment, as this is not a reliable way of determining the socket's
    state - i.e. we could potentially receive a SYN in the case of a normal passive open, in which
    case we do still want to update the listen queue. The user cannot have a handle on the socket if
    it is in SYN_RECEIVED as part of a passive open, so the only way for it to exist is for the
    listening socket to be present. Therefore it is safe to assume that if no listening socket is
    present, the socket must have entered SYN_RECEIVED by some means other than a passive open,
    i.e. through a simultaneous open.

    Talking about enqueue_oq_list_qinfo:

    NB: we use the relational form of the specification to good effect here, and it feels a bit like
    an attribute grammar.  The specification above decides which segments to emit, but it is the
    enqueueing operation below that decides whether each segment is queued successfully or not.
    Thus the first element of each pair (the message) is constrained above, and the second element
    (the queued flag) is constrained here.  That flag is then used above to decide whether state
    must be rolled back to account for the queueing failure.

 :*)

  )

/\

   (!h socks socks' iq iq' oq oq' sid sock_0 bndlm bndlm'
    i1 p1 i2 p2 tcp_sock_0
    iflgs idata oflgs odata SS SS' MM.










   deliver_in_3b /* rp_tcp, network nonurgent (*: Receive data after process has gone away :*) */
     (h with <| socks := socks;
               iq := iq ;
               oq := oq ;
               bndlm := bndlm |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks';
               iq := iq' ;
               oq := oq' ;
               bndlm := bndlm' |>,
     SS',MM)

   <==

    (* not INLINE, so must be PEEK *)
    (*: \textbf{Summary:} if data arrives after the process associated with a socket has gone away,  close socket and emit RST segment. :*)

    sid IN FDOM socks /\
    sock_0 = socks ' sid /\
    sock_0.is1 = SOME i1 /\ sock_0.ps1 = SOME p1 /\ sock_0.is2 = SOME i2 /\ sock_0.ps2 = SOME p2 /\
    sock_0.pr = TCP_PROTO(tcp_sock_0) /\

    ? S0 s s'.  SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
    read (i1,p1,i2,p2) T F (iflgs,idata) s s' /\
    iflgs = iflgs with <| SYN := F; SYNACK := F; RST := F |> /\
    idata IN UNIV /\

    (*: Note that there does not exist a better socket match to which the segment should be sent, as the whole quad is matched exactly. :*)

    (*: test that this is data arriving after process has gone away :*)
    tcp_sock_0.st IN {FIN_WAIT_1; CLOSING; LAST_ACK; FIN_WAIT_2; TIME_WAIT} /\
    sock_0.fid = NONE /\  (* why not check cantrcvmore instead?? *)

    (*: close socket and emit RST segment :*)
    socks' = socks |+ (sid,tcp_close h.arch sock_0) /\
    oflgs = oflgs with <| SYN := F; SYNACK := F; FIN := F; RST := T |> /\
    odata IN UNIV /\
    ? s''.
    write (i1,p1,i2,p2) (oflgs,odata) s' s'' /\
    destroy (i1,p1,i2,p2) (S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s'')]) SS'



   )

/\
   (!h iq iq' seg is1 i2
     SS MM.










   deliver_in_4 /* rp_tcp, network nonurgent (*: Receive and drop (silently) a non-sane or martian segment :*) */
     (h with <| iq := iq |>,SS,MM)
   -- Lh_tau -->
     (h with <| iq := iq' |>,SS,MM)

   <==

   (*: \textbf{Summary:}
   Receive and drop any segment for this host that does not have sensible checksum or offset fields,
   or one that originates from a martian address.  The first part of this condition is a
   placeholder, awaiting the day when we switch to a non-lossy segment representation, hence the
   [[F]].
   :*)

     dequeue_iq(iq,iq',SOME (TCP seg)) /\
     seg.is2 = SOME i2 /\  (* really we know this from deliver_in_99; remove? *)
     is1 = seg.is1 /\
     i2 IN local_ips(h.ifds) /\  (* really we know this from deliver_in_99; remove? *)
     (F \/                  (*: placeholder for segment checksum and offset field not sensible :*)
      ~( (* condition from deliver_in_1 (should not this only apply when the quad matches
            a socket in listen?)  I think BSD only checks on matching -RST SYN -ACK segs: *)
        T /\  (*: placeholder for not a link-layer multicast or broadcast :*)
        ~(is_broadormulticast h.ifds i2) /\  (*: seems unlikely, since [[i1 IN local_ips h.ifds]] :*)
        ~(is1 = NONE) /\
        ~is_broadormulticast h.ifds (THE is1)
      )
     )


   )

/\

   (!h iq iq' oq oq' bndlm bndlm'
    i1 p1 i2 p2 idata iflgs odata oflgs SS s s' s'' MM.










   deliver_in_5 /* rp_tcp, network nonurgent (*: Receive and drop (maybe with RST) a sane segment that does not match any socket :*) */
     (h with <| iq := iq ;
               oq := oq ;
               bndlm := bndlm |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
   -- Lh_tau -->
     (h with <|iq := iq' ;
              oq := oq' ;
              bndlm := bndlm' |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s'')],MM)

   <==

   (*: \textbf{Summary:}
   Receive and drop any segment for this host that does not match any sockets (but does have
   sensible checksum and offset fields). Typically, generate RST in response, computing [[ack]] and [[seq]] to supposedly  make the other
   end see this as an 'acceptable ack'.
   :*)

     read (i1,p1,i2,p2) T F (iflgs,idata) s s' /\

     i1 IN local_ips(h.ifds) /\  (* IP matches this host *)

     T /\                                              (*: placeholder for segment checksum and offset field sensible :*)

     ~(? ((sid,sock) :: h.socks) tcp_sock.
          sock.pr = TCP_PROTO(tcp_sock) /\
          match_score (sock.is1, sock.ps1, sock.is2, sock.ps2)
                      (i2, SOME p2, i1,SOME p1) > 0
       ) /\ (* no sock matches *)

     dropwithreset iflgs.RST (SOME i2, SOME i1) h.ifds oflgs.RST /\
     oflgs.SYN = F /\
     oflgs.SYNACK = F /\
     oflgs.FIN = F /\
     odata = [] /\
     write (i1,p1,i2,p2) (oflgs,odata) s' s''


   (*:
    @description

    TODO3

   @internal

   Not certain about ws,mss,ts -- think length-manipulation zaps them, but they might be inherited
   from the original segment?

   NB, what happens with pathological segments with zero is1,ps1 or ps2?
   :*)
   )

/\
(* has no effect on stream, so removed. May want to keep in if we wish to track stream syncs below socket layer.
   (!h iq iq' seg
     i1
     SS MM.










   deliver_in_6 /* rp_tcp, network nonurgent (*: Receive and drop (silently) a sane segment that matches a [[CLOSED]] socket :*) */
     (h with <| iq := iq |>,SS,MM)
   -- Lh_tau -->
     (h with <| iq := iq' |>,SS,MM)

   <==

   (*: \textbf{Summary:}
   Receive and drop any segment for this host that does not match any sockets (but does have
   sensible checksum or offset fields).

   Note that pathological segments where [[is1]], [[ps1]], or [[ps2]] are not set in the segment are
   not dealt with here but need to be.  :*)

     (* REMARK this rule must remain in Spec3 *)
     dequeue_iq(iq,iq',SOME (TCP seg)) /\
     (? ((sid,sock) :: h.socks) tcp_sock.
          sock.pr = TCP_PROTO(tcp_sock) /\
          match_score (sock.is1, sock.ps1, sock.is2, sock.ps2)
                      (THE seg.is1, seg.ps1, THE seg.is2, seg.ps2) > 0 /\
          tcp_socket_best_match h.socks (sid,sock) seg h.arch /\
          tcp_sock.st = CLOSED) /\
          seg.is2 = SOME i1 /\  i1 IN local_ips(h.ifds) /\  (* IP matches this host *)
          T (*: placeholder for segment checksum and offset field sensible :*)


   )

/\
*)

   (!h iq iq' socks sock
     ts tid ts_st d
     sid fid sf i1 p1 i2 p2 st cb es cantsndmore cantrcvmore
     err sock'
     iflgs idata SS SS' MM.

   deliver_in_7 /* rp_tcp, network nonurgent (*: Receive RST and zap non-[[{CLOSED]]; [[LISTEN]]; [[SYN_SENT]]; [[SYN_RECEIVED]]; [[TIME_WAIT}]] socket :*) */
     (h with <| ts := FUPDATE ts (tid,Timed(ts_st,d));
               socks := socks |++ [(sid,sock)] ;
               iq := iq |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| ts := FUPDATE ts (tid,Timed(ts_st,d));
               socks := socks |++ [(sid,sock')] ;
               iq := iq' |>,
     SS',MM)

   <==

     (*: \textbf{Summary:} receive RST and silently zap non-[[{CLOSED]]; [[LISTEN]]; [[SYN_SENT]]; [[SYN_RECEIVED]]; [[TIME_WAIT}]] socket :*)

     sock = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                 TCP_Sock(st,cb,NONE)) /\
     st NOTIN {CLOSED; LISTEN; SYN_SENT; SYN_RECEIVED; TIME_WAIT} /\

     ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
     read (i1,p1,i2,p2) T F (iflgs,idata) s s' /\
     iflgs.RST = T /\
     idata IN UNIV /\

     (* there does not exist a better socket match to which the segment should be sent, as the whole quad is matched *)

     ( (*: [[sock.st IN {CLOSED; LISTEN; SYN_SENT; SYN_RECEIVED; TIME_WAIT}]]
          excluded already above :*)
      if st IN {ESTABLISHED; FIN_WAIT_1; FIN_WAIT_2; CLOSE_WAIT} then
          err = SOME ECONNRESET
      else (*: [[sock.st IN {CLOSING; LAST_ACK}]] -- leave existing error :*)
          err = sock.es) /\

     (* no need to reset tt_fin_wait_2 in FIN_WAIT_2, because we're about to zap the socket *)

     (*: see {@link [[tcp_close]]} :*)
     sock' = tcp_close h.arch (sock with <| es := err |> ) /\
     destroy (i1,p1,i2,p2) (S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]) SS'

     (* this was previously calling tcp_drop_and_close which was expecting an RST to be on the output
        queue. Obviously, we do not want to send an RST in response to an RST! *)

     (* TODO: check sequence number is in the right range; cf tcp_input.c:1447 and rfc793:4272 *)
     (* TODO: P does not see why that assert is true *)
     (* gather together all the 'zap socket on receipt of a RST' cases together here *)
     (* this based on TCPv2p963ff, with a partial skim of previous control-flow (not sure why RST
        processing is so late, in fact - maybe to be after both fast-path and active/passive conn
        est) *)
     (* wrt RSTs in SYN_RECEIVED, I (P) do not understand TCPv2p963 at all... surely the 'new socket'
        was part of an earlier invocation of tcp_input? *)
     (* cb' = ... initial_cb ...  really, it does not exist - but we initialise ours in socket_1, not
        at connect or listen time...?  Guess should pull our defn of initial_cb *)
     (* guessing about other socket fields - should we leave [[sf]] alone, for example? *)
     (* Level 3 is going to have to update cached metrics, as tcp_close does *)



   )

/\

   (!h iq iq' socks sock
     sid fid sf i1 p1 i2 p2 cb es cantsndmore cantrcvmore
     sock' socks_update'
     iflgs idata SS SS' MM.

   deliver_in_7a /* rp_tcp, network nonurgent (*: Receive RST and zap [[SYN_RECEIVED]] socket :*) */
     (h with <| socks := socks |++ [(sid,sock)];
               iq := iq |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++ socks_update';
               iq := iq' |>,
     SS',MM)

  <==

     (*: \textbf{Summary:} receive RST and zap [[SYN_RECEIVED]] socket, removing from listen queue etc. :*)

    ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
    read (i1,p1,i2,p2) T F (iflgs,idata) s s' /\
    iflgs.RST = T /\
    idata IN UNIV /\

    sid NOTIN FDOM socks /\
    (* Not a better sock match as the whole quad is matched *)
    sock = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                TCP_Sock(SYN_RECEIVED,cb,NONE)) /\

    ( (*: There is a corresponding listening socket -- passive open :*)
     (?(sid',lsock) :: socks \\ sid.
      ?tcp_lsock lis q0L q0R lsock'.
        lsock.pr = TCP_PROTO(tcp_lsock) /\
        tcp_lsock.st = LISTEN /\
        tcp_lsock.lis = SOME lis /\
        lis.q0 = APPEND q0L (sid :: q0R) /\
        lsock' = lsock with
          <| pr := TCP_PROTO(tcp_lsock with <| lis :=
                     SOME (lis with <| q0 := APPEND q0L q0R |>) |>) |> /\  (* remove from q0 *)
        socks_update' = [(sid',lsock'); (sid,sock')]
    ) \/
    ( (*: No corresponding socket -- simultaneous open :*)
      socks_update' = [(sid,sock')] )) /\

    (*: We do not delete the socket entry here because of simultaneous opens.
    Keep existing error for [[SYN_RECEIVED]] socket on RST :*)
    sock' = (tcp_close h.arch sock) with <| ps1 := if bsd_arch h.arch then NONE else sock.ps1 |> /\
    destroy (i1,p1,i2,p2) (S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]) SS'



  (*:
    @description

    TODO3

    @internal

    in BSD, sock is just a syncache entry, so here BSD removes the entry completely without setting
    any error (nowhere to set it), whereas we bzero the cb of the socket and set an error.  Believe
    this error is not observable (and the socket is unreachable) because the socket is only on
    lis.q0.  Slightly concerned that the socket never gets gc'd from there - it's just CLOSED and on
    lis.q0

  :*)
)

/\

   (!h iq iq' socks seg sock
     sid fid sf i1 p1 i2 p2 is1 is2 ps2 cb lis es cantsndmore cantrcvmore
     SS MM.

   deliver_in_7b /* rp_tcp, network nonurgent (*: Receive RST and ignore for [[LISTEN]] socket :*) */
     (h with <| socks := socks |++ [(sid,sock)] ;
               iq := iq |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++ [(sid,sock)] ;
               iq := iq' |>,
     SS,MM)

   <==

     (*: \textbf{Summary:} receive RST and ignore for [[LISTEN]] socket :*)

     dequeue_iq(iq,iq',SOME (TCP seg)) /\
     sock = Sock(SOME fid,sf,is1,SOME p1,is2,ps2,es,cantsndmore,cantrcvmore,
                 TCP_Sock(LISTEN,cb,lis)) /\

     (*: BSD listen bug -- since we can call [[listen()]] from any state, the peer IP/port may have been set :*)
     ((is2 = NONE /\ ps2 = NONE) \/
      (bsd_arch h.arch /\ is2 = SOME i2 /\ ps2 = SOME p2)) /\

     (* condition from deliver_in_1: *)
     i1 IN local_ips h.ifds /\
     T /\  (*: placeholder for not a link-layer multicast or broadcast :*)
     (*: seems unlikely, since [[i1 IN local_ips h.ifds]] :*)
     ~(is_broadormulticast h.ifds i1) /\
     ~(is_broadormulticast h.ifds i2) /\
     (case is1 of
          SOME i1' -> i1' = i1 ||
          NONE -> T) /\

     (?seq_discard ack_discard URG_discard ACK_discard PSH_discard SYN_discard FIN_discard
       win_discard ws_discard urp_discard mss_discard ts_discard data_discard.
     seg = <|
            is1  := SOME i2;
            is2  := SOME i1;
            ps1  := SOME p2;
            ps2  := SOME p1;
            seq  := tcp_seq_flip_sense (seq_discard:tcp_seq_foreign);
            ack  := tcp_seq_flip_sense (ack_discard:tcp_seq_local);
            URG  := URG_discard;
            ACK  := ACK_discard;
            PSH  := PSH_discard;
            RST  := T;
            SYN  := SYN_discard;
            FIN  := FIN_discard;
            win  := win_discard;
            ws   := ws_discard;
            urp  := urp_discard;
            mss  := mss_discard;
            ts   := ts_discard;
            data := data_discard
           |>
     ) /\

     tcp_socket_best_match (socks \\ sid) (sid,sock) seg h.arch (*: there does not exist a better socket match to which the segment should be sent :*)



   )

/\

   (!h iq iq' socks sock sock' tcp_sock
     sid fid sf i1 p1 i2 p2 st cb es cantsndmore cantrcvmore
     iflgs idata SS s s' MM.

   deliver_in_7c /* rp_tcp, network nonurgent (*: Receive RST and ignore for [[SYN_SENT]](unacceptable ack) or [[TIME_WAIT]] socket :*) */
     (h with <| socks := socks |++ [(sid,sock)] ;
               iq := iq |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
   -- Lh_tau -->
     (h with <| socks := socks |++ [(sid,sock')] ;
               iq := iq' |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s')],MM)

   <==

     (*: \textbf{Summary:} receive RST and ignore for [[SYN_SENT]](unacceptable ack) or [[TIME_WAIT]] socket :*)

     read (i1,p1,i2,p2) T F (iflgs,idata) s s' /\
     sid NOTIN FDOM socks /\
     sock = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                 TCP_Sock(st,cb,NONE)) /\
     st IN {SYN_SENT; TIME_WAIT} /\

     iflgs.RST = T /\
     idata IN UNIV /\

     (* there does not exist a better socket match to which the segment should be sent, as the whole quad is matched *)

     (*: no- or unacceptable- ACK :*)
     (st = SYN_SENT ==> F) /\

     sock.pr = TCP_PROTO(tcp_sock) /\
     (if st = TIME_WAIT then  (*: only update if [[>= ESTABLISHED]], c.f.\ |tcp\_input.c:887| :*)
       sock' = sock with <| pr := TCP_PROTO(tcp_sock with
         <| cb := cb with
           <| tt_keep := SOME (Timed((),slow_timer TCPTV_KEEP_IDLE)) (* 2 hours *) |>
          |>) |>
     else (*: [[st = SYN_SENT]] :*)
       (*: BSD |rcv_wnd| bug: the receive window updated code in |tcp_input| gets executed \emph{before} the segment is
          processed, so even for bad segments, it gets updated :*)
       sock' = sock)


   (*:
    @description

    TODO3

   @internal

   tcp\_input.c:1362 for TIME\_WAIT, elsewhere for SYN\_SENT - do nothing.  NB: acceptable ACKs+RST in
   SYN\_SENT reset the connection.
   :*)

   )

/\
   (!h iq iq' socks sock sock'
     sid fid sf i1 p1 i2 p2 cb es cantsndmore cantrcvmore
     iflgs idata SS SS' MM.

   deliver_in_7d /* rp_tcp, network nonurgent (*: Receive RST and zap [[SYN_SENT]](acceptable ack) socket :*) */
     (h with <| socks := socks |++ [(sid,sock)] ;
               iq := iq |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++ [(sid,sock')];
               iq := iq' |>,
     SS',MM)

   <==

   (*: \textbf{Summary}
   Receiving an acceptable-ack RST segment: kill the connection and set the socket's error field appropriately,
   unless we are WinXP where we simply ignore the RST.
   :*)

     ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
     read (i1,p1,i2,p2) F F (iflgs,idata) s s' /\
     sid NOTIN FDOM socks /\
     sock = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                 TCP_Sock(SYN_SENT,cb,NONE)) /\

     iflgs.RST = T /\
     idata IN UNIV /\

     (* there does not exist a better socket match to which the segment should be sent, as the whole quad is matched *)

     if windows_arch h.arch then
         sock' = sock   (*: Windows XP just ignores RST's with a valid ack during connection establishment :*) /\
         SS' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]
     else
         (?err.
             err IN {ECONNREFUSED; ECONNRESET} /\ (*: Note it is unclear whether or not this error will overwrite any existing error on the socket :*)
             sock' = (tcp_close h.arch sock) with <| ps1 := if bsd_arch h.arch then NONE else sock.ps1; es := SOME err |> /\
             destroy (i1,p1,i2,p2) (S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]) SS')


   )

/\
   (!h iq iq' socks sock sock' bndlm bndlm' tcp_sock
     sid fid sf i1 p1 i2 p2 st cb es cantsndmore cantrcvmore oq
     oq'
     iflgs idata oflgs odata SS s s' s'' MM.

   deliver_in_8 /* rp_tcp, network nonurgent (*: Receive SYN in non-[[{CLOSED]]; [[LISTEN]]; [[SYN_SENT]]; [[TIME_WAIT}]] state :*) */
     (h with <| socks := socks |++ [(sid,sock)] ;
               iq := iq ;
               oq := oq ;
               bndlm := bndlm |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
   -- Lh_tau -->
     (h with <| socks := socks |++ [(sid,sock')] ;
               iq := iq' ;
               oq := oq' ;
               bndlm := bndlm' |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s'')],MM)

   <==

     (*: \textbf{Summary:}
     Receive a SYN in non-[[{CLOSED]]; [[LISTEN]]; [[SYN_SENT]]; [[TIME_WAIT}]] state.
     Drop it and (depending on the architecture) generate a RST. :*)

     sid NOTIN FDOM socks /\
     sock = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                 TCP_Sock(st,cb,NONE)) /\
     read (i1,p1,i2,p2) T F (iflgs,idata) s s' /\
     iflgs.RST = F /\ (iflgs.SYN \/ iflgs.SYNACK) /\
     idata IN UNIV /\

     (* there does not exist a better socket match to which the segment should be sent, as the whole quad is matched *)

     (*: Note that it may be the case that this rule should only apply when the SYN is \emph{in the
     trimmed window}, should not it?; it's OK if there's a SYN bit set, for example in a
     retransmission. :*)

     st NOTIN {CLOSED;LISTEN;SYN_SENT;TIME_WAIT} /\

     sock.pr = TCP_PROTO(tcp_sock) /\
     let tt_keep' = if tcp_sock.st <> SYN_RECEIVED then
                        SOME (Timed((),slow_timer TCPTV_KEEP_IDLE))
                    else
                        tcp_sock.cb.tt_keep in

     sock' = sock with <| pr := TCP_PROTO(tcp_sock with
       <| cb := tcp_sock.cb with <| tt_keep := tt_keep' |>
        |>) |> /\

     oflgs = oflgs with <| SYN := F; SYNACK := F; FIN := F; RST := T |> /\
     odata IN UNIV /\
     write (i1,p1,i2,p2) (oflgs,odata) s' s''



   )

/\
   (!h iq iq' socks seg sock oq oq' bndlm bndlm'
     sid fid sf i1 p1 i2 p2 cb es cantsndmore cantrcvmore
     iflgs idata oflgs odata SS s s' s'' MM.

   deliver_in_9 /* rp_tcp, network nonurgent (*: Receive SYN in [[TIME_WAIT]] state if there is no matching [[LISTEN]] socket or sequence number has not increased :*) */
     (h with <| socks := socks |++ [(sid,sock)] ;
               iq := iq;
               oq := oq;
               bndlm := bndlm |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
   -- Lh_tau -->
     (h with <| socks := socks |++ [(sid,sock)] ;
               iq := iq';
               oq := oq';
               bndlm := bndlm' |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s'')],MM)

   <==

     (*: \textbf{Summary:}
     Receive a SYN in [[TIME_WAIT}]] state where there is no matching [[LISTEN]] socket.
     Drop it and (depending on the architecture) generate a RST. :*)

     dequeue_iq(iq,iq',SOME (TCP seg)) /\

     sid NOTIN FDOM socks /\
     sock = Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                 TCP_Sock(TIME_WAIT,cb,NONE)) /\
     read (i1,p1,i2,p2) T F (iflgs,idata) s s' /\
     iflgs.RST = F /\ (iflgs.SYN \/ iflgs.SYNACK) /\
     idata IN UNIV /\

     (* there does not exist a better socket match to which the segment should be sent, as the whole quad is matched *)

     (*: no matching LISTEN socket, or the sequence number has not increased :*)
     (T
       \/
      ~(? ((sid,sock) :: socks) tcp_sock.
        sock.pr = TCP_PROTO(tcp_sock) /\
        tcp_sock.st = LISTEN /\
        sock.is1 IN {NONE;SOME i1} /\
        sock.ps1 = SOME p1)
     ) /\

     oflgs = oflgs with <| SYN := F; SYNACK := F; FIN := F; RST := T |> /\
     odata IN UNIV /\
     write (i1,p1,i2,p2) (oflgs,odata) s' s''

   (*:
   This rule does not appear in the BSD code; what happens there is that the old [[TIME_WAIT]] state
   socket is closed, and then the code jumps back to the top.  So this rule covers the case where it
   then discovers nothing else is listening, like [[deliver_in_5]].
   :*)


   )


/\

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[tcp_output]] Host LTS: TCP Output
TODO3
:*)

(*:

  @section [[tcp_output_section]] TCP Output



  A TCP implementation would typically perform output deterministically, e.g.\ during the processing
  a received segment it may construct and enqueue an acknowledgement segment to be emitted.  This
  means that the detailed behaviour of a particular implementation depends on exactly where the
  output routines are called, affecting when segments are emitted.  The contents of an emitted
  segment, on the other hand, must usually be determined by the socket state (especially the
  [[tcpcb]]), not from transient program variables, so that retransmissions can be performed.



  In this specification we choose to be somewhat nondeterministic, loosely specifying when
  common-case TCP output to occur.  This simplifies the modelling of existing implementations
  (avoiding the need to capture the code points at which the output routines are called) and should
  mean the specification is closer to capturing the set of all reasonable implementations.

  A significant defect in the current specification is that it does not impose a very tight lower
  bound on how often output takes place.  The satisfactory dynamic behaviour of TCP connections
  depends on an "ACK clock" property, with receivers  acknowledging data sufficiently often to
  update the sender's send window.  Characterising this may need additional constraints.

  The rule presented in this chapter describes TCP output in the common case, i.e.~the behaviour of
  TCP when emitting a non-SYN, non-RST segment. The whole behaviour is captured by the single rule
  [[deliver_out_1]] which relies upon the auxiliary functions {@link [[tcp_output_required]]} and
  {@link [[tcp_output_really]]}.  Output (strictly, adding segments to the host's output queue) may take
  place whenever this rule can fire; it does construct the output segments purely from the socket state.



% This specification
% allows a little more non-determinism than any given implementation: common case TCP output may
% take place, i.e. rule [[deliver_out_1]] may be applicable, at any time that a socket in the host's
% finite map of sockets is in a compatible state. This was a deliberate design choice that
% simplifies the modelling of existing TCP implementations which may emit segments under different
% conditions. All these may be valid behaviours either with respect to one or more of the TCP RFCs,
% or simply because their behaviour has become widely adopted and accepted. Either way, this rule
% encompasses all the observed behaviour of the implementations and the acceptable behaviour defined
% by the TCP RFCs (SB coughs!).


  The two auxiliary functions are loosely based on BSD's TCP output function, which can be logically
  divided into two halves. The first of these ---to some approximation--- is a guard that prevents
  output from occuring unless it is valid to do so, and the second actually creates a segment and
  passes it to the IP layer for output. This distinction is mirrored in the specification, with [[tcp_output_required]]
  acting as the guard and [[tcp_output_really]] forming the segment ready to be appended to the
  host's output queue. Unfortunately it is not possible to be as clean here as one might hope,
  because under some circumstances [[tcp_output_required]] may have side-effects. It should be noted
  that [[tcp_output_really]] only creates a segment and does not perform any "output" --- the
  act of adding the segment (perhaps unreliably) to the host's output queue is the job of the
  caller.

  The output cases not covered by [[deliver_out_1]] are handled specially and often in a more
  deterministic way. Segments with the SYN flag set are created by the auxiliary functions
  {@link [[make_syn_flgs_data]]} and {@link [[make_syn_ack_flgs_data]]} and are output deterministically in response to
  either user events or segment input. SYN segments are emitted by the rules commonly involved in
  connection establishment, namely [[connect_1]], [[deliver_in_1]], [[deliver_in_2]],
  [[timer_tt_rexmtsyn_1]] and [[timer_tt_rexmt_1]] and are special-cased in this way for clarity
  because connection establishment performs extra work such as option negotiation and state
  initialisation.

  The creation of RST segments is used by the rules that require a reset segment to be
  emitted in response to a user event, e.g.\ a [[close()]] call on a socket with a zero linger time,
  or as a socket's response to receiving some types of invalid segment.

  In a few places, mainly in the specification of certain congestion control methods, some rules use
  {@link [[tcp_output_really]]} or the wrapper functions {@link [[tcp_output_perhaps]]} and
  {@link [[stream_mlift_tcp_output_perhaps_or_fail]]} directly and---more importantly---deterministically. This is
  partly for clarity, perhaps because an RFC states that output "MUST" occur at that point, and
  partly for convenience, possibly because the model would require much extra state (hence adding
  unnecessary complexity) if the output function was not used in-place.

  The [[tcp_output_perhaps]] function almost entirely mimics an implementation's TCP output
  function. It calls [[tcp_output_required]] to check that output can take place, applying any
  side-effects that it returns, and finally creates the segment with [[tcp_output_really]].  See
  {@link [[tcp_output_perhaps]]} and {@link [[stream_mlift_tcp_output_perhaps_or_fail]]} for more
  information.

  Other auxiliary functions are involved in TCP output and are described earlier. Once a
  segment has been constructed it is added to the host's output queue by one of {@link [[enqueue_or_fail]]},
  {@link [[stream_enqueue_or_fail_sock]]}, {@link [[enqueue_and_ignore_fail]]}, {@link [[enqueue_each_and_ignore_fail]]} or
  {@link [[stream_mlift_tcp_output_perhaps_or_fail]]}.  These functions are used by [[deliver_out_1]] and other
  rules in the specification to non-deterministically add a segment to the host's output queue. In
  the common case, a segment is added to the host's output queue successfully. In other cases, the
  auxiliary function {@link [[rollback_tcp_output]]} may assert a segment is unroutable and prevent the
  segment from being added to the queue. Some failures are non-deterministic in order to model "out
  of resource" style errors, although most are deterministic routing failures determined from the
  socket and host states. [[rollback_tcp_output]] has a second task to "undo" several of the
  socket's control block changes upon an error condition. Some of the enqueue functions ignore
  failure, e.g. [[enqueue_and_ignore_fail]], and upon an error they just fail to queue the segment
  and do not update the socket with the "rolled-back" control block returned by
  [[rollback_tcp_output]]. %All of these functions are documented towards the end of this chapter.

:*)


   (!h socks oq oq' sid sock sock' sock''
     fid sf i1 p1 i2 p2 st cb es cantsndmore cantrcvmore
     tcp_sock tcp_sock'
     do_output persist_fun oflgs odata FIN SS s s' MM.

    deliver_out_1 /* rp_tcp, network nonurgent (*: Common case TCP output :*) */
      (h with <| socks := socks |++ [(sid,sock)] ;
                oq := oq |>,
      SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
    -- Lh_tau -->
      (h with <| socks := socks |++ [(sid,sock'')] ;
                oq :=  oq' |>,
      SS |++ [(streamid_of_quad (i1,p1,i2,p2),s')],MM)

   <==

    (*: \textbf{Summary:} output TCP segment if possible.  In some cases update the socket's persist
    timer without performing output. :*)

    (*: The TCP socket is connected :*)
    sid NOTIN FDOM socks /\
    sock = Sock(fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,
                cantrcvmore,TCP_PROTO(tcp_sock)) /\
    tcp_sock = TCP_Sock0(st,cb,NONE) /\

    (*: and either is in a synchronised state with initial [[SYN]] acknowledged\dots :*)
    ( (st IN {ESTABLISHED;CLOSE_WAIT;FIN_WAIT_1;FIN_WAIT_2;CLOSING;
              LAST_ACK;TIME_WAIT}) \/
    (*: \dots{}or is in the [[SYN_SENT]] or [[SYN_RECEIVED]] state and a [[FIN]] needs to be emitted :*)
      (st IN {SYN_SENT; SYN_RECEIVED} /\ cantsndmore)
    ) /\

    (*: A segment will be emitted if [[tcp_output_required]] asserts that a segment can be
        output ([[do_output]]). If [[tcp_output_required]] returns a function to alter the socket's
        persist timer ([[persist_fun]]), then this does not of itself mean that a segment is
        required, however [[deliver_out_1]] should still fire to allow the update to take place. :*)
    (do_output,persist_fun) IN tcp_output_required /\
    (do_output \/ persist_fun <> NONE) /\

    (*: Apply any persist timer side-effect from [[tcp_output_required]] :*)
    let sock0 = option_case sock
                (\ f. sock with <| pr := TCP_PROTO(tcp_sock with cb updated_by f) |>)
                persist_fun in

    (if do_output then (*: output a segment :*)
       (*: Construct the segment to emit, updating the socket's state :*)
       stream_tcp_output_really sock0 (sock',FIN) /\

       sock'.pr = TCP_PROTO(tcp_sock') /\

       (*: Add the segment to the host's output queue, rolling back the socket's control block state if
           an error occurs :*)
       oflgs = <| SYN := F; SYNACK := F; FIN := FIN; RST := F |> /\
       odata = [] /\
       write (i1,p1,i2,p2) (oflgs,odata) s s' /\
       stream_enqueue_or_fail_sock (tcp_sock'.st IN {CLOSED;LISTEN;SYN_SENT}) h.arch h.rttab h.ifds
                             (SOME i1, SOME i2) sock0 sock' sock''

     else (*: Do not output a segment, but ensure things are tidied up :*)
       oq = oq' /\
       sock'' = sock0 /\
       s' = s
    )


   (*:
    @description

    TODO3

    @internal

    States in which we may need to do some output, leaving out the connection-establishment states.

    In BSD, we may need to send a FIN from [[SYN_SENT]]/[[SYN_RECEIVED]] so we need to allow this
    rule to fire.

    We'll have other rules to deal with retransmission of SYN and SYN,ACK segments (which will need
    to deal with option negotiation), and to send RST segments.  This rule handles FIN sending.

    [[LAST_ACK]] is included as we may need to resend our FIN there.  [[TIME_WAIT]] is included because we
    may need to re-ACK a repeated FIN (which we would receive if the other end lost our original
    ACK).

    fid is not constrained, given that we want to allow a socket with no fid to send data; for
    example if a listening socket has connected but the user has not yet called accept() we should
    be able to ACK the data. similarly, a closing socket loses its fid, but should still be able to
    send a FIN!

    when we're sending oob data, we want to force out a segment, even if other tests say this would
    probably be silly.  NB: TODO: force implies the rule should be urgent, but we have no timer,
    so in level 2 do not bother

    TODO: going to need another rule to do whatever tcp\_output does when it does not get round to
    sending a segment.  Maybe just setting the persist timer etc?  (in level 3, need to set cwnd if
    idle whenevr tcp\_output gets called, too....)  Must at least do persist\_fun if do\_output is F.

    WORRY: having this rule fire asynchronously is different from BSD.  In BSD, tcp\_output is
    called in specific places, chiefly when a segment is received or when delack fires, thus giving
    rise to the so-called "[[ACK]] clock".

   :*)

)

/\

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[tcp_timers]] Host LTS: TCP Timers
TODO3
:*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(*:
  @section [[tcp_timers_section]] TCP Timers
TODO3
:*)
   (!h socks sid sock sock' cb cb' cb'' oq oq' shift
     tcp_sock
     oflgs odata SS SS' MM.

   timer_tt_rexmtsyn_1 /* rp_tcp, misc nonurgent (*: SYN retransmit timer expires :*) */
     (h with <| socks := socks |++ [(sid,sock)];
               oq := oq |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++ [(sid,sock')];
               oq := oq' |>,
     SS',MM)

   <==

     sock.pr = TCP_PROTO(tcp_sock) /\
     shift IN UNIV /\
     tcp_sock.st = SYN_SENT /\  (*: this rule is incomplete: [[RexmtSyn]] is possible in other states, since [[deliver_in_2]] may change state without clearing [[tt_rexmt]] :*)

     cb = tcp_sock.cb /\

     ?i1 i2 p1 p2. (sock.is1,sock.is2, sock.ps1, sock.ps2) = (SOME i1,SOME i2,SOME p1,SOME p2) /\
     if shift+1 >= TCP_MAXRXTSHIFT then
         (*: Timer has expired too many times. Drop and close the connection :*)

         (*: since socket state is [[SYN_SENT]], no segments can be output :*)
         tcp_drop_and_close h.arch (SOME ETIMEDOUT) sock (sock',(oflgs,odata)) /\
         ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
         write (i1,p1,i2,p2) (oflgs,odata) s s' /\
         destroy (i1,p1,i2,p2) (S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]) SS'

     else
         (*: Update the control block based upon the number of occasions on which the timer expired :*)

         cb' = cb /\

         ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
         (*: Create the segment to be retransmitted :*)
         (oflgs, odata) IN make_syn_flgs_data /\
         write (i1,p1,i2,p2) (oflgs,odata) s s' /\
         SS' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')] /\
         (*: Attempt to add the new segment to the host's output queue, constraining the final control block state :*)
         stream_enqueue_or_fail F h.arch h.rttab h.ifds (SOME i1, SOME i2) cb' cb'' /\
         sock' = sock with <| pr := TCP_PROTO(tcp_sock with <| cb := cb'' |>) |>


   (*:
    @description

    TODO3

   @internal

   This looks like a pre-monad comment:
        (  TCPv2p892 shows the tcp_drop_and_close function it uses to do this.  If TCPS_HAVERCVDSYN
        (ie st NOTIN {CLOSED;LISTEN;SYN_SENT}) this sends a RST. It then zaps the cb etc.  There
        seems to be some repeated softerror logic - compare p842 149--150 and p893 214--215. )

        ( do not want to repeat the code for tcp_drop_and_close in the various places it'll be used.
        Maybe we really want a goto idiom (ha!), along the lines of (sock',oq') =
        tcp_drop_and_close(...)  and then, maybe want to use the same idiom for the guts of
        deliver_out_3 ?  )


   :*)
   )

/\
   (!h socks sid sock sock' sock'' cb cb' cb'' oq oq' shift
     tcp_sock tcp_sock'
     oflgs odata SS SS' MM.

   timer_tt_rexmt_1 /* rp_tcp, misc nonurgent (*: retransmit timer expires :*) */
     (h with <| socks := socks |++
                        [(sid,sock)] ;
               oq := oq |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock'')] ;
               oq := oq' |>,
     SS',MM)

   <==

     sock.pr = TCP_PROTO(tcp_sock) /\
     sock'.pr = TCP_PROTO(tcp_sock') /\
     (tcp_sock.st NOTIN {CLOSED; LISTEN; SYN_SENT; CLOSE_WAIT; FIN_WAIT_2; TIME_WAIT} \/
         (tcp_sock.st = LISTEN /\ bsd_arch h.arch)) /\  (* assertion; makes intended dynamic restriction a static one *)

     shift IN UNIV /\

     cb = tcp_sock.cb /\

     (if
         shift+1 > (if tcp_sock.st = SYN_RECEIVED then
           TCP_SYNACKMAXRXTSHIFT else TCP_MAXRXTSHIFT)
     then
         (*: Note that BSD's syncaches have a much lower threshold for retransmitting SYN,ACKs than normal :*)
         (*: drop connection :*)

         (* TCPv2p892 shows the tcp_drop_and_close function it uses to do this.  If TCPS_HAVERCVDSYN (ie st        NOTIN {CLOSED;LISTEN;SYN_SENT}) this sends a RST. It then zaps the cb etc.  There seems to        be some repeated softerror logic - compare p842 149--150 and p893 214--215. *)
         tcp_drop_and_close h.arch (SOME ETIMEDOUT) sock (sock',(oflgs,odata)) /\ (*: will always get exactly one segment :*)
         if exists_quad_of sock then
             let (i1,p1,i2,p2) = quad_of sock in
             ? S0 s s'.  SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
             write (i1,p1,i2,p2) (oflgs,odata) s s' /\
             case tcp_sock.st = LISTEN of
                 T -> SS' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')] (* don't destroy stream *)
                 || F -> destroy (i1,p1,i2,p2) (S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]) SS'
         else
             SS' = SS

     else

        (*: backoff the timer and do a retransmit :*)
        cb' = cb /\

        (if tcp_sock.st = SYN_RECEIVED then
            (?i1 i2 p1 p2.
                (* note apparent asymmetry here - does make_syn_ack_segment have all the required behaviour? *)
                (*: If we're Linux doing a simultaneous open and support timestamping then ensure
                    timestamping is enabled in any retransmitted SYN,ACK segments. See [[deliver_in_2]]
                    for the rationale in full, but in short Linux is RFC1323 compliant and makes
                    a hash of option negotiation during a simultaneous open. We make the option decision
                    early (as per the RFC and BSD) and have to hack up SYN,ACK segments to contain
                    timestamp options if the Linux host supports timestamping.  :*)
                (*: Note: this behaviour is also safe if we are here due to a passive open. In this
                    case, if the remote end does not support timestamping, [[tf_req_tstmp]] is [[F]] due to
                    the option negotiation in [[deliver_in_1]]. Then [[tf_doing_tstmp]] is necessarily [[F]] too
                    and the retransmitted SYN,ACK segment does not contain a timestamp. OTOH, if
                    [[tf_req_tstmp]] is still [[T]] then so is [[tf_doing_tstmp]] and the faked up [[cb]] below is safe. :*)
                (*: Note that similar to the above note on timestamping, window scaling may also have to be dealt with here. :*)
                let cb''' = cb' in

                (*: Note that [[tt_delack]] and possibly other timers should be cleared here :*)
                (sock.is1,sock.is2, sock.ps1, sock.ps2) = (SOME i1,SOME i2,SOME p1,SOME p2) /\

                (*: We are in [[SYN_RECEIVED]] and want to retransmit the SYN,ACK, so we either got here
                    via [[deliver_in_1]] or [[deliver_in_2]]. In both cases, [[calculate_buf_sizes]] was used to
                    set [[cb.t_maxseg]] to the correct value (as per |tcp_mss()| in BSD), however, we need
                    to use the old values in retransmitting the SYN,ACK, as per |tcp_mssopt()| in BSD.
                    [[make_syn_ack_segment]] therefore uses the value stored in [[cb.t_advmss]] to set the
                    same mss option in the segment, so we do not need to do anything special here. :*)
                oflgs = <| SYN := F; SYNACK := T; FIN := F; RST := F |> /\
                odata = [] /\
                ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
                write (i1,p1,i2,p2) (oflgs,odata) s s' /\
                SS' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')] /\

                (*: We need to remember to add the length of the segment data (i.e. 1 for a SYN) back onto
                    [[snd_nxt]] in the [[cb]], since this is what [[tcp_output_really]] does for normal retransmits. If
                    we do not do this, then we'll end up trying to send the first lot of data with a [[seq]] of
                    [[iss]], rather than [[iss + 1]] :*)
                sock' = sock with <| pr := TCP_PROTO(tcp_sock with <| cb := cb' |>) |>
            )
        else if tcp_sock.st = LISTEN then  (*: BSD LISTEN bug:
                    in BSD it is possible to transition a socket to the LISTEN state without
                    cancelling the rexmt timer.  In this case, segments are emitted with
                    no flags set. :*)
                bsd_arch h.arch /\
                (?i1 i2 p1 p2.
                    (sock.is1,sock.is2, sock.ps1, sock.ps2) = (SOME i1,SOME i2,SOME p1,SOME p2) /\
                    sock.cantsndmore ==> oflgs.FIN /\
                    oflgs = oflgs with <| SYN := F; SYNACK := F; RST := F |> /\
                    odata = [] /\
                    ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
                    write (i1,p1,i2,p2) (oflgs,odata) s s' /\
                    SS' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')] /\
                    (*: Retransmission only continues if [[FIN]] is set in the outgoing segment (really!) :*)
                    sock' = sock with <| pr := TCP_PROTO(tcp_sock
                            with <| cb := cb' |> ) |>)
            else (*:  [[ESTABLISHED, FIN_WAIT_1, CLOSING, LAST_ACK]] :*)
                (*: i.e., cannot be [[CLOSED, LISTEN, SYN_SENT, CLOSE_WAIT, FIN_WAIT_2, TIME_WAIT]] :*)
                stream_tcp_output_really
                (sock with <| pr := TCP_PROTO(tcp_sock with <| cb := cb' |>) |> )
                (sock',oflgs.FIN)  (*: always emits exactly one segment :*) /\
                oflgs = oflgs with <| SYN := F; SYNACK := F; RST := F |> /\
                odata = [] /\
                let (i1,p1,i2,p2) = quad_of sock in
                ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
                write (i1,p1,i2,p2) (oflgs,odata) s s' /\
                SS' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]
        )

     ) /\

     stream_enqueue_or_fail T h.arch h.rttab h.ifds (sock'.is1,sock'.is2) tcp_sock'.cb cb'' /\
     sock'' = sock' with <| pr := TCP_PROTO(tcp_sock' with <| cb := cb'' |>) |>


   (*:
    @description

    TODO3

   @internal

        ( note that this makes t_rxtshift a count of the number of times tt_rexmt has expired, not a
        count of the number of retransmissions of the segment.  In the current Level 2, the two can
        differ...

        Another possible Level 2 approach would be to remove t_rxtshift and instead have a timer to drop the
        connection after a while.)

        ( TCPv2p842 calls in_losing if cb.t_rxtshift + 1 > TCP_MAXRXTSHIFT / 4, releasing any cached
        route. We cannot see this in our model, though when we've added per-host routing tables we might want to
        add route caches also; then we could. )


    This looks like a very old comment:

    ( see comment in tcp_output_def above: should force output? )

    ( P: considered folding this into deliver_out_1, as it's not clear why this and the persist timer
    should have different idioms (this a rule and a semaphore; that built into deliver_out_1) and I
    do not like having too many semaphores around. Then changed my mind, as this (and the estimator logic
    that'll be here in Level 3) really seems conceptually different from the out_1 stuff. Hmm. )


   :*)
   )

/\
   (!h socks sid sock sock' sock'' oq oq' tcp_sock tcp_sock'
    i1 i2 oflgs odata
    p1 p2 SS s s' MM.

   timer_tt_persist_1 /* rp_tcp, misc nonurgent (*: persist timer expires :*) */
     (h with <| socks := socks |++
                        [(sid,sock)];
               oq := oq |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock'')];
               oq := oq' |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s')],MM)

   <==

     sock.pr = TCP_PROTO(tcp_sock) /\
     sock'.pr = TCP_PROTO(tcp_sock') /\
     let sock0 = sock in
     stream_tcp_output_really
                       sock0
                       (sock',oflgs.FIN) /\
     oflgs = oflgs with <| SYN := F; SYNACK := F; RST := F |> /\
     odata = [] /\
       (*: guaranteed by [[stream_tcp_output_really]] :*)
       (SOME i1,SOME p1,SOME i2,SOME p2) = (sock.is1,sock.ps1,sock.is2,sock.ps2) /\
       write (i1,p1,i2,p2) (oflgs,odata) s s' /\

     stream_enqueue_or_fail_sock (tcp_sock'.st IN {CLOSED;LISTEN;SYN_SENT}) h.arch h.rttab h.ifds
                          (SOME i1, SOME i2) sock0 sock' sock''


   )

/\
   (!h socks oq oq' d
     sid fid sf i1 p1 i2 p2 st cb es cantsndmore cantrcvmore
     cb'
     SS MM.

   timer_tt_keep_1 /* rp_tcp, network nonurgent (*: keepalive timer expires :*) */
     (h with <| socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                                   TCP_Sock(st,cb,NONE)))] ;
               oq := oq |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,Sock(SOME fid,sf,SOME i1,SOME p1,SOME i2,SOME p2,es,cantsndmore,cantrcvmore,
                                   TCP_Sock(st,cb',NONE)))] ;
               oq := oq' |>,
     SS,MM)

   <==

     (* refer TCPv2p830 *)

     (*: Note that in another rule the following needs to be specified:
        if the timer has expired for the last time, then (in another rule):
         (if HAVERCVDSYN (i.e., not [[CLOSED/LISTEN/SYN_SENT]]) then
              send a RST
          else
              do not do anything yet) [[/\]]
         copy soft error to es [[/\]]
         free tcpcb, saving RTT
     :*)

     cb.tt_keep = SOME (Timed((),d)) /\
     timer_expires d /\

     cb' = cb with <| tt_keep := SOME (Timed((),slow_timer TCPTV_KEEPINTVL))  (* reset to tcp_keepintvl, 75sec *)
                   |>


   )

/\
   (!h socks sid sock sock' tcp_sock
    SS SS' MM.

   timer_tt_2msl_1 /* rp_tcp, misc nonurgent (*: 2*MSL timer expires :*) */
     (h with <| socks := socks |++
                        [(sid,sock)] |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock')] |>,
     SS',MM)

   <==


   (*: \textbf{Summary:}
   When the 2MSL [[TIME_WAIT]] period expires, the socket is closed.
   :*)

   (* A socket may be closed if its quad is set. *)
   if exists_quad_of sock then
     destroy (quad_of sock) SS SS'
   else

     sock.pr = TCP_PROTO(tcp_sock) /\
     sock' = tcp_close h.arch sock /\
     SS' = SS


   )

/\
   (!h socks sid sock sock' sock'' oq oq' tcp_sock tcp_sock'
    oflgs odata SS s s' MM i1 p1 i2 p2.

   timer_tt_delack_1 /* rp_tcp, misc nonurgent (*: delayed-ACK timer expires :*) */
     (h with <| socks := socks |++
                        [(sid,sock)];
               oq := oq |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s)],MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock'')];
               oq := oq' |>,
     SS |++ [(streamid_of_quad (i1,p1,i2,p2),s')],MM)

   <==

     sock.pr = TCP_PROTO(tcp_sock) /\
     sock'.pr = TCP_PROTO(tcp_sock') /\
     let sock0 = sock in
     stream_tcp_output_really sock0 (sock',oflgs.FIN) /\
     oflgs = oflgs with <| SYN := F; SYNACK := F; RST := F |> /\
     odata = [] /\
     (SOME i1, SOME p1, SOME i2, SOME p2) = (sock0.is1,sock0.ps1,sock0.is2,sock0.ps2) /\
     write (i1,p1,i2,p2) (oflgs,odata) s s' /\
     stream_enqueue_or_fail_sock (tcp_sock'.st IN {CLOSED;LISTEN;SYN_SENT}) h.arch h.rttab h.ifds
                          (sock0.is1,sock0.is2) sock0 sock' sock''


   (*:
   @description

   This overlaps with [[deliver_out_1]].  This is a bit odd, but is a consequence of our liberal nondeterministic TCP output.

   @internal
   - our segment emission is enabled
   always, whereas the BSD implementation tries to emit segments only at specific times, mainly when
   a segment is received and when delack fires.

   In level 4, we should do this too: either in those places that do not do their own output already,
   [[tcp_output]] should be called, or a semaphore should be set to trigger [[deliver_out_1]], which
   would then not always be enabled.
   :*)
   )

/\
   (!h socks sid sock oq oq' sock' tcp_sock
    oflgs odata SS SS' MM.

   timer_tt_conn_est_1 /* rp_tcp, misc nonurgent (*: connection establishment timer expires :*) */
     (h with <| socks := socks |++
                        [(sid,sock)];
               oq := oq |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock')];
               oq := oq' |>,
     SS',MM)

   <==

   (*:
   \textbf{Summary:}
   If the connection-establishment timer goes off, drop the connection
   (possibly [[RST]]ing the other end). :*)

     sock.pr = TCP_PROTO(tcp_sock) /\
     tcp_drop_and_close h.arch (SOME ETIMEDOUT) sock (sock',(oflgs,odata)) /\
     (*: Note it should be the case that the socket is in [[SYN_SENT]], and so [[outsegs]] will be empty, but that is not definite. :*)

     (*: write to stream if possible :*)
     if exists_quad_of sock then
       let (i1,p1,i2,p2) = quad_of sock in
       ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
       write (i1,p1,i2,p2) (oflgs,odata) s s' /\
       SS' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]
     else
       SS' = SS


   (*: @description
   POSIX: says, in the \emph{INFORMATIVE} section \emph{APPLICATION USAGE},
   that the state of the socket is unspecified if |connect()| fails.
   We could (in the POSIX "architecture") model this accurately.

   :*)
   )

/\
   (!h socks sid sock sock' tcp_sock
    SS SS' MM.

   timer_tt_fin_wait_2_1 /* rp_tcp, misc nonurgent (*: [[FIN_WAIT_2]] timer expires :*) */
     (h with <| socks := socks |++
                        [(sid,sock)] |>,
     SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock')] |>,
     SS',MM)

   <==

     sock.pr = TCP_PROTO(tcp_sock) /\
     sock' = tcp_close h.arch sock /\

   (* A socket may be closed if its quad is set. *)
   if exists_quad_of sock then
     destroy (quad_of sock) SS SS'
   else
     SS' = SS


   (*:
   @description
   This stops the timer and closes the socket.

   Unlike BSD, we take steps to ensure that this timer only fires when it is really time to close
   the socket.  Specifically, we reset it every time we receive a segment while in [[FIN_WAIT_2]],
   to [[TCPTV_MAXIDLE]].  This means we do not need any guarding conditions here; we just do it.

   This means that we do not directly model the BSD behaviour of "sleep for 10 minutes, then check
   every 75 seconds to see if the connection has been idle for 10 minutes".

   :*)
   )

/\

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[udp_input_processing]] Host LTS: UDP Input Processing
TODO3
 :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)


(*: @section [[udp_input_processing_section]] UDP Input Processing
TODO3
 :*)

   (!h iq socks sid sock rcvq iq' rcvq'
     data i3 ps3 i4 ps4 h0
     SS MM.

    deliver_in_udp_1 /* rp_udp, network nonurgent (*: Get UDP datagram from host's in-queue and deliver it to a matching socket :*) */
      (h0,SS,MM)
    -- Lh_tau -->
      (h0 with <| iq := iq';
                 socks := socks |++
                          [(sid,sock with pr := UDP_Sock(rcvq'))] |>,
      SS,MM)

    <==

      h0 = h with <| iq := iq;
                     socks := socks |++
                              [(sid,sock with pr := UDP_Sock(rcvq))] |> /\
      rcvq' = APPEND rcvq [Dgram_msg(<| data := data; is := SOME i3; ps := ps3 |>)] /\
      dequeue_iq(iq,iq',SOME (UDP(<| is1 := SOME i3; is2 := SOME i4; ps1 := ps3; ps2 := ps4; data := data |>))) /\
      (? (ifid,ifd) :: (h0.ifds). i4 IN ifd.ipset ) /\
      sid IN lookup_udp h0.socks (i3,ps3,i4,ps4) h0.bound h0.arch /\
      T /\  (*: placeholder for  "not a link-layer multicast or broadcast" :*)
      ~(is_broadormulticast h0.ifds i4) /\  (*: seems unlikely, since [[i1 IN local_ips h.ifds]] :*)
      ~(is_broadormulticast h0.ifds i3)


    (*:

     @description

     At the head of the host's in-queue is a UDP datagram with source address [[(SOME i3,ps3)]],
     destination address [[(SOME i4,ps4)]], and data [[data]]. The destination IP address, [[i4]],
     is an IP address for one of the host's interfaces and is not an IP- or link-layer broadcast or
     multicast address and neither is the source IP address, [[i3]].

     The UDP socket [[sid]] matches the address quad of the datagram (see {@link [[lookup_udp]]} for
     details). A [[Lh_tau]] transition is made. The datagram is removed from the host's in-queue,
     [[iq]], and appended to the tail of the socket's receive queue, [[rcvq']], leaving the host
     with in-queue [[iq']] and the socket with receive queue [[rcvq']].

    :*)


    )

/\

   (!h iq iq' oq' i3 i4 ps3 ps4 data icmp icmp_to_go
     SS MM.

    deliver_in_udp_2 /* rp_udp, network nonurgent (*: Get UDP datagram from host's in-queue but generate ICMP, as no matching socket :*) */
      (h with iq := iq,SS,MM)
    -- Lh_tau -->
      (h with <| iq := iq'; oq := if icmp_to_go then oq' else h.oq |>,SS,MM)

    <==

      dequeue_iq(iq,iq',SOME (UDP(<| is1 := SOME i3; is2 := SOME i4; ps1 := ps3;
                                     ps2 := ps4; data := data |>))) /\
      lookup_udp h.socks (i3,ps3,i4,ps4) h.bound h.arch = EMPTY /\
      icmp = ICMP(<| is1 := SOME i4; is2 := SOME i3; is3 := SOME i3; is4 := SOME i4;
                     ps3 := ps3; ps4 := ps4; proto := PROTO_UDP; seq := NONE;
                     t := ICMP_UNREACH(PORT) |>) /\
      (enqueue_oq(h.oq,icmp,oq',T) \/ icmp_to_go = F) (*: non-deterministic ICMP generation :*) /\
      i4 IN local_ips h.ifds /\
      T /\  (*: placeholder for  "not a link-layer multicast or broadcast" :*)
      ~(is_broadormulticast h.ifds i4) /\  (*: seems unlikely, since [[i1 IN local_ips h.ifds]] :*)
      ~(is_broadormulticast h.ifds i3)


    (*:

     @description

     At the head of the host's in-queue, [[iq]], is a UDP datagram with source address [[(SOME
     i3,ps3)]], destination address [[(SOME i4,ps4)]], and data [[data]]. The destination IP
     address, [[i4]], is an IP address for one of the host's interfaces and is neither a broadcast
     or multicast address; the source IP address, [[i3]], is also not a broadcast or multicast
     address. None of the sockets in the host's finite map of sockets, [[h.socks]], match the
     datagram (see {@link [[lookup_udp]]} for details).

     A [[Lh_tau]] transition is made. The datagram is removed from the host's in-queue, leaving it
     with in-queue [[iq']]. An ICMP Port-unreachable message may be generated and appended to the
     tail of the host's out-queue in response to the datagram.

     @internal

     Note that ICMP generation is unreliable; the Linux kernel has
     per-type-of-ICMP rate-limiting to control denial-of-service attacks.
     We take a nondeterministic approximation.
     Note also that the ICMP is dropped if the outqueue is full
     ([[ok=false]]).
     \mignore{In the real world, there is no socket to charge this to... so who
     says "no room to allocate skb"?}

    :*)

    )

/\

   (!h iq iq' dgram i2 is1
     SS MM.

   deliver_in_udp_3 /* rp_udp, network nonurgent (*: Get UDP datagram from host's in-queue and drop as from a martian address :*) */
     (h with <| iq := iq |>,SS,MM)
   -- Lh_tau -->
     (h with <| iq := iq' |>,SS,MM)

   <==

     dequeue_iq(iq,iq',SOME (UDP dgram)) /\
     dgram.is2 = SOME i2 /\
     is1 = dgram.is1 /\
     i2 IN local_ips(h.ifds) /\
     (F \/                  (* TODO: seg checksum and offset field not sensible *)
      ~(T /\  (* not a link-layer multicast or broadcast *)
        ~(is_broadormulticast h.ifds i2) /\  (*: seems unlikely, since [[i1 IN local_ips h.ifds]] :*)
        ~(is1 = NONE) /\
        ~is_broadormulticast h.ifds (THE is1)
      )
     )


   (*:

    @description

    At the head of the host's in-queue, [[iq]], is a UDP datagram with destination IP address [[SOME
    i2]] which is an IP address for one of the host's interfaces. Either [[i2]] is an IP-layer
    broadcast or multicast address, or the source IP address, [[is1]], is not set or is an IP-layer
    broadcast or multicast address.

    A [[Lh_tau]] transition is made. The datagram is dropped from the host's in-queue, leaving it
    with in-queue [[iq']].

    @internal

    Receive and drop any segment for this host that does not have sensible checksum or offset
    fields, or one that originates from a martian address.  The first part of this condition is a
    placeholder, awaiting the day when we switch to a non-lossy segment representation, hence the
    [[F]].

    :*)

   )

/\

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[icmp_input_processing]] Host LTS: ICMP Input Processing
TODO3
 :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(*: @section [[icmp_input_processing_section]] ICMP Input Processing
TODO3
 :*)


   (!h iq iq' oq oq' socks icmp sid sock sock'
     i3 tcp_sock udp_sock h0
     SS SS' MM.

   deliver_in_icmp_1 /* rp_all, network nonurgent (*: Receive [[ICMP_UNREACH_NET]] etc for known socket :*) */
     (h0,SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock')] ;
               iq := iq';
               oq := oq' |>,
     SS',MM)

   <==

     h0 = h with <| socks := socks |++
                             [(sid,sock)] ;
                    iq := iq;
                    oq := oq |> /\
     dequeue_iq(iq,iq',SOME (ICMP icmp)) /\
     icmp.t IN { ICMP_UNREACH c |
                 c IN {NET; HOST; SRCFAIL; NET_UNKNOWN; HOST_UNKNOWN; ISOLATED;
                       TOSNET; TOSHOST; PREC_VIOLATION; PREC_CUTOFF}} /\
     icmp.is3 = SOME i3 /\
     i3 NOTIN IN_MULTICAST /\
     sid IN lookup_icmp h0.socks icmp h0.arch h0.bound /\
     (case sock.pr of
        TCP_PROTO(tcp_sock) ->
          (?icmp_seq. icmp.seq = SOME icmp_seq /\
          ? snd_una_le_icmp_seq :: {T;F}.
          ? icmp_seq_lt_snd_max :: {T;F}.
          ? cond :: {T;F}.
          (tcp_sock.cb.t_softerror = NONE ==> cond = F) /\
          if snd_una_le_icmp_seq /\ icmp_seq_lt_snd_max then (* tcp_notify() *)
              if tcp_sock.st = ESTABLISHED then
                  sock' = sock /\  (*: ignore transient error while connected :*)
                  oq' = oq /\
                  SS' = SS
              else if tcp_sock.st IN {CLOSED;LISTEN;SYN_SENT;SYN_RECEIVED} /\
                      cond then
                  ? oflgs odata. tcp_drop_and_close h.arch (SOME EHOSTUNREACH) sock (sock',(oflgs,odata)) /\
		  if exists_quad_of sock then
                      let (i1,p1,i2,p2) = quad_of sock in
                      ? S0 s s'. S0 = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
                      write (i1,p1,i2,p2) (oflgs,odata) s s' /\
                      if tcp_sock.st = CLOSED then
                          SS' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]
                      else
                          destroy (i1,p1,i2,p2) (S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]) SS'
                  else
                      SS' = SS
              else
                  sock' = sock with <| pr := TCP_PROTO(tcp_sock with
                                    <| cb := tcp_sock.cb with
                                    <| t_softerror := SOME EHOSTUNREACH |> |>) |> /\
                  oq' = oq /\
                  SS' = SS
          else
                (*: Note the case where it is a syncache entry is not dealt with here: a |syncache_unreach()| should be done instead :*)
              sock' = sock /\
              oq' = oq /\
              SS' = SS ) ||
        UDP_PROTO(udp_sock) ->
           if windows_arch h.arch then
               sock' = sock with <| pr := UDP_PROTO(udp_sock with
                                 <| rcvq := APPEND udp_sock.rcvq [(Dgram_error(<| e := ECONNRESET |>))] |>) |> /\ oq' = oq
           else
               sock' = sock with <| es updated_by SOME ECONNREFUSED
                                       onlywhen ((sock.is2 <> NONE) \/ ~(SO_BSDCOMPAT IN sock.sf.b)) |> /\ oq' = oq)



   (*: @description
   Corresponds to FreeBSD 4.6-RELEASE's PRC\_UNREACH\_NET.
   :*)
   )

/\

   (!h iq iq' oq oq' socks icmp sid sock sock'
     tcp_sock icmpmtu udp_sock h0
     SS SS' MM.










   deliver_in_icmp_2 /* rp_all, network nonurgent (*: Receive [[ICMP_UNREACH_NEEDFRAG]] for known socket :*) */
     (h0,SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock')] ;
               iq := iq';
               oq := oq' |>,
     SS',MM)

   <==

     h0 = h with <| socks := socks |++
                             [(sid,sock)] ;
                    iq := iq;
                    oq := oq |> /\
     dequeue_iq(iq,iq',SOME (ICMP icmp)) /\
     icmp.t = ICMP_UNREACH (NEEDFRAG icmpmtu) /\
     (icmp.is3 = NONE \/ THE icmp.is3 NOTIN IN_MULTICAST) /\
     sid IN lookup_icmp h0.socks icmp h0.arch h0.bound /\
     let nextmtu = if F /\ (*: Note this is a placeholder for "there is a host (not net) route for icmp.is4" :*)
                      F then (*: Note this is a placeholder for "|rmx.mtu| not locked" :*)
                       let curmtu = 1492 in (*: Note this value should be taken from |rmx.mtu| :*)
                       let nextmtu = case icmpmtu of
                                        SOME mtu -> w2n mtu
                                     || NONE     -> next_smaller (mtu_tab h0.arch) curmtu in
                       if nextmtu < 296 then
                           (*: Note this should lock curmtu in rmxcache; and not change rmxcache MTU from curmtu :*)
                           SOME curmtu
                       else
                           (*: Note here, [[nextmtu]] should be stored in rmxcache :*)
                           SOME nextmtu
                   else
                       NONE in
     (case sock.pr of
          TCP_PROTO(tcp_sock) ->
            (?icmp_seq. icmp.seq = SOME icmp_seq /\
            if IS_SOME icmp.is3 then
               ? cond :: {T;F}.
               (if cond then (* tcp_mtudisc() *)
                   if nextmtu = NONE then
                       sock' = sock /\
                       oq' = oq /\
                       SS' = SS
                   else
                       ? tf_doing_tstmp :: {T;F}.
                       let mss = MIN (sock.sf.n(SO_SNDBUF))
                           (rounddown MCLBYTES
                            (THE nextmtu - 40 - (if tf_doing_tstmp then 12 else 0))) in
                            (*: BSD: TS, plus NOOP for alignment :*)
                           ? cond' :: {T;F}.
                           if cond' then
                               let sock'' = sock in
                                   ?sock''' FINs tcp_sock'''.
                                   sock'''.pr = TCP_PROTO(tcp_sock''') /\
                                   stream_tcp_output_perhaps sock'' (sock''',FINs) /\
                                   stream_enqueue_or_fail_sock (tcp_sock'''.st NOTIN {CLOSED;LISTEN;SYN_SENT})
                                   h.arch h.rttab h.ifds (sock.is1,sock.is2)
                                   sock'' sock''' sock' /\
                                   case FINs of NONE -> SS' = SS
                                             || SOME FIN ->
                                       let oflgs = <| SYN := F; SYNACK := F; FIN := FIN; RST := F |> in
                                       let (i1,p1,i2,p2) = quad_of sock in
                                       ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
                                       write (i1,p1,i2,p2) (oflgs,[]) s s' /\
                                       SS' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]
                           else
                               sock' = sock /\ oq' = oq /\ SS' = SS
               else
                (*: Note the case where it is a syncache entry is not dealt with here: a |syncache_unreach()| should be done instead :*)
                   sock' = sock /\ oq' = oq /\ SS' = SS)
            else
                sock' = sock /\ oq' = oq /\ SS' = SS) ||
          UDP_PROTO(udp_sock) ->
          if windows_arch h.arch then
              sock' = sock with <| pr := UDP_PROTO(udp_sock with
                                <| rcvq := APPEND udp_sock.rcvq [(Dgram_error(<| e := EMSGSIZE |>))] |>) |> /\ oq' = oq
          else
              sock' = sock with <| es := SOME EMSGSIZE |> /\ oq' = oq)


   (*: @description
   Corresponds to FreeBSD 4.6-RELEASE's PRC\_MSGSIZE.
   :*)

   )

/\

   (!h iq iq' oq oq' socks icmp sid sock sock'
     tcp_sock i3 udp_sock h0
     SS SS' MM.










   deliver_in_icmp_3 /* rp_all, network nonurgent (*: Receive [[ICMP_UNREACH_PORT]] etc for known socket :*) */
     (h0,SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock')] ;
               iq := iq';
               oq := oq' |>,
     SS',MM)

   <==

     h0 = h with <| socks := socks |++
                             [(sid,sock)] ;
                    iq := iq;
                    oq := oq |> /\
     dequeue_iq(iq,iq',SOME (ICMP icmp)) /\
     icmp.t IN { ICMP_UNREACH c |
                 c IN {PROTOCOL; PORT; NET_PROHIB; HOST_PROHIB; FILTER_PROHIB}} /\
     icmp.is3 = SOME i3 /\
     i3 NOTIN IN_MULTICAST /\
     sid IN lookup_icmp h0.socks icmp h0.arch h0.bound /\
     (case sock.pr of
          TCP_PROTO(tcp_sock) ->
            (?icmp_seq. icmp.seq = SOME icmp_seq /\
            ? cond :: {T;F}.
            if cond then (* tcp_drop_syn_sent() *)
                if tcp_sock.st = SYN_SENT then
                    ? oflgsodata.
                    (*: know from definition of [[tcp_drop_and_close]] that no segs will be emitted :*)
                    tcp_drop_and_close h.arch (SOME ECONNREFUSED) sock (sock',oflgsodata) /\
                    null_flgs_data oflgsodata /\
                    if exists_quad_of sock then
                      destroy (quad_of sock) SS SS'
                    else
                      SS' = SS
                else
                    sock' = sock /\ oq' = oq /\ SS' = SS
            else
                (*: Note the case where it is a syncache entry is not dealt with here: a |syncache_unreach()| should be done instead :*)
                sock' = sock /\ oq' = oq /\ SS' = SS ) ||
          UDP_PROTO(udp_sock) ->
              (if windows_arch h.arch then
                   sock' = sock with <| pr := UDP_PROTO(udp_sock with
                                     <| rcvq := APPEND udp_sock.rcvq [(Dgram_error(<| e := ECONNRESET |>))] |>) |> /\
                   oq' = oq
               else (* bsd_arch \/ linux_arch *)
                   sock' = sock with <| es updated_by SOME (ECONNREFUSED)
                                           onlywhen ((sock.is2 <> NONE) \/ ~(SO_BSDCOMPAT IN sock.sf.b)) |> /\ oq' = oq))





   (*: @description
   Corresponds to FreeBSD 4.6-RELEASE's PRC\_UNREACH\_PORT and PRC\_UNREACH\_ADMIN\_PROHIB.
   :*)
   )

/\
   (!h iq iq' oq oq' socks icmp sid sock sock'
     i3 tcp_sock udp_sock h0
     SS SS' MM.










   deliver_in_icmp_4 /* rp_all, network nonurgent (*: Receive [[ICMP_PARAMPROB]] etc for known socket :*) */
     (h0,SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock')] ;
               iq := iq';
               oq := oq' |>,
     SS',MM)

   <==

     h0 = h with <| socks := socks |++
                             [(sid,sock)] ;
                    iq := iq;
                    oq := oq |> /\
     dequeue_iq(iq,iq',SOME (ICMP icmp)) /\
     icmp.t IN { ICMP_PARAMPROB c |
                 c IN {BADHDR; NEEDOPT}} /\
     icmp.is3 = SOME i3 /\
     i3 NOTIN IN_MULTICAST /\
     sid IN lookup_icmp h0.socks icmp h0.arch h0.bound /\
     (case sock.pr of
          TCP_PROTO(tcp_sock) ->
            (?icmp_seq. icmp.seq = SOME icmp_seq /\
            ? cond :: {T;F}.
            if cond then (* tcp_notify() *)
                ? cond' :: {T;F}.
                cond' ==> tcp_sock.cb.t_softerror <> NONE /\
                if tcp_sock.st IN {CLOSED;LISTEN;SYN_SENT;SYN_RECEIVED} /\
                   cond' then
                    ? oflgs odata.
                    tcp_drop_and_close h.arch (SOME ENOPROTOOPT) sock (sock',(oflgs,odata)) /\
                    if exists_quad_of sock then
                      let (i1,p1,i2,p2) = quad_of sock in
                      ? S0 s s'. SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s)] /\
                      write (i1,p1,i2,p2) (oflgs,odata) s s' /\
                      if tcp_sock.st = CLOSED then
                          SS' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]
                      else
                          destroy (i1,p1,i2,p2) (S0 |++ [(streamid_of_quad (i1,p1,i2,p2),s')]) SS'
                    else
                      SS' = SS
                else
                    (* K guesses this delay till after 3 retransmits interacts with the timer_tt_rexmtsyn_1
                     behaviour that after 3 retransmits, timestamping (and CC) is turned off (??) *)
                    sock' = sock with <| pr := TCP_PROTO(tcp_sock with
                                      <| cb := tcp_sock.cb with <| t_softerror := SOME ENOPROTOOPT |> |>) |> /\
                    oq' = oq /\
                    SS' = SS
            else
                (* TODO: if it would be a syncache entry, should do syncache_unreach() instead *)
                sock' = sock /\ oq' = oq /\ SS' = SS) ||
          UDP_PROTO(udp_sock) ->
              (if windows_arch h.arch then
                   sock' = sock with <| pr := UDP_PROTO(udp_sock with
                                     <| rcvq := APPEND udp_sock.rcvq
                                      [(Dgram_error(<| e := ENOPROTOOPT |>))] |>) |> /\
                   oq' = oq
               else (* bsd_arch \/ linux_arch *)
                   sock' = sock with <| es := SOME (ENOPROTOOPT) |> /\ oq' = oq))




   (*: @description
   Corresponds to FreeBSD 4.6-RELEASE's PRC\_PARAMPROB.
   :*)
   )

/\
   (!h iq iq' socks icmp sid sock sock'
     i3 tcp_sock udp_sock h0
     SS MM.










   deliver_in_icmp_5 /* rp_all, network nonurgent (*: Receive [[ICMP_SOURCE_QUENCH]] for known socket :*) */
     (h0,SS,MM)
   -- Lh_tau -->
     (h with <| socks := socks |++
                        [(sid,sock')] ;
               iq := iq' |>,
     SS,MM)

   <==

     h0 = h with <| socks := socks |++
                             [(sid,sock)] ;
                    iq := iq |> /\
     dequeue_iq(iq,iq',SOME (ICMP icmp)) /\
     icmp.t = ICMP_SOURCE_QUENCH QUENCH /\
     icmp.is3 = SOME i3 /\
     i3 NOTIN IN_MULTICAST /\
     sid IN lookup_icmp h0.socks icmp h0.arch h0.bound /\
     (case sock.pr of
          TCP_PROTO(tcp_sock) ->
            (?icmp_seq. icmp.seq = SOME icmp_seq /\
            ? cond :: {T;F}.
            if cond then (* tcp_quench() *)
                sock' = sock
            (*: Note the state of the TCP socket should be checked here. :*)
            (*: Note it might be necessary to make an allowance for local/remote connection? :*)
            else
                (*: Note the case where it is a syncache entry is not dealt with here: a |syncache_unreach()| should be done instead :*)
                sock' = sock ) ||
          UDP_PROTO(udp_sock) ->
              (if windows_arch h.arch then
                   sock' = sock with <| pr := UDP_PROTO(udp_sock with
                                     <| rcvq := APPEND udp_sock.rcvq [(Dgram_error(<| e := EHOSTUNREACH |>))] |>) |>
               else (* bsd_arch \/ linux_arch *)
                   sock' = sock with <| es := SOME (EHOSTUNREACH) |>))



   (*: @description
   Corresponds to FreeBSD 4.6-RELEASE's PRC\_QUENCH.
   :*)
   )

/\
   (!h iq iq' icmp
     SS MM.










   deliver_in_icmp_6 /* rp_all, network nonurgent (*: Receive and ignore other ICMP :*) */
     (h with <| iq := iq |>,SS,MM)
   -- Lh_tau -->
     (h with <| iq := iq' |>,SS,MM)

   <==

     dequeue_iq(iq,iq',SOME (ICMP icmp)) /\
     (icmp.t IN { ICMP_TIME_EXCEEDED INTRANS; ICMP_TIME_EXCEEDED REASS } \/
      icmp.t IN { ICMP_UNREACH       (OTHER x) | x IN UNIV } \/
      icmp.t IN { ICMP_SOURCE_QUENCH (OTHER x) | x IN UNIV } \/
      icmp.t IN { ICMP_TIME_EXCEEDED (OTHER x) | x IN UNIV } \/
      icmp.t IN { ICMP_PARAMPROB     (OTHER x) | x IN UNIV })



   (*: @description
   If ICMP\_TIME\_EXCEEDED (either INTRANS or REASS), or if a bad code is received, then ignore
   silently.
   :*)
   )

/\
   (!h iq iq' icmp
     SS MM.

   deliver_in_icmp_7 /* rp_all, network nonurgent (*: Receive and ignore invalid or unmatched ICMP :*) */
     (h with <| iq := iq |>,SS,MM)
   -- Lh_tau -->
     (h with <| iq := iq' |>,SS,MM)

   <==

     dequeue_iq(iq,iq',SOME (ICMP icmp)) /\
     (icmp.t IN { ICMP_UNREACH c | ~?x. c = OTHER x } \/
      icmp.t IN { ICMP_PARAMPROB c | c IN {BADHDR; NEEDOPT} } \/
      icmp.t = ICMP_SOURCE_QUENCH QUENCH) /\
     (if ?icmpmtu. icmp.t = ICMP_UNREACH (NEEDFRAG icmpmtu) then
          ?i3. icmp.is3 = SOME i3 /\ i3 IN IN_MULTICAST
      else
          (icmp.is3 = NONE \/
           THE icmp.is3 IN IN_MULTICAST \/
           ~(?(sid,s) :: (h.socks).
                   s.is1 = icmp.is3 /\ s.is2 = icmp.is4 /\
                   s.ps1 = icmp.ps3 /\ s.ps2 = icmp.ps4 /\
                   proto_of s.pr = icmp.proto)))


   (*: @description
   If the ICMP is a type we handle, but the source IP is [[IP 0 0 0
   0]] or a multicast address, or there's no matching socket, then
   drop silently.  [[ICMP_UNREACH NEEDFRAG]] is handled specially,
   since we do not care if it's [[IP 0 0 0 0]], only if it's multicast.
   :*)
   )

/\

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[network_input_and_output]] Host LTS: Network Input and Output
TODO3
 :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(*: @section [[network_input_and_output_section]] Network Input and Output
TODO3
 :*)

   (!h msg iq iq' queued i1
     lbl SS MM MM'.

   deliver_in_99 /* rp_all, network nonurgent (*: Really receive things :*) */
     (h with <| iq := iq |>,SS,MM)
   -- lbl -->
     (h with <| iq := iq' |>,SS,MM')

   <==

     ( lbl = Lh_tau /\ (* TCP case *)
       MM' = MM /\
       (? q d q' d' tcp_segment.
         iq = Timed(q,d) /\
         iq' = Timed(q,d') /\ (* update timer only *)
         enqueue_iq(iq,TCP tcp_segment,Timed(q',d'),queued)))
     \/
     ( lbl = Lh_recvdatagram msg /\
       MM = BAG_INSERT msg MM' /\
       sane_msg msg /\
       SOME i1 = msg.is2 /\
       i1 IN local_ips(h.ifds) /\
       enqueue_iq(iq,msg,iq',queued))


   (*: @description
     Actually receive a message from the wire into the input queue.
     Note that if it cannot be queued (because the queue is full), it is
     silently dropped.

     We only accept messages that are for this host.  We also assert that any message we receive is
     well-formed (this excludes elements of type [[msg]] that have no physical realisation).

     Note the delay in in-queuing the datagram is not modelled here.

     @internal

     TODO: - don't belive this any more: renumber rules, so [[deliver_in_99]] has a different kind of
     name from [[deliver_in_3]].

     :*)
     )

/\


   (!h msg iq iq' i1
     SS MM.

   deliver_in_99a /* rp_all, network nonurgent (*: Ignore things not for us :*) */
     (h with <| iq := iq |>,SS,BAG_INSERT msg MM)
   -- Lh_recvdatagram msg -->
     (h with <| iq := iq' |>,SS,BAG_INSERT msg MM)

   <==

     SOME i1 = msg.is2 /\
     i1 NOTIN local_ips(h.ifds) /\
     iq = iq'


   (*: @description
     Do not accept messages that are not for this host.

     :*)
     )


/\

   (!h msg oq oq'
     lbl SS MM MM'.

   deliver_out_99 /* rp_all, network nonurgent (*: Really send things :*) */
     (h with <| oq := oq |>,SS,MM)
   -- lbl -->
     (h with <| oq := oq' |>,SS,MM')

   <==

     ( lbl = Lh_tau /\ (* case Spec1 deliver_out_99 with a TCP msg *)
       MM' = MM /\
       (* We would like oq' = oq, but if a TCP msg was dequeued, there can be a side effect on the timer. The following simulates this. *)
       (? q d tcp_segment.
         oq = Timed(q,d) /\
         dequeue_oq(Timed(TCP tcp_segment::q,d),oq',SOME (TCP tcp_segment))))
     \/
     ( lbl = Lh_senddatagram msg /\
       MM' = BAG_INSERT msg MM /\
       dequeue_oq(oq,oq',SOME msg) /\
       (?i2. msg.is2 = SOME i2 /\ i2 NOTIN local_ips h.ifds))


   (*:
     @description
     Actually emit a segment from the output queue.

     Note the delay in dequeuing the datagram is not modelled here.

     :*)
     )

/\
   (!h msg oq oq' iq iq' queued lbl
     SS MM.

   deliver_loop_99 /* rp_all, network nonurgent (*: Loop back a loopback message :*) */
     (h with <| iq := iq;
               oq := oq |>,
     SS,MM)
   -- lbl -->
     (h with <| iq := iq';
               oq := oq' |>,
     SS,MM)

   <==

     ( lbl = Lh_tau /\ (* TCP case *)
       (* oq *)
       (? q d tcp_segment.
         oq = Timed(q,d) /\
         dequeue_oq(Timed(TCP tcp_segment::q,d),oq',SOME (TCP tcp_segment))) /\
       (* iq *)
       (? q d q' d' tcp_segment.
         iq = Timed(q,d) /\
         iq' = Timed(q,d') /\ (* update timer only *)
         enqueue_iq(iq,TCP tcp_segment,Timed(q',d'),queued)))
     \/
     ( dequeue_oq(oq,oq',SOME msg) /\
       (?i2. msg.is2 = SOME i2 /\ i2 IN local_ips h.ifds) /\
       (lbl = if windows_arch h.arch then Lh_tau
             else Lh_loopdatagram msg) /\
       enqueue_iq(iq,msg,iq',queued))


   (*:
     @description
     Deliver a loopback message (for loopback address, or any of our
     addresses) from the outqueue to the inqueue.  (if we tagged each
     message in the outqueue with its interface, we'd just pick
     loopback-interface segments, but we do not, so we just discriminate
     on IP addresses).

     :*)
     )

/\

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[trace_and_interface]] Host LTS:  BSD Trace Records and Interface State Changes
TODO3 :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)


(*: @section [[trace_and_interface_section]] BSD Trace Records and Interface State Changes
TODO3
:*)

   (!h tr flav sid quad st cb
     SS MM.

   trace_1 /* rp_all, misc nonurgent (*: Trace TCPCB state, [[ESTABLISHED]] or later :*) */
     (h,SS,MM)
   -- Lh_trace tr -->
     (h,SS,MM)

   <==

     sid IN FDOM h.socks /\
     tr = (flav,sid,quad,st,cb) /\
     st IN {ESTABLISHED; FIN_WAIT_1; FIN_WAIT_2; CLOSING;
            CLOSE_WAIT; LAST_ACK; TIME_WAIT} /\
     tracesock_eq tr sid (h.socks ' sid)


   (*:
     @description
     This rule exposes certain of the fields of the socket and TCPCB, to
     allow open-box testing.

     Note that although the label carries an entire TCPCB, only certain
     selected fields are constrained to be equal to the actual TCPCB.
     See {@link [[tracesock_eq]]} and {@link [[tracecb_eq]]} for
     details.

     Checking trace equality is problematic as BSD generates trace records that
     fall logically inbetween the atomic transitions in this model. This happens
     frequently when in a state before [[ESTABLISHED]]. We only check for equality
     when we are in [[ ESTABLISHED]] or later states.

     :*)
     )

/\
   (!h tr flav sid quad st cb
     SS MM.

   trace_2 /* rp_all, misc nonurgent (*: Trace TCPCB state, pre-[[ESTABLISHED]] :*) */
     (h,SS,MM)
   -- Lh_trace tr -->
     (h,SS,MM)

   <==

     sid IN FDOM h.socks /\
     tr = (flav,sid,quad,st,cb) /\
     st NOTIN {ESTABLISHED; FIN_WAIT_1; FIN_WAIT_2; CLOSING;
               CLOSE_WAIT; LAST_ACK; TIME_WAIT} /\
     (st = CLOSED \/  (*: BSD emits one of these each time a tcpcb is created, eg at end of 3WHS :*)
      ((?sock tcp_sock.
        sock = (h.socks ' sid) /\
        proto_of sock.pr = PROTO_TCP /\
        tcp_sock = tcp_sock_of sock /\
        (case quad of
          SOME (is1,ps1,is2,ps2) -> if flav = TA_DROP \/ tcp_sock.st = CLOSED then T
				    else
					is1 = sock.is1 /\ ps1 = sock.ps1 /\ is2 = sock.is2 /\ ps2 = sock.ps2 ||
          NONE                   -> T) /\
        (st  = tcp_sock.st \/ tcp_sock.st = CLOSED))))



     )


/\


   (!h ifid up ifds ifds'
     SS MM.

   interface_1 /* rp_all, misc nonurgent (*: Change connectivity :*) */
     (h with <| ifds := ifds |>,SS,MM)
   -- Lh_interface (ifid,up) -->
     (h with <| ifds := ifds' |>,SS,MM)

   <==

     ifid IN FDOM ifds /\
     ifds' = ifds |+ (ifid, (ifds ' ifid) with <| up := up |>)


     (*:
     @description
     Allow interfaces to be externally brought up or taken down.

     :*)
     )

` handle e => Raise e;



(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[time_passage]] Host LTS:  Time Passage
TODO3
 :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)


(* -------------------------------------------------- *)
(*                Time passage function               *)
(* -------------------------------------------------- *)

(* should do reflection on hosts: find everything of type 'a timed, i.e., everything of the form
   Timed(...), and do something to it. *)




(*: @section [[time_passage_auxs_section]] ALL Time Passage auxiliaries

   Time passage is a \emph{function}, completely deterministic.
   Any nondeterminism must occur as a result of a tau
   (or other) transition.

   In the present semantics, time passage merely:
     \begin{enumerate}
     \item decrements all timers uniformly

     \item prevents time passage if a timer reaches zero

     \item prevents time passage if an urgent action is
        enabled.
     \end{enumerate}
   We model the first two points with functions [[Time_Pass_*]], for various types
   [[*]].  These functions return an option type: if the result is NONE then
   time may not pass for the given duration.  Essentially they pick out everything in a host state of type [['a timed]], and do something with it.

   We treat the last point in the network transition rules below.

:*)


val Time_Pass_timedoption_def = Phase.phase 3 Define`
(*: time passes for an [['a timed option]] value :*)
  (Time_Pass_timedoption : duration -> 'a timed option -> 'a timed option option)
     dur x0
   = case x0 of
       NONE   -> SOME NONE ||
       SOME x -> (case Time_Pass_timed dur x of
                    NONE -> NONE ||
                    SOME x0' -> SOME (SOME x0'))
`;

val Time_Pass_tcpcb_def = Define`
(*: time passes for a tcp control block :*)
  (Time_Pass_tcpcb : duration -> tcpcb -> tcpcb set option)  (* recall: 'a set == 'a -> bool *)
     dur cb
   = let tt_keep'      = Time_Pass_timedoption dur cb.tt_keep
     in
     if IS_SOME tt_keep'
     then
        SOME (\cb'.
              cb' =
              cb with <| (* not going to list everything here; too much! *)
                         tt_keep       := THE tt_keep'
                      |>)
     else
        NONE
`;

val Time_Pass_socket_def = Define`
(*: time passes for a socket :*)
  (Time_Pass_socket : duration -> socket -> socket set option)
     dur s
   = case s.pr of UDP_PROTO(udp) -> SOME { s }
     || TCP_PROTO(tcp_s) ->
       let cb's = Time_Pass_tcpcb dur tcp_s.cb
       in
       if IS_SOME cb's
       then
          SOME (\s'.
                choose cb' :: THE cb's.
                s' =
                s with <| (* fid unchanged *)
                          (* sf unchanged *)
                          (* is1,ps1,is2,ps2 unchanged *)
                          (* es unchanged *)
                          pr := TCP_PROTO(tcp_s with <| cb := cb' |>)
                       |>)
       else
          NONE
`;

val fmap_every_def = Phase.phase 3 Define`
(*: apply [[f]] to range of finite map, and succeed if each application succeeds :*)
 (fmap_every : ('a -> 'b option) -> ('c |-> 'a) -> ('c |-> 'b) option)
             f fm =
    let fm' = f o_f fm
    in
    if NONE IN FRANGE fm'
    then NONE
    else SOME (THE o_f fm')
`;

val fmap_every_pred_def = Define`
(*: apply [[f]] to range of finite map, and succeed if each application succeeds :*)
 (fmap_every_pred : ('a -> 'b set option) -> ('c |-> 'a) -> ('c |-> 'b) set option)
             f fm =
    if ?y. y IN FRANGE fm /\ f y = NONE then
        NONE
    else
        SOME { fm' | FDOM fm = FDOM fm' /\
                     !x. x IN FDOM fm ==> fm' ' x IN (THE (f (fm ' x))) }
`;

val Time_Pass_host_def = Define`
(*: time passes for a host :*)
  (Time_Pass_host : duration -> host -> host set option)
     dur h
   = let ts'     = fmap_every (Time_Pass_timed dur) h.ts
     and socks's = fmap_every_pred (Time_Pass_socket dur) h.socks
     and iq'     = Time_Pass_timed dur h.iq
     and oq'     = Time_Pass_timed dur h.oq
     and ticks's = Time_Pass_ticker dur h.ticks
     in
     if IS_SOME ts' /\
        IS_SOME socks's /\
        IS_SOME iq' /\
        IS_SOME oq'
     then
        SOME (\h'.
              choose socks' :: THE socks's.
              choose ticks' :: ticks's.
              h' =
              h with <| (* arch unchanged *)
                        (* ifds unchanged *)
                        ts := THE ts';
                        (* files unchanged *)
                        socks := socks';
                        (* listen unchanged *)
                        (* bound unchanged *)
                        iq := THE iq';
                        oq := THE oq';
                        ticks := ticks'
                        (* fds unchanged *)
                     |>)
     else
        NONE
`;




(* -------------------------------------------------- *)
(*          Host transition rules with time           *)
(* -------------------------------------------------- *)

(* @section [[time_passage_section]] ALL Host transitions with time

We now build the relation [[-- ( ) --=>]], which includes time transitions, from the relation [[-- ( ) -->]],
which is instantaneous.  This avoids circularity (or at best inductiveness) in the definition of
the transition relation.


*)

(* section removed, replaced by rules in TCP3_net *)

(* -------------------------------------------------- *)

val _ = export_theory();

(* Local Variables: *)
(* fill-column: 100 *)
(* End: *)
