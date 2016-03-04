(* A HOL98 specification of TCP *)

(* Definitions and support for various kinds of timer *)

(*[ RCSID "$Id: TCP1_timersScript.sml,v 1.1 2005/07/12 15:42:25 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse

open BasicProvers bossLib

open HolDoc

local open TCP1_baseTypesTheory TCP1_utilsTheory in end

local open arithmeticTheory realTheory word32Theory in end;

val _ = BasicProvers.augment_srw_ss [rewrites [LET_THM]]

val _ = new_theory "TCP1_timers";

val _ = Version.registerTheory "$RCSfile: TCP1_timersScript.sml,v $" "$Revision: 1.1 $" "$Date: 2005/07/12 15:42:25 $";

(* -------------------------------------------------- *)
(*      TIMERS                                        *)
(* -------------------------------------------------- *)

(*: @chapter [[TCP1_timers]] Timers

This file defines the various kinds of timer that are used by the host
specification.
%
   Timers are host-state components that are updated by the
   passage of time, in [[Lh_epsilon dur]] transitions.
%
   We define four kinds of timer:

\begin{enumerate}
\item the deadline timer ([['a timed]]), which wraps a value in a timer
      that will count towards a (possibly fuzzy) deadline, and stop
      the progress of time when it reaches the maximum deadline.

\item the time-window timer ([['a timewindow]]), which wraps a value in a
      timer just like a deadline timer, except that the value merely
      vanishes when it expires, rather than impeding the progress of
      time.

      These are an optimisation, designed to avoid having an extra
      rule (and consequent [[Lh_tau]] transitions) just for processing the
      expiry of such values.

\item the ticker ([[ticker]]), which contains a [[ts_seq]] (integral
      wraparound 32-bit type) that is incremented by one for every
      time a certain interval passes.  It also contains the real
      remainder, and the interval size that corresponds to a step.

\item the stopwatch ([[stopwatch]]), which may be reset at any time
      and counts upwards indefinitely from zero.  Note it may be
      necessary to add some fuzziness to this timer.

\end{enumerate}

   For each timer we define a constructor and a time-passage function.
   The time-passage function takes a duration (positive real) and a
   timer, and returns either the timer, or [[NONE]] if time is not
   permitted by the timer to pass that far (i.e., an urgent instant
   would be passed).  Timers that never need to stop time do not
   return an option type.  Timers that behave nondeterministically are
   defined relationally (taking the "result" as argument and returning
   a bool).

   For all of them, we want the two properties defined by Lynch and
   Vaandrager in Inf. and Comp., 128(1), 1996
   (http://theory.lcs.mit.edu/tds/papers/Lynch/IC96.html) as S1 and S2
   to hold.

:*)

(* -------------------------------------------------------------------- *)
(*   PROPERTIES                                                         *)
(* -------------------------------------------------------------------- *)

(*: @section [[timers_props]] ALL Properties

Axioms of time, that all timers must satisfy.

:*)

val time_pass_additive_def = Define`
  (time_pass_additive : (duration -> 'a -> 'a -> bool) -> bool)
                      time_pass
     = !dur1 dur2 s0 s1 s2.
         time_pass dur1 s0 s1 /\ time_pass dur2 s1 s2 ==> time_pass (dur1+dur2) s0 s2
`
(*: @description
Property S1, additivity:
%
    If [[s' -- (Lh_epsilon d) --> s'']] and [[s'' -- (Lh_epsilon d') --> s]] then [[s' -- (Lh_epsilon (d+d')) --> s]].
:*)
;

val time_pass_trajectory_def = Define`
  (time_pass_trajectory : (duration -> 'a -> 'a -> bool) -> bool)
                        time_pass
     = !dur s0 s1.
         time_pass dur s0 s1
         ==>
         ?w.
           w 0   = s0 /\
           w dur = s1 /\
           !t t'.
             0 <= t  /\ t <= dur /\
             0 <= t' /\ t' <= dur /\
             t < t'
             ==>
             time_pass (t'-t) (w t) (w t')
`
(*: @description
Property S2 is defined as follows:
    Each time passage step [[s' -- (Lh_epsilon d) --> s]] has a \emph{trajectory},
  where a trajectory is defined as follows.
  If $I$ is any left-closed interval of $\mathbb{R} \geq 0$ beginning with 0, then
  an $I$-trajectory is a function $w$ from $I$ to $\mathrm{states}(A)$ such that
    [[w(t) -- (Lh_epsilon (t'-t)) --> w(t')]] for all $t$,$t'$ in $I$ with $t < t'$.

  Now define $w.\mathrm{fstate} = w(0)$, $w.\mathrm{ltime}$ to be the supremum of $I$, and if
  $I$ is right-closed, $w.\mathrm{lstate} = w(w.\mathrm{ltime})$.  Then a trajectory for a
  step [[s' -- (Lh_epsilon d) --> s]] is a $[0,d]$-trajectory with $w.\mathrm{fstate} = s'$ and
  $w.\mathrm{lstate} = s$.

  In our case, S2 (which we call ``trajectory'') may be stated as follows:
     For each time passage step [[s' -- (Lh_epsilon d) --> s]], there exists a
     function $w$ from $[0,d]$ to states such that $w(0) = s'$, $w(d) = s$,
     and [[w(t) -- (Lh_epsilon (t'-t)) --> w(t')]] for all $t$,$t'$ in $[0,d]$ with $t < t'$.

:*)
;

val opttorel_def = Define`
  (opttorel : (duration -> 'a -> 'a option) -> (duration -> 'a -> 'a -> bool))
            tp dur x y
     = case tp dur x of
           SOME x' -> y = x'
        || NONE    -> F
`(*: @description
Impedance-matching coercion.
:*);


(* -------------------------------------------------------------------- *)
(*   BASIC TIMER : timer                                                *)
(* -------------------------------------------------------------------- *)

(*: @section [[timers_timer]] ALL Basic timer [[timer]]

The basic timer, [[timer]], is a triple of the elapsed time, the
minimum expiry time, and the maximum expiry time.  It may expire at
any time after the minimum expiry time, but time may not progress
beyond the maximum expiry time.

:*)

(* building block for deadline timer and time-window timer *)
val _ = Hol_datatype `timer = Timer of duration # time # time`;  (* elapsed, min, max *)

val fuzzy_timer_def = Phase.phase 1 Define`
  (*: timer that goes off in the interval [[ [d-eps,d+fuz] ]], like a BSD ticks-based timer :*)
  (*: [[fuz]] is some fuzziness added to mask the atomic nature of the model. :*)

  (fuzzy_timer : time -> duration -> duration -> timer)
               d eps fuz = Timer(0,d-eps,d+fuz)
`;
val sharp_timer_def = Phase.phase 1 Define`
(*: timer that goes off at exactly [[d]] after now :*)
  sharp_timer d = fuzzy_timer d 0
` (*: @mergewithnext :*) ;
val never_timer_def = Phase.phase 1 Define`
(*: timer that never goes off :*)
  never_timer = Timer(0,time_infty,time_infty)
` (*: @mergewithnext :*) ;
val upper_timer_def = Phase.phase 1 Define`
(*: timer that goes off between now and [[d]] :*)
  upper_timer d = Timer(0,time_zero,d)
`;

val timer_expires_def = Phase.phase 1 Define`
  (* true if the timer may expire now *)
  (* NB: we assume below that this is monotonic; if it is once true it
     is always true (at least at any time that can be reached *)
  (timer_expires : timer -> bool) (Timer(e,deadmin,deadmax))
  = (time e >= deadmin)
`;
val Time_Pass_timer_def = Phase.phase 3 Define`
(* state of timer after time passage *)
  (Time_Pass_timer : duration -> timer -> timer option)
     dur (Timer(e,deadmin,deadmax))
   = let e' = e + dur
     in
     if time e' <= deadmax
     then SOME (Timer(e',deadmin,deadmax))
     else NONE
`;

val Time_Pass_timer_additive =
  ``time_pass_additive (opttorel Time_Pass_timer)``;
val Time_Pass_timer_trajectory =
  ``time_pass_additive (opttorel Time_Pass_timer)``;


(* -------------------------------------------------------------------- *)
(*   DEADLINE TIMER : 'a timed                                          *)
(* -------------------------------------------------------------------- *)

(*: @section [[timers_timed]] ALL Deadline timer [[timed]]

The deadline timer [['a timed]] is simply a value [['a]] annotated by
a [[timer]].  This is a very convenient idiom.

:*)

(* deadline timer *)
(*[ NEWMODE straighttimed ]*)
(*[ HOL_CURRIED_ALIST
  Timed "" 99 false false
]*)
val _ = Hol_datatype `timed = Timed of 'a # timer`;
(*[ MODE 0 ]*)

val timed_val_of_def = Phase.phase 1 Define`timed_val_of (Timed(x,_)) = x`;
val timed_timer_of_def = Phase.phase 1 Define`timed_timer_of (Timed(x,d)) = d`;
val timed_expires_def = Phase.phase 1 Define`timed_expires (Timed(_,d)) = timer_expires d`;

val Time_Pass_timed_def = Phase.phase 3 Define`
  (Time_Pass_timed : duration -> 'a timed -> 'a timed option)
     dur (Timed(x,d))
   = case Time_Pass_timer dur d of
        SOME d' -> SOME (Timed(x,d'))
     || NONE    -> NONE
`;


val Time_Pass_timed_additive =
  ``time_pass_additive (opttorel Time_Pass_timed)``;
val Time_Pass_timed_trajectory =
  ``time_pass_additive (opttorel Time_Pass_timed)``;


(* -------------------------------------------------------------------- *)
(*   TIME-WINDOW TIMER : 'a timewindow                                  *)
(* -------------------------------------------------------------------- *)

(*: @section [[timers_timewindow]] ALL Time-window timer [[timewindow]]

The time-window timer [['a timewindow]], rendered as [[TimeWindow(x,d)]], is like a deadline timer [['a
timed]], except that when it expires the value merely evaporates,
rather than causing time to stop.  Thus an [['a timewindow]] never
induces urgency.

:*)

(* time-window timer *)
(*[ NEWMODE straighttimewindow ]*)
(*[ HOL_CURRIED_ALIST TimeWindow "" 99 false false
]*)
val _ = Hol_datatype `timewindow = TimeWindow of 'a # timer | TimeWindowClosed`;
(*[ MODE 0 ]*)

val timewindow_val_of_def = Phase.phase 1 Define`
  timewindow_val_of (TimeWindow(x,_)) = SOME x /\
  timewindow_val_of  TimeWindowClosed = NONE
`;

val timewindow_open_def = Phase.phase 1 Define`
  timewindow_open (TimeWindow(_,_)) = T /\
  timewindow_open  TimeWindowClosed = F
`;

val Time_Pass_timewindow_def = Phase.phase 3 Define`
  (Time_Pass_timewindow : duration -> 'a timewindow -> 'a timewindow -> bool)
     dur (TimeWindow(x,d)) tw'
   = (case Time_Pass_timer dur d of
         NONE    -> tw' = TimeWindowClosed
      || SOME d' -> tw' = TimeWindow(x,d') \/
                    (timer_expires d' /\ tw' = TimeWindowClosed)) /\
   Time_Pass_timewindow dur TimeWindowClosed tw' = (tw' = TimeWindowClosed)
`;

val Time_Pass_timewindow_additive =
  ``time_pass_additive Time_Pass_timewindow``;
val Time_Pass_timewindow_trajectory =
  ``time_pass_additive Time_Pass_timewindow``;


(* -------------------------------------------------------------------- *)
(*   TICKER : ticker                                                    *)
(* -------------------------------------------------------------------- *)

(*: @section [[timers_ticker]] ALL Ticker [[ticker]]

A ticker [[ticker]] models a discrete time counter.  It contains a
counter, a remainder, a minimum duration, and a maximum duration.  The
counter is incremented at least once every maximum duration, and at
most once every minimum duration.  The remainder stores the time since
the last increment.

:*)

(* ticker *)
(* Might think it would be more straightforward to simply have a 10ms
   timer and a rule that bumps the tick count whenever it fires; but that
   would yield a tau step every 10milliseconds, which would get rather
   annoying. *)
val _ = Hol_datatype `ticker = Ticker of ts_seq # duration(* may be zero *) # duration # duration`;

val ticks_of_def = Phase.phase 1 Define`ticks_of (Ticker(ticks,_,_,_)) = ticks`;

(* leave this out of any rewriting phases; it can be usefully treated as an
   atomic relation *)
val Time_Pass_ticker_def = Define`
  (Time_Pass_ticker : duration -> ticker -> ticker -> bool)
     dur (Ticker(ticks,remdr,intvlmin,intvlmax)) t'
   = let d = remdr + dur
     in
       ?delta remdr'.
          d - real_of_num delta * intvlmax <= remdr' /\
          remdr' <= d - real_of_num delta * intvlmin /\
          0 <= remdr' /\ remdr' < intvlmax /\
          t' = Ticker(ticks + delta, remdr', intvlmin, intvlmax)
`;

val ticker_ok_def = Phase.phase 1 Define`
  ticker_ok (Ticker(ticks, remdr, imin, imax)) =
    (0 <= remdr /\ remdr < imax /\ imin <= imax /\ 0 < imin)
`;

val tick_imin_def = Define`
  tick_imin(Ticker(t,r,imin, imax)) = imin
`;
val tick_imax_def = Define`
  tick_imax(Ticker(t,r,imin,imax)) = imax
`;

val Time_Pass_ticker_additive =
  ``time_pass_additive Time_Pass_ticker``;
val Time_Pass_ticker_trajectory =
  ``time_pass_trajectory Time_Pass_ticker``;


(* -------------------------------------------------------------------- *)
(*   STOPWATCH : stopwatch                                              *)
(* -------------------------------------------------------------------- *)

(*: @section [[timers_stopwatch]] ALL Stopwatch [[stopwatch]]

The stopwatch [[stopwatch]] records the time since it was started,
with fuzziness introduced by means of a minimum and maximum rate
factor applied to the passage of time.

:*)

val _ = Hol_datatype`
  stopwatch = Stopwatch of duration(* may be zero *) # real # real
`;

val stopwatch_val_of_def = Phase.phase 1 Define`
  stopwatch_val_of (Stopwatch(d,_,_)) = d
`;

val Time_Pass_stopwatch_def = Phase.phase 3 Define`
  (Time_Pass_stopwatch : duration -> stopwatch -> stopwatch -> bool)
    dur (Stopwatch(d,ratemin,ratemax)) s'
   = ?rate. ratemin <= rate /\ rate <= ratemax /\
     s' = Stopwatch(d+(dur*rate),ratemin,ratemax)
`;

val Time_Pass_stopwatch_additive =
  ``time_pass_additive Time_Pass_stopwatch``;
val Time_Pass_stopwatch_trajectory =
  ``time_pass_additive Time_Pass_stopwatch``;


(* -------------------------------------------------- *)

val _ = export_theory();
