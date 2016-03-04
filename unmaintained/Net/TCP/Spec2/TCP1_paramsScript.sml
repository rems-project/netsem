(* A HOL98 specification of TCP *)

(* Host behavioural parameters *)

(*[ RCSID "$Id: TCP1_paramsScript.sml,v 1.2 2005/07/13 12:24:41 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

local open TCP1_baseTypesTheory
           TCP1_utilsTheory
           TCP1_hostTypesTheory
in end;

val Term = Parse.Term;

val _ = new_theory "TCP1_params";

val _ = Version.registerTheory "$RCSfile: TCP1_paramsScript.sml,v $" "$Revision: 1.2 $" "$Date: 2005/07/13 12:24:41 $";

(*: @chapter [[TCP1_params]] Host behavioural parameters

This file defines a large number of constants affecting the behaviour
of the host.  Many of these of are adjustable by sysctls/registry keys on
the target architectures.

:*)


(* TODO: ultimately, these should probably all be host parameters, so
   we can tweak them without rebuilding the wHOLe spec... *)

(* KSW/MN: perhaps try underspecifying some of these constants, using the following: *)

(* new_specification { consts = [{const_name = "SOMAXCONN", fixity = Prefix}],
                       name = "SOMAXCONN_def",
                       sat_thm = |- ?x. x > 64 }
     returns a definition of the form |- SOMAXCONN > 64 *)



(* ------------------------------------------------------------------ *)
(*:
@section [[params_model]] ALL Model parameters

Booleans that select a particular model semantics.

:*)
(* ------------------------------------------------------------------ *)

val INFINITE_RESOURCES_def = Phase.phase 1 Define`
  INFINITE_RESOURCES = T
`(*:
@description

[[INFINITE_RESOURCES]] forbids various resource
failures, e.g.~lack of kernel memory.  These failures are
nondeterministic in the specification (to be more precise the
specification would have to model far more detail about the real
system) and rare in practice, so for testing and resoning one often
wants to exclude them altogether.

:*);

(* X
val BSD_RTTVAR_BUG_def = Phase.phase 1 Define`
  BSD_RTTVAR_BUG = T
`
(*:
@description
 [[BSD_RTTVAR_BUG]] enables a peculiarity of BSD behaviour for retransmit timeouts.
%
     After [[TCP_MAXRXTSHIFT / 4]] retransmit timeouts, [[t_srtt]] and
     [[t_rttvar]] are invalidated, but should still be used to compute
     future retransmit timeouts until better information becomes
     available.  BSD makes a mistake in doing this, thus causing
     future retransmit timeouts to be wrong.

     The code at |tcp_timer.c:420| adds the [[srtt]] value to the [[rttvar]],
     shifted "appropriately", and sets [[srtt]] to zero.  [[srtt==0]] is the
     indication (in BSD) that the [[srtt]] is invalid.  We instead code this
     with a separate boolean, and are thus able to keep using
     both [[srtt]] and [[rttvar]].

     But comparing with |tcp_var.h:281|, where the values are used,
     reveals that the correction is in fact wrong.

     This is not visible in the [[RexmtSyn]] case (where it would be most
     obvious),  because in that case the [[srtt]] never was valid,
     and [[rttvar]] was cunningly hacked up to give the right value (in
     |tcp_subr.c:542| --- and the |tcp_timer.c:420| code has no effect at
     all.
:*)
;
X *)


(* ------------------------------------------------------------------ *)
(*:
@section [[params_sched]] ALL Scheduling parameters

Parameters controlling the timing of the OS scheduler.

:*)
(* ------------------------------------------------------------------ *)

(* maximum host op scheduling delay: *)
val dschedmax_def = Phase.phase 1 Define`dschedmax = time ( 1000/1000) (* make large for now, tighten when better understood *)`(*: @mergewithnext :*);

(* maximum inqueue scheduling delay: *)
val diqmax_def = Phase.phase 1 Define`diqmax = time ( 1000/1000) (* make large for now, tighten when better understood *)`(*: @mergewithnext :*);

(* maximum outqueue emission delay: *)
val doqmax_def = Phase.phase 1 Define`doqmax = time ( 1000/1000) (* make large for now, tighten when better understood *)`
(*:
@description
%
[[dschedmax]] is the maximum scheduling delay between a system call
yielding a return value and that return value being passed to the
process.
%
[[diqmax]] and [[doqmax]] are the maximum scheduling delays between a
message being placed on the queue and being processed (respectively,
emitted).
%
For now, pending investigation of tighter realistic upper bounds, they
are all made conservatively large.

:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[params_timer]] ALL Timers

Parameters controlling the rate and fuzziness of the various timers
used in the model.

:*)
(* ------------------------------------------------------------------ *)


val HZ_def = Phase.phase 1 Define`
  HZ = 100 : real  (* Note this is the FreeBSD value. *)
`
(*:
@description
The nominal rate at which the timestamp (etc.) clock ticks, in hertz (ticks per second).
:*)
;

val tickintvlmin_def = Phase.phase 1 Define`
  tickintvlmin = 100/(105*HZ) : real
`(*: @mergewithnext :*);

val tickintvlmax_def = Phase.phase 1 Define`
  tickintvlmax = 105/(100*HZ) : real
`
(*:
@description
The actual bounds on the tick interval, in seconds-per-tick; must include [[1/HZ]], and be within the RFC1323 bounds of 1sec to 1msec.
:*)
;

val stopwatchfuzz_def = Phase.phase 1 Define`
  stopwatchfuzz = (5/100) : real  (* +/- factor on accuracy of stopwatch timers *)
`(*: @mergewithnext :*);

val stopwatch_zero_def = Phase.phase 1 Define`
  stopwatch_zero = Stopwatch(0,1/(1+stopwatchfuzz),1+stopwatchfuzz)
`
(*:
@description
A stopwatch timer is initialised to [[stopwatch_zero]], which gives it an initial time of [[0]] and a fuzz of [[stopwatchfuzz]].
:*)
;

val SLOW_TIMER_INTVL_def = Phase.phase 1 Define`
  SLOW_TIMER_INTVL = (1/2) : duration  (* slow timer is 500msec on BSD *)
`(*: @mergewithnext :*);

val SLOW_TIMER_MODEL_INTVL_def = Phase.phase 1 Define`
  SLOW_TIMER_MODEL_INTVL = (1/1000) : duration (*: 1msec fuzziness to mask atomicity of model; Note that it might be possible to reduce this fuzziness :*)
`(*: @mergewithnext :*);

val FAST_TIMER_INTVL_def = Phase.phase 1 Define`
  FAST_TIMER_INTVL = (1/5) : duration  (* fast timer is 200msec on BSD *)
`(*: @mergewithnext :*);

val FAST_TIMER_MODEL_INTVL_def = Phase.phase 1 Define`
  FAST_TIMER_MODEL_INTVL = (1/1000) : duration (*: 1msec fuzziness to mask atomicity of model; Note that it might be possible to reduce this fuzziness :*)
`(*: @mergewithnext :*);

val KERN_TIMER_INTVL_def = Phase.phase 1 Define`
  KERN_TIMER_INTVL = tickintvlmax : duration  (* precision of select timer *)
`(*: @mergewithnext :*);

val KERN_TIMER_MODEL_INTVL_def = Phase.phase 1 Define`
  KERN_TIMER_MODEL_INTVL = (the_time dschedmax) : duration (*: Note that some fuzziness may be required here :*)
  (* Note this was previously 0usec fuzziness; it should really have some fuzziness, though dschedmax
     has a current value of 1s which is too high. Once epsilon_2 is used properly by the checker,
     we should be able to reduce this fuzziness as it will enable the time transitions to be
     split. e.g. in pselect rules, we really want to change from PSelect2() to Ret() states
     pretty much exactly when the timer goes off, then allow a further epsilon transition
     before returning. *)
`
(*:
@description
The slow, fast, and kernel timers are the timers used to control TCP time-related behaviour.
The parameters here set their rates and fuzziness.

The slow timer is used for retransmit, persist, keepalive, connection
establishment, FIN\_WAIT\_2, 2MSL, and linger timers.  The fast timer
is used for delayed acks.  The kernel timer is used for timestamp
expiry, \texttt{select}, and bad-retransmit detection.
:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[params_portsetc]] ALL Ports, sockets, and files

Parameters defining the classes of ports, and limits on numbers of
file descriptors and sockets.

:*)
(* ------------------------------------------------------------------ *)

val privileged_ports_def = Phase.phase 1 Define`
  privileged_ports = { Port n | n < 1024 }
`(*: @mergewithnext :*);

val ephemeral_ports_def = Phase.phase 1 Define`
  ephemeral_ports = { Port n | n >= 1024 /\ n <= 5000 }
`
(*:
@description
Ports below 1024 are reserved, and can be bound by privileged users
only.  Ports in the range 1024 through 5000 inclusive are used for
autobinding, when no specific port is specified; these ports are
called "ephemeral".
:*)
;

val OPEN_MAX_def = Phase.phase 1 Define`
  OPEN_MAX = 957 : num  (*: typical value of |kern.maxfilesperproc| on one of our BSD boxen :*)
`(*: @mergewithnext :*);

val OPEN_MAX_FD_def = Phase.phase 1 Define`
  OPEN_MAX_FD = FD OPEN_MAX
`
(*:
@description
A process may hold a maximum of [[OPEN_MAX]] file descriptors at any
one time.  These are numbered consecutively from zero on non-Windows
architectures, and so the first forbidden file descriptor is [[OPEN_MAX_FD]].
:*)
;

val FD_SETSIZE_def = Phase.phase 1 Define`
  (FD_SETSIZE : arch -> num)  Linux_2_4_20_8 = 1024n /\
   FD_SETSIZE                 WinXP_Prof_SP1 = 64n /\
   FD_SETSIZE                 FreeBDS_4_6_RELEASE = 1024n
`
(*:
@description
The sets of file descriptors used in calls to [[pselect]] can contain
only file descriptors numbered less than [[FD_SETSIZE]].

@variation WinXP

[[FD_SETSIZE]] refers to the maximum number of file descriptors in a
file descriptor set.
:*)
;


val SOMAXCONN_def = Phase.phase 1 Define`
  SOMAXCONN = 128 : num
`
(*:
@description
The maximum listen-queue length.
:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[params_udp]] UDP UDP parameters

UDP-specific parameters.

:*)
(* ------------------------------------------------------------------ *)

val UDPpayloadMax_def = Phase.phase 1 Define`
    (UDPpayloadMax : arch -> num)
                      Linux_2_4_20_8 = 65507n /\
    UDPpayloadMax WinXP_Prof_SP1 = 65507n /\
    UDPpayloadMax FreeBSD_4_6_RELEASE = 9216n
`
(*:
@description
The architecture-dependent maximum payload for a UDP datagram.
:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[params_buffers]] ALL Buffers

Parameters to the buffer size computation.

:*)
(* ------------------------------------------------------------------ *)

val MCLBYTES_def = Phase.phase 1 Define` (* size of an mbuf cluster *)
  MCLBYTES = 2048 : num  (* BSD default on i386; really, just needs to be >=1500 to fit an etherseg *)
`(*: @mergewithnext :*);

val MSIZE_def = Phase.phase 1 Define`
  MSIZE = 256 : num  (* BSD default on i386; really, size of an mbuf *)
`(*: @mergewithnext :*);

val SB_MAX_def = Phase.phase 1 Define`
  SB_MAX = 256 * 1024 : num  (* BSD *)
`(*: @mergewithnext :*);

val oob_extra_sndbuf_def = Phase.phase 1 Define`
  oob_extra_sndbuf = 1024 : num
`;



(* ------------------------------------------------------------------ *)
(*:
@section [[params_flags]] ALL File and socket flag defaults

Default values of file and socket flags, applied on creation.  Some of
these are architecture-dependent. Note that [[SO_BSDCOMPAT]] should
really be set to [[T]] by default on FreeBSD.

:*)
(* ------------------------------------------------------------------ *)

val ff_default_b_def = Phase.phase 1 Define`
(*: file flags default :*)
  (ff_default_b : filebflag -> bool)
                O_NONBLOCK = F /\
   ff_default_b O_ASYNC    = F
`(*: @mergewithnext :*);
val ff_default_def = Phase.phase 1 Define`
  ff_default = <| b := ff_default_b |>
`;

val sf_default_b_def = Phase.phase 1 Define`
(*: [[bool]] socket flags default :*)
  (sf_default_b : sockbflag -> bool)
               SO_BSDCOMPAT  = F /\
  sf_default_b SO_REUSEADDR  = F /\
  sf_default_b SO_KEEPALIVE  = F /\
  sf_default_b SO_OOBINLINE  = F /\
  sf_default_b SO_DONTROUTE  = F
`;


val sf_default_n_def = Phase.phase 1 Define`
(*: [[num]] socket flags defaults :*)
  (sf_default_n : arch -> socktype -> socknflag -> num)
               Linux_2_4_20_8 SOCK_STREAM SO_SNDBUF      = 16384 /\ (* from tests *)
  sf_default_n WinXP_Prof_SP1 SOCK_STREAM SO_SNDBUF      = 8192 /\ (* from tests *)
  sf_default_n FreeBSD_4_6_RELEASE SOCK_STREAM SO_SNDBUF = 32*1024 /\ (* from code*)

  sf_default_n Linux_2_4_20_8 SOCK_STREAM SO_RCVBUF      = 43689 /\ (* from tests - strange number? *)
  sf_default_n WinXP_Prof_SP1 SOCK_STREAM SO_RCVBUF      = 8192  /\ (* from tests *)
  sf_default_n FreeBSD_4_6_RELEASE SOCK_STREAM SO_RCVBUF = 57344 /\ (* from code *)

  sf_default_n Linux_2_4_20_8 SOCK_STREAM SO_SNDLOWAT      = 1 /\ (* from tests *)
  sf_default_n WinXP_Prof_SP1 SOCK_STREAM SO_SNDLOWAT      = 1 /\ (* Note this value has not been checked in testing. *)
  sf_default_n FreeBSD_4_6_RELEASE SOCK_STREAM SO_SNDLOWAT = 2048 /\ (* from code *)

  sf_default_n Linux_2_4_20_8 SOCK_STREAM SO_RCVLOWAT      = 1 /\ (* from tests *)
  sf_default_n WinXP_Prof_SP1 SOCK_STREAM SO_RCVLOWAT      = 1 /\
  sf_default_n FreeBSD_4_6_RELEASE SOCK_STREAM SO_RCVLOWAT = 1 /\ (* from code *)

  sf_default_n Linux_2_4_20_8 SOCK_DGRAM SO_SNDBUF       = 65535 /\ (* from tests *)
  sf_default_n WinXP_Prof_SP1 SOCK_DGRAM SO_SNDBUF       = 8192 /\  (* from tests *)
  sf_default_n FreeBSD_4_6_RELEASE SOCK_DGRAM SO_SNDBUF  = 9216  /\ (* from code *)

  sf_default_n Linux_2_4_20_8 SOCK_DGRAM SO_RCVBUF       = 65535 /\ (* correct from tests *)
  sf_default_n WinXP_Prof_SP1 SOCK_DGRAM SO_RCVBUF       = 8192 /\  (* correct from tests *)
  sf_default_n FreeBSD_4_6_RELEASE SOCK_DGRAM SO_RCVBUF  = 42080 /\ (*: from tests but:  41600 from code; i386 only as dependent on |sizeof(struct sockaddr_in)| :*)

  sf_default_n Linux_2_4_20_8 SOCK_DGRAM SO_SNDLOWAT       = 1 /\ (* from tests *)
  sf_default_n WinXP_Prof_SP1 SOCK_DGRAM SO_SNDLOWAT       = 1 /\ (* from tests *)
  sf_default_n FreeBSD_4_6_RELEASE SOCK_DGRAM SO_SNDLOWAT  = 2048 /\ (* from code *)

  sf_default_n Linux_2_4_20_8 SOCK_DGRAM SO_RCVLOWAT       = 1 /\ (* from tests *)
  sf_default_n WinXP_Prof_SP1 SOCK_DGRAM SO_RCVLOWAT       = 1 /\ (* from tests *)
  sf_default_n FreeBSD_4_6_RELEASE SOCK_DGRAM SO_RCVLOWAT  = 1 (* from code *)
`;

val sf_default_t_def = Phase.phase 1 Define`
(*: [[time]] socket flags defaults :*)

  (sf_default_t : socktflag -> time)
               SO_LINGER     = time_infty /\
  sf_default_t SO_SNDTIMEO   = time_infty /\
  sf_default_t SO_RCVTIMEO   = time_infty
`;

val sf_default_def = Phase.phase 1 Define`
(*: socket flags defaults :*)
  sf_default arch socktype = <| b := sf_default_b;
                                n := sf_default_n arch socktype;
                                t := sf_default_t
                              |>
`;

val sf_min_n_def = Phase.phase 1 Define`
(*: minimum values of [[num]] socket flags :*)
  (sf_min_n : arch -> socknflag -> num)
           Linux_2_4_20_8 SO_SNDBUF      = 2048 /\ (* from tests *)
  sf_min_n WinXP_Prof_SP1 SO_SNDBUF      = 0 /\ (* from tests *)
  sf_min_n FreeBSD_4_6_RELEASE SO_SNDBUF = 1 /\ (* from code *)
  sf_min_n Linux_2_4_20_8 SO_RCVBUF      = 256 /\ (* from tests *)
  sf_min_n WinXP_Prof_SP1 SO_RCVBUF      = 0 /\ (* from tests *)
  sf_min_n FreeBSD_4_6_RELEASE SO_RCVBUF = 1 /\ (* from code *)
  sf_min_n Linux_2_4_20_8 SO_SNDLOWAT      = 1 /\ (* from tests *)
  sf_min_n WinXP_Prof_SP1 SO_SNDLOWAT      = 1 /\ (* Note this value has not been checked in testing. *)
  sf_min_n FreeBSD_4_6_RELEASE SO_SNDLOWAT = 1 /\ (* from code *)
  sf_min_n Linux_2_4_20_8 SO_RCVLOWAT      = 1 /\ (* from tests *)
  sf_min_n WinXP_Prof_SP1 SO_RCVLOWAT      = 1 /\ (* Note this value has not been checked in testing. *)
  sf_min_n FreeBSD_4_6_RELEASE SO_RCVLOWAT = 1  (* from code *)
`(*: @mergewithnext :*);

val sf_max_n_def = Phase.phase 1 Define`
(*: maximum values of [[num]] socket flags :*)
  (sf_max_n : arch -> socknflag -> num)
           Linux_2_4_20_8 SO_SNDBUF      = 131070 /\ (* from tests *)
  sf_max_n WinXP_Prof_SP1 SO_SNDBUF      = 131070 /\ (* from tests *)
  sf_max_n FreeBSD_4_6_RELEASE SO_SNDBUF =
       SB_MAX * MCLBYTES DIV (MCLBYTES + MSIZE) /\ (* from code *)
  sf_max_n Linux_2_4_20_8 SO_RCVBUF      = 131070 /\ (* from tests *)
  sf_max_n WinXP_Prof_SP1 SO_RCVBUF      = 131070 /\ (* from tests *)
  sf_max_n FreeBSD_4_6_RELEASE SO_RCVBUF =
       SB_MAX * MCLBYTES DIV (MCLBYTES + MSIZE) /\ (* from code *)
  sf_max_n Linux_2_4_20_8 SO_SNDLOWAT      = 1 /\ (* from tests *)
  sf_max_n WinXP_Prof_SP1 SO_SNDLOWAT      = 1 /\ (* Note this value has not been checked in testing. *)
  sf_max_n FreeBSD_4_6_RELEASE SO_SNDLOWAT =
       SB_MAX * MCLBYTES DIV (MCLBYTES + MSIZE) /\ (* clip to SO_SNDBUF *)
  sf_max_n Linux_2_4_20_8 SO_RCVLOWAT      = w2n INT32_SIGNED_MAX /\ (* from code *)
  sf_max_n WinXP_Prof_SP1 SO_RCVLOWAT      = 1 /\ (* Note this value has not been checked in testing. *)
  sf_max_n FreeBSD_4_6_RELEASE SO_RCVLOWAT =
       SB_MAX * MCLBYTES DIV (MCLBYTES + MSIZE)(* clip to SO_RCVBUF *)
`;

val sndrcv_timeo_t_max_def = Phase.phase 1 Define`
(*: maximum value of [[send]]/[[recv]] timeouts :*)
  sndrcv_timeo_t_max = time 655350000
`(*: @mergewithnext :*);

val pselect_timeo_t_max_def = Phase.phase 1 Define`
(*: maximum value of [[pselect]] timeouts :*)
  pselect_timeo_t_max = time (31 * 24 * 3600)
`;



(* ------------------------------------------------------------------ *)
(*:
@section [[params_rfc]] TCP RFC-specified limits

Protocol value limits specified in the TCP RFCs.

:*)
(* ------------------------------------------------------------------ *)

val dtsinval_def = Phase.phase 1 Define`
(*:
RFC1323 s4.2.3: timestamp validity period.
:*)  dtsinval = time (24 * 24 * 60 * 60)
`
;

val TCP_MAXWIN_def = Phase.phase 1 Define`
(*: maximum (scaled) window size :*)
  TCP_MAXWIN = 65535 : num
`(*: @mergewithnext :*);

val TCP_MAXWINSCALE_def = Phase.phase 1 Define`
(*: maximum window scaling exponent :*)
  TCP_MAXWINSCALE = 14 : num
`
(*:
@description
The maximum (scaled) window size value is [[TCP_MAXWIN]], and
the maximum scaling exponent is [[TCP_MAXWINSCALE]].  Thus the maximum
window size is [[TCP_MAXWIN << TCP_MAXWINSCALE]].
:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[params_proto]] TCP Protocol parameters

Various TCP protocol parameters, many adjustable by |sysctl| settings
(or equivalent).  The values here are typical.  It was not considered
worthwhile modelling these parameters changing during operation.

:*)
(* ------------------------------------------------------------------ *)

val MSSDFLT_def = Phase.phase 1 Define`
(*: initial [[t_maxseg]], modulo route and link MTUs :*)
  MSSDFLT = 512 : num  (* BSD default; RFC1122 sec. 4.2.2.6 says this MUST be 536 *)
`;

(* X
val SS_FLTSZ_LOCAL_def = Phase.phase 1 Define`
(*: initial [[snd_cwnd]] for local connections :*)
  SS_FLTSZ_LOCAL = 4 : num  (* BSD; is a sysctl *)
`(*: @mergewithnext :*);

val SS_FLTSZ_def = Phase.phase 1 Define`
(*: initial [[snd_cwnd]] for non-local connections :*)
  SS_FLTSZ = 1 : num  (* BSD; is a sysctl *)
`;

val TCP_DO_NEWRENO_def = Phase.phase 1 Define`
(*: do NewReno fast recovery :*)
  TCP_DO_NEWRENO = T : bool (* BSD default *)
`;
X *)

val TCP_Q0MINLIMIT_def = Phase.phase 1 Define`
  TCP_Q0MINLIMIT = 30 : num  (* FreeBSD 4.6-RELEASE: tcp_syncache.bucket_limit *)
`(*: @mergewithnext :*);

val TCP_Q0MAXLIMIT_def = Phase.phase 1 Define`
  TCP_Q0MAXLIMIT = 512 * 30 : num  (* FreeBSD 4.6-RELEASE: tcp_syncache.cache_limit *)
`
(*:
@description
The incomplete-connection listen queue [[q0]] has a nondeterministic
length limit.  Connections \emph{may} be dropped once [[q0]] reaches
[[TCP_Q0MINLIMIT]], and \emph{must} be dropped once [[q0]] reaches
[[TCP_Q0MAXLIMIT]].
:*)
;

val backlog_fudge_def = Phase.phase 1 Define`
  backlog_fudge (n:int) = MIN SOMAXCONN (clip_int_to_num n)
`
(*:
@description
The backlog length fudge-factor function, which translates the
requested length of the listen queue into the actual value used.  Some
architectures apply a linear transformation here.
:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[params_timevalues]] TCP Time values

Various time intervals controlling TCP's behaviour.

:*)
(* ------------------------------------------------------------------ *)

(* X

val TCPTV_DELACK_def = Phase.phase 1 Define`
  TCPTV_DELACK = time (1 / 10)  (* FreeBSD 4.6-RELEASE, tcp_timer.h *)
`
(*: @description
TODO3: SAY WHAT ALL THESE TIMER VALUES MEAN
:*)
;


val TCPTV_RTOBASE_def = Phase.phase 1 Define`
  TCPTV_RTOBASE = 3 : duration (* initial RTT, in seconds: FreeBSD 4.6-RELEASE, tcp_timer.h *)
`(*: @mergewithnext :*);

val TCPTV_RTTVARBASE_def = Phase.phase 1 Define`
  TCPTV_RTTVARBASE = 0 : duration  (* initial retransmit variance, in seconds *)
     (* FreeBSD has no way of encoding an initial RTT variance,
        but we do (thanks to tf_srttvalid); it should be zero
        so TCPTV_RTOBASE = initial RTO *)
`(*: @mergewithnext :*);

val TCPTV_MIN_def = Phase.phase 1 Define`
  TCPTV_MIN = 1 : duration  (* minimum RTT in absence of cached value, in seconds: FreeBSD 4.6-RELEASE, tcp_timer.h *)
`(*: @mergewithnext :*);

val TCPTV_REXMTMAX_def = Phase.phase 1 Define`
  TCPTV_REXMTMAX = time 64  (* BSD: maximum possible RTT *)
`;

X *)

val TCPTV_MSL_def = Phase.phase 1 Define`
  TCPTV_MSL = time 30 (* maximum segment lifetime: BSD: tcp_timer.h:79 *)
`;


val TCPTV_PERSMIN_def = Phase.phase 1 Define`
  TCPTV_PERSMIN = time 5  (* BSD: minimum possible persist interval: tcp_timer.h:85 *)
`(*: @mergewithnext :*);

val TCPTV_PERSMAX_def = Phase.phase 1 Define`
  TCPTV_PERSMAX = time 60  (* BSD: maximum possible persist interval: tcp_timer.h:86 *)
`;


val TCPTV_KEEP_INIT_def = Phase.phase 1 Define`
  TCPTV_KEEP_INIT = time 75 (* connect timeout: BSD: tcp_timer.h:88 *)
`(*: @mergewithnext :*);

val TCPTV_KEEP_IDLE_def = Phase.phase 1 Define`
  TCPTV_KEEP_IDLE = time (120*60) (* time before first keepalive probe: BSD: tcp_timer.h:89 *)
`(*: @mergewithnext :*);

val TCPTV_KEEPINTVL_def = Phase.phase 1 Define`
  TCPTV_KEEPINTVL = time 75 (* time between subsequent keepalive probes: BSD: tcp_timer.h:90 *)
`(*: @mergewithnext :*);

val TCPTV_KEEPCNT_def = Phase.phase 1 Define`
  TCPTV_KEEPCNT = 8 : num (* max number of keepalive probes (+/- a few?): BSD: tcp_timer.h:91 *)
`(*: @mergewithnext :*);

val TCPTV_MAXIDLE_def = Phase.phase 1 Define`
  TCPTV_MAXIDLE = 8 * TCPTV_KEEPINTVL (* BSD calls this tcp_maxidle *)
`;



(* ------------------------------------------------------------------ *)
(*:
@section [[params_timingrelated]] TCP Timing-related parameters

Parameters relating to TCP's exponential backoff.

:*)
(* ------------------------------------------------------------------ *)

val TCP_BSD_BACKOFFS_def = Phase.phase 1 Define` (* TCP exponential retransmit backoff: BSD: from source code, tcp_timer.c:155 *)
  TCP_BSD_BACKOFFS = [ 1; 2; 4; 8; 16; 32; 64; 64; 64; 64; 64; 64; 64 ] : num list
`(*: @mergewithnext :*);

val TCP_LINUX_BACKOFFS_def = Phase.phase 1 Define` (* TCP exponential retransmit backoff: Linux: experimentally determined *)
  TCP_LINUX_BACKOFFS = [ 1; 2; 4; 8; 16; 32; 64; 128; 256; 512; 512 ] : num list (* Note: the tail may be  incomplete *)
`(*: @mergewithnext :*);

val TCP_WINXP_BACKOFFS_def = Phase.phase 1 Define` (* TCP exponential retransmit backoff: WinXP: experimentally determined *)
  TCP_WINXP_BACKOFFS = [ 1; 2; 4; 8; 16 ] : num list (* Note: the tail may be incomplete *)
`;

val TCP_MAXRXTSHIFT_def = Phase.phase 1 Define`
(*: TCP maximum retransmit shift :*)
  TCP_MAXRXTSHIFT = 12 : num  (* TCPv2p842 *)
`(*: @mergewithnext :*);

val TCP_SYNACKMAXRXTSHIFT_def = Phase.phase 1 Define`
(*: TCP maximum SYNACK retransmit shift :*)
  TCP_SYNACKMAXRXTSHIFT = 3 : num  (* FreeBSD 4.6-RELEASE, tcp_syncache.c:SYNCACHE_MAXREXMTS *)
`;


val TCP_SYN_BSD_BACKOFFS_def = Phase.phase 1 Define` (* TCP exponential SYN retransmit backoff: BSD: tcp_timer.c:152 *)
  TCP_SYN_BSD_BACKOFFS = [ 1; 1; 1; 1; 1; 2; 4; 8; 16; 32; 64; 64; 64 ] : num list (* Our experimentation shows that this list stops at 8. This will be
   due to the connection establishment timer firing. Values here are
   obtained from the BSD source *)
`(*: @mergewithnext :*);

val TCP_SYN_LINUX_BACKOFFS_def = Phase.phase 1 Define` (* TCP exponential SYN retransmit backoff: Linux: experimentally determined *)
  TCP_SYN_LINUX_BACKOFFS = [ 1; 2; 4; 8; 16 ] : num list  (* This list might be longer. Experimentation does not show further entries, perhaps
   due to the connection establishment timer firing *)

`(*: @mergewithnext :*);

val TCP_SYN_WINXP_BACKOFFS_def = Phase.phase 1 Define` (* TCP exponential SYN retransmit backoff: WinXP: experimentally determined *)
  TCP_SYN_WINXP_BACKOFFS = [ 1; 2 ] : num list  (* This list might be longer. Experimentation does not show further entries, perhaps
   due to the connection establishment timer firing *)
`;



(* -------------------------------------------------- *)

val _ = export_theory();

