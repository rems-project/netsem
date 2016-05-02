(* A HOL98 specification of TCP *)

(* Type definitions of the host and its components: file, socket, TCPCB etc *)

(*[ RCSID "$Id: TCP1_preHostTypesScript.sml,v 1.4 2009/02/17 11:56:46 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

local open (*TCP1_errorsTheory
           TCP1_baseTypesTheory*)
           (* TCP1_timersTheory
           TCP1_netTypesTheory *)
	   TCP1_paramsTheory
in end

local open arithmeticTheory stringTheory pred_setTheory integerTheory
           finite_mapTheory realTheory bagTheory containerTheory in end;


val _ = new_theory "TCP1_preHostTypes";

(* -------------------------------------------------- *)
(*                       TCP STATES            *)
(* -------------------------------------------------- *)

(*: @section [[hostty_tcpstates]] TCP TCP states

TODO3

:*)

val _ = Hol_datatype`(*: TCP protocol states :*)
   tcpstate =  CLOSED
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
`(*:
@description
The states laid down by RFC793, with spelling as in the BSD source.

:*);

(* stripped the TCP control block flags TF_* and the OOB flags
TCBOOB_*, as these are not used in our model (we model them directly
in other ways).  See CVS r1.135 for the definitions. *)


val _ = Hol_datatype`(*: extra info for a listening socket :*)
   socket_listen
     = <| q0 : sid list; (* incomplete connections queue *)
          q  : sid list; (* completed connections queue *)
          qlimit : int   (* backlog value as passed to listen *)
       |>
`;

val _ = Hol_datatype`(*: ordinary datagram on UDP receive queue :*)
   dgram_msg
     = <| data : byte list;
          is   : ip option;  (* source ip *)
          ps   : port option (* source port *)
       |>
`(*:@mergewithnext:*);
(*        ifid : ifid;*)


val _ = Hol_datatype`(*: error (pseudo-)datagram on UDP receive queue :*)
   dgram_error
     = <| e : error |>
`(*:@mergewithnext:*);

val _ = Hol_datatype`(*: receive queue elements for a UDP socket :*)
   dgram = Dgram_msg of dgram_msg
         | Dgram_error of dgram_error
`(*:@mergewithnext:*);

val _ = Hol_datatype`(*: details of a UDP socket :*)
   udp_socket
     = <| rcvq : dgram list  |>
`(*:
@description
%
UDP sockets are very simple -- the protocol-specific content is merely
a receive queue.
%
The receive queue of a UDP socket, however, is not just
a queue of bytes as it is for a TCP socket.  Instead, it
is a queue of \emph{messages} and (in some implementations)
\emph{errors}.  Each message contains a block of types and some
ancilliary data.

@variation WinXP

On WinXP, errors are returned in order w.r.t.~messages; this is modelled
by placing them in the receive queue.

@variation FreeBSD,Linux

On FreeBSD and Linux, only messages are placed in the receive queue,
and errors are treated asynchronously.

:*);

val _ = Hol_datatype `(*: network interface descriptor :*)
                      ifd = <| ipset : ip set; (* set of IP addresses of this interface *)
                               primary : ip; (* and the primary IP address *)
                               netmask : netmask; (* netmask *)
                               up : bool  (* status: up (and connected) or not *)
                            |>`;

val _ = Hol_datatype`(*: routing table entry :*)
  routing_table_entry = <| destination_ip : ip;
                           destination_netmask : netmask;
                           ifid : ifid
                        |>
`
(*: @description

Note that both routing table entries and interfaces have IP addresses
(plural for interfaces, singular for RTEs) and netmasks; furthermore,
interfaces have a primary IP.  When we do routing, we ignore the IP
addresses and mask of the interface; we only use the address and mask
from the RTE.  The only use of the interface info is to obtain the
primary IP for use by connect().

However, there is one place where all the interface data is used: on
input, the interface IP addresses are consulted to see if we
can receive a packet.

The netmask of the interface is not used in the specification (except
by [[getifaddrs()]]).  Its function in the implementation relates to
gateways etc., which (as we abstract from IP routing) we do not model.

Note that the model does not represent the routing \emph{cache} here
(i.e., cached routes with gateways, MSS, RTT, etc.), just the routing
\emph{table}.
Cache data is treated nondeterministically.

@internal

You might expect some consistency between rte info and that of the
corresponding interface, but we do not enforce this (perhaps we
should?).


 no need for gateway, since we know only the IP model of the
network, as a fuzzy cloud rather than a network of routers

:*)
;

val _ = type_abbrev ("routing_table", ``:routing_table_entry list``);


val _ = Hol_datatype`(*: segment category, determining which band limiter to use :*)
  bandlim_reason = BANDLIM_UNLIMITED
                 | BANDLIM_RST_CLOSEDPORT
                 | BANDLIM_RST_OPENPORT
`(*: @description
internal bandlimiter state; intended to be opaque
 :*)
;


val _ = type_abbrev ("bandlim_state", ``:(tcpSegment # ts_seq # bandlim_reason) list``);


val _ =
  Hol_datatype`(*: state of host wrt a thread :*)
    hostThreadState = Run              (*: thread is running :*)
                    | Ret of TLang     (*: about to return given value to thread :*)
                    | Accept2 of sid   (*: blocked in [[accept]] :*)
                    | Close2 of sid    (*: blocked in [[close]] :*)
                    | Connect2 of sid  (*: blocked in [[connect]] :*)
                    | Recv2 of sid # num # msgbflag set  (*: blocked in [[recv]] :*)
                    | Send2 of sid # ((ip # port) option # ip option # port option # ip option # port option) option
                        # byte list # msgbflag set  (*: blocked in [[send]] :*)
                    | PSelect2 of fd list # fd list # fd list  (*: blocked in [[pselect]] :*)
`(*:
@description
Host threads are either [[Run]]ning or executing a sockets call.  The latter can either be about to return a value to the thread (state [[Ret]]) or blocked; the remaining states capture the data required for the unblock processing for each slow call.
:*);

                  (* | Exit
                     | Zombie
                     | Delay2
                     | Print2 of string *)

val _ = Hol_datatype `(*: other relevant bits of host configuration :*)
    hostParams = <|
                    min_eph_port  : num;
                    max_eph_port  : num
                  |>
`(*:
@description Specifies (inclusive) lower and upper bounds for the ephemeral
ports range, which can vary
from host to host; notably, the Linux kernel picks values for these parameters
based on the amount of available memory.
:*);

val _ = Hol_datatype`(*: trace record flavours :*)
  traceflavour = TA_INPUT
               | TA_OUTPUT
               | TA_USER
               | TA_RESPOND
               | TA_DROP
`
(*: @description
Different situations in which a trace may be generated.

:*);


val _ = Hol_datatype `
    hostid =
        Test
      | Aux
`;


(* -------------------------------------------------- *)
(*               RULE CATEGORIES                      *)
(* -------------------------------------------------- *)

(*: @section [[host0_cats]] ALL Rule categories

A rule carries a number of flags: the protocol it relates to, its
status (success, failure, or `bad' failure), its category (fast or
slow system call, network, etc.), and its urgency (whether it must
fire immediately, or may be delayed).

:*)

val _ = Hol_datatype`
  rule_proto = rp_tcp
             | rp_udp
             | rp_all
` (*: @description
Rules are classified as to whether they relate to TCP, to UDP, or to both.
:*);

val _ = Hol_datatype`
  rule_status = succeed
              | fail
              | badfail
`(*: @description
Socket call rules marked [[succeed]] construct an [[OK v]] value to be returned to the calling thread, whereas those maked [[fail]] or [[badfail]] construct a [[FAIL e]] error to be returned.
The [[badfail]] rules are those involving (unusual) lack of resources, e.g.~of ephemeral ports, file descriptors, or kernel memory.  They are distinguished from the [[fail]] rules to make it easy to state properties of the form "if no bad failures occur, then...".
:*)
;


val _ = Hol_datatype`
  rule_cat  = fast    of rule_status
            | block
            | slow    of bool  => rule_status
            | network of bool
            | misc    of bool
` (*: @description
Socket call rules are either [[fast]], immediately constructing a return value or error, [[block]], entering a state in which the calling thread is blocked, or [[slow]], completing processing for a blocked thread.
[[fast]] and [[slow]] rules have a [[rule_status]] as above.
The [[network]] rules include message send and receive and the internal actions involved in the protocol.
The [[misc]] rules cover the remainder:
returning values to threads, timer expiry, TCP tracing, interface status changes, and time passage.
The [[bool]] argument to [[slow]], [[network]], and [[misc]] rule categories
indicates whether the rule is \emph{urgent}.  If an urgent rule is enabled then no time may pass.

:*);

(*            | exit *)


val _ = Define`urgent = T` (*: @mergewithnext :*);
val _ = Define`nonurgent = F` (*: @mergewithnext :*);

val is_urgent_def = Define`
  is_urgent (slow    b _) = b /\
  is_urgent (network b  ) = b /\
  is_urgent (misc    b  ) = b /\
  is_urgent  _            = F
`;

(* -------------------------------------------------- *)



(* ------------------------------------------------------------------ *)
(*:
@section [[aux_arch]] ALL Architecture handling

Many aspects of host behaviour differ from one OS to another, and so a
host has an architecture parameter detailing its precise OS and
version (e.g., [[Linux_2_4_20_8]]).  Very often, however, we do not
need to be so precise -- a certain behaviour might apply to all Linux,
or even all Unix, OSes.  Below we define predicates for these cases, to allow variant architectures to be easily added later.
:*)
(* ------------------------------------------------------------------ *)

val windows_arch_def = Phase.phase 1 Define`
(*: test if host architecture is Windows :*)
windows_arch arch = (arch IN {WinXP_Prof_SP1}                     )`(*: @mergewithnext :*);
val bsd_arch_def     = Phase.phase 1 Define`
(*: test if host architecture is BSD :*)
bsd_arch     arch = (arch IN {FreeBSD_4_6_RELEASE}                )`(*: @mergewithnext :*);
val linux_arch_def   = Phase.phase 1 Define`
(*: test if host architecture is Linux :*)
linux_arch   arch = (arch IN {Linux_2_4_20_8}                     )`(*: @mergewithnext :*);
val unix_arch_def    = Phase.phase 1 Define`
(*: test if host architecture is Unix :*)
unix_arch    arch = (arch IN {Linux_2_4_20_8; FreeBSD_4_6_RELEASE})`;



(* ------------------------------------------------------------------ *)
(*:
@section [[aux_if]] ALL Interfaces and IP addresses

Constructors, predicates, and helper functions that deal with
interfaces, IP addresses, and routing.

:*)
(* ------------------------------------------------------------------ *)

(* -------------------------------------------------- *)
(*                NETMASKS                            *)
(* -------------------------------------------------- *)

val mask_def = Phase.phase 1 Define`(*: apply a netmask to an IP to obtain the network number :*)
  mask (NETMASK m) (ip n) = ip ((n DIV (2 EXP (32 - m))) * 2 EXP (32 - m))
`(*:@mergewithnext:*);

val mask_bits_def = Phase.phase 1 Define`(*: compute network bitmask from netmask :*)
  mask_bits (NETMASK m) = ((2 EXP 32 - 1) DIV (2 EXP (32 - m))) * 2 EXP (32 - m)
`(*:
@description
Netmask operations.
Recall netmasks are stored as the number of 1 bits in the mask; thus
255.255.128.0 is modelled by [[NETMASK 17]].
:*);


(* -------------------------------------------------- *)
(*                TCP/IP PARAMETERS AND HELPERS       *)
(* -------------------------------------------------- *)

(* DON'T phase: in betters *)
val IP_def = Define`(*: constructor for dotted-decimal IP addresses :*)
  IP (a:num) (b:num) (c:num) (d:num) = ip (a * 2 EXP 24 + b * 2 EXP 16 + c * 2 EXP 8 + d)
`(*:@mergewithnext:*);

val IN_MULTICAST_def = Phase.phase 1 Define`(*: the set of multicast addresses :*)
  IN_MULTICAST = { i | mask (NETMASK 4) i = IP 224 0 0 0 }
`(*:@mergewithnext:*);

val INADDR_BROADCAST_def = Phase.phase 1 Define`(*: the local broadcast address :*)
  INADDR_BROADCAST = IP 255 255 255 255
`(*:@mergewithnext:*);

val LOOPBACK_ADDRS_def = Phase.phase 1 Define`(*: the set of loopback addresses :*)
  LOOPBACK_ADDRS = { i | mask (NETMASK 8) i = IP 127 0 0 0 }
`(*:@mergewithnext:*);

val ip_localhost_def = Phase.phase 1 Define`(*: the canonical loopback address, aka 'localhost' :*)
  ip_localhost = IP 127 0 0 1
`(*:@mergewithnext:*);

val in_loopback_def = Phase.phase 1 Define`(*: is IP address a loopback address? :*)
  in_loopback i = (i IN LOOPBACK_ADDRS)
`(*:@mergewithnext:*);

(* don't put any phasing on this definition; the use of FRANGE means it's
   a pain to use directly in this form; a "better" rewrite is available
   instead. *)
(* DON'T phase: in betters *)
val in_local_def = Define`(*: is IP address a local address? :*)
  in_local (ifds:ifid |-> ifd) i =
         (in_loopback i \/
         i IN (BIGUNION { ifd_.ipset | ifd_ IN (FRANGE ifds) }))
  (*: Note: the test "[[in_loopback i]]" is usually redundant as there
     is almost always a loopback interface in [[ifds]] with [[ipset = LOOPBACK_ADDRS]] :*)
`(*:@mergewithnext:*);

(* DON'T phase: in betters *)
val local_ips_def = Define`(*: the set of local IP addresses :*)
  local_ips(ifds:ifid |-> ifd) = BIGUNION { ifd_.ipset | ifd_ IN (FRANGE ifds) }
(* annoying: ifd is a constructor, and { | } has no binder to allow us
   to shadow it *)
`(*:@mergewithnext:*);

val local_primary_ips_def = Phase.phase 1 Define`(*: the set of local primary IP addresses :*)
  local_primary_ips(ifds:ifid |-> ifd) = { ifd_.primary | ifd_ IN (FRANGE ifds) }
`(*:@mergewithnext:*);

(* DON'T phase: in betters *)
val is_localnet_def = Define`(*: is IP address on a local subnet of this host? :*)
  is_localnet (ifds0:ifid |-> ifd) i =
    (?ifd. ifd IN (FRANGE ifds0) /\  mask ifd.netmask i = mask ifd.netmask ifd.primary)
`(*:@mergewithnext:*);

val if_broadcast_def = Phase.phase 1 Define`(*: is IP address a broadcast address? :*)
  if_broadcast (ifd0:ifd)
    = case (ifd0.netmask, mask ifd0.netmask ifd0.primary) of
          (NETMASK m, ip n (* n has been masked by m above *)) =>
            ip (n + 2 EXP (32 - m) - 1)
    (*: Note: would be much easier if IPs were actually [[word32]] rather than [[num]] :*)
    (*: corresponds to [[INADDR_BROADCAST]] for the interface :*)
`(*:@mergewithnext:*);

val if_any_def = Phase.phase 1 Define`(*: the set of addresses in an interface's subnet :*)
  if_any (ifd0:ifd)
    = case (ifd0.netmask, mask ifd0.netmask ifd0.primary) of
          (NETMASK m, ip n (* n has been masked by m above *)) =>
            ip (n)
    (*: Note: would be much easier if IPs were actually [[word32]] rather than [[num]] :*)
`
(*:
@description
%
Various distinguished IP addresses and sets of IP addresses.  Some of these are
are dependent on the host's set of interfaces.

:*);

val is_broadormulticast_def = Phase.phase 2 Define`(*: is IP address a broadcast/multicast address? :*)
  is_broadormulticast (ifds0:ifid |-> ifd) i =
    (i IN IN_MULTICAST \/    (*: is [[i]] a multicast address? :*)
     i = INADDR_BROADCAST \/ (*: is [[i]] the default broadcast address? [CORRECT NAME?] :*)
     ? (k, ifd0) :: ifds0.
          i IN {if_broadcast ifd0;  (*: is [[i]] the broadcast addr for any interface? :*)
                if_any ifd0})       (*: RFC 1122 - should accept an all-0s or all-1s
                                                  broadcast address. all three OSes do :*)
`
(*:
@description
 Test if IP address [[i]] is a broadcast or multicast address, wrt the
   given set of interfaces [[ifds0]].  If no interfaces given
   ([[ifds0=NONE]]), then treat only [[INADDR_BROADCAST]] as a broadcast
   address.

 These correctly use the interface rather than the routing-table
   entry to check what is a broadcast address and what is in the local net of
   this host.  Whether there is a route allowing a send to that local
   net is another question entirely, although the two data structures
   \emph{should} be consistent.
:*)
;



(* -------------------------------------------------- *)
(*                ROUTING                             *)
(* -------------------------------------------------- *)

val routeable_def = Phase.phase 1 Define`(*: compute set of routeable addresses for a routing table entry :*)
  routeable(rte:routing_table_entry) =
    { i | mask rte.destination_netmask i = mask rte.destination_netmask rte.destination_ip }
`(*:@mergewithnext:*);

(* DON'T phase: in betters *)
val outroute_ifids_def = Define`(*: determine list of possible sending interfaces :*)
  outroute_ifids(i2,rttab:routing_table) =
    MAP_OPTIONAL (\rte. if i2 IN routeable rte then SOME rte.ifid else NONE) rttab
`(*:
@description
%
Determine the list of possible interfaces to use in sending to a given
IP, based on the routing table.

:*);

val ifid_up_def = Phase.phase 1 Define`(*: is the interface up? :*)
  ifid_up (ifds : ifid |-> ifd) ifid = (ifds ' ifid).up
`(*:@mergewithnext:*);

val outroute_def = Phase.phase 1 Define`(*: compute interface to use to send to given IP, if any :*)
  outroute(i2,rttab:routing_table,ifds:ifid |-> ifd) =
    case FILTER (ifid_up ifds) (outroute_ifids(i2,rttab)) of
        []           => NONE
     |  (ifid::_987) => SOME ifid
`
(*:
@description
%
Determine the interface to use to send to a given IP, if possible.
Returns the first up interface that can route to the destination.

:*)
;

(* subnet_routeable and subnet_outroute OBSELETED; see CVS v1.166 and earlier. *)

val auto_outroute_def = Phase.phase 1 Define`(*: compute source address to use to route to given IP :*)
  auto_outroute(i2',SOME i2,rttab,ifds) = {i2} /\
  auto_outroute(i2',NONE   ,rttab,ifds) = case outroute(i2',rttab,ifds) of
                                             SOME ifid => { (ifds ' ifid).primary }
                                           | NONE      => {}
`(*:
@description
%
Compute source address to use to route to a given IP, if any possible.
If the caller provides an address, use that without checking;
otherwise try to find one.  Do not return a specific error code.  Used
for autobinding to a local IP address.

:*);

val test_outroute_ip_def = Phase.phase 1 Define`(*: test if we can route to given IP, returning appropriate error if not :*)
  test_outroute_ip(i2:ip,rttab,ifds,arch)
   = let ifids = outroute_ifids(i2,rttab) in
	 if ifids = [] then
	     (if linux_arch arch then SOME ENETUNREACH
	      else SOME EHOSTUNREACH)
	 else
	     if FILTER (ifid_up ifds) ifids = [] then
		 SOME ENETDOWN
	     else NONE
`(*:@mergewithnext:*);

(* DON't phase: is phase 1, but handled explicitly in testEval *)
val test_outroute_def = Define`(*: if destination IP specified, do [[test_outroute_ip]] :*)
  test_outroute(msg:msg,rttab,ifds,arch)
    = case msg.is2 of
        SOME i2 => SOME (test_outroute_ip(i2,rttab,ifds,arch))
      | _ => NONE
`
(*:
@description
Check that we can route the message out.
%
First check that there is an interface that can route to the destination
address.  If not, [[EHOSTUNREACH]].  Then, check that there is one of
these that is up.  If not, [[ENETDOWN]].  Otherwise, succeed (indicated by
empty set of possible errors).  The message should have [[i2]]
specified.

You might think that we should check that the interface can send from
the source address also, but in fact, in the weak end system model,
they don't need to be the same interface.  We have tested Linux, and
find this behaviour.  Not sure yet about BSD, but suspect it will be
the same.  test 20030204T1525 or so.

[[test_outroute]] modified to be functional rather than relational, as
   behaviour is purely deterministic.  The result is of type [[error
   option option]], where the first level of "optionality" indicates
   whether or not the function is even being called on valid input
   (whether or not message has an [[is2]] "field"), and the next level
   indicates errors being raised, or not.

   Note that if we "knew" that this would only be called on messages
   with ok [[is2]] fields, then it would easier still to just use [[THE]],
   ignore the fact that the function had an unspecified result on
   arguments with bad [[is2]] fields, and make the result type [[ error option]].
:*)
;

val loopback_on_wire_def = Phase.phase 1 Define`(*: check if a message bears a loopback address :*)
  loopback_on_wire (msg:msg) (ifds:ifid |-> ifd) =
     case (msg.is1, msg.is2) of
        (NONE, NONE)     => F
      | (NONE, SOME j)   => F
      | (SOME i, NONE)   => F
      | (SOME i, SOME j) => in_loopback i /\ ~in_local ifds j
`
(*:
@description
 RFC1122 says loopback addresses must never appear on the wire.  Here we test if
   this segment is in violation.  Ideally, we'd check "(src or dest in
   loopback net) and interface not loopback", but we can't see which
   interface it's going out of in this model.  The condition above is
   possibly the best approximation we can make if one considers the possible
   values of [[msg.is1]] and [[msg.is2]].
:*)
;


(* ------------------------------------------------------------------ *)
(*:
@section [[aux_files]] ALL Files, file descriptors, and sockets

   The open files of a host are modelled by a set of open file
   descriptions, indexed by [[fid]].  The open files of a process are
   identified by file descriptor [[fd]], which is an index into a
   table of [[fid]]s.  This table is modelled by a finite map.
   File descriptors are isomorphic to the natural numbers.

:*)
(* ------------------------------------------------------------------ *)

(* This was a nasty list-based representation, but MichaelN changed it
   to a much nicer finite map representation. A lot of the auxiliaries
   that were here became inlined into the hostLTS side conditions. *)

val fdlt_def = Phase.phase 1 Define`(*: [[<]] comparison on file descriptors :*)
  fdlt (FD n) (FD m) <=> n < m
`(*: @mergewithnext :*);

val fdle_def = Phase.phase 1 Define`(*: [[<=]] comparison on file descriptors :*)
  fdle (FD n) (FD m) <=> n <= m
`(*:@mergewithnext:*);

val _ = overload_on ("<", ``fdlt``);
val _ = overload_on ("<=", ``fdle``);

val leastfd_def = Phase.phase 1 Define`(*: least [[fd]] satisfying predicate [[P]] :*)
  leastfd P = FD (LEAST n. P (FD n))
`(*:@mergewithnext:*);

val _ = set_fixity "leastfd" Binder;

(* DON'T phase: in betters *)
val nextfd_def = Define`(*: next file descriptor to use :*)
  nextfd arch fds fd' = if windows_arch arch then
                            (* no ordering on Windows fds; they're just handles *)
                            fd' NOTIN FDOM fds
                        else
                            (* POSIX architectures allocate in order *)
                            fd' = leastfd fd'. fd' NOTIN FDOM fds
`(*:
@description
%
Basic operations on file descriptors.  Normally, when a new file
descriptor is required the least unused one is used.

@variation WinXP

On Windows, file descriptors are opaque handles, and have no useful
ordering.  In particular, [[nextfd]] returns an arbitrary unused file
descriptor.

:*);

(* DON'T phase: in betters *)
val fid_ref_count_def = Define`(*: count references to given [[fid]] :*)
   fid_ref_count(fds:fd |-> fid,fid) = CARD (FDOM (RRESTRICT fds {fid}))
`
(*:
@description
A file is closed when its reference count drops to zero.  This function determines the
reference count of a file (strictly, a [[fid]]).
@internal
 When generalising to multiple processes, be sure to extend this to
   look at \emph{all} file descriptor tables, not just that of the current
   process

:*)
;


(* ------------------------------------------------------------------ *)
(*:
@section [[aux_timers]] ALL Timers

Many TCP protocol events are time-dependent, and time is also
necessary for a useful specification of the behaviour of system calls,
returns, and datagram emission and receipt.  These common
time-dependent behaviours are described using the timers below.

:*)
(* ------------------------------------------------------------------ *)

val slow_timer_def  = Phase.phase 1 Define`(*: TCP slow timer, typically 500ms resolution (for keepalive, MSL, linger, badrxtwin) :*)
  slow_timer d = fuzzy_timer d SLOW_TIMER_INTVL SLOW_TIMER_MODEL_INTVL`(*: @mergewithnext :*);
val fast_timer_def  = Phase.phase 1 Define`(*: TCP fast timer, typically 200ms resolution (for delack) :*)
  fast_timer d = fuzzy_timer d FAST_TIMER_INTVL FAST_TIMER_MODEL_INTVL`(*: @mergewithnext :*);
val kern_timer_def  = Phase.phase 1 Define`(*: kernel timer, typically 10ms resolution (for timestamp valid, pselect) :*)
  kern_timer d = fuzzy_timer d KERN_TIMER_INTVL KERN_TIMER_MODEL_INTVL`(*: @mergewithnext :*);
val sched_timer_def    = Phase.phase 3 Define`(*: scheduling timer (for OS returns) :*)
  sched_timer     = upper_timer dschedmax`(*: @mergewithnext :*);
val inqueue_timer_def  = Phase.phase 1 Define`(*: in-queue timer (incoming message processing) :*)
  inqueue_timer   = upper_timer diqmax`(*: @mergewithnext :*);
val outqueue_timer_def = Phase.phase 2 Define`(*: out-queue timer (outgoing message emission) :*)
  outqueue_timer  = upper_timer doqmax`
(*:
@description

   Traditionally TCP has been implemented using two timers, a slow
   timer ticking once every 500ms, and a fast timer ticking once every
   200ms.  In addition, the kernel is assumed to maintain a tick
   count, typically incremented every 10ms.

   Measuring intervals with such a timer means an uncertainty in
   duration: the observed interval may be up to one tick less than the
   specified interval, and is on average half a tick less.  We model
   this with a {@link [[fuzzy_timer]]}, fuzzy to the left by [[eps]]
   and to the right by [[fuz]], i.e., [[ [d-eps,d+fuz] ]].

    The [[eps]], one tick, accounts for the fact that we do not know
      where in the clock's period we set the timer.

    The [[fuz]] (some global fuzziness) is included
    to account for the atomicity of the model.
      For example, an implementation TCP processing step, performed by
  |tcp_output| etc., occupies some time interval, with timers such as
  [[tt_rexmt]] being reset at various points within that interval.
  The model, on the other hand, has atomic transitions.
  The possible time difference between multiple timer resets in the same step must be accounted for by this fuzziness.

    For example,
   a model rule may
   reset the [[tt_rexmt]] timer and also leave a segment on the output queue,
   with  time passing before the segment is seen on the wire.
%
%
%
%
% This time
%    passage covers not only the time to emit the packet but the mainly
%    unobservable (except for BSD) TCP processing being performed by the
%    host in [[tcp_output]] and friends. The period of TCP processing that
%    occurs before the rexmt timer is \emph{really} reset must be accounted for
%    by the fuzziness.

The various flavours of {@link [[upper_timer]]} -- [[sched_timer]],
[[inqueue_timer]], [[outqueue_timer]] -- fire at any time between now
and [[dmax]].  These events may occur at any time up to a specified
maximum delay.

:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[aux_timeopt]] ALL Time values for socket options

   The [[TLang]] sockets interface representation of a time is as a pair of integers,
   the first for seconds and the second for nanoseconds.
   It also uses [[(int#int) option]] representations, e.g.~in the arguments to [[setsocktopt]] and [[pselect]] and the result of [[setsocktopt]], with the [[None]] value meaning infinity.
   Internally, time is represented as a [[time]] value, either a real or infinity.
   These routines convert between the various types. Note that they allow ill-formed tltimeopts without complaint.
:*)
(* ------------------------------------------------------------------ *)


val time_of_tltime_def = Phase.phase 1 Define`(*: convert [[(sec,nsec)]] pair to real time value :*)
  (time_of_tltime : int # int -> time)
    (sec,nsec) = time (real_of_int sec + real_of_int nsec / 1000000000)
`(*:@mergewithnext:*);

val time_of_tltimeopt_def = Phase.phase 1 Define`(*: convert optional [[(sec,nsec)]] pair to real time value (where [[NONE]] mapped to [[time_infty]]) :*)
  time_of_tltimeopt  NONE     = time_infty /\
  time_of_tltimeopt (SOME sn) = time_of_tltime sn
`(*:@mergewithnext:*);

val tltimeopt_wf_def = Phase.phase 1 Define`(*: is an optional [[(sec,nsec)]] pair well-formed? :*)
  (tltimeopt_wf : (int # int) option -> bool)
                NONE             = T /\
  tltimeopt_wf (SOME (sec,nsec)) = (sec >= 0 /\ nsec >= 0 /\ nsec < 1000000000)
`(*:@mergewithnext:*);

val tltimeopt_of_time_def = Phase.phase 1 Define`(*: convert a [[time]] value to an optional [[(sec,nsec)]] pair :*)
  (tltimeopt_of_time : time -> (int # int) option) t
    = @x. tltimeopt_wf x /\ time_of_tltimeopt x = t  (*: garbage if [[t]] not nonnegative integral number of nsec :*)
`
(*:
@description
 A [[tltimeopt]] is well-formed if [[sec]] and [[nsec]] are positive
   and [[nsec]] is less than $10^9$.
:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[aux_queues]] ALL Queues

Messages are queued at various points within the implementations,
e.g.~within the network interface hardware and in the kernel.  These
queues can become full, though their "size" is not simple to describe
--- e.g.~in BSD there is some accounting of the number of mbufs used.
We model this with simple queues, for example the host message inqueue and outqueue (see [[iq]] and [[oq]], {@link [[host]]}) which have lists of messages.
These model the combination of network interface and kernel queues.
We allow them to nondetermistically be full for enqueue operations, to ensure that the specification includes all real-world traces.
This behaviour is guarded by [[INFINITE_RESOURCES]].

The nondeterminism means that queue operations must be relations, not
functions, and hence that many definitions that use them must also be
relational.

Many queues also associated with timers (see e.g.~{@link
[[inqueue_timer]]}) bounding the times within which they must next be
processed.

One might want additional properties, e.g.~(1) if a queue is empty then at least one message can be enqueued, or more
generally a specified finite lower bound on queue size;
or
(2) if a queue is full then is remains so until a message is dequeued
(perhaps only for enqueue attempts of at least the same size).
At present we see no need for the additional complication.


:*)
(* ------------------------------------------------------------------ *)

(* A nice property we might want, but don't seem to get this way, is
   that if the queue is full, it stays full until a message is
   dequeued.  (Perhaps this should only be true for the same message
   being tried again?  If it's size-bounded, and a smaller message is
   tried, it might get through even though the larger one didn't)

   No need, because it's not very interesting.  And if there are other
   processes in the system, it can be violated by their activity.
*)

(* NB: the queue models both the interface queue and the kernel's
   mbufs used on the way there *)

val enqueue_def = Phase.phase 2 Define`(*: attempt to enqueue a message :*)
  enqueue dq (Timed(q,d),msg,Timed(q',d'),queued)
    = ((INFINITE_RESOURCES ==> queued) /\
       (q',d') = (if queued then (APPEND q [msg],dq) else (q,d))
      )
`(*: @description
This is a relation between an original timed queue [[Timed(q,d)]], a message to enqueue, [[msg]], a resulting timed queue [[Timed(q',d')]], and a boolean [[queued]] indicating whether the enqueue was successful or not.  For a successful enqueue the timer on the resulting queue is set to [[dq]] :*);

val enqueue_iq_def = Phase.phase 2 Define`(*: attempt to enqueue onto the in-queue :*)
  enqueue_iq = enqueue inqueue_timer`(*: @mergewithnext :*);
val enqueue_oq_def = Phase.phase 2 Define`(*: attempt to enqueue onto the out-queue :*)
  enqueue_oq = enqueue outqueue_timer
`
(*:
@description
Add a message to the respective queue, returning the new queue and a flag
   saying whether the message was successfully queued.
:*)
;

val dequeue_def = Phase.phase 2 Define`(*: attempt to dequeue a message :*)
  dequeue dq (Timed(q,d),Timed(q',d'),msg)
    = case q of
        (msg0::q0) => q' = q0 /\ msg = SOME msg0 /\ d' = (if q0 = [] then never_timer else dq) |
        []         => q' = q  /\ msg = NONE      /\ d' = d
`(*:@mergewithnext:*);

val dequeue_iq_def = Phase.phase 1 Define`(*: attempt to dequeue from the in-queue :*)
  dequeue_iq = dequeue inqueue_timer`(*: @mergewithnext :*);
val dequeue_oq_def = Phase.phase 1 Define`(*: attempt to dequeue from the out-queue :*)
  dequeue_oq = dequeue outqueue_timer
`
(*:
@description
Remove a message from the queue, returning the new queue, and the
   message if there is one.
:*)
;

(*
   This function is fairly unnecessary at the moment; pattern matching
   could be used instead.  But it allows for future expansion or
   changing the datatype of queues.
*)

(* DON'T phase: handled by betters *)
val route_and_enqueue_oq_def = Define`(*: attempt to route and then enqueue an outgoing message :*)
  route_and_enqueue_oq (rttab,ifds,oq,msg,oq',es,arch)
    = case test_outroute (msg,rttab,ifds,arch) of
         NONE => F
       | SOME (SOME e) => oq' = oq /\ es = SOME e
       | SOME NONE => ?queued.
                         enqueue_oq (oq,msg,oq',queued) /\
                         es = if queued then NONE else SOME ENOBUFS
`
(*:
@description
 This is a relation because [[enqueue_oq]] can non-deterministically
   decide that the [[oq]] is full.
:*)
;

val enqueue_list_qinfo_def = Phase.phase 1 Define`(*: attempt to enqueue a list of messages :*)
  enqueue_list_qinfo dq (q,(msg,queued)::msgqs,q')
    = (?q0.
       enqueue            dq (q ,msg  ,q0,queued) /\
       enqueue_list_qinfo dq (q0,msgqs,q')) /\
  enqueue_list_qinfo dq (q,[],q')
    = (q' = q)
`(*:@mergewithnext:*);

val enqueue_list_def = Phase.phase 1 Define`(*: attempt to enqueue a list of messages, ignoring success flags :*)
  enqueue_list dq (q,msgs,q',queued) =
    (?msgqs.
     enqueue_list_qinfo dq (q,msgqs,q') /\
     msgs = MAP FST msgqs /\
     queued = EVERY (\x. SND x = T) msgqs)
`(*:@mergewithnext:*);

val enqueue_oq_list_qinfo_def = Phase.phase 1 Define`(*: attempt to enqueue a list of messages onto the out-queue :*)
  enqueue_oq_list_qinfo = enqueue_list_qinfo outqueue_timer`(*: @mergewithnext :*);
val enqueue_oq_list_def = Phase.phase 1 Define`(*: attempt to enqueue a list of messages onto the out-queue, ignoring success flags :*)
  enqueue_oq_list = enqueue_list outqueue_timer
`
(*:
@description
 We sometimes need to enqueue multiple messages at a time.  [[enqueue_list_qinfo]]
   tries to enqueue a list of messages, pairing each with its
   success boolean.

 Often, we don't care too much about the precise queueing success of
   each message.  [[enqueue_list]] provides the AND of success of each
   message (though this is of limited use).
:*)
;


val accept_incoming_q0_def = Phase.phase 1 Define`(*: should an incoming incomplete connection be accepted? :*)
  accept_incoming_q0 (lis:socket_listen) (b:bool)
    <=> (b <=> LENGTH lis.q < backlog_fudge lis.qlimit)
`(*: @mergewithnext :*);

val accept_incoming_q_def = Phase.phase 1 Define`(*: should an incoming completed connection be accepted? :*)
  accept_incoming_q (lis:socket_listen) (b:bool)
    <=> (b <=> LENGTH lis.q < 3 * backlog_fudge lis.qlimit DIV 2)
`(*:@mergewithnext:*);

val drop_from_q0_def = Phase.phase 1 Define`(*: drop from incomplete-connection queue? :*)
  drop_from_q0 (lis:socket_listen) (b:bool)
    = ((LENGTH lis.q0 >= TCP_Q0MINLIMIT /\ b = T) \/
       (LENGTH lis.q0 <  TCP_Q0MAXLIMIT /\ b = F))
`
(*:
@description
%
A listening socket has two queues, the incomplete connections queue
[[lis.q0]] and the completed connections queue [[lis.q]].
%
An incoming incomplete (respectively, completed) connection be
accepted onto [[lis.q0]] (respectively, [[lis.q]]) if the
relevant queue is not full.
%
Intriguingly, for FreeBSD 4.6-RELEASE, this specification  is
correct, but if syncaches were to be turned off, the condition in the
[[q0]] case would be [[LENGTH lis.q < 3 * lis.qlimit / 2]] instead.
%
Existing incomplete connections may dropped from [[lis.q0]] to make
room if its length is between its minimum and maximum limits.

:*)
;


val _ = export_theory();
