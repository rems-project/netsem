(* A HOL98 specification of TCP *)

(* Host auxiliary functions *)

(*[ RCSID "$Id: TCP1_auxFnsScript.sml,v 1.3 2005/07/19 12:24:02 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

local open TCP1_baseTypesTheory
           TCP1_utilsTheory
           TCP1_hostTypesTheory
           TCP1_paramsTheory

           containerTheory  (* for LIST_TO_SET *)
in end;

val Term = Parse.Term;

val _ = new_theory "TCP1_auxFns";

val _ = Version.registerTheory "$RCSfile: TCP1_auxFnsScript.sml,v $" "$Revision: 1.3 $" "$Date: 2005/07/19 12:24:02 $";

(*: @chapter [[TCP1_auxFns]] Auxiliary functions

This file defines a large number of auxiliary functions to the host
specification.

:*)



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
          (NETMASK m, ip n (* n has been masked by m above *)) ->
            ip (n + 2 EXP (32 - m) - 1)
    (*: Note: would be much easier if IPs were actually [[word32]] rather than [[num]] :*)
    (*: corresponds to [[INADDR_BROADCAST]] for the interface :*)
`(*:@mergewithnext:*);

val if_any_def = Phase.phase 1 Define`(*: the set of addresses in an interface's subnet :*)
  if_any (ifd0:ifd)
    = case (ifd0.netmask, mask ifd0.netmask ifd0.primary) of
          (NETMASK m, ip n (* n has been masked by m above *)) ->
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
  ifid_up ifds ifid = (ifds ' ifid).up
`(*:@mergewithnext:*);

val outroute_def = Phase.phase 1 Define`(*: compute interface to use to send to given IP, if any :*)
  outroute(i2,rttab:routing_table,ifds:ifid |-> ifd) =
    case FILTER (ifid_up ifds) (outroute_ifids(i2,rttab)) of
        []           -> NONE
     || (ifid::_987) -> SOME ifid
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
                                              SOME ifid -> { (ifds ' ifid).primary }
                                           || NONE      -> {}
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
        SOME i2 -> SOME (test_outroute_ip(i2,rttab,ifds,arch))
     || _ -> NONE
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
        (NONE, NONE) -> F
     || (NONE, SOME j) -> F
     || (SOME i, NONE) -> F
     || (SOME i, SOME j) -> in_loopback i /\ ~in_local ifds j
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
  fdlt (FD n) (FD m) = n < m
`(*: @mergewithnext :*);

val fdle_def = Phase.phase 1 Define`(*: [[<=]] comparison on file descriptors :*)
  fdle (FD n) (FD m) = n <= m
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

val sane_socket_def = Phase.phase 1 Define`(*: socket sanity invariants hold :*)
  sane_socket sock = case sock.pr of
                         TCP_PROTO tcp_sock ->
                           (*LENGTH tcp_sock.rcvq <= sock.sf.n(SO_RCVBUF) /\  (* true?? *)*)
                           LENGTH tcp_sock.rcvq <= TCP_MAXWIN << TCP_MAXWINSCALE (*/\*)
                           (*LENGTH tcp_sock.sndq <= sock.sf.n(SO_SNDBUF)     (* true?? *)*)
                       || UDP_PROTO udp_sock ->
                           T
`
(*:
@description
 There are some demonstrable invariants on a socket; this definition
 asserts them.  These are largely here to provide explicit bounds to
 the symbolic evaluator.

:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[aux_binding]] ALL Binding

Both TCP and UDP have a concept of a socket being \emph{bound} to a
local port, which means that that socket may receive datagrams
addressed to that port.  A specific local IP address may also be
specified, and a remote IP address and/or port.  This `quadruple'
(really a quintuple, since the protocol is also relevant) is used to
determine the socket that best matches an incoming datagram.

The functions in this section determine this best-matching socket,
using rules appropriate to each protocol.  Support is also provided
for determining which ports are available to be bound by a new socket,
and for automatically choosing a port to bind to in cases where the
user does not specify one.

:*)
(* ------------------------------------------------------------------ *)


(* DON'T phase: in betters *)
val bound_ports_protocol_autobind_def  = Define `(*: the set of ports currently bound by a socket for a protocol :*)
  bound_ports_protocol_autobind pr socks = {p | ?s:socket.
						 s IN FRANGE socks /\ s.ps1 = SOME p /\
                                                 proto_of s.pr = pr}
`(*:
@description
Rebinding of ports already bound is often restricted. [[bound_ports_protocol_autobind]] is a list of all ports having
a socket of the given protocol binding that port.

:*)
;



(* DON'T phase: in betters *)
val bound_port_allowed_def = Define`(*: is it permitted to bind the given (IP,port) pair? :*)
  bound_port_allowed pr socks sf arch is p =
    p NOTIN
     {port | ?s:socket.
        s IN FRANGE socks /\ s.ps1 = SOME port /\
        proto_eq s.pr pr /\
        (if bsd_arch arch /\ SO_REUSEADDR IN sf.b then
           s.is2 = NONE /\ s.is1 = is
         else if linux_arch arch /\ SO_REUSEADDR IN sf.b /\ SO_REUSEADDR IN s.sf.b /\
                 ((?tcp_sock. TCP_PROTO(tcp_sock) = s.pr /\ ~(tcp_sock.st = LISTEN)) \/
                   ?udp_sock. UDP_PROTO(udp_sock) = s.pr) then
            F (* If socket is not in LISTEN state or is a UDP socket can always rebind here *)
	 else if windows_arch arch /\ SO_REUSEADDR IN sf.b then
	    F (* can rebind any UDP address; not sure about TCP - assume the same for now *)
         else
            (is = NONE \/ s.is1 = NONE \/ (?i:ip. is = SOME i /\ s.is1 = SOME i))) }
`
(*:
@description
   This determines whether binding a socket (of protocol [[pr]]) to local address [[is,p]] is
   permitted, by considering the other bound sockets on the host and the
   state of the sockets' [[SO_REUSEADDR]] flags.
   Note: SB believes this definition is correct for TCP and UDP on BSD
   and Linux through exhaustive manual verification.
   Note: WinXP is still to be checked.
:*)
;

(* old bound_ports_protocol and bound_ipports_protocol removed;
OBSELETED by bound_port_allowed.  See CVS, v1.166 and before *)

val autobind_def = Phase.phase 1 Define`(*: set of ports available for autobinding :*)
  autobind(SOME p,_,_) = {p} /\
  autobind(NONE,pr,socks) = ephemeral_ports DIFF (bound_ports_protocol_autobind pr socks)
`
(*:
@description
Note that [[SO_REUSEADDR]] is not considered when choosing a port to
autobind to.

:*);

val bound_after_def = Phase.phase 1 Define `(*: was [[sid]] bound more recently than [[sid']]? :*)
  bound_after sid sid' [] = ASSERTION_FAILURE "bound_after" (* should never reach this case *) /\
  bound_after sid sid' (sid0::bound) =
    if sid = sid0 then T  (* newly-bound sockets are added to the head *)
    else if sid' = sid0 then F
	else bound_after sid sid' bound
`(*:@mergewithnext:*);

val match_score_def =
  Phase.phase 1  Define`(*: score the match against the given pattern of the given quadruple :*)
    (match_score (_,NONE,_,_) _ = 0n) /\
    (match_score (NONE, SOME p1, NONE, NONE) (i3,ps3,i4,ps4) =
       if ps4 = SOME p1 then 1 else 0) /\
    (match_score (SOME i1, SOME p1, NONE, NONE) (i3,ps3,i4,ps4) =
       if (i1 = i4) /\ (SOME p1 = ps4) then 2 else 0) /\
    (match_score (SOME i1, SOME p1, SOME i2, NONE) (i3,ps3,i4,ps4) =
       if (i2 = i3) /\ (i1 = i4) /\ (SOME p1 = ps4) then 3 else 0) /\
    (match_score (SOME i1, SOME p1, SOME i2, SOME p2) (i3,ps3,i4,ps4) =
       if (SOME p2 = ps3) /\ (i2 = i3) /\ (i1 = i4) /\ (SOME p1 = ps4) then 4
       else 0)
`
(*:
@description
These two functions are used to match an incoming UDP datagram to a
socket. The [[bound_after]] function returns [[T]] if the socket
[[sid]] (the first agrument) was bound after the socket [[sid']] (the
second argument) according to a list of bound sockets (the third
argument).

The [[match_score]] function gives a score specifying how closely two
address quads, one from a socket and one from a datagram, correspond;
a higher score indicates a more specific match.

:*)
;

val lookup_udp_def = Phase.phase 2 Define `(*: the set of sockets matching an address quad, for UDP :*)
  lookup_udp socks quad bound arch =
           { sid | sid IN FDOM socks /\
	           let s = socks ' sid in
		   let sn = match_score (s.is1,s.ps1,s.is2,s.ps2) quad in
		       sn > 0 /\
		       if windows_arch arch  then
			   if sn = 1 then
			       ~(? (sid',s') :: (socks \\ sid). match_score (s'.is1,s'.ps1,s'.is2,s'.ps2) quad > sn)
			   else T
		       else
			   ~(?(sid',s') :: (socks \\ sid).
				       (match_score (s'.is1,s'.ps1,s'.is2,s'.ps2) quad > sn \/
					(linux_arch arch /\ match_score (s'.is1,s'.ps1,s'.is2,s'.ps2) quad = sn /\
                                         bound_after sid' sid bound))) }
`
(*:

@description
This function returns a set of UDP sockets which the datagram with
address quad [[quad]] may be delivered to. For FreeBSD and Linux there
is only one such socket; for WinXP there may be multiple.

For each socket in the finite map of sockets [[socks]], the score,
[[sn]], of the matching of the socket's address quad and [[quad]] is
computed using {@link [[match_score]]}.

@variation FreeBSD

For FreeBSD, the set contains the sockets for which  the score is greater than zero and there is no other
socket in [[socks]] with a higher score.

@variation Linux

For Linux, the set contains the sockets for which the score is greater than zero, there are no sockets
with a higher score, and the socket was bound to its local port after
all the other sockets with the same score.

@variation WinXP

For WinXP, the set contains all the sockets with score greater than one and also the sockets for which the score is one, [[sn=1]], and there are no sockets
with greater scores.

:*);

val tcp_socket_best_match_def = Phase.phase 2 Define `(*: the set of sockets matching a quad, for TCP :*)
  tcp_socket_best_match (socks : sid |-> socket) (sid,sock) (seg : tcpSegment) arch =
    (* is the socket sid the best match for segment seg? *)
    let s = sock in
    let score = match_score (s.is1, s.ps1, s.is2, s.ps2)
                            (THE seg.is1, seg.ps1, THE seg.is2, seg.ps2) in
    ~(?(sid',s') :: socks \\ sid.
                match_score (s'.is1, s'.ps1, s'.is2, s'.ps2)
                            (THE seg.is1, seg.ps1, THE seg.is2, seg.ps2) > score)
`
(*:

 @description
 This function determines whether a given socket [[sid]] is the best match for a
 received TCP segment [[seg]].

 The score (obtained using {@link [[match_score]]}) for the given
 socket is determined, and compared with the score for each other
 socket in [[socks]].  If none have a greater score, this is the best
 match and true is returned; otherwise, false is returned.

:*);

val lookup_icmp_def = Phase.phase 2 Define `(*: the set of sockets matching a quad, for ICMP :*)
  lookup_icmp socks icmp arch bound =
       { sid0 | ? (sid,sock) :: socks.
	       sock.ps1 = icmp.ps3 /\ proto_of sock.pr = icmp.proto /\ sid0 = sid /\
	       if windows_arch arch then T
               else
		   sock.is1 = icmp.is3 /\ sock.is2 = icmp.is4 /\
                   (sock.ps2 = icmp.ps4 \/
                    (linux_arch arch /\
		     proto_of sock.pr = PROTO_UDP /\ sock.ps2 = NONE /\
		     ~(? (sid',s) :: (socks \\ sid).
		     	     s.is1 = icmp.is3 /\ s.is2 = icmp.is4 /\
		     	     s.ps1 = icmp.ps3 /\ s.ps2 = icmp.ps4 /\
		     	     proto_of s.pr = icmp.proto /\
		     	     bound_after sid' sid bound)
                    )) }
`(*:

  @description

  This function returns the set of sockets matching a received ICMP
  datagram [[icmp]].

  An ICMP datagram contains the initial portion of the header of the
  original message to which it is a response.  For a socket to match,
  it must at least be bound to the same port and protocol as the
  source of the original message.  Beyond this, architectures differ.
  Usually, the socket must be connected, and connected to the same
  port as the original destination; and the source and destination IP
  addresses must agree.

  @variation WinXP

  For Windows, the socket need not be connected, and the source and
  destination IP addresses need not agree; an ICMP is delivered to
  one socket bound to the same port and protocol as the original
  source.

  @variation Linux

  For Linux, UDP ICMPs may also be delivered to unconnected sockets,
  as long as no matching connected socket was bound more recently than
  that socket.

  @variation FreeBSD

  For FreeBSD, the behaviour is as described above.


:*);



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
        (msg0::q0) -> q' = q0 /\ msg = SOME msg0 /\ d' = (if q0 = [] then never_timer else dq) ||
        []         -> q' = q  /\ msg = NONE      /\ d' = d
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
         NONE -> F
      || SOME (SOME e) -> oq' = oq /\ es = SOME e
      || SOME NONE -> ?queued.
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
    = (b = LENGTH lis.q < backlog_fudge lis.qlimit)
`(*: @mergewithnext :*);

val accept_incoming_q_def = Phase.phase 1 Define`(*: should an incoming completed connection be accepted? :*)
  accept_incoming_q (lis:socket_listen) (b:bool)
    = (b = LENGTH lis.q < 3 * backlog_fudge lis.qlimit DIV 2)
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

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[misc_aux]] TCP TCP Options

TCP option handling.

     :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)



(* ----------------------------------------------------------- *)
(* WARNING: the two definitions following must be kept in sync *)
(* ----------------------------------------------------------- *)


(* Don't phase: handled in testEval *)
(* X
val do_tcp_options_def = Define`
(*: Constrain the TCP timestamp option values that appear in an outgoing segment :*)
  do_tcp_options cb_tf_doing_tstmp cb_ts_recent cb_ts_val  =
    if cb_tf_doing_tstmp then
       let ts_ecr' = option_case (ts_seq 0w) I (timewindow_val_of cb_ts_recent) in
           SOME(cb_ts_val,ts_ecr')
     else
         NONE
`;
X *)


val calculate_tcp_options_len_def =  Phase.phase 1 Define`
(*: Calculate the length consumed by the TCP options in a real TCP segment :*)
  calculate_tcp_options_len cb_tf_doing_tstmp =
    if cb_tf_doing_tstmp then 12 else 0 : num
`
(*: @description
This calculation omits
   window-scaling and mss options as these only appear in SYN segments during connection setup.
%
   The total length consumed by all options will always be a multiple of 4 bytes due to padding.
   If more TCP options were added to the model, the space consumed by options would be
   architecture/options/alignment/padding dependent.
:*);

(*:
 @section [[aux_buffers]] ALL Buffers, windows, and queues

Various functions that compute buffer sizes, window sizes, and
remaining send queue space.  Some of these computations are
architecture-specific.

:*)

(* Don't Phase: handled by testEval *)
val calculate_buf_sizes_def = Define`
(*: Calculate buffer sizes for [[rcvbufsize]], [[sndbufsize]], [[t_maxseg]], and [[snd_cwnd]]
:*)
  calculate_buf_sizes cb_t_maxseg seg_mss (* X bw_delay_product_for_rt X *) is_local_conn
                      rcvbufsize sndbufsize cb_tf_doing_tstmp arch (rcvbufsize',sndbufsize',t_maxseg') =

    let t_maxseg'' =
      (*: TCPv2p901 claims min 32 for "sanity"; FreeBSD4.6 has 64 in |tcp_mss()|.
         BSD has the route MTU if avail, or [[MIN MSSDFLT (link MTU)]] otherwise, as the first argument
         of the MIN below.  That is the same calculation as we did in [[connect_1]]. We don't repeat it,
         but use the cached value in [[cb.t_maxseg]]. :*)
      let maxseg = (MIN cb_t_maxseg (MAX 64 (option_case MSSDFLT I seg_mss))) in
          if linux_arch arch then
            maxseg
          else
            (*: BSD subtracts the size consumed by options in the TCP
            header post connection establishment. The WinXP and Linux
            behaviour has not been fully tested but it appears Linux
            does not do this and WinXP does. :*)
            maxseg - (calculate_tcp_options_len cb_tf_doing_tstmp)
    in
    (*: round down to multiple of cluster size if larger (as BSD).
    From BSD code; assuming true for WinXP for now :*)
    let t_maxseg''' = if linux_arch arch then t_maxseg''  (* from tests *)
                     else rounddown MCLBYTES t_maxseg'' in

    (* buffootle: rcv *)
    choose rcvbufsize'' :: UNIV. (* X option_case rcvbufsize I bw_delay_product_for_rt in X *)
    let (rcvbufsize''',t_maxseg'''') = (if rcvbufsize'' < t_maxseg'''
                                     then (rcvbufsize'',rcvbufsize'')
                                     else (MIN SB_MAX (roundup t_maxseg''' rcvbufsize''),
                                           t_maxseg''')) in

    (* buffootle: snd *)
    choose sndbufsize'' :: UNIV. (* X = option_case sndbufsize I bw_delay_product_for_rt in X *)
    let sndbufsize''' = (if sndbufsize'' < t_maxseg''''
                        then sndbufsize''
                        else MIN SB_MAX (roundup t_maxseg''' sndbufsize'')) in

    (* compute initial cwnd *)
    (* X let snd_cwnd = t_maxseg''' * (if is_local_conn then SS_FLTSZ_LOCAL else SS_FLTSZ) in X *)
    (rcvbufsize',sndbufsize',t_maxseg') = (rcvbufsize''',sndbufsize''',t_maxseg''''(* X, snd_cwnd X *))
`
(*: @description
Used in [[deliver_in_1]] and [[deliver_in_2]]. :*)
;

val calculate_bsd_rcv_wnd = Phase.phase 1 Define`
(*:  Calculation of [[rcv_wnd]] :*)
  calculate_bsd_rcv_wnd sf tcp_sock =
    MAX (Num (tcp_sock.cb.rcv_adv - tcp_sock.cb.rcv_nxt))
        (sf.n(SO_RCVBUF) - LENGTH tcp_sock.rcvq)
`(*: @description
 Calculation of [[rcv_wnd]] as done in BSD's |tcp_input.c|, line 1052. The model currently calls this from
   [[tcp_output_really]] in post-ESTABLISHED states, using [[deliver_in_3]] to update [[rcv_wnd]] as
   soon as a segment comes, rather than waiting for the next [[deliver_in]], as BSD does --- this
   is a saner thing to do. In order to comply with BSD however, we need [[calculate_bsd_rcv]]
   to be called on receipt of the first 'real' (i.e. non-syncache) segment, to update [[rcv_wnd]]
   from the temporary initial value.
:*);



val send_queue_space_def = Phase.phase 1 Define `
    send_queue_space (sndq_max : num) sndq_size oob arch maxseg i2 =
       { n | if bsd_arch arch then
	        n <= (sndq_max - sndq_size) + (if oob then oob_extra_sndbuf else 0)
	     else if linux_arch arch then
		 (if in_loopback i2 then
		      n = maxseg + ((sndq_max - sndq_size) DIV 16816) * maxseg
		  else
		      n = (2 * maxseg) + ((sndq_max - sndq_size - 1890) DIV 1888) * maxseg)
	     else n >= 0 }
`
(*:
 @description
   Calculation of the usable send queue space.

   FreeBSD calculates send buffer space based on the byte-count size and
   max, and the number and max of mbufs. As we do not model mbuf usage precisely we are somewhat nondeterministic
   here.

   Linux calculates it based on the MSS: the space is some multiple of
   the MSS; the number of bytes for each MSS-sized segment is the
   MSS+overhead where overhead is 420+(20 if using IP), which is why
   the i2 argument is needed.

   Windows is very strange.  Leaving it completely unconstrained is not
   what actually happens, but more investigation is needed in future to determine the actual behaviour.

 :*) ;


(* ------------------------------------------------------------------ *)
(*:
@section [[aux_bandlim]] ALL Band limiting

The rate of emission of certain TCP and ICMP responses from a host is
often controlled by a bandwidth limiter.  This limits resource usage
in the event of some error conditions, and also defends against
certain denial-of-service attacks.

Responses that may be bandlimited are grouped into categories
([[bandlim_reason]]), and bandlimiting is applied to each category
separately.  Bandlimiting is applied across the entire host, not per
socket or process.  There are a range of different schemes that may be
used, from none at all, through limiting the number of packets in any
given second, to a decaying average tuned to limit bursts and
sustained throughput differently.  We provide specifications for the
first two.

:*)
(* ------------------------------------------------------------------ *)

val bandlim_state_init_def = Phase.phase 1 Define`(*: initial state of bandlimiter :*)
  bandlim_state_init = [] : bandlim_state
`(*:@mergewithnext:*);

val bandlim_rst_ok_always_def = Phase.phase 1 Define`(*: the trivial 'always OK' bandlimiter :*)
  (bandlim_rst_ok_always : tcpSegment # ts_seq # bandlim_reason # bandlim_state -> bool # bandlim_state)
        (seg,ticks,reason,bndlm)
        = let bndlm' = (seg,ticks,reason)::bndlm
          in
          (T,bndlm')
`(*:@mergewithnext:*);

val simple_limit_def = Phase.phase 1 Define`(*: simple-bandlimiter rate settings :*)
  (simple_limit : bandlim_reason -> num option)
                BANDLIM_UNLIMITED      = NONE /\
  simple_limit BANDLIM_RST_CLOSEDPORT = SOME 200 /\
  simple_limit BANDLIM_RST_OPENPORT   = SOME 200
`(*:@mergewithnext:*);

val bandlim_rst_ok_simple_def = Phase.phase 1 Define`(*: a simple rate-limiting bandlimiter :*)
  (bandlim_rst_ok_simple : tcpSegment # ts_seq # bandlim_reason # bandlim_state -> bool # bandlim_state)
                  (seg,ticks,reason,bndlm)
     = let reasoneq = (\ r0. \ (s,t,r). r = r0)
       and ticksgt  = (\ t0. \ (s,t,r). t > t0)
       in
       let count = LENGTH (FILTER (reasoneq reason) (TAKEWHILE (ticksgt (ticks - num_floor (1 * HZ))) bndlm))
       in
       ((case simple_limit reason of
            NONE   -> T
         || SOME n -> count < n),
        (seg,ticks,reason)::bndlm)
`
(*:
@description
 Simple bandlimiter: limit number of ICMPs in the last second to the listed value.  This is based roughly on the BSD behaviour, save that for BSD it is "since the
   last second" not "in the last second".
:*)
;

val bandlim_rst_ok_def = Phase.phase 1 Define`(*: the bandlimiter actually used :*)
bandlim_rst_ok = bandlim_rst_ok_simple
`
(*:
@description
 Which band limiter to use?
:*)
;

(* TODO: think: should bandlim_rst_ok be a function or a relation?  currently function. *)


val enqueue_oq_bndlim_rst_def = Phase.phase 1 Define`(*: enqueue onto out-queue if allowed by bandlimiter :*)
  enqueue_oq_bndlim_rst(oq,seg,ticks,reason,bndlm,oq',bndlm',queued_or_dropped)
    = let (emit,bndlm0) = bandlim_rst_ok(seg,ticks,reason,bndlm)
      in
      bndlm' = bndlm0 /\
      if emit then
        enqueue_oq(oq,TCP seg,oq',queued_or_dropped)
      else
        (oq' = oq /\ queued_or_dropped = T)
`(*:
@description
For convenience, combine enqueueing and bandlimiting into a single function.

:*);



(* ------------------------------------------------------------------ *)
(*:
@section [[aux_udp]] UDP UDP support

Performing a UDP send, filling in required details as necessary.

:*)
(* ------------------------------------------------------------------ *)

val dosend_def =
  Phase.phase 1 Define`(*: do a UDP send, filling in source address and port as necessary :*)
   (dosend (ifds, rttab, (NONE, data), (SOME i1, SOME p1, SOME i2, ps2), oq, oq', ok) =
      enqueue_oq(oq,UDP(<| is1 := SOME i1; is2 := SOME i2;
			   ps1 := SOME p1; ps2 := ps2;
			   data := data |>),
		 oq',ok)) /\
   (dosend (ifds, rttab, (SOME(i,p), data), (NONE, SOME p1, NONE, NONE), oq, oq', ok) =
      (?i1'.enqueue_oq(oq,UDP(<| is1 := SOME i1'; is2 := SOME i;
		   	         ps1 := SOME p1;  ps2 := SOME p;
			         data := data |>),
		       oq',ok) /\ i1' IN auto_outroute(i,NONE,rttab,ifds))) /\
   (dosend (ifds, rttab, (SOME(i,p), data),(SOME i1, SOME p1, is2, ps2), oq, oq', ok) =
      enqueue_oq(oq,UDP(<| is1 := SOME i1; is2 := SOME i;
			   ps1 := SOME p1; ps2 := SOME p;
			   data := data |>),
		 oq',ok))`
(*:
@description
 For use in UDP [[sendto()]].
:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[aux_tcptime]] TCP TCP timing and RTT

TCP performs repeated transmissions in three situations:
retransmission of unacknowledged data, retransmission of an
unacknowledged SYN, and probing a closed window (`persisting').  In
each case the interval between transmissions is a function of the
estimated round-trip time for the connection, and is exponentially
backed off if no response is received.  The RTT estimate indicates
when TCP should expect a reply, and the exponential backoff controls
TCP's resource usage.

:*)
(* ------------------------------------------------------------------ *)

val tcp_backoffs_def = Phase.phase 1 Define`(*: select this architecture's retransmit backoff list :*)
  tcp_backoffs (arch: arch) =
    if bsd_arch arch then TCP_BSD_BACKOFFS
    else if linux_arch arch then TCP_LINUX_BACKOFFS
    else if windows_arch arch then TCP_WINXP_BACKOFFS
    else TCP_BSD_BACKOFFS (* default to BSD *)
`(*:@mergewithnext:*);

val tcp_syn_backoffs_def = Phase.phase 1 Define`(*: select this architecture's [[SYN]]-retransmit backoff list :*)
  tcp_syn_backoffs (arch: arch) =
    if bsd_arch arch then TCP_SYN_BSD_BACKOFFS
    else if linux_arch arch then TCP_SYN_LINUX_BACKOFFS
    else if windows_arch arch then TCP_SYN_WINXP_BACKOFFS
    else TCP_SYN_BSD_BACKOFFS (* default to BSD *)
`;

val mode_of_def = Phase.phase 1 Define`(*: obtain the mode of a backoff timer :*)
  (mode_of : (rexmtmode # num) timed option -> rexmtmode option)
          (SOME (Timed((mode,_),_))) = SOME mode /\
  mode_of  NONE                      = NONE
`(*:@mergewithnext:*);

val shift_of_def = Phase.phase 1 Define`(*: obtain the shift of a backoff timer :*)
  shift_of (SOME (Timed((_,shift),_))) = shift
`
(*:
@description
 TCP exponential-backoff timers are represented as [[(rexmtmode # num) timed option]],
   where [[mode : rexmtmode]] is the current TCP output mode (see {@link [[rexmtmode]]}), and
   [[shift : num]] is the 0-origin index into the backoff list of the
   interval \emph{currently underway}.
:*)
;

(* X
val computed_rto_def = Phase.phase 2 Define`(*: compute retransmit timeout to use :*)
  computed_rto (backoffs:num list) (shift:num) (* X (ri:rttinf) X *) (n:real)
    = T (* X real_of_num (EL shift backoffs) *
      MAX ri.t_rttmin (ri.t_srtt     + 4 * ri.t_rttvar) X *)
`(*:@mergewithnext:*);
X *)

val computed_rxtcur_def = Define`(*: compute the last-used [[rxtcur]] :*)
  computed_rxtcur (* X (ri:rttinf) X *) (arch: arch) (rxtcur:real)
    = T (* X MAX ri.t_rttmin
          (MIN (THE TCPTV_REXMTMAX)
               (computed_rto (if ri.t_wassyn then tcp_syn_backoffs arch
                              else tcp_backoffs arch)
                              ri.t_lastshift ri)) X *)
(* X perhaps want to write (rxtcur <= THE (TCPTV_REXMTMAX:time)) but we have removed TCPTV_REXMTMAX from Spec2.TCP1_params X*)
`
(*:
@description

 [[computed_rto]] computes the retransmit timeout to be used, from the
 backoff list, the shift, and the current RTT estimators.  The base
 time is $\mathit{RTT} + 4\mathit{RTTVAR}$; this is clipped against a
 minimum value, and then multiplied by the value from the backoff
 list.

 [[computed_rxtcur]] is not used in constructing timers, but
 [[tcp_output]] uses it to check if TCP has been idle for a while
 (causing slow start to be entered again).  It is an approximation to
 the value actually used below.  Note it might be possible to make
 this precise rather than an approximation; also, [[computed_rxmtcur]]
 and [[start_tt_rexmt_gen]] could be merged.

 Note: [[TCPTV_REXMTMAX]] had better not be infinite!

:*)
;

val start_tt_rexmt_gen_def = Phase.phase 2 Define`(*: construct retransmit timer (generic) :*)
  start_tt_rexmt_gen (mode:rexmtmode) (backoffs:num list) (shift:num) (wantmin:bool) (* X (ri:rttinf) X *) timer
    = choose rxtcur :: UNIV. (* X = MAX (if wantmin
                        then MAX ri.t_rttmin (ri.t_lastrtt + 2/HZ)
                        else ri.t_rttmin)
                       (MIN (THE TCPTV_REXMTMAX (* better not be infinite! *) )
                            (computed_rto backoffs shift ri)
                       )
      in X *)
      timer = SOME (Timed((mode,shift),slow_timer (time rxtcur)))
`(*:@mergewithnext:*);

val start_tt_rexmt_def = Phase.phase 1 Define`(*: construct normal retransmit timer :*)
  start_tt_rexmt (arch: arch) = start_tt_rexmt_gen Rexmt (tcp_backoffs arch)
`(*:@mergewithnext:*);

val start_tt_rexmtsyn_def = Phase.phase 1 Define`(*: construct [[SYN]]-retransmit timer :*)
  start_tt_rexmtsyn (arch: arch) = start_tt_rexmt_gen RexmtSyn (tcp_syn_backoffs arch)
`(*:@mergewithnext:*);

val start_tt_persist_def = Phase.phase 2 Define`(*: construct persist timer :*)
  start_tt_persist (shift:num) (* X (ri:rttinf) X *) (arch: arch) timer
    = choose cur :: {t| THE TCPTV_PERSMIN <= t /\ t <= THE TCPTV_PERSMAX}. (* X = MAX (THE TCPTV_PERSMIN (* better not be infinite! *) )
                    (MIN (THE TCPTV_PERSMAX (* better not be infinite! *) )
                         (computed_rto (tcp_backoffs arch) shift (* X ri X *) )
                    )
      in X *)
      timer = SOME (Timed((Persist,shift),slow_timer (time cur)))
`
(*:
@description

 Starting the retransmit, [[SYN]]-retransmit, and persist timers:
   these function return the new timer with the given shift.  This
   models both initialisation on receiving a segment, and update in
   the retransmit timer handler.

 There are two alternative clipping values used for the minimum timer.
 [[ri.t_rttmin]] is used always, but in one place [[t.last_rtt+2/HZ]]
 (i.e., 0.02s plus the last measured RTT) is used as well.  The BSD
 sources have a comment here saying "minimum feasible timer"; it is a
 puzzle why this value is not used elsewhere also.  (tcp\_input.c:2408
 vs tcp\_timer.c:394, tcp\_input.c:2542).

  Starting the persist timer is similar to starting the retransmit
  timers, but the bounds are different.

 Note that we don't need to look at [[tf_srttvalid]], since in any case
   [[t_srtt]] and [[t_rttvar]] will have sensible values.  That flag is just
   for the benefit of [[update_rtt]].

:*)
;

(* X
val update_rtt_def = Phase.phase 1 Define`(*: update RTT estimators from new measurement :*)
  update_rtt (rtt:duration) (ri:rttinf)
    = let (t_srtt',t_rttvar')
        = (if ri.tf_srtt_valid then
             let delta     = (rtt - 1/HZ) - ri.t_srtt
             in
             let vardelta  = abs delta - ri.t_rttvar
             in
             let t_srtt'   = MAX (1/(32*HZ)) (ri.t_srtt + (1/8) * delta)
             and t_rttvar' = MAX (1/(16*HZ)) (ri.t_rttvar + (1/4) * vardelta)
                 (* BSD behaviour is never to let these go to zero,
                    but clip at the least positive value.  Since SRTT
                    is measured in 1/32 tick and RTTVAR in 1/16 tick,
                    these are the minimum values.  A more natural
                    implementation would clip these to zero. *)
             in
             (t_srtt',t_rttvar')
           else
             let t_srtt' = rtt
             and t_rttvar' = rtt / 2
             in
             (t_srtt',t_rttvar'))
      in
      ri with <| t_rttupdated  := ri.t_rttupdated + 1;
                 tf_srtt_valid := T;
                 t_srtt        := t_srtt';
                 t_rttvar      := t_rttvar';
                 t_lastrtt     := rtt;
                 t_lastshift   := 0;
                 t_wassyn      := F  (* if t_lastshift=0, this doesn't make a difference *)
                 (* t_softerror, t_rttseg, and t_rxtcur must be handled by the caller *)
              |>
`
(*:
@description
 Update the round trip time estimators on obtaining a new instantaneous value.
 Based on a close reading of tcp\_xmit\_timer(), tcp\_input.c:2347-2419.
:*)
;


(* -------------------------------------------------- *)
(*                WINDOW CALCULATION                  *)
(* -------------------------------------------------- *)

val expand_cwnd_def = Phase.phase 1 Define`(*: expand congestion window :*)
  expand_cwnd ssthresh maxseg maxwin cwnd
    = MIN maxwin (cwnd + (if cwnd > ssthresh then (maxseg * maxseg) DIV cwnd else maxseg))
`
(*:
@description

 Congestion window expansion is linear or exponential depending on the
 current threshold [[ssthresh]].

:*)
;
X *)


(* ------------------------------------------------------------------ *)
(*:
@section [[aux_pmtu]] TCP Path MTU Discovery

For efficiency and reliability, it is best to send datagrams that do
not need to be fragmented in the network.  However, TCP has direct
access only to the maximum packet size (MTU) for the interfaces at
either end of the connection -- it has no information about routers
and links in between.

To determine the MTU for the entire path, TCP marks all datagrams `do
not fragment'.  It begins by sending a large datagram; if it receives
a `fragmentation needed' ICMP in return it reduces the size of the
datagram and repeats the process.  Most modern routers include the
link MTU in the ICMP message; if the message does not contain an MTU,
however, TCP uses the next lower MTU in the table below.

:*)
(* ------------------------------------------------------------------ *)


val next_smaller_def = Phase.phase 1 Define`(*: find next-smaller element of a set :*)
  (next_smaller:(num->bool) -> num -> num) xs y = @x::xs. x < y /\ !x'::xs. x' > x ==> x' >= y
`(*:@mergewithnext:*);

val mtu_tab_def = Phase.phase 1 Define`(*: path MTU plateaus to try :*)
  mtu_tab arch = if linux_arch arch then
                     {32000; 17914; 8166; 4352; 2002; 1492; 576; 296; 216; 128; 68} : num set
                 else
                     {65535; 32000; 17914; 8166; 4352; 2002; 1492; 1006; 508; 296; 68}
`
(*:
@description
 MTUs to guess for path MTU discovery.  This table is from RFC1191,
   and is the one that appears in BSD.

   On |comp.protocols.tcp-ip, Sun, 15 Feb 2004 01:38:26 -0000,
   <102tjcifv6vgm02@corp.supernews.com>, kml@bayarea.net (Kevin Lahey)|
   suggests that this is out-of-date, and 2312 (WiFi 802.11), 9180
   (common ATM), and 9000 (jumbo Ethernet) should be added.  For some
   polemic discussion, see |http://www.psc.edu/~mathis/MTU/|.

   RFC1191 says explicitly "We do not expect that the values in the
   table [...] are going to be valid forever.  The values given here
   are an implementation suggestion, NOT a specification or
   requirement.  Implementors should use up-to-date references to pick
   a set of plateaus [...]".  BSD is therefore not compliant here.

   Linux adds 576, 216, 128 and drops 1006.  576 is used in X.25
   networks, and the source says 216 and 128 are needed for AMPRnet
   AX.25 paths.  1006 is used for SLIP, and was used on the ARPANET.
   Linux does not include the modern MTUs listed above.

:*)
;


(* ------------------------------------------------------------------ *)
(*:
@section [[aux_reass]] TCP Reassembly

TCP segments may arrive out-of-order, leaving holes in the data
stream.  They may also overlap, due to retransmission, confusion, or
deliberate effort by an unusual TCP implementation.  The TCP
reassembly algorithm is responsible for retrieving the data stream
from the segments that arrive (note this is not to be confused with IP
fragmentation reassembly, which is beneath the scope of this
specification).

There are various ways of resolving overlaps; in this specification we
are completely nondeterministic, and allow any legal reassembly.

:*)
(* ------------------------------------------------------------------ *)

(* DON'T phase: handled by betters *)
val tcp_reass_def = Define`(*: perform TCP segment reassembly :*)
  tcp_reass seq (rsegq : tcpReassSegment list) =
     let myrel = { (i,c) | ?rseg.
                              rseg IN' rsegq /\
                              i >= rseg.seq /\
                              i < rseg.seq + LENGTH rseg.data +
                                    (if rseg.spliced_urp <> NONE then 1 else 0) /\
                              (case rseg.spliced_urp of
                                 SOME(n) ->
                                   (if i > n then
                                     c = SOME(EL (Num (i - rseg.seq - 1)) (rseg.data))
                                    else if i = n then
                                     c = NONE
                                    else
                                     c = SOME(EL (Num (i - rseg.seq)) (rseg.data))) ||
                                 NONE ->
                                     c = SOME(EL (Num (i - rseg.seq)) (rseg.data))) } in
     { (cs',len,FIN) | ?cs. cs' = CONCAT_OPTIONAL cs /\
                   (!n:num. n < LENGTH cs ==> (seq+n,EL n cs) IN myrel) /\
                   (~?c. (seq+LENGTH cs,c) IN myrel) /\
                   (len = LENGTH cs) /\
                   (FIN = ?rseg. rseg IN' rsegq /\
                                 rseg.seq + LENGTH rseg.data +
                                   (if rseg.spliced_urp <> NONE then 1 else 0) =
                                     seq + LENGTH cs /\
	  	                 rseg.FIN ) }

         (* NB: the FIN may come from a 0-length segment, or from a
         different segment from that which the last character came but logically is
         always at the end of cs's. *)
`
(*:
@description
 Returns the set of maximal-length strings starting at [[seq]] that can
   be constructed by taking bytes from the segments in [[rsegq]], accounting for
   any spliced (out-of-line) urgent data.
:*)
;

(*

  -=-=-
  SB: WARNING!! WARNING!! This is no longer correct following my
  addition of correct urgent data splicing to tcp_reass and
  tcp_reass_prune. Don't have the time or the inclination to fix this!
  -=-=-

  For your amusement, here is a possible OCaml rendering of the above,
  as a function.  Not guaranteed to be equivalent.

    type seqno = int

    type rseg = { seq  : seqno;
                  data : char list;
                  fin  : bool }

    let rec tcp_reass0 : rseg list -> seqno -> char list list -> char list list * bool list
      = fun rsegq seq css
     -> let rec dat rsegs cs
          = match rsegs with
              []            -> cs
            | (rseg::rsegs) -> dat rsegs (if rseg.seq <= seq
                                             && seq < rseg.seq + List.length rseg.data
                                          then
                                             (List.nth rseg.data (seq - rseg.seq)) :: cs
                                          else
                                             cs)
        in
        let rec fin rsegs bs
          = match rsegs with
              [] -> bs
            | (rseg::rsegs) -> fin rsegs (if seq = rseg.seq + List.length rseg.data
                                          then
                                             rseg.fin :: bs
                                          else
                                             bs)
        in
        match dat rsegq [] with
          []           -> (List.rev css,fin rsegq [])
        | (_::_) as cs -> tcp_reass0 rsegq (seq+1) (cs::css)

    let tcp_reass rsegq seq = tcp_reass0 rsegq seq []

*)

val tcp_reass_prune_def = Phase.phase 1 Define`(*: drop prefix of reassembly queue :*)
  tcp_reass_prune seq (rsegq : tcpReassSegment list) =
    FILTER (\rseg. rseg.seq + LENGTH rseg.data + (if rseg.spliced_urp <> NONE then 1 else 0) +
                     (if rseg.FIN then 1 else 0) > seq) rsegq
`
(*:
@description
 Prune away every segment ending before the specified [[seq]], accounting for
   any spliced (out-of-line) urgent data.
:*)
;



(* ------------------------------------------------------------------ *)
(*:
@section [[initial_cb]] TCP The initial TCP control block

The initial state of the TCP control block.

:*)
(* ------------------------------------------------------------------ *)


(* the all-bits-zero TCPCB, i.e., bzero(), as updated by tcp_newtcpcb *)
(* Don't Phase: handled specially by testEval *)
val initial_cb_def = Define`
  initial_cb =
    <| t_segq            := [];
       tt_rexmt          := NONE;
       tt_keep           := NONE;
       tt_2msl           := NONE;
(* X        tt_delack         := NONE; X *)
       tt_conn_est       := NONE;
       tt_fin_wait_2     := NONE;
       tf_needfin        := F;
       tf_shouldacknow   := F;
       snd_una           := tcp_seq_local 0w;
       snd_max           := tcp_seq_local 0w;
       snd_nxt           := tcp_seq_local 0w;
       snd_wl1           := tcp_seq_foreign 0w;
       snd_wl2           := tcp_seq_local 0w;
       iss               := tcp_seq_local 0w;
       snd_wnd           := 0;
(* X       snd_cwnd          := TCP_MAXWIN << TCP_MAXWINSCALE;
       snd_ssthresh      := TCP_MAXWIN << TCP_MAXWINSCALE; X *)
       rcv_wnd           := 0;
       tf_rxwin0sent     := F;
       rcv_nxt           := tcp_seq_foreign 0w;
       rcv_up            := tcp_seq_foreign 0w;
       irs               := tcp_seq_foreign 0w;
       rcv_adv           := tcp_seq_foreign 0w;
(*       snd_recover       := tcp_seq_local 0w; *)
       t_maxseg          := MSSDFLT;
       t_advmss          := NONE;
(* X       t_rttseg          := NONE;
       t_rttinf :=
       <|
         t_rttupdated      := 0;
         tf_srtt_valid     := F;
         t_srtt            := TCPTV_RTOBASE;
         t_rttvar          := TCPTV_RTTVARBASE;
         t_rttmin          := TCPTV_MIN;
         t_lastrtt         := 0;
         t_lastshift       := 0;
         t_wassyn          := F  (* if t_lastshift=0, this doesn't make a difference *)
       |>;
       t_dupacks         := 0; X *)
       t_idletime        := stopwatch_zero;
       t_softerror       := NONE;
       snd_scale         := 0;
       rcv_scale         := 0;
       request_r_scale   := NONE; (* this like many other things is overwritten with
                                     the chosen value later - cf tcp_newtcpcb() *)
       tf_doing_ws       := F;
(* X       ts_recent         := TimeWindowClosed; X *)
(* X       tf_req_tstmp      := F;    (* cf tcp_newtcpcb() *)
       tf_doing_tstmp    := F; X *)
       last_ack_sent     := tcp_seq_foreign 0w;
       bsd_cantconnect   := F
(* X       snd_cwnd_prev     := 0;
       snd_ssthresh_prev := 0;
       t_badrxtwin       := TimeWindowClosed X *)
       (* Note: everything should be listed here, leaving nothing as ARB. *)
       (* Many are always overwritten, however. *)
    |>
`;


(* ------------------------------------------------------------------ *)
(*: @chapter [[TCP1_auxFns_relmonad]] Relational monad

The relational `monad' is used to describe stateful computation in a
convenient and compositional way.

:*)
(* ------------------------------------------------------------------ *)

(* not sure if this belongs in this file *)



(* ------------------------------------------------------------------ *)
(*:
@section [[aux_relmonad]] TCP Relational monad

   The implementation TCP input and output routines are imperative C
   code, with mutations of state variables and calls to various other
   routines, some of which send messages or have other observable
   effects.  These are intertwined in a complex control flow.
%
   In the specification we have attempted, as much as possible, to
   adopt purely functional or relational styles.  To deal with the
   observable side effects in the middle of (e.g.) |tcp_output|,
   however, we have had to identify some intermediate states.
%
   We introduce a relational monadic style to do so, using
   higher-order functions to hide the plumbing of state variables.
   The nondeterminism of our model adds another layer of complexity;
   instead of the usual functional monads, we use relational monads.

   An operation on the current state is modelled by a relation on the
   current and resulting states.  A number of primitive operations
   are defined; these operations are then chained together by a
   binding combinator, which takes two relations and yields their
   composition.  In this way arbitrarily complex operations on state
   may be defined in a modular manner, and the referential
   transparency of the logic is maintained.

   In the present application, the current state is a pair
   [[(sock:socket,bndlm:bandlim_state)]] of the current socket and the
   state of the host's band limiter.  The resulting state is a
   quadruple [[((sock':socket,bndlm':bandlim_state,outsegs':'msg
   list),continue':bool)]] of the final socket, band-limiter state, a
   list of segments to be output, and a flag.  This flag models
   aborting: if it is set, operations should be chained together
   normally; if it is cleared, subsequent operations should \emph{not}
   be performed, and instead the resulting state should be the final
   state of the entire composite operation of which this is a part.

   The binding combinator is [[andThen]].  Primitive operators include
   [[cont]], which does nothing and continues, and [[stop]], which
   does nothing and stops.  Several other operations are defined to
   manipulate the state -- the monadic glue is intended to abstract
   away from the implementation of that state as a pair of tuples.

   It should be a theorem that [[andThen]] is assoc, that [[cont]] is
   unit and [[stop]] is zero, and so on.

   Note that [[outsegs]], the list of messages, is actually a list of
   arbitrary type; this enables us to lift the glue to the type [[msg
   # bool]] in [[deliver_in_3]], where we need the flag to deal with
   queueing failure.

   As throughout this specification, beware that the nondeterminism
   of, e.g., [[chooseM]] is modelled by an existential, and is thus
   "angelic" in some sense.  This may or may not be what you expect.

:*)
(* ------------------------------------------------------------------ *)

val _ = add_infix ("andThen", 97, LEFT); (* absolutely no idea what precedence to choose *)

val andThen_def = Phase.phase_x 2 xDefine "andThen" `(*: normal sequencing :*)
  (op1 andThen op2) =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       ?sock1 bndlm1 outsegs1 continue1 sock2 bndlm2 outsegs2 continue2.
       op1 (sock,bndlm) ((sock1,bndlm1,outsegs1),continue1) /\
       if continue1 then
           op2 (sock1,bndlm1) ((sock2,bndlm2,outsegs2),continue2) /\
           (sock' = sock2 /\ bndlm' = bndlm2 /\ outsegs' = APPEND outsegs1 outsegs2 /\ continue' = continue2)
       else
           (sock' = sock1 /\ bndlm' = bndlm1 /\ outsegs' = outsegs1 /\ continue' = F)
`(*:@mergewithnext:*);

val cont_def = Phase.phase 2 Define`(*: do nothing, and continue (unit for [[andThen]]) :*)
  cont =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       (sock' = sock /\ bndlm' = bndlm /\ outsegs' = [] /\ continue' = T)
`(*:@mergewithnext:*);

val stop_def = Phase.phase 2 Define`(*: do nothing, and stop (zero for [[andThen]]) :*)
  stop =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       (sock' = sock /\ bndlm' = bndlm /\ outsegs' = [] /\ continue' = F)
`(*:@mergewithnext:*);

val assert_def = Phase.phase 2 Define`(*: assert truth of condition, and continue :*)
  assert p =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       (p /\ sock' = sock /\ bndlm' = bndlm /\ outsegs' = [] /\ continue' = T)
`(*:@mergewithnext:*);

val assert_failure_def = Phase.phase 2 Define`(*: assertion violated; fail noisily :*)
  assert_failure s =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       ASSERTION_FAILURE s
`(*:@mergewithnext:*);

val chooseM_def = Phase.phase 2 Define`(*: choose a value from a set, nondeterministically :*)
  chooseM s f =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       choose x :: s. f x (sock,bndlm) ((sock',bndlm',outsegs'),continue')
`;

val get_sock_def = Phase.phase 2 Define`(*: get current socket :*)
  get_sock f =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       f sock (sock,bndlm) ((sock',bndlm',outsegs'),continue')
`(*: @mergewithnext :*);
val get_tcp_sock_def = Phase.phase 2 Define`(*: assert current socket is TCP, and get its protocol data :*)
  get_tcp_sock f =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       ?tcp_sock.
       sock.pr = TCP_PROTO(tcp_sock) /\
       f tcp_sock (sock,bndlm) ((sock',bndlm',outsegs'),continue')
`(*: @mergewithnext :*);
val get_cb_def = Phase.phase 2 Define`(*: assert current socket is TCP, and get its control block :*)
  get_cb f =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       ?tcp_sock.
       sock.pr = TCP_PROTO(tcp_sock) /\
       f tcp_sock.cb (sock,bndlm) ((sock',bndlm',outsegs'),continue')
`(*: @mergewithnext :*);

(* alter socket *)
val modify_sock_def = Phase.phase 2 Define`(*: apply function to current socket :*)
  modify_sock f =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       (sock' = f sock /\ bndlm' = bndlm /\ outsegs' = [] /\ continue' = T)
`(*: @mergewithnext :*);
(* alter TCP socket *)
val modify_tcp_sock_def = Phase.phase 2 Define`(*: apply function to current socket :*)
  modify_tcp_sock f =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       (?tcp_sock.
        sock.pr = TCP_PROTO(tcp_sock) /\
        sock' = sock with <| pr := TCP_PROTO (f tcp_sock) |> /\ bndlm' = bndlm /\ outsegs' = [] /\ continue' = T)
`(*: @mergewithnext :*);
val modify_cb_def = Phase.phase 2 Define`(*: assert current socket is TCP, and apply function to its control block :*)
  modify_cb f =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       ?tcp_sock.
       sock.pr = TCP_PROTO(tcp_sock) /\
       (sock' = sock with <| pr := TCP_PROTO(tcp_sock with <| cb := (f tcp_sock.cb) |>) |> /\
        bndlm' = bndlm /\ outsegs' = [] /\ continue' = T)
`;

val emit_segs_def = Phase.phase 2 Define`(*: append segments to current output list :*)
  emit_segs segs =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       (sock' = sock /\ bndlm' = bndlm /\ outsegs' = segs /\ continue' = T)
`(*:@mergewithnext:*);

val emit_segs_pred_def = Phase.phase 2 Define`(*: append segments specified by a predicate (nondeterministic) :*)
  emit_segs_pred f =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       (sock' = sock /\ f bndlm bndlm' outsegs' /\ continue' = T)
`;

val mliftc_def = Phase.phase 2 Define`(*: lift a monadic operation not involving [[continue]] or [[bndlm]] :*)
  mliftc f =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       (f sock (sock',outsegs') /\ bndlm' = bndlm /\ continue' = T)
`(*:@mergewithnext:*);

val mliftc_bndlm_def = Phase.phase 2 Define`(*: lift a monadic operation not involving [[continue]] :*)
  mliftc_bndlm f =
     \ (sock:socket,bndlm:bandlim_state) ((sock':socket,bndlm':bandlim_state,outsegs':'msg list),continue':bool).
       (f (sock,bndlm) (sock',bndlm',outsegs') /\ continue' = T)
`;


(* ALL THIS BELOW WAS AT THE START OF TCP1_hostLTSSCript.sml *)

(*: @chapter [[TCPmajorAuxFns]] Auxiliary functions for TCP segment creation and drop

We gather here all the general TCP segment generation and processing
functions that are used in the host LTS.

:*)


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_syn_rst_segment_creation]] TCP SYN and RST Segment Creation

Generating various simple segments (none of which contain any user data).

     :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* Don't Phase: handled by testEval *)
val make_syn_segment_def = Define`
(*: Make a SYN segment for emission by [[connect_1]] etc :*)
  make_syn_segment cb (i1,i2,p1,p2) ts_val seg' =
    (choose urp_any :: UNIV.
     choose ack_any :: UNIV.

    (* Determine window size; fail if out of range *)
    let win = n2w cb.rcv_wnd in
    w2n win = cb.rcv_wnd /\

    (* Choose a window scaling; fail if out of range *)
    (* Note there may be a better place for this assertion. *)
    let ws = OPTION_MAP CHR cb.request_r_scale in
    (IS_SOME cb.request_r_scale ==> ORD (THE ws) = THE cb.request_r_scale) /\
    (case ws of NONE -> T || SOME n -> ORD n <= TCP_MAXWINSCALE) /\

    (* Determine maximum segment size; fail if out of range *)
    (*: Put the MSS we initially advertise into [[t_advmss]] :*)
    let mss = (case cb.t_advmss of
                  NONE   -> NONE
               || SOME v -> SOME (n2w v)) in
    (case cb.t_advmss of
        NONE   -> T
     || SOME v -> v = w2n (THE mss)) /\

    (* Do timestamping? *)
    choose ts :: UNIV. (* X = do_tcp_options cb.tf_req_tstmp cb.ts_recent ts_val in X *)

    seg' = <| is1  := SOME i1;
              is2  := SOME i2;
              ps1  := SOME p1;
              ps2  := SOME p2;
              seq  := cb.iss;
              ack  := ack_any;
              URG  := F;
              ACK  := F;
              PSH  := F;
              RST  := F;
              SYN  := T;
              FIN  := F;
              win  := win;
              ws   := ws;
              urp  := urp_any;
              mss  := mss;
              ts   := ts;
              data := []
           |>
    )
`;

(* Don't Phase: handled by testEval *)
val make_syn_ack_segment_def = Define`
(*: Make a SYN,ACK segment for emission by [[deliver_in_1]], [[deliver_in_2]], etc.:*)
  make_syn_ack_segment cb (i1,i2,p1,p2) ts_val' seg' =
    choose urp_any :: UNIV.

    (* Determine window size; fail if out of range *)
    (*: We don't scale yet ([[>> rcv_scale']]). RFC1323 says: segments with SYN are not scaled, and BSD
       agrees.  Even though we know what scaling the other end wants to use, and we know whether we
       are doing scaling, we can't use it until we reach the ESTABLISHED state. :*)
    let win = n2w cb.rcv_wnd in (*: [[rcv_window - LENGTH data']] :*)
    w2n win = cb.rcv_wnd /\

    (* If doing window scaling, set it; fail if out of range *)
    let ws = if cb.tf_doing_ws then SOME (CHR cb.rcv_scale) else NONE in
    (cb.tf_doing_ws ==> ORD (THE ws) = cb.rcv_scale) /\

    (* Determine maximum segment size; fail if out of range *)
    (*: Put the MSS we initially advertise into [[t_advmss]] :*)
    let mss = (case cb.t_advmss of
                  NONE   -> NONE
               || SOME v -> SOME (n2w v)) in
    (case cb.t_advmss of
        NONE   -> T
     || SOME v -> v = w2n (THE mss)) /\

    (* Set timestamping option? *)
    choose ts :: UNIV. (* X =  do_tcp_options cb.tf_doing_tstmp cb.ts_recent ts_val' in X *)

    seg' = <| is1  := SOME i1;
              is2  := SOME i2;
              ps1  := SOME p1;
              ps2  := SOME p2;
              seq  := cb.iss;
              ack  := cb.rcv_nxt;
              URG  := F;
              ACK  := T;
              PSH  := F;  (*: see below :*)
              RST  := F;
              SYN  := T;
              FIN  := F;  (* Note: we are not modelling T/TCP *)
              win  := win;
              ws   := ws;
              urp  := urp_any;
              mss  := mss;
              ts   := ts;
              data := []  (*: see below :*)
           |>
(*: No [[data]] can be send here using the BSD sockets API, although
TCP notionally allows it.  Accordingly, the [[PSH]] flag is never set
(under BSD, PSH is only set if we're sending a non-zero amount of data
(and emptying the send buffer); see |tcp_output.c:626|). :*) `;



(* Don't Phase: handled by testEval *)
val make_ack_segment_def = Define`
(*: Make a plain boring ACK segment in response to a SYN,ACK segment :*)
  make_ack_segment cb FIN (i1,i2,p1,p2) ts_val' seg' =
    ((* SB thinks these should be unconstrained. *)
    choose urp_garbage :: UNIV.

    (* Determine window size; fail if out of range *)
    (* Connection is now established so any scaling should be taken into account *)
    (* Note it might be appropriate to clip the value to be in range rather than failing if out of range. *)
    let win = n2w (cb.rcv_wnd >> cb.rcv_scale) in
    w2n win = cb.rcv_wnd >> cb.rcv_scale /\

    (* Set timestamping option? *)
    choose ts :: UNIV. (* X = do_tcp_options cb.tf_doing_tstmp cb.ts_recent ts_val' in X *)

    seg' = <| is1  := SOME i1;
              is2  := SOME i2;
              ps1  := SOME p1;
              ps2  := SOME p2;
              seq  := if FIN then cb.snd_una else cb.snd_nxt;
              ack  := cb.rcv_nxt;
              URG  := F;
              ACK  := T;
              PSH  := F;  (*: see comment for [[make_syn_ack_segment]] :*)
              RST  := F;
              SYN  := F;
              FIN  := FIN;
              win  := win;
              ws   := NONE;
              urp  := urp_garbage;
              mss  := NONE;
              ts   := ts;
              data := [] (*: Note that if there is data in [[sndq]] then it
                            should always appear in a seperate segment after the connnection
                            establishment handshake, but this needs to be verified. :*)
           |>)
`;


(* Don't Phase: handled by testEval *)
val bsd_make_phantom_segment_def = Define`
(*: Make phantom (no flags) segment for BSD [[LISTEN]] bug :*)
(* If a socket is changed to the LISTEN state, the rexmt timer may still be running.
   If it fires, phantom segments are emitted. *)
  bsd_make_phantom_segment cb (i1,i2,p1,p2) ts_val' cantsndmore seg' =
    (choose urp_garbage :: UNIV.

    (* Determine window size; fail if out of range *)
    (* Connection is now established so any scaling should be taken into account *)
    (* Note it might be appropriate to clip the value to be in range rather than failing if out of range. *)
    let win = n2w (cb.rcv_wnd >> cb.rcv_scale) in
    w2n win = cb.rcv_wnd >> cb.rcv_scale /\

    let FIN = (cantsndmore /\ cb.snd_una < (cb.snd_max - 1)) in

    (* Set timestamping option? *)
    choose ts :: UNIV. (* X = do_tcp_options cb.tf_doing_tstmp cb.ts_recent ts_val' in X *)

    seg' = <| is1  := SOME i1;
              is2  := SOME i2;
              ps1  := SOME p1;
              ps2  := SOME p2;
              seq  := if FIN then cb.snd_una else cb.snd_max; (* no flags, no data, and no persist timer so use snd_max *)
              ack  := cb.rcv_nxt;  (*: yes, really, even though [[~ACK]] :*)
              URG  := F;
              ACK  := F;
              PSH  := F;
              RST  := F;
              SYN  := F;
              FIN  := FIN;
              win  := win;
              ws   := NONE;
              urp  := urp_garbage;
              mss  := NONE;
              ts   := ts;
              data := [] (*: sndq always empty in this situation :*)
           |>)
`;


(* Don't phase: handled by testEval *)
val make_rst_segment_from_cb_def = Define`
(*: Make a RST segment asynchronously, from socket information only :*)
  make_rst_segment_from_cb cb (i1,i2,p1,p2) seg' =
    (* Deliberately unconstrained *)
    choose urp_garbage  :: UNIV .
    choose URG_garbage  :: UNIV .
    choose PSH_garbage  :: UNIV .
    choose win_garbage  :: UNIV .
    choose data_garbage :: UNIV.
    choose FIN_garbage  :: UNIV .

    (*: Note that BSD is perfectly capable of putting data in a RST segment; try filling the buffer
       and then doing a force close: the result is a segment with RST+PSH+data+win advertisement.
       Presumably URG is also possible.  This is *not* the same as the RFC-suggested data carried by
       a RST; that would be an error message, this is just data from the buffer!  :*)
    seg' = <| is1  := SOME i1;
              ps1  := SOME p1;
              is2  := SOME i2;
              ps2  := SOME p2;
              seq  := cb.snd_nxt;   (*: from RFC793p62 :*)
              ack  := cb.rcv_nxt;   (*: seems the right thing to do :*)
              URG  := URG_garbage;  (*: expect: [[F]] :*)
              ACK  := T;            (*: from TCPv1p248 :*)
              PSH  := PSH_garbage;  (*: expect: [[F]] :*)
              RST  := T;
              SYN  := F;
              FIN  := FIN_garbage;  (*: expect: [[F]] :*)
              win  := win_garbage;  (*: expect: [[0w]] :*)
              ws   := NONE;
              urp  := urp_garbage;  (*: expect: [[0w]] :*)
              mss  := NONE;
              ts   := NONE;  (*: RFC1323 S4.2 recommends no TS on RST, and BSD follows this :*)
              data := data_garbage  (*: expect: [[ [] ]] :*)
           |>
`;



val make_rst_segment_from_seg_def = Phase.phase 2 Define`
(*: Make a RST segment synchronously, in response to an incoming segment :*)
  make_rst_segment_from_seg seg seg' =
    (seg.RST = F /\  (* Sanity check: never RST a RST *)

    (?ack'.
    (* Deliberately unconstrained *)
    choose urp_garbage::UNIV.
    choose URG_garbage::UNIV.
    choose PSH_garbage::UNIV.
    choose win_garbage::UNIV.
    choose data_garbage::UNIV.
    choose FIN_garbage::UNIV.

    (* RFC795 S3.4: only ack segments that don't contain an ACK.
       SB believes this is equivalent to: only send a RST+ACK segment in response to a bad SYN
       segment *)
    let ACK' = ~seg.ACK in

    (* Sequence number is zero for RST+ACK segments, otherwise it is the next sequence number
       expected *)
    let seq' = if seg.ACK then tcp_seq_flip_sense seg.ack
	       else tcp_seq_local 0w in

   (if ACK' then
       (* RFC794 S3.4: for RST+ACK segments the ack value must be valid *)
       ack' = tcp_seq_flip_sense seg.seq + LENGTH seg.data + (if seg.SYN then 1 else 0)
     else
       (* otherwise it can be arbitrary, although it possibly should be zero *)
       ack' IN { n | T }
    ) /\
    seg' = <| is1  := seg.is2;
              ps1  := seg.ps2;
              is2  := seg.is1;
              ps2  := seg.ps1;
              seq  := seq';
              ack  := ack';
              URG  := URG_garbage;  (*: expect: [[F]] :*)
              ACK  := ACK';
              PSH  := PSH_garbage;  (*: expect: [[F]] :*)
              RST  := T;
              SYN  := F;
              FIN  := FIN_garbage;  (*: expect: [[F]] :*)
              win  := win_garbage;  (*: expect: [[0w]] :*)
              ws   := NONE;
              urp  := urp_garbage;  (*: expect: [[0w]] :*)
              mss  := NONE;
              ts   := NONE;  (*: RFC1323 S4.2 recommends no TS on RST, and BSD follows this :*)
              data := data_garbage  (*: expect: [[ [] ]] :*)
           |>
    ))
`;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_segment_creation]] TCP General Segment Creation

The TCP output routines.  These, together with the input routines in
[[deliver_in_3]], form the heart of TCP.


:*)


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* Don't Phase: handled specially by netEval *)
val tcp_output_required_def = Define`
(*: determine whether TCP output is required :*)
  tcp_output_required arch ifds0 sock (do_output', persist_fun') =
    let tcp_sock = tcp_sock_of sock in
    let cb = tcp_sock.cb in

    (*: Note this does not deal with |TF_LASTIDLE| and |PRU_MORETOCOME| :*)
(* X    let snd_cwnd' =
      if ~(cb.snd_max = cb.snd_una /\
           stopwatch_val_of cb.t_idletime >= computed_rxtcur cb.t_rttinf arch)
      then  (* inverted so this clause is tried first *)
         cb.snd_cwnd
      else
        (*: The connection is idle and has been for  >= 1 RTO :*)
         (*: Reduce [[snd_cwnd]] to commence slow start :*)
         cb.t_maxseg * (if is_localnet ifds0 (THE sock.is2) then SS_FLTSZ_LOCAL else SS_FLTSZ) in X *)

    (*: Calculate the amount of unused send window :*)
    choose win :: {win| 0 <= win /\ win <= (cb.snd_wnd)}. (* X = MIN cb.snd_wnd snd_cwnd' in X *) (* X it's a bit odd to let this be non-deterministically 0 even when snd_wnd is not X *)
    let snd_wnd_unused = int_of_num win - (cb.snd_nxt - cb.snd_una) in

    (*: Is it possible that a FIN may need to be sent? :*)
    let fin_required = (sock.cantsndmore /\ tcp_sock.st NOTIN {FIN_WAIT_2;TIME_WAIT}) in

    (*: Under BSD, we may need to send a [[FIN]] in state [[SYN_SENT]] or [[SYN_RECEIVED]], so we may
        effectively still have a [[SYN]] on the send queue. :*)
    let syn_not_acked = (bsd_arch arch /\ tcp_sock.st IN {SYN_SENT;SYN_RECEIVED}) in

    (*: Is there data or a FIN to transmit? :*)
    let last_sndq_data_seq = cb.snd_una + LENGTH tcp_sock.sndq in
    let last_sndq_data_and_fin_seq  = last_sndq_data_seq + (if fin_required then 1 else 0)
                                                         + (if syn_not_acked then 1 else 0) in
    let have_data_to_send = cb.snd_nxt < last_sndq_data_seq in
    let have_data_or_fin_to_send = cb.snd_nxt < last_sndq_data_and_fin_seq in

    (*: The amount by which the right edge of the advertised window could be moved :*)
    let window_update_delta = (int_min (int_of_num(TCP_MAXWIN << cb.rcv_scale))
				       (int_of_num(sock.sf.n(SO_RCVBUF)) - int_of_num(LENGTH
				       tcp_sock.rcvq))) -
			      (cb.rcv_adv - cb.rcv_nxt) in

    (*: Send a window update? This occurs when (a) the advertised window can be increased by at
        least two maximum segment sizes, or (b) the advertised window can be increased by at least
        half the receive buffer size. See |tcp_output.c:322ff|. :*)
    let need_to_send_a_window_update = (window_update_delta >= int_of_num (2 * cb.t_maxseg) \/
                                       2 * window_update_delta >= int_of_num (sock.sf.n(SO_RCVBUF)))
    in

    (*: Note that silly window avoidance and [[max_sndwnd]] need to be dealt with here; see |tcp_output.c:309| :*)

    (*: Can a segment be transmitted? :*)
    let do_output = (
      (*: Data to send and the send window has some space, or a FIN can be sent :*)
      (have_data_or_fin_to_send /\
       (have_data_to_send ==> snd_wnd_unused > 0)) \/  (* don't need space if only sending FIN *)

      (*: Can send a window update :*)
      need_to_send_a_window_update \/

      (*: There is outstanding urgent data to be transmitted :*)
      IS_SOME tcp_sock.sndurp \/

      (*: An ACK should be sent immediately (e.g. in reply to a window probe) :*)
      cb.tf_shouldacknow
      ) in

    choose tt_rexmt' :: start_tt_persist 0 arch.
    let persist_fun =
      let cant_send = (~do_output /\ tcp_sock.sndq <> [] /\ mode_of cb.tt_rexmt = NONE) in
      let window_shrunk = (win = 0 /\ snd_wnd_unused < 0 /\ (*: [[win = 0]] if in [[SYN_SENT]], but still may send FIN :*)
                           (bsd_arch arch ==> tcp_sock.st <> SYN_SENT)) in

      if cant_send then  (* takes priority over window_shrunk; note this needs to be checked *)
        (*: Can not transmit a segment despite a non-empty send queue and no running persist or
            retransmit timer. Must be the case that the receiver's advertised window is now zero, so
            start the persist timer. Normal: |tcp_output.c:378ff| :*)
        SOME \cb. cb with <| tt_rexmt := tt_rexmt' (* X start_tt_persist 0 (* X cb.t_rttinf X *) arch X *) |>
      else if window_shrunk then
        (*: The receiver's advertised window is zero and the receiver has retracted window space
            that it had previously advertised. Reset [[snd_nxt]] to [[snd_una]] because the data
            from [[snd_una]] to [[snd_nxt]] has likely not been buffered by the receiver and should
            be retransmitted. Bizzarely (on FreeBSD 4.6-RELEASE), if the persist timer is running
            reset its shift value :*)
        (* Window shrunk: |tcp_output.c:250ff| *)
        SOME \cb.
         cb with <| tt_rexmt := case cb.tt_rexmt of
                        SOME (Timed((Persist,shift),d)) -> SOME (Timed((Persist,0),d))
                        || _593 -> tt_rexmt' (* X start_tt_persist 0 cb.t_rttinf arch X *) ;
                    snd_nxt := cb.snd_una |>
      else
        (*: Otherwise, leave the persist timer alone :*)
        NONE
    in
      (do_output', persist_fun') = (do_output,persist_fun)`

(*:

  @description

  This function determines if it is currently necessary to emit a
  segment.  It is not quite a predicate, because in certain
  circumstances the operation of testing may start or reset the
  persist timer, and alter [[snd_nxt]].  Thus it returns a pair of a
  flag [[do_output]] (with the obvious meaning), and an optional
  mutator function [[persist_fun]] which, if present, performs the
  required updates on the TCP control block.

  @internal

  we feel that there should be a simpler version of tcp_output, that is called from various places
  in deliver_in_3.  The full glory of tcp_output below should only be needed by deliver_out_1.  In
  order to write the simpler version, though, we need to work out exactly when all the various
  conditions in tcp_output hold, particularly at the moments it is called from deliver_in_3.

  NB: whenever tcp\_output.c has nothing to do, absolutely nothing happens, even though this might
  not be immediately apparent; we know [[~do_output ==> ~force_output ==> tt_persist' =
  cb.tt_persist]], and nothing else has changed.

  ARGH!  Not quite true - snd_cwnd may change if idle!

  About cb.tf_shouldacknow:  -- explicit output requested
      ? on receiving a keepalive probe; or
      ? on receiving a repeated old ACK (fast retransmit); or
      ? by recv() when a zero-size (or teeny) window is opened
      ? by send() when new urgent data is sent, changing sndurp
      ? when performing dropafterack

  BSD uses cb.tf_acknow for some of these; P thinks we should have distinct semaphores (with
  sensible names) for each case (cantsndmore should have a similar name).  Are these all pure
  boolean semaphores?  When we come to Level 3, not sure our urgency idiom is going to be very lucid
  - guess BSD just doesn't allow interleaving between (eg) such a recv() and the call to
  tcp_output.

  -- delayed ack timer (tt_delack) expires - dealt with by timer_tt_delack_1

  force_output -- persist timer expires (or send_OOB called) - believe dealt with by snd_wnd_unused
  munging above

  -- retransmission timer (tt_rexmt) expires - currently dealt with by timer_tt_rexmt_1

  IS_SOME tcp_sock.sndurp:

  This condition cannot made false by emitting a segment, whereas the other disjuncts may be. OTOH,
  this condition is superfluous as it is (really) contained within have_data_{or_fin_}to_send

:*);

val tcp_output_really_def = Phase.phase 2 Define`
(*: do TCP output :*)
  tcp_output_really arch window_probe ts_val' ifds0 sock (sock',outsegs') =
    let tcp_sock = tcp_sock_of sock in
    let cb = tcp_sock.cb in

    (*: Assert that the socket is fully bound and connected :*)
    sock.is1 <> NONE /\
    sock.is2 <> NONE /\
    sock.ps1 <> NONE /\
    sock.ps2 <> NONE /\

    (*: Note this does not deal with |TF_LASTIDLE| and |PRU_MORETOCOME| :*)
    (* X let snd_cwnd' =
      if ~(cb.snd_max = cb.snd_una /\
           stopwatch_val_of cb.t_idletime >= computed_rxtcur cb.t_rttinf arch)
      then  (* inverted so this clause is tried first *)
         cb.snd_cwnd
      else
        (*: The connection is idle and has been for >= 1RTO :*)
         (*: Reduce [[snd_cwnd]] to commence slow start :*)
         cb.t_maxseg * (if is_localnet ifds0 (THE sock.is2) then SS_FLTSZ_LOCAL else SS_FLTSZ) in X *)

    (*: Calculate the amount of unused send window :*)
    choose win0 :: {win| 0 <= win /\ win <= (cb.snd_wnd)}. (* X = MIN cb.snd_wnd snd_cwnd' in X *) (* X it's a bit odd to let this be non-deterministically 0 even when snd_wnd is not X *)
    let win = (if window_probe /\ win0 = 0 then 1 else win0) in
    let (snd_wnd_unused : int) = int_of_num win - (cb.snd_nxt - cb.snd_una) in

    (*: Is it possible that a [[FIN]] may need to be transmitted? :*)
    let fin_required = (sock.cantsndmore /\ tcp_sock.st NOTIN {FIN_WAIT_2;TIME_WAIT}) in

    (*: Calculate the sequence number after the last data byte in the send queue :*)
    let last_sndq_data_seq = cb.snd_una + LENGTH tcp_sock.sndq in

    (*: The data to send in this segment (if any) :*)
    let data' = DROP (Num (cb.snd_nxt - cb.snd_una)) tcp_sock.sndq in
    let data_to_send = TAKE (MIN (clip_int_to_num snd_wnd_unused) cb.t_maxseg) data' in

    (*: Should [[FIN]] be set in this segment? :*)
    let FIN = (fin_required /\ cb.snd_nxt + LENGTH data_to_send >= last_sndq_data_seq) in

    (*: Should [[ACK]] be set in this segment? Under BSD, it is not set if the socket is in [[SYN_SENT]]
        and emitting a [[FIN]] segment due to [[shutdown()]] having been called. :*)
    let ACK = if (bsd_arch arch /\ FIN /\ tcp_sock.st = SYN_SENT) then F else T in

    (*: If this socket has previously sent a [[FIN]] which has not yet been acked, and [[snd_nxt]]
        is past the [[FIN]]'s sequence number, then [[snd_nxt]] should be set to the sequence number
        of the [[FIN]] flag, i.e. a retransmission. Check that [[snd_una <> iss]] as in this case no
        data has yet been sent over the socket  :*)
    let snd_nxt' = if FIN /\ (cb.snd_nxt + LENGTH data_to_send = last_sndq_data_seq+1 /\
                      cb.snd_una  <> cb.iss \/ Num(cb.snd_nxt - cb.iss) = 2) then
		     cb.snd_nxt - 1
                   else
		     cb.snd_nxt in

    (*: The BSD way: set [[PSH]] whenever sending the last byte of data in the send queue :*)
    let PSH = (data_to_send <> [] /\ cb.snd_nxt + LENGTH data_to_send = last_sndq_data_seq) in

    (*: If sending urgent data, set the [[URG]] and [[urp]] fields appropriately :*)
    let (URG,urp) = (case tcp_sock.sndurp of
                      NONE -> (F,0) ||  (*: No urgent data; don't set :*)
                      SOME sndurpn -> let urp_n = (cb.snd_una + sndurpn) - cb.snd_nxt + 1 in
                                          (* points one byte *past* the urgent byte *)
                                      if urp_n < 1 then
                                        (F,0) (*: Urgent data out of range; don't set :*)
                                      else if urp_n < 65536 then
                                        (T,Num urp_n) (*: Urgent data in range; set :*)
                                      else
					(*: Urgent data in the very distant future; set :*)
					(* Steven's suggestion; not sure if followed *)
                                        (T,65535)) in

    (*: Calculate size of the receive window (based upon available buffer space) :*)
    let rcv_wnd'' = calculate_bsd_rcv_wnd sock.sf tcp_sock in
    let rcv_wnd' = MAX (Num (cb.rcv_adv - cb.rcv_nxt)) (MIN (TCP_MAXWIN << cb.rcv_scale)
                  (if rcv_wnd'' < sock.sf.n(SO_RCVBUF) DIV 4 /\ rcv_wnd'' < cb.t_maxseg
		   then 0  (*: Silly window avoidance: shouldn't advertise a tiny window :*)
                   else rcv_wnd'')) in

    (*: Possibly set the segment's timestamp option. Under BSD, we may need to send a
        [[FIN]] segment from [[SYN_SENT]], if the user called [[shutdown()]], in which
        case the timestamp option hasn't yet been negotiated, so we used [[tf_req_tstmp]]
        rather than [[tf_doing_tstmp]]. :*)
    (* X let want_tstmp  = if (bsd_arch arch /\ tcp_sock.st = SYN_SENT) then cb.tf_req_tstmp
                                                                  else cb.tf_doing_tstmp in X *)
    choose ts :: UNIV. (* X let ts = do_tcp_options want_tstmp cb.ts_recent ts_val' in X *)

    (*: Advertise an appropriately scaled receive window :*)
    (*: Assert the advertised window is within a sensible range :*)
    let win = n2w (rcv_wnd' >> cb.rcv_scale) in
    w2n win = rcv_wnd' >> cb.rcv_scale /\

    (*: Assert the urgent pointer is within a sensible range :*)
    let urp_ = n2w urp in
    w2n urp_ = urp /\

    let seg = <| is1  := sock.is1;
                 is2  := sock.is2;
                 ps1  := sock.ps1;
                 ps2  := sock.ps2;
                 seq  := snd_nxt';
                 ack  := cb.rcv_nxt;
                 URG  := URG;
                 ACK  := ACK;
                 PSH  := PSH;
                 RST  := F;
                 SYN  := F;
                 FIN  := FIN;
                 win  := win;
                 ws   := NONE;
                 urp  := urp_;
                 mss  := NONE;
                 ts   := ts;
                 data := data_to_send
               |> in

    (*: If emitting a [[FIN]] for the first time then change TCP state :*)
    let st' = if FIN then
                case tcp_sock.st of
                  SYN_SENT     -> tcp_sock.st ||    (*: can't move yet -- wait until connection established (see [[deliver_in_2]]/[[deliver_in_3]]) :*)
                  SYN_RECEIVED -> tcp_sock.st ||    (*: can't move yet -- wait until connection established (see [[deliver_in_2]]/[[deliver_in_3]]) :*)
                  ESTABLISHED  -> FIN_WAIT_1 ||
                  CLOSE_WAIT   -> LAST_ACK ||
                  FIN_WAIT_1   -> tcp_sock.st ||    (*: FIN retransmission :*)
                  FIN_WAIT_2   -> tcp_sock.st ||    (*: can't happen       :*)
                  CLOSING      -> tcp_sock.st ||    (*: FIN retransmission :*)
                  LAST_ACK     -> tcp_sock.st ||    (*: FIN retransmission :*)
                  TIME_WAIT    -> tcp_sock.st       (*: can't happen       :*)
              else
                tcp_sock.st in

    (*: Updated values to store in the control block after the segment is output :*)
    let snd_nxt'' = snd_nxt' + LENGTH data_to_send + (if FIN then 1 else 0) in
    let snd_max' = MAX cb.snd_max snd_nxt'' in

    (*: Following a |tcp_output| code walkthrough by SB: :*)
    choose tt_rexmt'' ::  start_tt_rexmt arch 0 F (* X cb.t_rttinf X *).
    let tt_rexmt' = if (mode_of cb.tt_rexmt = NONE \/
		       (mode_of cb.tt_rexmt = SOME(Persist) /\ ~window_probe)) /\
                        snd_nxt'' > cb.snd_una then
                       (*: If the retransmit timer is not running, or the persist timer is running
                           and this segment isn't a window probe, and this segment contains data or
                           a [[FIN]] that occurs past [[snd_una]] (i.e.~new data), then start the
                           retransmit timer. Note: if the persist timer is running it will be
                           implicitly stopped :*)
                       tt_rexmt'' (* X start_tt_rexmt arch 0 F (* X cb.t_rttinf X *) X *)
		    else if (window_probe \/ (IS_SOME tcp_sock.sndurp)) /\ win0 <> 0 /\
                       mode_of cb.tt_rexmt = SOME(Persist) then
                       (*: If the segment is a window probe or urgent data is being sent, and in
                           either case the send window is not closed, stop any running persist
                           timer. Note: if [[window_probe]] is [[T]] then a persist timer will
                           always be running but this isn't necessarily true when urgent data is
                           being sent :*)
                       NONE (*: stop persisting :*)
                    else
		       (*: Otherwise, leave the timers alone :*)
                       cb.tt_rexmt in

    (*: Time this segment if it is sensible to do so, i.e.~the following conditions hold : (a) a
        segment is not already being timed, and (b) data or a FIN are being sent, and (c) the
        segment being emitted is not a retransmit, and (d) the segment is not a window probe :*)
    (* X let t_rttseg' = if IS_NONE cb.t_rttseg /\ (data_to_send <> [] \/ FIN) /\
                       snd_nxt'' > cb.snd_max /\ ~window_probe
		    then
                       SOME(ts_val', snd_nxt')
                    else
                       cb.t_rttseg in X *)

    (*: Update the socket :*)
    sock' = sock with <| pr := TCP_PROTO(tcp_sock with
                        <| st := st'; cb := tcp_sock.cb with
                          <| tt_rexmt      := tt_rexmt';
                             (* X snd_cwnd      := snd_cwnd'; X *)
                             rcv_wnd       := rcv_wnd';
                             tf_rxwin0sent := (rcv_wnd' = 0);
                             tf_shouldacknow := F;
                             (* X t_rttseg      := t_rttseg'; X *)
                             snd_max       := snd_max';
                             snd_nxt       := snd_nxt'';
                             (* X tt_delack     := NONE; X *)
                             last_ack_sent := cb.rcv_nxt;
                             rcv_adv       := cb.rcv_nxt + rcv_wnd'
                       |> |>) |> /\

    (*: Constrain the list of output segments to contain just the segment being emitted :*)
    outsegs' = [TCP seg]
`
(*:

  @description

  This function constructs the next segment to be output.  It is
  usually called once [[tcp_output_required]] has returned true, but
  sometimes is called directly when we wish always to emit a segment.
  A large number of TCP state variables are modified also.

  Note that while constructing the segment a variety of errors such as
  [[ENOBUFS]] are possible, but this is not modelled here. Also,
  window shrinking is not dealt with properly here.

  @internal

  Deliberately not requiring the FIN to fit in the window, only the actual data.  We think this is
  the only sensible way; we're not sure what BSD does

  The BSD code jumps to roughly the top of tcp_output again if 'sendalot' has been set.  Instead, we
  rely on the fact that deliver_out_1 can fire again if required, with any (possibly zero) time
  delay.

  If attempting to emit a segment when [[snd_nxt]] is past the end of the send queue and we a
  previous [[FIN]] that is unacked, then set [[snd_nxt]] temporarily to be the seq number of the
  [[FIN]] in order to construct a valid segment. This arises if a [[FIN]] was sent and the remote
  end sends a [[FIN]],[[ACK]] segment where the [[ack]] value does not acknowledge our [[FIN]]. When
  we [[ACK]] their [[FIN]] our seq number must be in range (and thus [[FIN]] should be set too)

:*);





(* combine both chunks into something a bit like tcp_output.c; sometimes useful *)

val tcp_output_perhaps_def = Phase.phase 2 Define`
(*: combination of [[tcp_output_required]] and [[tcp_output_really]] :*)
  tcp_output_perhaps arch ts_val ifds0 sock (sock',outsegs) =
    choose (do_output,persist_fun) :: tcp_output_required arch ifds0 sock.
    let sock'' =
      option_case sock (\ f. sock with <| pr := TCP_PROTO(tcp_sock_of sock with cb updated_by f) |>)
        persist_fun in
    if do_output then
      tcp_output_really arch F ts_val ifds0 sock'' (sock',outsegs)
    else
      (sock' = sock'' /\ outsegs = [])
`;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_segment_queueing]] TCP Segment Queueing

Once a segment is generated for output, it must be enqueued for
transmission.  This enqueuing may fail.  These functions model what
happens in this case, and encapsulate the
enqueuing-and-possibly-rolling-back process.

    :*)


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)


(* Don't Phase: handled specially by testEval *)
val rollback_tcp_output_def = Define`
(*: Attempt to enqueue segments, reverting appropriate socket fields if the enqueue fails :*)
  rollback_tcp_output rcvdsyn seg arch rttab ifds is_connect cb0 cb_in (cb',es',outsegs') =

    (*: NB: from [[cb0]], only [[snd_nxt]], [[tt_delack]], [[last_ack_sent]], [[rcv_adv]],
        [[tf_rxwin0sent]], [[t_rttseg]], [[snd_max]], [[tt_rexmt]] are
        used. :*)

     (choose allocated :: (if INFINITE_RESOURCES then {T} else {T;F}).
      let route = test_outroute (seg,rttab,ifds,arch) in
      let f0 = \cb. cb with <| (* revert to original values; on ip_output failure *)
                               snd_nxt       := cb0.snd_nxt;
                               (* X tt_delack     := cb0.tt_delack; X *)
                               last_ack_sent := cb0.last_ack_sent;
                               rcv_adv       := cb0.rcv_adv
                            |> in
      let f1 = \cb. if ~rcvdsyn then
                        cb
                    else
                        cb with <| (* set soft error flag; on ip_output routing failure *)
                                   t_softerror := THE route  (* assumes route = SOME (SOME e) *)
                                |> in
      let f2 = \cb. cb with <| (* revert to original values; on early ENOBUFS *)
                               tf_rxwin0sent := cb0.tf_rxwin0sent;
                               (* X t_rttseg      := cb0.t_rttseg; X *)
                               snd_max       := cb0.snd_max;
                               tt_rexmt      := cb0.tt_rexmt
                            |> in
      choose tt_rexmt' ::  start_tt_rexmt arch 0 F (* X cb.t_rttinf X *).
      let f3 = \cb. if IS_SOME cb.tt_rexmt \/ is_connect then  (* quench; on ENOBUFS *)
                        cb
                    else
                        cb with <| (* maybe start rexmt and close down window *)
                                   tt_rexmt      := tt_rexmt'
                                   (* X snd_cwnd      := cb.t_maxseg (* no LAN allowance, by design *) X *)
                                |> in
      if ~allocated then  (* allocation failure *)
          cb' = f3 (f2 (f0 cb_in)) /\ outsegs' = [] /\ es' = SOME ENOBUFS
      else if route = NONE then  (* ill-formed segment *)
          ASSERTION_FAILURE "rollback_tcp_output:1"  (* should never happen *)
      else if ?e. route = SOME (SOME e) then  (* routing failure *)
          cb' = f1 (f0 cb_in) /\ outsegs' = [] /\ es' = THE route
      else if loopback_on_wire seg ifds then (* loopback not allowed on wire - RFC1122 *)
          (if windows_arch arch then
               cb' = cb_in /\ outsegs' = [] /\ es' = NONE  (* Windows silently drops segment! *)
           else if bsd_arch arch then
               cb' = f0 cb_in /\ outsegs' = [] /\ es' = SOME EADDRNOTAVAIL
           else if linux_arch arch then
               cb' = f0 cb_in /\ outsegs' = [] /\ es' = SOME EINVAL
           else
               ASSERTION_FAILURE "rollback_tcp_output:2" (* never happen *)
          )
      else
          (?queued.
           outsegs' = [(seg,queued)] /\
           if ~queued then  (* queueing failure *)
               cb' = f3 (f0 cb_in) /\ es' = SOME ENOBUFS
           else  (* success *)
               cb' = cb_in /\ es' = NONE)
     )
`(* @description
   Attempt to enqueue segments, reverting appropriate socket fields if
   the enqueue fails.  Models failure behaviour of FreeBSD 4.6-RELEASE's
   |tcp_output()|.  We must return whether the queueing succeeded because
   in a few instances we pass the error on up.  Note that we model not
   just failure of |ip_output| with |ENOBUFS|, but also failure of
   |tcp_output| to allocate an mbuf (also |ENOBUFS|).  If enqueue fails, we
   may treat it as either of these two types of failure.  This isn't
   quite right, as the second type is not really an enqueue failure.

   Arguments: segments to emit (zero or one only!), queue on which to
   place them, original socket state (from which rollback values are
   taken), socket state at emit time.  Result (relational): resulting
   socket state, resulting queue, queueing succeeded flag.

    Roll back |tcp_output|'s behaviour if an output error
   (ENOBUFS, of whichever type, or routing failure) occurred.
    Allocation failure is decided internally; routing failure is decided
    canonically; queueing failure is decided externally.

    This code deals with allocation failure in |tcp_output|, routing
    failure, and queueing failure (due to full queue).  [[rcvdsyn]]
    should be set if [[HAVERCVDSYN]], i.e., if routing errors should be
    stored in [[t_softerror]].  [[seg]] is the segment to attempt to
    output.  [[rttab]] and [[ifds]] are from the host, for use by the
    router.  [[cb0]] is the tcpcb before [[tcp_output]], [[cb_in]] is
    that after, and [[cb']] is the output tcpcb.  [[es']] is the output
    error if any.  [[outsegs']] is the output list (empty or singleton)
    of pairs of segments and queueing success flags.
:*)
;

val enqueue_or_fail_def = Phase.phase 2 Define`
(*: wrap [[rollback_tcp_output]] together with enqueue :*)
  enqueue_or_fail rcvdsyn arch rttab ifds outsegs oq cb0 cb_in (cb',oq') =
    (case outsegs of
        []    -> cb' = cb0 /\ oq' = oq
     || [seg] -> (?outsegs' es'.
                  rollback_tcp_output rcvdsyn seg arch rttab ifds F cb0 cb_in (cb',es',outsegs') /\
                  enqueue_oq_list_qinfo (oq,outsegs',oq'))
     || _other84 -> ASSERTION_FAILURE "enqueue_or_fail" (* only 0 or 1 segments at a time *)
    )
`;


val enqueue_or_fail_sock_def = Phase.phase 2 Define`
  (*: version of [[enqueue_or_fail]] that works with sockets rather than cbs :*)
  enqueue_or_fail_sock rcvdsyn arch rttab ifds outsegs oq sock0 sock (sock',oq') =
    (*: NB: could calculate [[rcvdsyn]], but clearer to pass it in :*)
    let tcp_sock = tcp_sock_of sock in
    let tcp_sock0 = tcp_sock_of sock0 in
    (?cb'.
     enqueue_or_fail rcvdsyn arch rttab ifds outsegs oq (tcp_sock_of sock0).cb (tcp_sock_of sock).cb (cb',oq') /\
     sock' = sock with <| pr := TCP_PROTO(tcp_sock_of sock with <|
                                             cb := cb'
                        |>) |>)
`;


val enqueue_and_ignore_fail_def = Phase.phase 2 Define`
(*: version of [[enqueue_or_fail]] that ignores errors and doesn't touch the tcpcb :*)
  enqueue_and_ignore_fail arch rttab ifds outsegs oq oq' =
    ?rcvdsyn cb0 cb_in cb'.
    enqueue_or_fail rcvdsyn arch rttab ifds outsegs oq cb0 cb_in (cb',oq')
`;

val enqueue_each_and_ignore_fail_def = Phase.phase 2 Define`
(*: version of above that ignores errors and doesn't touch the tcpcb :*)
  (enqueue_each_and_ignore_fail arch rttab ifds [] oq oq' = (oq = oq')) /\
  (enqueue_each_and_ignore_fail arch rttab ifds (seg::segs) oq oq''
     = ?oq'. enqueue_and_ignore_fail arch rttab ifds [seg] oq oq' /\
             enqueue_each_and_ignore_fail arch rttab ifds segs oq' oq'')
`;


val mlift_tcp_output_perhaps_or_fail_def = Phase.phase 2 Define`
(*: do mliftc for function returning at most one segment and not dealing with queueing flag :*)
  mlift_tcp_output_perhaps_or_fail ts_val arch rttab ifds0 =
    mliftc (\ s (s',outsegs').
              ?s1 segs.
              tcp_output_perhaps arch ts_val ifds0 s (s1,segs) /\
              case segs of
                 []       -> s' = s1 /\ outsegs' = []
              || [seg]    -> (?cb' es'.  (* ignore error return *)
                              rollback_tcp_output T seg arch rttab ifds0 F
                                                  (tcp_sock_of s).cb (tcp_sock_of s1).cb (cb',es',outsegs') /\
                              s' = s1 with <| pr := TCP_PROTO(tcp_sock_of s1 with <| cb := cb' |>) |>)
              || _other58 -> ASSERTION_FAILURE "mlift_tcp_output_perhaps_or_fail"  (* never happen *)
           )
`;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_incoming_segment]] TCP Incoming Segment Functions

Updates performed to the idle, keepalive, and |FIN_WAIT_2| timers for
every incoming segment.

     :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* Don't Phase: handled by testEval *)
val update_idle_def = Define`
(*: Do updates appropriate to receiving a new segment on a connection :*)
  update_idle tcp_sock =
    let t_idletime' = stopwatch_zero in     (*: update 'time most recent packet received' field :*)
    let tt_keep' = (if ~(tcp_sock.st = SYN_RECEIVED /\ tcp_sock.cb.tf_needfin) then
                      (*: reset keepalive timer to 2 hours. :*)
                      SOME (Timed((),slow_timer TCPTV_KEEP_IDLE))
                    else
                      tcp_sock.cb.tt_keep) in
    let tt_fin_wait_2' = (if tcp_sock.st = FIN_WAIT_2 then
                            SOME (Timed((),slow_timer TCPTV_MAXIDLE))
                          else
                            tcp_sock.cb.tt_fin_wait_2) in
    (t_idletime', tt_keep', tt_fin_wait_2')
`;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_drop_segment]] TCP Drop Segment Functions

When an erroneous or unexpected segment arrives, it is usually dropped
(i.e, ignored).  However, the peer is usually informed immediately by
means of a RST or ACK segment.

     :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)


val dropwithreset_def = Phase.phase 2 Define`
(*: emit a RST segment corresponding to the passed segment, unless that would be stupid. :*)
  dropwithreset seg ifds0 ticks reason bndlm bndlm' outsegs =
   (*: Needs list of the host's interfaces, to verify that the incoming segment wasn't broadcast.
   Returns a list of segments. :*)

    if  (* never RST a RST *)
        seg.RST \/
        (* is segment a (link-layer?) broadcast or multicast? *)
        F \/
        (* is source or destination broadcast or multicast? *)
        (?i1. seg.is1 = SOME i1 /\ is_broadormulticast FEMPTY i1) \/
        (?i2. seg.is2 = SOME i2 /\ is_broadormulticast ifds0 i2)
          (* BSD only checks incoming interface, but should have same effect as long as interfaces don't overlap *)
    then
        outsegs = [] /\ bndlm' = bndlm
    else
        (choose seg' :: make_rst_segment_from_seg seg.
        let (emit,bndlm'') = bandlim_rst_ok(seg',ticks,reason,bndlm) in  (* finally: check if band-limited *)
        bndlm' = bndlm'' /\
        outsegs = if emit then [TCP seg'] else [])
`;





val mlift_dropafterack_or_fail_def = Phase.phase 2 Define`
(*: send immediate ACK to segment, but otherwise process it no further :*)
  mlift_dropafterack_or_fail seg arch rttab ifds ticks (sock,bndlm) ((sock',bndlm',outsegs'),continue) =
   (*:    [[ifds]] is just in case we need to send a RST, to make sure we don't
   send it to a broadcast address. :*)
   let tcp_sock = tcp_sock_of sock in
    (continue = T /\
     let cb = tcp_sock.cb in
     if tcp_sock.st = SYN_RECEIVED /\
        seg.ACK /\
        (let ack = tcp_seq_flip_sense seg.ack in
          (ack < cb.snd_una \/ cb.snd_max < ack))
     then
         (*: break loop in "LAND" DoS attack, and also prevent ACK
            storm between two listening ports that have been sent
            forged SYN segments, each with the source address of
            the other. (|tcp_input.c:2141|) :*)
         sock' = sock /\
         dropwithreset seg ifds ticks BANDLIM_RST_OPENPORT bndlm bndlm' (MAP FST outsegs')
              (* ignore queue full error *)
     else
         (?sock1 msg cb' es'.  (* ignore errors *)
          let tcp_sock1 = tcp_sock_of sock1 in
          tcp_output_really arch F ticks ifds sock (sock1,[msg]) /\  (*: did set [[tf_acknow]] and call [[tcp_output_perhaps]], which seemed a bit silly :*)
          (*: notice we here bake in the assumption that the timestamps use the same counter as the band limiter; perhaps this is unwise :*)
          rollback_tcp_output T msg arch rttab ifds F tcp_sock.cb tcp_sock1.cb (cb',es',outsegs') /\
          sock' = sock1 with <| pr := TCP_PROTO(tcp_sock1 with <| cb := cb' |>) |> /\
          bndlm' = bndlm))
`;


val dropwithreset_ignore_fail_def = Phase.phase 2 Define`
(*: do [[emit_segs_pred]], for function returning at most one seg and not dealing with queueing flag :*)
  dropwithreset_ignore_fail seg_in arch ifds rttab ticks reason b b' (outsegs':(msg # bool) list) =
  (*:  No rollback necessary here. :*)
    ?segs.
    dropwithreset seg_in ifds ticks reason b b' segs /\
    case segs of
       []       -> outsegs' = []
    || [seg]    -> (choose allocated :: if INFINITE_RESOURCES then {T} else {T;F}.
                    if ~allocated then
                        outsegs' = []
                    else
                        (case test_outroute (seg,rttab,ifds,arch) of
                            NONE          -> ASSERTION_FAILURE "dropwithreset_ignore_fail:1"  (* never happen *)
                         || SOME (SOME e) -> outsegs' = []  (* ignore error *)
                         || SOME NONE     -> ?queued. outsegs' = [(seg,queued)]))
    || _other57 -> ASSERTION_FAILURE "dropwithreset_ignore_fail:2"  (* never happen *)
`;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[tcp_close]] TCP Close Functions

Closing a connection, updating the socket and TCP control block
appropriately.

     :*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* Don't Phase: handled by testEval *)
val tcp_close_def = Define`
(*: close the socket and remove the TCPCB :*)
  tcp_close arch sock = sock with
    <| cantrcvmore := T; (* MF doesn't believe this is correct for Linux or WinXP *)
       cantsndmore := T;
       is1 := if bsd_arch arch then NONE else sock.is1;
       ps1 := if bsd_arch arch then NONE else sock.ps1;
       pr := TCP_PROTO(tcp_sock_of sock with
         <| st := CLOSED;
            cb := initial_cb with (* in reality, it's dropped entirely, but we don't do that *)
                  <| bsd_cantconnect := if bsd_arch arch then T else F |> ;
            sndq := [] |>)
     |>
`(*: @description
   This is similar to BSD's |tcp_close()|, except
   that we do not actually remove the protocol/control blocks. The quad of the socket is
   cleared, to enable another socket to bind to the port we were previously using --- this
   isn't actually done by BSD, but the effect is the same. The [[bsd_cantconnect]] flag is
   set to indicate that the socket is in such a detached state. :*)
;



(* Don't Phase: handled by testEval *)
val tcp_drop_and_close_def = Define`
(*: drop TCP connection, reporting the specified error.  If synchronised, send RST to peer :*)
  tcp_drop_and_close arch err sock (sock',outsegs) =
    let tcp_sock = tcp_sock_of sock in (
      (if tcp_sock.st NOTIN {CLOSED;LISTEN;SYN_SENT} then
         (choose seg :: (make_rst_segment_from_cb tcp_sock.cb
                          (THE sock.is1, THE sock.is2, THE sock.ps1, THE sock.ps2)).
          outsegs = [TCP seg])
       else
          outsegs = []) /\
    let es' =
      if err = SOME ETIMEDOUT then
       (if tcp_sock.cb.t_softerror <> NONE then
          tcp_sock.cb.t_softerror
        else
          SOME ETIMEDOUT)
      else if err <> NONE then err
      else sock.es
    in
      sock' = tcp_close arch (sock with <| es := es' |>))
`(*: @description
 BSD calls this |tcp_drop| :*)
;

(* --- TIDY: SB has tidied up the layout and comments down to here --- *)






(* -------------------------------------------------- *)

val _ = export_theory();
