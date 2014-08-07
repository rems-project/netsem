

(* sketches for an implementation of TCP, directly from RFC 793. *)

(* hacks to get this to compile *)

type word32=int
type word16=int
type word6=int
type word4=int



(* want to do this all with pure functions, so wrap any OCaml library
   functions that may raise exceptions *)

let list_assoc a l = try Some(List.assoc a l) with Not_found -> None 


exception UNFINISHED;;

(* translating TNet_typesScript.sml *)

type port = Port of int    (* really want 1..65535  *)
type ip = IP of int32      (* really want 1..2^32-1 *)

type ipBody = 
    UDP of port option * port option * char list   
  | ICMP_HOST_UNREACH of ip * port option * ip * port option
  | ICMP_PORT_UNREACH of ip * port option * ip * port option
   
  (* use char list not string, as OCaml strings are mutable *)

  (* for this faithful-to-the-wire stuff, it would be better to have
  ip option above, but I'll leave it for now so as not to have to
  make umpteen tiny changes *)

type msg = { src : ip; dest : ip; body : ipBody; }

let mk_ip(src,dest,body) = {src=src; dest=dest; body=body;}

type ifid = LO | ETH of int 
type netmask = NETMASK of int32
type ifd = { ifid : ifid ; ipset : ip list ;
                               primary : ip ; netmask : netmask ;}

  (* really should use an abstract type of sets not ip list there *)

type fd = FD of int 

type error = 
    EACCES
  | EADDRINUSE
  | EADDRNOTAVAIL
  | EAGAIN
  | EBADF
  | ECONNREFUSED
  | EHOSTUNREACH
  | EINTR
  | EINVAL
  | EMFILE
  | EMSGSIZE
  | ENFILE
  | ENOBUFS
  | ENOMEM
  | ENOTCONN
  | ENOTSOCK

type 'a err = OK of 'a | FAIL of error

type sockopt = SO_BSDCOMPAT | SO_REUSEADDR

type flags = { bsdcompat : bool ; reuseaddr : bool ; }

let mk_flags(bsdcompat,reuseaddr)  =
  { bsdcompat = bsdcompat;
     reuseaddr = reuseaddr; }

type socket = { fd : fd ;
               is1 : ip option ; ps1 : port option;
               is2 : ip option ; ps2 : port option;
               es : error option; f : flags; mq : (msg * ifid) list ;}


let mk_sock(fd,is1,ps1,is2,ps2,es,f,mq)  =
  { fd  = fd;
     is1 = is1; ps1 = ps1;
     is2 = is2; ps2 = ps2;
     es  = es;
     f   = f;
     mq  = mq ; }

type tid = TID of int


(* skipping over lang typing and okness *)

type time = float

  (* float ?! *)

type 'a timed = Timed of 'a * time

let dsched = 1.0

(* experiment with coding all the return types we use into a single
ret type rather than a more general thing *)

type ret = Return_unit of unit err


type hostThreadState = 
    Run
  | Exit
  | Zombie
  | Ret of ret
  | Sendto2 of (fd * (ip * port) option *
                  ip option * port option *
                  ip option * port option *
                  char list )   
  | Recvfrom2 of fd
  | Select2 of (fd list * fd list)
  | Delay2
  | Print2 of char list

  (* again char list not string above*)


type host = 
    { 
      ifds : ifd list   ;   (* should really be a set? originally ifd -> bool *)
      ts : (tid * hostThreadState timed) list ;  (* should really be a finite map ?*)
      s : socket list;       (* what is the ordering data here? *)
      oq : msg list timed ;
      oqf : bool ;}


(* skip over all ok defns, though really should turn into computable
predicates and assert them frequently *)



(* from TNet_auxfnsScript.sml *)
   (* just things we need later *)


let find_socket : host*fd -> (socket * socket list) option 
      = fun (h,fd) -> raise UNFINISHED

let update_ts : (tid * hostThreadState timed) list -> tid -> hostThreadState timed -> 
  (tid * hostThreadState timed) list
    = raise UNFINISHED 

let autobind : port option * socket list -> port
      = raise UNFINISHED

let dosend _ = raise UNFINISHED


(* from TNet_LIBinterfaceScript.sml *)
   (* again just being shallow *)

type lib_interface =
    Socket of unit
  | Bind of (fd *  ip option * port option)
  | Connect of (fd * ip * port option)
  | Disconnect of fd
  | Getsockname of fd
  | Getpeername of fd
  | Sendto of (fd * (ip * port) option * char list * bool)
  | Recvfrom of (fd * bool)
  | Geterr of fd
  | Getsockopt of (fd * sockopt)
  | Setsockopt of (fd * sockopt * bool)
  | Close of fd
  | Select of (fd list * fd list * int option)  (* time in usec *)
  | Delay of int (* time in usec *)
  | Port_of_int of int
  | Ip_of_string of char list
  | Getifaddrs of unit
  | Print_endline_flush of char list
  | Create of unit
  | ExitCall of unit  (* irritating OCaml constructor semantics *)

  (* char list replacing string.  initial caps. *)



(* from TNet_hostLTSScript.sml *)

let uDPpayloadMax = 65507

let execute_lib :  host -> tid -> lib_interface -> host option

   (* not going to use this for nonexistent tids or tids not in the
   run state.  To make it a total function, therefore, make the result
   type an option.  This will be ugly, but the alternatives (eg making
   it the identity function on hosts in those cases) seem even more
   ugly. *)



    = fun h tid call -> 

      match list_assoc tid (h.ts) with
        None -> None
      | Some(Timed(Exit ,d)) -> None
      | Some(Timed(Zombie ,d)) -> None
      | Some(Timed(Ret _ ,d)) -> None
      | Some(Timed(Sendto2 _,d)) -> None
      | Some(Timed(Recvfrom2 _,d)) -> None
      | Some(Timed(Select2 _,d)) -> None
      | Some(Timed(Delay2,d)) -> None
      | Some(Timed(Print2 _,d)) -> None
      | Some(Timed(Run ,d)) -> 
      (* didn't want to use a wildcard as wanted this all before the meat *)

          Some(match call with 
            Sendto(fd,ips,data,nb) -> (
              match find_socket(h,fd) with
                None -> raise UNFINISHED (* notsockfd_2 *)
              | Some (s,ss) -> (
                  if not(s.es = None) then raise UNFINISHED (* sendto_5 *)
                  else
                    let p1'=autobind(s.ps1,ss) in
                    match dosend(h.ifds, (ips, data),
                      (s.is1, Some p1', s.is2, s.ps2), h.oq, h.oqf) with
                      None ->  raise UNFINISHED (* sendto_3 *)
                    | Some(oq',oqf') -> 
                        if List.length data > uDPpayloadMax then raise UNFINISHED (* sendto_6 *)
                        else
                          if (not(ips =None) || not(s.is2=None)) then raise UNFINISHED (* sendto_4 *)
                          else
                            let s' = {s with  ps1 = Some p1'} in            (* es := NONE *)
                            let ts' = update_ts h.ts tid (Timed(Ret (Return_unit(OK ())),dsched)) in
                            { h with ts=ts';  s=s'::ss; oq=oq'; oqf=oqf' }
                 ))
          | _ -> raise UNFINISHED)
     

(* and here's the original 

   (!SC h ts tid d s ips data nb oq' oqf' p1'.

   sendto_1 /* succeed (*: autobinding :*) */
      h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                s := SC (s with es := NONE) |>


    -- Lh_call (tid,sendto(s.fd,ips,data,nb)) -->

      h with <| ts := FUPDATE ts (tid, Timed(Ret (OK ()),dsched));
                s := SC (s with <| es := NONE; ps1 := SOME p1' |>);
                oq := oq'; oqf := oqf' |>


    <==

      socklist_context SC /\
      p1' IN autobind(s.ps1, SC) /\
      (oq', oqf', T) IN dosend(h.ifds, (ips, data),
                               (s.is1, SOME p1', s.is2, s.ps2),
                               h.oq, h.oqf) /\
      STRLEN data <= UDPpayloadMax /\
      ((ips <> NONE) \/ (s.is2 <> NONE))

    )

*)


(* so could add sugar for finite-map or list-context patterns? *)

(* for symbolic execution by some unification-based thing, might be handy to:

- use utterly concrete representations, eg association lists that are
  kept in a canonical order (from an order on their key components)

- ?? have subranges coded into the syntax, eg  port = Priv of 1..1023 | ...
  or have extra predicates floating about?

*)





type tcp_protocol_state = 
    LISTEN       
  | SYN_RCVD    
  | SYN_SENT
  | ESTABLISHED  
  | CLOSE_WAIT   
  | LAST_ACK
  | FIN_WAIT_1   
  | FIN_WAIT_2
  | CLOSING
  | TIME_WAIT

(* put mss into tcp_segment explicitly, instead of having a list of options like this 
type tcp_option = End_of_option_list | No_operation | MSS of word16
*)

type tcp_segment = {
    is1 : ip option ;
    is2 : ip option ;
    ps1 : port option;
    ps2 : port option;
    seq : word32;         (* sequence_number       *)
    ack : word32;         (* acknowledgment_number *)
    len : word32;         (* length                *)
    wnd : word16;         (* window_size           *)
    up  : word16;         (* urgent_pointer        *) 
    urg_flag : bool;  ack_flag : bool;  psh_flag : bool;  
    rst_flag : bool;  syn_flag : bool;  fin_flag : bool;
(*    data_offset : word4; *)
    reserved : word6;
    checksum : word16;

    mss : word16 option ;
    wscale : word8 option ; (* really {0..14} option *)
    timestamp : (word32 * word32) option ; 

    data : char list;
  } 

  (* includes data from IP and TCP headers, and the body.  enough to get a bijection?
   ugh

  do we keep the actual data here, or in send/recv buffers?  Here makes things more orthogonal

  have all the is1 etc here, just in case they might vary?

  should wnd and up be word32?
  *)

 

type tcp_state = { 
    is1 : ip option ; 
    ps1 : port option;
    is2 : ip option ; 
    ps2 : port option;
    state : tcp_protocol_state;

    (* stuff to queue incoming connections.  This is used only in
    LISTEN states(?).  As far as I can see the queues are just lists
    of socket_id; we make up a new socket as soon as an incoming SYN
    appears *)

    backlog : int ;   
    incomplete_connection_queue : socket_id list ;
    complete_connection_queue : socket_id list;


    (* stuff for data flow *)

    snd_una : word32; (* send unacknowledged                                 *)
    snd_nxt : word32; (* send next                                           *)
    snd_wnd : word32; (* send window                                         *)
    snd_up  : word32; (* send urgent pointer                                 *)
    snd_wl1 : word32; (* segment sequence number used for last window update *)
    snd_wl2 : word32; (* segment acknowledgment number used for last window  *)
                      (*        update                                       *)
    iss     : word32; (* initial send sequence number                        *)
    rcv_nxt : word32; (* receive next                                        *)
    rcv_wnd : word32; (* receive window                                      *)
    rcv_up  : word32; (* receive urgent pointer                              *)
    irs     : word32; (* initial receive sequence number                     *)

    retransmission_q : tcp_segment list;
  } 

       (* comments and names mostly from RFC793 3.2 - there SND.UNA etc *)
       (* see also linux source C&P p494 *)

       (* have to choose whether this structure is flat or whether it
       depends on the tcp_protocol_state.  at the momement I'm
       guessing that flat is simpler *)


(* let's try a transition or two.  from rfc0793 page 65

*******************************
*
* Suppose  tcp.state = LISTEN and we get a seg : tcp_segment.
*
*******************************

if seg.rst_flag then discard this seg

else if seg.ack_flag then construct a seg' with 
    seg'.seq=seg.ack
    seg'.rst_flag = true
    ...?...
  and send it, then discard this seg

else if seg.syn_flag then 
  - make up a new socket tcp', much like tcp, and mess with the connection queues

  - choose an iss value

  - construct a new seg' with
      seg'.seq=iss
      seg'.ack=seg.seq+1
      seg'.syn_flag=true
      seg'.ack_flag=true
    and send it

  - tcp'.rcv_nxt := seg.seq + 1
    tcp'.irs     := seg.seq
    tcp'.iss     := iss
    tcp'.snd_nxt := iss +1
    tcp'.snd_una := iss
    tcp'.state   := SYN_RECEIVED  
 
  - fill in any is2,ps2 if required

  - make a seg'' by erasing the syn_flag and ack_flag and put it at
    the front of the tcp' queue (!!) to be processed in the SYN_RECEIVED
    state


*******************************
*
* Suppose  tcp.state = SYN_RECEIVED and we get a seg : tcp_segment.
*
*******************************





*******************************
*
* Suppose  tcp.state = ESTABLISHED and we get a seg : tcp_segment.
*
*******************************

the RFC description here starts on [Page 69].  It squishes together
processing that is common to a number of tcp_protocol_states, but I'll
ignore all except the ESTABLISHED parts.


acceptable(tcp,seg) iff
    (seg.len = 0 && tcp.rcv_wnd =0  && seg.seq=tcp.rcv_nxt) 
 || (seg.len = 0 && tcp.rcv_wnd >0  
          && tcp.rcv_nxt <= seg.seq             < tcp.rcv_nxt+tcp.rcv_wnd )
 || (seg.len > 0 && tcp.rcv_wnd >0  
    && (    (tcp.rcv_nxt <= seg.seq             < tcp.rcv_nxt+tcp.rcv_wnd )
         || (tcp.rcv_nxt <= seg.seq +seg.len -1 < tcp.rcv_nxt+tcp.rcv_wnd )))

ignore chat about 'special allowance should be made to accept valid
ACKS URGs RSTs'

check acceptable(tcp,seq) and not(seg.rst_flag) and not(seq.syn_flag)
      and seg.ack_flag (otherwise do some error processing)


ignore chat about 'if the segment ack is not acceptable'


ack processing:

case  tcp.snd_una < seg.ack <= tcp.snd_nxt   (otherwise ???)

   remove fully-acked segments from tcp.retransmission_q 

   'users should receive positive acknowledments for buffers that have
   been sent and fully acknowledged' -- but sockets doesn't, AFAIK

   update send window: 

    if (tcp.snd_wl1 < seg.seq || (tcp.snd_wl1=seg.seq && tcp.snd_wl2<=seg.ack))
    then 
       tcp.snd_wnd := seg.wnd
       tcp.snd_wl1 := seg.seq
       tcp.snd_wl2 := seg.ack
    else ??? (unspecified)

case  tcp.snd_una = seg.ack    (unspecified !!!!)


case  tcp.snd_una > seg.ack   (duplicate ack)

   ignore the ack

case  seg.ack > tcp.snd_nxt   (ack of something not yet sent)

   send an ack, drop the segment


urg processing:

  I'll skip over

text processing:

  move as much as possible into the receive buffer.  Say this is n bytes.

  (if that doesn't exhaust seg then keep the rest hanging around...?)

  tcp.rcv_nxt += n
  tcp.rcv_wnd = ...?

  make up an ack seg' with
    seg'.seq=tcp.snd_nxt
    seg'.ack=tcp.rcv_nxt
    seg'.ack_flag = true
  and send it



fin processing:
 
  I'll skip over




