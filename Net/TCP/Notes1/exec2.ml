

(* sketches for an implementation of UDP, by hand-translation from our
HOL model.  14 May 2002 *)


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

