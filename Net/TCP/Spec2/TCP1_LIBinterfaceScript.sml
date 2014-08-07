(* A HOL98 specification of TCP *)

(* Type declarations and groups of system ("LIB") calls *)

(*[ RCSID "$Id: TCP1_LIBinterfaceScript.sml,v 1.2 2005/07/13 12:24:40 tjr22 Exp $" ]*)

open HolKernel Parse boolLib

local open TCP1_baseTypesTheory in end

open bossLib

open HolDoc

val _ = new_theory "TCP1_LIBinterface";

val _ = Version.registerTheory "$RCSfile: TCP1_LIBinterfaceScript.sml,v $" "$Revision: 1.2 $" "$Date: 2005/07/13 12:24:40 $";

(*: @chapter [[TCP1_LIBinterface]] System call types

This file gives the system call API that is modelled by the
specification.
:*)

(* Michael: is there a nicer way we can present this, so we can write
   something like "socket : one -> fd" etc and derive LIB_interface
   and retType from this? *)

(* why does Peter's OCaml use "ip lift", whereas Net_LIB used "ip option"? *)

(* based on interface.ml *)

(*: @section [[lib_interface]] ALL The interface

The Sockets API is modelled by the library interface below.  As
discussed in volume 1, we refine the C interface slightly:
\begin{itemize}

\item We use ML-style datatypes, abstracting from pointers and length
parameters.

\item Where the C API provides multiple entry points to a single
operation (such as |send|/|sendto|/|sendmsg|/|write|, or
|pselect|/|select|) we combine them all into a single general
function.

\item Certain special cases of general functions (such as |getsockopt|
with |SO_ERROR|, |ioctl| with |SIOCATMARK|, and |fcntl| with
|F_GETFL|) have been pulled out into separate functions
([[getsockerr]], [[sockatmark]] (following POSIX), and
[[getfileflags]] respectively).

\item Features not relevant to TCP or UDP (e.g. Unix domain sockets), or
historical artifacts (such as the address family / protocol family
distinction in |socket|) are elided.
\end{itemize}

The HOL type [[LIB_interface]] defines the calls. It
takes their arguments to be the relevant HOL types (rather than values
of [[TLang]]) so that HOL typechecking ensures consistency.  The return
types of the calls cannot be embedded so neatly within the HOL type
system, so an additional [[retType]] function defines these (and HOL
typechecking does not check this data at present).

:*)

val _ =
    Hol_datatype
    `LIB_interface =
        accept       of fd
      | bind         of (fd # ip option # port option)
      | close        of fd
      | connect      of (fd # ip # port option)
      | disconnect   of fd
      | dup          of fd
      | dupfd        of (fd # int)
      | getfileflags of fd
      | getifaddrs   of one
      | getpeername  of fd
      | getsockbopt  of (fd # sockbflag)
      | getsockerr   of fd
      | getsocklistening of fd
      | getsockname  of fd
      | getsocknopt  of (fd # socknflag)
      | getsocktopt  of (fd # socktflag)
      | listen       of (fd # int)
      | pselect      of (fd list # fd list # fd list # (int # int) option # signal list option)
      | recv         of (fd # int # msgbflag list)
      | send         of (fd # (ip # port) option # string # msgbflag list)
      | setfileflags of (fd # filebflag list)
      | setsockbopt  of (fd # sockbflag # bool)
      | setsocknopt  of (fd # socknflag # int)
      | setsocktopt  of (fd # socktflag # (int # int) option)
      | shutdown     of (fd # bool # bool)
      | sockatmark   of fd
      | socket       of socktype
`
(*: @description
Sockets calls with their argument types.
:*)
;





(*
      (* and now the non-POSIX stuff: *)
      | port_of_int         of int
      | int_of_port         of port
      | ip_of_string        of string
      | string_of_ip        of ip
      | int_of_fd           of fd
   (* NB: fd_of_int is deliberately omitted; see dupfd *)
   (* | create              of ('a -> 'b # 'a)   *)
      | delay               of int
      | print_ef            of string
      | exit                of one

   (* | getaddrinfo of ????                  *)
   (* | poll        of (fd # event) list ??? *)
*)

val retType_def =
  Define`retType (accept      _) = TLty_pair(TLty_fd,TLty_pair(TLty_ip, TLty_port))
      /\ retType (bind        _) = TLty_one
      /\ retType (close       _) = TLty_one
      /\ retType (connect     _) = TLty_one
      /\ retType (disconnect  _) = TLty_one
      /\ retType (dup         _) = TLty_fd
      /\ retType (dupfd       _) = TLty_fd
      /\ retType (getfileflags _) = TLty_list TLty_filebflag
      /\ retType (getifaddrs          _) = TLty_list
             (TLty_pair(TLty_ifid,TLty_pair(TLty_ip,TLty_pair((TLty_list TLty_ip),TLty_netmask))))
      /\ retType (getpeername _) = TLty_pair(TLty_ip, TLty_port)
      /\ retType (getsockbopt _) = TLty_bool
      /\ retType (getsockerr  _) = TLty_one
      /\ retType (getsocklistening _) = TLty_bool
      /\ retType (getsockname _) = TLty_pair(TLty_lift TLty_ip, TLty_lift TLty_port)
      /\ retType (getsocknopt _) = TLty_int
      /\ retType (getsocktopt _) = TLty_lift (TLty_pair(TLty_int,TLty_int))
      /\ retType (listen      _) = TLty_one
      /\ retType (pselect     _) = TLty_pair(TLty_list TLty_fd,
                                             TLty_pair(TLty_list TLty_fd,
                                                       TLty_list TLty_fd))
      /\ retType (recv        _) = TLty_pair (TLty_string,
                                              TLty_lift(TLty_pair(TLty_pair(TLty_ip,
									    TLty_port),
								  TLty_bool)))
      /\ retType (send        _) = TLty_string
      /\ retType (setfileflags _) = TLty_one
      /\ retType (setsockbopt _) = TLty_one
      /\ retType (setsocknopt _) = TLty_one
      /\ retType (setsocktopt _) = TLty_one
      /\ retType (shutdown    _) = TLty_one
      /\ retType (sockatmark  _) = TLty_bool
      /\ retType (socket      _) = TLty_fd


     `
(*: @description
Return types of sockets calls.
:*)
;



(*

(*    /\ retType (getaddrinfo _) = TLty_???? *)
(*    /\ retType (poll        _) = TLty_???? *)

    (* and now the non-POSIX stuff: *)
      /\ retType (port_of_int         _) = TLty_err TLty_port
      /\ retType (int_of_port         _) = TLty_int
      /\ retType (ip_of_string        _) = TLty_err TLty_ip
      /\ retType (string_of_ip        _) = TLty_string
      /\ retType (int_of_fd           _) = TLty_int
(*    /\ retType (create              _) = TLty_tid                           *)
      /\ retType (delay               _) = TLty_one
      /\ retType (print_ef            _) = TLty_err TLty_one
      /\ retType (exit                _) = TLty_void
*)


(*: @section [[lib_groups]] ALL Useful groups of calls
For some purposes it is useful to group together all the system calls
that expect a single [[fd]], and those that expect a socket [[fd]].
:*)

val fd_op_def = Define`
  fd_op fd opn = (
    opn = accept(fd) \/
    (?is ps. opn = bind(fd,is,ps)) \/
    opn = close(fd) \/
    (?i p. opn = connect(fd,i,p)) \/
    opn = disconnect(fd) \/
    opn = dup(fd) \/
    (?fd'. opn = dupfd(fd,fd')) \/
    (opn = getfileflags(fd)) \/
    (?flags. opn = setfileflags(fd,flags)) \/
    opn = getsockname(fd) \/
    opn = getpeername(fd) \/
    (?sfb. opn = getsockbopt(fd,sfb)) \/
    (?sfn. opn = getsocknopt(fd,sfn)) \/
    (?sft. opn = getsocktopt(fd,sft)) \/
    (?sfb b. opn = setsockbopt(fd,sfb,b)) \/
    (?sfn n. opn = setsocknopt(fd,sfn,n)) \/
    (?sft t. opn = setsocktopt(fd,sft,t)) \/
    (?n. opn = listen(fd,n)) \/
    (?n opt. opn = recv(fd,n,opt)) \/
    (?data opt. opn = send(fd,data,opt)) \/
    (?r w. opn = shutdown(fd,r,w)) \/
    opn = sockatmark(fd) \/
    opn = getsockerr(fd) \/
    opn = getsocklistening(fd)
)`
(*: @description
Calls that expect a (single) fd.
:*)
;


   (* | getaddrinfo of ????                  *)
   (* | poll        of (fd,event) list ??? *)
    (* NOT pselect *)
    (* NOT socket *)
    (* NOT the non-POSIX ones *)

val fd_sockop_def = Define`
  fd_sockop fd opn = (
    opn = accept(fd) \/
    (?is ps. opn = bind(fd,is,ps)) \/
    (?i p. opn = connect(fd,i,p)) \/
    opn = disconnect(fd) \/
    opn = getsockname(fd) \/
    opn = getpeername(fd) \/
    (?sfb. opn = getsockbopt(fd,sfb)) \/
    (?sfn. opn = getsocknopt(fd,sfn)) \/
    (?sft. opn = getsocktopt(fd,sft)) \/
    (?sfb b. opn = setsockbopt(fd,sfb,b)) \/
    (?sfn n. opn = setsocknopt(fd,sfn,n)) \/
    (?sft t. opn = setsocktopt(fd,sft,t)) \/
    (?n. opn = listen(fd,n)) \/
    (?n opt. opn = recv(fd,n,opt)) \/
    (?data opt. opn = send(fd,data,opt)) \/
    (?r w. opn = shutdown(fd,r,w)) \/
    opn = sockatmark(fd) \/
    opn = getsockerr(fd) \/
    opn = getsocklistening(fd)
)`
(*: @description
Calls that expect a (single) socket fd.
:*)
;


    (* NOT close *)
    (* NOT dup *)
    (* NOT dupfd *)
    (* NOT getfileflags *)
    (* NOT setfileflags *)
   (* | getaddrinfo of ????                  *)
   (* | poll        of (fd,event) list ??? *)
    (* NOT pselect *)
    (* NOT socket *)
    (* NOT the non-POSIX ones *)


val _ = export_theory();
