(* A HOL98 specification of TCP *)

(* Basic types used in the specification, including language types and time types *)

(*[ RCSID "$Id: TCP1_baseTypesScript.sml,v 1.66 2009/02/17 11:56:46 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

local open TCP1_errorsTheory TCP1_signalsTheory TCP1_utilsTheory in end

local open arithmeticTheory stringTheory pred_setTheory integerTheory
           finite_mapTheory realTheory in end;

val _ = new_theory "TCP1_baseTypes";

val _ = Version.registerTheory "$RCSfile: TCP1_baseTypesScript.sml,v $" "$Revision: 1.66 $" "$Date: 2009/02/17 11:56:46 $";

(*: @chapter [[TCP1_baseTypes]] Base types

This file defines basic types used throughout the specification.
%including
%types for ports, IP addresses, and file descriptors; types of file and socket flags used in the sockets API;
%
%
%the language types and the time and duration
%types.

:*)

(* -------------------------------------------------- *)
(*                       TYPES REQUIRED FOR TL        *)
(* -------------------------------------------------- *)

(*: @section [[base_os]] ALL Network and OS-related types

The specification distinguishes between the types [[port]] and [[ip]],
for which we do not use the zero values, and option types [[port option]] and
[[ip option]], with values [[NONE]] (modelling the zero values) and [[SOME p]] and [[SOME i]], modelling the non-zero values.
Zero values are used as wildcards in some places and are forbidden in others;
this typing lets that be captured explicitly.
:*)

val _ = Hol_datatype `port = Port of num (*: really 16 bits, non-zero :*)`
(*: @description
TCP or UDP port number, non-zero.
:*)
;
val _ = Hol_datatype `ip   = ip of num (*: really 32 bits, non-zero :*)`
(*: @description
IPv4 address, non-zero.
:*)
;

val _ = Hol_datatype `ifid = LO | ETH of num`
(*: @description
Interface ID: either the loopback interface, or a numbered Ethernet interface.
:*)
;

val _ = Hol_datatype `netmask = NETMASK of num`
(*: @description
Network mask, represented as the number of 1 bits (as in a CIDR /nn
suffix).
:*)
;

val _ = Hol_datatype `fd = FD of num`
(*: @description
File descriptor.  On Unix-like systems this is a small nonnegative
integer; on Windows it is an arbitrary handle.

@internal
     This was FD of int, but I can't find any rationale for the
     choice.  It's an index into a table of open file descriptions,
     and so can't by definition be negative.
:*)
;


(*: @section [[base_flags]] ALL File and socket flags

This defines the types of various flags used in the sockets API: file flags, socket flags, message flags (used in [[send]] and [[recv]] calls), and socket types (used in [[socket]] calls).  The socket flags are partitioned into those with boolean, natural-number and time-valued arguments.
:*)

val _ = Hol_datatype
  `filebflag = O_NONBLOCK
             | O_ASYNC
`
(*: @description
Boolean flags affecting the behaviour of an open file (or socket).

[[O_NONBLOCK]] makes all operations on this file (or socket) nonblocking.

[[O_ASYNC]] specifies whether signal driven I/O is enabled.

:*)
;

val _ = Hol_datatype
  `sockbflag = SO_BSDCOMPAT (* Linux only *)
             | SO_REUSEADDR
             | SO_KEEPALIVE
             | SO_OOBINLINE (* ? *)
             | SO_DONTROUTE
`
(*: @description
Boolean flags affecting the behaviour of a socket.

     [[SO_BSDCOMPAT]] Specifies whether the BSD semantics for delivery of ICMPs to UDP sockets
     with no peer address set is enabled.

     [[SO_DONTROUTE]] Requests that outgoing messages bypass the standard routing
     facilities. The destination shall be on a directly-connected network, and messages are directed
     to the appropriate network interface according to the destination address.

    [[SO_KEEPALIVE]] Keeps connections active by enabling the periodic transmission of
     messages, if this is supported by the protocol.

     [[SO_OOBINLINE]] Leaves received out-of-band data (data marked urgent) inline.

     [[SO_REUSEADDR]] Specifies that the rules used in validating addresses supplied to
     [[bind()]] should allow reuse of local ports, if this is supported by the protocol.


@variation Linux
The flag [[SO_BSDCOMPAT]] is Linux-only.
:*)
;

val _ = Hol_datatype
  `socknflag = SO_SNDBUF
             | SO_RCVBUF
             | SO_SNDLOWAT
             | SO_RCVLOWAT
`
(*: @description
Natural-number flags affecting the behaviour of a socket.

     [[SO_SNDBUF]] Specifies the send buffer size.

     [[SO_RCVBUF]] Specifies the receive buffer size.

     [[SO_SNDLOWAT]] Specifies the minimum number of bytes to process for socket output
      operations.

     [[SO_RCVLOWAT]] Specifies the minimum number of bytes to process for socket input
     operations.
:*)
;

val _ = Hol_datatype
  `socktflag = SO_LINGER
             | SO_SNDTIMEO
             | SO_RCVTIMEO
`
(*: @description
Time-valued flags affecting the behaviour of a socket.

   [[SO_LINGER]]  specifies a maximum duration
    that a [[close(fd)]] call is permitted to block.

     [[SO_RCVTIMEO]] specifies the timeout value for input operations.

     [[SO_SNDTIMEO]] specifies the timeout value for an output function blocking because flow
     control prevents data from being sent.


:*)
;

val _ = Hol_datatype
  `msgbflag = MSG_PEEK      (* recv only, [in] *)
            | MSG_OOB       (* recv and send, [in] *)
            | MSG_WAITALL   (* recv only, [in] *)
            | MSG_DONTWAIT  (* recv and send, [in] *)
`
(*: @description
Boolean flags affecting the behaviour of a [[send]] or [[recv]] call.

 [[MSG_DONTWAIT]]: Do not block if there is no data available.

 [[MSG_OOB]]: Return out-of-band data.

 [[MSG_PEEK]]: Read data but do not remove it from the socket's receive queue.

 [[MSG_WAITALL]]: Block untill all [[n]] bytes of data are available.

:*)
;

val _ = Hol_datatype
  `socktype = SOCK_STREAM
             | SOCK_DGRAM
`
(*: @description
The two different flavours of socket, as passed to the [[socket]] call,
  [[SOCK_STREAM]] for TCP and [[SOCK_DGRAM]] for UDP.

:*)
;


(*: @section [[base_langinter]] GEN Language interaction types

The specification makes almost no assumptions on the programming language used to drive sockets calls.  It supposes that calls are made by threads, with thread IDs of type [[tid]], and that calls return values of the [[err]] types indicating success or failure.
Our \textsf{OCaml} binding maps the latter to exceptions.

Values occuring as arguments or results of sockets calls are typed.
There is a HOL type [[TLang_type]] of the names of these types and a
HOL type [[TLang]] which is a disjoint union of all of their values.
An inductive definition defines a typing relation between the two.



:*)

val _ = Hol_datatype `tid = TID of num`
(*: @description
Thread IDs.

@internal
Or do we want names?
:*)
;

(* REMARK tjr the following type is overly general in taking an 'a;
further, OK is overloaded later in this file in a (to me) very
confusing manner *)

val _ = Hol_datatype `err = OK of 'a | FAIL of error`
(*: @description
Each library call returns either success ([[OK v]]) or failure ([[FAIL err]]).

:*)
;
(*
val _ = Hol_datatype `exn = EX_udp of error
                          | EX_match_failure of (string # num # num)`
(*: @description

The language appears to have exceptions

:*)
;

val _ = Hol_datatype `except = EOK of 'a | EEX of exn`
(*: @description

- isn't this for something we don't do?
:*)
;
*)

(* -------------------------------------------------- *)
(*                   LANGUAGE TYPES                   *)
(* -------------------------------------------------- *)

(* (*: @section [[base_langty]] ALL Language types :*) *)

val _ = Hol_datatype
  `TLang_type = TLty_int
              | TLty_bool
              | TLty_string
              | TLty_one
              | TLty_pair of (TLang_type # TLang_type)
              | TLty_list of TLang_type
              | TLty_lift of TLang_type
              | TLty_err of TLang_type
              | TLty_fd
              | TLty_ip
              | TLty_port
              | TLty_error
              | TLty_netmask
              | TLty_ifid
              | TLty_filebflag
              | TLty_sockbflag
              | TLty_socknflag
              | TLty_socktflag
	      | TLty_socktype
              | TLty_tid
              | TLty_signal`
(*: @description
Type names for language types that are used in the sockets API.
:*)
;


(*              | TLty_void                   *)
(*              | TLty_ref of TLang_type      *)
(*              | TLty_exn                    *)
(*              | TLty_except of TLang_type   *)

(*
val _ = Hol_datatype `location = Loc of TLang_type # num `
(*: @description
Locations.
:*)
;
*)

val _ = Hol_datatype
  `TLang = TL_int of int
         | TL_bool of bool
         | TL_string of string
         | TL_one of one
         | TL_pair of TLang # TLang
         | TL_list of TLang list
         | TL_option of TLang option
         | TL_err of TLang err
         | TL_fd of fd
         | TL_ip of ip
         | TL_port of port
         | TL_error of error
         | TL_netmask of netmask
         | TL_ifid of ifid
         | TL_filebflag of filebflag
         | TL_sockbflag of sockbflag
         | TL_socknflag of socknflag
         | TL_socktflag of socktflag
         | TL_socktype of socktype
         | TL_tid of tid
         | TL_signal of signal`
(*: @description
Language values.

:*)
;

(* Note that one of [[TLty_lift]] and [[TL_option]] needs to be fixed so that the names are consistent. *)


val (TLang_typing_rules,TLang_typing_ind,TLang_typing_cases) =
    IndDefLib.Hol_reln`
       (!i. tlang_typing (TL_int i) TLty_int) /\

       (!b. tlang_typing (TL_bool b) TLty_bool) /\

       (!s. tlang_typing (TL_string s) TLty_string) /\

       tlang_typing (TL_one one) TLty_one /\

       (!p1 p2 ty1 ty2.
            tlang_typing p1 ty1 /\ tlang_typing p2 ty2 ==>
            tlang_typing (TL_pair(p1,p2)) (TLty_pair(ty1,ty2))) /\

       (!tl ty. (!e. MEM e tl ==> tlang_typing e ty) ==>
                tlang_typing (TL_list tl) (TLty_list ty)) /\

       (!p ty. tlang_typing p ty ==>
               tlang_typing (TL_option (SOME p)) (TLty_lift ty)) /\
       (!ty. tlang_typing (TL_option NONE) (TLty_lift ty)) /\

       (!e ty. tlang_typing (TL_err (FAIL e)) (TLty_err ty)) /\
       (!p ty. tlang_typing p ty ==>
               tlang_typing (TL_err (OK p)) (TLty_err ty)) /\

       (!fd. tlang_typing (TL_fd fd) TLty_fd) /\

       (!i. tlang_typing (TL_ip i) TLty_ip) /\
       (!p. tlang_typing (TL_port p) TLty_port) /\
       (!e. tlang_typing (TL_error e) TLty_error) /\
       (!nm. tlang_typing (TL_netmask nm) TLty_netmask) /\
       (!ifid. tlang_typing (TL_ifid ifid) TLty_ifid) /\
       (!ff. tlang_typing (TL_filebflag ff) TLty_filebflag) /\
       (!sf. tlang_typing (TL_sockbflag sf) TLty_sockbflag) /\
       (!sf. tlang_typing (TL_socknflag sf) TLty_socknflag) /\
       (!sf. tlang_typing (TL_socktflag sf) TLty_socktflag) /\
       (!st. tlang_typing (TL_socktype st) TLty_socktype) /\
       (!tid. tlang_typing (TL_tid tid) TLty_tid) /\
(*       (!l ty. tlang_typing (TL_ref (Loc (ty,l))) (TLty_ref ty)) /\ *)
(*       (!ex. tlang_typing (TL_exn ex) TLty_exn ) /\ *)
(*       (!p ty.  tlang_typing p ty ==>                    *)
(*                tlang_typing (TL_except (EOK p)) (TLty_except ty)) /\ *)
(*        (!ex ty.  tlang_typing (TL_exn ex) TLty_exn ==> *)
(*                 tlang_typing (TL_except (EEX ex)) (TLty_except ty)) /\ *)
       (!s. tlang_typing (TL_signal s) TLty_signal)`;


val TLang_typing_thm = let
  open simpLib
  fun app_letter ty ctxt = let
    open Lexis
    val tyopname = #1 (dest_type ty)
        handle HOL_ERR _ => (* if a vartype *) dest_vartype ty
    val letter = gen_variant tmvar_vary ctxt (String.substring(tyopname, 0, 1))
  in
    (letter::ctxt, mk_var(letter, ty))
  end
  fun gen_case constr = let
    val cty = type_of constr
    val (argtys, _) = strip_fun cty
    val (_ (* varnames used *), args) = stmonad.mmap app_letter argtys []
    val tm = list_mk_comb(constr, args)
  in
    GEN_ALL (CONV_RULE (SIMP_CONV (BasicProvers.srw_ss()) [])
                       (SPEC tm TLang_typing_cases))
  end
in
  save_thm("TLang_typing_thm",
           LIST_CONJ (map gen_case (TypeBase.constructors_of ``:TLang``)))
end


(* -------------------------------------------------- *)
(*                     OK AND FAIL                    *)
(* -------------------------------------------------- *)

val OK'_def   = Phase.phase 1 Define `OK'   v = TL_err (OK   v)`(*:@norender:*);
val FAIL'_def = Phase.phase 1 Define `FAIL' e = TL_err (FAIL e)`(*:@norender:*);

val _ = overload_on("FAIL", ``FAIL'``);

val OK'_int_def     = Phase.phase 1 Define `OK'_int     v = OK' (TL_int v)`(*:@norender:*);
val OK'_bool_def    = Phase.phase 1 Define `OK'_bool    v = OK' (TL_bool v)`(*:@norender:*);
val OK'_string_def  = Phase.phase 1 Define `OK'_string  v = OK' (TL_string v)`(*:@norender:*);
val OK'_one_def     = Phase.phase 1 Define `OK'_one     v = OK' (TL_one v)`(*:@norender:*);
val OK'_pair_def    = Phase.phase 1 Define `OK'_pair    v = OK' (TL_pair v)`(*:@norender:*);
val OK'_list_def    = Phase.phase 1 Define `OK'_list    v = OK' (TL_list v)`(*:@norender:*);
val OK'_option_def  = Phase.phase 1 Define `OK'_option  v = OK' (TL_option v)`(*:@norender:*);
val OK'_err_def     = Phase.phase 1 Define `OK'_err     v = OK' (TL_err v)`(*:@norender:*);
val OK'_fd_def      = Phase.phase 1 Define `OK'_fd      v = OK' (TL_fd v)`(*:@norender:*);
val OK'_ip_def      = Phase.phase 1 Define `OK'_ip      v = OK' (TL_ip v)`(*:@norender:*);
val OK'_port_def    = Phase.phase 1 Define `OK'_port    v = OK' (TL_port v)`(*:@norender:*);
val OK'_error_def   = Phase.phase 1 Define `OK'_error   v = OK' (TL_error v)`(*:@norender:*);
val OK'_tid_def     = Phase.phase 1 Define `OK'_tid     v = OK' (TL_tid v)`(*:@norender:*);
val OK'_netmask_def = Phase.phase 1 Define `OK'_netmask v = OK' (TL_netmask v)`(*:@norender:*);
val OK'_ifid_def    = Phase.phase 1 Define `OK'_ifid    v = OK' (TL_ifid v)`(*:@norender:*);
val OK'_fileflags_def = Phase.phase 1 Define `
  OK'_fileflags v = OK' (TL_list (MAP TL_filebflag v))
`(*:@norender:*);
val OK'_sockbflag_def = Phase.phase 1 Define `
  OK'_sockbflag v = OK' (TL_sockbflag v)
`(*:@norender:*);
val OK'_socknflag_def = Phase.phase 1 Define `
  OK'_socknflag v = OK' (TL_socknflag v)
`(*:@norender:*);
val OK'_socktflag_def = Phase.phase 1 Define `
  OK'_socktflag v = OK' (TL_socktflag v)
`(*:@norender:*);
val OK'_int_option_def = Phase.phase 1 Define `
  OK'_int_option v = OK' (TL_option (OPTION_MAP TL_int v))
`(*:@norender:*);
val OK'_intpair_option_def = Phase.phase 1 Define `
  OK'_intpair_option v = OK' (TL_option
                                (OPTION_MAP (\ (x,y). TL_pair (TL_int x,
                                                               TL_int y)) v))
`(*:@norender:*);
val OK'_string_ipportpair_pair_def = Phase.phase 1 Define `
  OK'_string_ipportpair_pair (s,ipo) =
    OK'_pair (TL_string s,
	      TL_option
                (OPTION_MAP
                   (\ ((i,p),b).
                      TL_pair(TL_pair(TL_option (OPTION_MAP TL_ip i),
				      TL_option (OPTION_MAP TL_port p)),
                              TL_bool b)) ipo))
`(*:@norender:*);
val OK'_ipport_def = Phase.phase 1 Define `
  OK'_ipport (i1,p1) = OK'_pair (TL_ip i1, TL_port p1)
`(*:@norender:*);
val OK'_ipportlift_def = Phase.phase 1 Define `
    OK'_ipportlift (is1,ps1) =
             OK'_pair (TL_option (OPTION_MAP TL_ip is1),
                       TL_option (OPTION_MAP TL_port ps1))
`(*:@norender:*);
val OK'_fdipport_def = Phase.phase 1 Define `
  OK'_fdipport (fd,(i2,p2)) =
             OK' (TL_pair (TL_fd fd,
                           TL_pair (TL_ip i2,
                                    TL_port p2)))
`(*:@norender:*);
val OK'_errorlift_def = Phase.phase 1 Define `
  OK'_errorlift e = OK'_option (OPTION_MAP TL_error e)
`(*:@norender:*);
(*
val OK'_msglift_def =
  Define `OK'_msglift (i1,ps1,data) =
             TL_err (OK(TL_pair(TL_ip i1,
                                TL_pair(TL_option (OPTION_MAP TL_port ps1),
                                        TL_string data))))`(*:@norender:*);
*)
val OK'_fdlisttriple_def = Phase.phase 1 Define`
  OK'_fdlisttriple (fdl1, fdl2, fdl3) =
             TL_err (OK(TL_pair(TL_list (MAP TL_fd fdl1),
                                TL_pair(TL_list (MAP TL_fd fdl2),
                                        TL_list (MAP TL_fd fdl3)))))`(*:@norender:*);
val OK'_getifaddrs_ret_def = Phase.phase 1 Define`
    OK'_getifaddrs_ret retlist =
        TL_err (OK(TL_list
                     (MAP (\ (ifid, i, ipl, nm).
                               TL_pair(TL_ifid ifid,
                                       TL_pair(TL_ip i,
                                               TL_pair(TL_list (MAP TL_ip ipl),
                                                       TL_netmask nm))))
                          retlist)))`(*:@norender:*);

val _ = overload_on("OK", ``OK'_int``);
val _ = overload_on("OK", ``OK'_bool``);
val _ = overload_on("OK", ``OK'_string``);
val _ = overload_on("OK", ``OK'_one``);
val _ = overload_on("OK", ``OK'_pair``);
val _ = overload_on("OK", ``OK'_list``);
val _ = overload_on("OK", ``OK'_option``);
val _ = overload_on("OK", ``OK'_err``);
val _ = overload_on("OK", ``OK'_fd``);
val _ = overload_on("OK", ``OK'_ip``);
val _ = overload_on("OK", ``OK'_port``);
val _ = overload_on("OK", ``OK'_error``);
val _ = overload_on("OK", ``OK'_netmask``);
val _ = overload_on("OK", ``OK'_ifid``);
val _ = overload_on("OK", ``OK'_fileflags``);
val _ = overload_on("OK", ``OK'_sockbflag``);
val _ = overload_on("OK", ``OK'_socknflag``);
val _ = overload_on("OK", ``OK'_socktflag``);
val _ = overload_on("OK", ``OK'_tid``);
val _ = overload_on("OK", ``OK'_int_option``);
val _ = overload_on("OK", ``OK'_intpair_option``);

val _ = overload_on("OK", ``OK'_string_ipportpair_pair``);

val _ = overload_on("OK", ``OK'_ipport``);
val _ = overload_on("OK", ``OK'_ipportlift``);
val _ = overload_on("OK", ``OK'_fdipport``);
val _ = overload_on("OK", ``OK'_errorlift``);
(*
val _ = overload_on("OK", ``OK'_msglift``);
*)
val _ = overload_on("OK", ``OK'_fdlisttriple``);
val _ = overload_on("OK", ``OK'_getifaddrs_ret``);


(* -------------------------------------------------- *)
(*                        TIME                        *)
(* -------------------------------------------------- *)

(*: @section [[base_time]] GEN Time types

Time and duration are defined as type synonyms.  Time must be
non-negative and may be infinite; duration must be positive and
finite.

:*)

val _ = Hol_datatype `time = time_infty | time of real`

val _ = type_abbrev ("duration", ``:real``);

val time_lt_def  = Phase.phase 1 Define `
 (*: written [[<]] :*)
    ((time_lt:time -> time -> bool) (time x) (time y) = (x < y))
 /\ (time_lt  time_infty     ys      = F)
 /\ (time_lt xs        time_infty    = T)
`(*: @mergewithnext :*) ;
val time_lte_def = Phase.phase 1 Define `
 (*: written [[<=]] :*)
  time_lte (time x) (time y) = (x <= y) /\
  time_lte t time_infty = T /\
  time_lte time_infty t = (t = time_infty)
`(*: @mergewithnext :*) ;
val time_gt_def  = Phase.phase 1 Define `
 (*: written [[>]] :*)
  time_gt  xs ys = time_lt ys xs
`(*: @mergewithnext :*) ;
val time_gte_def = Phase.phase 1 Define`
 (*: written [[>=]] :*)
  time_gte xs ys = time_lte ys xs
`;
val _ = overload_on("<" , ``time_lt`` );
val _ = overload_on("<=", ``time_lte``);
val _ = overload_on(">" , ``time_gt`` );
val _ = overload_on(">=", ``time_gte``);

val time_min_def = Phase.phase 1 Define `
 (*: written [[MIN x y]] :*)
  time_min (time x) (time y) = time (MIN x y) /\
  time_min (time x) time_infty = time x /\
  time_min time_infty (time x) = time x /\
  time_min time_infty time_infty = time_infty
`(*: @mergewithnext :*) ;

val time_max_def = Phase.phase 1 Define `
 (*: written [[MAX x y]] :*)
  time_max (time x) (time y) = time (MAX x y) /\
  time_max time_infty (time x) = time_infty /\
  time_max (time x) time_infty = time_infty /\
  time_max time_infty time_infty = time_infty
`(*: @mergewithnext :*) ;

val _ = overload_on("MIN", ``time_min``);
val _ = overload_on("MAX", ``time_max``);

(* adding a duration to a time *)
val time_plus_dur_def = Phase.phase 1 Define`
 (*: written [[+]] :*)
  ((time_plus_dur:time -> duration -> time)
                   (time x) y = time (x+y)) /\
   (time_plus_dur  time_infty    y = time_infty)
`(*: @mergewithnext :*);
val _ = overload_on("+", ``time_plus_dur``) handle e => Raise e;

(* subtracting a duration from a time *)
val time_minus_dur_def = Phase.phase 1 Define`
 (*: written [[-]] :*)
  ((time_minus_dur:time -> duration -> time)
                    (time x)      y = time (x-y)) /\
   (time_minus_dur  time_infty    y = time_infty)
`(*: @mergewithnext :*);
val _ = overload_on("-", ``time_minus_dur``);

(* scalar premultiplication of a time by a real *)
val real_mult_time_def = Phase.phase 1 Define`
 (*: written [[*]] :*)
  (real_mult_time:real -> time -> time)
                  x  (time y)      = time (x*y) /\
   real_mult_time x  time_infty    = time_infty
`;
val _ = overload_on("*", ``real_mult_time``) handle e => Raise e;

val time_zero_def = Phase.phase 1 Define `
  (time_zero : time) = time 0
`;

(* construct a duration from two naturals *)
val duration_def = Phase.phase 1 Define`
  (duration : num -> num -> duration) sec usec = $&sec + $&usec / 1000000
`
(*: @description
Some durations may be represented as [[duration sec usec]], where [[sec]]
and [[usec]] are both natural numbers.
:*)
;

(* absolute time - constructed from two naturals, time since the epoch *)
val abstime_def = Phase.phase 1 Define`
  (abstime : num -> num -> duration) sec usec =  $&sec + $&usec / 1000000
`
(*: @description
Some times may be represented as [[duration sec usec]], where [[sec]]
and [[usec]] are both natural numbers.
:*)
;

(* destructor - to option *)
val realopt_of_time_def = Phase.phase 1 Define `
  (realopt_of_time : time -> real option) (time x) = SOME x /\
  realopt_of_time time_infty = NONE
`(*: @mergewithnext :*);

(* destructor - to real; unspecified on time_infty *)
val the_time_def = Phase.phase 1 Define`
  (*: written [[THE]] :*)
  the_time (time x) = x
`;
val _ = overload_on("THE", ``the_time``);


(*: @section [[base_net]] TCP Basic network types: sequence numbers

We have several flavours of TCP sequence numbers, all represented by
32-bit values: local sequence numbers, foreign sequence numbers, and
timestamps.  This helps prevent confusion.  We also define
[[tcp_seq_flip_sense]], which converts a local to a foreign sequence
number and vice versa.

:*)

(* -------------------------------------------------- *)
(*                       BYTES                        *)
(* -------------------------------------------------- *)

val _ = type_abbrev ("byte", ``:char``);


(* -------------------------------------------------- *)
(*               SEQUENCE NUMBERS                     *)
(* -------------------------------------------------- *)

(* Sequence numbers are 32-bit quantities
   with special wraparound comparison operators *)

local open integer_wordTheory (* for w2i and i2w functions *) in end;


val _ = Hol_datatype `
  seq32 = SEQ32 of 'a => word32
`
(*: @description
32-bit wraparound sequence numbers, as used in TCP, along with their special arithmetic.
:*)
;

(* Arithmetic: adding or subtracting a natural or integer *)

val seq32_plus_def = Phase.phase 1 Define`
 (*: written [[+]] :*)
  seq32_plus   (SEQ32 a n) (m:num) = SEQ32 a (n + n2w m)
`(*: @mergewithnext :*);
val seq32_minus_def = Phase.phase 1 Define`
 (*: written [[-]] :*)
  seq32_minus  (SEQ32 a n) (m:num) = SEQ32 a (n - n2w m)
`(*: @mergewithnext :*);
val seq32_plus'_def = Phase.phase 1 Define`
 (*: written [[+]] :*)
  seq32_plus'  (SEQ32 a n) (m:int) = SEQ32 a (n + i2w m)
`(*: @mergewithnext :*);
val seq32_minus'_def = Phase.phase 1 Define`
 (*: written [[-]] :*)
  seq32_minus' (SEQ32 a n) (m:int) = SEQ32 a (n - i2w m)
`(*: @mergewithnext :*);

val _ = overload_on("+", ``seq32_plus``  );
val _ = overload_on("-", ``seq32_minus`` );
val _ = overload_on("+", ``seq32_plus'`` );
val _ = overload_on("-", ``seq32_minus'``);

(* Difference: *)

val seq32_diff_def = Phase.phase 1 Define`
 (*: written [[-]] :*)
  seq32_diff (SEQ32 (a:'a) n) (SEQ32 (b:'a) m) = w2i (n - m)
`(*: @mergewithnext :*);

val _ = overload_on("-", ``seq32_diff``);

(* Comparison: code from BSD says:
     define  SEQ_LT(a,b)   ((int)((a)-(b)) < 0)
     define  SEQ_LEQ(a,b)  ((int)((a)-(b)) <= 0)
     define  SEQ_GT(a,b)   ((int)((a)-(b)) > 0)
     define  SEQ_GEQ(a,b)  ((int)((a)-(b)) >= 0)
*)

val seq32_lt_def = Phase.phase 1 Define`
 (*: written [[<]] :*)
  seq32_lt  (n:'a seq32) (m:'a seq32) <=> ( (n - m) : int ) < 0
`(*: @mergewithnext :*);
val seq32_leq_def = Phase.phase 1 Define`
 (*: written [[<=]] :*)
  seq32_leq (n:'a seq32) (m:'a seq32) <=> ( (n - m) : int ) <= 0
`(*: @mergewithnext :*);
val seq32_gt_def = Phase.phase 1 Define`
 (*: written [[>]] :*)
  seq32_gt  (n:'a seq32) (m:'a seq32) <=> ( (n - m) : int ) > 0
`(*: @mergewithnext :*);
val seq32_geq_def = Phase.phase 1 Define`
 (*: written [[>=]] :*)
  seq32_geq (n:'a seq32) (m:'a seq32) <=> ( (n - m) : int ) >= 0
`(*: @mergewithnext :*);
val _ = overload_on("<" , ``seq32_lt`` );
val _ = overload_on("<=", ``seq32_leq``);
val _ = overload_on(">" , ``seq32_gt`` );
val _ = overload_on(">=", ``seq32_geq``);

(* coercion *)
val seq32_fromto_def = Phase.phase 1 Define`
  seq32_fromto (a:'a) b (SEQ32 (c:'a) n) = SEQ32 b n
`(*: @mergewithnext :*);
val seq32_coerce_def = Phase.phase 1 Define`
  seq32_coerce (SEQ32 a n) = SEQ32 ARB n
`(*: @mergewithnext :*);

val seq32_min_def = Phase.phase 1 Define`
 (*: written [[MIN x y]] :*)
  seq32_min (n:'a seq32) (m:'a seq32) = if n < m then n else m
`(*: @mergewithnext :*);
val seq32_max_def = Phase.phase 1 Define`
 (*: written [[MAX x y]] :*)
  seq32_max (n:'a seq32) (m:'a seq32) = if n < m then m else n
`;
val _ = overload_on("MIN", ``seq32_min``);
val _ = overload_on("MAX", ``seq32_max``);


(* -------------------------------------------------- *)
(*      TCP SEQUENCE NUMBERS and TIMESTAMPS           *)
(* -------------------------------------------------- *)

(* TCP singleton types *)
val _ = Hol_datatype`tcpLocal   = TcpLocal  `;
val _ = Hol_datatype`tcpForeign = TcpForeign`;

(* TCP sequence number types *)
val _ = type_abbrev("tcp_seq_local"  , ``:tcpLocal   seq32``);
val _ = type_abbrev("tcp_seq_foreign", ``:tcpForeign seq32``);

(* TCP constructors *)
val _ = Phase.phase 1 Define`tcp_seq_local   (n:word32) = SEQ32 TcpLocal   n`(*: @mergewithnext :*);
val _ = Phase.phase 1 Define`tcp_seq_foreign (n:word32) = SEQ32 TcpForeign n`(*: @mergewithnext :*);

(* TCP flip-sense overloaded operator *)
val _ = Define`tcp_seq_local_to_foreign = seq32_coerce:tcp_seq_local -> tcp_seq_foreign`(*: @mergewithnext :*);
val _ = Define`tcp_seq_foreign_to_local = seq32_coerce:tcp_seq_foreign -> tcp_seq_local`;
val _ = overload_on("tcp_seq_flip_sense", ``tcp_seq_local_to_foreign``);
val _ = overload_on("tcp_seq_flip_sense", ``tcp_seq_foreign_to_local``);


(* timestamps are treated identically with TCP sequence numbers,
   as wraparound unsigned 32-bit words *)
val _ = Hol_datatype`tstamp = Tstamp`;
val _ = type_abbrev("ts_seq", ``:tstamp seq32``);
val _ = Phase.phase 1 Define`ts_seq (n:word32) = SEQ32 Tstamp n`;

(* -------------------------------------------------- *)

val _ = export_theory();
