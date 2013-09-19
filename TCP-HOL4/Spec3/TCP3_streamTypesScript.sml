(* A HOL98 specification of TCP *)

(* Basic types used in the specification, including language types and time types *)

(*[ RCSID "$Id: TCP3_streamTypesScript.sml,v 1.14 2009/02/19 17:47:27 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

local open TCP1_baseTypesTheory in end

local open arithmeticTheory stringTheory pred_setTheory integerTheory
           finite_mapTheory realTheory word32Theory in end;

val _ = new_theory "TCP3_streamTypes";

val _ = Version.registerTheory "$RCSfile: TCP3_streamTypesScript.sml,v $" "$Revision: 1.14 $" "$Date: 2009/02/19 17:47:27 $";

(*: @chapter [[TCP3_streamTypes]] Stream types

This file defines types for streams: stream control information to
represent control messages on the wire, a unidirectional stream, and a
bidirectional stream.

:*)

(*: @section [[TCP3_streamTypes]] ALL Stream types

Basic stream types.

:*)

val _ = type_abbrev("streamid", ``:(ip#port) set``)
(* @description

A stream is identified by the quad for the connection. The quad is of
the form [[(i1,p1,i2,p2)]]. The stream is bidirectional, so this quad
identifies the same stream as that identified by quad
[[(i2,p2,i1,p1)]]. To capture this quotienting, we represent the
stream identifier as [[{(i1,p1),(i2,p2)}]].

REMARK type abbreviation comments are ignored by HOLDoc
*)
;

val _ = Hol_datatype `
    (*: stream control information :*)
    streamFlags = <|
        SYN : bool;    (*: [[SYN]], no [[ACK]] :*)
        SYNACK : bool; (*: [[SYN]] with [[ACK]] :*)
        FIN : bool;
        RST : bool
    |>
`
(*: @description

We record stream control-flow information with each unidirectional
stream. This corresponds to the protocol-level control-flow
messages. For example, the [[SYNACK]] flag is set iff there is a
message at the protocol-level (in queues or on the wire) that has both
the [[SYN]] and the [[ACK]] flags set, and which may be received as a
valid message. A message may not be valid if, for example, the
sequence number is out of order.

:*)
;


val _ = Hol_datatype `
    (*: unidirectional stream :*)
    tcpStream = <|
        i : ip;      (*: source IP :*)
        p : port;    (*: source port :*)
        flgs : streamFlags;
        data : byte list;
        destroyed : bool
    |>
`
(*: @description

The [[ip]] and [[port]] record the origin of the stream, which is primarily used
to identify a unidirectional stream in an unordered pair of streams. The
[[flgs]] record the control-flow information. The [[data]] is simply
a list of bytes. The [[destroyed]] flag records whether the socket has been
closed at the source, or perhaps removed altogether.

:*) ;

val _ = Hol_datatype `
    (*: bidirectional stream :*)
    tcpStreams = <| streams : tcpStream set |>
`
(*: @description

A bidirectional stream is an unordered pair of streams, thus, we
expect that there are always two [[tcpStream]]s in [[streams]].

 :*)
;


val _ = export_theory();

