(* A HOL98 specification of TCP *)

(* Type definitions of the network and its components *)

(*[ RCSID "$Id: TCP3_streamScript.sml,v 1.18 2009/02/20 10:35:33 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse

open bossLib

open HolDoc

local open TCP3_streamTypesTheory
in end

(* local open arithmeticTheory stringTheory pred_setTheory bagTheory
           integerTheory finite_mapTheory realTheory word32Theory word16Theory in end; *)

val _ = new_theory "TCP3_stream";

val _ = Version.registerTheory "$RCSfile: TCP3_streamScript.sml,v $" "$Revision: 1.18 $" "$Date: 2009/02/20 10:35:33 $";

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @chapter [[TCP3_stream]] Stream auxiliary functions

This file gives default initial values for stream types, and defines auxiliary functions, such as
reading and writing to streams, and destroying one or more streams from a stream map.

:*)

(*: @section [[TCP3_stream_initial]] ALL Default initial values

Default initial values for stream types.

:*)

val _ = Phase.phase 1 Define `
    (*: initial stream flags :*)
    initial_streamFlags = <|
        SYN := F;
        SYNACK := F;
        FIN := F;
        RST := F
    |>
`
(*: @description

The initial flags are all false, since no messages are in transit.

:*)
;

val _ = Phase.phase 1 Define `
    (*: initial unidirectional stream :*)
    initial_stream (i,p) destroyed = <|
        i := i;
        p := p;
        flgs := initial_streamFlags;
        data := [];
        destroyed := destroyed
    |>
`
(*: @description

A unidirectional stream is constructed by giving the originating ip address and port, and the value
the [[destroyed]] flag should take. Then [[data]] is initialized to the empty list.

:*)
;

val _ = Phase.phase 1 Define `
    (*: initial bidirectional stream :*)
    initial_streams (i1,p1,i2,p2) = (
        (* in stream is initially destroyed because other host knows nothing of the connection attempt *)
        let in_ = initial_stream (i2,p2) T in
        let out = initial_stream (i1,p1) F in
        <| streams := {in_;out} |>)
`
(*: @description

A stream is constructed based on the quad [[(i1,p1,i2,p2)]]. Only one endpoint, at the originating
host [[(i1,p1)]], exists, thus, the output stream is not destroyed, whilst the input stream is
destroyed.

:*)
;

val _ = Phase.phase 1 Define `
    (*: form the stream identifier from quad :*)
    streamid_of_quad ((i1,p1,i2,p2):ip#port#ip#port) = {(i1,p1);(i2,p2)}
`
(*: @description

A stream identifier is an unordered pair of the endpoint ip and port addresses.

:*)
;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[TCP3_stream_aux]] ALL Auxiliary functions

Auxiliary stream functions, such as reading and writing to a stream.

:*)

val null_flgs_data_def = Phase.phase 1 Define `
    (*: flags and data corresponding to no control information :*)
    null_flgs_data (flgs,data) = (
        flgs = <| SYN := F; SYNACK := F; FIN := F; RST := F |> /\
        data = [])
`;

val _ = Phase.phase 1 Define `
    (*: flags and data corresponding to an initial [[SYN]] message :*)
    make_syn_flgs_data (flgs,data:char list) = (
        flgs = <| SYN := T; SYNACK := F; FIN := F; RST := F |> /\
        data = [])
`;

val _ = Define `
    (*: flags and data corresponding to an initial [[SYNACK]] message :*)
    make_syn_ack_flgs_data (flgs,data:char list) = (
        flgs = <| SYN := F; SYNACK := T; FIN := F; RST := F |> /\
        data = [] )
`;

val _ = Define `
     (*: retrieve unidirectional streams from bidirectional stream :*)
     sync_streams (i1:ip,p1:port,i2:ip,p2:port) (s:tcpStreams) (in_,out) = (
         s.streams = {in_; out} /\
         (in_.i,in_.p) = (i2,p2) /\
         (out.i,out.p) = (i1,p1) )

     (* i1 p1 are local, i2 p2 are foreign *)
`
(*: @description

A function to extract the input stream [[in_]] and output stream [[out]] from a bidirectional stream
[[s]] based on the ip address and port of an endpoint.

:*)
;

val _ = Define `
    (*: write flags and data to a stream :*)
    write (i1,p1,i2,p2) (flgs,data) s s' = (
        ? in_ out in' out'.
        sync_streams (i1,p1,i2,p2) s (in_,out) /\
        sync_streams (i1,p1,i2,p2) s' (in',out') /\
        in' = in_ /\
        out'.flgs =
        <|  SYN := (out.flgs.SYN \/ flgs.SYN);
            SYNACK := (out.flgs.SYNACK \/ flgs.SYNACK);
            FIN := (out.flgs.FIN \/ flgs.FIN);
            RST := (out.flgs.RST \/ flgs.RST)
        |> /\
        out'.data = (out.data ++ data))
`
(*: @description

The unidirectional streams before ([[in_,out]]) and after ([[in',out']]) are first extracted using
[[sync_streams]]. The [[flgs]] and [[data]] of the output stream [[out']] are updated to reflect the
write. For example, [[data]] is appended to [[out.data]] to form [[out'.data]].

:*)
;

val _ = Define `
    (*: read flags and data from a stream :*)
    read (i1,p1,i2,p2) (peek:bool) (inline:bool) (flgs:streamFlags,data:char list) s s' = (
        ? in_ out in' out'.
        sync_streams (i1,p1,i2,p2) s (in_,out) /\
        sync_streams (i1,p1,i2,p2) s' (in',out') /\
        out' = out /\

        (case flgs.SYN of T -> in'.flgs.SYN = F /\ in_.flgs.SYN = T || F -> in'.flgs.SYN = in_.flgs.SYN) /\
        (case flgs.SYNACK of
             T -> in'.flgs.SYNACK = F /\ in_.flgs.SYNACK = T
          || F -> in'.flgs.SYNACK = in_.flgs.SYNACK) /\
        (case flgs.FIN of T -> in'.flgs.FIN = F /\ in_.flgs.FIN = T || F -> in'.flgs.FIN = in_.flgs.FIN) /\
        (case flgs.RST of T -> in'.flgs.RST = F /\ in_.flgs.RST = T || F -> in'.flgs.RST = in_.flgs.RST) /\

        (? pre post.
            ((pre ++ data ++ post) = in_.data) /\
            (inline ==> pre = []) /\
            if peek then
                in'.data = in_.data
            else
                in'.data = (pre ++ post)))
`
(*: @description

The unidirectional streams before ([[in_,out]]) and after ([[in',out']]) are first extracted using
[[sync_streams]]. The [[flgs]] and [[data]] of the input stream [[in']] are updated to reflect the
read. For example, if [[flgs.SYN]] is set, a [[SYN]] was read, which causes the [[SYN]] flag for
input stream [[in']] to be lowered; furthore, [[in_.flgs.SYN]] must also have been set, i.e. there
must have been a [[SYN]] to read.

:*)
;


(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
(*: @section [[TCP3_stream_destroy]] ALL Stream removal

Auxiliary functions to help with removing streams when they have been destroyed.

:*)

val both_streams_destroyed_def = Define `
    (*: test whether both unidirectional streams are destroyed :*)
    both_streams_destroyed ss = ! s t. ss.streams = {s;t} ==> s.destroyed /\ t.destroyed
`;

val remove_destroyed_streams_def = Define `
    (*: restrict the stream map to those streams that are not destroyed :*)
    remove_destroyed_streams (SS:streamid |-> tcpStreams) = (
       let alive = {stid | ~ both_streams_destroyed (SS ' stid)} in
       DRESTRICT SS alive)
`
(*: @description

Streams where both unidirectional streams are destroyed are garbage collected.

:*)
;

val _ = Define `
    (*: destroy a particular unidirectional stream, then clean up :*)
    destroy (i1,p1,i2,p2) SS S'' = (
        ? S0 s in_ out s' S'.
        SS = S0 |++ [(streamid_of_quad (i1,p1,i2,p2), s)] /\
        sync_streams (i1,p1,i2,p2) s (in_,out) /\
        s' = <| streams := {in_; out with <| destroyed := T |>} |> /\
        S' = S0 |++ [(streamid_of_quad (i1,p1,i2,p2), s')] /\
        S'' = remove_destroyed_streams S')
`
(*: @description

The particular stream [[s]] identified by quad [[(i1,p1,i2,p2)]] is extracted from the stream map [[SS]]. In turn, the input and output streams are extracted from [[s]]. The stream [[s]] is updated to mark the output stream [[out]] as destroyed, producing the updated stream map [[S']]. Finally, streams with both endpoints destroyed are garbage collected using [[remove_destroyed_streams]].

:*)
;

val destroy_quads_def = Define `
    (*: destroy all quads in a stream map, then clean up :*)
    destroy_quads quads (SS:streamid |-> tcpStreams) S'' = (
        ? S'. FDOM S' = FDOM SS /\
        (! stid. stid IN (FDOM SS) ==>
            ? in_ out in' out'.
            (SS ' stid).streams = {in_;out} /\
            in' = in_ with  <| destroyed updated_by T onlywhen ((in_.i,in_.p,out.i,out.p) IN quads) |> /\
            out' = out with <| destroyed updated_by T onlywhen ((out.i,out.p,in_.i,in_.p) IN quads) |> /\
            (S' ' stid).streams = {in';out'}) /\
        S'' = remove_destroyed_streams S')
`
(*: @description

Similar to [[destroy]], but allowing the destruction of multiple streams, for example, when a listening socket with pending connections is closed.

:*)
;


val _ = export_theory();

(* Local Variables: *)
(* fill-column: 100 *)
(* End: *)


