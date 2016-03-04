open Tcpcbtypes;;
open Nettypes;;
open Parserlib;;
open Printf;;
open Unix;;
open Sock;;

val taddr_render: traceaddr -> string

val tstate_render: tcpstate -> string

val tsact_render: tcpaction -> string

val render_ts_recent: tswindow -> string

val tcpcb_render: tcpcb -> string

val tcpcb_trace_to_string : tcpaction -> tracesid -> traceaddr -> tcpstate -> tcpcb -> string

val tcpcb_trace_render: tcpaction -> tracesid -> traceaddr -> tcpstate -> tcpcb -> string

(*
val tcpcb_trace_render_to_socket: file_descr -> ns_parse_data -> unit

*)
