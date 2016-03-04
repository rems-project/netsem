open Libcalls;;
open Parserlib;;
open Ocamllib;;
open Printf;;
open Int64;;
open Unix;;

exception Fatal of string;;

(* no semicolon version *)
val lh_return_to_string: libreturnstructure -> tid -> string;;
val lh_call_to_string: libstructure -> tid -> string;;

val lib_call_render: libstructure -> tid -> string;;
val lib_call_render_call: libstructure -> string;;

val lib_return_render: libreturnstructure -> tid -> string;;
val lib_return_render_return: libreturnstructure -> string;;

(*
val lib_render_to_socket: file_descr -> ns_parse_data -> unit;;
*)
