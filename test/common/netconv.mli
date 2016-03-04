open Nettypes;;

type endianness = Little | Big;;

exception Packet_Truncated of string
exception Packet_Malformed of string

val assert_packet_wf: string -> bool -> unit

val input_uint32: endianness -> char list -> uint * char list
val input_uint16: endianness -> char list -> uint * char list
val input_byte: char list -> uint * char list
val input_bytes: int -> char list -> uint list * char list
val input_uint32_net: char list -> uint * char list
val input_uint16_net: char list -> uint * char list
val input_sint32: endianness -> char list -> sint * char list

val output_uint16: endianness -> uint -> uint list -> uint list
val output_uint16_net: uint -> uint list -> uint list
val output_uint32: endianness -> uint -> uint list -> uint list
val output_uint32_net: uint -> uint list -> uint list

val bits: int -> int -> uint -> uint
val bit: int -> uint -> bool

val (<|>): ('a -> 'b) -> ('a -> 'c) -> 'a -> 'b * 'c
val mapfst: ('a -> 'b) -> ('a * 'c) -> 'b * 'c
val splitat: int -> 'a list -> 'a list * 'a list
val drop: int -> 'a list -> 'a list

