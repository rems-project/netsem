(* ***********************)
(* byte,word etc parsing *)
(* ***********************)

open Nettypes;;

(** endianness **)
type endianness = Little | Big;;

(** define some exceptions for the packet reader **)
exception Packet_Truncated of string
exception Packet_Malformed of string
let assert_packet_wf str b = if b then () else raise (Packet_Malformed str)

(** read from the byte stream **)

(* get a uint32 with specified endianness *)
let input_uint32 endian cs = match cs with
  (a::b::c::d::cs) ->
    (match endian with
       Little -> ((((((ch d << 8) |. ch c) << 8) |. ch b) << 8) |. ch a),cs
     | Big    -> ((((((ch a << 8) |. ch b) << 8) |. ch c) << 8) |. ch d),cs)
| _ -> raise (Packet_Truncated "input_uint32")

(* get a uint16 with specified endianness *)
let input_uint16 endian cs = match cs with
  (a::b::cs) ->
    (match endian with
       Little -> ((ch b << 8) |. ch a),cs
     | Big    -> ((ch a << 8) |. ch b),cs)
| _ -> raise (Packet_Truncated "input_uint16")

(* get a byte *)
let input_byte cs = match cs with
  (a::cs) -> (ch a),cs
| _ -> raise (Packet_Truncated "input_byte")

(** helpers **)

(* get n bytes *)
let input_bytes n cs =
  let rec loop cs bs nb =
    assert_packet_wf "input_bytes: bad byte length requested" (nb >= 0);
    if nb = 0 then
      (List.rev bs),cs
    else
      let b,cs = input_byte cs in
      loop cs (b :: bs) (nb - 1) in
  loop cs [] n

(* get an int32 in network byte order *)
let input_uint32_net cs = input_uint32 Big cs
(* get an int16 in network byte order *)
let input_uint16_net cs = input_uint16 Big cs

(* get a signed int32 with specified endianness *)
let input_sint32 endian cs =
  let u,cs = input_uint32 endian cs in
  (Int64.to_int32 u),cs

(* pick out some bits: and with `mask' and shift right by `shift' *)
let bits mask shift n = (n &: mask) >> shift
(* pick out a boolean flag: and with `mask' and check if nonzero *)
let bit mask n = (n &: mask) <> uint 0

(* "fork" *)
let (<|>) f g x = f x, g x

(* "mapfst" *)
let mapfst f (x,y) = (f x,y)

(* split list after n elts *)
let splitat n ys =
  let rec splitat0 n xs ys = match (n,ys) with
    (0,_)     -> (List.rev xs,ys)
  | (n,y::ys) -> splitat0 (n - 1) (y :: xs) ys
  | (n,[])    -> raise Not_found in
  splitat0 n [] ys

(* drop first n elts of list *)
let drop n ys =
  let (_,ys') = splitat n ys in
  ys'

let output_uint16 endian x l =
  match endian with
    Little -> (x &: 0xff)::((x>>8) &: 0xff)::l
  | Big -> ((x>>8) &: 0xff)::(x &: 0xff)::l;;

let output_uint16_net x l =
  output_uint16 Big x l;;

let output_uint32 endian x l =
  match endian with
    Little -> (x &: 0xff)::((x>>8) &: 0xff)::((x>>16) &: 0xff)::((x>>24) &: 0xff)::l
  | Big -> ((x>>24) &: 0xff)::((x>>16) &: 0xff)::((x>>8) &: 0xff)::(x &: 0xff)::l;;

let output_uint32_net x l =
  output_uint32 Big x l;;

