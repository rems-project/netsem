open Char;;
open String;;
open Int64;;
open Unix;;
open Rawsock;;

(* **************************************** *)
(* a nice type big enough to hold an uint32 *)
(* **************************************** *)

exception Error of string;;

type uint = int64
let (|.) n m = Int64.logor n m
let (&:) n m = Int64.logand n (Int64.of_int m)
let (<<) n m = Int64.shift_left n m
let (>>) n m = Int64.shift_right_logical n m
let ch c = Int64.of_int (int_of_char c)
let uint n = Int64.of_int n
let int n = Int64.to_int n (* could do a range check here *)

(* an option in an IP packet, uninterpreted *)
type ip_option = uint list

(* IP header (lossless representation) *)
type ip_header = {
  ip_v    : uint ;
  ip_hl   : uint ;
  ip_tos  : uint ;
  ip_len  : uint ;
  ip_id   : uint ;
  ip_zf   : bool ;
  ip_df   : bool ;
  ip_mf   : bool ;
  ip_off  : uint ;
  ip_ttl  : uint ;
  ip_p    : uint ;
  ip_sum  : uint ;
  ip_src  : uint ;
  ip_dst  : uint ;
  ip_opts : ip_option list ;
}

(* IP datagram (lossless representation) *)
type ip_packet = {
  ip_h : ip_header ;
  ip_data : char list ;  (* length not necessarily checked! *)
  }

let hdr =
  {ip_v = uint 4; ip_hl = uint 5; ip_tos = uint 0; ip_len = uint 20; ip_id = uint 0;
   ip_zf = false; ip_df = true; ip_mf = false; ip_off = uint 0;
   ip_ttl = uint 255; ip_p = uint 6; (*ip_sum = uint 64124*) ip_sum = uint 0; ip_src = uint 3232235532;
   ip_dst = uint 3232235532; ip_opts = [];};;

let packet = {ip_h = hdr; ip_data = []};;

let u64_to_str_bigend v n s off =
  let rec u64_to_str_bigend_h i =
    if (i=0) then ()
    else let x = s.[off+i-1] <- chr(int ((shift_right v ((n-i)*8)) &: 255))
	 in u64_to_str_bigend_h (i-1)
  in u64_to_str_bigend_h n;;

let make_flags zf df mf =
  logor (if (zf = true) then (uint 1) << 2 else uint 0)
      (logor (if (df = true) then (uint 1) << 1 else uint 0)
	   (if (mf = true) then uint 1 else uint 0));;

let output_packet p =
  let hdr = p.ip_h in
  let s = create 20 in
  let _ = s.[0] <- chr(int ((shift_left hdr.ip_v 4) |. hdr.ip_hl)) in
  let _ = s.[1] <- chr(int hdr.ip_tos) in
(*  let x = u64_to_str_bigend hdr.ip_len 2 s 2 in *)
  let _ = s.[2] <- chr(int (hdr.ip_len &: 255)) in
  let _ = s.[3] <- chr(int ((hdr.ip_len >> 8) &: 255)) in
  let _ = u64_to_str_bigend hdr.ip_id 2 s 4 in
  let _ = s.[7] <- chr(int (logor (shift_left (make_flags hdr.ip_zf hdr.ip_df hdr.ip_mf) 5)
				  (shift_right (hdr.ip_off) 8))) in
  let _ = s.[6] <- chr(int (hdr.ip_off &: 255)) in
  let _ = s.[8] <- chr(int hdr.ip_ttl) in
  let _ = s.[9] <- chr(int hdr.ip_p) in
  let _ = u64_to_str_bigend hdr.ip_sum 2 s 10 in
  let _ = u64_to_str_bigend hdr.ip_src 4 s 12 in
  let _ = u64_to_str_bigend hdr.ip_dst 4 s 16 in
  s;;

let sd =
  try raw_socket PF_INET 0
  with Unix_error(e, s1, s2) ->
    raise(Error("Error:" ^ error_message(e) ^ s1 ^ s2))
in
  let opt = raw_sockopt_hdrincl sd in
  let addr = ADDR_INET(inet_addr_of_string "192.168.0.1", 7000) in
  sendto sd (output_packet packet) 0 20 [] addr;;
