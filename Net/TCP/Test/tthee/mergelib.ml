open Int64;;
open Printf;;

open Platform;;
open Parserlib;;
open Nettypes;;
open Holrender;;
open Holparselib;;
open Librender;;
open Tcpcbrender;;
open Renderlib;;

type merge_input =
    MESSAGE of ns_parse_return
  | FINISH;;

(* ---------- *)
(* Pretty prn *)
(* ---------- *)

let header2 = sprintf
      "(* ----------------------------------------\
          ---------------------------------- *)\n";;

(* Write a custom string to the file header *)
let writeCustomHeader out str =
  output_string out header2;
  output_string out (str ^ "\n");
  output_string out header2;;


(* Write merger file header to the specified channel *)
let writeMergeHeader out =
  let header1 = sprintf
      "(* Netsem logging & merging tool (mlogger) - Date: %s   *)\n"
    (Platform.gettimeofday ()) in
  let _ = output_string out header2 in
  let _ = output_string out header1 in
  let _ = output_string out header2 in
  ();;

(* Write our merger header's footer to the specified channel *)
let writeMergeHeaderFooter out =
  let header1 = "(* BEGIN  *)\n\n" in
  let _ = output_string out header1 in
  ();;

let string_of_time time =
  sprintf "%s %s" (Int64.to_string (time /. time_base_us))
    (Int64.to_string (time % time_base_us));;

(* generateEpsilonTransition (previous time in microsecs) (new time in microsecs) *)
(* Generate an epsilon transition from the specified times *)
let generateEpsilonTransition prev_time new_time =
  let diff = new_time -. prev_time in
  let backwards_warning =
    if(diff <. uint_zero) then
      let str =
      "(* ## WARNING: time went backwards (negative epsilon transition) ## *)" in
      (* done like this to stop spurious newlines *)
      (prerr_string (str); str^"\n")
    else
      "" in
  let diff_sign = if diff <. uint_zero then uint (-1) else uint 1 in
  let diff_abs  = Int64.abs diff in
  let diff_s    = diff_sign *. (diff_abs /. time_base_us) in
  let diff_us   = diff_sign *. (diff_abs % time_base_us) in
  if (diff_s ==. uint_zero) && (diff_us ==. uint_zero) then ""
  else
    sprintf "%sLh_epsilon(duration %s %s);\n\n" backwards_warning
      (Int64.to_string diff_s) (Int64.to_string diff_us);

(* ---------- *)
(* Real work  *)
(* ---------- *)

exception Fatal of string;;

(* Return the message with the minimum time *)
let minimum m1 m2 =
  match (m1,m2) with
    ((PARSE_RETURN(Some(TIMECOMMENT(t1_us,_)),_,_),_,_),
     (PARSE_RETURN(Some(TIMECOMMENT(t2_us,_)),_,_),_,_)) ->
       if t1_us <=. t2_us then m1
       else m2
  | _ -> raise (Fatal("Mergelib.minimum(): received an invalid message type"));;

(* Fold a function over a nonempty list (avoids need for an initial value) *)
let fold1_left f l =
  match l with
    [] -> raise(Fatal("Mergelib.fold1_left(): called on an empty list"))
  | (x::xs) -> List.fold_left f x xs;;

(* Given a list of parsed messages pick the minimum *)
(* with respect to the timestamp ordering *)
let findMinimum mlist =
  try
    fold1_left minimum mlist
  with
    Fatal(s) -> raise(Fatal("Mergelib.findMinimum(): "^s));;



