open Unix;;
open String;;
open Rawsock;;

exception Fatal of string;;

(*let hexchar2int d =
  match d with
    'A' -> 10
  | 'a' -> 10
  | 'B' -> 11
  | 'b' -> 11
  | 'C' -> 12
  | 'c' -> 12
  | 'D' -> 13
  | 'd' -> 13
  | 'E' -> 14
  | 'e' -> 14
  | 'F' -> 15
  | 'f' -> 15
  | '0' -> 0
  | '1' -> 1
  | '2' -> 2
  | '3' -> 3
  | '4' -> 4
  | '5' -> 5
  | '6' -> 6
  | '7' -> 7
  | '8' -> 8
  | '9' -> 9
  | _ -> raise(Fatal("Cannot convert hexchar to int. Invalid character"));;

let hexstring2int hexstr =
  let len = String.length hexstr in
  let rec loop c v =
    match c with
      0 -> (v lsl 8) lor (hexchar2int (String.get hexstr c))
    | n -> loop (c-1) ((v lsl 8) lor (hexchar2int (String.get hexstr c)))
  in loop (len-1) 0;;

let readnextpkt fd =
  let star = String.create 1 in
  let comment = String.create 8 in
  let length = String.create 7 in
  let data = String.create 5 in
  let _ =
    let rec loop1 x=
      let r = read fd star 0 1 in
      if r=0 then loop1 ()
      else if ((String.get star 0) = '*') then
	let r = read fd comment 0 8 in
	if r != 8 then
	  raise(Fatal("File read error"))
	else
	  if ((String.compare comment "Comment=") = 0) then
	    ()
	  else
	    raise(Fatal("Unexpected token when 'Comment=' expected"))
      else loop1 ()
    in loop1 ()
  in
  let len =
    let rec loop2 x=
      let r = read fd star 0 1 in
      if r=0 then loop2 ()
      else if ((String.get star 0) = '*') then
	let r = read fd length 0 7 in
	if r != 8 then
	  raise(Fatal("File read error"))
	else
	  if ((String.compare length "Length=") = 0) then
	    (* get length here *)0
	  else
	    raise(Fatal("Unexpected token when 'Length=' expected"))
      else loop2 ()
    in loop2 ()
  in
  in (), true;;



let writepkt x y = ();;

let readslurpinject f =
  let fd = openfile f [O_RDONLY] 0 in
  let sd = raw_socket PF_INET 0 in
  let _ = raw_sockopt_hdrincl sd in
  let _ =
    let rec readloop x =
      let (pkt, st) = readnextpkt fd in
      match st with
	false -> ()
      |	true ->
	  let _ = writepkt sd pkt in
	  readloop ()
    in readloop ()
  in
  let _ = Unix.close sd in
  let _ = Unix.close fd in
  ()

*)


