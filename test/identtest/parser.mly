%{
open Char;;
open String;;
open Errors;;

let hexchar2int d =
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
  | _ -> raise(Parse_error("Cannot convert hexchar to int. Invalid character"));;

let hexpair2char p =
 chr ((hexchar2int(String.get p 0) lsl 4) lor (hexchar2int(String.get p 1)));;

let hexstring2charstr hexstr =
  let len = String.length hexstr in
  if (len mod 2) != 0 then
    raise(Parse_error("Invalid packet length"))
  else
    let output = String.create (len/2) in
    let rec loop c p =
      if (c = len) then
	output
      else
	((String.set output p (hexpair2char (String.sub hexstr c 2))); (loop (c+2) (p+1)))
    in loop 0 0;;

%}

%token <string> STRING
%token COMMENT LENGTH DATA SEP

%start main
%type <string> main
%%

main:
  packet { $1 }
;

packet:
  comment length data SEP { if (int_of_string($2)*2) != (String.length $3) then
		              raise(Parse_error("Invalid file format")) else
                              hexstring2charstr $3
                           }
;

comment:
  COMMENT strings { () }
;

length:
  LENGTH strings { $2 }
;

data:
  DATA strings { $2 }
;

strings:
  strings STRING { String.concat "" ($1::[$2]) }
| STRING  { $1 }
;

