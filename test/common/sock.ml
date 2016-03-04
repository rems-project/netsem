open Unix;;
(*open ThreadUnix;;*)

exception Fatal of string;;

let write sd str =
  let len = String.length str in
  let rec trysend c s =
    match c with
      0 ->
	raise(Fatal("Cannot send/write data to connected socket\n"))
    | n ->
	let strlen = String.length s in
	let lensent = (*ThreadUnix.*)write sd s 0 strlen in
	if(lensent != strlen) then
	  trysend (c-1) (String.sub s (lensent-1) (strlen-lensent))
	else
	  ()
  in
  trysend 10 str;;


