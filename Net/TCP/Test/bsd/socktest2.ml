open Unix;;

exception Error of string;;

let sd =
  try socket PF_INET SOCK_RAW 0
  with Unix_error(e, s1, s2) ->
    raise(Error("Error:" ^ error_message(e) ^ s1 ^ s2))
in
  let opt = ip_setsockopt sd IP_HDRINCL true 
  in
    if (ip_getsockopt sd IP_HDRINCL) = true   
    then print_endline("IP_HDRINCL")
    else print_endline("!IP_HDRINCL");;
