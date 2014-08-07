open Unix;;

exception Fatal of string;;

let sd = 
  try socket PF_INET SOCK_STREAM 6
  with Unix_error(e,s1,s2) ->
    raise(Fatal("Error:"^(error_message(e))^s1^s2)) 
in
  let opt = setsockopt sd SO_KEEPALIVE true 
  in
    if (getsockopt sd SO_KEEPALIVE) = true   
    then print_endline("SO_KEEPALIVE")
    else print_endline("!SO_KEEPALIVE");;
