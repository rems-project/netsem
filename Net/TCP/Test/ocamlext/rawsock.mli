open Unix;;

val raw_socket: socket_domain -> int -> file_descr

val raw_sockopt_hdrincl: file_descr -> unit

val raw_sendto: file_descr -> string -> string (*ip addr*) -> unit
