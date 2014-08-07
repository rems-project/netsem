open Unix;;

external raw_socket: socket_domain -> int -> file_descr = "raw_socket"

external raw_sockopt_hdrincl: file_descr -> unit = "raw_sockopt_hdrincl"

external raw_sendto: file_descr -> string -> string -> unit = "raw_sendto"
