(* ********* *)
(* test code *)
(* ********* *)

(* here's a good capture command, to run on kurt (Linux):

# tcpdump -p -i eth0 -s 65535  -c 10 tcp and not host kurt

*)

(*
let chan = open_in "dump.dmp"
let pcap_chars =
  let rec loop cs =
    match
      (try Some (input_char chan) with
        End_of_file ->
          None) with
      Some c -> loop (c::cs)
    | None   -> cs
  in List.rev (loop [])

let pfh,c = parse_pcap_file_header pcap_chars

let rec loop c st = match c with
  [] ->
    ()
| _ ->
    let (ts,ip),c = parse_pcapfile_ip_packet pfh c in
    match ip_input st ts ip with
      (st,Some ip) ->
        let tcp = parse_tcp_datagram ip in
        let _ = printf "\n----TCP datagram:----\n" in
        let _ = render_tcp_datagram tcp in
        let _ = print_newline () in
        loop c st
    | (st,None) ->
        let _ = printf "\n----fragment----\n" in
        let _ = print_newline () in
        loop c st

let _ = loop c init_ip_input_state
*)
