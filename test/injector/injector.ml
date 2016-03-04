open Unix;;
open Nettypes;;
open Netconv;;
open Holparselib;;
open Rawsock;;
open Hol2net;;
open Holtypes;;
open Parserlib;;
open Printf;;

(* ---------------------------------------------------------------------- *)

exception Fatal of string;;

type requested_socket_type =
    REQ_TCP of string * string
  | REQ_UNIX of string;;

(* Command-line argument syntax *)
let cmdlineargs = "Usage: injector TCP ip port  OR  injector UNIX namedsocket";;

(* Parse the command-line arguments. Raise exception if incorrect *)
let check_cmdline_args argv =
  let len = Array.length argv in
  if(len = 3) then  REQ_UNIX(Array.get argv 2)
  else if(len = 4) then REQ_TCP(Array.get argv 2, Array.get argv 3)
  else raise(Fatal("Incorrect arguments: " ^ cmdlineargs));;

(* ---------------------------------------------------------------------- *)

(* Open the command channel socket *)
let opensocket requested_socket =
  let sd, addr =
    match requested_socket with
      REQ_TCP(ip, port) ->
	let sd = Unix.socket PF_INET Unix.SOCK_STREAM 0 in
	let _ = Unix.setsockopt sd SO_REUSEADDR true in
	let addr = ADDR_INET (inet_addr_of_string ip, int_of_string port) in
	sd, addr
    | REQ_UNIX(fname) ->
	(Unix.socket PF_UNIX Unix.SOCK_STREAM 0), ADDR_UNIX(fname) in
  let _ = Unix.bind sd addr in
  let _ = Unix.listen sd 0 in
  let (sdconn, sdaddr) = Unix.accept sd in
  sd, sdconn

(* ---------------------------------------------------------------------- *)

let do_message_processing holmsg =
  (* Construct the TCP or ICMP packet *)
  let (is1, is2, pkt),proto =
    match holmsg with
      TCPMSG(x) -> (tcp_flatten x, ip_proto_tcp)
    | UDPMSG(x) -> (udp_flatten x, ip_proto_udp)
    | ICMPMSG(x) -> (icmp_flatten x , ip_proto_icmp) in
  (* Encapsulate this in an IP packet *)
  let ippkt = ip_encapsulate is1 is2 proto pkt in
  (* Convert the IP packet to a string representation *)
  let outputstr = uint_list_to_string ippkt in

  (* Pull out the destination IP address to enable *)
  (* the packet's sending via a raw socket *)
  let is2 = match holmsg with
    TCPMSG(x) ->
      (match x.is2 with
	None -> raise(Fatal("Injector: Destination IP address can not be NONE"))
      | Some(ip) -> ip)
  | UDPMSG(x) ->
      (match x.udp_hol_is2 with
	None -> raise(Fatal("Injector: Destination IP address can not be NONE"))
      | Some(ip) -> ip)
  | ICMPMSG(x) ->
      (match x.icmp_hol_is2 with
	None -> raise(Fatal("Injector: Destination IP address can not be NONE"))
      | Some(ip) -> ip) in
  let ip_component_list = output_uint32_net is2 [] in
  let ip_str =
    match ip_component_list with
      a::b::c::d::[] ->
	(Int64.to_string a)^"."^(Int64.to_string b)^"."^
	(Int64.to_string c)^"."^(Int64.to_string d)
    | _ -> "0.0.0.0" in

  (* Return the ip packet and destination ip address strings*)
  outputstr, ip_str;;


(* The parse and inject loop *)
let do_parse_and_inject sd rawsd =
  let parseenv = Threadparsing.create_parse_env () in
  try
    let lexbuf = Lexing.from_channel (Unix.in_channel_of_descr sd) in
    while true do
      try
	(* Parse the next message from the command channel *)
	let parser_output = Parser.main parseenv Lexer.token lexbuf in
        let holmsg =
	  match parser_output with
	    PARSE_RETURN(_,_, HOLSNDMSG(x)) -> x
	  | _ -> raise(Fatal("Parse error: incorrect message type returned")) in

	(* Process the message to form a packet suitable for injection *)
	let outputstr, ipstr = do_message_processing holmsg in

	(* Inject the raw packet using the raw socket *)
	let _ = raw_sendto rawsd outputstr ipstr in
	()
      with ParseWarning(s) ->
	print_endline ("Warning: "^s)
    done
  with Lexer.Eof ->
    ();;

(* ---------------------------------------------------------------------- *)

(* Parse cmd-line args and open the command channel's socket *)
let requested_socket = check_cmdline_args Sys.argv in
let sd, sdconn = opensocket requested_socket in
(* Create the raw socket for injection *)
let rawsd = raw_socket PF_INET 0 in
let _ = raw_sockopt_hdrincl rawsd in
(* Sit in a tight parser loop, parsing and injecting until EOF *)
let _ = do_parse_and_inject sdconn rawsd in
(* Close everything down *)
let _ = Unix.close sdconn in
Unix.close sd;;




