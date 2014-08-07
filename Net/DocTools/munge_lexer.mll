(* File lexer.mll *)
{
exception Eof
exception Deunderscore
exception Deminus



let typehack = ref true   (* true if types take precedence over vars; false the other way round *)

let is_rule s = try
                  (String.index s '.' ) <> (String.length s) -1
                with
                  Not_found -> false

(* watch out - this code is copied in rules_to_latex.ml and munge_lexer.mll.  yuk *)
let letterify_char c =
  if ((c>='a' && c<='z') || (c>='A' && c <='Z'))
  then c
  else if c='.' then 'X'
  else if (c>= '1' && c<='9') then char_of_int ((int_of_char c)+16)
  else if (c='0') then 'Z'
  else c

let name_to_latex_command s =
  let ss = String.copy s in
  for i =0 to (String.length s)-1 do
    String.set ss i (letterify_char (String.get ss i))
  done ;
  ss^"X"



let is_type s = List.mem s
[ "fd"            ;
  "ip"            ;
  "port"          ;
  "error"         ;
  "netmask"       ;
  "ifid"          ;
  "sockopt"       ;
  "int"           ;
  "bool"          ;
  "string"        ;
  "list"          ;
  "err"           ;
  "void"          ;
  "set"           ;
  "ipBody"        ;
  "msg"           ;
  "ifd"           ;
  "flags"         ;
  "socket"        ;
  "boxid"         ;   "hostid" ;
  "boxThreadState";   "hostThreadState" ;
  "box"           ;   "host" ;
  "network" ;
  "exn"  ;
  "lift"  ;
  "ref"  ;
  "msg-ok" ;
  "ifd-set-ok";
  "socket-ok";
  "msg-oq-ok";
  "box-ok" ; "host-ok" ;
]


let is_con s = List.mem s
[ "EACCES"             ;
  "EADDRINUSE"         ;
  "EADDRNOTAVAIL"      ;
  "EAGAIN"             ;
  "EBADF"              ;
  "ECONNREFUSED"       ;
  "EHOSTUNREACH"       ;
  "EINTR"              ;
  "EINVAL"             ;
  "EMFILE"             ;
  "EMSGSIZE"           ;
  "ENFILE"             ;
  "ENOBUFS"            ;
  "ENOMEM"             ;
  "ENOTCONN"           ;
  "ENOTSOCK"           ;
  "EPERM"              ;
  "EDESTADDRREQ"  ;
  "EISCONN"  ;
  "EWOULDBLOCK"  ;
  "ENETUNREACH"  ;
  "BadInjection" ;
  "lo"                 ;
  "eth0"               ;
  "eth1"               ;
  "true"         ;
  "false"         ;
  "nil"                ;
  "OK"                 ;
  "Fail"               ;
  "UDP"                ;
  "IP"                 ;
  "IF"                 ;
  "Flags"              ;
  "Sock"               ;
  "alan"               ;
  "emil"               ;
  "john"               ;
  "kurt"               ;
  "astrocyte"          ;
  "Run"                ;
  "Term"               ;
  "Ret"                ;
  "RET"                ;
  "Sendto2"            ;
  "Recvfrom2"          ;
  "Select2"            ;
  "Print2"             ;
  "Box"                ; "Host" ;
  "Lift"  ;
  "Star"  ;
  "c" ;
  "RetOK";
  "RetFail";
  "Op2" ;
  "SO_BSDCOMPAT"       ;
  "SO_REUSEADDR"       ;
  "ICMP_HOST_UNREACH"  ;
  "ICMP_PORT_UNREACH"  ;
  "ICMP_X_UNREACH"  ;
  "Match_failure"  ;
  "SOL_SOCKET";
  "SO_ERROR"
]




let deunderscore_and_minus s =
  Str.global_replace (Str.regexp "_") "\\_"
    (Str.global_replace (Str.regexp "-") "\\mbox{-}"
      s)


let deminus s =
  if s ="msg-ok" then "msg\\mbox{-}ok"
  else if s ="ifd-set-ok" then "ifd\\mbox{-}set\\mbox{-}ok"
  else if s ="socket-ok" then "socket\\mbox{-}ok"
  else if s ="box-ok" then "box\\mbox{-}ok"
   else if s = "host-ok" then "host\\mbox{-}ok"
  else if s = "msg-oq-ok" then "msg\\mbox{-}oq\\mbox{-}ok"
  else raise Deminus





let is_lib s = List.mem s [
  "socket"      ;
  "bind"        ;
  "connect"     ;
  "disconnect"  ;
  "getsockname" ;
  "getpeername" ;
  "geterr"      ;
  "getsockopt"  ;
  "setsockopt"  ;
  "sendto"      ;
  "recvfrom"    ;
  "close"       ;
  "select"      ;
  "getifaddrs"  ;
  "exit"        ;
  "print_endline_flush" ;
  "port_of_int"      ;
  "int_of_port"      ;
  "ip_of_string"     ;
  "iplift_of_string" ;
  "string_of_iplift" ;
  "string_of_int" ;
  "create"  ;
  "delay"
]


let is_aux s = List.mem s
 [ "autobind" ;
  "lookup"   ;
  "outroute" ;
  "socks"    ;
  "sockfd"  ;
  "sockfds"  ;
  "unused"   ;
  "ephemeral";
  "privileged";
  "ephemeralErrors" ;
  "reuseaddr";
  "bsdcompat";
  "setbsdcompat" ;
  "setreuseaddr" ;
  "UDPpayloadMax" ;
  "orderings" ;
  "size"  ;
  "Con" ;
  "arity" ;
  "store"  ;
  "closed";
  "localhost";
  "Loopback" ;
  "loop" ;
  "LOOPBACK"  ;
  "MARTIAN"  ;
  "LOCAL"  ;
  "MCAST"  ;
  "MULTICAST"  ;
  "BADCLASS"  ;
  "ZERONET"  ;
  "LIB"  ;
  "LIBEX"  ;
  "SocketUDP"  ;
  "TinyStdio"  ;
  "enqueue"  ;
  "dequeue"  ;
  "dosend"  ;
  "boxids" ; "hostids" ;
  "threadids"  ;
  "btsType" ; "htsType" ;
  "RET" ;
  "CALL";
  "TAU" ;
  "PROG" ;
  "match" ;
  "score" ;
  "martian"  ;
  "loopback"  ;
  "Lbox"  ; "Lhost" ;
  "Lnetwork"  ;
  "Lthread"  ;
  "function"  ;
  "let"  ;
  "raise"  ;
  "try"  ;
  "while"  ;
  "done";
  "rec" ;
  "if" ;
  "iserr";
  "isterm" ;
  "Alan";
  "Kurt";
  "console" ;
  "succeed" ;
  "enter2" ;
(*  "exit";  clashes with is_lib *)
  "fail";
  "badfail";
  "accept";
  "emit";
  "slowsucceed";
  "slowfail";
  "slowintr";
  "slowbadfail";
  "internaldelivery";
  "disjoint_addr";
  "dom";
  "instep";
  "Crash";
  "crash";
  "map";
  "image" ;
  "val"  ;
  "unit"
 ]



let is_aux_infix s = List.mem s
 [ "and";
   "or" ;
   "else" ;
   "then" ;
   "do";
  "in";
   "with";
   "ref"
  ]


let is_var_prefix s = List.mem s
[ "v" ;
  "f"   ;
  "ifds" ;
  "t"   ;
  "s"   ;
  "oq"  ;
  "oqf" ;
  "fd"  ;
  "i"   ;
  "p"   ;
  "e"   ;
  "tm"  ;
  "mq"  ;
  "is"  ;
  "ps"  ;
  "es"  ;
  "tms" ;
  "E"   ;
  "F"   ;
  "H"   ;
  "Q"   ;
  "OP"  ;
  "ifid";
  "iset";
  "iprimary";
  "netmask";
  "readseq" ;
  "writeseq" ;
  "opt" ;
  "iflist" ;
  "T" ;
  "TL" ;
  "data"  ;
  "ra"  ;
  "bc"  ;
  "body" ;
  "nb"  ;
  "nm"  ;
  "mtch";
  "expr";
  "fds"
]

let is_var_underscore s = List.mem s
[
  "status_ref"  ;
  "receiver_thread"  ;
  "get_status"  ;
  "sender_thread"  ;
  "start_heartbeat_a"  ;
  "start_heartbeat_k" ;
  "i_alan";
  "i_kurt"
]


let is_var s = (Str.string_match
                  (Str.regexp "\\([A-Za-z]+\\)[0-9]*[']*")
                  s
                  0 ) &&
               (Str.match_end() = String.length s) &&
               (is_var_prefix (Str.matched_group 1 s))

let subscript_var s =
  let _ = (Str.string_match
             (Str.regexp "\\([A-Za-z]+\\)\\([0-9]*\\)\\([']*\\)")
             s
             0 ) in
  if "" <> (Str.matched_group 2 s) then
    ((Str.matched_group 1 s)^(Str.matched_group 3 s)^"_{"^(Str.matched_group 2 s)^"}")
  else
    (Str.matched_group 1 s)^(Str.matched_group 3 s)


let extra_left_space s = if List.mem s  [
  "done";
  "list"        ;
  "set"  ;
  "err"  ;
  "store";
  "closed";
  "ref";
  "msg-ok" ;
  "msg-oq-ok" ;
  "ifd-set-ok";
  "socket-ok";
  "box-ok"; "host-ok" ;
  "network"
] then "\\," else ""


let extra_right_space s = if List.mem s  [
  "Select2";
  "Ret";
  "Sendto2";
  "Recvfrom2";
  "Print2";
  "console";
  "reuseaddr";
  "bsdcompat";
  "setbsdcompat" ;
  "setreuseaddr" ;
  "if";
  "while";
  "function";
  "try";
  "let";
  "rec";
  "raise";
  "Fail"        ;
  "disconnect"  ;
  "getsockname" ;
  "getpeername" ;
  "geterr"      ;
  "close"       ;
  "exit"        ;
  "lookup"      ;
  "print_endline_flush" ;
  "port_of_int" ;
  "ip_of_string"
] then "\\;" else ""




let space s =
  (extra_left_space s)^s^(extra_right_space s)

let write_unseen_string s = prerr_endline ("  \"" ^ s ^ "\"  ; ")

let transform s =
  let s' = deunderscore_and_minus s and
      lsp = extra_left_space s and
      rsp = extra_right_space s in
  let sps' = lsp ^ s' ^ rsp in

  if (is_rule s) then                 "\\tsrule{"^sps'^"}" else
  if (is_con s) then                  "\\tscon{"^sps'^"}" else
  if (is_aux s) then                  "\\tsaux{"^sps'^"}" else
  if (is_aux_infix s) then            "\\tsaux{\\ "^sps'^"\\ }" else
  if (!typehack) then (
    if (is_type s) then               "\\tstype{"^sps'^"}" else
    if (is_lib s) then                "\\tslib{"^sps'^"}" else
    if (is_var s) then                "\\tsvar{"^lsp^(subscript_var s)^rsp^"}" else
    if (is_var_underscore s) then     "\\tsvar{"^sps'^"}" else
    (write_unseen_string s ; (""^s^""))
   ) else (
    if (is_lib s) then                "\\tslib{"^sps'^"}" else
    if (is_var s) then                "\\tsvar{"^lsp^(subscript_var s)^rsp^"}" else
    if (is_var_underscore s) then     "\\tsvar{"^sps'^"}" else
    if (is_type s) then               "\\tstype{"^sps'^"}" else
    (write_unseen_string s ; (""^s^""))
   )

let lift      = "\\lift{}"
let arrow     = "\\totype{}"
let turnstile = "\\vdash{}"
let cce       = "\\cce{}"
let colon     = "\\oftype{}"
let cons      = "\\cons{}"

let debug s = () (*print_endline s*)

let print_indent s = (
  print_string "\\\\\n" ;
  for i = 1 to (String.length s) -1
  do
    print_string "\\Mindent{}"
  done )

}


rule
  munge = parse
    "<["         { mungeb lexbuf }
  | "<HACK-TYPE>" { typehack := true  ; munge lexbuf }
  | "<HACK-VAR>"  { typehack := false ; munge lexbuf }
  | "\\showrule{" { print_string "\\showrule{\\"; mungec lexbuf }
  | _            { print_string (Lexing.lexeme lexbuf) ; munge  lexbuf }
  | eof          { raise Eof }


and
  mungeb = parse
    "]>"    { munge lexbuf }
  | "<["    { print_string "WARNING: UNEXPECTED <[ IN MUNGE\n"; prerr_endline "WARNING: UNEXPECTED <[ IN MUNGE\n"; munge lexbuf }
  | ['A'-'Z' 'a'-'z'] (['A'-'Z' 'a'-'z' '0'-'9'] | ('_' ['A'-'Z' 'a'-'z'] ) | (['.' '-'] ['A'-'Z' 'a'-'z' '0'-'9' '*']))* ('\''*)
            { print_string (transform (Lexing.lexeme lexbuf)) ; mungeb lexbuf}
  | "\\" ['A'-'Z' 'a'-'z' ] +  { print_string (Lexing.lexeme lexbuf) ; mungeb lexbuf}
  | "\""    { print_string "\\Mquotedstring{" ;  munged lexbuf }
  | '^'     { print_string "\\Mcaret{}" ; mungeb lexbuf }
  | "-->"   { print_string "\\Maarrow{}"    ; mungeb lexbuf }
  | "->"    { print_string "\\Marrow{}"    ; mungeb lexbuf }
  | "=>"    { print_string "\\MArrow{}" ; mungeb lexbuf }
  | "<=>"    { print_string "\\MDArrow{}" ; mungeb lexbuf }
  | ";"     { print_string "\\Msemicolon{}"   ; mungeb lexbuf }
  | ";;"     { print_string "\\Msemisemicolon{}"   ; mungeb lexbuf }
  | "::="   { print_string "\\Mcce{}"     ; mungeb lexbuf }
  | ":="   { print_string "\\Mce{}"     ; mungeb lexbuf }
  | "::"    { print_string "\\Mcoloncolon{}"    ; mungeb lexbuf }
  | ":"     { print_string "\\Mcolon{}" ; mungeb lexbuf }
  | "[]"    { print_string "\\Mbrackets{}" ; mungeb lexbuf }
  | "<HACK-TYPE>" { typehack := true  ; mungeb lexbuf }
  | "<HACK-VAR>"  { typehack := false ; mungeb lexbuf }
  | _       { print_string (Lexing.lexeme lexbuf); mungeb lexbuf }
  | eof     { () }
and
  mungec = parse
    ['A'-'Z' 'a'-'z' '0'-'9' '.']*  {print_string (name_to_latex_command (Lexing.lexeme lexbuf)) ; mungec lexbuf }
  | "}"                             {print_string "}"  ; munge lexbuf }
  | _                               {print_string "SURPRISE IN MUNGEC" ; munge lexbuf }
and
  munged = parse
    [^'"']*   {print_string  (Lexing.lexeme lexbuf)  ;  munged lexbuf }
  | "\""      {print_string  "}"  ;                    mungeb lexbuf }

and
  rebracket = parse
    "[["    {print_string "$<[" ; rebracket lexbuf }
  | "]]"    {print_string "]>$" ; rebracket lexbuf }
  | _       {print_string (Lexing.lexeme lexbuf); rebracket lexbuf }
  | eof     { () }

and
  munge_ocaml = parse
    "open Udplange;;\n"   { typehack := false ;  munge_ocaml_b lexbuf }
  | "open Udplange2;;\n"  { typehack := false ;  munge_ocaml_b lexbuf }
  | "(*start_munge_types_true*)\n"   { typehack := true ;  munge_ocaml_b lexbuf }
  | "(*start_munge_types_false*)\n"   { typehack := false ;  munge_ocaml_b lexbuf }
  |  _                    { munge_ocaml lexbuf }
  |  eof                  { () }

and
  munge_ocaml_b = parse
    "Lift"  {print_string "\\Mcaret{}" ; munge_ocaml_b lexbuf }
  | "lift"  {print_string "\\Mcaret{}" ; munge_ocaml_b lexbuf }
  | "Star"  {print_string "*" ; munge_ocaml_b lexbuf }
  | ['A'-'Z' 'a'-'z'] (['A'-'Z' 'a'-'z' '0'-'9'] | ('_' ['A'-'Z' 'a'-'z'] ) | (['.' '-'] ['A'-'Z' 'a'-'z' '0'-'9']))* ('\''*){ print_string (transform (Lexing.lexeme lexbuf)) ; munge_ocaml_b lexbuf}
  |  "UDP(Unix." {print_string ((transform "UDP")^"(")  ; munge_ocaml_b lexbuf }
  | "->"    { print_string "\\Marrow{}"    ; munge_ocaml_b lexbuf }
  | "[]"    { print_string "\\Mbrackets{}" ; munge_ocaml_b lexbuf }
  | '_'     { print_string "\\_" ; munge_ocaml_b lexbuf }
  | "\""    { print_string "\\Mquotedstring{" ; munge_ocaml_c lexbuf }
  | "\n"" "*   { print_indent (Lexing.lexeme lexbuf); munge_ocaml_b lexbuf }
  | _          { print_string (Lexing.lexeme lexbuf); munge_ocaml_b lexbuf }
  | '(' '*' [^'*'] * '*' ')' {print_string ("\\Mcomment{"^(Lexing.lexeme lexbuf)^"}") ; munge_ocaml_b lexbuf }
  | eof        { () }


and
  munge_ocaml_c = parse
    [^'"']*   {print_string  (Lexing.lexeme lexbuf)  ;  munge_ocaml_c lexbuf }
  | "\""      {print_string  "}"  ;                    munge_ocaml_b lexbuf }
and
  wc = parse
    "\\"['A'-'Z' 'a'-'z']+                   {wc lexbuf}
  | "\\["                                    {wc_b lexbuf}
  | "[["                                     {wc_c lexbuf}
  | "%whichversion.1"                        {wc_d lexbuf}
  | "%"                                      {wc_e lexbuf}
  | "\\mref{"['A'-'Z' 'a'-'z' '0'-'9']*"}"   {wc lexbuf}
  | "\\mlabel{"['A'-'Z' 'a'-'z' '0'-'9']*"}" {wc lexbuf}
  | "\\xindex{"['A'-'Z' 'a'-'z' '0'-'9']*"}" {wc lexbuf}
  | ['A'-'Z' 'a'-'z']       {print_string (Lexing.lexeme lexbuf); wc lexbuf }
  | ['\n']                  {print_string "\n"; wc lexbuf }
  | [^'\n' 'A'-'Z' 'a'-'z'] {print_string " "; wc lexbuf }
  | eof     { () }
and
  wc_b = parse
    "\\]"                       {wc lexbuf}
  | _                           {wc_b lexbuf}
and
  wc_c = parse
    "]]"                        {wc lexbuf}
  | _                           {wc_c lexbuf}
and
  wc_d = parse
    "whichversion.2"            {wc lexbuf}
  | _                           {wc_d lexbuf}
and
  wc_e = parse
    '\n'                        {print_string "\n"; wc lexbuf}
  | [^'\n']                     {wc_e lexbuf}




