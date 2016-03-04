open Ocamllib;;
open Holtypes;;
open Tcpcbtypes;;
open Libcalls;;

type time = int64;;
val time_base_us: int64;;

type libcall = tid * libstructure;;
type libreturn = tid * libreturnstructure;;
type tcptrace = tcpaction * tracesid * traceaddr * tcpstate * tcpcb;;
type duration = DURATION of time * time

type ns_parse_data =
    HOLSNDMSG of holmsg
  | HOLLOOPMSG of holmsg
  | HOLRCVMSG of holmsg
  | LIBCALL of libcall
  | LIBRETURN of libreturn
  | TCPTRACE of tcptrace
  | HOLEPSILON of duration
  | HOLABSTIME of time * time

type timecomment =
    TIMECOMMENT of time * string
;;


type ns_parse_return =
    PARSE_RETURN of timecomment option * string list option * ns_parse_data
;;


type spec3_parse_data =
  | HOLLN1_HOST of string * ns_parse_data (* expect e.g. no HOLEPSILON in the parse_data *)
  | HOLLN1_EPSILON of duration
  | HOLLN1_ABSTIME of time * time

type spec3_parse_return =
    SPEC3_PARSE_RETURN of timecomment option * string list option * spec3_parse_data
