open Unix;;
open Nettypes;;
open Holtypes;;

exception ParseWarning of string;;
exception ParseError of string;;

let assertw x y = if x then (raise(ParseWarning(y));()) else ();;
let asserte x y = if x then (raise(ParseError(y));()) else ();;

type icmp_partial =
    HOL_ICMP_IS1 of ip option
  | HOL_ICMP_IS2 of ip option
  | HOL_ICMP_IS3 of ip option
  | HOL_ICMP_IS4 of ip option
  | HOL_ICMP_PS3 of port option
  | HOL_ICMP_PS4 of port option
  | HOL_ICMP_PROTO of protocol
  | HOL_ICMP_SEQ of word32 option
  | HOL_ICMP_TYPE of icmp_type
;;

type icmp_status = {
    is1_up : bool;
    is2_up : bool;
    is3_up : bool;
    is4_up : bool;
    ps3_up : bool;
    ps4_up : bool;
    proto_up : bool;
    seq_up : bool;
    type_up : bool;
  } ;;

let clear_icmp_status =
  { is1_up = false; is2_up = false; is3_up = false; is4_up = false;
    ps3_up = false; ps4_up = false; proto_up = false; seq_up = false; type_up = false };;

let chk_missing_icmp x =
  asserte (not x.is1_up) "No icmp.is1 specified";
  asserte (not x.is2_up) "No icmp.is2 specified";
  asserte (not x.is3_up) "No icmp.is3 specified";
  asserte (not x.is4_up) "No icmp.is4 specified";
  asserte (not x.ps3_up) "No icmp.ps3 specified";
  asserte (not x.ps4_up) "No icmp.ps4 specified";
  asserte (not x.proto_up) "No icmp.proto specified";
  asserte (not x.seq_up) "No icmp.seq specified";
  asserte (not x.type_up) "No icmp.type specified";;

let clear_icmp_hol =
  { icmp_hol_is1 = None; icmp_hol_is2 = None;
    icmp_hol_is3 = None; icmp_hol_is4 = None;
    icmp_hol_ps3 = None; icmp_hol_ps4 = None;
    icmp_hol_proto = PROTO_UDP; icmp_hol_seq = None;
    icmp_hol_type = ICMP_NONE } ;;

let update_icmp update status oldrec =
  match update with
    HOL_ICMP_IS1(x) -> (assertw status.is1_up "Duplicate icmp.is1 fields in record. Using most recent.";
			{ status with is1_up = true },
			{ oldrec with icmp_hol_is1 = x })
  | HOL_ICMP_IS2(x) -> (assertw status.is2_up "Duplicate icmp.is2 fields in record. Using most recent.";
			{ status with is2_up = true },
			{ oldrec with icmp_hol_is2 = x })
  | HOL_ICMP_IS3(x) -> (assertw status.is3_up "Duplicated icmp.is3 fields in record. Using most recent.";
			{ status with is3_up = true },
			{ oldrec with icmp_hol_is3 = x })
  | HOL_ICMP_IS4(x) -> (assertw status.is4_up "Duplicated icmp.is4 fields in record. Using most recent.";
			{ status with is4_up = true },
			{ oldrec with icmp_hol_is4 = x })
  | HOL_ICMP_PS3(x) -> (assertw status.ps3_up "Duplicate icmp.ps3 fields in record. Using most recent.";
			{ status with ps3_up = true },
			{ oldrec with icmp_hol_ps3 = x })
  | HOL_ICMP_PS4(x) -> (assertw status.ps4_up "Duplicate icmp.ps4 fields in record. Using most recent.";
			{ status with ps4_up = true },
			{ oldrec with icmp_hol_ps4 = x })
  | HOL_ICMP_PROTO(x) -> (assertw status.proto_up "Duplicate icmp.proto fields in record. Using most recent.";
			  { status with proto_up = true },
			  { oldrec with icmp_hol_proto = x })
  | HOL_ICMP_SEQ(x) -> (assertw status.seq_up "Duplicated icmp.seq fields in record. Using most recent.";
			{ status with seq_up = true },
			{ oldrec with icmp_hol_seq = x })
  | HOL_ICMP_TYPE(x) -> (assertw status.type_up "Duplicate icmp.type fields in record. Using most recent.";
			 { status with type_up = true },
			 { oldrec with icmp_hol_type = x });;

type tcp_partial =
    HOL_TCP_IS1 of ip option
  | HOL_TCP_IS2 of ip option
  | HOL_TCP_PS1 of port option
  | HOL_TCP_PS2 of port option
  | HOL_TCP_SEQ of word32
  | HOL_TCP_ACK of word32
  | HOL_TCP_URG of bool
  | HOL_TCP_ACKF of bool
  | HOL_TCP_PSH of bool
  | HOL_TCP_RST of bool
  | HOL_TCP_SYN of bool
  | HOL_TCP_FIN of bool
  | HOL_TCP_WIN of word16
  | HOL_TCP_URP of word16
  | HOL_TCP_MSS of word16 option
  | HOL_TCP_SCALE of byte option
  | HOL_TCP_TS of (word32 * word32) option
  | HOL_TCP_DATA of byte list;;

type tcp_status = {
    is1_tup : bool;
    is2_tup : bool;
    ps1_tup : bool;
    ps2_tup : bool;
    seq_tup : bool;
    ack_tup : bool;
    urg_tup : bool;
    ackf_tup : bool;
    psh_tup : bool;
    rst_tup : bool;
    syn_tup : bool;
    fin_tup : bool;
    win_tup : bool;
    urp_tup : bool;
    mss_tup : bool;
    scale_tup : bool;
    ts_tup : bool;
    data_tup : bool;
  } ;;

let clear_tcp_status =
  { is1_tup = false; is2_tup = false; ps1_tup = false; ps2_tup = false;
    seq_tup = false; ack_tup = false; urg_tup = false; ackf_tup = false;
    psh_tup = false; rst_tup = false; syn_tup = false; fin_tup = false;
    win_tup = false; urp_tup = false; mss_tup = false; scale_tup = false;
    ts_tup = false; data_tup = false };;

let chk_missing_tcp x =
  asserte (not x.is1_tup) "No TCP.is1 specified";
  asserte (not x.is2_tup) "No TCP.is2 specified";
  asserte (not x.ps1_tup) "No TCP.ps1 specified";
  asserte (not x.ps2_tup) "No TCP.ps2 specified";
  asserte (not x.seq_tup) "No TCP.seq specified";
  asserte (not x.ack_tup) "No TCP.ack specified";
  asserte (not x.urg_tup) "No TCP.uRG specified";
  asserte (not x.ackf_tup) "No TCP.aCK specified";
  asserte (not x.psh_tup) "No TCP.pSH specified";
  asserte (not x.rst_tup) "No TCP.rST specified";
  asserte (not x.syn_tup) "No TCP.sYN specified";
  asserte (not x.fin_tup) "No TCP.fIN specified";
  asserte (not x.win_tup) "No TCP.wIN specified";
  asserte (not x.urp_tup) "No TCP.uRP specified";
  asserte (not x.mss_tup) "No TCP.mss specified";
  asserte (not x.scale_tup) "No TCP.ws specified";
  asserte (not x.ts_tup) "No TCP.ts specified";
  asserte (not x.data_tup) "No TCP.data specified";;


let clear_tcp_hol =
  { is1 = None; is2 = None; ps1 = None; ps2 = None; seq = uint 0;
    ack = uint 0; uRG = false; aCK = false; pSH = false; rST = false;
    sYN = false; fIN = false; win = uint 0; urp = uint 0;
    mss = None; scale = None; ts = None; data = [] };;

let update_tcp update status oldrec =
  match update with
    HOL_TCP_IS1(x) -> (assertw status.is1_tup "Duplicate tcp.is1 fields in record. Using most recent.";
		       { status with is1_tup = true },
		       { oldrec with is1 = x })
  | HOL_TCP_IS2(x) -> (assertw status.is2_tup "Duplicate tcp.is2 fields in record. Using most recent.";
		       { status with is2_tup = true },
		       { oldrec with is2 = x })
  | HOL_TCP_PS1(x) -> (assertw status.ps1_tup "Duplicate tcp.ps1 fields in record. Using most recent.";
		       { status with ps1_tup = true },
		       { oldrec with ps1 = x })
  | HOL_TCP_PS2(x) -> (assertw status.ps2_tup "Duplicate tcp.ps2 fields in record. Using most recent.";
		       { status with ps2_tup = true },
		       { oldrec with ps2 = x })
  | HOL_TCP_SEQ(x) -> (assertw status.seq_tup "Duplicate tcp.seq fields in record. Using most recent.";
		       { status with seq_tup = true },
		       { oldrec with seq = x })
  | HOL_TCP_ACK(x) -> (assertw status.ack_tup "Duplicate tcp.ack fields in record. Using most recent.";
		       { status with ack_tup = true },
		       { oldrec with ack = x })
  | HOL_TCP_URG(x) -> (assertw status.urg_tup "Duplicate tcp.uRG fields in record. Using most recent.";
		       { status with urg_tup = true },
		       { oldrec with uRG = x })
  | HOL_TCP_ACKF(x) -> (assertw status.ackf_tup "Duplicate tcp.aCK fields in record. Using most recent.";
		       { status with ackf_tup = true },
		       { oldrec with aCK = x })
  | HOL_TCP_PSH(x) -> (assertw status.psh_tup "Duplicate tcp.pSH fields in record. Using most recent.";
		       { status with psh_tup = true },
		       { oldrec with pSH = x })
  | HOL_TCP_RST(x) -> (assertw status.rst_tup "Duplicate tcp.rST fields in record. Using most recent.";
		       { status with rst_tup = true },
		       { oldrec with rST = x })
  | HOL_TCP_SYN(x) -> (assertw status.syn_tup "Duplicate tcp.sYN fields in record. Using most recent.";
		       { status with syn_tup = true },
		       { oldrec with sYN = x })
  | HOL_TCP_FIN(x) -> (assertw status.fin_tup "Duplicate tcp.fIN fields in record. Using most recent.";
		       { status with fin_tup = true },
		       { oldrec with fIN = x })
  | HOL_TCP_WIN(x) -> (assertw status.win_tup "Duplicate tcp.win fields in record. Using most recent.";
		       { status with win_tup = true },
		       { oldrec with win = x })
  | HOL_TCP_URP(x) -> (assertw status.urp_tup "Duplicate tcp.urp fields in record. Using most recent.";
		       { status with urp_tup = true },
		       { oldrec with urp = x })
  | HOL_TCP_MSS(x) -> (assertw status.mss_tup "Duplicate tcp.mss fields in record. Using most recent.";
		       { status with mss_tup = true },
		       { oldrec with mss = x })
  | HOL_TCP_SCALE(x) -> (assertw status.scale_tup "Duplicate tcp.scale fields in record. Using most recent.";
		       { status with scale_tup = true },
		       { oldrec with scale = x })
  | HOL_TCP_TS(x) -> (assertw status.ts_tup "Duplicate tcp.ts fields in record. Using most recent.";
		       { status with ts_tup = true },
		       { oldrec with ts = x })
  | HOL_TCP_DATA(x) -> (assertw status.data_tup "Duplicate tcp.data fields in record. Using most recent.";
		       { status with data_tup = true },
		       { oldrec with data = x });;

type udp_partial =
    HOL_UDP_IS1 of ip option
  | HOL_UDP_IS2 of ip option
  | HOL_UDP_PS1 of port option
  | HOL_UDP_PS2 of port option
  | HOL_UDP_DATA of byte list;;

type udp_status = {
    udp_is1_up : bool;
    udp_is2_up : bool;
    udp_ps1_up : bool;
    udp_ps2_up : bool;
    udp_data_up : bool;
  };;

let clear_udp_status =
  { udp_is1_up = false; udp_is2_up = false; udp_ps1_up = false;
    udp_ps2_up = false; udp_data_up = false };;

let chk_missing_udp x =
  asserte (not x.udp_is1_up) "No udp.is1 specified";
  asserte (not x.udp_is2_up) "No udp.is2 specified";
  asserte (not x.udp_ps1_up) "No udp.ps1 specified";
  asserte (not x.udp_ps2_up) "No udp.ps2 specified";
  asserte (not x.udp_data_up) "No udp.data specified";;

let clear_udp_hol =
  { udp_hol_is1 = None; udp_hol_is2 = None; udp_hol_ps1 = None; udp_hol_ps2 = None; udp_hol_data = [] };;

let update_udp update status oldrec =
  match update with
    HOL_UDP_IS1(x) -> (assertw status.udp_is1_up "Duplicate udp.is1 fields in record. Using most recent.";
		       { status with udp_is1_up = true },
		       { oldrec with udp_hol_is1 = x})
  | HOL_UDP_IS2(x) -> (assertw status.udp_is2_up "Duplicate upd.is2 fields in record. Using most recent.";
		       { status with udp_is2_up = true },
		       { oldrec with udp_hol_is2 = x})
  | HOL_UDP_PS1(x) -> (assertw status.udp_ps1_up "Duplicate udp.ps1 fields in record. Using most recent.";
		       { status with udp_ps1_up = true },
		       { oldrec with udp_hol_ps1 = x})
  | HOL_UDP_PS2(x) -> (assertw status.udp_ps2_up "Duplicate udp.ps2 fields in record. Using most recent.";
		       { status with udp_ps2_up = true },
		       { oldrec with udp_hol_ps2 = x })
  | HOL_UDP_DATA(x) -> (assertw status.udp_data_up "Duplicate data fields in record. Using most recent.";
			{ status with udp_data_up = true },
			{ oldrec with udp_hol_data = x });;

