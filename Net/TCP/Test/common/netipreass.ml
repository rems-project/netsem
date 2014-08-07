(* *************** *)
(* IP Reassembly   *)
(* *************** *)

open Nettypes;;
open Netconv;;

(* nice to keep all fragments untouched, so we can play with different
   reassembly semantics.  For example, Markus and Richard are
   interested to know if the reassembly semantics in the IDS is the
   same as the reassembly semantics in the host; otherwise an attacker
   could slip some data past the IDS without being detected.
*)

(* we are however committed to reassemble implementations that are online
   (as soon as enough frags arrive, reassembly is performed) and that
   forget all about an IP ID as soon as reassembly is done.
*)

type fragment = {
    f_p   : ip_packet;
    f_ts  : timestamp;
  }

(* unique datagram identifier *)
type ip_uniq = {
    ipu_id  : uint;
    ipu_src : uint;
    ipu_dst : uint;
    ipu_p   : uint;
  }

type defrag_chain = {
    dfc_uniq : ip_uniq;        (* unique identifier of all fragments in chain *)
    dfc_ts   : timestamp;      (* invariant: earliest timestamp in dfc_data *)
    dfc_data : fragment list;  (* invariant: in reverse order of arrival; nonempty *)
  }

type reass_frag = {
    rf_off  : int;
    rf_dlen : int;
    rf_mf   : bool;
    rf_data : char list;
  }

type defrag_state = defrag_chain list  (* set of defrag chains *)

(* is a packet fragmented? *)
let is_fragmented (p : ip_packet) =
  p.ip_h.ip_mf || p.ip_h.ip_off > uint 0

(* what is the unique ID of this packet's datagram? *)
let get_uniq (p : ip_packet) =
  { ipu_id  = p.ip_h.ip_id;
    ipu_src = p.ip_h.ip_src;
    ipu_dst = p.ip_h.ip_dst;
    ipu_p   = p.ip_h.ip_p;
  }

(* find the chain matching `uniq' and do `mdf' to it;
   if not present, do `ins' to the entire list *)

(* `mdf' takes the matching defrag_chain and either returns a modified
    defrag_chain or deletes it; it also returns an 'a *)

(* `ins' takes the uniq and the entire defrag_chain list and returns a
    modified defrag_chain list; it also returns an 'a *)

let find_chain
    (uniq : ip_uniq)
    (mdf  : defrag_chain -> (defrag_chain option * 'a))
    (ins  : ip_uniq -> defrag_chain list -> (defrag_chain list * 'a))
    (dfcs : defrag_chain list) =
  let rec find_chain0 dfcsL dfcsR = match dfcsR with
    [] ->
      ins uniq (List.rev dfcsL)
  | (dfc::dfcs) ->
      if uniq = dfc.dfc_uniq then
        match mdf dfc with
          (Some dfc', a) ->
            (List.rev (dfc' :: dfcsL) @ dfcsR , a)
        | (None, a) ->
            (List.rev dfcsL @ dfcsR, a)
      else
        find_chain0 (dfc :: dfcsL) dfcsR in
  find_chain0 [] dfcs

(* given a defrag_chain (list of packets), rebuild the IP datagram
   if possible, or None if not *)
(* algorithm follows TCPv2pp293-5 closely *)
(* this is a bit weird, because it does it all at once, rather than
   incrementally. *)
let reass_chain (dfc : defrag_chain) =

  let go frag rfs = (* insert an IP packet (frag) into the chain *)
    let frf = (* extract relevant (data) part of packet into fragment data structure *)
      { rf_off  = int frag.f_p.ip_h.ip_off;
        rf_dlen = int frag.f_p.ip_h.ip_len - int frag.f_p.ip_h.ip_hl * 4;
        rf_mf   = frag.f_p.ip_h.ip_mf;
        rf_data = frag.f_p.ip_data;  (* should check right length? *)
      } in
    if rfs = [] then  (* this is the first fragment; we're done *)
      [frf]
    else  (* this is not the first fragment; put it in the right place and clip *)

      let rec loop rfsL rfsR = (* find the appropriate place for the fragment *)
        match rfsR with
          (rf::rfsR') when rf.rf_off <= frf.rf_off ->
            loop (rf::rfsL) rfsR'
        | _ ->
            dopre rfsL rfsR

      and dopre rfsL rfsR = (* trim any left overlap from frf *)
        match rfsL with
          (rfL::_) ->
            let i = rfL.rf_off + rfL.rf_dlen - frf.rf_dlen in
            if i >= frf.rf_dlen then (* prev frag completely overlaps; frf redundant so drop; done *)
              List.rev rfsL @ rfsR
            else
              let frf' =
                if i > 0 then  (* prev frag overlaps; drop a prefix from frf and continue *)
                  { rf_off  = frf.rf_off + i;
                    rf_dlen = frf.rf_dlen - i;
                    rf_mf   = frf.rf_mf;
                    rf_data = drop i frf.rf_data;
                  }
                else  (* no left overlap; continue *)
                  frf in
              dopost rfsL rfsR frf'
        | [] -> (* no prev frag; continue *)
            dopost rfsL rfsR frf

      and dopost rfsL rfsR frf = (* trim any right overlap from rfsR *)
        match rfsR with
          (rfR::rfsR') ->
            let i = frf.rf_off + frf.rf_dlen - rfR.rf_off in
            if i >= rfR.rf_dlen then  (* next frag completely overlapped; drop it *)
              dopost rfsL rfsR' frf
            else
              let rfR' =
                if i <= 0 then  (* no right overlap; done *)
                  rfR
                else  (* next frag partially overlapped; trim next frag and continue *)
                  { rf_off  = rfR.rf_off + i;
                    rf_dlen = rfR.rf_dlen - i;
                    rf_mf   = rfR.rf_mf;
                    rf_data = drop i rfR.rf_data;
                  } in
              List.rev (frf::rfsL) @ (rfR'::rfsR')
        | [] -> (* no next frag; done *)
            List.rev (frf::rfsL) in

      (* insert the frag in the right place *)
      loop [] rfs in

  (* insert each fragment in the defrag_chain into the fragment list *)
  let rfs = List.fold_right go (List.rev dfc.dfc_data) [] in
    (* recall dfc_data is in reverse order! *)

  (* check for completion, and build data if complete *)
  let rec agglom data rfs n = match rfs with
    (rf::rfs) ->
      if rf.rf_off = n then                    (* no gap *)
        let data' = rf.rf_data :: data in
        let n'    = rf.rf_dlen + n in
        if not rf.rf_mf then                   (* final fragment *)
          (assert_packet_wf "More fragments after final fragment" (rfs = []);
           Some (n',List.flatten (List.rev data')))
        else                                   (* not final fragment *)
          agglom data' rfs n'
      else                                     (* gap *)
        None
  | [] ->
      None in                                  (* no final fragment *)

  (* build the completed IP datagram, or None *)
  match agglom [] rfs 0 with
    Some (dlen,data) ->
      Some { ip_h = { (List.hd dfc.dfc_data).f_p.ip_h with
                      ip_len = uint (dlen + int (List.hd dfc.dfc_data).f_p.ip_h.ip_hl * 4);
                      ip_off = uint 0;
                      ip_mf = false;
                      ip_sum = uint 0;  (* SHOULD RECALC CHECKSUM?!! *)
                    };
             ip_data = data;
           }
  | None ->
      (None : ip_packet option)


(* prepend a new defrag_chain to the defrag chain list *)
(* to be given a frag and passed to `find_chain' as the `ins' argument *)
(* ASSUMES uniq = get_uniq frag *)
let new_chain frag uniq dfcs =
  (
   { dfc_uniq = uniq;
     dfc_ts   = frag.f_ts;
     dfc_data = [frag];
   } :: dfcs,  (* prepend fragment chain *)
   None        (* not a complete datagram *)
  )

(* add a fragment to an existing defrag chain *)
(* to be given a frag and passed to `find_chain' as the `mdf' argument *)
(* ASSUMES get_uniq frag is correct *)
let add_to_chain frag dfc =
  let dfc = { dfc with
              dfc_data = frag :: dfc.dfc_data
            } in
  match reass_chain dfc with
    Some ip -> (None,      (* delete fragment chain *)
                Some ip)   (* return completed datagram *)
  | None    -> (Some dfc,  (* store modified fragment chain *)
                None)      (* not a complete datagram *)


(* timeout for defrag chain in seconds *)
let iPFRAGTTL = {t_sec = uint 30; t_usec = uint 0;}  (* BSD value acc TCPv2p292 *)

let ip_input (st : defrag_state) (ts : timestamp) (ip : ip_packet) =

  (* time out old defrag chains *)
  let st = List.filter (fun dfc -> ((ts.t_sec <. (dfc.dfc_ts.t_sec +. iPFRAGTTL.t_sec)) ||
                                   ((ts.t_sec ==. (dfc.dfc_ts.t_sec +. iPFRAGTTL.t_sec)) &&
				    (ts.t_usec <. (dfc.dfc_ts.t_usec +. iPFRAGTTL.t_usec))))) st in
    (* should really send an ICMP if we have the first fragment;
       see RFC122 and TCPv2p292 *)

  if not (is_fragmented ip) then  (* not fragmented; return immediately *)
    (st,Some ip)
  else  (* fragmented; process *)

    (* build fragment *)
    let frag = { f_p  = ip;
                 f_ts = ts;
               } in
    let uniq = get_uniq ip in

    (* insert into appropriate chain and possibly return reassembled datagram *)
    (find_chain uniq (add_to_chain frag) (new_chain frag) st
       : defrag_state * ip_packet option)

(* initial state for above *)
let init_ip_input_state = []












