(* Usage: conflate [trace0 trace1 ...]

   conflate is the trace conflater that takes spec1 traces and
   produces a spec1 Ln1 nettrace.

   Input are trace files trace0 ... Outputs merged nettrace on stdout,
   and versions of trace0 ... with additional epsilon transitions
   (i.e. projection of nettrace back onto hosts) in
   trace0.epsilon ...

   conflate is almost idempotent in the sense that running on
   generated .epsilon traces

   conflate trace0.epsilon

   should produce a trace0.epsilon.epsilon which is identical to the
   .epsilon. This is not quite true because the conflate index comment
   gets reinserted.

   N.B. conflate omits files that don't have an abstime label (and by
   implication no further labels). This means that it is possible to
   run conflate on a file, and no .epsilon will be generated. In this
   case, the network trace will consist of a single default abstime
   label, which is the result when running conflate with no input
   traces.

*)


(* FIXME tjr this is still pretty hacky- the downside of having a
   terrible parser that, e.g. parses initial_host s as comments.

   Really we need a model of the HOL datatypes in OCaml, with parsing
   and pretty printing functions. Amazingly, this has not been done so
   far. So we write the code in terms of parsereturns. Should be easy
   to port the code when proper embedding of the HOL datatypes is
   available.

*)

(*open List;;*)
(*open String;;*)

open Holparselib;;
open Parserlib;;
open Renderlib;;

(* general library stuff *)

let last xs = List.hd (List.rev xs);;

let butlast xs = List.rev (List.tl (List.rev xs));;

let less_than t1 t2 = Int64.compare t1 t2 = -1;;

(* [0;1...n-1] *)
let rec upto n = match n with 0 -> [] | _ -> (upto (n-1))@[n-1];;

(* auxiliaries to do with parsing and datatypes derived from parser.mly *)

(* get the contents of the file as a Holparselib list *)

(* contents are returned as a list, with the first parsed object at
   the end of the list, i.e. new items are cons'ed onto the front of the
   list *)
let trace_contents fname =
  let inch = open_in fname in
  let env = Threadparsing.create_parse_env () in
  let lexbuf = Lexing.from_channel inch in
  let result = ref [] in
  let rec loop () =
    let next = try Parser.main env Lexer.token lexbuf with
      | Threadparsing.Parse_error ->
	  let _ = print_endline ("Fatal: Parse error in file " ^ fname) in
	  let e = (match !result with
		     | [] -> "(Failed to parse header information block)"
		     | PARSE_RETURN(tco,_,_)::_ ->
			 ("Last label parsed had timecomment: " ^ timecomment_option_to_string tco)) in
	  let _ = print_endline e in
	    exit 1 in
    let _ = (result := next::(!result)) in
      loop () in
    try loop () with
      | Lexer.Eof ->
	  let _ = close_in inch in
	    !result;;

let timestamp_of_holtime (s, u) = Int64.add (Int64.mul s 1000000L) u;;

let holtime_of_timestamp t = (Int64.div t 1000000L, Int64.rem t 1000000L);;

let epsilon_of_label lbl = match lbl with
  | PARSE_RETURN(_,_,HOLEPSILON(DURATION(sec, usec))) -> timestamp_of_holtime (sec, usec)
  | _ -> 0L

let is_epsilon lbl = match lbl with
  | PARSE_RETURN(_,_,HOLEPSILON(_)) -> true
  | _ -> false

(* take a list of labels, and return a list of (time,lbl). *)
let time_lbls basetime lbls =
  let f = fun lbl (acc,t) ->
    let acc = (t,lbl)::acc in (* associate a time with a message *)
    let t = Int64.add t (epsilon_of_label lbl) in (* update the current time *)
      (acc,t) in
    fst (List.fold_right f lbls ([],basetime))

(* should only be called on a PARSE_RETURN(tc,cso,HOLABSTIME...) *)
let timestamp_of_holabstime pr = match pr with
  | PARSE_RETURN(tc,slo,HOLABSTIME(s, u)) -> timestamp_of_holtime (s, u)
  | _ -> failwith "conflate/timestamp_of_holabstime: not a HOLABSTIME" ;;

(* should only be called on a PARSE_RETURN(tc,cso,HOLABSTIME...) *)
let replace_basetime pr basetime = match pr with
  | PARSE_RETURN(tc,slo,HOLABSTIME(s, u)) ->
      let (s,u) = holtime_of_timestamp basetime in (* hate the way we can't have pair returns directly in place *)
	PARSE_RETURN(tc,slo,HOLABSTIME(s,u))
  | _ -> failwith "conflate/replace_basetime: not a HOLABSTIME";;

(* update initial_host -- parsed as comment! -- to net_initial_host *)
let initial_host_to_net_initial_host hostname =
  let initial_host_string = "initial_host" in
  let net_initial_host_string = "net_initial_host" in
  let f s =
    let (ns,ni) = (String.length s, String.length initial_host_string) in
      if ni <= ns && String.sub s 0 ni = initial_host_string
      then net_initial_host_string ^ " " ^ hostname ^ String.sub s ni (ns - ni)
      else s in
    List.map f;;

(* a label has a host identifier, a time and the parsed info *)

type hlbl = [ `Host of int * int64 * ns_parse_return ]
type nlbl = [ `Host of int * int64 * ns_parse_return | `Epsilon of ns_parse_return ]

(* augment a label by adding a comment *)
let add_comment =
  let add_comment cso c =
    let cs = match cso with None -> [] | Some xs -> xs in
      (* N.B. add comment on end, cos first comment is at end of list, see parser.mly *)
      Some (cs @ [c]) in
  let add_comment pr c = match pr with
    | PARSE_RETURN(tco,cso,pd) -> PARSE_RETURN(tco,add_comment cso c,pd) in
  let add_comment (nlbl:nlbl) c = match nlbl with
    | `Host (i,t,pr) -> `Host(i,t,add_comment pr c)
    | `Epsilon pr -> `Epsilon (add_comment pr c) in
    add_comment;;

let main =
  let map = List.map in

  let files =
    (* Horrible hack to weed out those files that don't have any
       labels. We expect (and parser.mly might imply) that a trace has at
       least an abstime label. If this is missing, we don't do anything
       with the trace. The alternative is to change the generation phase
       so that zero length traces are not produced (at least an abstime
       is present). N.B. this means that there may be some traces that
       don't have an equivalent .epsilon trace after running the
       conflator on them.*)
    let fs = List.tl (Array.to_list Sys.argv) in
      (* weed out those which don't have an abstime *)
      List.filter (fun f -> not (trace_contents f = [])) fs in

    (* identify each host by int *)
  let hosts = upto (List.length files) in
    (* and provide a way to get back to the names, which are the filenames with quotes *)
  let hostname n = "\"" ^ List.nth files n ^ "\"" in

  (* get timed labels from file *)
  let (lblss:ns_parse_return list list) = map trace_contents files in

  (* get basetimes separately and drop from labels we are interested in- we add it back in later *)
  let btimes = map last lblss in (* assumes last lbl is a basetime *)
  let basetimes = map timestamp_of_holabstime btimes in
  let mintime = match basetimes with (* deal with case no trace files supplied *)
    | [] -> 0L | _ -> List.hd (List.sort Int64.compare basetimes) in
  let lblss = map butlast lblss in

  (* add times to each label *)
  let (timed_lblss: (int64*ns_parse_return) list list) = List.map2 time_lbls basetimes lblss in

  (* want to remove epsilons prior to sort- we add back in different epsilons later *)
  let timed_lblss = map (List.filter (fun (_,x) -> not (is_epsilon x))) timed_lblss in

  let (nlblss:hlbl list list) =
    List.map2 (fun n -> map (fun (t,lbl) -> `Host(n,t,lbl))) hosts timed_lblss in

  (* combine lbls into one big list *)
  let (nlbls:hlbl list) = List.concat nlblss in

  (* sort the labels, remembering that we want the earliest at the end of the list *)
  let nlbls =
    let greater_than (`Host(_,t1,_)) (`Host(_,t2,_)) = Int64.compare t2 t1 in
      List.stable_sort greater_than nlbls in

  (* add epsilons back in *)
  let (nlbls:nlbl list) =
    let f = fun nlbl (acc,current) -> match nlbl with
      | `Host(_,t,_) ->
	  (* might want an epsilon transition *)
	  let epsilon = match less_than current t with
	    | true ->
		let delta = Int64.sub t current in
		let (sec,usec) = holtime_of_timestamp delta in
		  [`Epsilon  (PARSE_RETURN(None,None,HOLEPSILON(DURATION(sec, usec))))]
	    | false -> [] in
	  let current = t in
	    ([(nlbl:>nlbl)]@epsilon@acc,current) in (* FIXME why do we need explicit cast? *)

      fst (List.fold_right f nlbls ([],mintime)) in

  (* printing *)

  (* first number lbls- all conflate output has consistent numbering,
     i.e. a lbl in the conflated output has the same index as that in the
     .epsilon files *)

  (* reverse the labels first so that earliest is at front *)
  let nlbls = List.rev nlbls in

  (* add "Conflate Index" comments to each label *)
  let nlbls =
    let f = fun i nlbl ->
      let comment = "(* Conflate Index: " ^ (string_of_int i) ^ " *)" in
	add_comment nlbl comment in
      List.map2 f (upto (List.length nlbls)) nlbls in

  (* output nettrace to stdout *)
  let _ =
    (* convert to spec3_parse_returns *)
    let (nlbls: spec3_parse_return list) =
      let f nlbl = match nlbl with
	| `Host(i,_,PARSE_RETURN(tco,cso,pd)) -> SPEC3_PARSE_RETURN(tco,cso,HOLLN1_HOST(hostname i,pd))
	| `Epsilon (PARSE_RETURN(tco,cso,pd)) -> match pd with
	    | HOLEPSILON(dur) -> SPEC3_PARSE_RETURN(tco,cso,HOLLN1_EPSILON(dur))
		(* following never happens *)
	    | _ -> failwith "conflate: Epsilon did not contain a HOLEPSILON" in
	List.map f nlbls in

    (* add basetime label back in, which includes all comments from other basetimes *)
    let nlbls =
      let tco = None (* Some(TIMECOMMENT(mintime,"")) *) in
      let cs = List.fold_right2
		 (fun i (PARSE_RETURN(_,cso,_)) acc -> match cso with
		      (* take this opportunity to update the initial_host *)
		    | None -> acc | Some xs -> initial_host_to_net_initial_host (hostname i) xs @ acc)
		 hosts
		 btimes
		 [] in
      let (s,u) = holtime_of_timestamp mintime in
	(SPEC3_PARSE_RETURN(tco,Some cs,HOLLN1_ABSTIME(s,u)))::nlbls in

    let nlbl_to_string nlbl =
      spec3_parse_return_to_string nlbl
      ^ (match nlbl with | SPEC3_PARSE_RETURN(tco,cso,HOLLN1_ABSTIME _) -> "" | _ -> ";")
      ^ "\n\n" in
      (* print the labels *)
    let ss = List.map nlbl_to_string nlbls in
    let _ = List.iter print_string ss in
      () in

  (* now output original traces with extra epsilons *)
  let lbl_to_string lbl =
    ns_parse_return_to_string lbl
    ^ (match lbl with | PARSE_RETURN(tco,cso,HOLABSTIME _) -> "" | _ -> ";")
    ^ "\n\n" in

  let output_to_file f lbls =
    let ss = List.map lbl_to_string lbls in
    let _ = List.iter (output_string f) ss in
    let _ = flush f in
      () in

  let nlbl_to_ns_parse_return nlbl = match nlbl with
    | `Host(_,_,pr) -> pr
    | `Epsilon pr -> pr in

  (* output .epsilon *)
  let f i =
    let file = List.nth files i in
    let file_eps = open_out (file ^ ".epsilon") in

    let nlbls =
      let f nlbl = match nlbl with
	| `Host(j,_,_) -> i = j
	| `Epsilon _ -> true in
	List.filter f nlbls in
    let lbls = List.map nlbl_to_ns_parse_return nlbls in
      (* want to add modified basetime back in at front *)
    let lbls =
      let lbl = replace_basetime (List.nth btimes i) mintime in
	lbl :: lbls in
    let _ = output_to_file file_eps lbls in
      close_out file_eps in

  let _ = List.iter f hosts in
    ()
;;

