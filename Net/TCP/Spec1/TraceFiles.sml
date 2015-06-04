(* A HOL98 specification of TCP *)
structure TraceFiles :> TraceFiles =
struct
(* Parser for trace files *)

open HolKernel Parse boolLib

local open TCP1_hostLTSTheory TCP1_evalSupportTheory in end;


val _ = Version.register "$RCSfile: TraceFiles.sml,v $" "$Revision: 1.5 $" "$Date: 2004/03/22 11:40:01 $";

(* initial host, expanded, and the list of labels in the trace *)
fun host_and_labels_from_file filename =
  let open TextIO Substring
      val istr = openIn filename
      val contents = full (inputAll istr)
      val _ = closeIn istr

      val (pre,post) = ("\n(* HOST *)\n","\n(* TSOH *)\n")
      val (_,co1) = position pre contents
      val co1' = triml (String.size pre) co1
      val (hoststr,co2) = position post co1'
      val co2' = triml (String.size post) co2

      val (pre,post) = ("\n(* BASETIME *)\n","\n(* EMITESAB *)\n")
      val (_,co1) = position pre co2'
      val co1' = triml (String.size pre) co1
      val (basetimestr,co2) = position post co1'
      val co2' = triml (String.size post) co2

      val labsstr = trimr 1 (dropr (fn c => c <> #";") co2')

      val host0 = Parse.Term [QUOTE (string hoststr)]
      val basetime0 = Parse.Term [QUOTE (string basetimestr)]
      val labels = #1 (listSyntax.dest_list
                         (Parse.Term [QUOTE ("[ "^string labsstr^" ]")]))
  in
  (host0,labels)
  end
end