(* magic code to make SIGINT appear as an Interrupt exception *)
(*
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;
*)

val _ = Version.register "$RCSfile: CheckTraces.sml,v $" "$Revision: 1.53 $" "$Date: 2006/06/23 06:20:28 $";

val args = CommandLine.arguments()

val odir = ref "."        (* the directory to which output files are written *)

(* whether or not to save the trace theorems to a theory file *)
val save_tracethms = ref false


open testEval

fun fromSOME s (SOME x) = x
| fromSOME s NONE = raise (Fail s)

(* given a substring ss, searches for the next occurrence of a
   variable (\$[0-9] or \$[A-Za-z_][A-Za-z_0-9]* or \${[^}]*}).
   Returns SOME(ss0,v,ss1) where v is the variable name (without the
   dollar sign or braces), ss0 is the substring before the occurrence
   and ss1 is the substring after; or NONE if no variable occurrence
   exists. *)
fun varocc ss =
    let val (ss0,ss1) = Substring.position "$" ss
    in
    if Substring.size ss1 < 2 then
        NONE
    else
        let val (_,ss2) = fromSOME "varocc:1" (Substring.getc ss1)
        in
            let val (c,ss3) = fromSOME "varocc:2" (Substring.getc ss2)
            in
                if Char.isDigit c then
                    SOME (ss0, Substring.slice (ss2,0,SOME 1), ss3)
                else if c = #"{" then
                    let val (v,ss4) = Substring.splitl (fn c => c <> #"}") ss3
                    in
                        if Substring.isEmpty ss4 then
                            raise (Fail "Unterminated ${ variable reference")
                        else
                            let val (_,ss5) = fromSOME "varocc:3" (Substring.getc ss4)
                            in
                                SOME (ss0, v, ss5)
                            end
                    end
                else if Char.isAlpha c orelse c = #"_" then
                    let val (v,ss4) = Substring.splitl (fn c => Char.isAlphaNum c orelse c = #"_") ss2
                    in
                        SOME (ss0, v, ss4)
                    end
                else
                    NONE
            end
        end
    end

fun resolvevar f s =
    let fun go sss ss =
            case varocc ss of
                NONE => Substring.concat (List.rev (ss :: sss))
              | SOME(ss0,v,ss1) => go ([Substring.full (f v), ss0] @ sss) ss1
    in
        go [] (Substring.full s)
    end

fun lookup kvs k =
  case kvs of
    (k',v)::kvs' => if k' = k then v else lookup kvs' k
  | []           => raise (Fail ("variable not found: `"^k^"'"))

(* Dump a file, replacing all occurrences of ${VAR_NAME} with the
   value of that variable, as specified in an associative list passed
   as argument. *)
fun dump_string_template vs hnd s = let
  val s' = resolvevar (fn v => lookup vs (Substring.string v)) s
in
  TextIO.output(hnd,s')
end

fun fileHead n f = let
  val istr = TextIO.openIn f
  val s = case (TextIO.inputLine istr, TextIO.inputLine istr) of
          (SOME t, SOME t') => t ^ t'
          | (SOME t, NONE) => t
          | (NONE, SOME t) => t
          | (NONE, NONE) => ""
  val _ = TextIO.closeIn istr
in
  s
end

fun copy n x =
    if n <= 0 then [] else x :: copy (n-1) x

fun concatWith s sss =
    case sss of
        [] => ""
      | [ss] => Substring.string ss
      | (ss::sss) => Substring.string ss ^ s ^ concatWith s sss

fun relpath here there = let
in
    if not (String.sub (here,0) = #"/" andalso String.sub (there,0) = #"/") then
        "/BOGUSPATH/"^there
    else
        let fun loop hcs tcs =
                case (hcs,tcs) of
                    ((hc::hcs'),(tc::tcs')) => if Substring.string hc = Substring.string tc then loop hcs' tcs' else (hcs,tcs)
                  | _ => (hcs,tcs)
        in let val (hcs,tcs) = loop (Substring.tokens (fn c => c = #"/") (Substring.full here))
                                    (Substring.tokens (fn c => c = #"/") (Substring.full there))
           in
               (*Substring.*)concatWith "/" (copy (List.length hcs - 1) (Substring.full "..") @ tcs)
           end
        end
end

local
  fun roman_helper (one,five,ten) n =
      case n of
        1 => one
      | 2 => one^one
      | 3 => one^one^one
      | 4 => one^five
      | 5 => five
      | 6 => five ^ one
      | 7 => five ^ one ^ one
      | 8 => five ^ one ^ one ^ one
      | 9 => one ^ ten
      | _ => ""
  val roman_unit = roman_helper ("I", "V", "X")
  val roman_ten = roman_helper ("X", "L", "C")
  val roman_hundred = roman_helper ("C", "D", "M")
in

fun to_roman n =
    if n >= 1000 then raise Overflow
    else if n < 0 then raise Overflow
    else if n = 0 then "Z"
    else let
        val ones = roman_unit (n mod 10)
        val n = n div 10
        val tens = roman_ten (n mod 10)
        val n = n div 10
        val hundreds = roman_hundred (n mod 10)
      in
        hundreds ^ tens ^ ones
      end

end;

fun strip_fupd t = let
  fun recurse acc t = let
    val (fm, kvpair) = finite_mapSyntax.dest_fupdate t
  in
    recurse (pairSyntax.dest_pair kvpair::acc) fm
  end handle HOL_ERR _ => (t, acc)
in
  recurse [] t
end

(* get before and after information on socket states in a transition theorem *)
val socks_fldsel_t = ``TCP1_hostTypes$host_socks : host -> (sid |-> socket)``
fun get_sock_data th = let
  val (_, args) = strip_comb (concl th)
  fun get_socks_fmap t =
      rhs (concl (simpLib.SIMP_CONV testEval.phase1_ss []
                                    (mk_comb(socks_fldsel_t, t))))
  val hosts = filter (fn t => type_of t = ``:host``) args
  val sock_maps = map get_socks_fmap hosts
  fun get_sock_state t = let
    val base =
        rhs (concl (simpLib.SIMP_CONV
                      testEval.phase1_ss []
                      (mk_comb(``\s. (tcp_sock_of s).st``, t))))
  in
    SOME (#1 (dest_const base)) handle HOL_ERR _ => NONE
  end
  fun sockstate_map ((k,v),db) = Binarymap.insert(db,k,get_sock_state v)
  fun build_db sockmap = let
    val (_, args) = strip_fupd sockmap
  in
    List.foldl sockstate_map (Binarymap.mkDict Term.compare) args
  end
  val dbs = map build_db sock_maps
  val init_db = Binarymap.transform (fn s => (SOME s, NONE)) (hd dbs)
  fun update_with_laters (k,v,db) =
      case Binarymap.peek (db, k) of
        SOME (preval, _) => Binarymap.insert(db, k, (preval, SOME v))
      | NONE => Binarymap.insert(db, k, (NONE, SOME v))
in
  Binarymap.foldl update_with_laters init_db (hd (tl dbs))
end

fun label_string th = let
  (* return the name of the head constructor of a transition theorem's
     label *)
  val lab = valOf (List.find (fn t => type_of t = ``:Lhost0``)
                             (#2 (strip_comb (concl th))))
in
  #1 (dest_const (#1 (strip_comb lab)))
end

(* generate latex trace labels *)
fun print_transition_labels hnd thmlist = let
  fun appix f x list = let
    fun recurse n x list =
        case list of
          [] => x
        | h::t => (let val x' = f (n,x,h) in recurse (n + 1) x' t end)
  in
    recurse 0 x list
  end
  fun printinv (lbls,tistep) =
      if tistep >= 0 then
          output (hnd,
                  "\\newcommand{\\labelstep"^to_roman tistep^
                  "b}{"^lbls^"} % b LATEXTRANS\n")
      else if lbls = "" then
          ()
      else
          output (hnd,
                  "SOMETHING WRONG - invisible labels precede visible ones, ouch \\wibble\n")
  fun printi (i, (lbls,tistep), (thm,tstep,_,_)) = let
      val sockdata = get_sock_data thm
        (* sockdata is a Binarymap, keyed on terms (sids), with a range type
           of (string option option * string option option).  This type is
           a pair because it gives before and after information.  The outer
           option level indicates whether or not the socket was even in the
           map.  The inner option level indicates whether or not a meaningful
           state was deducible.  Partiality here might be caused by the
           socket being a UDP socket, or if the trace was for some reason
           unsure itself, resulting in an expression dependent on the context,
           for example *)
      fun print_sock_state soptopt =
          case soptopt of
            NONE => "_"
          | SOME NONE => "???"
          | SOME (SOME s) => s
      val label_name = label_string thm
      val rule_name = testEval.rule_name thm
      fun print_sockdata (k, (state0, state)) =
          output(hnd, "TRANSITION" ^  (* grep(1) key (at leftmost column) *)
                      " " ^ Int.toString i ^  (* check step number *)
                      " " ^ Int.toString tstep ^  (* merge index *)
                      " " ^ label_name ^  (* outermost label constructor *)
                      " " ^ term_to_string k ^  (* sid *)
                      ": " ^ print_sock_state state0 ^  (* left socket state st *)
                      " --> " ^ print_sock_state state ^  (* right socket state st' *)
                      " " ^ rule_name ^  (* rule name *)
                      "\n")
      val lbl = "[[" ^ testEval.rule_name thm ^ "]]"
  in
    Binarymap.app print_sockdata sockdata;
    if List.exists (fn x => label_name = x) ["Lh_epsilon", "Lh_tau", "Lh_trace"] then
        (* "invisible" label *)
        if lbls = "" then
            (lbl, tistep)
        else
            (lbls ^ "; " ^ lbl, tistep)
    else
        (* "visible" label *)
        (printinv (lbls,tistep);
         output (hnd,
                 "\\newcommand{\\labelstep"^to_roman tstep^"}{[[" ^
                 rule_name ^ "]]} % a LATEXTRANS\n");
         ("",tstep))
  end
in
  htmlOutput hnd ("<div class=\"translabels\">\n");
  output (hnd,"==Transition labels:\n");
  let val x = appix printi ("",~1) thmlist in
      printinv x
  end;
  htmlOutput hnd ("\n</div>\n")
end

(* Utilities end; here's where the real work happens *)

fun do_one_file_body hnd fname = let
  val _ = htmlOutput hnd "<div id=\"thelist\">\n"
in
  try_finally (fn () => let
    val (host0, labels) = simp_hostlabels_from_file hnd fname
    val s = do_timed_trace hnd (host0, labels)
    val a_valid_trace = SOME (seq.hd s) handle Fail _ => NONE
  in
    a_valid_trace
  end
  ) (fn () => htmlOutput hnd "</div>\n"
  )
end

fun is_localconstant_spec t = let
  val (v, bod) = dest_exists t
  val (l,r) = dest_eq bod
in
  Term.compare(v,l) = EQUAL andalso not (free_in l r)
end handle HOL_ERR _ => false

fun output_theory thyname thmlist = let
  fun namethm ((th, _, _, _), (i, acc)) = let
    val name = "trace_step" ^ StringCvt.padLeft #"0" 4 (Int.toString i)
  in
    (i + 1, (name, th) :: acc)
  end
  val (_, named_thms) = List.foldl namethm (0, []) thmlist
  val outputfile = !odir ^ "/" ^ thyname ^ ".thydata"
in
  DiskThms.write_file outputfile (List.rev named_thms)
end


fun do_one_file h = let
    val _ = print ("Processing " ^ h ^ "\n")
    val basename = Path.file h
    val outfile = Path.concat (!odir,basename ^ ".out.html")
    val hnd = if !toStdOut then TextIO.stdOut else openOut outfile
    val datestr = Date.fmt "%Y-%m-%d T %H:%M:%S Z (%a)" (Date.fromTimeUniv (Time.now ()))
in
    (if !outputtingHtml then dump_string_template [("HEADING","HOL Trace: "^basename)] hnd strings.html_header else ());
    htmlOutput hnd "<div class=\"tracehead\">\n";
    altOutput hnd ("==Working on trace file <a href=\"" ^ relpath outfile h ^ ".html\">" ^ h ^ "</a> [<a href=\"" ^ relpath outfile h ^ "\">plain</a>] [<a href=\"" ^ relpath outfile h ^ ".ps.gz\">ps</a>]\n")
                  ("==Working on trace file " ^ h ^ "\n");
    htmlOutput hnd "<br>";
    output (hnd,("==Date: " ^ datestr ^ "\n"));
    htmlOutput hnd "<pre>\n";
    output (hnd,(fileHead 2 h handle _ => ""));
    htmlOutput hnd "</pre>\n";
    altOutput hnd ("<div class=\"verhead\" id=\"thever\">==Version numbers:\n<div class=\"vertab\">" ^ Version.getTable ()) ("==Versions:\n" ^ Version.getString ());
    htmlOutput hnd "</div></div></div>\n";
    TextIO.flushOut hnd;
    (case try_finally (fn () => do_one_file_body hnd h)
                      (fn () => htmlOutput hnd "<div class=\"tracetail\">\n") of
       NONE => output_and_print (hnd,"==Trace " ^ basename ^ " FAILED\n")
     | SOME ((_, host, ctxt), thmlist) =>
       (output_and_print (hnd,"==Trace " ^ basename ^ " SUCCEEDED\n");
        htmlOutput hnd "<pre>\n";
        output (hnd, "==Final host:\n");
        output (hnd, Parse.term_to_string host);
        output (hnd, "\n==Final context:\n");
        appi (fn n => fn t => (output(hnd, Int.toString (n + 1)^". ");
                               output(hnd, Parse.term_to_string t);
                               output(hnd, "\n")))
             (List.filter (not o is_localconstant_spec) ctxt);
        print_transition_labels hnd thmlist;
        if !save_tracethms then output_theory basename thmlist else ();
        htmlOutput hnd "</pre>\n"))

      handle Interrupt => output_and_print (hnd,"==Trace " ^ basename ^ " INTERRUPTED\n")
           | CtxtTooComplicated csts =>
             (output_and_print (hnd,"==Trace " ^ basename ^ " TOO_COMPLICATED:\n");
              htmlOutput hnd "<pre>\n";
              appi (fn n => fn t => (output (hnd,(Int.toString (n + 1) ^ ". "));
                                     output (hnd,Parse.term_to_string t);
                                     output (hnd,"\n"))) csts;
              htmlOutput hnd "</pre>\n";
              output (hnd,"==Complicated constraint list ends\n"))
           | ExcessiveBackTracking =>
             output_and_print (hnd, "==Trace " ^basename ^
                                    " EXCESSIVE_BACKTRACKING\n")
           | SendDatagramMismatch =>
             output_and_print(hnd, "==Trace " ^basename ^
                                   " SEND_DATAGRAM_MISMATCH\n")
           | OutputQueueTooLong =>
             output_and_print(hnd, "==Trace "^basename ^
                                   " OUTPUT_QUEUE_TOO_LONG\n")
           | HOL_ERR err =>
             (output_and_print (hnd,"==Trace " ^ basename ^ " INTERNAL_ERROR:\n");
              htmlOutput hnd "<pre>\n";
              output (hnd,Feedback.exn_to_string (HOL_ERR err));
              htmlOutput hnd "</pre>\n");
    htmlOutput hnd "</div>\n";
    (if !outputtingHtml then dump_string_template [] hnd strings.html_trailer else ());
    TextIO.flushOut hnd;
    (if !toStdOut then () else closeOut hnd)
end

fun do_many_files filenamelist =
    case filenamelist of
      [] => Process.exit Process.success
    | h :: t => (do_one_file h; do_many_files t)

(* accept files to process from stdin, terminated by EOF *)
(* a simple acknowledgement protocol is used *)
fun do_accept_files () =
    (output (stdOut, "\nReady.\n"); flushOut stdOut;
     let fun loop () =
         case inputLine stdIn of
         NONE => () | SOME "quit\n" => () (* EOF or quit means quit *)
         | SOME filename0 =>
           let val filename = String.substring (filename0, 0, String.size filename0 - 1) in
             output (stdOut, "Processing "^filename^"\n"); flushOut stdOut;
             do_one_file filename;
             output (stdOut, "\nReady.\n"); flushOut stdOut;
             loop ()
           end
     in
         loop ()
     end;
     output (stdOut, "\nBye.\n"); flushOut stdOut)


fun the_or exn x = case x of
                     NONE => raise exn
                   | SOME x => x

fun die s = (TextIO.output(TextIO.stdErr, s^"\n");
             Process.exit Process.failure)
(* arguments:
   -s         output to stdout rather than to appropriately-named output files.
   -t         output in plain text (rather than HTML)
   -d dir     output files go to directory dir
   -a         accept trace files to process from stdin
              (using a simple protocol) rather than from the command line
   -bt directive
              control bracktracking with directives of form
                 <n>%   allow n% more steps than there are steps in the trace
                 <n>    allow n more steps
                 none   no limit on backtracking
   file1 ...  trace files to process
*)
fun parse_btdirective s =
    case s of
      "none" => testEval.btrack_control := NONE
    | _ => if String.sub(s, size s - 1) = #"%" then
             case Int.fromString (String.substring(s, 0, size s - 1)) of
               SOME i => testEval.btrack_control := SOME (PercentExtra i)
             | NONE => die "Mal-formed percentage for backtrack control"
           else
             case Int.fromString s of
               SOME i => testEval.btrack_control := SOME (AbsExtra i)
             | NONE => die "Mal-formed number for backtrack control"

fun do_args args =
    (print ("do_args with "^(Int.toString (List.length args))^" args\n") ;
    case args of
      "-s" :: args => (toStdOut := true; do_args args)
    | "-t" :: args => (outputtingHtml := false; do_args args)
    | "-d" :: dir :: args => (odir := dir; do_args args)
    | "-a" :: args => if null args then do_accept_files ()
                      else die "-a must be final argument"
    | ["-bt"] => die "-bt must be followed by back track control argument"
    | "-bt" :: dir :: args => (parse_btdirective dir; do_args args)
    | "--nosdm" :: args => (testEval.sdm_check_enabled := false; do_args args)
    | "--sdmbt" :: args => (testEval.sdm_fail_exception := false; do_args args)
    | "--saveths" :: args => (save_tracethms := true; do_args args)
    | "--timing" :: args => (outputtingTiming := true; do_args args)
    | _            => do_many_files args)

val _ = (print "Initialisation complete.\n"; do_args args)

