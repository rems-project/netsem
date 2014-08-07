(* A handy tool for drawing dependencies graphs of HOL theories *)

(* In HOL, type 'use "<file>";' where <file> is the path to this file.
   This exposes new functions graphviz_string and graphviz_write. Now
   do:

      graphviz_write "<theory>" "<output-file>"

   where <theory> is the name of any currently-loaded theory and
   <output-file> is the file to write output into.

  Then you probably want to run the output through dot, for which the
  graphviz bundle needs to be installed. Do this:

      dot <dot-file> -Tpng > <image-file>

*)

load "Splayset";

val empty_stringset = Splayset.empty String.compare;

fun dependency_graph s =
  let fun f []         oldtheories edgelist = (Splayset.listItems oldtheories, edgelist)
        | f (t::newtl) oldtheories edgelist =
            if Splayset.member (oldtheories, t) then f newtl oldtheories edgelist
            else let val plist = parents t in
              f (plist @ newtl) (Splayset.add (oldtheories, t)) ((List.map (fn x => (t,x)) plist) @ edgelist) end
  in f [s] empty_stringset [] end;

fun graphviz_string s =
  let val (nodes, edges) = dependency_graph s in
    ("digraph " ^ s ^ "_ancestors \n{\n")
    ^
    (List.foldl (fn (x,y) => y ^ " " ^ x ^ "\n") "" nodes)
    ^
    (List.foldl (fn ((p,q),r) => r ^ " " ^ p ^ " -> " ^ q ^ "\n") "" edges)
    ^
    "}\n"
  end;

fun graphviz_write s f =
  let
    val fp = TextIO.openOut f
  in
    TextIO.output (fp, graphviz_string s); TextIO.closeOut fp
  end;
