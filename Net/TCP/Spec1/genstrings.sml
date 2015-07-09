(* Render files as a MoSML string constants, in a module *)

open TextIO

fun renderfile f = let
  val n = OS.Path.file f
  val istr = TextIO.openIn f
  val _ = print ("val " ^ n ^ " = \"\\\n")
  val _ =
    while not (endOfStream istr) do let
      val line = valOf (inputLine istr)
      val line' = String.toString (String.extract(line,0,SOME (size line - 1)))
    in
      print ("\\" ^ line' ^ "\\n\\\n")
    end
  val _ = print "\\\"\n\n"
  val _ = TextIO.closeIn istr
in
  ()
end

fun main() = let
in
  print "(* generated code; do not edit! *)\n";
  print "structure strings = struct\n";
  List.app renderfile (CommandLine.arguments ());
  print "end (* struct *)\n";
  print "(* eof *)\n"
end
