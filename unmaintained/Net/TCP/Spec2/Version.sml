(* A HOL98 specification of TCP *)

(* Version tracking *)

structure Version :> Version =
struct

val versions = ref []

fun dercs s0 =
    let val s = Substring.all s0
    in let val s' = if Substring.size s = 0 orelse Substring.sub (s,0) <> #"$"
                    then s
                    else Substring.triml 1 (Substring.dropl (not o Char.isSpace) s)
       in let val s'' = if Substring.size s' < 2 orelse Substring.sub (s',Substring.size s' - 1) <> #"$" orelse Substring.sub (s',Substring.size s' - 2) <> #" "
                        then s'
                        else Substring.trimr 2 s'
          in Substring.string s''
          end
       end
    end

fun register file ver date =
    versions := (!versions @ [(dercs file,dercs ver,dercs date)])

fun adjoin_to_theory s =
    HolKernel.adjoin_to_theory
        { sig_ps = NONE,
          struct_ps =
          SOME (fn pps =>
                   (PP.add_string pps s;
                    PP.add_newline pps))}

(* add code to theory to do registration then *)
fun registerTheory file ver date =
    adjoin_to_theory ("val _ = Version.register \"" ^ String.toString file
                      ^ "\" \"" ^ String.toString ver
                      ^ "\" \"" ^ String.toString date ^ "\";")

fun get () =
    let fun vercompare ((f1,_,_),(f2,_,_)) = String.compare (f1,f2)
    in Listsort.sort vercompare (!versions)
    end

fun getString () =
    List.foldr (fn ((file,ver,date),s) => file ^ ": " ^ ver ^ " " ^ date ^ "\n" ^ s) "" (get ())

fun getTable () =
    "<table>" ^
    List.foldr (fn ((file,ver,date),s) => "<tr><td>" ^ file ^ "</td><td>" ^ ver ^ "</td><td>" ^ date ^ "</td></tr>\n" ^ s) "</table>" (get ())

val _ = register "$RCSfile: Version.sml,v $" "$Revision: 1.1 $" "$Date: 2005/07/12 15:42:25 $";

end (* struct *)
