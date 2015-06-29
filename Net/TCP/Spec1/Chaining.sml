(* given an unordered list of pairs (x_i, x_{i + 1}) find their correct order
   in the "chain" which looks like [(x_0, x_1), (x_1, x_2), (x_2, x_3) ...]
   etc.

   The difficulty is that we have no way of telling what ordering
   pertains between x_0 and x_2 (say) simply by inspecting them.  This
   problem is exercise 5.24 in Knuth, "Sorting and searching" 2nd
   edition.  The good solution (O(n(log n)^2)) on page 590 is rather
   complicated, so I've put it into its own file here.  The algorithm
   is apparently due to Norman Hardy (circa 1967).

   The various x_i's need to have a sorting relation on them (this will be
   independent of the chain order).  This function is the first parameter.
*)
structure Chaining :> Chaining =
struct
open Lib

val _ = Version.register "$RCSfile: Chaining.sml,v $" "$Revision: 1.2 $" "$Date: 2004/03/22 11:40:00 $";

fun norman_hardy sort list = let
  val sort_fst = Listsort.sort (sort o (fst ## fst))
  fun sort_snd l = Listsort.sort (sort o (snd ## snd)) l
  val N = length list
  fun liftsort (x, y) = case (x,y) of
                       (NONE, NONE) => EQUAL
                     | (NONE, SOME _) => GREATER
                     | (SOME _, NONE) => LESS
                     | (SOME x0, SOME y0) => sort (x0, y0)
  fun listhd [] = (NONE, NONE)
    | listhd ((x,y)::_) = (SOME x, SOME y)
  fun advance [] = [] | advance (_ :: t) = t
  val eof = null
  fun core t (F, G, H, F', G') = let
    val (x,x') = listhd F
    val (y,y') = listhd G
    val (z,z') = listhd H
  in
    if eof F then (F', G')
    else if liftsort(x',z) = EQUAL then
      core t (advance F, G, advance H, (valOf x, valOf z')::F', G')
    else case liftsort(x',y') of
           EQUAL => core t (advance F, advance G, H, F',
                            (valOf y - t, valOf x)::G')
         | GREATER => core t (F, advance G, H, F', G')
         | _ => if liftsort(x',z) = GREATER then
                  core t (F, G, advance H, F', G')
                else raise Fail "Knuth is an idiot"
  end
  fun first_pass (F, H) (twos, lastpair) = let
    val (x,x') = listhd F
    val (z,z') = listhd H
  in
    if eof F then (twos, lastpair)
    else case liftsort (x',z) of
           EQUAL => first_pass (advance F, advance H)
                               ((valOf x, valOf z')::twos, lastpair)
         | LESS => first_pass (advance F, H)
                              (twos, (N - 1, valOf x) ::
                                     (N, valOf x') :: lastpair)
         | _ => first_pass (F, advance H) (twos, lastpair)
  end
  val (twos, lastpair) = first_pass (sort_snd list, sort_fst list) ([], [])
  fun rev_append [] list = list
    | rev_append (h::t) list = rev_append t (h::list)
  fun merge sort acc (l1, l2) =
      case (l1, l2) of
        ([], _) => rev_append acc l2
      | (_, []) => rev_append acc l1
      | (h1::t1, h2::t2) => let
        in
          case sort(h1, h2) of
            LESS => merge sort (h1::acc) (t1, l2)
          | GREATER => merge sort (h2::acc) (l1, t2)
          | EQUAL => raise Fail "Knuth is an idiot"
        end
  fun mainloop n (F, G) =
      if n > N then
        map snd (Listsort.sort (Int.compare o (fst ## fst)) G)
      else let
          val H = sort_fst F
          val F = sort_snd F
          val G = sort_snd G
          val (F', G') = core n (F, G, H, [], [])
        in
          mainloop (n * 2) (F',
                            merge (sort o (snd ## snd)) [] (G, sort_snd G'))
        end
in
  mainloop 2 (twos, lastpair)
end

(* find a test for the above given some string of letters; generates a chain
   by chaining together letters in the order they appear in the input
   string (dropping duplicate letters).  Returns this list of pairs sorted on
   its first component.   *)
fun gentest s = let
  open Substring
  val ss = full s
  fun recurse seen c0 acc ss =
      case getc ss of
        NONE => acc
      | SOME (c, ss') => if Binaryset.member(seen, c) then
                           recurse seen c0 acc ss'
                         else recurse (Binaryset.add(seen, c)) c
                                      ((str c0, str c)::acc)
                                      ss'
  val result0 =
      case getc ss of
        NONE => []
      | SOME (c,ss') => recurse (Binaryset.singleton Char.compare c) c
                                [] ss'
in
  Listsort.sort (String.compare o (fst ## fst)) result0
end

(* try, for example,
    norman_hardy String.compare (gentest "");
    norman_hardy String.compare (gentest "a"); (* gives [], correctly *)
    norman_hardy String.compare (gentest "ba");
    norman_hardy String.compare (gentest "zyxwvutsrqponm");
    norman_hardy String.compare (gentest "abcdefghijklm");
    norman_hardy String.compare
                 (gentest "the quick brown fox jumps over the lazy dog");

*)

end; (* struct *)
