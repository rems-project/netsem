(* A HOL98 specification of TCP *)

(* Various utility definitions *)

(*[ RCSID "$Id: TCP1_utilsScript.sml,v 1.69 2005/02/07 15:12:27 kw217 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse

open bossLib

open HolDoc

local open arithmeticTheory stringTheory pred_setTheory integerTheory
           finite_mapTheory realTheory wordsTheory
           containerTheory in end;

val _ = new_theory "TCP1_utils";

val _ = BasicProvers.augment_srw_ss [rewrites [LET_THM]]

(*: @chapter [[TCP1_utils]] Utility functions

This file contains various utility functions and definitions, for functions, lists, and numeric types, that are
used throughout the specification.

:*)

(* -------------------------------------------------- *)
(*                   STUFF                            *)
(* -------------------------------------------------- *)

(*: @section [[util_stuff]] GEN Basic utilities

Basic utilities for functions, numbers, maps, and records.

:*)

(* equal and not-equal with same precedence as comparison operators, tighter than /\ *)
val _ = ParseExtras.tight_equality()

val notinlist_def = Define`notinlist x l = ~MEM x l` (*: @norender :*);
val _ = BasicProvers.export_rewrites ["notinlist_def"]
val _ = overload_on("NOTIN", ``notinlist``)

(* dont put this into any phase of the
   rewriting; it's handled specially elsewhere *)

val funupd_def = Define`
(*: update one point of a function:*)
  funupd f x y = \x'. if x'=x then y else f x'
` (*: @mergewithnext :*);

val funupd_list_def = Phase.phase 1 Define`
(*: update multiple points of a function:*)
  funupd_list f xys = FOLDL (\f (x,y). funupd f x y) f xys
`  (*: @mergewithnext :*) ;

val clip_int_to_num_def = Phase.phase 1 Define`
(*: clip [[int]] to [[num]] :*)
  clip_int_to_num (i:int) = if i < 0 then 0 else Num i
`  (*: @mergewithnext :*);

(* shifts on naturals (only defined on words so far) *)
val left_shift_num_def = Phase.phase 1 Define`
  (*: left shift, written [[<<]] :*)
  left_shift_num (n:num) (i:num) = n * 2 EXP i
`  (*: @mergewithnext :*);
val right_shift_num_def = Phase.phase 1 Define`
  (*: right shift, written [[>>]] :*)
  right_shift_num (n:num) (i:num) = n DIV 2 EXP i
`  (*: @mergewithnext :*);
val _ = overload_on("<<", ``left_shift_num``);
val _ = overload_on(">>", ``right_shift_num``);

(* Don't Phase: handled by testEval *)
val rounddown_def = Define`
(*: round [[v]] down to multiple of [[bs]], unless [[v < bs]] already :*)
  rounddown bs v = if v < bs then v else (v DIV bs) * bs
`
(*: @mergewithnext :*)
;

(* Don't Phase: handled by testEval *)
val roundup_def = Define`
  (*: round [[v]] up to next multiple of [[bs]]; if [[v = k*bs]] then no change :*)
  roundup   bs v = ((v + (bs - 1)) DIV bs) * bs
`(*: @mergewithnext :*) ;



(* -------------------------------------------------- *)
(*                   WORD32                           *)
(* -------------------------------------------------- *)

(* COMPATIBILITY *)
(* CVS change wordFunctorLib.sml,1.1,1.2 annoyingly renamed this value; rename it back *)
val _ = overload_on("w_0", ``word_0:word16``);
val _ = overload_on("w_0", ``word_0:word32``);

val _ = add_bare_numeral_form (#"w", SOME "n2w")


(* -------------------------------------------------- *)
(*                   REAL                             *)
(* -------------------------------------------------- *)

val _ = overload_on("MIN", ``real$min``);
val _ = overload_on("MAX", ``real$max``);

(* this definition really should be built in... *)
(* ... doesn't need phasing; handled specially in testEval *)
val real_of_int_def = Define`
(*: inject [[int]] into [[real]] :*)
  real_of_int (i:int) = if i < 0 then ~(real_of_num (Num ~i))
                                 else real_of_num (Num i)
`(*: @mergewithnext :*);

val num_floor_def = Define`
(*: [[num]] floor of [[real]] :*)
  num_floor (x:real) = LEAST (n:num). real_of_num (n+1) > x
`(*: @mergewithnext :*); (* better version proved in TCP1_timerProps, though could/should be here
      really *)

val num_floor_and_frac_def = Define`
(*: [[num]] floor and fractional part of [[real]] :*)
  num_floor_and_frac (x:real)
    = let n = LEAST (n:num). real_of_num (n+1) > x
      in
      (n,x - real_of_num n)
`(*: @mergewithnext :*);



(* ----------------------------------------------------------------------
    FINITE MAPS
   ---------------------------------------------------------------------- *)

val fm_exists_def = Define`
  (*: finite map exists, written [[?(k,v) :: fm . P (k,v)]] :*)
  fm_exists fm P = ?k. k IN FDOM fm /\ P (k, fm ' k)
`  (*: @mergewithnext :*);

(* enable syntax like
     ?(k,v) :: fm \\ k0. k = v
   which should be read as
     there exists a (k,v) pair in the finite map fm \\ k0, such that
     k = v
*)
val _ = overload_on ("RES_EXISTS", ``fm_exists``)



(* -------------------------------------------------- *)
(*             RECORDS                                *)
(* -------------------------------------------------- *)

(* allows you to say  cb with <| field updated_by value onlywhen condition |>
   instead of cb with <| field := if condition then value else cb.field |> *)

val _ = add_infix ("onlywhen", 461, NONASSOC);  (* slightly tighter than updated_by (=450) *)

val onlywhen_def = Phase.phase_x 1 xDefine "onlywhen" `
  (*: used for conditional record updates :*)
  (x onlywhen b) = if b then K x else I
`
(*: @description
    TODO3
    @internal
    [[rounddown]] and [[roundup]] are part of |tcp_mss()|: calculate buffer sizes based on MSS etc.
:*)
;(* onlywhen xDefine only because of HOLDoc limitations *)



(* -------------------------------------------------- *)
(*             NONDETERMINISTIC CHOICE                *)
(* -------------------------------------------------- *)

(* choose a value nondetermistically from A, and pass it
   to f:
      choose x :: {1;2;3}. y = x + x
   is true if y IN {2;4;6} and false otherwise.
   Note, this is angelic nondeterminism (I think).  Beware.
*)

val _ = set_fixity "choose" Binder;
val _ = associate_restriction("choose", "choose_from_set");
val _ = overload_on("choose_from_set", ``bool$RES_EXISTS``);


val _ = overload_on("choose", ``$?``);
val _ = overload_on("?", ``$?``);

(* by repeating that there is a link from constant ? to "?", the system
   knows that we prefer to see "?" rather than "choose" when it prints
   things out, but the parser will accept "choose" *)



(* would like to write:

     choose x from A in e

   to mean

     ?x. x IN A /\ e

   in other words "choose x from A in" should be a prefix operator
   which also binds x.

   Can write

      choose x :: A . e

   for the moment.

   Can also write

      choose x. e

   which is equivalent to

     choose x :: UNIV. e
*)


(* -------------------------------------------------- *)
(*                   LISTS                            *)
(* -------------------------------------------------- *)

(*: @section [[util_lists]] GEN List utilities
This section contains a number of basic functions for manipulating lists.
:*)

val SPLIT_REV_0_def = Define`
(*: split worker function:*)
  (SPLIT_REV_0      0  ls     rs  = (ls,rs)) /\
  (SPLIT_REV_0 (SUC n) ls (r::rs) = SPLIT_REV_0 n (r::ls) rs) /\
  (SPLIT_REV_0 (SUC n) ls     []  = (ls,[]))
`(*: @mergewithnext :*);

val SPLIT_REV_def = Define`
(*: split a list after [[n]] elements, returning the reversed prefix
and the remainder:*)
  SPLIT_REV n rs = SPLIT_REV_0 n [] rs
`(*: @mergewithnext :*);

val SPLIT_def = Define`
(*: split a list after [[n]] elements, returning the prefix and the remainder:*)
  SPLIT n rs = let (ls,rs) = SPLIT_REV n rs in (REVERSE ls,rs)
`(*: @mergewithnext :*);

val TAKE_def = Define`
(*: take the first [[n]] elements of a list:*)
  TAKE n rs = let (ls,rs) = SPLIT_REV n rs in REVERSE ls
`(*: @mergewithnext :*);

val DROP_def = Define`
(*: drop the first [[n]] elements of a list:*)
  DROP n rs = let (ls,rs) = SPLIT_REV n rs in rs
`(*: @mergewithnext :*);

val TAKEWHILE_REV_def = Phase.phase 1 Define`
(*: split a list at first element not satisfying [[p]], returning reversed prefix and remainder:*)
  TAKEWHILE_REV p ls (r::rs) = TAKEWHILE_REV p (if p r then (r::ls) else ls) rs /\
  TAKEWHILE_REV p ls     []  = ls
`(*: @mergewithnext :*);

val TAKEWHILE_def = Phase.phase 1 Define`
(*: split a list at first element not satisfying [[p]], returning prefix and remainder:*)
  TAKEWHILE p rs = REVERSE (TAKEWHILE_REV p [] rs)
`(*: @mergewithnext :*);

val REPLICATE_def = Phase.phase 1 Define`
(*: make a list of [[n]] copies of [[x]]:*)
  (REPLICATE      0  x = []) /\
  (REPLICATE (SUC n) x = x :: REPLICATE n x)
`(*: @mergewithnext :*);

val decr_list_def = Phase.phase 1 Define`
(*: decrement a list of nums by a num, dropping any that count below zero:*)
  ((decr_list : num -> num list -> num list)
             d [] = []) /\
  (decr_list d (n::ns) = (if n < d then I else CONS (n-d)) (decr_list d ns))
`(*: @mergewithnext :*);

(* member and not-member for lists *)
val _ = add_infix ("IN'"   , 450, NONASSOC);
val _ = overload_on ("IN'", ``MEM``);

val _ = add_infix ("NOTIN'", 450, NONASSOC);
val NOTIN'_def = xDefine "NOTIN'" `
(*: not in :*)
(x NOTIN' y) = ~(MEM x y)` (*: @mergewithnext:*);  (* xDefine only because of HOLDoc limitations *)

val MAP_OPTIONAL_def = Phase.phase 1 Define`
(*: map with optional result:*)
  MAP_OPTIONAL f (x::xs) = APPEND (case f x of
                                     NONE => []
                                   | SOME y => [y])
                                  (MAP_OPTIONAL f xs) /\
  MAP_OPTIONAL f []      = []
`
(*: @mergewithnext :*);

val CONCAT_OPTIONAL_def = Phase.phase 1 Define`
(*: concatentation of option list that drops all [[NONE]]s:*)
  CONCAT_OPTIONAL xs = MAP_OPTIONAL I xs
`
(*: @mergewithnext :*);

val ORDERINGS_def = Phase.phase 1 Define`
(*: the set of all orderings of a set :*)
  ORDERINGS s l = (LIST_TO_SET l = s /\
                   LENGTH l      = CARD s)
`(*: @mergewithnext :*);


val INSERT_ORDERED_def = Phase.phase 1 Define`
(*: insert ordered:*)
  INSERT_ORDERED new old bad =
     FILTER (\fd. fd IN' new \/ fd IN' bad) old
`;



(* -------------------------------------------------- *)
(*                   ASSERTIONS                       *)
(* -------------------------------------------------- *)

(*: @section [[util_assertions]] GEN Assertions
This definition is an alias for false, which induces the checker to
emit a special message indicating an assertion failure.
:*)

val ASSERTION_FAILURE_def = Define`
(*: assertion failure (causes checker to halt) :*)
  ASSERTION_FAILURE (s:string) = F
`;


(* -------------------------------------------------- *)

val _ = adjoin_to_theory
        { sig_ps = NONE,
          struct_ps =
          SOME (fn pps =>
                   (PP.add_string pps "val _ = Datatype.big_record_size := 8;";
                    PP.add_newline pps))}

val _ = export_theory();
