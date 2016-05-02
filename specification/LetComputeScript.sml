(* A HOL4 specification of TCP *)

(* This file is the theory of "computation" lets.  CLET is a HOL
   constant with exactly the same semantics as the normal built-in
   LET, but treated differently here (via rewrite theorems and code in
   LetComputeLib) to allow our own special brand of lazy evaluation. *)

(*[ RCSID "$Id: LetComputeScript.sml,v 1.9 2005/02/02 04:59:44 mn200 Exp $" ]*)

open HolKernel Parse boolLib

open simpLib boolSimps BasicProvers

val _ = new_theory "LetCompute"

local
  open sumTheory pairTheory listTheory optionTheory realTheory integerTheory
       finite_mapTheory
in
end


(* CLET stands for "computing let" *)
val CLET_THM = new_definition ("CLET_THM", ``CLET f x = f x``);

(* the value constant is a tag used to indicate that the simplifier has seen
   (and worked over) a term. *)
val value_def = new_definition("value_def", ``value x = x``);

(* the pending constant is another tag, used to indicate that a hypothesis
   is an equality that shouldn't be eliminated just yet.  *)
val pending_def = new_definition("pending_def", ``pending (x:bool) = x``);

val LET_CLET = store_thm (
  "LET_CLET",
  ``LET f x = CLET f x``,
  REWRITE_TAC [CLET_THM, LET_THM]);

val tac =   SIMP_TAC bool_ss [CLET_THM, value_def, pending_def]
fun value_thm(s,t) = boolLib.store_thm(s,t,tac) before export_rewrites [s]

(* CLET congruence *)
val CLET_congruence = store_thm(
  "CLET_congruence",
  ``(v = v') ==> (f = f') ==> (CLET f v = CLET f' (LetCompute$value v'))``,
  tac);

val CLET_CLET_AND_ELIM = store_thm(
  "CLET_CLET_AND_ELIM",
  ``CLET (CLET f v1) v2 = CLET (\z. CLET (f z) v2) v1``,
  REWRITE_TAC [CLET_THM] THEN BETA_TAC THEN REWRITE_TAC []);


(* theorems for moving CLETs around terms *)
val LEFT_CLET_AND_THM = store_thm(
  "LEFT_CLET_AND_THM",
  ``(CLET (\v. f v) e /\ P) = CLET (\v. f v /\ P) e``,
  tac);
val RIGHT_CLET_AND_THM = store_thm(
  "RIGHT_CLET_AND_THM",
  ``(P /\ CLET (\v. f v) e) = CLET (\v. P /\ f v) e``,
  tac);
val EXISTS_CLET_THM = store_thm(
  "EXISTS_CLET_THM",
  ``(?x. CLET (\v. f x v) e) = CLET (\v. ?x. f x v) e``,
  tac);

(* don't want this one as a value_thm because it would loop as a rewrite *)
val CLET_CLET_TRANSPOSE = store_thm(
  "CLET_CLET_TRANSPOSE",
  ``CLET (\u. CLET (\v. f u v) e1) e2 = CLET (\v. CLET (\u. f u v) e2) e1``,
  tac);

val CLET_CLET_ARG = value_thm(
  "CLET_CLET_ARG",
  ``CLET f (CLET g v) = CLET (\u. CLET f (g u)) v``
);

val CLET_value = value_thm(
  "CLET_value",
  ``CLET g (value (CLET f v)) = CLET g (CLET (\u. value (f u)) v)``
);

val CLET_SIMP = value_thm(
  "CLET_SIMP",
  ``CLET (\v. M) e = M``
);

val CLET_RATOR = store_thm(
  "CLET_RATOR",
  ``CLET f e x = CLET (combin$C f x) e``,
  SRW_TAC [][CLET_THM]
);
val _ = export_rewrites ["CLET_RATOR"]

val CLET_UNCURRY = store_thm(
  "CLET_UNCURRY",
  ``CLET (UNCURRY f) v =
    CLET (\p. CLET (\v1. CLET (f v1) (SND p)) (FST p)) v``,
  SIMP_TAC bool_ss [CLET_THM, pairTheory.UNCURRY_VAR]);
val _ = export_rewrites ["CLET_UNCURRY"]




(* turning a CLET into a pending *)

val CLET_pending = store_thm(
  "CLET_pending",
  ``(CLET f (value e) ==> P) = !v. pending (v = e) ==> f v ==> P``,
  tac);



(* theorems that allow the transfer of values into the bodies of
   let abstractions, or which move lets and pending tags around *)

val pending_AND = value_thm(
  "pending_AND",
  ``pending (p /\ q) = (pending p /\ pending q)``
);


val CLET_EQ = value_thm(
  "CLET_EQ",
  ``(v = CLET f e) = CLET (\u. v = f u) e``
);

val CLET_ABS = value_thm(
  "CLET_ABS",
  ``CLET f (\x. g x) = f (\x. g x)``
);

val pending_ABS = value_thm(
  "pending_ABS",
  ``pending (f = (\x. g x)) = (f = (\x. g x))``
);

val CLET_BOOL = value_thm(
  "CLET_BOOL",
  ``(CLET f T = f T) /\ (CLET f F = f F)``
);

val pending_BOOL = value_thm(
  "pending_BOOL",
  ``(pending (v = T) = (v = T)) /\ (pending (v = F) = (v = F)) /\
    (pending T = T) /\ (pending F = F)``
);

val CLET_OPTION = value_thm(
  "CLET_OPTION",
  ``(CLET f (value NONE) = f NONE) /\
    (CLET f (value (SOME x)) = CLET (\v. f (SOME v)) (value x))``
);

val pending_OPTION = value_thm(
  "pending_OPTION",
  ``(pending (v = NONE) = (v = NONE)) /\
    (pending (v = SOME e) = ?w. pending (w = e) /\ (v = SOME w))``
);

val CLET_NUM = value_thm(
  "CLET_NUM",
  ``(CLET f (value (NUMERAL x)) = f (NUMERAL x)) /\
    (CLET f (value 0) = f 0)``
);

val pending_NUM = value_thm(
  "pending_NUM",
  ``(pending (v = 0) = (v = 0)) /\
    (pending (v = NUMERAL e) = (v = NUMERAL e))``
);

val CLET_PROD = value_thm(
  "CLET_PROD",
  ``CLET f (value (x,y)) = CLET (\v1. CLET (\v2. f (v1, v2)) (value y)) (value x)``
);

val pending_PROD = value_thm(
  "pending_PROD",
  ``(pending (v = (e1, e2)) = ?w1 w2. (v = (w1, w2)) /\ pending (w1 = e1) /\
                                      pending (w2 = e2))``
);

val CLET_INT = value_thm(
  "CLET_INT",
  ``(CLET f (value 0) = f 0) /\
    (CLET f (value (int_of_num(NUMERAL x) : int)) = f (int_of_num(NUMERAL x))) /\
    (CLET f (value (~int_of_num(NUMERAL x))) = f (~int_of_num(NUMERAL x)))``
);

val pending_INT = value_thm(
  "pending_INT",
  ``(pending (v = 0) = (v = 0)) /\
    (pending (v = int_of_num(NUMERAL x): int) = (v = int_of_num(NUMERAL x))) /\
    (pending (v = ~int_of_num(NUMERAL x)) = (v = ~int_of_num(NUMERAL x)))``
);

val CLET_REAL = value_thm(
  "CLET_REAL",
  ``(CLET f (value 0) = f 0) /\
    (CLET f (value (real_of_num(NUMERAL x) : real)) = f (real_of_num(NUMERAL x))) /\
    (CLET f (value (~real_of_num(NUMERAL x))) = f (~real_of_num(NUMERAL x))) /\
    (CLET f (value (real_of_num(NUMERAL x) / real_of_num(NUMERAL y))) =
        f (real_of_num(NUMERAL x) / real_of_num(NUMERAL y))) /\
    (CLET f (value (~real_of_num(NUMERAL x) / real_of_num(NUMERAL y))) =
        f (~real_of_num(NUMERAL x)/ real_of_num(NUMERAL y)))``
);

val pending_REAL = value_thm(
  "pending_REAL",
  ``(pending (v = 0) = (v = 0)) /\
    (pending (v = real_of_num(NUMERAL x)) = (v = real_of_num (NUMERAL x))) /\
    (pending (v = ~real_of_num(NUMERAL x)) = (v = ~real_of_num(NUMERAL x))) /\
    (pending (v = real_of_num(NUMERAL x) / real_of_num(NUMERAL y)) =
             (v = real_of_num(NUMERAL x) / real_of_num(NUMERAL y))) /\
    (pending (v = ~real_of_num(NUMERAL x) / real_of_num(NUMERAL y)) =
             (v = ~real_of_num(NUMERAL x) / real_of_num(NUMERAL y)))``
);


val pending_FMAP = value_thm(
  "pending_FMAP",
  ``(pending (fm = FEMPTY) = (fm = FEMPTY)) /\
    (pending (fm = (f |+ (k,v))) = (fm = (f |+ (k,v))))``
);


(* the basic terms *)
val value_t = mk_thy_const {Name = "value", Thy = "LetCompute",
                            Ty = alpha --> alpha}
val pending_t = ``LetCompute$pending``
val CLET_t = mk_thy_const {Name = "CLET", Thy = "LetCompute",
                           Ty = ``:('a -> 'b) -> ('a -> 'b)``}

val _ = export_theory();
