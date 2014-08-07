(* pipe this -*- sml -*- file into hol:
     hol < quant-check.ml

   .ml suffix ensures Holmake won't try to compile this file.

*)

quietdec := true;
set_trace "show_alias_printing_choices" 0;
Feedback.emit_WARNING := false;
print "Loading LTS theory ";
app (fn s => (print "."; load s)) ["bossLib", "realTheory",
                                   "TCP1_utilsTheory", "TCP1_hostTypesTheory",
                                   "TCP1_hostLTSTheory"];
print " done\n";

val th = TCP1_hostLTSTheory.host_redn0_rules

fun order_calc ty = let
  val {Thy,Tyop,Args} = dest_thy_type ty
in
  case (Thy,Tyop) of
    ("min", "fun") => Int.max(order_calc (hd Args) + 1,
                              order_calc (hd (tl Args)))
  | ("finite_map", "fmap") => Int.max(order_calc (hd Args) + 1,
                                      order_calc (hd (tl Args)))
  | ("TCP1_hostTypes", "host") => 0
  | _ => List.foldl (fn (ty, mx) => Int.max(mx, order_calc ty)) 0 Args
end handle HOL_ERR _ => 0;

fun is_binder t = is_forall t orelse is_exists t

fun update_maxbind (acc as (oldmax,oldvar)) t = let
  val (v,_) = dest_exists t handle HOL_ERR _ => dest_forall t
  val order = order_calc (#2 (dest_var v))
in
  if order > oldmax then (order,v)
  else acc
end


fun foldterm P f acc t = let
  val fold = foldterm P f
  val acc' = if P t then f acc t else acc
in
  case dest_term t of
    COMB(t1,t2) => fold (fold acc' t1) t2
  | LAMB(v,bod) => fold acc' bod
  | _ => acc'
end;

val rules = CONJUNCTS th

fun rule_name th =
    #1 (dest_const (find_term (fn t => type_of t = ``:rule_ids`` andalso
                                       is_const t) (concl th)))
    handle HOL_ERR _ => "(rule with no name??)"

fun foldthis (th, acc) = let
  val name = rule_name th
  val (ord,v) = foldterm is_binder update_maxbind (~1, T) (concl th)
in
  Binarymap.insert(acc, name, (ord,v))
end;

val basemap = Binarymap.mkDict String.compare;

print "Calculating quantifier information ... ";
val calcmap = List.foldl foldthis basemap rules;
print "done\n";

fun print_results (k,(m,v)) = let
  val (vname, ty) = dest_var v
in
  print (StringCvt.padRight #" " 25 k);
  print ": ";
  print (StringCvt.padRight #" " 6 vname);
  print (StringCvt.padRight #" " 40 (type_to_string ty));
  print (Int.toString m);
  print "\n"
end

val _ = Binarymap.app print_results calcmap;



