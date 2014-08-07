(* lts_to_latex.ml -- turn LTS (in HOL) into LaTeX code *)
(* Keith Wansbrough 2001-2004 *)

open Holdoc_init
open Holparse
open Holparsesupp
open Holparsetools
open Holdocmodel
open Simpledump
open Mngdump


(* see Net/TCP/Spec1/tags.txt for format and tag descriptions *)

(* -------------------------------------------------------------------- *)
(*  Diagnostics                                                         *)
(* -------------------------------------------------------------------- *)

exception Unimplemented of string


(* -------------------------------------------------------------------- *)
(*  Configuration options                                               *)
(* -------------------------------------------------------------------- *)

let opt_fatal         = ref false  (* should parsesemifatal warnings be fatal? *)
let opt_internal      = ref false  (* should @internal comments be visible? *)
let opt_inlinetext    = ref false  (* should inline text comments be visible in rules? *)
let opt_inlinetextdef = ref true   (* should inline text comments be visible in definitions? *)
let opt_cmds          = ref true   (* should each item become a command which is later used?
                                      (vs just emitting TeX in place) *)
let opt_verb          = ref true   (* should |text| denote verbatim in TeX? *)
let opt_merge         = ref true   (* should @mergewithnext be enabled? *)

let opts = [
  "-fatal"       , Arg.Set opt_fatal       , "warnings are fatal";
  "-nofatal"     , Arg.Clear opt_fatal     , "warnings are not fatal";
  "-internal"    , Arg.Set opt_internal    , "@internal comments are visible";
  "-nointernal"  , Arg.Clear opt_internal  , "@internal comments are hidden";
  "-inlinetext"  , Arg.Set opt_inlinetext  , "inline (* comments *) are visible in rules";
  "-noinlinetext", Arg.Clear opt_inlinetext, "inline (* comments *) are hidden in rules";
  "-inlinetextdef"  , Arg.Set opt_inlinetextdef  , "inline (* comments *) are visible in definitions";
  "-noinlinetextdef", Arg.Clear opt_inlinetextdef, "inline (* comments *) are hidden in definitions";
  "-cmds"        , Arg.Set opt_cmds        , "items become TeX commands";
  "-nocmds"      , Arg.Clear opt_cmds      , "items are emitted in place";
  "-verb"        , Arg.Set opt_verb        , "|text| is verbatim in TeX";
  "-noverb"      , Arg.Clear opt_verb      , "|text| is not special in TeX";
  "-merge"       , Arg.Set opt_merge       , "mergewithnext enabled";
  "-nomerge"     , Arg.Clear opt_merge     , "mergewithnext disabled";
]

(* -------------------------------------------------------------------- *)
(*  Utilities                                                           *)
(* -------------------------------------------------------------------- *)

let isIdent : hol_content -> bool
    = function
        (HolIdent _,_) -> true
      | _ -> false

let isIndent : hol_content -> bool
    = function
        (HolIndent _,_) -> true
      | _ -> false

let optionCat : 'a option list -> 'a list
    = fun xs ->
      let rec go xs ys =
        match xs with
          [] -> List.rev ys
        | (Some x::xs) -> go xs (x::ys)
        | (None  ::xs) -> go xs ys
      in
      go xs []

let option : 'b -> ('a -> 'b) -> 'a option -> 'b
    = fun none some -> function
        None   -> none
      | Some x -> some x

let optionMap : ('a -> 'b) -> 'a option -> 'b option
    = fun f ->
      option None (fun x -> Some (f x))

let optionId : 'a -> 'a option -> 'a
    = fun dflt ->
      option dflt (fun x -> x)

let isNone : 'a option -> bool
    = function
        None -> true
      | Some _ -> false

let isSome : 'a option -> bool
    = function
        None -> false
      | Some _ -> true

let null : 'a list -> bool
    = function
        [] -> true
      | _  -> false

let ($) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c
    = fun f g x ->
      f (g x)

(* turn Not_found into None *)
let maybe : ('a -> 'b) -> 'a -> 'b option
  = fun f x
 -> try Some(f x) with Not_found -> None

let the : string -> 'a option -> 'a
    = fun s -> function
        Some x -> x
      | None -> raise (Failure ("the: "^s))

let headopt : 'a list -> 'a option
    = function
      | (x::_) -> Some x
      | []     -> None

type ('a, 'b) sum = Inl of 'a | Inr of 'b

let ifknown : string option -> string
    = function
      | None   -> "<unknown>"
      | Some s -> s

(* find the longest prefix satisfying the predicate, and the remainder *)
let span : ('a -> bool) -> 'a list -> ('a list * 'a list)
    = fun p xs ->
      let rec go xs ys =
        match xs with
        | (x::xs) when p x -> go xs (x::ys)
        | _                -> (List.rev ys, xs)
      in
      go xs []

(* flatten xss, interspersing ss between elements of xss *)
let concat_sep : 'a list -> 'a list list -> 'a list
    = fun ss xss ->
      let rec go ys xss =
        match xss with
        | []        -> ys
        | [xs]      -> xs @ ys
        | (xs::xss) -> go (ss @ xs @ ys) xss
      in
      go [] (List.rev xss)


(* find first pair with key less than or equal to search key *)
let rec gassoc i = function
  | [] -> None
  | ((n,x)::nxs) ->
      if i >= n then
        Some (n,x)
      else
        gassoc i nxs

let rec roman_pos uc i =
  let letters =
    if uc then
      [(1000,"M"); (900,"CM"); (500,"D"); (400,"CD");
       (100,"C"); (90,"XC"); (50,"L"); (40,"XL");
       (10,"X"); (9,"IX"); (5,"V"); (4,"IV"); (1,"I")]
    else
      [(1000,"m"); (900,"cm"); (500,"d"); (400,"cd");
       (100,"c"); (90,"xc"); (50,"l"); (40,"xl");
       (10,"x"); (9,"ix"); (5,"v"); (4,"iv"); (1,"i")]
  in
  match gassoc i letters with
  | Some (n,s) ->
      s ^ roman_pos uc (i-n)
  | None ->
      if i = 0 then
        ""
      else
        raise (Failure ("roman: "^string_of_int i))

let roman uc i =
  if i < 0 then
    (if uc then "N" else "n")^roman_pos uc (-i)
  else if i > 0 then
    roman_pos uc i
  else
    (if uc then "Z" else "z")

let texify_command s =
  let f s = roman true (int_of_string (Str.matched_string s))
  in
   Str.global_replace    (Str.regexp "[^A-Za-z0-9]") "T"
  (Str.global_substitute (Str.regexp "[0-9]+"      )  f
                         s)

let gensym =
  let r = ref 0 in
  fun () ->
    r := !r + 1;
    string_of_int !r

(* move left edge given distance *)
let move_left : int -> Lexing.position * Lexing.position -> Lexing.position * Lexing.position
    = fun n (l0,l1) ->
      ({l0 with Lexing.pos_cnum = l0.Lexing.pos_cnum + n}, l1)

(* set right edge to given distance past left edge *)
let set_right : int -> Lexing.position * Lexing.position -> Lexing.position * Lexing.position
    = fun n (l0,l1) ->
      (l0,{l0 with Lexing.pos_cnum = l0.Lexing.pos_cnum + n})


(* -------------------------------------------------------------------- *)
(*  Parser types and helpers                                            *)
(* -------------------------------------------------------------------- *)

let my_loc_len = String.length "TCP1_hostLTSScript.sml" + 5*2 + 3*2 + 6
let my_format_location l =
  let f = format_location l in
  f ^ String.make (my_loc_len - String.length f) ' '

exception ParseFail of string located

let parsefail : string -> string -> hol_content list -> 'a
    = fun expected at -> function
        ((_,l) as d::_) -> raise (ParseFail ("Expected "^expected^" but found "^dumphol_content d^" "^at,l))
      | []     -> raise (ParseFail ("Expected "^expected^" but found end of input "^at,zero_loc))

let parsesemifatal : string located -> unit
    = fun (s,l) ->
      if !opt_fatal then
        raise (ParseFail (s,l))
      else
        (let w = my_format_location l ^ "WARNING: "^s in
        print_string ("% "^w^"\n");
        prerr_string (w^"\n"))

let white_re = Str.regexp "^[ \t\n]+"
let nonwhite_re = Str.regexp "^[^ \t\n]+"

let tidy : string -> string
    = fun s ->
      if Str.string_match white_re s 0 then
        Str.string_after s (Str.match_end ())
      else
        s

let unexpected_arg : string -> string -> texdoc -> unit
    = fun tag expected ts ->
      match ts with
        ((_,l) as t::_) ->
          parsesemifatal ("LDoc tag @"^tag^": expected "^expected^", found "^dumptexdoc_content t,l)
      | [] ->
          parsesemifatal ("LDoc tag @"^tag^": expected "^expected^", found end of input",zero_loc)


let rec assertempty : string -> texdoc -> unit
    = fun tag ds0 ->
      match ds0 with
      | [] -> ()
      | ((d,_) :: ds) ->
          match d with
          | TexContent s when tidy s = ""
            -> assertempty tag ds
          | TexContent _
          | TexHol _
          | TexDir _
            -> unexpected_arg tag "nothing" ds0

type ('a, 'b) prser = 'b list -> ('a * 'b list)
type 'b prser_ = 'b list -> 'b list

type 'a holparser = ('a, hol_content) prser
type holparser_ = hol_content prser_

type 'a mosmlparser = ('a, mosml_content) prser
type mosmlparser_ = mosml_content prser_


(* -------------------------------------------------------------------- *)
(*  LTS documentation mid-level model                                   *)
(* -------------------------------------------------------------------- *)

type ldoctag =
    (* cluster comment tags *)
    LdocPreamble
  | LdocChapter of string * texdoc           (* name, title *)
  | LdocSection of string * string * texdoc  (* name, category, title *)
  | LdocErrors
  | LdocError of holdoc * texdoc  (* texdoc is stuff after the @error, but on the same line *)
  | LdocErrorinclude of string * holdoc
  | LdocCommoncases
  | LdocApi
  | LdocModeldetails
    (* rule comment tags *)
  | LdocDescription
(*| LdocModeldetails - as above *)
  | LdocVariation of string
  | LdocInternal
  | LdocNorender
  | LdocToafter of string
  | LdocToappendix
  | LdocMergewithnext
    (* No-op tag; has no effect *)
  | LdocNop


(* list of tag, body pairs *)
type ldoc_mid = (ldoctag located * texdoc) list


(* -------------------------------------------------------------------- *)
(*  texdoc preprocessing for LTS documentation - mid-level              *)
(* -------------------------------------------------------------------- *)

(* handles inline tags by transformation; luckily, the only inline tag
   can easily be processed this way. *)

let inline_re = Str.regexp "{@\\([A-Za-z0-9_]*\\)"
let end_inline_re = Str.regexp "^[ \t\n]*}"

let expand_tag : string located -> holdoc -> texdoc
    = fun (tag,l) ts ->
      if tag = "link" then
        match ts with
        | [(HolIdent(_,s),l)] ->
            [(TexContent "\\ltslink{",l);
             (TexContent (texify_command s),l);
             (TexContent "}{",l);
             (TexHol((TexHolLR,TexHolLR),ts),l);
             (TexContent "}",l)
           ]
        | _ ->
            parsesemifatal ("{@link} tag expected a single HOL identifier as argument",l);
            []
      else
        (parsesemifatal ("unrecognised inline LDoc tag {@"^tag^"}",l);
         [])

let string_match_somewhere re s =
  try
    let (_:int) = Str.search_forward re s 0 in
    true
  with
    Not_found -> false

let rec expand_inline_tags0 : texdoc -> texdoc -> texdoc
    = fun seen ds ->
      match ds with
      | [] -> seen
      | ((TexContent s,l) as d :: ds) when string_match_somewhere inline_re s ->
          let (b,e) = (Str.match_beginning (), Str.match_end ()) in
          let s0 = Str.string_before s b in
          let tag = Str.matched_group 1 s in
          let s1 = Str.string_after s e in
          expand_inline_tags1 tag
            ((TexContent s0, set_right b l) :: seen)
            ((TexContent s1, move_left e l) :: ds)
      | (d :: ds) ->
          expand_inline_tags0 (d::seen) ds

and expand_inline_tags1 : string -> texdoc -> texdoc -> texdoc
    = fun tag seen ds ->
      match ds with
      | ((TexContent s,_) :: ds) when tidy s = "" ->
          expand_inline_tags1 tag seen ds
      | ((TexHol(_,ts),_) :: ds) ->
          expand_inline_tags2 tag ts seen ds
      | _ ->
          unexpected_arg (tag^" (inline)") "HOL arg" ds;
          expand_inline_tags0 seen ((TexContent "{",zero_loc)::ds)  (* to balance the closing curly we'll probably soon see *)

and expand_inline_tags2 : string -> holdoc -> texdoc -> texdoc -> texdoc
    = fun tag ts seen ds ->
      match ds with
      | ((TexContent s,_) :: ds) when tidy s = "" ->
          expand_inline_tags2 tag ts seen ds
      | ((TexContent s,l) :: ds) when string_match_somewhere end_inline_re s ->
          let e = Str.match_end () in
          let s1 = Str.string_after s e in
          let ds' = expand_tag (tag,set_right e l) ts in
          expand_inline_tags0 (List.rev_append ds' seen)
            ((TexContent s1, move_left e l) :: ds)
      | _ ->
          unexpected_arg (tag^" (inline)") "}" ds;
          expand_inline_tags0 seen ((TexContent "{",zero_loc)::ds)  (* to balance the closing curly we'll probably soon see *)

let expand_inline_tags : texdoc -> texdoc
    = fun ds ->
      List.rev (expand_inline_tags0 [] ds)


let rec expand_verb0 : texdoc -> texdoc -> texdoc
    = fun seen ds ->
      match ds with
      | ((TexContent s,l) as d :: ds) ->
          (match maybe (String.index s) '|' with
          | None ->
              expand_verb0 (d::seen) ds
          | Some i ->
              expand_verb1
                ((TexContent (String.sub s 0 i),set_right i l)::seen)
                ("",set_right 0 (move_left (i+1) l))
                ((TexContent (String.sub s (i+1) (String.length s - (i+1))),move_left (i+1) l)::ds))
      | (d :: ds) ->
          expand_verb0 (d::seen) ds
      | [] ->
          List.rev seen

and expand_verb1 : texdoc -> string located -> texdoc -> texdoc
    = fun seen (verb,vl) ds ->
      match ds with
      | ((TexContent s,l) as d :: ds) ->
          (match maybe (String.index s) '|' with
          | None ->
              expand_verb1 seen (verb ^ s, (fst vl,snd l)) ds
          | Some i ->
              let verb = verb ^ String.sub s 0 i in
              let verb' = "\\wasverb{" ^ texify_text verb ^ "}" in
              expand_verb0
                ((TexContent verb',(fst vl,snd (set_right i l)))::seen)
                ((TexContent (String.sub s (i+1) (String.length s - (i+1))),move_left (i+1) l)::ds))
      | ((t,l)::_) ->
          parsesemifatal ("Unterminated verbatim form |...: expected |, found "^dumptexdoc_content (t,l),l);
          List.rev_append seen ds
      | [] ->
          parsesemifatal ("Unterminated verbatim form |...: expected |, found end of input",zero_loc);
          List.rev seen


let preprocess_texdoc : texdoc -> texdoc
    = fun ds ->
      let ds = expand_inline_tags ds in
      let ds = if !opt_verb then expand_verb0 [] ds else ds in
      ds


(* -------------------------------------------------------------------- *)
(*  Parse LTS documentation - mid-level                                 *)
(* -------------------------------------------------------------------- *)

let dir_re = Str.regexp "^@\\([A-Za-z0-9_]*\\)"

let rec parse_line0_rev : texdoc -> texdoc -> texdoc * texdoc
    = fun seen ds ->
      match ds with
        []                         -> (seen,[])
      | (((TexHol _    ),_) as d :: ds)
      | (((TexDir _    ),_) as d :: ds) -> parse_line0_rev (d::seen) ds
      | (((TexContent s),l) as d :: ds) ->
          match maybe (String.index s) '\n' with
            None                    -> parse_line0_rev (d::seen) ds
          | Some i ->
              ((TexContent (String.sub s 0 i), set_right i l) :: seen,
               (TexContent (String.sub s (i+1) (String.length s - (i+1))), move_left (i+1) l) :: ds)

(* returns the REVERSED parsed line and the remainder *)
let parse_line_rev : texdoc -> texdoc * texdoc
    = fun ds ->
      parse_line0_rev [] ds


(* push the substring after the match back onto the input list *)
let push_rest : string located -> texdoc -> texdoc
    = fun (s,l) ds ->
      let i = Str.match_end () in
      let s' = Str.string_after s i in
      if s' = "" then
        ds
      else
        (TexContent s',move_left i l) :: ds

let rec collect_string_arg : string -> string option -> texdoc -> (string * texdoc)
    = fun tag so ds ->
      match (so,ds) with
        (_, (TexContent "",_) :: ds) ->
          collect_string_arg tag so ds
      | (None, ((TexContent s,l) :: ds)) ->
          if Str.string_match white_re s 0 then
            collect_string_arg tag None (push_rest (s,l) ds)
          else if Str.string_match nonwhite_re s 0 then
            let s' = Str.matched_string s in
            collect_string_arg tag (Some s') (push_rest (s,l) ds)
          else
            raise (NeverHappen "collect_string_arg")
      | (Some s0, ((TexContent s,l) :: ds)) ->
          if Str.string_match white_re s 0 then
            (s0, push_rest (s,l) ds)
          else if Str.string_match nonwhite_re s 0 then
            let s' = Str.matched_string s in
            collect_string_arg tag (Some (s0 ^ s')) (push_rest (s,l) ds)
          else
            raise (NeverHappen "collect_string_arg")
      | (Some s0, []) ->
          (s0,[])
      | _ ->
          unexpected_arg tag "string arg" ds;
          ("",ds)

let rec collect_holdoc_arg : string -> texdoc -> (holdoc * texdoc)
    = fun tag ds ->
      match ds with
        ((TexContent s,_) :: ds) when tidy s = "" ->
          collect_holdoc_arg tag ds
      | ((TexHol(_,ts),_) :: ds) ->
          (ts, ds)
      | _ ->
          unexpected_arg tag "HOL arg" ds;
          ([], ds)

let extract_single_ident : string located -> holdoc -> string
    = fun (tag,l) ds ->
      match ds with
      | [(HolIdent(_,s),_)] -> s
      | _ -> parsesemifatal ("Tag @"^tag^" expected a single HOL identifier as argument",l);
          (gensym ())

let rec hasTag1 : string located -> texdoc -> ldoctag located
    = fun (tag,l) ds ->
      ((match tag with
      | "chapter"      ->
          let (n,ds) = collect_holdoc_arg tag ds in
          LdocChapter (extract_single_ident (tag,l) n, preprocess_texdoc ds)
      | "section"      ->
          let (n,ds) = collect_holdoc_arg tag ds in
          let (s,ds) = collect_string_arg tag None ds in
          LdocSection (extract_single_ident (tag,l) n, s, preprocess_texdoc ds)
      | "errors"       -> assertempty tag ds; LdocErrors
      | "error"        ->
          let (t,ds) = collect_holdoc_arg tag ds in
          LdocError (t, preprocess_texdoc ds)
      | "commoncases"  -> assertempty tag ds; LdocCommoncases
      | "api"          -> assertempty tag ds; LdocApi
      | "modeldetails" -> assertempty tag ds; LdocModeldetails
      | "description"  -> assertempty tag ds; LdocDescription
      | "variation"    ->
          let (s,ds) = collect_string_arg tag None ds in
          assertempty tag ds;
          LdocVariation s
      | "norender"     -> assertempty tag ds; LdocNorender
      | "internal"     -> assertempty tag ds; LdocInternal
      | "toafter"      ->
          let (t,ds) = collect_holdoc_arg tag ds in
          assertempty tag ds;
          LdocToafter (extract_single_ident (tag,l) t)
      | "toappendix"   -> assertempty tag ds; LdocToappendix
      | "mergewithnext"-> assertempty tag ds; LdocMergewithnext
      | "errorinclude" ->
          let (s0,ds) = collect_holdoc_arg tag ds in
          let (t,ds) = collect_holdoc_arg tag ds in
          assertempty tag ds;
          LdocErrorinclude (extract_single_ident (tag,l) s0, t)
      | _ -> (parsesemifatal ("unrecognised LDoc tag @"^tag,l);
              assertempty tag ds;
              LdocNop)
       ),
       l)


(* assumes directive won't be broken across TexContent items *)
let rec hasTag : texdoc -> ldoctag located option
    = fun ds ->
      match ds with
        [] -> None
      | ((TexHol _    ,_) :: ds)
      | ((TexDir _    ,_) :: ds) -> None
      | ((TexContent s,l) :: ds) ->
          if Str.string_match white_re s 0 then
            hasTag (push_rest (s,l) ds)
          else if Str.string_match dir_re s 0 then
            let s' = Str.matched_group 1 s in
            Some (hasTag1 (s',l) (push_rest (s,l) ds))
          else
            None


let rec ltsdoc_mid0 : ldoctag located -> texdoc -> texdoc -> ldoc_mid -> ldoc_mid
    = fun tag seen ds ls ->
      match ds with
        [] -> List.rev ((tag,preprocess_texdoc (List.rev seen))::ls)
      | _  ->
          let (line_rev,ds) = parse_line_rev ds in
          match hasTag (List.rev line_rev) with
            None      -> ltsdoc_mid0 tag ((TexContent "\n",zero_loc) :: line_rev @ seen) ds ls
          | Some tag' -> ltsdoc_mid0 tag' [] ds ((tag,preprocess_texdoc (List.rev seen))::ls)

let ltsdoc_mid : texdoc located -> ldoc_mid
    = fun (ds,l) ->
      ltsdoc_mid0 (LdocPreamble, l) [] ds []

(* also, use expand_inline in TeX comments embedded in HOL: *)
let _ =
  let old_render_HolTex_hook = !render_HolTex_hook in
  render_HolTex_hook := begin
    fun pvs d ->
      old_render_HolTex_hook pvs (preprocess_texdoc d)
  end


(* -------------------------------------------------------------------- *)
(*  LTS documentation high-level model                                  *)
(* -------------------------------------------------------------------- *)

(* NB: many of these things are compulsory, but the high-level parser
   is easier to write this way - sorry! *)

type ldoc_chapter =
    { ldh_name : string option;
      ldh_chaptertitle : texdoc option;
      ldh_amble : texdoc option;
      ldh_norender : bool;
      ldh_toafter : string option;
      ldh_toappendix : bool;
    }

type ldoc_cluster =
    { ldc_name : string option;
      ldc_sectiontitle : texdoc option;
      ldc_sectioncategory : string option;
      ldc_preamble : texdoc option;
      ldc_errors_preamble : texdoc option;
      ldc_errors : (holdoc * texdoc) list;
      ldc_errorincludes : (string * holdoc) list;
      ldc_commoncases : texdoc option;
      ldc_api : texdoc option;
      ldc_modeldetails : texdoc option;
      ldc_norender : bool;
      ldc_toafter : string option;
      ldc_toappendix : bool;
    }

type ldoc_rule =
    { ldr_description : texdoc option;
      ldr_modeldetails : texdoc option;
      ldr_variation : (string * texdoc) list;
      ldr_internal : texdoc option;
      ldr_norender : bool;
      ldr_toafter : string option;
      ldr_toappendix : bool;
      ldr_mergewithnext : bool;
    }


(* -------------------------------------------------------------------- *)
(*  Parse LTS documentation - high-level                                *)
(* -------------------------------------------------------------------- *)

let blank_re = Str.regexp "^[ \t\n]*$"

let blank_texdoc_content : texdoc_content -> bool
    = function
        (TexHol _    ,_) -> false
      | (TexDir _    ,_) -> false
      | (TexContent s,_) -> Str.string_match blank_re s 0

let blank_texdoc : texdoc -> bool
    = fun ts ->
      List.for_all blank_texdoc_content ts

let todo3_re = Str.regexp "[ \n\t]*TODO3[ \n\t]*"

let rec collect_texcontent : texdoc -> string list -> (string * texdoc)
    = fun d ss ->
      match d with
      | ((TexContent s,_) :: d') -> collect_texcontent d' (s::ss)
      | _ -> (String.concat "" (List.rev ss), d)

let omit_if_todo3 : texdoc option -> texdoc option
    = fun d ->
      match d with
      | None -> None
      | Some dd ->
          match collect_texcontent dd [] with
          | (s,[]) ->
              if Str.string_match todo3_re s 0 then
                None
              else
                d
          | _ ->
              d

let pfassert : bool -> string located -> unit
    = fun b s ->
      if b then
        ()
      else
        parsesemifatal s

let rec ldocmid_is_chapter : ldoc_mid -> bool
    = function
      | [] -> false
      | ((ldoc,l),_)::ls ->
          match ldoc with
          | LdocPreamble  -> ldocmid_is_chapter ls
          | LdocChapter _ -> true
          | LdocSection _ -> false
          | LdocNop       -> ldocmid_is_chapter ls
          | _ ->
              parsesemifatal ("Chapter or section comment should begin with @chapter or @section",l);
              false

let ltsdoc_chapter0 : ldoc_chapter -> ldoctag located * texdoc -> ldoc_chapter
    = fun doc ((ldoc,l),t) ->
      let blankcheck field t =
        if blank_texdoc t then
          (parsesemifatal ("Empty "^field^" in chapter comment",l);
           None)
        else
          Some t
      in
      match ldoc with
        LdocPreamble ->
          pfassert (blank_texdoc t) ("Chapter comment has text before @section",l);
          doc
      | LdocChapter (name,t0) ->
          pfassert (isNone doc.ldh_name && isNone doc.ldh_chaptertitle && isNone doc.ldh_amble)
            ("Duplicate @chapter",l);
          let topt = blankcheck "preamble" t in
          { doc with
            ldh_name = Some name;
            ldh_chaptertitle = Some t0;
            ldh_amble = topt }
      | LdocNorender ->
          pfassert (not doc.ldh_norender)
            ("Duplicate @norender",l);
          pfassert (blank_texdoc t) ("Non-empty content under @norender tag",l);
          { doc with ldh_norender = true }
      | LdocToafter s ->
          pfassert (isNone doc.ldh_toafter) ("Duplicate @toafter "^s,l);
          pfassert (blank_texdoc t) ("Non-empty content under @toafter tag",l);
          { doc with ldh_toafter = Some s }
      | LdocToappendix ->
          pfassert (not doc.ldh_toappendix) ("Duplicate @toappendix",l);
          pfassert (blank_texdoc t) ("Non-empty content under @toappendix tag",l);
          { doc with ldh_toappendix = true }
      | LdocNop ->
          pfassert (blank_texdoc t) ("Non-empty content under ignored or no-op tag",l);
          doc
      | _ ->
          parsesemifatal ("Bad directive in chapter comment",l);
          doc

let ltsdoc_cluster0 : ldoc_cluster -> ldoctag located * texdoc -> ldoc_cluster
    = fun doc ((ldoc,l),t) ->
      let blankcheck field t =
        if blank_texdoc t then
          (parsesemifatal ("Empty "^field^" in cluster comment",l);
           None)
        else
          Some t
      in
      match ldoc with
        LdocPreamble ->
          pfassert (blank_texdoc t) ("Cluster comment has text before @section",l);
          doc
      | LdocSection (name,s,t0) ->
          pfassert (isNone doc.ldc_name && isNone doc.ldc_sectiontitle && isNone doc.ldc_preamble)
            ("Duplicate @section",l);
          let topt = blankcheck "preamble" t in
          { doc with
            ldc_name = Some name;
            ldc_sectiontitle = Some t0;
            ldc_sectioncategory =
              if s = "GEN" then Some ""
	      else if s = "ALL" then Some "(TCP and UDP)"
	      else Some ("(" ^ s ^ " only)");
            ldc_preamble = topt }
      | LdocErrors ->
          pfassert (isNone doc.ldc_errors_preamble)
            ("Duplicate @errors",l);
          let topt = blankcheck "errors preamble" t in
          { doc with ldc_errors_preamble = topt }
      | LdocError (s,t0) ->
          pfassert (not (List.mem_assoc s doc.ldc_errors))
            ("Duplicate @error "^dumpholdoc s,l);
          { doc with ldc_errors = (s,t0@(TexContent("\n"),l)::t)::doc.ldc_errors }
      | LdocErrorinclude (s,t0) ->
          pfassert (blank_texdoc t) ("Non-empty content under @errorinclude",l);
          { doc with ldc_errorincludes = (s,t0)::doc.ldc_errorincludes }
      | LdocCommoncases ->
          pfassert (isNone doc.ldc_commoncases)
            ("Duplicate @commoncases",l);
          let topt = blankcheck "common cases" t in
          { doc with ldc_commoncases = topt }
      | LdocApi ->
          pfassert (isNone doc.ldc_api)
            ("Duplicate @api",l);
          let topt = blankcheck "API" t in
          { doc with ldc_api = topt }
      | LdocModeldetails ->
          pfassert (isNone doc.ldc_modeldetails)
            ("Duplicate @modeldetails",l);
          let topt = blankcheck "model details" t in
          { doc with ldc_modeldetails = topt }
      | LdocNorender ->
          pfassert (not doc.ldc_norender)
            ("Duplicate @norender",l);
          pfassert (blank_texdoc t) ("Non-empty content under @norender tag",l);
          { doc with ldc_norender = true }
      | LdocToafter s ->
          pfassert (isNone doc.ldc_toafter) ("Duplicate @toafter "^s,l);
          pfassert (blank_texdoc t) ("Non-empty content under @toafter tag",l);
          { doc with ldc_toafter = Some s }
      | LdocToappendix ->
          pfassert (not doc.ldc_toappendix) ("Duplicate @toappendix",l);
          pfassert (blank_texdoc t) ("Non-empty content under @toappendix tag",l);
          { doc with ldc_toappendix = true }
      | LdocNop ->
          pfassert (blank_texdoc t) ("Non-empty content under ignored or no-op tag",l);
          doc
      | _ ->
          parsesemifatal ("Bad directive in cluster comment",l);
          doc

let ltsdoc_chapterorcluster : ldoc_mid -> (ldoc_chapter, ldoc_cluster) sum
    = fun ls ->
      let emptydoc =
        { ldc_name            = None;
          ldc_sectiontitle    = None;
          ldc_sectioncategory = None;
          ldc_preamble        = None;
          ldc_errors_preamble = None;
          ldc_errors          = [];
          ldc_errorincludes   = [];
          ldc_commoncases     = None;
          ldc_api             = None;
          ldc_modeldetails    = None;
          ldc_norender        = false;
          ldc_toafter         = None;
          ldc_toappendix      = false;
        }
      in
      let emptychap =
        { ldh_name         = None;
          ldh_chaptertitle = None;
          ldh_amble        = None;
          ldh_norender        = false;
          ldh_toafter         = None;
          ldh_toappendix      = false;
        }
      in
      let l = match ls with
      | (((_,l),_)::_) -> l
      | [] -> zero_loc
      in
      match ls with
      | [((LdocPreamble,_), t)] ->
          pfassert false ("Old-style cluster comment",l);
          Inr { emptydoc with
                ldc_name            = Some (gensym ());
                ldc_sectiontitle    = Some [];
                ldc_sectioncategory = Some "?";
                ldc_preamble = Some ((TexContent "(PARSED OLD-STYLE COMMENT)\n\n",zero_loc)::t) }
      | _ when ldocmid_is_chapter ls ->
          let doc =
            List.fold_left ltsdoc_chapter0 emptychap ls
          in
          pfassert (isSome doc.ldh_name           ) ("Missing name in chapter comment",l);
          pfassert (isSome doc.ldh_chaptertitle   ) ("Missing chapter title in chapter comment",l);
          Inl doc
      | _ ->
          let doc =
            List.fold_left ltsdoc_cluster0 emptydoc ls
          in
          pfassert (isSome doc.ldc_name           ) ("Missing name in cluster comment",l);
          pfassert (isSome doc.ldc_sectiontitle   ) ("Missing section title in cluster comment",l);
          pfassert (isSome doc.ldc_sectioncategory) ("Missing section category in cluster comment",l);
          Inr doc

let ltsdoc_rule0 : ldoc_rule -> ldoctag located * texdoc -> ldoc_rule
    = fun doc ((ldoc,l),t) ->
      match ldoc with
        LdocPreamble ->
          pfassert (blank_texdoc t) ("Cluster comment has text before @description",l);
          doc
      | LdocDescription ->
          pfassert (isNone doc.ldr_description)
            ("Duplicate @description",l);
          { doc with
            ldr_description = Some t }
      | LdocModeldetails ->
          pfassert (isNone doc.ldr_modeldetails)
            ("Duplicate @modeldetails",l);
          { doc with ldr_modeldetails = Some t }
      | LdocVariation s ->
          pfassert (not (List.mem_assoc s doc.ldr_variation))
            ("Duplicate @variation "^s,l);
          { doc with ldr_variation = (s,t)::doc.ldr_variation }
      | LdocInternal ->
          pfassert (isNone doc.ldr_internal)
            ("Duplicate @internal",l);
          { doc with ldr_internal = Some t }
      | LdocNorender ->
          pfassert (not doc.ldr_norender)
            ("Duplicate @norender",l);
          pfassert (blank_texdoc t) ("Non-empty content under @norender tag",l);
          { doc with ldr_norender = true }
      | LdocToafter s ->
          pfassert (isNone doc.ldr_toafter) ("Duplicate @toafter "^s,l);
          pfassert (blank_texdoc t) ("Non-empty content under @toafter tag",l);
          { doc with ldr_toafter = Some s }
      | LdocToappendix ->
          pfassert (not doc.ldr_toappendix) ("Duplicate @toappendix",l);
          pfassert (blank_texdoc t) ("Non-empty content under @toappendix tag",l);
          { doc with ldr_toappendix = true }
      | LdocMergewithnext ->
          pfassert (not doc.ldr_mergewithnext) ("Duplicate @mergewithnext",l);
          pfassert (blank_texdoc t) ("Non-empty content under @mergewithnext tag",l);
          { doc with ldr_mergewithnext = true }
      | LdocNop ->
          pfassert (blank_texdoc t) ("Non-empty content under ignored or no-op tag",l);
          doc
      | _ ->
          parsesemifatal ("Bad directive in rule comment",l);
          doc

let ltsdoc_rule : ldoc_mid -> ldoc_rule
    = fun ls ->
      let emptydoc =
        { ldr_description     = None;
          ldr_modeldetails    = None;
          ldr_variation       = [];
          ldr_internal        = None;
          ldr_norender        = false;
          ldr_toafter         = None;
          ldr_toappendix      = false;
          ldr_mergewithnext   = false;
        }
      in
      let l = match ls with
      | (((_,l),_)::_) -> l
      | [] -> zero_loc
      in
      match ls with
        [((LdocPreamble,_), t)] ->
          pfassert false ("Old-style rule comment",l);
          { emptydoc with ldr_description = Some ((TexContent "(PARSED OLD-STYLE COMMENT)\n\n",zero_loc)::t) }
      | _ ->
          let doc =
            List.fold_left ltsdoc_rule0 emptydoc ls
          in
          pfassert (doc.ldr_mergewithnext || doc.ldr_norender || isSome doc.ldr_description ) ("Missing description in rule comment",l);
          doc


(* -------------------------------------------------------------------- *)
(*  Render LTS documentation - high-level                               *)
(* -------------------------------------------------------------------- *)

let sep_by : (unit -> unit) -> ('a -> unit) -> 'a list -> unit
    = fun s f xs ->
      match xs with
      | [] -> ()
      | (x::xs) ->
          f x;
          List.iter (fun x -> s (); f x) xs

let render_table : pvars -> ('a -> unit) -> ('a * texdoc) list -> unit
    = fun pvs f xys ->
      print_string "\\par\\begin{ltstabular}\n";
      let go (x,y) =
        f x;
        print_string "\n& ";
        rendertexdoc_pvs pvs y
      in
      let sep () =
        print_string "\\\\\\hline\n"
      in
      sep_by sep go xys;
      print_string "\\end{ltstabular}\\par\n"

let render_table3 : ('a -> unit) -> ('b -> unit) -> ('c -> unit) -> ('a * 'b * 'c) list -> unit
    = fun f g h rows ->
      print_string "\\par\\begin{ltstabulariii}\n";
      let go (x,y,z) =
        f x;
        print_string "\n& ";
        g y;
        print_string "\n& ";
        h z
      in
      let sep () =
        print_string "\\\\\n"
      in
      sep_by sep go rows;
      print_string "\\end{ltstabulariii}\\par\n"

let ssec : string -> string -> unit
    = fun style s ->
      print_string ("\\"^style^"subsection{"^s^"}\n")

let optsec : string -> string option -> string -> 'a option -> ('a -> unit) -> unit
    = fun style wrapcmd s v f ->
      match v with
        Some x ->
          ssec style s;
          (match wrapcmd with
          | Some cmd ->
              wrap ("\\"^cmd^"{") "}" f x
          | None -> f x)
      | None ->
          ()

let optsecs : string -> string -> 'a list -> ('a list -> unit) -> unit
    = fun style s v f ->
      match v with
        ((_::_) as x) ->
          ssec style s;
          f x
      | [] ->
          ()

let render_desc : hol_content -> unit
    = function
      | (HolText d,_) ->
          let s = dumptextdoc d in
          print_string (texify_text s)
      | (HolTex d,_) ->
          rendertexdoc d
      | (_,l) ->
          (parsesemifatal ("Internal: Unexpected description content",l);
           ())


let render_ltsdoc_chapter : ldoc_chapter -> unit
    = fun doc ->
      wrap "\\chaptersection{" "}\n"
        (option () rendertexdoc) doc.ldh_chaptertitle;
      option () (fun s -> print_string ("\\label{"^s^"}%\n")) doc.ldh_name;
      wrap "\\chapcomm{" "}\n"
        (option () rendertexdoc) (omit_if_todo3 doc.ldh_amble)


let render_ltsdoc_cluster : (string * string option * hol_content option) list -> ldoc_cluster -> unit
    = fun summary doc ->
      wrap "\\clustersection{" "}\n"
        (fun () ->
          print_string (optionId "\\textless unknown\\textgreater " doc.ldc_sectioncategory);
          print_string "}{";
          option () rendertexdoc doc.ldc_sectiontitle
        ) ();
      option () (wrap "\\seccomm{" "}" rendertexdoc) (omit_if_todo3 doc.ldc_preamble);
      if isSome doc.ldc_errors_preamble || doc.ldc_errors <> [] then begin
        ssec "cluster" "Errors";
        wrap "\\seccomm{" "}"
          (fun () ->
            option () rendertexdoc doc.ldc_errors_preamble;
            (match doc.ldc_errors with
              (_::_) as es ->
                render_table [] (wrap "$" "$" (munge_holdoc [])) (List.rev es)
            | [] ->
                ())
          ) ()
      end;
      optsec "cluster" (Some "seccomm") "Common cases" doc.ldc_commoncases rendertexdoc;
      optsec "cluster" (Some "seccomm") "API" doc.ldc_api rendertexdoc;
      optsec "cluster" (Some "seccomm") "Model details" doc.ldc_modeldetails rendertexdoc;
      optsecs "cluster" "Summary" summary
        (render_table3
           (wrap "$\\tsrule{" "}$" print_string $ texify_math)
           (option () (wrap "\\textbf{" "}" print_string))  (* already texified *)
           (option () render_desc));
      ssec "cluster" "Rules";
      print_string "~"  (* ugh, dummy content to make the subsection non-vacuous *)


let render_ltsdoc_rule : pvars -> ldoc_rule -> unit
    = fun pvs doc ->
      optsec "rule" None "Description" (omit_if_todo3 doc.ldr_description) (rendertexdoc_pvs pvs);
      optsec "rule" None "Model details" doc.ldr_modeldetails (rendertexdoc_pvs pvs);
      optsecs "rule" "Variations" (List.rev doc.ldr_variation) (render_table pvs print_string);
      (if !opt_internal then optsec "rule" None "Internal" doc.ldr_internal (rendertexdoc_pvs pvs));
      (if isSome doc.ldr_description || isSome doc.ldr_modeldetails || not (null doc.ldr_variation) || (!opt_internal && isSome doc.ldr_internal) then
        print_string "\\rrulepad ")


(* -------------------------------------------------------------------- *)
(*  High-level document model                                           *)
(* -------------------------------------------------------------------- *)

type rule_body =
    { r_name        : string;
      r_var_list    : string list;
      r_proto       : string list;
      r_category    : string list;
      r_description : hol_content option;
      r_lhs         : holdoc;
      r_label       : string * holdoc * string;
      r_rhs         : holdoc;
      r_side        : holdoc option;
      r_comment     : ldoc_rule option;
    }

type netrule_body =
    { rb_name        : string;
      rb_var_list    : string list;
      rb_description : hol_content option;
      rb_lhs         : holdoc;
      rb_label       : string * holdoc * string;
      rb_rhs         : holdoc;
      rb_side        : holdoc option;
      rb_comment     : ldoc_rule option;
    }

type chaptercomment_body =
    { h_name : string;
      h_body : ldoc_chapter;
    }

type sectioncomment_body =
    { c_name : string;
      c_body : ldoc_cluster;
      c_summary : (string * string option * hol_content option) list;  (* name, category, description of items in section *)
    }

type definition_body =
    { d_name : string;
      d_description : hol_content option;
      d_body : holdoc;
      d_comment : ldoc_rule option;
    }

type type_body =
    { t_name : string;
      t_description : hol_content option;
      t_body : holdoc;
      t_comment : ldoc_rule option;
    }

type item =
    Rule of rule_body
  | NetRule of netrule_body
  | Definition of definition_body
  | Type of type_body
  | Directive of directive_content  (* a directive that is not inside an item *)
  | Block of item list  (* IN REVERSE ORDER *) (* multiple (short) items merged together, generated by @mergewithnext *)
  | SectionComment of sectioncomment_body
  | ChapterComment of chaptercomment_body


(* @norender processing: norender set? *)
let rec item_norender : item -> bool
    = function
      | Rule r           -> option false (fun r -> r.ldr_norender) r.r_comment
      | NetRule r           -> option false (fun r -> r.ldr_norender) r.rb_comment
      | ChapterComment h -> h.h_body.ldh_norender
      | SectionComment c -> c.c_body.ldc_norender
      | Block b          -> option false item_norender (headopt b)
      | Definition d     -> option false (fun r -> r.ldr_norender) d.d_comment
      | Type t           -> option false (fun r -> r.ldr_norender) t.t_comment
      | Directive _      -> false

(* @toafter processing: name of an item *)
let rec item_name : item -> string option
    = function
      | Rule r       -> Some r.r_name
      | NetRule r       -> Some r.rb_name
      | ChapterComment h -> Some h.h_name
      | SectionComment c -> Some c.c_name
      | Definition d -> Some d.d_name
      | Type t       -> Some t.t_name
      | Block b      -> option None item_name (headopt (List.rev b))
      | Directive _  -> None

(* collect all names of an item *)
let rec item_names : item -> string list
    = function
      | Rule r       -> [r.r_name]
      | NetRule r       -> [r.rb_name]
      | ChapterComment h -> [h.h_name]
      | SectionComment c -> [c.c_name]
      | Definition d -> [d.d_name]
      | Type t       -> [t.t_name]
      | Block b      -> List.concat (List.rev_map item_names b)
      | Directive _  -> []

(* @toafter processing: after-request of an item *)
let rec item_after : item -> string option
    =
  let getafter rc =
    match rc with
    | Some c -> c.ldr_toafter
    | None   -> None
  in
  function
    | Rule r       -> getafter (r.r_comment)
    | NetRule r       -> getafter (r.rb_comment)
    | ChapterComment h -> h.h_body.ldh_toafter
    | SectionComment c -> c.c_body.ldc_toafter
    | Definition d -> getafter (d.d_comment)
    | Type t       -> getafter (t.t_comment)
    | Block b      -> option None item_after (headopt b)
    | Directive _  -> None

let rec clear_item_after : item -> item
    = fun i ->
      let clearafter rc =
        match rc with
        | Some c -> Some { c with ldr_toafter = None }
        | None   -> None
      in
      match i with
      | Rule r               -> Rule { r with r_comment = clearafter r.r_comment }
      | ChapterComment h     -> ChapterComment { h with h_body = { h.h_body with ldh_toafter = None }}
      | SectionComment c     -> SectionComment { c with c_body = { c.c_body with ldc_toafter = None }}
      | Definition d         -> Definition { d with d_comment = clearafter d.d_comment }
      | Type t               -> Type { t with t_comment = clearafter t.t_comment }
      | Block []             -> i
      | Block (b::bs)        -> Block (clear_item_after b::bs)
      | Directive _          -> i

(* @toappendix processing: appendix-request of an item *)
let rec item_appendix : item -> bool
    =
  let getappendix rc =
    match rc with
    | Some c -> c.ldr_toappendix
    | None   -> false
  in
  function
    | Rule r       -> getappendix (r.r_comment)
    | NetRule r       -> getappendix (r.rb_comment)
    | ChapterComment h -> h.h_body.ldh_toappendix
    | SectionComment c -> c.c_body.ldc_toappendix
    | Definition d -> getappendix (d.d_comment)
    | Type t       -> getappendix (t.t_comment)
    | Block b      -> option false item_appendix (headopt b)
    | Directive _  -> false

let rec clear_item_appendix : item -> item
    = fun i ->
      let clearappendix rc =
        match rc with
        | Some c -> Some { c with ldr_toappendix = false }
        | None   -> None
      in
      match i with
      | Rule r               -> Rule { r with r_comment = clearappendix r.r_comment }
      | ChapterComment h     -> ChapterComment { h with h_body = { h.h_body with ldh_toappendix = false }}
      | SectionComment c     -> SectionComment { c with c_body = { c.c_body with ldc_toappendix = false }}
      | Definition d         -> Definition { d with d_comment = clearappendix d.d_comment }
      | Type t               -> Type { t with t_comment = clearappendix t.t_comment }
      | Block []             -> i
      | Block (b::bs)        -> Block (clear_item_appendix b::bs)
      | Directive _          -> i


(* @mergewithnext processing *)
let rec item_mergewithnext : item -> bool
    = fun item ->
      let get rc n =
        match rc with
        | Some c ->
            if c.ldr_mergewithnext then
              if     c.ldr_description  = None
                  && c.ldr_modeldetails = None
                  && c.ldr_variation    = []
                  && c.ldr_internal     = None
                  && c.ldr_norender     = false
                  && c.ldr_toafter      = None
                  && c.ldr_toappendix   = false
              then
                true
              else
                (parsesemifatal ("Cannot merge item with nonempty comment: "^n,zero_loc);
                 false)
            else
              false
        | None ->
            false
      in
      match item with
      | Rule r           -> (match r.r_comment with
                            | Some c ->
                                if c.ldr_mergewithnext then
                                  parsesemifatal ("Cannot merge LTS rules: "^r.r_name,zero_loc);
                                false
                            | None ->
                                false)
      | NetRule r -> false
      | ChapterComment h -> false
      | SectionComment c -> false
      | Definition d     -> get d.d_comment d.d_name
      | Type t           -> get t.t_comment t.t_name
      | Block b          -> option false item_mergewithnext (headopt b)
      | Directive _      -> false



(* -------------------------------------------------------------------- *)
(*  HOL fragment parsers                                                *)
(* -------------------------------------------------------------------- *)

(* zero or more white space on one line *)
let rec parse_sp : holparser_
    = function
        ((HolWhite  _,_) :: ds)
          -> parse_sp ds
      | ds -> ds

(* zero or more white space, may be multi-line *)
let rec parse_sp' : holparser_
    = function
        ((HolWhite  _,_) :: ds)
      | ((HolIndent _,_) :: ds)
          -> parse_sp' ds
      | ds -> ds

(* optional comment *)
let rec parse_optcomm : hol_content option holparser
    = function
        (((HolText _,_) as d) :: ds) -> (Some d,ds)
      | (((HolTex  _,_) as d) :: ds) -> (Some d,ds)
      | ds                           -> (None,  ds)

(* optional TeX comment *)
let rec parse_opttexcomm : texdoc located option holparser
    = function
        ((HolTex t,l) :: ds) -> (Some (t,l),ds)
      | ds                   -> (None,  ds)

(* particular token *)
let parse_x : hol_content0 -> string -> holparser_
    = fun x s -> function
        ((d,_)::ds) when d = x -> ds
      | ds -> parsefail (dumphol_content (x,zero_loc)) s ds

(* rule variable list *)
let parse_rulevars : string -> string list holparser
    = fun rulename ->
      let rec go vs = function
        ((HolIdent(b,s)         ,_) ::ts) -> go (s::vs) ts
      | ((HolDir (DirVARS bis,_),_) ::ts) -> go (List.map snd bis @ vs) ts
      | ((HolWhite _            ,_) ::ts)
      | ((HolIndent _           ,_) ::ts) -> go vs ts
      | ((HolSep "."            ,_) ::ts) -> (List.rev vs,ts)
      | ts -> parsefail "ident, space, or separator" ("while parsing rule "^rulename^" variable list") ts
    in
    go []

(* identifiers without intervening comments *)
let parse_idsnocomm : string list holparser
    = let rec go vs = function
        ((HolIdent(true,s),_)::ts) -> go (s::vs) ts
      | ((HolWhite _      ,_)::ts) -> go vs ts
      | ts                         -> (List.rev vs, ts)
    in
    go []

(* all stuff until n blank lines *)
let parse_chunk : int -> string -> holdoc holparser
    = fun n0 s ->
      let rec go n ds ds_blanks = function
          (((HolIndent(l),_) as d)::ts) ->
            if n = 0 then
              (List.rev ds,ts)
            else
              go (n-1) ds (d::ds_blanks) ts
        | (t::ts) ->
            go n0 (t::ds_blanks@ds) [] ts
        | [] ->
            parsefail (string_of_int n0^" blank lines") s []
      in
      go n0 [] []

(* a newline *)
let parse_indent : string -> holparser_
    = fun s -> function
        ((HolIndent _,_)::ds) -> ds
      | ds -> parsefail "indent" s ds

(* an optional newline *)
let parse_optindent : holparser_
    = function
        ((HolIndent _,_)::ds) -> ds
      | ds -> ds

(* an identifier *)
let parse_ident : string -> string holparser
    = fun s -> function
        ((HolIdent(_,s),_)::ds) -> (s,ds)
      | ds -> parsefail "ident" s ds

(* parse until "--" or "---" at start of line; blank line is an error;
   line on which token occurs is not included in parse. *)
let parse_lhs : string -> holdoc holparser
    = fun rulename ts ->
      (* number of newlines in a row;
         at start of line?
         tokens read so far on this line
         tokens read so far on previous lines
         newline tokens read so far
         start of line pointer
         input stream *)
      let rec go newlines start ds ds0 ds_newlines ts0 = function
          (((HolIndent _,_) :: _) as ts) when newlines >= 1 ->
            parsefail "label" ("while parsing lhs of rule "^rulename) ts
        | (((HolIndent _,_) as d)::ts) ->
            go (newlines+1) true [] (ds @ ds0) (d::ds_newlines) ts ts
        | (((HolWhite _,_) as d)::ts) ->
            go 0 start (d::ds_newlines@ds) ds0 [] ts0 ts
        | ((HolIdent(false,"--"),_)::ts)
        | ((HolIdent(false,"---"),_)::ts) when start ->
            (List.rev ds0,ts0)
        | (d::ts) ->
            go 0 false (d::ds_newlines@ds) ds0 [] ts0 ts
        | [] ->
            parsefail "lhs or label" ("while parsing lhs of rule "^rulename) []
      in
      go 0 true [] [] [] ts ts

(* parse label of rule *)
let parse_label : string -> (string * holdoc * string) holparser
    = fun rulename ts ->
      let arrowlefts = ["--";"---"] in
      let arrowrights = ["-->";"--->";"--=>"] in
      let rec go1 = function
          ((HolWhite _,_)::ts) -> go1 ts
        | ((HolIdent(_,s),_)::ts) when List.mem s arrowlefts
              -> go2 s [] ts
        | ts -> parsefail "label arrow" ("when looking for label of rule "^rulename) ts
      and go2 s1 ds = function
          ((HolIdent(_,s),_)::ts) when List.mem s arrowrights ->
              go3 s1 (List.rev ds) s ts
        | (((HolIndent _,_) :: _) as ts) ->
            parsefail "end of label arrow" ("when reading label of rule "^rulename) ts
        | (t::ts) -> go2 s1 (t::ds) ts
        | [] -> parsefail "end of label arrow" ("when reading label of rule "^rulename) []
      and go3 s1 lab s2 = function
          ((HolWhite _,_)::ts) -> go3 s1 lab s2 ts
        | ((HolIndent _,_)::ts) -> ((s1,lab,s2),ts)
        | ts -> parsefail "newline" ("after label of rule "^rulename) ts
      in
      go1 ts

(* parse an LTS rule *)
let parse_rule : rule_body holparser
    = fun ds ->
      let ds = parse_sp' ds in
      let ds = parse_x (HolSep("(")) "at start of rule" ds in
      let ds = parse_sp ds in
      let ds = parse_x (HolIdent(false,"!")) "at start of rule variable list" ds in
      let (var_list,ds) = parse_rulevars "<unknown>" ds in
      let ds = parse_sp' ds in
      let (name,ds) = parse_ident "while looking for rule name" ds in
      let ds = parse_sp ds in
      let ds = parse_x (HolIdent(false,"/*")) ("after rule "^name^" name") ds in
      let ds = parse_sp ds in
      let (proto,ds) = parse_idsnocomm ds in
      let ds = parse_x (HolSep(",")) ("after rule "^name^" protocol") ds in
      let ds = parse_sp ds in
      let (category,ds) = parse_idsnocomm ds in
      let ds = parse_sp ds in
      let (description,ds) = parse_optcomm ds in
      let ds = parse_sp ds in
      let ds = parse_x (HolIdent(false,"*/")) ("after rule "^name^" category and description") ds in
      let ds = parse_sp' ds in
      let (lhs,ds) = parse_lhs name ds in
      let (label,ds) = parse_label name ds in
      let (rhs,ds) = parse_chunk 1 ("right-hand side of rule "^name) ds in
      let ds = parse_sp' ds in
      let ds = parse_x (HolIdent(false,"<==")) ("after conclusion of rule "^name) ds in
      let ds = parse_sp ds in
      let ds = parse_indent ("after <== in rule "^name) ds in
      let ds = parse_sp' ds in
      let (side,ds) = parse_chunk 2 ("side condition of rule "^name) ds in
      let ds = parse_sp' ds in
      let (comment,ds) = parse_opttexcomm ds in
      let ds = parse_sp' ds in
      let ds = parse_x (HolSep ")") ("at end of rule "^name) ds in
      let ds = parse_sp' ds
      in
      ({ r_name        = name       ;
         r_var_list    = var_list   ;
         r_proto       = proto      ;
         r_category    = category   ;
         r_description = description;
         r_lhs         = lhs        ;
         r_label       = label      ;
         r_rhs         = rhs        ;
         r_side        = if List.for_all isIndent side then None else Some side;
         r_comment     = match comment with
                           None -> None
                         | Some x -> Some (ltsdoc_rule (ltsdoc_mid x));
       }, ds)

let parse_netrule : netrule_body holparser
    = fun ds ->
      let ds = parse_sp' ds in
      let ds = parse_x (HolSep("(")) "at start of rule" ds in
      let ds = parse_sp ds in
      let ds = parse_x (HolIdent(false,"!")) "at start of rule variable list" ds in
      let (var_list,ds) = parse_rulevars "<unknown>" ds in
      let ds = parse_sp' ds in
      let (name,ds) = parse_ident "while looking for rule name" ds in
      let ds = parse_sp ds in
      let ds = parse_x (HolIdent(false,"/**/")) ("after rule "^name^" name") ds in
      let ds = parse_sp ds in
      let (lhs,ds) = parse_lhs name ds in
      let (label,ds) = parse_label name ds in
      let (rhs,ds) = parse_chunk 1 ("right-hand side of rule "^name) ds in
      let ds = parse_sp' ds in
      let ds = parse_x (HolIdent(false,"<==")) ("after conclusion of rule "^name) ds in
      let ds = parse_sp ds in
      let ds = parse_indent ("after <== in rule "^name) ds in
      let ds = parse_sp' ds in
      let (side,ds) = parse_chunk 2 ("side condition of rule "^name) ds in
      let ds = parse_sp' ds in
      let (comment,ds) = parse_opttexcomm ds in
      let ds = parse_sp' ds in
      let ds = parse_x (HolSep ")") ("at end of rule "^name) ds in
      let ds = parse_sp' ds in
      ({ rb_name        = name       ;
         rb_var_list    = var_list   ;
         rb_description = None (* FIXME *);
         rb_lhs         = lhs        ;
         rb_label       = label      ;
         rb_rhs         = rhs        ;
         rb_side        = if List.for_all isIndent side then None else Some side;
         rb_comment     = match comment with
                           None -> None
                         | Some x -> Some (ltsdoc_rule (ltsdoc_mid x));
       }, ds)


(* -------------------------------------------------------------------- *)
(*  MoSML fragment parsers                                              *)
(* -------------------------------------------------------------------- *)

(* zero or more white space, may be multi-line *)
let rec parsemosml_sp' : mosmlparser_
    = function
        ((MosmlWhite  _,_) :: ds)
      | ((MosmlIndent _,_) :: ds)
          -> parsemosml_sp' ds
      | ds -> ds

(* optional TeX comment *)
let rec parsemosml_opttexcomm : texdoc located option mosmlparser
    = function
        ((MosmlTex t,l) :: ds) -> (Some (t,l),ds)
      | ds                     -> (None,  ds)


(* -------------------------------------------------------------------- *)
(*  Parse item(s) from each chunk                                       *)
(* -------------------------------------------------------------------- *)

let parse_Net_Hol_reln : hol_content list located -> item list
    = fun (ds,l) ->
      let ds = parse_sp' ds in
      let rec go vs ds =
        match ds with
          ((HolSep("("),_) :: _) ->
            (let (r,ds) = parse_rule ds in
            let vs = Rule r :: vs in
            match ds with
              ((HolIdent(false,"/\\"),_)::ds) -> go vs ds
            | []                              -> List.rev vs
            | _ -> parsefail "/\\ or end of input" ("after parsing rule "^r.r_name) ds)
              (* section comment not allowed here; that belongs *above* the rules *)
        | ((HolTex ts,l) :: ds) ->
            let ds = parse_sp' ds in
            let v =
              match ltsdoc_chapterorcluster (ltsdoc_mid (ts,l)) with
              | Inl chapter -> ChapterComment { h_name = the "ldh_name:1" chapter.ldh_name;
                                                h_body = chapter }
              | Inr cluster -> SectionComment { c_name = the "ldc_name:1" cluster.ldc_name;
                                                c_body = cluster;
                                                c_summary = [] }
            in
            go (v::vs) ds
        | ((HolIndent _,_) :: ds) ->
            go vs ds
        | ((HolWhite _,_) :: ds) ->
            go vs ds
	| ((HolText _,_) :: ds) ->
	    go vs ds
        | _ -> parsefail "rule or section comment" "while parsing LTS rules" ds
      in
      go [] ds

(* network transitions *)
let parse_Net_reln : hol_content list located -> item list
    = fun (ds,l) ->
      let ds = parse_sp' ds in
      let rec go vs ds =
        match ds with
          ((HolSep("("),_) :: _) ->
            (let (r,ds) = parse_netrule ds in
            let vs = NetRule r :: vs in
            match ds with
              ((HolIdent(false,"/\\"),_)::ds) -> go vs ds
            | []                              -> List.rev vs
            | _ -> parsefail "/\\ or end of input" ("after parsing rule "^r.rb_name) ds)
              (* section comment not allowed here; that belongs *above* the rules *)
        | ((HolTex ts,l) :: ds) ->
            let ds = parse_sp' ds in
            let v =
              match ltsdoc_chapterorcluster (ltsdoc_mid (ts,l)) with
              | Inl chapter -> ChapterComment { h_name = the "ldh_name:1" chapter.ldh_name;
                                                h_body = chapter }
              | Inr cluster -> SectionComment { c_name = the "ldc_name:1" cluster.ldc_name;
                                                c_body = cluster;
                                                c_summary = [] }
            in
            go (v::vs) ds
        | ((HolIndent _,_) :: ds) ->
            go vs ds
        | ((HolWhite _,_) :: ds) ->
            go vs ds
	| ((HolText _,_) :: ds) ->
	    go vs ds
        | _ -> parsefail "rule or section comment" "while parsing LTS rules" ds
      in
      go [] ds

let parse_xDefine : string -> hol_content list located -> texdoc located option -> item
    = fun name (ds,l) t ->
      let ds = parse_sp' ds in  (* strip leading whitespace *)
      let (desc,ds) = parse_optcomm ds in  (* find initial comment if any *)
      let ds = parse_sp' ds in  (* strip more leading whitespace *)
      let ds = List.rev (parse_sp' (List.rev ds)) in  (* strip trailing whitespace *)
      Definition { d_name = name;
                   d_description = desc;
                   d_body = ds;
                   d_comment = (match t with
                                | None -> None
                                | Some x -> Some (ltsdoc_rule (ltsdoc_mid x)))
                 }

let parse_Define : hol_content list located -> texdoc located option -> item
    = fun (ds,l) t ->
      let name =  (* name is the first identifier in the body *)
        try
          match List.find isIdent ds with
            (HolIdent(_,s),_) -> s
          | _ -> raise (NeverHappen "parse_Define")
        with
          Not_found -> (parsesemifatal ("Definition without obvious name",l);
                        "unknown")
      in
      parse_xDefine name (ds,l) t

let parse_Hol_datatype : hol_content list located -> texdoc located option -> item
    = fun (ds,l) t ->
      let name =  (* name is the first identifier in the body *)
        try
          match List.find isIdent ds with
            (HolIdent(_,s),_) -> s
          | _ -> raise (NeverHappen "parse_Hol_datatype")
        with
          Not_found -> (parsesemifatal ("Datatype without obvious name",l);
                        "unknown")
      in
      let ds = parse_sp' ds in  (* strip leading whitespace *)
      let (desc,ds) = parse_optcomm ds in  (* find initial comment if any *)
      let ds = parse_sp' ds in  (* strip more leading whitespace *)
      let ds = List.rev (parse_sp' (List.rev ds)) in  (* strip trailing whitespace *)
      Type { t_name = name;
             t_description = desc;
             t_body = ds;
             t_comment = (match t with
                          | None -> None
                          | Some x -> Some (ltsdoc_rule (ltsdoc_mid x)))
           }  (* TODO: parse properly *)


let skiptext : textdoc -> unit
    = fun ds ->
      List.iter (function (TextDir _,_) -> raise (Unimplemented ("Directive in MoSML text comment")) | _ -> ()) ds

let skiptex : texdoc -> unit
    = fun ds ->
      List.iter (function (TexDir _,_) -> raise (Unimplemented ("Directive in MoSML TeX comment")) | _ -> ()) ds


(* -------------------------------------------------------------------- *)
(*  Document grunging                                                   *)
(* -------------------------------------------------------------------- *)

(* drop all non-TeX comments from a HOL document *)
let drop_inline_text : holdoc -> holdoc
    = fun d ->
      let p = function (HolText _,_) -> false | _ -> true
      in
      List.filter p d

(* filter the HOL document as specified by the options *)
let holdoc_filter : holdoc -> holdoc
    = fun d ->
      if !opt_inlinetext then
        d
      else
        drop_inline_text d


(* -------------------------------------------------------------------- *)
(*  Parse whole file                                                    *)
(* -------------------------------------------------------------------- *)

(* parse all the items from a mosml_content stream: worker.
   Results prepended onto 'is' in reverse order. *)
(* tagstrs accumulates ident followed by zero or more strings, preceding a MosmlHol *)
let rec parseltsdoc0 : (string * string list) option -> mosml_content list -> item list -> item list
    = fun tagstrs ds is ->
      match ds with
        [] -> is
      | ((d,l)::ds) ->
          let do_commented_thing prser d' =
            let ds = parsemosml_sp' ds in
            let (c,ds) = parsemosml_opttexcomm ds in
            let i = prser (d',l) c in
            parseltsdoc0 None ds (i::is)
          in
          match d with
          | MosmlContent s -> parseltsdoc0 tagstrs ds is  (* hack: ignore intervening junk *)
          | MosmlWhite s   -> parseltsdoc0 tagstrs ds is
          | MosmlStr s     ->
              let tagstrs' =
                match tagstrs with
                | None -> None
                | Some(t,ss) -> Some(t,s::ss)
              in
              parseltsdoc0 tagstrs' ds is
          | MosmlIndent n  -> parseltsdoc0 tagstrs ds is
          | MosmlIdent(b,s) -> parseltsdoc0 (Some(s,[])) ds is  (* could be ident before backtick *)
          | MosmlHol(MosmlHolBT,d') ->
              (match tagstrs with  (* NB: strings are reversed! *)
              | Some("Net_Hol_reln",[] ) ->
                  let is' = parse_Net_Hol_reln (d',l) in
                  parseltsdoc0 None ds (List.rev_append is' is)
              | Some("Net_reln",[] ) ->
                  let is' = parse_Net_reln (d',l) in
                  parseltsdoc0 None ds (List.rev_append is' is)
              | Some("Define"      ,[] ) -> do_commented_thing parse_Define d'
              | Some("xDefine"     ,[s]) -> do_commented_thing (parse_xDefine s) d'
              | Some("Hol_datatype",[] ) -> do_commented_thing parse_Hol_datatype d'
              | Some("Hol_reln"    ,[])  -> do_commented_thing (parse_xDefine "tlang_typing") d'  (* hack alert! FIXME this relies on there being exactly one Hol_reln, and it being this one *)
              | Some(tag,_) ->
                  parsesemifatal("Ignoring "^tag^"`...` item",l);
                  parseltsdoc0 None ds is
              | None ->
                  parsesemifatal("Ignoring `...` item with no preceding identifier",l);
                  parseltsdoc0 None ds is)
          | MosmlHol(MosmlHolBTBT,d') ->
              (match tagstrs with  (* NB: strings are reversed! *)
              | Some("type_abbrev",[s]) ->
                  do_commented_thing (parse_xDefine ("type_abbrev_"^s))
                    ((HolIdent(true,"type_abbrev"),zero_loc)::(HolWhite(" "),zero_loc)::(HolIdent(true,s),zero_loc)::(HolWhite(" "),zero_loc)::d')
              | Some("new_constant",[s]) ->
                  do_commented_thing (parse_xDefine ("new_constant_"^s))
                    ((HolIdent(true,"new_constant"),zero_loc)::(HolWhite(" "),zero_loc)::(HolIdent(true,s),zero_loc)::(HolWhite(" "),zero_loc)::d')
              | Some("overload_on",[s]) ->
                  parseltsdoc0 None ds is  (* IGNORE overloadings *)
              | Some("add_record_field",[s]) ->
                  parseltsdoc0 None ds is  (* IGNORE manual record fields *)
              | Some("=",[]) ->
                  parseltsdoc0 None ds is  (* IGNORE pure terms *)
              | Some(tag,_) ->
                  parsesemifatal("Ignoring ``...`` item possibly tagged by "^tag,l);
                  parseltsdoc0 None ds is
              | None ->
                  parsesemifatal("Ignoring ``...`` item with no preceding identifier",l);
                  parseltsdoc0 None ds is)
          | MosmlText d -> (skiptext d; parseltsdoc0 tagstrs ds is)
          | MosmlTex ts ->
              let i =
                match ltsdoc_chapterorcluster (ltsdoc_mid (ts,l)) with
                | Inl chapter -> ChapterComment { h_name = the "ldh_name:2" chapter.ldh_name;
                                                  h_body = chapter }
                | Inr cluster -> SectionComment { c_name = the "ldc_name:2" cluster.ldc_name;
                                                  c_body = cluster;
                                                  c_summary = [] }
              in
              parseltsdoc0 None ds (i::is)
          | MosmlDir (DirRCSID s,_) ->
              rCSID := Some s;  (* record this as soon as we see it *)
              parseltsdoc0 tagstrs ds is
          | MosmlDir dir -> parseltsdoc0 tagstrs ds (Directive dir::is)


(* parse all the items from a mosmldoc *)
let parseltsdoc : mosmldoc -> item list
    = fun d ->
      List.rev (parseltsdoc0 None d [])


(* -------------------------------------------------------------------- *)
(*  Handle @errorincludes on whole file                                 *)
(* -------------------------------------------------------------------- *)

let holdoc_eq d1 d2 = (String.compare (dumpholdoc d1) (dumpholdoc d2) = 0)

let rec assoc_by eq k = function
  | [] -> raise Not_found
  | ((k',v)::kvs') -> if eq k k' then v else assoc_by eq k kvs'

let collect_errors : (string, (holdoc * texdoc) list) Hashtbl.t -> item list -> unit
    = fun h is ->
      let f = function
        | SectionComment c ->
            Hashtbl.add h c.c_name c.c_body.ldc_errors
        | _ -> ()
      in
      List.iter f is

let fill_in_errors : (string, (holdoc * texdoc) list) Hashtbl.t -> item list -> item list
    = fun h is ->
      let get_error (s,d) =
        try
          let hts = (Hashtbl.find h s) in
          (d, assoc_by holdoc_eq d hts)
        with
          Not_found ->
            parsesemifatal ("Could not locate error include of "^dumpholdoc d^" from "^s,zero_loc);
            (d, [])
      in
      let f = function
        | SectionComment c ->
            let new_errors =
              List.map get_error c.c_body.ldc_errorincludes
            in
            SectionComment { c with
                                 c_body = { c.c_body with
                                            ldc_errors = new_errors @ c.c_body.ldc_errors } }
        | i -> i
      in
      List.map f is

let process_error_includes : item list -> item list
    = fun is ->
      let h = Hashtbl.create 100 in
      collect_errors h is;
      fill_in_errors h is


(* -------------------------------------------------------------------- *)
(*  Reorder whole file                                                  *)
(* -------------------------------------------------------------------- *)

let remove_all : ('a, 'b) Hashtbl.t -> 'a -> unit
    = fun h x ->
      while Hashtbl.mem h x do
        Hashtbl.remove h x
      done

(* collect all items below this chunk: for a chapter, the whole
   chapter; for a section, the whole section; for an item, just
   itself. *)
let grab_chunk : item -> item list -> (item list * item list)
    = fun i is ->
      match i with
      | ChapterComment _ ->
          span (function ChapterComment _ -> false | _ -> true) is
      | SectionComment _ ->
          span (function ChapterComment _ | SectionComment _ -> false | _ -> true) is
      | _ ->
          ([],is)

let rec reorderltsdoc0 : (string, item * item list) Hashtbl.t -> (item * item list) list -> item list -> item list -> item list
(* todrop: hash table of chunks waiting to be dropped (may be multiple values per key);
   appendix: list of chunks to go in the appendix;
   seen: list of items already processed (in reverse order);
   is: list of items to be processed. *)
    = fun todrop appendix seen is ->
      match is with
      | [] ->
          (match appendix with
          | [] ->
              let r = ref seen in
              let f n (i,is) =
                parsesemifatal ("Item "^ifknown (item_name i)^" could not be dropped after "^n,zero_loc);
                r := clear_item_after i :: is @ !r
              in
              Hashtbl.iter f todrop;
              List.rev !r
          | (_::_) ->
              let is_appendix = List.concat (List.rev_map (fun (i,is) -> List.map clear_item_appendix (i::is)) appendix) in
              reorderltsdoc0 todrop [] seen is_appendix  (* for now, no special separator to mark the beginning of the appendix *))
      | (i::is) ->
          if !opt_merge && item_mergewithnext i then begin
            let b = match i with Block b -> b | _ -> [i] in
            match is with
            | (Definition _ as i2 :: is_rest)
            | (Type       _ as i2 :: is_rest) ->
                reorderltsdoc0 todrop appendix seen (Block (i2::b) :: is_rest)
            | _ ->
                parsesemifatal ("Invalid merge request for item "^ifknown (item_name i),zero_loc);
                reorderltsdoc0 todrop appendix (i::seen) is
          end else if item_appendix i then begin
            let (is_chunk,is_rest) = grab_chunk i is in
            reorderltsdoc0 todrop ((i,is_chunk)::appendix) seen is_rest
          end else match item_after i with
          | Some after ->
              let (is_chunk,is_rest) = grab_chunk i is in
              Hashtbl.add todrop after (i,is_chunk);
              reorderltsdoc0 todrop appendix seen is_rest
          | None ->
              match item_name i with
              | Some n ->
                  (* compute the list of items to be dropped here *)
                  let drop_iss = Hashtbl.find_all todrop n in
                  let drop_iss = List.rev_map (fun (i,is) -> (List.map clear_item_after (i::is))) drop_iss in
                  remove_all todrop n;
                  (* figure out where to drop them *)
                  let (is_chunk,is_rest) = grab_chunk i is in
                  (* do it *)
                  reorderltsdoc0 todrop appendix (i::seen) (is_chunk @ List.concat drop_iss @ is_rest)
              | None ->
                  reorderltsdoc0 todrop appendix (i::seen) is

let reorderltsdoc : item list -> item list
    = fun is ->
      reorderltsdoc0 (Hashtbl.create 10) [] [] is


(* -------------------------------------------------------------------- *)
(*  Compute section summaries                                           *)
(* -------------------------------------------------------------------- *)

let de_rp_proto : string -> string
    = Str.replace_first (Str.regexp ("^rp_")) ""

let rec summarise : item -> (string * string option * hol_content option) list
    = function
      | i when item_norender i -> []
      | Rule           r -> [(r.r_name,
                              Some (String.concat " " (List.map (texify_text $ de_rp_proto) r.r_proto)^": "
                                    ^String.concat " " (List.map texify_text r.r_category)),
                              r.r_description)]
      | NetRule           r -> [(r.rb_name, None, r.rb_description)]
      | Definition     d -> [(d.d_name, None, d.d_description)]
      | Type           t -> [(t.t_name, None, t.t_description)]
      | Block          b -> List.concat (List.rev_map summarise b)
      | Directive      _ -> []
      | SectionComment _ -> []
      | ChapterComment _ -> []

let rec summarisesecs0 : item list -> item list -> item list
    = fun seen is ->
      match is with
      | [] -> List.rev seen
      | (i::is) ->
          match i with
          | SectionComment c ->
              let (is_chunk, is_rest) = grab_chunk i is in
              let summary = List.concat (List.map summarise is_chunk) in
              summarisesecs0 (List.rev_append is_chunk (SectionComment { c with c_summary = summary } :: seen)) is_rest
          | _ ->
              summarisesecs0 (i :: seen) is

let summarisesecs : item list -> item list
    = fun is ->
      summarisesecs0 [] is


(* -------------------------------------------------------------------- *)
(*  Render whole file                                                   *)
(* -------------------------------------------------------------------- *)

let strip : holdoc -> holdoc
    = fun d ->
      if !(!curmodals.cOMMENTS) then
        holdoc_filter d
      else
        let is_interesting = fun (x,_) -> match x with
            HolIndent(_) -> false
          | HolWhite(_)  -> false
          | HolTex(_)    -> false
          | HolText(_)   -> false
          | _            -> true
        in
        List.filter is_interesting d

(* render a transition label *)
let munge_label : pvars -> string * holdoc * string -> unit
    = fun pvs (s1,d,s2) ->
      let n = match s2 with
      | "-->" -> 1
      | "--->" -> 1
      | "--=>" -> 2
      | _ -> (parsesemifatal ("Unknown label arrow type "^s2,zero_loc); 1)
      in
      wrap "\\Mtransition{" ("}{"^string_of_int n^"}") (munge_holdoc pvs) (strip d)

(* either define a new command, or just emit the TeX inline *)
let def_or_dump : string -> ('a -> unit) -> 'a -> unit
    = fun cmd f x ->
      if !opt_cmds then
        wrap ("\\newcommand{"^cmd^"}{") "}\n\n" f x
      else begin
        f x;
        print_string "\n\n";
      end

(* Generate index info for a possibly-multiple-def-containing definition *)
let index_info xs =
  match xs with
  | [] -> ""
  | (x1::xs_rest) ->
      "\\iA{"^texify_math x1^"}"  (* first: \iA{} *)
      ^String.concat "" (List.map (fun x -> "\\iB{"^texify_math x^"}") xs_rest)  (* rest: \iB{} *)

(* render an item to a TeX definition,
   returning the TeX command name for that definition *)
let rec renderitem : item -> string option
    = function
      | i when item_norender i ->
          None
      | Rule r ->
          let cmd = "\\" ^ texify_command r.r_name in
          let pvs =
            r.r_var_list
            @ potential_vars r.r_lhs
            @ potential_vars (match r.r_label with (_,x,_) -> x)
            @ potential_vars r.r_rhs
            @ option [] potential_vars r.r_side in
          let rrule = "\\rrule"
              ^ (if isNone r.r_side then "n" else "c")
              ^ (if isNone r.r_comment then "n" else "c") in
          def_or_dump cmd
            (fun () ->
              print_string (rrule^"{"
                            ^texify_command r.r_name^"}{"  (* anchor *)
                            ^texify_math r.r_name^"}{"     (* title *)
                            ^String.concat " " (List.map (texify_math $ de_rp_proto) r.r_proto)^": "
                            ^String.concat " " (List.map texify_math r.r_category)^"}");
              wrap "{" "}\n" (option () (munge_hol_content pvs)) r.r_description;
              wrap "{" "}\n" (munge_holdoc pvs) (strip r.r_lhs);
              wrap "{" "}\n" (munge_label pvs) r.r_label;
              wrap "{" "}\n" (munge_holdoc pvs) (strip r.r_rhs);
              wrap "{" "}\n" (option () (munge_holdoc pvs $ strip)) r.r_side;
              wrap "{" "}\n" (option () (render_ltsdoc_rule pvs)) r.r_comment;
            ) ();
          Some cmd
      | NetRule r ->
          let cmd = "\\" ^ texify_command "FIXMEcommand" in
          let pvs =
            r.rb_var_list
            @ potential_vars r.rb_lhs
            @ potential_vars (match r.rb_label with (_,x,_) -> x)
            @ potential_vars r.rb_rhs
            @ option [] potential_vars r.rb_side in
          let rrule = "\\rrule"
              ^ (if isNone r.rb_side then "n" else "c")
              ^ (if isNone r.rb_comment then "n" else "c") in
          def_or_dump cmd
            (fun () ->
              print_string (rrule^"{"
                            ^(texify_command r.rb_name)^"}{"  (* anchor *)
                            ^(texify_math r.rb_name)^"}{"     (* title *)
			    ^"}");
              wrap "{" "}\n" (option () (munge_hol_content pvs)) r.rb_description;
              wrap "{" "}\n" (munge_holdoc pvs) (strip r.rb_lhs);
              wrap "{" "}\n" (munge_label pvs) r.rb_label;
              wrap "{" "}\n" (munge_holdoc pvs) (strip r.rb_rhs);
              wrap "{" "}\n" (option () (munge_holdoc pvs $ strip)) r.rb_side;
              wrap "{" "}\n" (option () (render_ltsdoc_rule pvs)) r.rb_comment;
            ) ();
          Some cmd
      | SectionComment c ->
          let cmd = "\\seccomm" ^ texify_command c.c_name in
          def_or_dump cmd (render_ltsdoc_cluster c.c_summary) c.c_body;
          Some cmd
      | ChapterComment h ->
          let cmd = "\\chapcomm" ^ texify_command h.h_name in
          def_or_dump cmd render_ltsdoc_chapter h.h_body;
          Some cmd
      | Definition _ as i -> renderitem (Block [i])
      | Type _       as i -> renderitem (Block [i])
      | Block b as i ->
          let defname = ifknown (item_name i) in
          let defcomment = match b with (Definition d::_) -> d.d_comment | (Type t::_) -> t.t_comment | _ -> None in
          let getdesc i0 =
            match i0 with
            | Definition d -> d.d_description
            | Type t -> t.t_description
            | _ -> (parsesemifatal ("Internal error: block "^defname^" contains non-def item",zero_loc);
                    None)
          in
          let getbody i0 =
            match i0 with
            | Definition d -> d.d_body
            | Type t -> t.t_body
            | _ -> (parsesemifatal ("Internal error: block "^defname^" contains non-def item",zero_loc);
                    [])
          in
          let renderdef b i0 =
            print_string (if b then "\\subddefnA" else "\\subddefnB");
            option () (wrap "[{" "}]" render_desc) (getdesc i0);
            wrap "{" "}" (option () (print_string $ texify_math)) (item_name i0);
            wrap "{" "}\n" renderholdoc ((if !opt_inlinetextdef then function x -> x else strip) (getbody i0))
          in
          let renderdefs = function
            | [] -> ()
            | (i::is) -> renderdef true i; List.iter (renderdef false) is
          in
          let cmd = "\\defn" ^ texify_command defname in
          def_or_dump cmd
            (fun () ->
              print_string ("\\ddefn"
                            ^(if isNone defcomment then "n" else "c")
                            ^"{"^texify_command defname^"}{"  (* anchor *)
                            ^index_info (item_names i)^"}");
              wrap "{" "}\n" renderdefs (List.rev b);
              wrap "{" "}\n" (option () (render_ltsdoc_rule [])) defcomment;
            ) ();
          Some cmd
      | Directive (dir,_) ->
          do_directive dir;
          None

let renderitems : item list -> string list
    = optionCat $ List.map renderitem


(* -------------------------------------------------------------------- *)
(*  Main program                                                        *)
(* -------------------------------------------------------------------- *)

let _ =
  try
    !curmodals.rULES := true;
    let ltsdoc = parse_fileargs_ext opts (fun ()->()) "Invalid argument" ModeMosml mosml_main in
    print_string "%%%% AUTOGENERATED FILE (from LTS source) -- DO NOT EDIT! %%%%\n";
    let items = parseltsdoc ltsdoc in
    (match !rCSID with
      Some s -> print_string ("\\def\\rulesrcsid{"^texify_text s^"}\n\n")
    | None   -> ());
    let items = process_error_includes items in
    let items = reorderltsdoc items in
    let items = summarisesecs items in
    let cmds = renderitems items in
    if !opt_cmds then begin
      wrap "\\newcommand{\\dumpallrules}{\n" "}\n\n"
        (List.iter (fun rn -> print_string ("\\showrule{"^rn^"}\n"))) cmds;
    end;
    print_string "%%%% END %%%%\n";
    dump_unseen_strings ()
  with
  | ParseFail(s,l) ->
      let s = ("***** DYING ON FATAL EXCEPTION *****\n"^
               my_format_location l ^ s ^ "\n") in
      prerr_string s;
      print_string s;
      exit 1
  | e ->
      let s = ("***** DYING ON FATAL EXCEPTION *****\n"^Printexc.to_string e^"\n") in
      prerr_string s;
      print_string s;
      exit 1
