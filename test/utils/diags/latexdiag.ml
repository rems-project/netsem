(* ---------------------------------------------------------------------- *)
(* Netsem Project: simple latex diagram library                           *)
(* Steve Bishop - Created 20031016                                        *)
(* $Id: latexdiag.ml,v 1.9 2004/12/18 14:41:22 pes20 Exp $ *)
(* ---------------------------------------------------------------------- *)

open Printf

type color =
    BLACK
  | LIGHTGRAY
  | DARKGRAY

type diaglib_graphic =
    (* DLABEL of xpos * ypos * boxlength * angle * string *)
    DLABEL of int * int * int * int * string
    (* DLINE of xpos * ypos * length * angle * colour *)
  | DLINE of  int * int * int * int * color
    (* DARROWLR of xpos * ypos * length * angle * string *  *)
    (* left ratio * right ratio (left-to-right labelled) *)
  | DARROWLR of int * int * int * int * string * float * float * int
    (* DARROWRL of xpos * ypos * length * angle * string *  *)
    (* left ratio * right ratio (right-to-left labelled) *)
  | DARROWRL of int * int * int * int * string * float * float * int
    (* DARROWU of xpos * ypos * length * angle  (unlabelled) *)
  | DARROWU of int * int * int * int
    (* DDISC of xpos * ypos * diameter *)
  | DDISC of int * int * int


type alignment =
    LEFT
  | RIGHT
  | CENTRE
  | ALL

type diaglib_object =
    (* LABEL of x * y * max length * angle * alignment * string *)
    LABEL of int * int * int * int * alignment * string
    (* LINE of x1 * y1 * x2 * y2 * colour *)
  | LINE of  int * int * int * int * color
    (* ARROW of x1 * y1 * x2 * y2 * label * label position *)
  | ARROW of int * int * int * int * string * alignment
    (* DISC of x * y * diameter *)
  | DISC of int * int * int


type diaglib_page = diaglib_graphic list


type diaglib_hnd = {
    page_width  : int;
    page_height : int;
    preamble    : string;
    postamble   : string;
    doctitle    : string;
    pages       : diaglib_page list ref  (* order important *)
  }

exception Diagram_failure

let sep = "% -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-\n"

let rad_2_degs = 180.0 /. 3.1415927


(* -=-=-=-=-=-=-=-=-=-=-=-=--=-=--=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


let readfile filename =
  let ch =
    try open_in filename
    with Sys_error(es) ->
      prerr_endline ("readfile failed on file " ^ filename ^ " : " ^ es);
      exit(1)
  in
  let string =
    let rec readloop str =
      try
	readloop (str ^ (input_line ch) ^ "\n")
      with End_of_file ->
	str
    in readloop ""
  in
  close_in ch;
  string


(* -=-=-=-=-=-=-=-=-=-=-=-=--=-=--=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


(* diaglib_init: latex_preamble_filename -> latex_postamble_filename ->
     page_width -> page_height -> document_title -> handle *)
let diaglib_init preamble_file postamble_file width height title =

  {
   page_width = width;
   page_height = height;
   preamble = readfile preamble_file;
   postamble = readfile postamble_file;
   doctitle = title;
   pages = ref [[(*empty first page*)]];
  }


(* -=-=-=-=-=-=-=-=-=-=-=-=--=-=--=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

let check_pages handle n =
  let act_len = List.length !(handle.pages) - 1 in
  if act_len < n then
    let rec create_blank_pages num =
      if num = 1 then [[]]
      else if num < 1 then [] (* just to be safe *)
      else []::(create_blank_pages (num-1))
    in
    handle.pages := !(handle.pages) @ (create_blank_pages (n - act_len))
  else
    ()

(* diablib_add: handle -> graphic to add -> unit *)
let diaglib_add handle graphic =
  let line_munge x1 y1 x2 y2 c =
    let x1,y1,x2,y2 =
      if y1 <= y2 then x1,y1,x2,y2
      else x2,y2,x1,y1 in
    let convert_line x1 y1 x2 y2 c =
      if y1 = y2 then
	[y1 / handle.page_height,
	 if x1 <= x2 then
	   DLINE(x1, handle.page_height - (y1 mod handle.page_height),x2-x1,0,c)
	 else
	   DLINE(x2, handle.page_height - (y1 mod handle.page_height),x1-x2,0,c)]
      else (
	let x1_f,y1_f,x2_f,y2_f = float_of_int x1, float_of_int y1,
	  float_of_int x2, float_of_int y2 in
	let len =
	  if x1 = x2 then y2 - y1
	  else truncate (sqrt (((x2_f -. x1_f) ** 2.0) +.
				 ((y2_f -. y1_f) ** 2.0))) in
	let angle =
	  if x1 = x2 then 270
	      else if x1 < x2 then
		270 + truncate ((atan ((x2_f -. x1_f) /. (y2_f -. y1_f)))
				  *. rad_2_degs)
	      else
		270 - (truncate ((atan ((x1_f -. x2_f) /. (y2_f -. y1_f)))
				   *. rad_2_degs)) in
	[y1 / handle.page_height,
	 DLINE((if x1 < x2 then x1 else x2),
		   handle.page_height - (y1 mod handle.page_height),len,angle,c)]
       ) in

    if (y1 / handle.page_height) = (y2 / handle.page_height) then
      convert_line x1 y1 x2 y2 c
    else
      let rec split_line curr_x1 curr_y1 x2 y2 =
	if (curr_y1 / handle.page_height) = (y2 / handle.page_height) then
	  convert_line curr_x1 curr_y1 x2 y2 c
	else
	  let new_ydiff = handle.page_height -
	      (curr_y1 mod handle.page_height) - 1 in
	  let new_y2 = curr_y1 + new_ydiff in
	  let xdiff = float_of_int (x2 - curr_x1) in
	  let ydiff = float_of_int (y2 - curr_y1) in
	  let new_x2 = curr_x1 + (truncate (
				  (xdiff /. ydiff) *. float_of_int (new_ydiff))) in
	  (convert_line curr_x1 curr_y1 new_x2 new_y2 c) @
	  (split_line new_x2 (new_y2 + 1) x2 y2)
      in split_line x1 y1 x2 y2
  in

  let insert_list =
    match graphic with
      LABEL(x,y,len,angle,align,text) ->
	[(y / handle.page_height,
	  DLABEL(x, handle.page_height - (y mod handle.page_height), len, angle, text))
	]

    | LINE(x1,y1,x2,y2,c) ->
	line_munge x1 y1 x2 y2 c

    | DISC(x,y,diam) ->
	[(y / handle.page_height,
	  DDISC(x, handle.page_height - (y mod handle.page_height), diam))]

    | ARROW(x1,y1,x2,y2,label,align) ->
	let line_list = line_munge x1 y1 x2 y2 BLACK in
	let arrow_list = List.map
	    (function (pg, cmd) ->
	      match cmd with
		DLINE(x,y,len,angle,c) ->
		    (pg, DARROWU(x,y,len,angle))
	      |	_ -> raise Diagram_failure
	    )
	    line_list
	in
	match arrow_list with
	  [] -> raise Diagram_failure
	| (pg,DARROWU(x,y,len,angle))::ls ->
	    let lr,rr,ll = match align with
	      LEFT -> 0.15, 0.85, 3*len/7
	    | RIGHT -> 0.55, 0.45, 3*len/7
	    | CENTRE -> 0.3, 0.7, 6*len/7
	    | ALL -> 0.10, 0.90, 6*len/7 in
	     if(angle >= 0) && (angle <= 90) || (angle >= 270) && (angle <= 360) then
	       (pg, DARROWLR(x,y,len,angle,label,lr,rr,ll))::ls
	     else
	       (pg, DARROWRL(x,y,len,angle,label,lr,rr,ll))::ls
	| _ -> raise Diagram_failure
  in
  List.iter (function (a,b) -> check_pages handle a) insert_list;
  let rec insert_graphics pgs pgnum pics =
    match pgs with
      [] -> []
    | p::ps ->
	(match pics with
	  [] -> p::ps
	| ((page, cmd)::cs) ->
	    (if pgnum = page then
	      insert_graphics ((cmd::p)::ps) pgnum cs
	    else
	      p::(insert_graphics ps (pgnum+1) ((page, cmd)::cs))))
  in
  (* Update pages *)
  handle.pages := insert_graphics !(handle.pages) 0 insert_list



(* -=-=-=-=-=-=-=-=-=-=-=-=--=-=--=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


let emit_graphic ch graphic =
  match graphic with
    DLABEL(x,y,len,angle,text) ->
      let cmd = sprintf "\\rtext{(%d,%d)}{%d}{%d}{%s}\n" x y len angle text in
      output_string ch cmd
  | DLINE(x,y,len,angle,c) ->
      let prefix =
	match c with
	  BLACK -> ""
	| LIGHTGRAY -> "\\color{lightgray}"
	| DARKGRAY -> "\\color{darkgray}" in
      let cmd = sprintf "%s\\rline{(%d,%d)}{%d}{%d}\\color{black}\n" prefix x y len angle in
      output_string ch cmd
  | DARROWLR(x,y,len,angle,text,lr,rr,ll) ->
      let cmd = sprintf "\\arrowr{(%d,%d)}{%d}{%d}{%d}{%s}{%.2f}{%.2f}\n"
	  x y len angle ll text lr rr in
      output_string ch cmd
  | DARROWRL(x,y,len,angle,text,lr,rr,ll) ->
      let cmd = sprintf "\\arrowl{(%d,%d)}{%d}{%d}{%d}{%s}{%.2f}{%.2f}\n"
	  x y len angle ll text lr rr in
      output_string ch cmd
  | DARROWU(x,y,len,angle) ->
      let cmd = sprintf "\\arrowu{(%d,%d)}{%d}{%d}\n" x y len angle in
      output_string ch cmd
  | DDISC(x,y,diam) ->
      let cmd = sprintf "\\disc{(%d,%d)}{%d}\n" x y diam in
      output_string ch cmd


(* -=-=-=-=-=-=-=-=-=-=-=-=--=-=--=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


(* diablib_emit: handle -> latex_output_filename -> unit *)
let diaglib_emit handle filename unitlength_opt scale_opt =
  (* Open the output file *)
  let ch =
    try open_out filename
    with Sys_error(es) ->
      prerr_endline ("diaglib_emit failed to open output file " ^
		     filename ^ " : " ^ es);
      exit(1)
  in
  (* Write warning and preamble to output file *)
  output_string ch sep;
  output_string ch "% Warning: this file was automatically generated. Edit with care\n";
  output_string ch (sep ^ "\n");
  output_string ch handle.preamble;

  (* optional unitlength setting *)
  (match unitlength_opt with
    None -> ()
  | Some(x) -> output_string ch ("\\setlength{\\unitlength}{"^(string_of_float x)^"pt}\n"));

  (* Process each page... *)
  let rec process_pages page_list pagenum =
    match page_list with
      [] -> ()
    | p::ps ->
	(* Start a new page *)
	output_string ch sep;
	output_string ch ("% Start of page " ^ (string_of_int pagenum) ^ "\n");
	output_string ch sep;
	if pagenum <> 1 then output_string ch "\\newpage\n";

	(* Start a new picture *)
        (* optional scalebox *)
        (match scale_opt with
          None -> ()
        | Some(x) -> output_string ch ("\\scalebox{"^(string_of_float x)^"}{\n"));

	output_string ch ("\\begin{picture}(" ^ (string_of_int handle.page_width) ^
			  "," ^ (string_of_int handle.page_height) ^ ")\n");

	(* Process the graphics on each page *)
	let rec process_graphics graphic_list =
	  match graphic_list with
	    [] -> ()
	  | g::gs ->
	      emit_graphic ch g;
	      process_graphics gs
	in process_graphics (List.rev p); (* reverse order so we output from top-down *)
	(* Finish the picture, hence ending the page *)
	output_string ch "\\end{picture}\n\n";

        (* close optional scalebox *)
        (match scale_opt with
          None -> ()
        | Some(x) -> output_string ch ("}\n"));



	(* Process the next page *)
	process_pages ps (pagenum+1)
  in

  (* Start processing the first page *)
  process_pages !(handle.pages) 1;
  (* Write the latex postamble and close *)
  output_string ch handle.postamble;
  close_out ch


(* -=-=-=-=-=-=-=-=-=-=-=-=--=-=--=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

let texify_text_list =
  [('_', "\\textunderscore{}")
  ;('~', "\\textasciitilde{}")
  ;('$', "\\$")
  ;('%', "\\%")
  ;('&', "\\&")
  ;('\\', "\\textbackslash{}")
  ;('^', "\\textasciicircum{}")
  ;('{', "\\{")
  ;('}', "\\}")
  ;('#', "\\#")
  ;('<', "\\textless{}")  (* the {} is to work around a bug in LaTeX / fontenc: \textless\textless == \textguillemotleft  (!!!) *)
  ;('>', "\\textgreater{}")  (* the {} is to work around a bug in LaTeX / fontenc *)
  ]

let dotexify tlist =
  let re = Str.regexp (String.concat "\\|" (List.map (function (c,_) -> Str.quote (String.make 1 c)) tlist))
  in
  let go s =
    match s with
      Str.Text(s)  -> s
    | Str.Delim(s) -> List.assoc (String.get s 0) tlist
  in
  function s ->
    String.concat "" (List.map go (Str.full_split re s))

let texify_text = dotexify texify_text_list

let convert_string s =
  dotexify texify_text_list s

(* -=-=-=-=-=-=-=-=-=-=-=-=--=-=--=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* END OF FILE *)
(* -=-=-=-=-=-=-=-=-=-=-=-=--=-=--=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
