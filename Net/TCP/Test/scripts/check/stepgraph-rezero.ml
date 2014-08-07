(* takes the first time, and emits differences relative to that
   first time.  Actually, emits log10 of that difference. *)

let readintpair () =
  let s = read_line () in
  let firstspace = String.index s ' ' in
  let s1 = String.sub s 0 firstspace  in
  let s2 = String.sub s (1+firstspace) (String.length s - firstspace -1) in
(*  let _ = print_string ("x"^s1^"y"^s2^"z\n") in *)
  let i1 = int_of_string s1 in
  let i2 = int_of_string s2 in
  (i1,i2)

let writetriple (i1,i2,i3) = print_int i1; print_string " "; print_float i2; print_string " "; print_float i3; print_string "\n"; flush stdout

let _ =
  try
    let (i1,i2) = readintpair () in
(*    let _ = writeintpair (i1,0) in *)
    let i2'_prev = ref i2 in
    while true do
      let (i1',i2') = readintpair () in
      writetriple (i1',
                   log10(float_of_int (i2'-i2) +. 0.0),
                   log10(float_of_int (i2'- !i2'_prev) +. 0.0));
      i2'_prev := i2'
    done
  with
    End_of_file -> ()
