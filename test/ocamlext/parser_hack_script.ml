open Str;;
open Sys;;
open Unix;;

exception Fatal of string;;

let _ =
  (* Accept filename from commandline *)
  let filename =
    let len = Array.length argv in
    if(len < 2) then
      raise(Fatal("Incorrect arguments: must specify a filename "))
    else
      Array.get argv 1
  in

  (* Deduce name of ml and mli file *)
  let mlname = String.concat "" [filename; ".ml"] in
  let mliname = String.concat "" [filename; ".mli"] in

  (* Create an input channel for the ml file *)
  let ml_fd = openfile mlname [O_RDONLY] 0 in
  let ml_ch = in_channel_of_descr ml_fd in
  let ml_len = in_channel_length ml_ch in
  let ml_str = String.create ml_len in

  (* Create an input channel for the mli file *)
  let mli_fd = openfile mliname [O_RDONLY] 0 in
  let mli_ch = in_channel_of_descr mli_fd in
  let mli_len = in_channel_length mli_ch in
  let mli_str = String.create mli_len in

  (* Input both the ml and mli file into a string buffer *)
  let _ = really_input ml_ch ml_str 0 ml_len in
  let _ = really_input mli_ch mli_str 0 mli_len in

  (* Do the some global search and replaces *)
  let ml_str = global_replace (regexp "Parsing") "Threadparsing" ml_str in
  let ml_str = global_replace (regexp "let main") "let main (env : Threadparsing.env)" ml_str in
  let ml_str = global_replace (regexp "let spec3main") "let spec3main (env : Threadparsing.env)" ml_str in
  let ml_str = global_replace (regexp "yyparse") "yyparse env" ml_str in

  let mli_str = global_replace (regexp "Parsing") "Threadparsing" mli_str in
  let mli_str = global_replace (regexp "val main :") "val main : Threadparsing.env ->" mli_str in
  let mli_str = global_replace (regexp "val spec3main :") "val spec3main : Threadparsing.env ->" mli_str in

  let _ = close ml_fd in
  let _ = close mli_fd in

  (* Write the modified files back out *)
  let ml_fd = openfile mlname [O_APPEND; O_WRONLY; O_TRUNC] 0o664 in
  let mli_fd = openfile mliname [O_APPEND; O_WRONLY; O_TRUNC] 0o664 in
  let ml_ch = out_channel_of_descr ml_fd in
  let mli_ch = out_channel_of_descr mli_fd in
  let _ = output ml_ch ml_str 0 (String.length ml_str) in
  let _ = output mli_ch mli_str 0 (String.length mli_str) in
  prerr_string "Parser hacked successfully!\n";;
