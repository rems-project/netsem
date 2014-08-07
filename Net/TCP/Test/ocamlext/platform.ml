type platform =
    WIN32
  | LINUX
  | BSD
  | UNKNOWN;;

external check_platform: unit -> platform = "c_check_platform"

external gethostname: unit -> string = "c_gethostname"

external gettimeofday: unit -> string = "c_gettimeofday"

external getdecenttimeofday_helper: unit -> (int * int) = "c_getdecenttimeofday"

let getdecenttimeofday () =
  let ts,tus = getdecenttimeofday_helper () in
  let ts,tus = Int64.of_int ts, Int64.of_int tus in
  Int64.add (Int64.mul ts (Int64.of_int 1000000)) tus;;

external getpty: unit -> Unix.file_descr * Unix.file_descr = "getpty"

external condition_abs_timedwait:
  Condition.t -> Mutex.t -> float -> unit
  = "c_condition_rel_timedwait"

external condition_rel_timedwait:
  Condition.t -> Mutex.t -> float -> unit
  = "c_condition_rel_timedwait"

external win32_terminate_process: int -> int -> unit = "c_win32_terminate_process"

external win32_open_read_descriptor: int -> in_channel = "caml_open_descriptor_in"

external win32_open_handle: Unix.file_descr -> int = "c_win32_open_handle"

let win32_in_channel_of_descr handle =
  let hnd = win32_open_handle handle in
  (hnd, win32_open_read_descriptor(hnd));;

external win32_free_open_handle: int -> unit = "c_win32_free_open_handle"

