
type platform =
    WIN32
  | LINUX
  | BSD
  | UNKNOWN;;

val check_platform: unit -> platform
val gethostname: unit -> string
val gettimeofday: unit -> string
val getdecenttimeofday: unit -> int64

val getpty: unit -> Unix.file_descr * Unix.file_descr

(* Binding of POSIX threads pthread_cond_timedwait
     (absolute deadline, time since epoch) *)
val condition_abs_timedwait: Condition.t -> Mutex.t -> float -> unit

(* Alternate binding of POSIX threads pthread_cond_timedwait
     (relative deadline, time to wait) *)
val condition_rel_timedwait: Condition.t -> Mutex.t -> float -> unit

val win32_terminate_process: int -> int -> unit

val win32_in_channel_of_descr: Unix.file_descr -> int * in_channel

val win32_free_open_handle: int -> unit