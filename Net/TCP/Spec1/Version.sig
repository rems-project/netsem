signature Version = sig

  val register : string -> string -> string -> unit
  val registerTheory : string -> string -> string -> unit
  val get : unit -> (string * string * string) list
  val getString : unit -> string
  val getTable : unit -> string

end;
