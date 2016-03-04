signature TraceFiles =
sig
  include Abbrev
  val host_and_labels_from_file : string -> term * term list
end
