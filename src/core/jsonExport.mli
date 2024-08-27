(* the name of the file is meh, but `json` was already taken *)

val yojson_of_term : Term.term -> Yojson.Safe.t

(** export the json out of a trace sequent.

    I couldn't figure out how to make this a function that would be recognized
    by yojson. This is a problem for the caller to figure out. *)
val json_of_low_trace_sequent : LowTraceSequent.t -> Yojson.Safe.t