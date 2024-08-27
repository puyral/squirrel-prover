(* the name of the file is meh, but `json` was already taken *)

val yojson_of_term : Term.term -> Yojson.Safe.t

val json_of_low_trace_sequent : LowTraceSequent.t -> Yojson.Safe.t