(** {2 Macro definitions} *)

(** Declare a global (timestamp-dependent) macro,
  * given a term abstracted over input variables, indices,
  * and some timestamp.
  * A fresh name is generated for the macro if needed. *)
val declare_global :
  string ->
  inputs:Vars.var list ->
  indices:Index.t list ->
  ts:Vars.var ->
  Term.term -> Symbols.macro Symbols.t

(** {2 Macro expansions} *)

(** Tells whether a macro symbol can be expanded when applied
  * at a particular timestamp. *)
val is_defined : Symbols.macro Symbols.t -> Term.timestamp -> bool

(** Return the term corresponding to the declared macro,
  * if the macro can be expanded. *)
val get_definition :
  Symbols.macro Symbols.t -> Index.t list -> Term.timestamp -> Term.term

(** When [m] is a global macro symbol,
  * [get_definition m li] return a term which resembles the one that
  * would be obtained with [get_definition m li ts] for some [ts],
  * except that it will feature meaningless action names in some places. *)
val get_dummy_definition :
  Symbols.macro Symbols.t -> Index.t list -> Term.term
