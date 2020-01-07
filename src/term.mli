open Vars

(** Terms for the Meta-BC logic.
  *
  * This module describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

(** {2 Timestamps} *)
(** Timestamps represent positions in a trace *)
type timestamp =
  | TVar of var
  | TPred of timestamp
  | TName of Symbols.action Symbols.t * Index.t list

val pp_timestamp : Format.formatter -> timestamp -> unit

val ts_vars : timestamp -> Vars.var list

(** {2 Symbols}
  *
  * We have function, name, state and macro symbols. Each symbol
  * can then be indexed.
  *
  * Names represent random values, uniformly sampled by the process.
  * State symbols represent memory cells.
  * Macros represent input, outputs, and let definitions:
  * everything that is expansed when translating the meta-logic to
  * the base logic.
  * TODO merge states into macros *)

(** Type of indexed symbols in some namespace *)
type 'a indexed_symbol = 'a Symbols.t * Index.t list

type name = Symbols.name Symbols.t
type nsymb = Symbols.name indexed_symbol

type kind = Vars.sort

type fname = Symbols.fname Symbols.t
type fsymb = Symbols.fname indexed_symbol

type mname = Symbols.macro Symbols.t
type msymb = Symbols.macro indexed_symbol

type state = msymb

(** Type of terms *)
type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | MVar of var
  | Macro of msymb * term list * timestamp

(** Pretty printing *)

val pp_name : Format.formatter -> name -> unit
val pp_nsymb : Format.formatter -> nsymb -> unit

val pp_fname : Format.formatter -> fname -> unit
val pp_fsymb : Format.formatter -> fsymb -> unit

val pp_mname :  Format.formatter -> mname -> unit
val pp_msymb :  Format.formatter -> msymb -> unit

(** {2 Terms} *)

(** [term_vars t] returns the variables of [t]*)
val term_vars : term -> var list

(** [term_ts t] returns the timestamps appearing in [t].
  * The returned list is guaranteed to have no duplicate elements. *)
val term_ts : term -> timestamp list

(** [precise_ts t] returns a list [l] of timestamps such that
  * any term that appears in [(t)^I] that is not an attacker
  * symbol or a frame must appear in a macro applied to a timestamp
  * that is less than [sigma_T(ts)] for some [ts] in [l].
  * Concretely, this is achieved by taking the timestamps occurring
  * in [t] but only the predecessors of timestamps occurring as
  * input timestamps. *)
val precise_ts : term -> timestamp list

val pp_term : Format.formatter -> term -> unit

(** {2 Substitutions} *)

(** Substitutions for all purpose, applicable to terms and timestamps.
  * Substitutions are performed bottom to top to avoid loops. *)

type asubst =
  | Term of term * term
  | TS of timestamp * timestamp
  | Index of Index.t * Index.t

type subst = asubst list

val to_isubst : subst ->  (var * var) list

(** From the type of the varibles, creates the corresponding substitution. *)
val from_varsubst : (var * var) list -> subst

val pp_subst : Format.formatter -> subst -> unit

val get_index_subst : subst -> Index.t -> Index.t

val subst_index : subst -> Index.t -> Index.t
val subst_ts : subst -> timestamp -> timestamp
val subst_macro : subst -> msymb -> msymb
val subst_term : subst -> term -> term

(** {2 Predefined symbols} *)

val dummy : term

val in_macro : msymb
val out_macro : msymb

val f_true : fsymb
val f_false : fsymb
val f_and : fsymb
val f_or : fsymb
val f_not : fsymb
val f_ite : fsymb

val f_pred : fsymb
val f_succ : fsymb

val f_xor : fsymb
val f_zero : fsymb

val f_pair : fsymb
val f_fst : fsymb
val f_snd : fsymb
