(** Indices are used to generate arbitrary families of terms *)
type index
type indices = index list

val pp_index : Format.formatter -> index -> unit
val pp_indices : Format.formatter -> indices -> unit

val fresh_index : unit -> index


type 'a item = {
  par_choice : int * 'a list ;
  sum_choice : int
}
type 'a t = ('a item) list

val conflict : 'a t -> 'a t -> bool

val depends : 'a t -> 'a t -> bool

val enables : 'a t -> 'a t -> bool

type action_shape = string item list

type action = (string*index) item list

val mk_shape : string item list -> action_shape

(** This is for testing, it should never be necessary in the actual code. *)
val mk_action : (string * index) item list -> action

val get_shape : action -> action_shape

val action_indices : action -> indices

(** [same_shape a b] returns [Some subst] if [a] and [b] have the same action
    shapes. Return [None] otherwise.
    If [a] indices appear at most once in [a], then [subst] is the index
    substitution sending [a] to [b]. *)
val same_shape : action -> action -> (index * index) list option

(** [constr_equal a b] returns the list of index constraints necessary to have
    [a] and [b] equal, if there is one. Return None otherwise. *)
val constr_equal : action -> action -> (index * index) list option

type 'a subst = ('a * 'a) list

val app_subst : ('a * 'a) list -> 'a -> 'a

val ivar_subst_action : index subst -> action -> action

(** Given an action, generate a fresh instance of it together with
  * the corresponding substitution for indices. *)
val refresh : action -> action * index subst

val pp_action : Format.formatter -> action -> unit

val pp_shape : Format.formatter -> action -> unit

val pp_action_shape : Format.formatter -> action_shape -> unit
