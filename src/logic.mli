(** Logic instantiates three modules, to capture proofs contexts:
    - Gamma contains a set of facts
    - Theta contains a set of constraints
    - Judgment is a goal inside a context, i.e a Gamma and a Theta *)
open Term

(** Tags used to record some information on gamma elements:
    - [euf] records whether the EUF axiom has been applied. *)
type tag = { t_euf : bool; cpt : int }

val cpt_tag : int ref

val set_euf : bool -> tag -> tag

(** Gamma represent the current proved equalities or disequalities regarding
    messages *)
module Gamma : sig
  type gamma

  val pp_gamma : Format.formatter -> gamma -> unit

  val mk : unit -> gamma

  val add_facts : gamma -> fact list -> gamma

  val get_facts : gamma -> fact list
  val set_facts : gamma -> fact list -> gamma

  val get_atoms : gamma -> atom list

  val update_trs : gamma -> gamma

  val get_trs : gamma -> Completion.state

  (** [is_sat g] returns [False] if [g] is inconsistent, and [True]
      otherwise. *)
  val is_sat : gamma -> bool

  (** [select g f f_up] returns the pair [(g',at)] where [at] is such that
      [f at tag] is true (where [tag] is the tag of [at] in [g]), and [at]'s
      tag has been updated in [g] according to [f_up].
      Raise [Not_found] if no such element exists. *)
  val select : gamma -> (atom -> tag -> bool) -> (tag -> tag) -> gamma * atom

  val add_descr : gamma -> Process.descr -> gamma

  (** [get_all_terms g] provides the list of all terms appearing inside
      atoms or facts of the [g]. *)
  val get_all_terms :gamma -> Term.term list

end

(** Store the constraints. We remember the last models that was computed,
    potentially on a less restricted constraint.
    We should guarrantee that TODO (give the invariant on models and queries) *)
module Theta : sig
  type theta

  val pp_theta : Format.formatter -> theta -> unit

  val mk : constr -> theta

  val add_constr : theta -> constr -> theta

  val is_sat : theta -> bool

  val is_valid : theta -> tatom list -> bool

  (** [maximal_elems theta elems] returns an over-approximation of the set of
      maximals elements of [elems] in [theta]. *)
  val maximal_elems : theta -> timestamp list -> timestamp list

  val get_equalities : theta -> timestamp list list
end

type typed_formula =
  | Unit
  | Formula of formula
  | Postcond of postcond
  | Fact of fact

(** Judgments are the sequents of our proof system *)
module Judgment : sig
  type judgment = { vars : fvar list;
                    theta : Theta.theta;
                    gamma : Gamma.gamma;
                    formula : typed_formula; }

  type t = judgment

  val pp_judgment : Format.formatter -> judgment -> unit

  val init : formula -> judgment

  val add_vars : Term.fvar list -> judgment -> judgment
  val add_indices : Action.index list -> judgment -> judgment

  (** Side-effect: Add necessary action descriptions. *)
  val add_fact : Term.fact -> judgment -> judgment

  (** Side-effect: Add necessary action descriptions. *)
  val add_constr : Term.constr -> judgment -> judgment

  val update_trs : judgment -> judgment

  val set_formula : typed_formula -> judgment -> judgment

  val set_gamma : Gamma.gamma -> judgment ->  judgment

end
