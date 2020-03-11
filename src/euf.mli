(** Module for the euf axiom application *)

(** Type of an euf axiom case schema.
    [e] of type [euf_schema] represents the fact that the message [e.message]
    has been hashed.
    [e.action_descr] stores the relevant action description for future use,
    with fresh indices where relevant (i.e. for indices other than the
    key's indices).  *)
type euf_schema = { message : Term.message;
                    action_descr : Action.descr;
                    env : Vars.env }


val pp_euf_schema : Format.formatter -> euf_schema -> unit


(** Type of a direct euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices]. *)
type euf_direct = { d_key_indices : Vars.index list;
                    d_message : Term.message }

val pp_euf_direct : Format.formatter -> euf_direct -> unit

(** Type of an euf axiom rule:
    - [hash] stores the hash function name.
    - [key] stores the key considered in this rule.
    - [case_schemata] is the list (seen as a disjunction) of case schemata.
    - [cases_direct] is the list (seen as a disjunction) of direct cases. *)
type euf_rule = { hash : Term.fname;
                  key : Term.name;
                  case_schemata : euf_schema list;
                  cases_direct : euf_direct list }

val pp_euf_rule : Format.formatter -> euf_rule -> unit

(** Exception thrown when the axiom syntactic side-conditions do not hold. *)
exception Bad_ssc

(** Returns true if the syntactic side condition of the key is met inside the
    protocol and the messages. *)
val hash_key_ssc :
  system:Action.system ->
  Term.fname -> Term.name -> Term.message list -> bool

(** [mk_rule proc hash_fn key_n] create the euf rule associated to an given
    hash function and key in a process.
    TODO: memoisation *)
val mk_rule :
  system:Action.system ->
  env:Vars.env -> mess:Term.message -> sign:Term.message ->
  hash_fn:Term.fname -> key_n:Term.name -> key_is:Vars.index list -> euf_rule
