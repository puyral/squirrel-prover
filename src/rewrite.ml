open Utils

module Args = TacticsArgs
module SE   = SystemExpr

(*------------------------------------------------------------------*)
(** A rewrite rule.
    Invariant: if
    [{ rw_tyvars = tyvars; rw_vars = sv; rw_conds = φ; rw_rw = (l,r); }]
    is a rewrite rule, then:
    - sv ⊆ FV(l)
    - ((FV(r) ∪ FV(φ)) ∩ sv) ⊆ FV(l) *)
type rw_erule = {
  rw_tyvars : Type.tvars;        (** type variables *)
  rw_vars   : Vars.Sv.t;         (** term variables *)
  rw_conds  : Term.term list; (** premisses *)
  rw_rw     : Term.esubst;       (** pair (source, destination) *)
}

(*------------------------------------------------------------------*)
(** Check that the rule is correct. *)
let check_erule (rule : rw_erule) : unit =
  let Term.ESubst (l, r) = rule.rw_rw in
  let fvl, fvr = Term.fv l, Term.fv r in
  let sh = List.fold_left (fun sh h ->
      Vars.Sv.union sh (Term.fv h)
    ) Vars.Sv.empty rule.rw_conds
  in

  if not (Vars.Sv.subset rule.rw_vars fvl) ||
     not (Vars.Sv.subset
            (Vars.Sv.inter (Vars.Sv.union fvr sh) rule.rw_vars)
            fvl) then
    Tactics.hard_failure Tactics.BadRewriteRule;
  ()

(** Make a rewrite rule from a formula *)
let pat_to_rw_erule ?loc dir (p : Term.term Match.pat) : rw_erule =
  let subs, f = Term.decompose_impls_last p.pat_term in

  let e = match f with
    | Term.Atom (`Message   (`Eq, t1, t2)) -> Term.ESubst (t1,t2)
    | Term.Atom (`Timestamp (`Eq, t1, t2)) -> Term.ESubst (t1,t2)
    | Term.Atom (`Index     (`Eq, t1, t2)) ->
      Term.ESubst (Term.mk_var t1,Term.mk_var t2)
    | _ -> Tactics.hard_failure ?loc (Tactics.Failure "not an equality")
  in

  let e = match dir with
    | `LeftToRight -> e
    | `RightToLeft ->
      let Term.ESubst (t1,t2) = e in
      Term.ESubst (t2,t1)
  in

  let rule = {
    rw_tyvars = p.pat_tyvars;
    rw_vars   = p.pat_vars;
    rw_conds  = subs;
    rw_rw     = e;
  } in

  (* We check that the rule is valid *)
  check_erule rule;

  rule

(*------------------------------------------------------------------*)
exception NoRW

let _rewrite_head
    (table  : Symbols.table)
    (system : SE.t)
    (rule   : rw_erule)
    (t      : Term.term) : Term.term * Term.term list
  =
  let (l, r) : Term.term * Term.term =
    match rule.rw_rw with
    | Term.ESubst (l, r) ->
      if not (Term.kind t = Term.kind l) then raise NoRW;

      l, r
  in

  let pat =
    Match.{ pat_tyvars = rule.rw_tyvars; pat_vars = rule.rw_vars; pat_term = l; }
  in

  let mv =
    match Match.T.try_match table system t pat with
    | FreeTyv | NoMatch _ -> raise NoRW
    | Match mv -> mv
  in
  let subst = Match.Mvar.to_subst ~mode:`Match mv in
  let r = Term.subst subst r in
  let subs = List.map (Term.subst subst) rule.rw_conds in
  r, subs

let rewrite_head
    (table  : Symbols.table)
    (system : SE.t)
    (rule   : rw_erule)
    (t      : Term.term) : (Term.term * Term.term list) option
  =
  if not (Term.kind t = Type.KMessage) then 
    None
  else
    try Some (_rewrite_head table system rule t) with NoRW -> None

(*------------------------------------------------------------------*)
  type rw_res = [
    | `Result of Equiv.any_form * Term.term list
    | `NothingToRewrite
    | `MaxNestedRewriting
  ]

(*------------------------------------------------------------------*)
(** A opened rewrite rule. Not exported. *)
type rw_rule =
  Type.tvars * Vars.Sv.t * Term.term list * Term.term * Term.term

(*------------------------------------------------------------------*)
let rewrite
    (table  : Symbols.table)
    (system : SE.t)
    (env    : Vars.env)
    (mult   : Args.rw_count)
    (rule   : rw_erule)
    (target : Equiv.any_form) : rw_res
  =
  let exception Failed of [`NothingToRewrite | `MaxNestedRewriting] in

  let check_max_rewriting : unit -> unit =
    let cpt_occ = ref 0 in
    fun () ->
      if !cpt_occ > 1000 then   (* hard-coded *)
        raise (Failed `MaxNestedRewriting);
      incr cpt_occ;
  in

  (* Attempt to find an instance of [left], and rewrites all occurrences of
     this instance.
     Return: (f, subs) *)
  let rec _rewrite : 
    Args.rw_count ->
    rw_rule ->
    Equiv.any_form ->
    Equiv.any_form * Term.term list
    = fun mult (tyvars, sv, rsubs, left, right) f ->
      check_max_rewriting ();

      let subs_r = ref [] in
      let found_instance = ref false in

      (* This is a reference, so that it can be over-written later
         after we found an instance of [left]. *)
      let pat : Term.term Match.pat ref =
        ref Match.{ pat_tyvars = tyvars; pat_vars = sv; pat_term = left }
      in
      let right_instance = ref None in

      (* If there is a match (with [mv]), substitute [occ] by [right] where
         free variables are instantiated according to [mv], and variables
         bound above the matched occurrences are universally quantified in
         the generated sub-goals. *)
      let rw_inst occ vars conds =
        match Match.T.try_match table system occ !pat with
        | NoMatch _ | FreeTyv -> `Continue

        (* head matches *)
        | Match mv ->
          if !found_instance then
            (* we already found the rewrite instance earlier *)
            `Map (oget !right_instance)

          else begin (* we found the rewrite instance *)
            found_instance := true;
            let subst = Match.Mvar.to_subst ~mode:`Match mv in
            let left = Term.subst subst left in
            let right = Term.subst subst right in

            right_instance := Some right;
            subs_r :=
              List.map (fun rsub ->
                  Term.mk_forall ~simpl:true vars (Term.subst subst rsub)
                ) rsubs;

            pat := Match.{ pat_term   = left;
                           pat_tyvars = [];
                           pat_vars   = Sv.empty; };

            `Map right
          end
      in

      let f_opt = match f with
        | `Equiv f ->
          let f_opt = Match.E.map rw_inst env f in
          omap (fun x -> `Equiv x) f_opt

        | `Reach f ->
          let f_opt = Match.T.map rw_inst env f in
          omap (fun x -> `Reach x) f_opt
      in

      match mult, f_opt with
      | `Any, None -> f, !subs_r

      | (`Once | `Many), None -> raise (Failed `NothingToRewrite)

      | (`Many | `Any), Some f ->
        let f, rsubs' = _rewrite `Any (tyvars, sv, rsubs, left, right) f in
        f, List.rev_append (!subs_r) rsubs'

      | `Once, Some f -> f, !subs_r
  in

  let Term.ESubst (l,r) = rule.rw_rw in
  match
    _rewrite mult (rule.rw_tyvars, rule.rw_vars, rule.rw_conds, l, r) target
  with
  | f, subs                                -> `Result (f, List.rev subs)
  | exception Failed (`NothingToRewrite)   -> `NothingToRewrite
  | exception Failed (`MaxNestedRewriting) -> `MaxNestedRewriting
