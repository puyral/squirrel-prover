(** All reachability tactics.
   Tactics are organized in three classes:
    - Logical -> relies on the logical properties of the sequent.
    - Structural -> relies on properties of protocols, or of equality over
      messages,...
    - Cryptographic -> relies on a cryptographic assumptions, that must be
      assumed.
*)

open Term
open Utils

module T    = Prover.ProverTactics
module Args = HighTacticsArgs
module L    = Location
module SE   = SystemExpr

module TS = TraceSequent

module Hyps = TS.LocalHyps

type tac = TS.t Tactics.tac
type lsymb = Theory.lsymb
type sequent = TS.sequent

module Sp = Match.Pos.Sp
              
(*------------------------------------------------------------------*)
open LowTactics

(*------------------------------------------------------------------*)
let wrap_fail = TraceLT.wrap_fail

let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** {2 Logical Tactics} *)

(** Propositional connectives *)

let goal_or_right_1 (s : TS.t) =
  match Term.destr_or (TS.goal s) with
  | Some (lformula, _) -> [TS.set_goal (lformula) s]
  | None -> soft_failure (Tactics.Failure "not a disjunction")

let goal_or_right_2 (s : TS.t) =
  match Term.destr_or (TS.goal s) with
  | Some (_, rformula) -> [TS.set_goal (rformula) s]
  | None -> soft_failure (Tactics.Failure "not a disjunction")

let () =
  T.register "left"
    ~tactic_help:{general_help = "Reduce a goal with a disjunction conclusion \
                                  into the goal where the conclusion has been \
                                  replaced with the first disjunct.";
                  detailed_help = "G => A v B yields G => A";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun goal_or_right_1)

let () =
  T.register "right"
    ~tactic_help:{general_help = "Reduce a goal with a disjunction conclusion \
                                  into the goal where the conclusion has been \
                                  replace with the second disjunct.";
                  detailed_help = "G => A v B yields G => B";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun goal_or_right_2)

(*------------------------------------------------------------------*)
let goal_true_intro (s : TS.t) =
  match TS.goal s with
  | tt when tt = Term.mk_true -> []
  | _ -> soft_failure (Tactics.Failure "Cannot introduce true")

let () =
  T.register "true"
     ~tactic_help:{general_help = "Solves a goal when the conclusion is true.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                   tactic_group = Logical}
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun goal_true_intro)


(*------------------------------------------------------------------*)
let left_not_intro (Args.String hyp_name) s =
  let id, formula = Hyps.by_name hyp_name s in
  let s = Hyps.remove id s in
  match Term.destr_not formula with
  | Some f ->
    [Hyps.add (Args.Named (Ident.name id)) (Term.not_simpl f) s]

  | None -> soft_failure (Tactics.Failure "cannot introduce negation")

let () =
  T.register_typed "notleft"
    ~general_help:"Push a negation inside a formula."
    ~detailed_help:"Normalize the formula according to the negation rules over \
                    logical connectors."
    ~tactic_group:Logical
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg left_not_intro) Args.String

(*------------------------------------------------------------------*)
(** Case analysis on [orig = Find (vars,c,t,e)] in [s].
  * This can be used with [vars = []] if orig is an [if-then-else] term. *)
let case_cond orig vars c t e s : sequent list =
  let vars, subst = Term.refresh_vars `Global vars in
  let then_c = Term.subst subst c in
  let else_c = Term.mk_forall vars (Term.mk_not then_c) in

  let then_t = Term.subst subst t in
  let else_t = e in

  let mk_case case_vars case_t case_cond : sequent =
    let case_subst =
      if case_vars = [] then [Term.ESubst (orig, case_t)] else []
    in

    let prem =
      Term.mk_exists
        case_vars
        (Term.mk_and ~simpl:false
           case_cond
           (Term.mk_atom `Eq orig case_t))
    in

    let case_goal =
      Term.mk_impl ~simpl:false
        prem
        (Term.subst case_subst (TS.goal s))
    in
    TS.set_goal case_goal s
  in

  [ mk_case vars then_t then_c;
    mk_case    [] else_t else_c]

let conditional_case (m : Term.term) s : sequent list =
  match m with
  | Term.Find (vars,c,t,e) -> case_cond m vars c t e s
  | Term.Fun (f,_,[c;t;e]) when f = Term.f_ite ->
    case_cond m [] c t e s

  | Term.Macro (ms,[],ts) ->

    if not (TS.query_happens ~precise:true s ts) then
      soft_failure (Tactics.MustHappen ts);

    begin
      match Macros.get_definition_exn (TS.mk_trace_cntxt s) ms ts with
      | Term.Find (vars,c,t,e) -> case_cond m vars c t e s
      | Term.Fun (f,_,[c;t;e]) when f = Term.f_ite -> case_cond m [] c t e s
      | _ -> Tactics.(soft_failure (Failure "message is not a conditional"))
    end

  | _ ->
    Tactics.(soft_failure (Failure "message is not a conditional"))

let boolean_case b s : sequent list =
  let do_one b_case b_val =
    let g = Term.subst [Term.ESubst (b, b_val)] (TS.goal s) in
    TS.set_goal (Term.mk_impl ~simpl:false b_case g) s
  in
  [ do_one b Term.mk_true;
    do_one (Term.mk_not ~simpl:false b) Term.mk_false]

(* [ty] must be the type of [m] *)
let message_case (t : Term.term) ty s : sequent list =
  match ty with
  | Type.Boolean -> boolean_case t s
  | _ -> conditional_case t s

(*------------------------------------------------------------------*)
let do_case_tac (args : Args.parser_arg list) s : sequent list =
  match Args.convert_as_lsymb args with
  | Some str when Hyps.mem_name (L.unloc str) s ->
    let id, _ = Hyps.by_name str s in
    List.map
      (fun (TraceLT.CHyp _, ss) -> ss)
      (TraceLT.hypothesis_case ~nb:`Any id s)

  | _ ->
    match TraceLT.convert_args s args Args.(Sort Term) with
    | Args.Arg (Term (ty, f, _)) ->
      begin
        match ty with
        | Type.Timestamp -> TraceLT.timestamp_case f s
        | Type.Index -> bad_args ()
        | _ -> message_case f ty s
      end
    | _ -> bad_args ()


let case_tac args = wrap_fail (do_case_tac args)

(*------------------------------------------------------------------*)

let rec simpl_left s =
  let func _ f = match f with
    | Fun (fs, _,_) when fs = Term.f_false || fs = Term.f_and -> true
    | Term.Quant (Exists, _, _) -> true
    | _ -> false
  in

  match Hyps.find_opt func s with
  | None -> Some s
  | Some (id,f) ->
    match f with
    | tf when tf = Term.mk_false -> None

    | Quant (Exists,vs,f) ->
      let s = Hyps.remove id s in
      let env = ref @@ TS.vars s in
      let subst =
        List.map
          (fun v ->
             Term.ESubst  (Term.mk_var v,
                           Term.mk_var (Vars.make_approx_r env v)))
          vs
      in
      let f = Term.subst subst f in
      simpl_left (Hyps.add Args.AnyName f (TS.set_vars !env s))

    | _ as form ->
      let f, g = oget (Term.destr_and form) in
      let s = Hyps.remove id s in
      simpl_left (Hyps.add_list [(Args.AnyName, f); (Args.AnyName, g)] s)

let simpl_left_tac s = match simpl_left s with
  | None -> []
  | Some s -> [s]

(*------------------------------------------------------------------*)
(** [any_assumption s] succeeds (with no subgoal) if the sequent [s]
    can be proved using the axiom rule (plus some other minor rules). 
    If [hyp = Some id], only checks for hypothesis [id]. *)
let assumption ?hyp (s : TS.t) = 
  let goal = TS.goal s in
  let assumption_entails id f = 
    (hyp = None || hyp = Some id) &&
    match f with
    | Equiv.Global (Equiv.Atom (Reach f))
    | Equiv.Local f ->
      TS.Reduce.conv_term s goal f ||
      List.exists (fun f ->
          TS.Reduce.conv_term s goal f ||
          TS.Reduce.conv_term s f Term.mk_false
        ) (decompose_ands f)
    | Equiv.Global _ -> false
  in
  if goal = Term.mk_true ||
     TS.Hyps.exists assumption_entails s
  then begin
    dbg "assumption %a" Term.pp goal;
    []
  end else soft_failure Tactics.NotHypothesis

let do_assumption_tac args s : TS.t list =
  let hyp =
    match Args.convert_as_lsymb args with
    | Some str -> Some (fst (Hyps.by_name str s))
    | None -> None 
  in
  assumption ?hyp s

let assumption_tac args = wrap_fail (do_assumption_tac args)

(*------------------------------------------------------------------*)
(** [localize h h' s sk fk] succeeds with a single subgoal if
    the sequent [s] has a global hypothesis [h] which is a reachability
    atom.
    The generated subgoal is identical to [s] but with a new local
    hypothesis [h'] corresponding to that atom. *)
let localize h h' s =
  match TS.Hyps.by_name h s with
    | _,Global (Equiv.Atom (Reach f)) ->
        [TS.Hyps.add h' (Local f) s]
    | _ ->
        Tactics.(soft_failure (Failure "cannot localize this hypothesis"))
    | exception Not_found ->
        Tactics.(soft_failure (Failure "no hypothesis"))

let () =
  T.register_general "localize"
    ~tactic_help:
      {general_help = "Change a global hypothesis containing a reachability \
                       formula to a local hypothesis.";
       detailed_help = "";
       usages_sorts = [Sort (Pair (String, String))];
       tactic_group = Logical}
    ~pq_sound:true
    (function
       | TacticsArgs.[String_name h; NamingPat h'] ->
           fun s sk fk ->
             begin match LowTactics.genfun_of_pure_tfun (localize h h') s with
               | subgoals -> sk subgoals fk
               | exception (Tactics.Tactic_soft_failure e) -> fk e
             end
       | _ -> assert false)

(*------------------------------------------------------------------*)
(** {2 Structural Tactics} *)

(*------------------------------------------------------------------*)
(** [congruence judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
let congruence (s : TS.t) : bool =
  match simpl_left s with
  | None -> true
  | Some s ->
    let conclusions =
      Utils.odflt [] (Term.disjunction_to_literals (TS.goal s))
    in

    let term_conclusions =
      List.fold_left (fun acc conc -> 
          lit_to_form (neg_lit conc) :: acc
        ) [] conclusions
    in
    let s = List.fold_left (fun s f ->
        Hyps.add Args.Unnamed f s
      ) s term_conclusions
    in
    TS.eq_atoms_valid s

(** [constraints s] proves the sequent using its trace formulas. *)
let congruence_tac (s : TS.t) =
  match congruence s with
  | true ->
    let () = dbg "closed by congruence" in
    []

  | false ->
    let () = dbg "congruence failed" in
    soft_failure Tactics.CongrFail

let () =
  T.register "congruence"
    ~tactic_help:
      {general_help = "Tries to derive false from the messages equalities.";
       detailed_help = "It relies on the reflexivity, transitivity \
                        and stability by function application \
                        (f(u)=f(v) <=> u=v).";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun congruence_tac)

(*------------------------------------------------------------------*)
let constraints (s : TS.t) =
  match simpl_left s with
  | None -> true
  | Some s ->
    let conclusions =
      Utils.odflt [] (Term.disjunction_to_literals (TS.goal s))
    in
    let trace_conclusions =
      List.fold_left (fun acc conc -> 
          let keep = match conc with 
            | _, `Happens _ -> true
            | _, `Comp (_, t, _) ->
              Term.ty t = Type.Timestamp || Term.ty t = Type.Index
          in
          if keep then
            lit_to_form (neg_lit conc) :: acc
          else 
            acc
        ) [] conclusions
    in
    let s = List.fold_left (fun s f ->
        Hyps.add Args.Unnamed f s
      ) s trace_conclusions
    in
    TS.constraints_valid s

(** [constraints s] proves the sequent using its trace formulas. *)
let constraints_tac (s : TS.t) =
  let s = as_seq1 (TraceLT.intro_all s) in
  match constraints s with
  | true ->
    let () = dbg "closed by constraints" in
    []

  | false ->
   let () = dbg "constraints failed" in
   soft_failure (Tactics.Failure "constraints satisfiable")

let () = T.register "constraints"
    ~tactic_help:
      {general_help = "Tries to derive false from the trace formulas.";
       detailed_help = "From ordering constraints on the timestamps, \
                        checks that we can build an acyclic graph on \
                        them, i.e., if they are a possible trace.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun constraints_tac)

(*------------------------------------------------------------------*)
(* SMT-based combination of constraints and congruence *)

let smt (s : TS.t) =
  (* let's avoid massaging the goal beforehand
   * so that we can send it as it is to the SMT solver
   * (in the current implementation, the goal is preserved while
   *  only the trace literals and equality atoms are sent among the hypotheses)
   * NOTE: this means that in principle this will sometimes be less powerful
   *       than calling constraints/congruence *)
  (* match simpl_left s with
   * | None -> true
   * | Some s ->
   *   let conclusions =
   *     Utils.odflt [] (Term.disjunction_to_literals (TS.goal s))
   *   in
   *   let term_conclusions =
   *     List.fold_left (fun acc conc -> match conc with
   *         | `Pos, (#generic_atom as at) ->
   *           let at = (at :> Term.generic_atom) in
   *           Term.(mk_not (mk_atom1 at)) :: acc
   *         | `Neg, (#generic_atom as at) ->
   *           Term.mk_atom1 at :: acc)
   *       []
   *       conclusions
   *   in
   *   let s = List.fold_left (fun s f ->
   *       Hyps.add Args.AnyName f s
   *     ) s term_conclusions
   *   in *)
    TS.literals_unsat_smt s

let smt_tac (s : TS.t) =
  (* let s = as_seq1 (TraceLT.intro_all s) in *)
  match smt s with
  | true ->
    let () = dbg "closed by smt" in
    []

  | false ->
   let () = dbg "smt failed" in
   soft_failure (Tactics.Failure "smt did not return unsat")

let () = T.register "smt"
    ~tactic_help:
      {general_help = "Tries to discharge goal using an SMT solver.";
       detailed_help = "implements a combination of congruence, constraints, \
                        eqnames and macroexpansion, plus first-order reasoning";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    (LowTactics.genfun_of_pure_tfun smt_tac)

let slowsmt_tac (s : TS.t) =
  match TS.literals_unsat_smt ~slow:true s with
  | true ->
    let () = dbg "closed by smt" in
    []

  | false ->
   let () = dbg "smt failed" in
   soft_failure (Tactics.Failure "smt did not return unsat")

let () = T.register "slowsmt"
    ~tactic_help:
      {general_help = "Version of smt tactic with higher time limit.";
       detailed_help = "";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    (LowTactics.genfun_of_pure_tfun slowsmt_tac)



(*------------------------------------------------------------------*)
(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

(** Add index constraints resulting from names equalities, modulo the TRS.
    The judgment must have been completed before calling [eq_names]. *)
let eq_names (s : TS.t) =
  let table = TS.table s in

  (* we now collect equalities between timestamp implied by equalities between
     names. *)
  let trs = TS.get_trs s in
  let cnstrs =
    Completion.name_index_cnstrs table trs (TS.get_all_messages s)
  in
  let s =
    List.fold_left (fun s c ->
        let () = dbg "new equalities (names): %a" Term.pp c in
        Hyps.add Args.Unnamed c s
      ) s cnstrs
  in
  [s]

let () = T.register "eqnames"
    ~tactic_help:
      {general_help = "Add index constraints resulting from names equalities, \
                       modulo the known equalities.";
       detailed_help = "If n[i] = n[j] then i = j. \
                        This is checked on all name equality entailed \
                        by the current context.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun eq_names)

(*------------------------------------------------------------------*)
(** Add terms constraints resulting from timestamp and index equalities. *)
let eq_trace (s : TS.t) =
  let ts_classes = TS.get_ts_equalities ~precise:false s
  in
  let ts_classes = List.map (List.sort_uniq Stdlib.compare) ts_classes in
  let ts_subst =
    let rec asubst e = function
        [] -> []
      | p::q -> Term.ESubst (p,e) :: (asubst e q)
    in
    List.map (function [] -> [] | p::q -> asubst p q) ts_classes
    |> List.flatten
  in
  let ind_classes = TS.get_ind_equalities ~precise:false s
  in
  let ind_classes = List.map (List.sort_uniq Stdlib.compare) ind_classes in
  let ind_subst =
    let rec asubst e = function
        [] -> []
      | p::q -> Term.ESubst (Term.mk_var p,Term.mk_var e) :: (asubst e q)
    in
    (List.map (function [] -> [] | p::q -> asubst p q) ind_classes)
    |> List.flatten
  in
  let terms = TS.get_all_messages s in
  let facts =
    List.fold_left
      (fun acc t ->
         let normt : Term.term = Term.subst (ts_subst @ ind_subst) t in
         if normt = t
         then acc
         else Term.mk_atom `Eq t normt ::acc)
      [] terms
  in
  let s =
    List.fold_left (fun s c ->
        let () = dbg "new trace equality: %a" Term.pp c in
        Hyps.add Args.Unnamed c s
      ) s facts
  in
  [s]

let () = T.register "eqtrace"
    ~tactic_help:
      {general_help = "Add terms constraints resulting from timestamp \
                       and index equalities.";
       detailed_help = "Whenver i=j or ts=ts', we can substitute one \
                        by another in the other terms.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun eq_trace)


(*------------------------------------------------------------------*)
(* no longer used for fresh. 
   left here temporarily, for compatibility *)
(** triple of the action and the name indices *)
type deprecated_fresh_occ = (Action.action * Vars.var list) Iter.occ

(** check if all instances of [o1] are instances of [o2].
    [o1] and [o2] actions must have the same action name *)
let deprecated_fresh_occ_incl table system (o1 : deprecated_fresh_occ) (o2 : deprecated_fresh_occ) : bool =
  (* for now, positions not allowed here *)
  assert (Sp.is_empty o1.occ_pos && Sp.is_empty o2.occ_pos);
  
  let a1, is1 = o1.occ_cnt in
  let a2, is2 = o2.occ_cnt in

  let cond1 = Term.mk_ands (List.rev o1.occ_cond)
  and cond2 = Term.mk_ands (List.rev o2.occ_cond) in

  (* build a dummy term, which we used to match in one go all elements of
     the two occurrences *)
  let mk_dum a is cond =
    let action = SE.action_to_term table system a in
    Term.mk_ands ~simpl:false
      ((Term.mk_atom `Eq Term.init action) ::
       (Term.mk_indices_eq ~simpl:false is is) ::
       [cond])
  in
  let pat2 = Term.{
      pat_tyvars = [];
      pat_vars   = Sv.of_list o2.occ_vars;
      pat_term   = mk_dum a2 is2 cond2;
    }
  in

  let context = SE.reachability_context system in
  match Match.T.try_match table context (mk_dum a1 is1 cond1) pat2 with
  | Match.FreeTyv | Match.NoMatch _ -> false
  | Match.Match _ -> true

(** Add a new fresh rule case, if it is not redundant. *)
let deprecated_add_fresh_case
    table system
    (c : deprecated_fresh_occ)
    (l : deprecated_fresh_occ list) : deprecated_fresh_occ list
  =
  if List.exists (fun c' -> deprecated_fresh_occ_incl table system c c') l
  then l
  else
    (* remove any old case which is subsumed by [c] *)
    let l' =
      List.filter (fun c' ->
          not (deprecated_fresh_occ_incl table system c' c)
        ) l
    in
    c :: l'

(** Add many new fresh rule cases, if they are not redundant. *)
let deprecated_add_fresh_cases
    table system
    (l1 : deprecated_fresh_occ list)
    (l2 : deprecated_fresh_occ list) : deprecated_fresh_occ list
  =
  List.fold_left (fun l2 c -> deprecated_add_fresh_case table system c l2) l2 l1

(* Indirect cases - names ([n],[is']) appearing in actions of the system *)
let deprecated_mk_fresh_indirect_cases
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    (ns : Term.nsymb)
    (terms : Term.term list)
  =
  (* sanity check: free variables in [ns] and [terms] are included in [env] *)
  assert (
    let all_fv =
      List.fold_left (fun s t ->
          Sv.union s (Term.fv t)
        ) (Sv.of_list1 ns.Term.s_indices) terms
    in
    Sv.subset all_fv (Vars.to_set env));

  let macro_cases =
    Iter.fold_macro_support0 (fun action_name a t macro_cases ->
        let fv =
          Sv.diff
            (Sv.union (Action.fv_action a) (Term.fv t))
            (Vars.to_set env)
        in

        let new_cases =
          let fv = List.rev (Sv.elements fv) in
          OldFresh.deprecated_get_name_indices_ext ~fv cntxt ns.s_symb t
        in
        let new_cases =
          List.map (fun (case : OldFresh.deprecated_name_occ) ->
              { case with
                occ_cnt = (a, case.occ_cnt);
                occ_cond = case.occ_cond; }
            ) new_cases
        in

        List.assoc_up_dflt action_name []
          (fun l ->
             deprecated_add_fresh_cases cntxt.table cntxt.system new_cases l
          ) macro_cases
      ) cntxt env terms []
  in
  (* we keep only action names in which the name occurs *)
  List.filter (fun (_, occs) -> occs <> []) macro_cases




    
(*------------------------------------------------------------------*)
let apply_substitute subst s =
    let s =
    match subst with
      | Term.ESubst (Term.Var v, t) :: _ when
        not (List.mem v (Term.get_vars t)) ->
          TS.set_vars (Vars.rm_var v (TS.vars s)) s
      | _ -> s
  in
  [TS.subst subst s]

let substitute_mess (m1, m2) s =
  let subst =
        let trs = TS.get_trs s in
        if Completion.check_equalities trs [(m1,m2)] then
          [Term.ESubst (m1,m2)]
        else
          soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_ts (ts1, ts2) s =
  let subst =
      let models = TS.get_models s in
      if Constr.query ~precise:true models [(`Pos, `Comp (`Eq,ts1,ts2))] then
        [Term.ESubst (ts1,ts2)]
      else
        soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_idx (i1 , i2 : Term.term * Term.term) s =
  let i1, i2 =  match i1, i2 with
    | Var _, Var _ -> i1, i2
    | (Diff _), _ | _, (Diff _) ->
      hard_failure
        (Tactics.Failure "only variables are supported when substituting \
                          index terms")
    | _ -> assert false
  in

  let subst =
    let models = TS.get_models s in
    if Constr.query ~precise:true models [(`Pos, `Comp (`Eq,i1,i2))] then
      [Term.ESubst (i1,i2)]
    else
      soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_tac arg s =
  let open Args in
  match arg with
  | Pair (Term (Type.Message, f1, _), Term (Type.Message, f2, _)) ->
    substitute_mess (f1,f2) s

  | Pair (Term (Type.Timestamp, f1, _), Term (Type.Timestamp, f2, _)) ->
    substitute_ts (f1,f2) s

  | Pair (Term (Type.Index, f1, _), Term (Type.Index, f2, _)) ->
    substitute_idx (f1,f2) s

  | _ ->
    hard_failure
      (Tactics.Failure "expected a pair of messages, booleans or a pair of \
                        index variables")

let () =
  T.register_typed "subst"
    ~general_help:"If i = t where i is a variable, substitute all occurences \
                   of i by t and remove i from the context variables."
    ~detailed_help:""
    ~tactic_group:Structural
    ~usages_sorts:[Args.(Sort (Pair (Index, Index)));
                   Args.(Sort (Pair (Timestamp, Timestamp)));
                   Args.(Sort (Pair (Message, Message)))]
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg substitute_tac)
    Args.(Pair (Term, Term))


(* let eqsubst arg s =
 *   let open Args in
 *   let subst,f = match arg with
 *   | Pair (ETerm (Type.Message, f1, _), ETerm (Type.Message, f2, _)) ->
 *     [Term.ESubst (f1,f2)],  Term.mk_atom `Eq f1 f2
 *
 *   | Pair (ETerm (Type.Timestamp, f1, _), ETerm (Type.Timestamp, f2, _)) ->
 *     [Term.ESubst (f1,f2)],   Term.mk_atom `Eq f1 f2
 *
 *   | Pair (ETerm (Type.Index, f1, _), ETerm (Type.Index, f2, _)) ->
 *     [Term.ESubst (f1,f2)],  Term.mk_atom `Eq f1 f2
 *
 *   | _ ->
 *     hard_failure
 *       (Tactics.Failure "expected a pair of messages, booleans or a pair of \
 *                         index variables")
 *   in
 *    TS.set_goal f s :: apply_substitute subst s
 *
 * let () =
 *   T.register_typed "substeq"
 *     ~general_help:"Given an equality i=t, substitute all occurences \
 *                    of i by t and remove i from the context variables,\
 *                    and asks to prove the equality."
 *     ~detailed_help:""
 *     ~tactic_group:Structural
 *     ~usages_sorts:[Args.(Sort (Pair (Index, Index)));
 *                    Args.(Sort (Pair (Timestamp, Timestamp)));
 *                    Args.(Sort (Pair (Message, Message)))]
 *     eqsubst Args.(Pair (ETerm, ETerm)) *)


(* FIXME: use higher-level function to retrieve the equality *)
let do_subst_eq (args : Args.parser_arg list) s : sequent list =
  let subst, f =
    match args with
    | [arg] ->
      begin
        match Args.convert_as_lsymb args with
        | Some str when Hyps.mem_name (L.unloc str) s ->
          let id, at = Hyps.by_name str s in
          begin match Term.destr_eq at with
            | Some (t1, t2) ->
              [Term.ESubst (t1,t2)],  Term.mk_eq t1 t2

            | _ -> hard_failure
                     (Tactics.Failure "expected an equality hypothesis")
          end
        | _ -> hard_failure
                 (Tactics.Failure "expected an hypothesis name")
      end

    | _ ->
      match TraceLT.convert_args s args Args.(Sort (Pair (Term, Term))) with
      | Args.Arg Pair (Term (_, f1, _), Term (_, f2, _)) ->
        [Term.ESubst (f1,f2)],  Term.mk_eq f1 f2

      | _ ->
        hard_failure
          (Tactics.Failure "expected a pair of messages")
  in
  TS.set_goal f s :: apply_substitute subst s




let subst_eq_tac args = wrap_fail (do_subst_eq args)

let () =
  T.register_general "substeq"
    ~tactic_help:
      {general_help = "Given an equality i=t, substitute all occurences \
                   of i by t and remove i from the context variables,\
                   and asks to prove the equality.";
       detailed_help = "";
       usages_sorts = [Args.(Sort (Pair (Index, Index)));
                   Args.(Sort (Pair (Timestamp, Timestamp)));
                       Args.(Sort (Pair (Message, Message)));
                      Sort Args.String];
       tactic_group = Logical}
    ~pq_sound:true
    (LowTactics.gentac_of_ttac_arg subst_eq_tac)




(*------------------------------------------------------------------*)
let autosubst s =
  let id, (x,y) = match
      Hyps.find_map
        (fun id f -> match Term.destr_eq f with
           | Some (Term.Var x, Term.Var y) 
             when Vars.ty x = Type.Timestamp || 
                  Vars.ty x = Type.Index ->
             Some (id, (x,y))
           | _ -> None)
        s
    with | Some (id,f) -> id, f
         | None -> Tactics.(soft_failure (Failure "no equality found"))
  in
  let s = Hyps.remove id s in

  let process (x : Vars.var) (y : Vars.var) : TS.t =
    (* Just remove the equality if x and y are the same variable. *)
    if x = y then s else
      (* Otherwise substitute the newest variable by the oldest one,
       * and remove it from the environment. *)
      let x,y =
        if Vars.compare x y <= 0 then y,x else x,y
      in

      let () = dbg "subst %a by %a" Vars.pp x Vars.pp y in

      let s = TS.subst [Term.ESubst (Term.mk_var x, Term.mk_var y)] s in
      TS.set_vars (Vars.rm_var x (TS.vars s)) s

  in
  [process x y]

(*------------------------------------------------------------------*)
(* TODO: this should be an axiom in some library, not a rule *)
let exec (Args.Message (a,_)) s =
  let _,var = Vars.make `Approx (TS.vars s) Type.Timestamp "t" in
  let formula =
    Term.mk_forall ~simpl:false
      [var]
      (Term.mk_impl
         (Term.mk_timestamp_leq (mk_var var) a)
         (mk_macro Term.exec_macro [] (mk_var var)))
  in
  [TraceLT.happens_premise s a ;

   TS.set_goal (Term.mk_macro exec_macro [] a) s;

    TS.set_goal
      (Term.mk_impl ~simpl:false formula (TS.goal s)) s]

let () =
  T.register_typed "executable"
    ~general_help:"Assert that exec@_ implies exec@_ for all \
                   previous timestamps."
    ~detailed_help:"This is by definition of exec, which is the conjunction of \
                    all conditions before this timestamp."
    ~tactic_group:Structural
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg exec)
    Args.Timestamp


(*------------------------------------------------------------------*)
(** [fa s] handles some goals whose conclusion formula is of the form
  * [C(u_1..u_N) = C(v_1..v_N)] and reduced them to the subgoals with
  * conclusions [u_i=v_i]. We only implement it for the constructions
  * [C] that congruence closure does not support: conditionals,
  * sequences, etc. *)
let fa s =
  let unsupported () = soft_failure (Failure "equality expected") in

  let check_vars vars vars' =
    if List.length vars <> List.length vars' then
      soft_failure (Failure "FA: sequences with different lengths");

    let tys_compatible = 
      List.for_all2 (fun v1 v2 -> 
          Type.equal (Vars.ty v1) (Vars.ty v2)
        ) vars vars'
    in
    if not tys_compatible then
      soft_failure (Failure "FA: sequences with different types");
  in

  let u, v = match TS.Reduce.destr_eq s Local_t (TS.goal s) with
    | Some (u,v) -> u, v
    | None -> unsupported ()
  in
  match u,v with
  | Term.Fun (f,_,[c;t;e]), Term.Fun (f',_,[c';t';e'])
    when f = Term.f_ite && f' = Term.f_ite ->
    let subgoals =
      let open TraceSequent in
      [ s |> set_goal (Term.mk_impl c c') ;

        s |> set_goal (Term.mk_impl c' c) ;

        s |> set_goal (Term.mk_impls
                         (if TS.Reduce.conv_term s c c' then [c] else [c;c'])
                         (Term.mk_atom `Eq t t'));

        s |> set_goal (Term.mk_impls
                         [Term.mk_not c;
                          Term.mk_not c']
                         (Term.mk_atom `Eq e e')) ]
    in
    subgoals

  (* FIXME: allow ForAll and Exists? *)
  | Term.Quant (Seq, vars,t), Term.Quant (Seq, vars',t')
    when List.for_all (Type.is_finite -| Vars.ty) vars -> 
    check_vars vars vars';

    (* have [t'] use the same variables names than [t] *)
    let t' = 
      let subst = 
        List.map2 (fun v' v -> 
            Term.ESubst (Term.mk_var v', Term.mk_var v)
          ) vars' vars
      in
      Term.subst subst t'
    in

    let env = ref (TS.vars s) in
    let vars, subst = Term.refresh_vars (`InEnv env) vars in
    let s = TS.set_vars !env s in
    let t = Term.subst subst t in
    let t' = Term.subst subst t' in
    let subgoals =
      [ TS.set_goal (Term.mk_atom `Eq t t') s ]
    in
    subgoals

  | Term.Find (vs,c,t,e),
    Term.Find (vars',c',t',e')
    when List.for_all (Type.is_finite -| Vars.ty) vs &&
         List.length vs = List.length vars' ->
    (* We verify that [e = e'],
     * and that [t = t'] and [c <=> c'] for fresh index variables.
     *
     * We do something more general for the conditions,
     * which is useful for cases arising from diff-equivalence
     * where some indices are unused on one side:
     *
     * Assume [vars = used@unused]
     * where [unusued] variables are unused in [c] and [t].
     *
     * We verify that [forall used. (c <=> exists unused. c')]:
     * this ensures that if one find succeeds, the other does
     * too, and also that the selected indices will match
     * except for the [unused] indices on the left, which does
     * not matter since they do not appear in [t]. *)

    (* Refresh bound variables in c and t*)
    let env = ref (TS.vars s) in
    let vars, subst = Term.refresh_vars (`InEnv env) vs in
    let c  = Term.subst subst c in
    let t  = Term.subst subst t in

    (* Create substitution from vars' to fresh_var *)
    (* We avoid relying on the fact that currently, subst is preserving
       the order of vars, and rather create a substitution vs -> vars',
       that we apply on the lhs of vs -> vars *)

    let subst_aux = List.map2 (fun x y ->
        Term.(ESubst (mk_var x,mk_var y))) vs vars' in
    let subst' = List.map (function ESubst (x, y) ->
        Term.(ESubst (subst subst_aux x,y))) subst in

    let s = TS.set_vars !env s in

    let c' = Term.subst subst' c' in

    let t' = Term.subst subst' t' in

    (* Extract unused variables. *)
    let used,unused =
      let occ_vars = Term.get_vars c @ Term.get_vars t in
      List.partition
        (fun v -> List.mem v occ_vars)
        vars
    in

    let subgoals =
      let open TraceSequent in
      [ set_goal (Term.mk_impl c (Term.mk_exists unused c')) s ;

        set_goal (Term.mk_impl c' c) s;

        set_goal (Term.mk_impls [c;c']
                    (mk_atom `Eq t t')) s;

        set_goal (Term.mk_atom `Eq e e') s]
    in
    subgoals

  | _ -> Tactics.(soft_failure (Failure "unsupported equality"))

let fa_tac args = match args with
  | [] -> wrap_fail fa
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
(** New goal simplification *)

let new_simpl ~red_param ~congr ~constr s =
  let s = TraceLT.reduce_sequent red_param s in

  let goals = Term.decompose_ands (TS.goal s) in
  let s = TS.set_goal Term.mk_false s in
  let goals = List.filter_map (fun goal ->
      if Hyps.is_hyp goal s || Term.f_triv goal then None
      else match form_to_xatom goal with
        | None -> Some goal
        | Some at ->
          match at, Term.ty_xatom at with
          | _, Type.Index | _, Type.Timestamp -> 
            let lit = `Pos, (at :> xatom) in
            if constr && Constr.query ~precise:true (TS.get_models s) [lit]
            then None
            else Some goal

          | `Comp (`Eq, t1, t2), _ ->
            if congr &&
               Completion.check_equalities (TS.get_trs s) [(t1,t2)]
            then None
            else Some goal

          | _ -> Some goal
    ) goals in
  [TS.set_goal (Term.mk_ands goals) s]


(*------------------------------------------------------------------*)
(** Automated goal simplification *)

let clear_triv s sk fk = sk [Hyps.clear_triv s] fk

(** Simplify goal. *)
let _simpl ~red_param ~close ~strong =
  let open Tactics in
  let intro = Config.auto_intro () in

  let assumption = if close then [try_tac (wrap_fail assumption)] else [] in

  let new_simpl ~congr ~constr =
    if strong && not intro
    then [wrap_fail (new_simpl ~red_param ~congr ~constr)] @ assumption
    else []
  in

  let expand_all =
    (if strong && close && not intro
     then [wrap_fail (TraceLT.expand_all_l `All)] @ assumption
     else [])
  in


  andthen_list ~cut:true (
    (* Try assumption first to avoid loosing the possibility
       * of doing it after introductions. *)
    assumption @
    (new_simpl ~congr:false ~constr:false) @
    (if close || intro then [wrap_fail TraceLT.intro_all;
                             wrap_fail simpl_left_tac] else []) @
    assumption @
    expand_all @
    (* Learn new term equalities from constraints before
     * learning new index equalities from term equalities,
     * otherwise this creates e.g. n(j)=n(i) from n(i)=n(j). *)
    (* (if intro then [wrap eq_trace] else []) @ *)
    (if strong then [wrap_fail eq_names] else []) @
    (* Simplify equalities using substitution. *)
    (repeat ~cut:true (wrap_fail autosubst)) ::
    expand_all @
    assumption @ (new_simpl ~congr:true ~constr:true) @
    [clear_triv]
  )

(*------------------------------------------------------------------*)
(* Attempt to close a goal. *)
let do_conclude =
  Tactics.orelse_list [wrap_fail congruence_tac;
                       wrap_fail constraints_tac;
                       wrap_fail assumption]



(* If [close] then tries to automatically prove the goal,
 * otherwise it may also be reduced to a single subgoal. *)
let simpl ~red_param ~strong ~close : TS.t Tactics.tac =
  let rec simpl_aux ~close = 
    let open Tactics in
    let (>>) = andthen ~cut:true in
    (* if [close], we introduce as much as possible to help. *)
    _simpl ~red_param ~strong ~close >>

    if not strong
    then (fun g sk fk -> sk [g] fk)
    else
      (if close || Config.auto_intro ()
       then try_tac do_conclude else Tactics.id) >>
      fun g sk fk ->
      (* If we still have a goal, we can try to split a conjunction
       * and prove the remaining subgoals, or return this goal,
       * but we must respect [close]. *)
      let fk =
        if close
        then fun _ -> fk (None, GoalNotClosed)
        else fun _ -> sk [g] fk
      in
      (wrap_fail TraceLT.goal_and_right) g
        (fun l _ -> match l with
           | [g1;g2] ->
             simpl_aux ~close g1
               (fun l' _ ->
                  if l'=[] then
                    simpl_aux ~close g2 sk fk
                  else
                    simpl_aux ~close:true g2
                      (fun l'' fk -> assert (l'' = []) ; sk l' fk)
                      fk)
               fk
           | _ -> assert false)
        fk
  in
  simpl_aux ~close
    
let tac_auto args ~red_param ~strong ~close s sk (fk : Tactics.fk) =
  match args with
  | [] -> simpl ~red_param ~close ~strong s sk fk
  | _ -> hard_failure (Tactics.Failure "no argument allowed")

let tac_autosimpl s =
  tac_auto
    ~red_param:Reduction.rp_default
    ~close:false
    ~strong:(Config.auto_intro ()) s


(* tries to close the goal with simpl *)
(* returns true if the goal was closed, false otherwise *)
let tryauto_closes (g:sequent) : bool =
  (* exception to get out of the continuations *)
  let exception Res of bool in
  let red_param = Reduction.rp_default in
  try
    let _:Tactics.a =
      simpl ~red_param ~strong:true ~close:true g
        (* if simpl succeeds: it closes the goal, so l = [] *)
        (fun l _ -> assert (l = []); raise (Res true)) 
        (* otherwise: leave the goal unchanged *)
        (fun _ -> raise (Res false))
    in
    assert false (* impossible: simpl never returns, it runs its continuations *)
  with
  | Res b -> b
   

(* returns gs without the goals that can be closed automatically *)
let tryauto (gs:sequent list) : sequent list =
  List.filter (fun g -> not (tryauto_closes g)) gs



(*------------------------------------------------------------------*)
(** Projecting a goal on a bi-system
  * to distinct goals for each projected system. *)

let project s =
  match SE.to_list (SE.to_fset (TS.system s).set) with
  | [_] ->
    soft_failure (Tactics.Failure "goal already deals with a \
                                           single process")
  | l ->
    List.map (fun (lbl,_) -> TS.pi lbl s) l

let () =
  T.register "project"
     ~tactic_help:{
       general_help = "Turn a goal on a bi-system into \
                       one goal for each projection of the bi-system.";
       detailed_help = "This tactic will project all occurrences of \
                        diff operators in local formulas.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    ~pq_sound:true
     (LowTactics.genfun_of_pure_tfun project)

(*------------------------------------------------------------------*)
(** {2 Cryptographic Tactics} *)

(*------------------------------------------------------------------*)
(** {3 Create integrity rules parameters } *)
type integrity_rule = NonMalleability


type unforgeabiliy_param = Term.fname * Term.nsymb * Term.term
                           * Term.term
                           * (Symbols.fname -> bool)
                           * Term.term list * bool
                           * (Symbols.fname -> bool) option



(*------------------------------------------------------------------*)
let non_malleability_param
    (table : Symbols.table) (t : Term.term) : unforgeabiliy_param
  =
  let bad_param () =
    soft_failure
      (Tactics.Failure
         "NM can only be applied to an hypothesis of the form
          sdec(s,sk) = m (or symmetrically) ") 
  in

  let t1, t2 = match Term.destr_eq t with
    | Some (t1, t2) -> t1, t2
    | _ -> bad_param () 
  in

  let param_dec adec key m s =
    match Symbols.Function.get_data adec table with
    | Symbols.AssociatedFunctions [aenc; pk] ->
      (aenc, key, m, s,  (fun x -> x = adec || x = pk),
       [ ], false, Some (fun x -> x=pk))

    | _ -> assert false in

  match t1, t2 with
  | (Fun (adec, _, [Tuple [m; Name key]]), s)
    when Symbols.is_ftype adec Symbols.ADec table ->
    param_dec adec key m s

  | (s, Fun (adec, _, [Tuple [m; Name key]]))
    when Symbols.is_ftype adec Symbols.ADec table ->
    param_dec adec key m s

  | _ -> bad_param ()

(*------------------------------------------------------------------*)
let mk_integrity_rule_param
    (rule : integrity_rule)
  : Symbols.table -> Term.term -> unforgeabiliy_param =
  match rule with
  | NonMalleability -> non_malleability_param
    
(*------------------------------------------------------------------*)
(** Unforgeability Axioms *)

let euf_apply_schema
    sequent (_, key, m, s, _, _, _, _) (case : OldEuf.euf_schema) : sequent
  =
  (* Equality between hashed messages *)
  let new_f = Term.mk_atom `Eq case.message m in

  (* Equalities between key indices *)
  let eq_indices =
    List.fold_left2
      (fun cnstr i i' ->
         Term.mk_and cnstr (Term.mk_atom `Eq (mk_var i) (mk_var i')))
      Term.mk_true
      key.s_indices case.key_indices
  in

  let system = SE.to_fset (TS.system sequent).set in
  let table  = TS.table sequent in

  (* Now, we need to add the timestamp constraints. *)
  (* The action name and the action timestamp variable are equal. *)
  let action_descr_ts =
    SystemExpr.action_to_term table system case.action
  in
 let ts_list =
    let iter = 
      new OldFresh.deprecated_get_actions ~cntxt:(TS.mk_trace_cntxt sequent) 
    in
    List.iter iter#visit_message [s; m];
    iter#get_actions
  in
  (* The action occured before the test H(m,k) = s. *)
  let maximal_elems = TS.maximal_elems ~precise:false sequent ts_list in

  let le_cnstr =
    List.map
      (function ts ->
        (Term.mk_timestamp_leq action_descr_ts ts))
      maximal_elems
  in
  let le_cnstr = Term.mk_ors le_cnstr in

  (* TODO: use an existential for new indices. *)
  let sequent = TS.set_vars case.env sequent in

  let goal =
    Term.mk_impls [eq_indices; new_f; le_cnstr]
      (TS.goal sequent)
  in
  TS.set_goal goal sequent

let euf_apply_direct s (_, key, m, _, _, _, _, _) OldEuf.{d_key_indices;d_message} =
  (* The components of the direct case may feature variables that are
   * not in the current environment: this happens when the case is extracted
   * from under a binder, e.g. a Seq or ForAll construct. We need to add
   * such variables to the environment. *)
  let subst, env =
    List.fold_left (fun (subst,env) v ->
        if Vars.mem env v then subst, env else
          let env,v' = Vars.make_approx env v in
          let subst = Term.(ESubst (mk_var v, mk_var v')) :: subst in
          subst,env)
      ([], TS.vars s)
      (List.sort_uniq Stdlib.compare
         (d_key_indices @
          Term.get_vars d_message))
  in
  let s = TS.set_vars env s in
  let d_message = Term.subst subst d_message in
  let d_key_indices = Term.subst_vars subst d_key_indices in

  (* Equality between hashed messages. *)
  let eq_hashes = Term.mk_atom `Eq d_message m in

  (* Equality between key indices. *)
  let eq_indices =
    List.fold_left2
      (fun cnstr i i' ->
         Term.mk_and ~simpl:false cnstr (Term.mk_atom `Eq (mk_var i) (mk_var i')))
      Term.mk_true
      key.s_indices d_key_indices
  in

  let goal =
    Term.mk_impls [eq_indices; eq_hashes] (TS.goal s)
  in
  TS.set_goal goal s

let euf_apply_facts drop_head s
    ((head_fn, key, mess, sign, allow_functions, _, _, fun_wrap_key) as p) =
  let env = TS.vars s in
  let cntxt = TS.mk_trace_cntxt s in

  (* check that the SSCs hold *)
  let errors =
    OldEuf.key_ssc ~globals:true ~messages:[mess;sign]
      ~allow_functions ~cntxt head_fn key.s_symb
  in
  if errors <> [] then
    soft_failure (Tactics.BadSSCDetailed errors);

  (* build the rule *)
  let rule =
    OldEuf.mk_rule
      ~elems:[] ~drop_head ~allow_functions ~fun_wrap_key
      ~cntxt ~env ~mess ~sign
      ~head_fn ~key_n:key.s_symb ~key_is:key.s_indices
  in

  let schemata_premises =
    List.map (fun case -> euf_apply_schema s p case) rule.OldEuf.case_schemata

  and direct_premises =
    List.map (fun case -> euf_apply_direct s p case) rule.OldEuf.cases_direct
  in

  if Symbols.is_ftype head_fn Symbols.SEnc cntxt.table
  || Symbols.is_ftype head_fn Symbols.AEnc cntxt.table then
    Cca.check_encryption_randomness
      ~cntxt
      rule.OldEuf.case_schemata rule.OldEuf.cases_direct head_fn [mess;sign] [];

  schemata_premises @ direct_premises

(** Tag EUFCMA - for composition results *)
let euf_apply
    (rule_kind : integrity_rule)
    (Args.String hyp_name)
    (s : TS.t)
  =
  let table = TS.table s in
  let id, at = Hyps.by_name hyp_name s in

  let (h,key,m,_,_,extra_goals,drop_head,_) as p =
    mk_integrity_rule_param rule_kind table at
  in
  let extra_goals = List.map (fun x ->
      TS.set_goal (Term.mk_impl x (TS.goal s)) s
    ) extra_goals in

  let tag_s =
    let f =
      Prover.get_oracle_tag_formula (Symbols.to_string h)
    in
    (* if the hash is not tagged, the formula is False, and we don't create
       another goal. *)
    if f = Term.mk_false
    then []
    else
      (* else, we create a goal where m,sk satisfy the axiom *)
      let uvarm, uvarkey,f = match f with
        | Quant (ForAll,[uvarm;uvarkey],f) -> uvarm,uvarkey,f
        | _ -> assert false
      in

      match Vars.ty uvarm,Vars.ty uvarkey with
      | Type.(Message, Message) -> let f = Term.subst [
          ESubst (Term.mk_var uvarm,m);
          ESubst (Term.mk_var uvarkey,Term.mk_name key);] f in
        [TS.set_goal
           (Term.mk_impl f (TS.goal s)) s]

      | _ -> assert false 
  in

  (* we create the honest sources using the classical eufcma tactic *)
  let honest_s = euf_apply_facts drop_head s p in

  (tag_s @ honest_s @ extra_goals)



(*------------------------------------------------------------------*)
exception Name_not_hidden

class name_under_enc (cntxt:Constr.trace_cntxt) enc is_pk target_n key_n
  = object (self)

 inherit Iter.deprecated_iter_approx_macros ~exact:false ~cntxt as super

 method visit_message t =
    match t with
    (* any name n can occur as enc(_,_,pk(k)) *)
    | Term.Fun (f, _, [Tuple [_; m; Term.Fun (g, _ , [Term.Name k])]])
      when f = enc && is_pk g && k.s_symb = key_n->  super#visit_message m
    | Term.Name name when name.s_symb = target_n -> raise Name_not_hidden
    | Term.Var m -> raise Name_not_hidden

    | _ -> super#visit_message t

end


let non_malleability arg (s : TS.t) =
  let hyp_name, opt_m = 
    match arg with
    | Args.(Pair (String hyp_name, Opt (Message, opt_m))) -> hyp_name, opt_m
    | _ -> assert false 
  in

  let enc_occurences_goals =
    euf_apply NonMalleability (Args.String hyp_name) s in
  let table = TS.table s in
  let id, at = Hyps.by_name hyp_name s in
  let (enc, key_n, _, mess1, mess2 , _ , _, is_pk) = 
    non_malleability_param table at 
  in
  let name_ssc =  match mess1, opt_m with
    | Term.Name name, None -> name
    | m, Some (Message (Term.Name name,ty)) -> name
    | _, _ -> soft_failure
      (Tactics.Failure
         "When NM is applied to an hypothesis of the form
          sdec(s,sk) = m, where m is not a name, one must give as extra \
          parameter a name such that m strongly depends on it. ")
  in
  (* we check is the given name name_ssc only occurs under valid encryptions *)
  (* the fact that the encryptions all use distinct randoms is checked by
     the later euf application (cf euf_apply_facts) *)
  let is_pk = match is_pk with Some f -> f | _ -> assert false in
  let cntxt = TS.mk_trace_cntxt s in
  let ssc =
    new name_under_enc cntxt enc is_pk name_ssc.s_symb key_n.s_symb in
  (try
     (* Remark: if we start considering C[dec(m,sk)], we will need to also
        check the SSC for C. *)
     SystemExpr.iter_descrs
       cntxt.table cntxt.system
       (fun action_descr ->
          ssc#visit_message (snd action_descr.output) ;
          List.iter (fun (_,t) -> ssc#visit_message t) action_descr.updates)
  with Name_not_hidden -> soft_failure Tactics.NameNotUnderEnc);
  let neq_goals = match mess1, opt_m with
    | Term.Name name, None -> [] (* we have nothing to do, a name will always be
                                    not equal to another fres name *)
  | m, Some (Message (Term.Name n as name,ty)) ->
    (* we now create the inequality to be checked *)
    let ndef = Symbols.{ n_fty = Type.mk_ftype [] [] ty; } in
    let table,n =
      Symbols.Name.declare table (L.mk_loc L._dummy "n_NM") ndef
    in
    let freshname = Term.mk_isymb n ty [] in
    let s = TS.set_table table s in
    let new_mess = Term.subst [Term.ESubst (name, Term.mk_name freshname)] m in
    [TS.set_goal (Term.mk_atom `Neq new_mess m) s]
  | _, _ -> soft_failure
      (Tactics.Failure
         "When NM is applied to an hypothesis of the form
          sdec(s,sk) = m, where m is not a name, one must give as extra \
          parameter a name such that m strongly depends on it. ")
    in
  neq_goals @ enc_occurences_goals

let () =
  T.register_typed "nm"
    ~general_help:"Apply the NM axiom to the given hypothesis name."
    ~detailed_help:"Can be applied to any hypothesis of the form dec(m,sk) = t(n)."
    ~tactic_group:Cryptographic
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg non_malleability)
    Args.(Pair (String, Opt Message))

(*------------------------------------------------------------------*)
let valid_hash (cntxt : Constr.trace_cntxt) (t : Term.term) =
  match t with
  | Fun (hash, _, [Tuple [m; Name key]]) ->
    Symbols.is_ftype hash Symbols.Hash cntxt.table

  | _ -> false

(** We collect all hashes appearing inside the hypotheses, and which satisfy
    the syntactic side condition. *)
let top_level_hashes s =
  let cntxt = TS.mk_trace_cntxt s in

  let hashes =
    List.filter (valid_hash cntxt) (TS.get_all_messages s)
    |> List.sort_uniq Stdlib.compare
  in

  if List.length hashes = 0 then soft_failure Tactics.NoSSC;

  let rec make_eq acc hash_list =
    match hash_list with
    | [] -> acc
    | h1::q ->
      List.fold_left
        (fun acc h2 ->
           match h1, h2 with
           | Fun (hash1, _, [Tuple [_; Name key1]]),
             Fun (hash2, _, [Tuple [_; Name key2]])
             when hash1 = hash2 && key1 = key2 -> (h1, h2) :: acc
           | _ -> acc)
        (make_eq acc q) q
  in

  let trs = TS.get_trs s in

  make_eq [] hashes
  |> List.filter (fun (a,b) ->
      Completion.check_equalities trs [(a,b)])



(** [collision_resistance judge sk fk] applies the collision resistance axiom
    between the hashes:
    - if [i = Some j], collision in hypothesis [j]
    - if [i = None], collects all equalities between hashes that occur at
    toplevel in message hypotheses. *)
let collision_resistance TacticsArgs.(Opt (String, i)) (s : TS.t) =

  let hash_eqs = match i with
    | None -> top_level_hashes s
    | Some (String j) -> 
      let _, h = Hyps.by_name j s in
      match TS.Reduce.destr_eq s Local_t h with
      | Some (t1, t2) ->
        let cntxt = TS.mk_trace_cntxt s in
        if not (valid_hash cntxt t1) || not (valid_hash cntxt t2) then
          soft_failure Tactics.NoSSC;

        [t1,t2]
      | _ -> soft_failure Tactics.NoCollision
  in

  let new_facts =
    List.fold_left
      (fun acc (h1,h2) ->
         match h1, h2 with
         | Fun (hash1, _, [Tuple [m1; Name key1]]),
           Fun (hash2, _, [Tuple [m2; Name key2]])
           when hash1 = hash2 && key1 = key2 ->
           Term.mk_atom `Eq m1 m2 :: acc
         | _ -> acc)
      [] hash_eqs
  in
  let f_coll = Term.mk_ands new_facts in

  if f_coll = Term.mk_true then soft_failure Tactics.NoCollision;

  let goal = Term.mk_impl ~simpl:false f_coll (TS.goal s) in
  [TS.set_goal goal s]

let () = T.register_typed "collision"
    ~general_help:"Collects all equalities between hashes \
                   occurring at toplevel in\
                   message hypotheses, and adds the equalities \
                   between messages that have the same hash with \
                   the same valid key."
    ~detailed_help:"A key is valid if it is only used in a key \
                    position. Remark that this could be relaxed, \
                    as CR holds for any valid key, even known to \
                    the attacker."
    ~tactic_group:Cryptographic
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg collision_resistance)
    Args.(Opt String)

(*------------------------------------------------------------------*)

(** Transform a term according to some equivalence given as a biframe.
  * Macros in the term occurring (at toplevel) on the [src] projection
  * of some biframe element are replaced by the corresponding [dst]
  * projection. *)
let rewrite_equiv_transform
    ~(src:Term.proj)
    ~(dst:Term.proj)
    ~(s:TS.t)
    (biframe : Term.term list)
    (term : Term.term) : Term.term option
  =
  let exception Invalid in

  let assoc (t : Term.term) : Term.term option =
    match List.find_opt (fun e -> 
        TS.Reduce.conv_term s (Term.project1 src e) t
      ) biframe 
    with
    | Some e -> Some (Term.project1 dst e)
    | None -> None
  in
  let rec aux (t : term) : term = 
    match Term.ty t with
    | Type.Timestamp | Type.Index -> t
    | _ ->
      match assoc t with
      | None -> aux_rec t
      | Some t' -> t'

  and aux_rec (t : Term.term) : Term.term = 
    match t with
    | t when is_pure_timestamp t -> t

    | Fun (fsymb,ftype,args) ->
      let args = List.map aux args in
      Term.mk_fun0 fsymb ftype args

    | Diff (Explicit l) ->
      Term.mk_diff (List.map (fun (p,t) -> p, aux t) l)

    (* We can support input@ts (and keep it unchanged) if
     * for some ts' such that ts'>=pred(ts),
     * frame@ts' is a biframe element, i.e. the two
     * projections are frame@ts'.
     * Note that this requires that ts' and pred(ts)
     * happen, which is necessary to have input@ts =
     * att(frame@pred(ts)) and frame@pred(ts) a sublist
     * of frame@ts'. *)
    | Macro (msymb,messages,ts) when msymb = Term.in_macro ->
      let ok_frame = function
        | Macro (msymb',[],ts') ->
          msymb' = Term.frame_macro &&
          TS.query ~precise:true s
            [`Pos,`Comp (`Leq, mk_pred ts, ts')]
        | _ -> false
      in
      if List.exists ok_frame biframe then t else raise Invalid

    | _ -> raise Invalid
  in
  try Some (aux term) with Invalid -> None

(* Rewrite equiv rule on sequent [s] with direction [dir],
   using assumption [ass] wrt system [ass_context]. *)
let rewrite_equiv (ass_context,ass,dir) (s : TS.t) : TS.t list =

  (* Decompose [ass] as [subgoal_1 => .. => subgoal_N => equiv(biframe)].
     We currently require subgoals to be reachability formulas,
     for simplicity. *)
  let subgoals, biframe =
    let rec aux = function
      | Equiv.(Atom (Equiv bf)) -> [],bf
      | Impl (Atom (Reach f),g) -> let s,bf = aux g in f::s,bf
      | _ -> Tactics.(soft_failure (Failure "invalid assumption"))
    in aux ass
  in

  (* Subgoals are relative to [ass_context.set].
     They are proved in theory as global formulas, immediately changed in
     the tactic to local formulas. These local formulas cannot be proved
     while keeping all local hypotheses: however, we can keep the pure trace
     formulas from the local hypotheses.
     We already know that [ass_context.set] is compatible with the systems
     used in the equivalence, hence we keep [s]'s context. *)
  let s' =
    s |>
    TS.Hyps.filter
      (fun _ -> function
         | Local f -> Term.is_pure_timestamp f
         | Global  _ -> true)
  in
  let subgoals = List.map (fun f -> TS.set_goal f s') subgoals in

  (* Identify which projection of the assumption's conclusion
     corresponds to the current goal and new goal (projections [src,dst])
     and the expected systems before and after the transformation. *)
  let src,dst,orig_sys,new_sys =
    let pair = Utils.oget ass_context.SE.pair in
    let left,lsys = SE.fst pair in
    let right,rsys = SE.snd pair in
    match dir with
      | `LeftToRight -> left,right,lsys,rsys
      | `RightToLeft -> right,left,rsys,lsys
  in

  (* Compute new set annotation, checking by the way
     that rewrite equiv applies to sequent [s]. *)
  let updated_set =
    SE.to_list (SE.to_fset (TS.system s).set) |>
    List.map (fun (p,s) ->
                if s = orig_sys then p, new_sys else
                  Tactics.(soft_failure Rewrite_equiv_system_mismatch)) |>
    SE.of_list
  in
  let updated_context =
    { (TS.system s) with set = (updated_set:>SE.arbitrary) } in

  let warn_unsupported t =
    Printer.prt `Warning
      "Cannot transform %a: it will be dropped.@." Term.pp t
  in

  (* Attempt to transform. If the transformation can't
   * be applied we can simply drop the hypothesis rather
   * than failing completely. *)
  let rewrite (h : Term.term) : Term.term option =
    match rewrite_equiv_transform ~src ~dst ~s biframe h with
    | None -> warn_unsupported h; None
    | x -> x
  in

  let goal =
    TS.set_goal_in_context
      ~update_local:rewrite
      updated_context
      (match rewrite_equiv_transform ~src ~dst ~s biframe (TS.goal s) with
       | Some t -> t
       | None -> warn_unsupported (TS.goal s); Term.mk_false)
      s
  in
  subgoals @ [goal]

let rewrite_equiv_args args (s : TS.t) : TS.t list =
  match args with
  | [TacticsArgs.RewriteEquiv rw] ->
    let ass_context, subgs, ass, dir = TraceLT.p_rw_equiv rw s in
    subgs @ rewrite_equiv (ass_context, ass, dir) s
  | _ -> bad_args ()

let rewrite_equiv_tac args = wrap_fail (rewrite_equiv_args args)

let () =
  T.register_general "rewrite equiv"
    ~tactic_help:{
      general_help =
        "Use an equivalence to rewrite a reachability goal.";
      detailed_help =
        "The tactic argument should be a proof term corresponding to an \
         assumption which concludes with an equivalence atom, i.e. a biframe. \
         If the assumption has premises, new subgoals are created.\
         \n\n\
         When applied, all occurrences of left elements of the biframe \
         are rewritten by their corresponding right elements. \
         All macros in the goal must be rewritten, or the tactic fails.\
         Default direction is left-to-right (can be changed using `-`).";
      tactic_group = Structural;
      usages_sorts = [] }
    ~pq_sound:true
    (LowTactics.gentac_of_ttac_arg rewrite_equiv_tac)
