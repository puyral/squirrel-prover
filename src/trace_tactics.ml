open Tactics
open Logic
open Formula
open Term

type tac = Judgment.t Tactics.tac

module T = Prover.Prover_tactics

(** Propositional connectives *)

let goal_or_intro_l (judge : Judgment.t) sk fk =
  match judge.Judgment.formula with
  | (Or (lformula, _)) -> sk
                            [Judgment.set_formula (lformula) judge]
                            fk
  | _ -> fk (Tactics.Failure "Cannot introduce a disjunction")

let goal_or_intro_r (judge : Judgment.t) sk fk =
  match judge.Judgment.formula with
  | (Or (_, rformula)) -> sk [Judgment.set_formula (rformula) judge] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a disjunction")

let () = T.register "left" goal_or_intro_l
let () = T.register "right" goal_or_intro_r

(* TODO currently unused: remove? *)
let goal_true_intro (judge : Judgment.t) sk fk =
  match judge.Judgment.formula with
  | True -> sk () fk
  | _ -> fk (Tactics.Failure "Cannot introduce true")

let goal_and_intro (judge : Judgment.t) sk fk =
  match judge.Judgment.formula with
  | And (lformula, rformula) ->
    sk [ Judgment.set_formula (lformula) judge;
         Judgment.set_formula (rformula) judge ] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a conjonction")

let () = T.register "split" goal_and_intro

(** Introduce various connectives to the right: currently,
  * disjunction and implication (with conjunction on its left).
  * TODO this is a bit arbitrary, and it will be surprising for
  * users that "intro" does not introduce universal quantifiers. *)
let goal_intro (judge : Judgment.t) sk fk =
  let exception No_intro in
  try
    let ((facts,constrs),new_goal) =
      match judge.Judgment.formula with
      | f when is_disjunction f ->
        let (f1,c1) = disjunction_to_atom_lists f in
        (List.map (fun c -> Bformula.Not c) f1,
         List.map (fun c -> Bformula.Not c) c1)
      , False
      | Impl(lhs,rhs) when is_conjunction lhs ->
        (conjunction_to_atom_lists lhs, rhs)
      | _ -> raise No_intro
    in
    let judge = List.fold_left
        (fun j f -> Judgment.add_fact f j) judge facts
    in
    let judge = List.fold_left
        (fun j c -> Judgment.add_constr c j) judge constrs
    in
    sk [Judgment.set_formula new_goal judge] fk
  with No_intro ->
    fk (Tactics.Failure "Can only introduce disjunction of atoms, \
                         or the left hand-side of an implication which \
                         is a conjonction")

let () = T.register "intro" goal_intro

(** Quantifiers *)

(** Introduce the universally quantified variables and the goal. *)
let goal_forall_intro (judge : Judgment.t) sk fk =
  match judge.Judgment.formula with
  | ForAll (vs,f) ->
    let env = ref judge.Judgment.env in
    let vsubst =
      List.map
        (fun x ->
           (x, Vars.make_fresh_from_and_update env x))
        vs
    in
    let subst = Term.from_varsubst vsubst in
    let new_formula = subst_formula subst f in
    let new_judge = Judgment.set_formula new_formula judge
                    |> Judgment.set_env (!env)
    in
    sk [new_judge] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a forall")

let () = T.register "forall_r" goal_forall_intro

let goal_exists_intro nu (judge : Judgment.t) sk fk =
  match judge.Judgment.formula with
  | Exists (vs,f) ->
    let new_formula = subst_formula nu f in
    sk [Judgment.set_formula new_formula judge] fk
  | _ -> fk (Tactics.Failure "Cannot introduce an exists")

let () = T.register_subst "exists" goal_exists_intro

let goal_any_intro j sk fk =
  Tactics.orelse_list
    [goal_and_intro;
     goal_intro;
     goal_forall_intro] j sk fk

let () =
  T.register_macro "intros"
    Prover.AST.(
      Repeat
        (OrElse
           [ Abstract ("intro",[]) ;
             Abstract ("forall_r",[]) ]))

let () =
  T.register_macro "anyintro"
    Prover.AST.(
      OrElse
        [ Abstract ("split",[]) ;
          Abstract ("intro",[]) ;
          Abstract ("forall_r",[]) ])

(** Absurd *)

let constr_absurd (judge : Judgment.t) sk fk =
  if not @@ Theta.is_sat judge.Judgment.theta then
    sk [] fk
  else fk (Tactics.Failure "Constraints satisfiable")

let gamma_absurd (judge : Judgment.t) sk fk =
  if not @@ Gamma.is_sat judge.Judgment.gamma then
    sk [] fk
  else fk (Tactics.Failure "Equations satisfiable")

let () = T.register "congruence" gamma_absurd

let () = T.register "notraces" constr_absurd

let assumption (judge : Judgment.t) sk fk =
  match judge.Judgment.formula with
  | True -> sk [] fk
  | Atom (Message f) ->
    if Judgment.mem_fact (Bformula.Atom f) judge then
      sk [] fk
    else fk (Tactics.Failure "Not in hypothesis")
  | _ -> fk (Tactics.Failure "Not in hypothesis")

let () = T.register "assumption" assumption

(** Utils *)

let mk_or_cnstr l = match l with
  | [] -> Bformula.False
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (Bformula.Or (x,acc)) l in
    mk_c a l'

let mk_and_cnstr l = match l with
  | [] -> Bformula.True
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (Bformula.And (x,acc)) l in
    mk_c a l'

open Bformula

(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

let eq_names (judge : Judgment.t) sk fk =
  let judge = Judgment.update_trs judge in
  let cnstrs = Completion.name_index_cnstrs (Gamma.get_trs judge.Judgment.gamma)
      (Gamma.get_all_terms judge.Judgment.gamma)
  in
  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_constr c judge
      ) judge cnstrs
  in
  sk [judge] fk

let () = T.register "eqnames" eq_names

let eq_constants fn (judge : Judgment.t) sk fk =
  let judge = Judgment.update_trs judge in
  let cnstrs =
    Completion.constant_index_cnstrs fn (Gamma.get_trs judge.Judgment.gamma)
      (Gamma.get_all_terms judge.Judgment.gamma)
  in
  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_constr c judge
      ) judge cnstrs
  in
  sk [judge] fk

let () = T.register_fname "eqconstants" eq_constants

let eq_timestamps (judge : Judgment.t) sk fk =
  let ts_classes = Theta.get_equalities judge.Judgment.theta
                   |> List.map (List.sort_uniq Pervasives.compare)
  in
  let subst =
    let rec asubst e = function
        [] -> []
      | p::q -> TS (p,e) :: (asubst e q)
    in
    List.map (function [] -> [] | p::q -> asubst p q) ts_classes
    |> List.flatten
  in
  let terms = (Gamma.get_all_terms judge.Judgment.gamma) in
  let facts =
    List.fold_left
      (fun acc t ->
         let normt : Term.term = subst_term subst t in
         if normt = t then
           acc
         else
           Bformula.Atom (Eq, t, normt) ::acc)
      [] terms
  in
  let judge =
    List.fold_left
      (fun judge c ->
         Judgment.add_fact c judge)
      judge facts
  in
  sk [judge] fk

let () = T.register "eqtimestamps" eq_timestamps

(** EUF Axioms *)

(** [modulo_sym f at] applies [f] to [at] modulo symmetry of the equality. *)
let modulo_sym f at = match at with
  | (Eq as ord, t1, t2) | (Neq as ord, t1, t2) -> begin match f at with
      | Some _ as res -> res
      | None -> f (ord, t2, t1) end
  | _ -> f at

let euf_param (at : term_atom) = match at with
  | (Eq, Fun ((hash, _), [m; Name key]), s) ->
    if Theory.is_hash hash then
      Some (hash, key, m, s)
    else None
  | _ -> None

let euf_apply_schema theta (_, (_, key_is), m, s) case =
  let open Euf in
  let open Process in
  (* We create the term equality *)
  let eq = Atom (Eq, case.message, m) in
  let new_f = And (eq, case.blk_descr.condition) in
  (* Now, we need to add the timestamp constraints. *)
  (* The block action name and the block timestamp variable are equal. *)
  let blk_ts = TName case.blk_descr.action in
  (* The block occured before the test H(m,k) = s. *)
  let le_cnstr =
    List.map (fun ts ->
        Atom (Pts (Leq, blk_ts, ts))
      ) (Theta.maximal_elems theta (term_ts s @ term_ts m))
    |> mk_or_cnstr
  in
  (* The key indices in the bock and when m was hashed are the same. *)
  let eq_cnstr =
    List.map2 (fun i i' ->
        Atom (Pind (Eq, i, i'))
      ) key_is case.key_indices
    |> mk_and_cnstr
  in
  let constr = And (eq_cnstr, le_cnstr) in
  (new_f, constr)

let euf_apply_direct theta (_, (_, key_is), m, _) dcase =
  let open Euf in
  let open Process in
  (* We create the term equality *)
  let eq = Atom (Eq, dcase.d_message, m) in
  (* Now, we need to add the timestamp constraint between [key_is] and
     [dcase.d_key_indices]. *)
  let eq_cnstr =
    List.map2 (fun i i' ->
        Atom (Pind (Eq, i, i'))
      ) key_is dcase.d_key_indices
    |> mk_and_cnstr
  in
  (eq, eq_cnstr)

(* TODO : make error reporting for euf more informative *)
let euf_apply_facts judge at = match modulo_sym euf_param at with
  | None -> raise @@ Tactic_Hard_Failure "bad euf application"
  | Some p ->
    let env = ref judge.Judgment.env in
    let (hash_fn, (key_n, key_is), m, s) = p in
    let rule = Euf.mk_rule env m s hash_fn key_n in
    let schemata_premises =
      List.map (fun case ->
          let new_f, new_cnstr = euf_apply_schema judge.Judgment.theta p case in
          Judgment.add_fact new_f judge
          |> Judgment.add_constr new_cnstr
          |> Judgment.set_env !env
        ) rule.Euf.case_schemata
    and direct_premises =
      List.map (fun case ->
          let new_f, new_cnstr = euf_apply_direct judge.Judgment.theta p case in
          Judgment.add_fact new_f judge
          |> Judgment.add_constr new_cnstr
        ) rule.Euf.cases_direct
    in
    schemata_premises @ direct_premises

let euf_apply f_select (judge : Judgment.t) sk fk =
  let g, at = Gamma.select judge.Judgment.gamma f_select (set_euf true) in
  let judge = Judgment.set_gamma g judge in
  (* TODO: need to handle failure somewhere. *)
  sk (euf_apply_facts judge at) fk

let () =
  T.register_int "euf"
    (fun i ->
       let f_select _ t = t.id = i in
       euf_apply f_select)

let apply gp (subst:subst) (judge : Judgment.t) sk fk =
  let exception No_apply in
  let env = ref judge.Judgment.env in
  let formula = subst_formula subst gp in
  try
    let ((check_facts,check_constrs),(new_facts,new_constrs)) =
      match formula with
      | f when is_conjunction f ->
        ([], []), conjunction_to_atom_lists f
      | Impl(lhs,rhs) when is_disjunction lhs && is_conjunction rhs->
        disjunction_to_atom_lists lhs, conjunction_to_atom_lists rhs
      | ForAll(vs,f) when is_conjunction f ->
        let f = fresh_quantifications env f in
        ([], []), conjunction_to_atom_lists f
      | ForAll(vs, Exists(vs2, f)) when is_conjunction f ->
        begin
          match fresh_quantifications env (Exists(vs2, f)) with
          |  (Exists(vs2, f)) ->
            ([], []), conjunction_to_atom_lists f
          | _ -> assert false
        end
      | ForAll(vs, Impl(lhs,rhs))
        when is_disjunction lhs && is_conjunction rhs->
        begin
          match fresh_quantifications env (Impl(lhs, rhs)) with
          | Impl(lhs,rhs) ->
            disjunction_to_atom_lists lhs, conjunction_to_atom_lists rhs
          | _ -> assert false
        end
      | ForAll(vs, Impl(lhs, Exists(vs2, rhs)))
        when is_disjunction lhs && is_conjunction rhs->
        begin
          match fresh_quantifications env (Impl(lhs, Exists(vs2, rhs))) with
          | (Impl(lhs, Exists(vs2, rhs))) ->
            disjunction_to_atom_lists lhs, conjunction_to_atom_lists rhs
          | _ -> assert false
        end

      | _ -> raise No_apply
    in
    let ts_atom_list = List.map (function
        | Bformula.Atom a -> a
        | _ -> assert false) check_constrs in
    if not( Theta.is_valid judge.Judgment.theta ts_atom_list) then
      raise @@ Tactic_Hard_Failure "Failed to prove the variable constraint.";
    let term_atom_list = List.map (function
        | Bformula.Atom a -> a
        | _ -> assert false) check_facts in
    if not( Gamma.is_valid judge.Judgment.gamma term_atom_list) then
      raise @@ Tactic_Hard_Failure "Failed to prove the variable constraint.";
    let judge = List.fold_left
        (fun j f -> Judgment.add_fact f j) judge new_facts
    in
    let judge = List.fold_left
        (fun j c -> Judgment.add_constr c j) judge new_constrs
    in
    sk [judge] fk
  with No_apply -> fk (Failure "Can only apply quantified conjunction of atoms
 or a disjunction implying a conjunction.")

let () =
  T.register_general "apply"
    (function
       | [Prover.Goal_name gname; Prover.Subst s] ->
           let f = Prover.get_goal_formula gname in
           apply f s
       | _ -> raise @@ Tactics.Tactic_Hard_Failure "improper arguments")

let tac_assert f j sk fk =
  let j1 = Judgment.set_formula f j in
  match Formula.formula_to_fact f with
    | fact -> sk [j1; Judgment.add_fact fact j] fk
    | exception Failure _ ->
        match Formula.formula_to_constr f with
          | constr -> sk [j1; Judgment.add_constr constr j] fk
          | exception Failure _ -> fk (Failure "unsupported formula")

let () =
  T.register_formula "assert"
    (fun f j sk fk -> tac_assert f j sk fk)

let collision_resistance (judge : Judgment.t) sk fk =
  let judge = Judgment.update_trs judge in
  let hashes = List.filter
      (fun t -> match t with
         | Fun ((hash, _), [m; Name key]) -> Theory.is_hash hash
         | _ -> false)
      (Gamma.get_all_terms judge.Judgment.gamma)
  in
  let rec make_eq hash_list =
    match hash_list with
    | [] -> []
    | h1::q -> List.fold_left (fun acc h2 ->
        match h1, h2 with
        | Fun ((hash, _), [m1; Name key1]), Fun ((hash2, _), [m2; Name key2])
          when hash = hash2 && key1 = key2 -> (h1, h2) :: acc
        | _ -> acc
      ) [] q
  in
  let hash_eqs = make_eq hashes
                 |> List.filter (fun eq -> Completion.check_equalities
                                    (Gamma.get_trs judge.Judgment.gamma) [eq])
  in
  let new_facts =
    List.fold_left (fun acc (h1,h2) ->
        match h1, h2 with
        | Fun ((hash, _), [m1; Name key1]), Fun ((hash2, _), [m2; Name key2])
          when hash = hash2 && key1 = key2 ->
          Atom (Eq, m1, m2) :: acc
        | _ -> acc
      ) [] hash_eqs
  in
  let judge =
    List.fold_left (fun judge f ->
        Judgment.add_fact f  judge
      ) judge new_facts
  in
  sk [judge] fk

let () = T.register "collision" collision_resistance
