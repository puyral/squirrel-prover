open Term

type tac = EquivSequent.t Tactics.tac

module T = Prover.EquivTactics

(** {2 Utilities} *)

exception Out_of_range

(** When [0 <= i < List.length l], [nth i l] returns [before,e,after]
  * such that [List.rev_append before (e::after) = l] and
  * [List.length before = i].
  * @raise Out_of_range when [i] is out of range. *)
let nth i l =
  let rec aux i acc = function
    | [] -> raise Out_of_range
    | e::tl -> if i=0 then acc,e,tl else aux (i-1) (e::acc) tl
  in aux i [] l

(** {2 Tactics} *)

(** Wrap a tactic expecting an equivalence goal (and returning arbitrary
  * goals) into a tactic expecting a general prover goal (which fails
  * when that goal is not an equivalence). *)
let only_equiv t (s : Prover.Goal.t) sk fk =
  match s with
  | Prover.Goal.Equiv s -> t s sk fk
  | _ -> fk (Tactics.Failure "Equivalence goal expected")

(** Wrap a tactic expecting and returning equivalence goals
  * into a general prover tactic. *)
let pure_equiv t s sk fk =
  let t' s sk fk =
    t s (fun l fk -> sk (List.map (fun s -> Prover.Goal.Equiv s) l) fk) fk
  in
  only_equiv t' s sk fk

(* Admit tactic *)
let () =
  T.register_general "admit"
    ~help:"Closes the current goal, or frop a bi-frame element.\
           \n Usage: admit [pos]."
    (function
       | [] -> only_equiv (fun _ sk fk -> sk [] fk)
       | [Prover.Int i] ->
           pure_equiv begin fun s sk fk ->
             let before,_,after = nth i (EquivSequent.get_biframe s) in
             let s =
               EquivSequent.set_biframe s (List.rev_append before after)
             in
               sk [s] fk
           end
       | _ -> raise @@ Tactics.Tactic_hard_failure
                         (Tactics.Failure "improper arguments"))

(** Tactic that succeeds (with no new subgoal) on equivalences
  * where the two frames are identical. *)
let refl (s : EquivSequent.t) sk fk =
  if EquivSequent.get_frame Term.Left s = EquivSequent.get_frame Term.Right s
  then
    sk [] fk
  else
    fk (Tactics.Failure "Frames not identical")


let () =
  T.register "refl"
    ~help:"Closes a reflexive goal.\n Usage: refl."
    (only_equiv refl)


let assumption s sk fk =
  let hypothesis = EquivSequent.get_hypothesis_biframe s in
  if List.for_all (fun elem -> List.mem elem hypothesis)
      (EquivSequent.get_biframe s) then
    sk [] fk
  else
     fk (Tactics.Failure "Conclusion different from hypothesis.")

let () =
  T.register "assumption"
    ~help:"Close a goal contained in its hypothesis.\n Usage: assump."
    (only_equiv assumption)

let induction ts s sk fk =
  let env = EquivSequent.get_env s in
  let tsubst = Theory.subst_of_env env in
  let ts = Theory.convert tsubst ts Sorts.Timestamp in
  match ts with
  | Var t ->
    if List.exists (function
        | EquivSequent.Message m -> List.mem (Vars.EVar t)
                                      (Term.get_vars m)
        | EquivSequent.Formula m -> List.mem (Vars.EVar t)
                                      (Term.get_vars m)
      )
        (EquivSequent.get_hypothesis_biframe s) then
      raise @@ Tactics.Tactic_hard_failure
        (Tactics.Failure "Variable should not occur in the premise");
    let s = EquivSequent.set_env (Vars.rm_var env t) s in
    let subst = [Term.ESubst(ts,Pred(ts))] in
    let goal = EquivSequent.get_biframe s in
    let hypothesis = EquivSequent.(apply_subst_frame subst goal) in
    let induc_goal = EquivSequent.set_hypothesis_biframe s hypothesis in
    let init_goal =
      EquivSequent.(set_biframe
                      s (apply_subst_frame [Term.ESubst(ts,Init)] goal))
    in
    let goals = ref [] in
    let add_action a =
      let env = ref @@ EquivSequent.get_env induc_goal in
      let indices =
        List.map
          (fun i -> Vars.make_fresh_from_and_update env i)
          a.Action.indices
      in
      let subst =
        List.map2 (fun i i' -> Term.ESubst (Term.Var i,Term.Var i'))
          a.Action.indices indices
      in
      let name = Action.to_term (Action.subst_action subst a.Action.action) in
      let ts_subst = [Term.ESubst(ts,name)] in
      goals := (EquivSequent.apply_subst ts_subst induc_goal
                |> EquivSequent.set_env !env)
               ::!goals
    in
  Action.iter_descrs (EquivSequent.get_system s) add_action ;
    sk (init_goal::!goals) fk
  | _ ->  raise @@ Tactics.Tactic_hard_failure
      (Tactics.Failure "Induction is only possible over a variable")

let () =
  T.register_general "induction"
    ~help:"Apply the induction scheme to the given timestamp.\
           \n Usage: induction t."
    (function
       | [Prover.Theory th] -> pure_equiv (induction th)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))

let enrich (t : Theory.term) s sk fk =
  let tsubst = Theory.subst_of_env (EquivSequent.get_env s) in
  let elem = match Theory.convert tsubst t Sorts.Boolean with
    | f -> EquivSequent.Formula f
    | exception _ ->
      begin
        match Theory.convert tsubst t Sorts.Message with
        | m -> EquivSequent.Message m
        | exception _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments")
      end
  in
  sk [EquivSequent.set_biframe s
        (elem :: EquivSequent.get_biframe s)] fk

let () = T.register_general "enrich"
    ~help:"Enrich the goal with the given term.\
           \n Usage: enrich t."
    (function
       | [Prover.Theory v] -> pure_equiv (enrich v)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))


let timestamp_case ts s sk fk =
  let tsubst = Theory.subst_of_env (EquivSequent.get_env s) in
  let ts = Theory.convert tsubst ts Sorts.Timestamp in
  let goals = ref [] in
  let add_action a =
    let env = ref @@ EquivSequent.get_env s in
    let indices =
      List.map
        (fun i -> Vars.make_fresh_from_and_update env i)
        a.Action.indices
    in
    let subst =
      List.map2 (fun i i' -> Term.ESubst (Term.Var i,Term.Var i'))
        a.Action.indices indices
    in
    let name = Action.to_term (Action.subst_action subst a.Action.action) in
    let ts_subst = [Term.ESubst(ts,name)] in
    goals := (EquivSequent.apply_subst ts_subst s
             |> EquivSequent.set_env !env)
             ::!goals
  in
  Action.iter_descrs (EquivSequent.get_system s) add_action ;
  goals := EquivSequent.apply_subst [Term.ESubst(ts,Term.Init)] s :: !goals ;
  sk !goals fk

let () =
  T.register_general "case"
    ~help:"Introduce all the possible goals when instantiating T with all \
           \n possible actions.
           \n Usage: case T."
    (function
       | [Prover.Theory th] -> pure_equiv (timestamp_case th)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))

let const s sk fk =
  let frame = EquivSequent.get_biframe s in
  let rec is_const : type a. a Term.term -> bool = function
    | True -> true
    | False -> true
    | Fun (f,l) -> List.for_all is_const l
    | And (f, g) -> (is_const f) && (is_const g)
    | Or (f, g) -> (is_const f) && (is_const g)
    | Impl (f, g) -> (is_const f) && (is_const g)
    | Not f -> (is_const f)
    | _ -> false
  in
  let is_const =  function
    | EquivSequent.Message e -> is_const e
    | EquivSequent.Formula e -> is_const e
  in
  sk [EquivSequent.set_biframe s
        (List.filter (fun e -> not (is_const e)) frame)] fk

let () =
  T.register "const"
    ~help:"Remove all constants from the frame.
           \n Usage: const." (pure_equiv const)

(** Function application *)
let fa i s sk fk =
  let expand : type a. a Term.term -> EquivSequent.elem list = function
    | Fun (f,l) ->
        List.map (fun m -> EquivSequent.Message m) l
    | ITE (c,t,e) when t = e ->
        EquivSequent.[ Message t ]
    | ITE (c,t,e) ->
        EquivSequent.[ Formula c ; Message t ; Message e ]
    | And (f,g) ->
        EquivSequent.[ Formula f ; Formula g ]
    | Or (f,g) ->
      EquivSequent.[ Formula f ; Formula g ]
    | Atom (`Message (_,f,g)) ->
        EquivSequent.[ Message f ; Message g ]
    | Impl (f,g) ->
        EquivSequent.[ Formula f ; Formula g ]
    | Not f -> EquivSequent.[ Formula f ]
    | True -> []
    | False -> []
    | Diff _ ->
        Tactics.soft_failure
          (Tactics.Failure "No common construct")
    | _ ->
        Tactics.soft_failure
          (Tactics.Failure "Unsupported: TODO")
  in
  let expand = function
    | EquivSequent.Message e -> expand (Term.head_normal_biterm e)
    | EquivSequent.Formula e -> expand (Term.head_normal_biterm e)
  in
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        begin try
          let biframe = List.rev_append before (expand e @ after) in
          sk [EquivSequent.set_biframe s biframe] fk
        with
          | Tactics.Tactic_soft_failure err -> fk err
        end
    | exception Out_of_range ->
        fk (Tactics.Failure "Out of range position")

let () =
  T.register_general "fa"
    ~help:"Break function applications on the nth term of the sequence.\
           \n Usage: fa i."
    (function
       | [Prover.Int i] -> pure_equiv (fa i)
       | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))

(** Fresh *)

exception Name_found
exception Var_found


class check_fresh ~(system:Action.system) name = object (self)
 inherit Iter.iter_approx_macros ~exact:false ~system as super

  method visit_term t = match t with
    | EquivSequent.Message e -> self#visit_message e
    | EquivSequent.Formula e -> self#visit_formula e

  method visit_message t = match t with
    | Term.Name (n,_) -> if n = name then raise Name_found
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_name_indices ~system name acc = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~system as super

  val mutable indices : (Vars.index list) list = acc
  method get_indices = indices

  method visit_term t = match t with
    | EquivSequent.Message e -> self#visit_message e
    | EquivSequent.Formula e -> self#visit_formula e

  method visit_message t = match t with
    | Term.Name (n,is) -> if n = name then indices <- is::indices
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

let indices_of_name ~system name acc elems =
  let iter = new get_name_indices ~system name acc in
  iter#visit_term elems ;
  iter#get_indices

let rec mk_inequalities l0 l =
  match l0,l with
  | [hd0],[hd] -> Term.Atom (`Index (`Neq, hd0, hd))
  | hd0::tl0,hd::tl -> Term.And(Term.Atom (`Index (`Neq, hd0, hd)), mk_inequalities tl0 tl)
  | _ -> Term.True

let mk_fresh_cond ~system name indices proj biframe =
  begin try
    let proj_frame = List.map (EquivSequent.pi_elem proj) biframe in
    match indices with
    | [] -> let iter = new check_fresh ~system name in
            List.iter iter#visit_term proj_frame;
            Term.True
    | _  -> let list_of_indices =
              List.fold_left (indices_of_name ~system name) [] proj_frame in
            let list_of_inequalities =
              List.map (mk_inequalities indices) list_of_indices in
            List.fold_left
              (fun acc eq -> Term.And(acc,eq))
              (List.hd list_of_inequalities)
              (List.tl list_of_inequalities)
  with
  | Name_found -> raise @@ Tactics.Tactic_hard_failure
                  (Tactics.Failure "Name not fresh")
  | Var_found -> raise @@ Tactics.Tactic_hard_failure
                 (Tactics.Failure "Variable found, unsound to apply fresh")
  end

let mk_if_term phi_left phi_right n_left ind_left n_right ind_right =
  let then_branch = Term.Fun (Term.f_zero,[]) in
  let else_branch = Term.Diff
    (Term.Name (n_left, ind_left), Term.Name (n_right, ind_right)) in
  match phi_left, phi_right with
  | Term.True, Term.True -> EquivSequent.Message then_branch
  | Term.True, _ ->
      EquivSequent.Message (Term.ITE(phi_right, then_branch, else_branch))
  | _, Term.True ->
      EquivSequent.Message (Term.ITE(phi_left, then_branch, else_branch))
  | _, _ ->
      EquivSequent.Message (Term.ITE(Term.And(phi_left,phi_right),
                            then_branch, else_branch))

let fresh i s sk fk =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        begin try
          let (n_left, ind_left, n_right, ind_right) =
            match EquivSequent.pi_elem Term.Left e, EquivSequent.pi_elem Term.Right e with
            | (EquivSequent.Message Name (nl,isl),
              EquivSequent.Message Name (nr,isr)) -> (nl,isl,nr,isr)
            | _ -> raise @@ Tactics.Tactic_hard_failure
                    (Tactics.Failure "Can only apply fresh on names")
          in
          let biframe = List.rev_append before after in
          let system = (EquivSequent.get_system s) in
          let system_left = Action.(make_trace_system system.left) in
          let phi_left = mk_fresh_cond system_left n_left ind_left Term.Left biframe in
          let system_right = Action.(make_trace_system system.right) in
          let phi_right = mk_fresh_cond system_right n_right ind_right Term.Right biframe in
          let if_term = mk_if_term phi_left phi_right n_left ind_left n_right ind_right in
          let biframe = (List.rev_append before (if_term::after)) in
          sk [EquivSequent.set_biframe s biframe] fk
        with
        | Tactics.Tactic_hard_failure err -> fk err
        end
    | exception Out_of_range ->
        fk (Tactics.Failure "Out of range position")

let () =
  T.register_general "fresh"
    ~help:"Removes a name if fresh.\n Usage: fresh i."
    (function
       | [Prover.Int i] -> pure_equiv (fresh i)
       | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))

let fresh_name_ssc ~system name elems =
  begin try
    let iter = new check_fresh ~system name in
    List.iter iter#visit_term elems ;
    true
  with
  | Name_found | Var_found -> false
  end

let xor i s sk fk =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        begin try
          let (name,xor_terms_left,xor_terms_right) =
            match e with
            | EquivSequent.Message Diff
                (Fun (fl,Term.Name (nl,_)::ll), Fun (fr,Term.Name (nr,_)::lr))
                when (fl = Term.f_xor && fr = Term.f_xor && nl=nr) -> (nl,ll,lr)
            | _ -> raise @@ Tactics.Tactic_hard_failure
                    (Tactics.Failure "Can only apply xor tactic on terms of the form (t1 xor t2)")
          in
          (* the biframe to consider in case of success *)
          let biframe = List.rev_append before after in
          (* the two frames to use for the freshness condition *)
          let frame_left =
            EquivSequent.Message (Fun (Term.f_xor,xor_terms_left))
            ::List.map (EquivSequent.pi_elem Term.Left) biframe in
          let frame_right =
            EquivSequent.Message (Fun (Term.f_xor,xor_terms_right))
            ::List.map (EquivSequent.pi_elem Term.Right) biframe in
          let bisystem = EquivSequent.get_system s in
          if fresh_name_ssc
               Action.(make_trace_system bisystem.left) name frame_left
          then
            if fresh_name_ssc
                 Action.(make_trace_system bisystem.right) name frame_right
            then sk [EquivSequent.set_biframe s biframe] fk
            else raise @@ Tactics.Tactic_hard_failure
              (Tactics.Failure "Name not fresh in the right system")
          else
            raise @@ Tactics.Tactic_hard_failure
              (Tactics.Failure "Name not fresh in the left system")
        with
        | Tactics.Tactic_hard_failure err -> fk err
        end
    | exception Out_of_range ->
        fk (Tactics.Failure "Out of range position")

let () =
  T.register_general "xor"
    ~help:"Removes diff(n XOR u,n XOR v) if n is fresh.\n Usage: xor i."
    (function
       | [Prover.Int i] -> pure_equiv (xor i)
       | _ -> Tactics.hard_failure (Tactics.Failure "Improper arguments"))

let dup i s sk fk =
  match nth i (EquivSequent.get_biframe s) with
  | before, e, after ->
    let biframe = List.rev_append before after in
    let s = EquivSequent.set_biframe s biframe in
    if List.mem e before || List.mem e after
    then
      sk [s] fk
    else begin
      match e with
      | EquivSequent.Message (Term.Macro (input_macro,[],l)) ->
        let test_dup els =
          List.exists
            (function
              | EquivSequent.Message
                  (Term.Macro (frame_macro,[],
                               Term.Pred (Term.Action(n,is))))
              | EquivSequent.Message
                  (Term.Macro (frame_macro,[],Term.Action(n,is))) ->
                begin
                  match l with
                  | Term.Action (n2,is2) ->
                    l = Term.Action (n,is) ||
                    Action.(depends (of_term n2 is2) (of_term n is))
                  | _ -> false
                end
              | _ -> false)
            els
        in
        if test_dup before || test_dup after then
          sk [s] fk
        else
          fk (Tactics.Failure "Dup tactic not applicable")
      | _ -> fk (Tactics.Failure "Dup tactic not applicable")
    end
  | exception Out_of_range ->
    fk (Tactics.Failure "Out of range position")

let () =
  T.register_general "dup"
    ~help:"Removes a duplicated term.\n Usage: dup i."
    (function
       | [Prover.Int i] -> pure_equiv (dup i)
       | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))



let expand_seq (term : Theory.term) (ths:Theory.term list) (s : EquivSequent.t)
    sk fk =
  let env = EquivSequent.get_env s in
  let tsubst = Theory.subst_of_env env in
  match Theory.convert tsubst term Sorts.Message with
  | Seq ( vs, t) ->
    let vs = List.map (fun x -> Vars.EVar x) vs in
    let subst = Theory.parse_subst env vs ths in
    let new_t = EquivSequent.Message (Term.subst subst t) in
    let biframe =
      let old_biframe = EquivSequent.get_biframe s in
      if List.mem new_t old_biframe then old_biframe else new_t :: old_biframe
    in
    let hypo_biframe =
      let old_hyp_biframe = EquivSequent.get_hypothesis_biframe s in
      if List.mem new_t old_hyp_biframe then old_hyp_biframe
      else new_t :: old_hyp_biframe
    in
    sk [ EquivSequent.set_biframe
           (EquivSequent.set_hypothesis_biframe s hypo_biframe)
           biframe] fk
  | _ ->
    Tactics.hard_failure
      (Tactics.Failure "Can only expand with sequences with parameters")
  | exception Theory.(Conv e) ->
      fk (Tactics.Failure  (Fmt.str "%a" Theory.pp_error e))


let expand (term : Theory.term)(s : EquivSequent.t) sk fk =
  let tsubst = Theory.subst_of_env (EquivSequent.get_env s) in
  let succ subst =
    let apply_subst = function
      | EquivSequent.Message e -> EquivSequent.Message (Term.subst subst e)
      | EquivSequent.Formula e -> EquivSequent.Formula (Term.subst subst e)
    in
    sk [EquivSequent.set_biframe s
          (List.map apply_subst (EquivSequent.get_biframe s))] fk
  in
  match Theory.convert tsubst term Sorts.Boolean with
    | Macro ((mn, sort, is),l,a) ->
      succ [Term.ESubst (Macro ((mn, sort, is),l,a),
                         Macros.get_definition
                           (EquivSequent.get_system s) sort mn is a)]
    | _ ->
      Tactics.hard_failure (Tactics.Failure "Can only expand macros")
    | exception Theory.(Conv (Type_error _)) ->
      begin
        match Theory.convert tsubst term Sorts.Message with
        | Macro ((mn, sort, is),l,a) ->
          succ [Term.ESubst (Macro ((mn, sort, is),l,a),
                             Macros.get_definition
                               (EquivSequent.get_system s) sort mn is a)]
        | _ ->
          Tactics.hard_failure (Tactics.Failure "Can only expand macros")
        | exception Theory.(Conv e) ->
          fk (Tactics.Failure  (Fmt.str "%a" Theory.pp_error e))
      end
    | exception Theory.(Conv e) ->
          fk (Tactics.Failure  (Fmt.str "%a" Theory.pp_error e))

let () = T.register_general "expand"
    ~help:"Expand all occurences of the given macro, or expand the given \
           sequence using the given indices.\
           \n Usage: expand macro. expand seq(i,k...->t(i,k,...),i1,k1,..."
    (function
      | [Prover.Theory v] -> pure_equiv (expand v)
      | (Prover.Theory v)::ids ->
          let ids =
            List.map
              (function
                 | Prover.Theory th -> th
                 | _ -> raise @@ Tactics.hard_failure
                     (Tactics.Failure "improper arguments"))
              ids
          in
        pure_equiv (expand_seq v ids)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))

let equiv t1 t2 (s : EquivSequent.t) sk fk =
  let env = EquivSequent.get_env s in
  let system = EquivSequent.get_system s in
  let tsubst = Theory.subst_of_env env in
  match Theory.convert tsubst t1 Sorts.Boolean,
        Theory.convert tsubst t2 Sorts.Boolean with
  | t1,t2 ->
    let trace_sequent =
        TraceSequent.init ~system
          (Term.And(Term.Impl(t1, t2), Term.Impl(t2, t1)))
          |> TraceSequent.set_env env
      in
      let subgoals =
        [ Prover.Goal.Trace trace_sequent;
          Prover.Goal.Equiv
            (EquivSequent.apply_subst [Term.ESubst(t1, t2)] s) ]
      in
      sk subgoals fk
  | exception (Theory.Conv e) ->
      Tactics.soft_failure
        (Tactics.Failure
           (Fmt.str "%a" Theory.pp_error e))

let () = T.register_general "equivalent"
    ~help:"Replace all occurences of a formula by another, and ask to prove \
           \n that they are equivalent.
           \n Usage: equiv t1, t2."
    (function
       | [Prover.Theory v1; Prover.Theory v2] -> only_equiv (equiv v1 v2)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))


let no_if i s sk fk =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
      begin try
          let cond, negative_branch =
            match e with
            | EquivSequent.Message ITE (c,t,e) -> (c, EquivSequent.Message e)
            | _ -> raise @@ Tactics.Tactic_hard_failure
                (Tactics.Failure "improper arguments")
          in
          let biframe = List.rev_append before (negative_branch :: after) in
          let env = EquivSequent.get_env s in
          let system = EquivSequent.get_system s in
          let trace_sequent = TraceSequent.init ~system
              (Term.Impl(cond,False))
                                   |> TraceSequent.set_env env
           in
           sk [Prover.Goal.Trace trace_sequent;
               Prover.Goal.Equiv (EquivSequent.set_biframe s biframe)] fk
        with
          | Tactics.Tactic_soft_failure err -> fk err
        end
    | exception Out_of_range ->
        fk (Tactics.Failure "Out of range position")
let () =
  T.register_general "noif"
    ~help:"Try to prove diff equivalence by proving that the condition at the \
           \n i-th position implies False.\
           \n Usage: noif i."
    (function
       | [Prover.Int i] -> only_equiv (no_if i)
       | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))
