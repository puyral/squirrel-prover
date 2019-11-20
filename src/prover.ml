open Logic
open Term

(** State in proof mode.
  * TODO goals do not belong here *)

type named_goal = string * formula

let goals : named_goal list ref = ref []
let current_goal : named_goal option ref = ref None
let subgoals : Judgment.t list ref = ref []
let goals_proved = ref []

type prover_mode = InputDescr | GoalMode | ProofMode | WaitQed

type gm_input =
  | Gm_goal of string * Term.formula
  | Gm_proof


exception Cannot_undo

type proof_state = { goals : named_goal list;
                     current_goal : named_goal option;
                     subgoals : Judgment.t list;
                     goals_proved : named_goal list;
                     cpt_tag : int;
                     prover_mode : prover_mode;
                   }

let proof_states_history : proof_state list ref = ref []

let save_state mode =
  proof_states_history :=
    {goals = !goals;
     current_goal = !current_goal;
     subgoals = !subgoals;
     goals_proved = !goals_proved;
     cpt_tag = !cpt_tag;
     prover_mode = mode } :: (!proof_states_history)

let rec reset_state n =
  match (!proof_states_history,n) with
  | [],_ -> raise Cannot_undo
  | p::q,0 ->
    proof_states_history := q;
    goals := p.goals;
    current_goal := p.current_goal;
    subgoals := p.subgoals;
    goals_proved := p.goals_proved;
    cpt_tag := p.cpt_tag;
    p.prover_mode
  | p::q, n -> proof_states_history := q; reset_state (n-1)

(** Tactic expressions and their evaluation *)

(* TODO some of this (generalized) should go to Tactics
 *   type 'a tac for tactic expressions with atoms of type 'a
 *   type string tac could be printed
 *   type ('a Tactics.tac) tac could be evaluated
 *   problem: apply (and other tactics with arguments) make the
 *   general treatment difficult
 *   solution: a general notion of tactic args and associated syntax ? *)

type tac =
  | Admit : tac
  | Ident : tac

  | NoSimp : tac -> tac
  | Left : tac
  | Right : tac
  | Intro : tac
  | Split : tac

  | Apply : (string * subst) -> tac
  | Assert : Term.fact -> tac

  | ForallIntro : tac
  | ExistsIntro : subst -> tac
  | AnyIntro : tac

  | GammaAbsurd : tac
  | ConstrAbsurd : tac

  | Assumption : tac

  | EqNames : tac
  | EqTimestamps : tac
  | EqConstants : fname -> tac

  (* | UProveAll : utac -> utac *)
  | AndThen : tac * tac -> tac
  | OrElse : tac * tac -> tac
  | Try : tac * tac -> tac
  | Repeat : tac -> tac

  | Euf : int -> tac
  | CollisionResistance : tac
  | Cycle : int -> tac

let rec pp_tac : Format.formatter -> tac -> unit =
  fun ppf tac -> match tac with
    | Admit -> Fmt.pf ppf "admit"
    | Ident -> Fmt.pf ppf "ident"
    | NoSimp t -> Fmt.pf ppf "no simplification for %a" pp_tac t
    | Left -> Fmt.pf ppf "goal_or_intro_l"
    | Right -> Fmt.pf ppf "goal_or_intro_r"
    | Intro -> Fmt.pf ppf "goal_intro"
    | Split -> Fmt.pf ppf "goal_and_intro"

    | Apply (s, t) ->
        if t = [] then
          Fmt.pf ppf "apply %s" s
        else
          Fmt.pf ppf "apply %s to .." s
    | Assert f ->
        Fmt.pf ppf "assert %a" Term.pp_fact f

    | ForallIntro -> Fmt.pf ppf "forall_intro"
    | ExistsIntro (nu) ->
      Fmt.pf ppf "@[<v 2>exists_intro@;%a@]"
        pp_subst nu
    | AnyIntro -> Fmt.pf ppf "any_intro"
    | GammaAbsurd -> Fmt.pf ppf "gamma_absurd"
    | ConstrAbsurd -> Fmt.pf ppf "constr_absurd"

    | Assumption -> Fmt.pf ppf "assumption"

    | EqNames -> Fmt.pf ppf "eq_names"
    | EqTimestamps -> Fmt.pf ppf "eq_timestamps"
    | EqConstants fn -> Fmt.pf ppf "eq_constants %a" pp_fname fn

    (* | ProveAll utac -> Fmt.pf ppf "apply_all(@[%a@])" pp_tac utac *)
    | AndThen (ut, ut') ->
      Fmt.pf ppf "@[%a@]; @,@[%a@]" pp_tac ut pp_tac ut'
    | OrElse (ut, ut') ->
      Fmt.pf ppf "@[%a@] + @,@[%a@]" pp_tac ut pp_tac ut'
    | Try (ut, ut') ->
      Fmt.pf ppf "try@[%a@] orelse @,@[%a@]" pp_tac ut pp_tac ut'
    | Repeat t ->
      Fmt.pf ppf "repeat @[%a@]]" pp_tac t
    (* | TacPrint ut -> Fmt.pf ppf "@[%a@].@;" pp_tac ut *)

    | Euf i -> Fmt.pf ppf "euf %d" i
    | CollisionResistance -> Fmt.pf ppf "collision resistance"
    | Cycle i -> Fmt.pf ppf "cycle %d" i

let rec tac_apply :
  type a.
  tac -> Judgment.t ->
  (Judgment.t list, a) Tactics.sk ->
  a Tactics.fk -> a
=
  let open Tactics in
  fun tac judge sk fk -> match tac with
    | Admit -> sk [Judgment.set_formula Unit judge] fk
    | Ident -> sk [judge] fk
    | NoSimp tac -> tac_apply tac judge sk fk
    | ForallIntro -> goal_forall_intro judge sk fk
    | ExistsIntro (nu) -> goal_exists_intro nu judge sk fk
    | AnyIntro -> goal_any_intro judge sk fk
    | Apply (gname, s) ->
        let f =
          match
            List.filter (fun (name,g) -> name = gname) !goals_proved
          with
            | [(_,f)] -> f
            | [] -> raise @@ Failure "No proved goal with given name"
            | _ -> raise @@ Failure "Multiple proved goals with the same name"
        in
        apply f s judge sk fk
    | Assert f -> tac_assert f judge sk fk
    | Left -> goal_or_intro_l judge sk fk
    | Right -> goal_or_intro_r judge sk fk
    | Split -> goal_and_intro judge sk fk
    | Intro -> goal_intro judge sk fk

    | GammaAbsurd -> gamma_absurd judge sk fk
    | ConstrAbsurd -> constr_absurd judge sk fk

    | Assumption -> assumption judge sk fk

    | EqNames -> eq_names judge sk fk
    | EqTimestamps -> eq_timestamps judge sk fk
    | EqConstants fn -> eq_constants fn judge sk fk
    | Euf i ->
      let f_select _ t = t.cpt = i in
      euf_apply f_select judge sk fk

    (* | ProveAll tac -> prove_all judge (tac_apply gt tac) sk fk *)
    | CollisionResistance -> collision_resistance judge sk fk
    | AndThen (tac,tac') ->
      tact_andthen
        (tac_apply tac)
        (tac_apply tac')
        judge sk fk

    | OrElse (tac,tac') ->
      tact_orelse (tac_apply tac) (tac_apply tac') judge sk fk

    (* Try is just syntactic sugar *)
    | Try (tac,tac') ->
      tac_apply (OrElse(tac,Ident)) judge sk fk

    | Repeat tac ->
      repeat (tac_apply tac) judge sk fk
    | Cycle _ -> assert false   (* This is not a focused tactic. *)

    (* | TacPrint tac ->
     *   Fmt.pr "%a @[<hov 0>%a@]@;%!"
     *     (Fmt.styled `Bold ident) "Tactic:" pp_tac tac;
     *   tac_apply gt tac judge (fun judge fk ->
     *       Fmt.pr "%a%!" (Judgment.pp_judgment (pp_gt_el gt)) judge;
     *       sk judge fk)
     *     fk *)

let simpGoal =
  AndThen(Repeat AnyIntro,
          AndThen(EqNames,
                  AndThen(EqTimestamps,
                          AndThen(Try(GammaAbsurd,Ident),
                                  Try(ConstrAbsurd,Ident)))))

exception Tactic_Soft_Failure of string

(** The evaluation of a tactic, may either raise a soft failure or a hard
    failure (cf tactics.ml). A soft failure should be formatted inside the
    Tactic_soft_failure exception.
    A hard failure inside Tactic_hard_failure. Those exceptions are catched
    inside the interactive loop. *)
let eval_tactic_judge : tac -> Judgment.t -> Judgment.t list = fun tac judge ->
  (* the failure should raise the soft failure, according to [pp_tac_error] *)
  let failure_k tac_error =
    raise @@ Tactic_Soft_Failure (Fmt.strf "%a" Tactics.pp_tac_error tac_error )
  in
  let suc_k judges _ =
    judges
  in
     tac_apply tac judge suc_k failure_k

let auto_simp judges =
  List.map Tactics.simplify judges
  |> Tactics.remove_finished
  |> List.map (eval_tactic_judge simpGoal)
  |> List.flatten
  |> List.map Tactics.simplify
  |> Tactics.remove_finished

let tsubst_of_judgment j =
  List.map
    (fun v ->
       match Vars.var_type v with
       | Vars.Index -> Theory.Idx (Vars.name v,v)
       | Vars.Timestamp -> Theory.TS (Vars.name v,TVar v)
       | Vars.Message -> Theory.Term (Vars.name v,MVar v)
    )
    (Vars.to_list j.Judgment.env)

let parse_fact fact =
  match !subgoals with
    | [] -> failwith "Cannot parse fact without a goal"
    | j::_ ->
        Theory.convert_fact_glob (tsubst_of_judgment j) fact

let parse_subst j uvars ts : subst =
          let u_subst = tsubst_of_judgment j in
          List.map2 (fun t u ->
              match Vars.var_type u with
              | Vars.Timestamp -> TS (TVar u, Theory.convert_ts u_subst t )
              | Vars.Message -> Term (MVar u, Theory.convert_glob u_subst t)
              | Vars.Index -> Index (u, Theory.conv_index u_subst t)
          ) ts uvars

let parse_args goalname ts : subst =
  let goals = List.filter (fun (name,g) -> name = goalname) !goals_proved in
  match goals with
  | [] ->  raise @@ Failure "No goal with given name"
  | [(np, gp)] ->
      begin
      let uvars = gp.uvars in
      if (List.length uvars) <> (List.length ts) then
        raise @@ Failure "Number of parameters different than expected";
      match !subgoals with
      | [] ->
          raise @@
          Failure "Cannot parse term with respect to empty current goal"
      |  j :: _ -> parse_subst j uvars ts
      end
  | _ ->  raise @@ Failure "Multiple proved goals with same name"

let parse_args_exists ts : subst =
  match !subgoals with
  | [] ->
    raise @@
    Failure "Cannot parse term with respect to empty current goal"
  |  j :: _ -> match j.Judgment.formula with
    | Postcond p -> parse_subst j p.evars ts
    | _ -> raise @@ Failure "Cannot parse term for existential intro which does
not exists"


(** Declare Goals And Proofs *)

type args = (string * Theory.kind) list

let make_goal ((uargs,uconstr), (eargs,econstr), ufact, efact) =
  (* In the rest of this function, the lists need to be reversed and appended
     carefully to properly handle variable shadowing.  *)
  let env = ref (Vars.empty_env ()) in
  List.iter (fun (s,k) -> Theory.check_rebound_symbol s) (uargs@eargs);
  let (u_subst, ufvars) = Theory.convert_vars env uargs
  and (e_subst, efvars) = Theory.convert_vars env eargs in
  let uconstr =
    Theory.convert_constr_glob
      (List.rev uargs)
      u_subst
      uconstr in
  let ufact =
    Theory.convert_fact_glob
      u_subst
      ufact in

  let econstr =
    Theory.convert_constr_glob
      (List.rev_append eargs (List.rev uargs))
      (e_subst @ u_subst)
      econstr in
  let efact =
    Theory.convert_fact_glob
      (e_subst @ u_subst)
      efact in

  { uvars = ufvars;
    uconstr = uconstr;
    ufact = ufact;
    postcond = [{ evars = efvars;
                  econstr = econstr;
                  efact = efact }] }

type parsed_input =
  | ParsedInputDescr
  | ParsedQed
  | ParsedTactic of tac
  | ParsedUndo of int
  | ParsedGoal of gm_input
  | EOF

let add_new_goal g = goals := g :: !goals

let add_proved_goal g = goals_proved := g :: !goals_proved

let iter_goals f = List.iter f !goals

(** Pretty-print goals. This is currently unused. *)
let pp_goals ppf () =
  let cpt = ref 0 in
  Fmt.pf ppf "@[<v>";
  iter_goals (fun (gname,goal) ->
    Fmt.pf ppf "@[<v>%d: @[@[%a@]@;@]@]@;"
      !cpt Term.pp_formula goal ;
    incr cpt) ;
  Fmt.pf ppf "@]%!@."

let goals_to_proved () = !goals <> []

let is_proof_completed () = !subgoals = []

let complete_proof () =
  assert (is_proof_completed ());
  try
    add_proved_goal (Utils.opt_get !current_goal);
    current_goal := None;
    subgoals := []
  with Not_found ->  raise @@ Tactics.Tactic_Hard_Failure "Cannot complete proof
with empty current goal"

let pp_goal ppf () = match !current_goal, !subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf ppf "@[<v 0>[goal> No subgoals remaining.@]@."
  | Some _, j :: _ ->
    Fmt.pf ppf "@[<v 0>[goal> Focused goal (1/%d):@;%a@;@]"
      (List.length !subgoals)
      Judgment.pp_judgment j
  | _ -> assert false

(** [eval_tactic_focus tac] applies [tac] to the focused goal.
  * @return [true] if there are no subgoals remaining. *)
let eval_tactic_focus : tac -> bool = fun tac -> match !subgoals with
  | [] -> assert false
  | judge :: ejs' ->
    let new_j =  (eval_tactic_judge tac judge) in
    let ejs =  (match tac with
      | NoSimp t -> new_j
      | _ -> auto_simp new_j) @ ejs' in
      subgoals := ejs;
      is_proof_completed ()

let cycle i l =
  let rec cyc acc i = function
    | [] -> raise @@ Tactics.Tactic_Hard_Failure "Cycle error."
    | a :: l ->
      if i = 1 then l @ (List.rev (a :: acc))
      else cyc (a :: acc) (i - 1) l in
  if i = 0 then l else
  if i < 0 then cyc [] (List.length l + i) l
  else cyc [] i l

let eval_tactic : tac -> bool = fun utac -> match utac with
  | Cycle i -> subgoals := cycle i !subgoals; false
  | _ -> eval_tactic_focus utac


let start_proof () = match !current_goal, !goals with
  | None, (gname,goal) :: _ ->
    assert (!subgoals = []);
    cpt_tag := 0;
    current_goal := Some (gname,goal);
    subgoals := auto_simp [Judgment.init goal];
    None
  | Some _,_ ->
    Some "Cannot start a new proof (current proof is not done)."

  | _, [] ->
    Some "Cannot start a new proof (no goal remaining to prove)."
