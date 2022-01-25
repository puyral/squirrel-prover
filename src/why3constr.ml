(* Useful auxiliary function? *)
let cast_evar_option kind ev =
  try Some (Vars.ecast ev kind)
  with Vars.CastError -> None

let filter_cast (kind : 'a Type.kind) (evars : Vars.evars) : 'a Vars.var list =
  List.filter_map (cast_evar_option kind) evars

let get_smt_setup
  : unit -> (Why3.Theory.theory * Why3.Whyconf.config_prover * Why3.Driver.driver) option =
  let mem = ref None in
  fun () -> match !mem with
    | Some _ as x -> x
    | None -> begin
        (* Setup following http://why3.lri.fr/doc/api.html *)
        let config = Why3.Whyconf.init_config None in
        (* builds the environment from the [loadpath]
         * theory_dir taken from the code of Main.mk_load_paths *)
        let env =
          let exec_dir = Filename.dirname Sys.executable_name in
          Why3.Env.create_env (Filename.(concat exec_dir "theories") ::
                               Why3.Whyconf.(loadpath (get_main config))) in
        let exception Load_driver_fails in
        try
          let tm_theory =
            Why3.Env.read_theory env ["trace_model_int"] "Trace_model" in
          let alt_ergo =
            snd Why3.Whyconf.(Mprover.max_binding
                                (filter_provers config
                                   (parse_filter_prover "Alt-Ergo"))) in
          try
            let result =
              Some (tm_theory, alt_ergo,
                    Why3.Whyconf.(load_driver (get_main config) env alt_ergo)) in
            mem := result;
            result
          with e ->
            Format.printf "smt: Alt-Ergo driver failed to load: %a@.\n"
              Why3.Exn_printer.exn_printer e; None
        with
        | Not_found -> (* may be raised by max_binding *)
          Format.printf "smt: Alt-Ergo prover not found\n"; None
        | Why3.Env.LibraryConflict _ | Why3.Env.LibraryNotFound _
        | Why3.Env.AmbiguousPath   _ | Why3.Env.TheoryNotFound  _ ->
          Format.printf "smt: error while loading SMT theory file\n"; None
      end

let run_prover ?limit_opt task =
  let limit = match limit_opt with
    | None   -> Config.solver_timeout ()
    | Some x -> x
  in
  Utils.omap (fun (env, prover, driver) ->
      Why3.Call_provers.wait_on_call
        (Why3.Driver.prove_task
           ~limit:{ Why3.Call_provers.empty_limit with limit_time = limit }
           ~command:prover.Why3.Whyconf.command
           driver task))
    (get_smt_setup ())


let mk_const_symb x ty_symb =
  Why3.Term.create_fsymbol (Why3.Ident.id_fresh x) [] (Why3.Ty.ty_app ty_symb [])

exception Unsupported

(** this is called [build_task_bis] because there was another build_task
 ** previously that just handled the theory of timestamps / actions
 ** (i.e. "constraints" tactic + dependencies) *)

let build_task_bis
    (table       : Symbols.table)
    (system      : SystemExpr.t)
    (evars       : Vars.evar list)
    (msg_atoms   : Term.message_atom list)
    (trace_lits  : Term.trace_literal list)
    (given_axioms: Term.message list)
    (tm_theory   : Why3.Theory.theory)
  : Why3.Task.task =
  let tm_export = tm_theory.Why3.Theory.th_export in

  let index_symb   = Why3.Theory.ns_find_ts tm_export ["index"] in
  let action_symb  = Why3.Theory.ns_find_ts tm_export ["action"] in
  let msg_symb     = Why3.Theory.ns_find_ts tm_export ["message"] in
  let ts_symb      = Why3.Theory.ns_find_ts tm_export ["timestamp"] in
  let ilist_symb   = Why3.Theory.ns_find_ts tm_export ["ilist"] in

  let eqv_symb     = Why3.Theory.ns_find_ls tm_export ["infix ~~"] in
  let leq_symb     = Why3.Theory.ns_find_ls tm_export ["infix <~"] in
  let happens_symb = Why3.Theory.ns_find_ls tm_export ["happens"] in
  let init_symb    = Why3.Theory.ns_find_ls tm_export ["init"] in
  let act_symb     = Why3.Theory.ns_find_ls tm_export ["act"] in
  let pred_symb    = Why3.Theory.ns_find_ls tm_export ["pred"] in

  let cons_symb    = Why3.Theory.ns_find_ls tm_export ["Cons"] in
  let nil_symb     = Why3.Theory.ns_find_ls tm_export ["Nil"] in

  let xor_symb     = Why3.Theory.ns_find_ls tm_export ["xoxo"] in

  let msg_is_true_symb = Why3.Theory.ns_find_ls tm_export ["msg_is_true"] in
  let macro_cond_symb  = Why3.Theory.ns_find_ls tm_export ["macro_cond"] in
  let macro_exec_symb  = Why3.Theory.ns_find_ls tm_export ["macro_exec"] in

  (** TODO copy/pasted from trace_literals_unsat (+ msgvars) **)
  let indices = filter_cast Type.KIndex     evars
  and tsvars  = filter_cast Type.KTimestamp evars
  and msgvars = filter_cast Type.KMessage   evars in

  (* We first create Why3 constants for all action/index/timestamp names that appear
   * TODO: check that our conversions var/symbol -> string avoids spurious collisions *)
  (* NOTE: latest change: while action_tbl contains symbols (that can be applied),
   *       the other tables now contain terms e.g. t_app_infer symbol []
   *       (so they can be obtained from either constants or variables) *)
  let actions_tbl    = Hashtbl.create 12
  and indices_tbl    = Hashtbl.create (List.length indices)
  and timestamps_tbl = Hashtbl.create (List.length tsvars)
  and messages_tbl   = Hashtbl.create (List.length msgvars) in
  let action_iter = SystemExpr.iter_descrs table system in
  action_iter (fun descr ->
      (* need to handle init as special case *)
      if descr.name <> Symbols.init_action
      then let str = Symbols.to_string descr.name in
        Hashtbl.add actions_tbl str (mk_const_symb str action_symb)
    );
  (* use declaration for trace model theory + constant declarations for actions *)
  let task_header = ref (Why3.Task.use_export None tm_theory
                         |> Hashtbl.fold (fun _ symb task ->
                             Why3.Task.add_param_decl task symb) actions_tbl) in
  (* only add the init action now! so that it doesn't get declared twice *)
  Hashtbl.add actions_tbl Symbols.(to_string init_action) init_symb;

  let add_tbl_var tbl tysymb var =
    let str = Vars.name var in
    let symb = mk_const_symb str tysymb in
    Hashtbl.add tbl str (Why3.Term.t_app_infer symb []);
    (* update task header here, the only place where the function symbol
     * (rather than the constant term) is used
     * -> this will declare all sequent toplevel variables as constants in the task *)
    task_header := Why3.Task.add_param_decl !task_header symb
  in
  List.iter (add_tbl_var indices_tbl    index_symb) indices;
  List.iter (add_tbl_var timestamps_tbl ts_symb)    tsvars;
  List.iter (add_tbl_var messages_tbl   msg_symb)   msgvars;

  (* Next, say that all actions are distinct *)
  let distinct_actions_axioms = Hashtbl.fold (fun k a acc ->
      Hashtbl.fold (fun k' a' acc' ->
          if k < k'
          then Why3.Term.(t_neq (t_app_infer a []) (t_app_infer a' [])) :: acc'
          else acc'
        ) actions_tbl acc
    ) actions_tbl [] in

  (* Add axioms for action dependencies to above mutable list *)
  (* "depends" function from action.ml but weakened *)
  let eq_actitem a b =
    (* TODO: this is a terrible hack (sound but in principle incomplete),
     * the "right" way would be to handle variable renaming *)
    let open Action in
    let (x1, l1) = a.par_choice and (x2, l2) = b.par_choice
    and (y1, m1) = a.sum_choice and (y2, m2) = b.sum_choice in
    x1 = x2 && y1 = y2 &&
    List.map Vars.name l1 = List.map Vars.name l2 &&
    List.map Vars.name m1 = List.map Vars.name m2
  in
  let rec depends a b = match a, b with
    | [], _::_ -> true
    | hda::tla, hdb::tlb when eq_actitem hda hdb -> depends tla tlb
    | _ -> false
  in
  action_iter (fun descr1 -> action_iter (fun descr2 ->
      if descr1.name <> Symbols.init_action &&
         depends descr1.action descr2.action then (
        let action_indices = Hashtbl.create (List.length descr2.indices) in
        (* assume that all variables must occur in 2nd action *)
        let quantified_vars = descr2.indices |> List.map (fun i ->
            let str   = Vars.name i in
            let vsymb = Why3.(Term.create_vsymbol (Ident.id_fresh str)
                                (Ty.ty_app index_symb [])) in
            Hashtbl.add action_indices str vsymb;
            vsymb
          ) in
        let list_of_list (l : Vars.index list) : Why3.Term.term =
          let open Why3.Term in
          List.fold_right (fun i acc ->
              t_app_infer cons_symb
                [t_var (Hashtbl.find action_indices (Vars.name i)); acc]
            ) l (t_app_infer nil_symb [])
        in
        let f (d : Action.descr) =
          let symb = Hashtbl.find actions_tbl (Symbols.to_string d.name) in
          Why3.Term.t_app_infer act_symb [Why3.Term.t_app_infer symb [];
                                          list_of_list d.indices]
        in
        (* 1 <~ 2 **when 2 happens** *)
        let axiom = let open Why3.Term in
          t_app_infer leq_symb [f descr1; f descr2]
          |> t_implies (t_app_infer happens_symb [f descr2])
          |> t_forall_close quantified_vars [] in
        task_header := Why3.Task.add_prop_decl !task_header Why3.Decl.Paxiom
            (Why3.Decl.create_prsymbol @@ Why3.Ident.id_fresh "axiom_depends")
            axiom;
      )));
  let task_header   = !task_header in
  let functions_tbl = Hashtbl.create 12
  and macros_tbl    = Hashtbl.create 12
  and names_tbl     = Hashtbl.create 12 in
  let msg_ty   = Why3.Ty.ty_app msg_symb   []
  and ts_ty    = Why3.Ty.ty_app ts_symb    []
  and ilist_ty = Why3.Ty.ty_app ilist_symb [] in
  Symbols.Function.iter (fun fname (ftype, _) _ ->
      if fname <> Symbols.fs_xor then
        (* special treatment of xor for two reasons:
         *   - id_fresh doesn't avoid the "xor" why3 keyword (why3 api bug?)
         *   - allows us to declare the equations for xor in the .why file *)
        let str = Symbols.to_string fname in
        let symb = Why3.Term.create_fsymbol
            (Why3.Ident.id_fresh str)
            (ilist_ty :: List.map (fun _ -> msg_ty) ftype.fty_args)
            (* the arguments of the function symbol are a list of indices
             * + several messages (above), and it returns a message (below) *)
            msg_ty in
        (* Format.printf "registering function %s with %d index params and %d message params\n"
         *   str ftype.fty_iarr (List.length ftype.fty_args); *)
        Hashtbl.add functions_tbl str symb
    ) table;
  Symbols.Macro.iter (fun mn _ _ ->
      let str = Symbols.to_string mn in
      let symb = Why3.Term.create_fsymbol (Why3.Ident.id_fresh str)
          [ilist_ty ; ts_ty] msg_ty in
      Hashtbl.add macros_tbl str symb
    ) table;
  Symbols.Name.iter (fun name _ _ ->
      let str = Symbols.to_string name in
      let symb = Why3.Term.create_fsymbol (Why3.Ident.id_fresh str)
          [ilist_ty] msg_ty in
      Hashtbl.add names_tbl str symb
    ) table;
  let add_all_symbols tbl =
    Hashtbl.fold (fun _ symb task -> Why3.Task.add_param_decl task symb) tbl
  in
  let task_header = task_header
                    |> add_all_symbols functions_tbl
                    |> add_all_symbols macros_tbl
                    |> add_all_symbols names_tbl in
  let open Why3.Term in
  let index_to_wterm i =
    Hashtbl.find indices_tbl (Vars.name i)
  in
  let rec ilist_to_wterm = function
    | []    -> t_app_infer nil_symb []
    | i::is -> t_app_infer cons_symb [index_to_wterm i; ilist_to_wterm is]
  in
  let rec timestamp_to_wterm = function
    | Term.Pred ts -> t_app_infer pred_symb [timestamp_to_wterm ts]
    | Term.Action (a, indices) -> t_app_infer act_symb [
        t_app_infer (Hashtbl.find actions_tbl (Symbols.to_string a)) [];
        ilist_to_wterm indices
      ]
    | Var v -> Hashtbl.find timestamps_tbl (Vars.name v)
    | Diff (_, _) -> failwith "diff of timestamps to why3 term not implemented"
    (* TODO doesn't seem necessary? *)
  in
  let trace_atom_to_fmla = function
    | `Timestamp (comp,ts1,ts2) ->
      let listargs = List.map timestamp_to_wterm [ts1; ts2] in
      begin match comp with
        | `Eq  -> t_app_infer eqv_symb listargs
        | `Neq -> t_not (t_app_infer eqv_symb listargs)
        | `Leq -> t_app_infer leq_symb listargs
        | `Geq -> t_app_infer leq_symb (List.rev listargs)
        | `Lt  -> t_and (t_app_infer leq_symb listargs)
                    (t_not @@ t_app_infer eqv_symb listargs)
        | `Gt  -> let listargs = List.rev listargs in
          t_and (t_app_infer leq_symb listargs)
            (t_not @@ t_app_infer eqv_symb listargs)
      end
    | `Index (`Eq,  i1, i2) ->        t_equ (index_to_wterm i1) (index_to_wterm i2)
    | `Index (`Neq, i1, i2) -> t_not (t_equ (index_to_wterm i1) (index_to_wterm i2))
    | `Happens ts -> Why3.Term.t_app_infer happens_symb [timestamp_to_wterm ts]
  in
  let trace_lit_to_fmla = function
    | (`Pos, x) ->        trace_atom_to_fmla x
    | (`Neg, x) -> t_not (trace_atom_to_fmla x)
  in
  let find_fn f = Hashtbl.find functions_tbl (Symbols.to_string f) in
  (* in the function below I guess t_app_infer invokes the Why3 typechecker
   * to ensure that messages and timestamps are not mixed up
   * but this is not reflected in our OCaml types
   * the function subsumes timestamp_to_wterm from build_task (constraints) *)
  let rec msg_to_wterm : Term.message -> Why3.Term.term = fun c ->
    let open Term in
    let open Why3.Term in
    (* TODO lots of t_app_infer + Hashtbl.find + Symbols.to_string
     *      -> factor into common utility function *)
    match c with (* cases taken from Completion.cterm_of_term *)
    | Fun ((f,is),_,terms) -> begin match terms with
        | [t1; t2] when f = Symbols.fs_xor ->
          t_app_infer xor_symb [msg_to_wterm t1; msg_to_wterm t2]
        | [cond; t1; t2] when f = Symbols.fs_ite ->
          (* hard-coded special case for if-then-else
           * the benefit is not just to use the "native" why3 conditional
           * but also to translate the condition into a formula (this avoids the
           *  need for a conversion from atoms to why3 terms of type message) *)
          t_if (msg_to_fmla cond) (msg_to_wterm t1) (msg_to_wterm t2)
        | _ ->  t_app_infer (find_fn f) (ilist_to_wterm is
                                         :: List.map msg_to_wterm terms)
      end

    | Macro (ms,l,ts) ->
      assert (l = []);
      t_app_infer
        (Hashtbl.find macros_tbl (Symbols.to_string ms.s_symb))
        [ilist_to_wterm ms.s_indices; timestamp_to_wterm ts]

    | Name ns ->
      t_app_infer
        (Hashtbl.find names_tbl (Symbols.to_string ns.s_symb))
        [ilist_to_wterm ns.s_indices]

    | Diff(c,d) ->
      t_app_infer
        (find_fn Symbols.fs_diff)
        [ilist_to_wterm []; msg_to_wterm c; msg_to_wterm d]

    | Var v -> Hashtbl.find messages_tbl (Vars.name v)

    | Atom a ->
      Format.printf "TODO: handle atoms as messages properly\n";
      (* maybe using msg_atom_to_fmla below *)
      raise Unsupported

    | _ ->  Format.printf "%s\n" begin match c with
        | Fun  _ -> "fun"
        | Name _ -> "name"
        | Macro _ -> "macro"
        | Seq _ -> "seq"
        | Var _ -> "var"
        | Diff _ -> "diff"
        | Find _ -> "find"
        | Atom _ -> "atom"
        | ForAll _ -> "forall"
        | Exists _ -> "exists"
      end;
      raise Unsupported

  and msg_atom_to_fmla = function
    | `Message (`Eq,  m1, m2) -> t_equ (msg_to_wterm m1) (msg_to_wterm m2)
    | `Message (`Neq, m1, m2) -> t_neq (msg_to_wterm m1) (msg_to_wterm m2)

  and msg_to_fmla fmla =
    (* TODO: there has to be a better way to write this sequence of destrs... *)
    match Term.destr_false fmla with
    | Some () -> t_false
    | None -> match Term.destr_true fmla with
      | Some () -> t_true
      | None -> match Term.destr_not fmla with
        | Some f -> t_not (msg_to_fmla f)
        | None -> match Term.destr_and fmla with
          | Some (f1, f2) -> t_and (msg_to_fmla f1) (msg_to_fmla f2)
          | None -> match Term.destr_or fmla with
            | Some (f1, f2) -> t_or (msg_to_fmla f1) (msg_to_fmla f2)
            | None -> match Term.destr_impl fmla with
              | Some (f1, f2) -> t_implies (msg_to_fmla f1) (msg_to_fmla f2)
              | None -> match Term.destr_forall fmla with
                | Some (vs, f) -> msg_to_fmla_q t_forall_close vs f
                | None -> match Term.destr_exists fmla with
                  | Some (vs, f) -> msg_to_fmla_q t_exists_close vs f
                  | None -> match fmla with
                    | Atom (#Term.message_atom as at) ->   msg_atom_to_fmla at
                    | Atom (#Term.trace_atom   as at) -> trace_atom_to_fmla at
                    | Macro (ms,[],ts) when ms.s_symb = Symbols.cond ->
                      t_app_infer macro_cond_symb [timestamp_to_wterm ts]
                    | Macro (ms,[],ts) when ms.s_symb = Symbols.exec ->
                      t_app_infer macro_exec_symb [timestamp_to_wterm ts]
                    | x -> t_app_infer msg_is_true_symb [msg_to_wterm x]
  and msg_to_fmla_q quantifier vs f =
    let i_vs = filter_cast Type.KIndex     vs
    and t_vs = filter_cast Type.KTimestamp vs
    and m_vs = filter_cast Type.KMessage   vs in
    (* NOTE: here we use the fact that OCaml hashtables can have multiple
     *       bindings, and the newer ones shadow the older ones
     * thus we can use Hashtbl.(add|remove) to handle bound variable scope *)
    let create_var symb tbl v =
      let str = Vars.name v in
      let vsymb =
        create_vsymbol (Why3.Ident.id_fresh str) (Why3.Ty.ty_app symb []) in
      Hashtbl.add tbl str (t_var vsymb);
      vsymb
    and rem_var tbl v = Hashtbl.remove tbl (Vars.name v) in
    let quantified_vars =
      List.map (create_var index_symb indices_tbl)    i_vs @
      List.map (create_var ts_symb    timestamps_tbl) t_vs @
      List.map (create_var msg_symb   messages_tbl)   m_vs in
    (* at this stage the variables are added to the scope, we can recurse *)
    let subfmla = msg_to_fmla f in
    (* and then cleanup *)
    List.iter (rem_var indices_tbl)    i_vs;
    List.iter (rem_var timestamps_tbl) t_vs;
    List.iter (rem_var messages_tbl)   m_vs;
    quantifier quantified_vars [] subfmla
  in

  let open Why3.Term in
  (* Axiom: forall x y. fst (x,y) = x /\ snd (x,y) = y *)
  let axiom_pair =
    let vx = Why3.(Term.create_vsymbol (Ident.id_fresh "x")
                     (Ty.ty_app msg_symb [])) in
    let vy = Why3.(Term.create_vsymbol (Ident.id_fresh "y")
                     (Ty.ty_app msg_symb [])) in
    [(Symbols.fs_fst, vx); (Symbols.fs_snd, vy)]
    |> List.map (fun (proj, v) ->
        t_equ (t_app_infer (find_fn proj)
                 [ilist_to_wterm [];
                  t_app_infer (find_fn Symbols.fs_pair)
                    [ilist_to_wterm []; t_var vx; t_var vy]])
          (t_var v))
    |> t_and_l
    |> t_forall_close [vx; vy] [] in

  let equational_axioms =
    let open Symbols in
    Function.fold (fun fname def data acc ->
        match (snd def), data with
        (* cases taken from Completion.init_erules *)
        | AEnc, AssociatedFunctions [f1; f2] ->
          let dec, pk = (* from Completion.dec_pk *)
            match Function.get_def f1 table, Function.get_def f2 table with
            | (_, ADec), (_, PublicKey) -> f1, f2
            | (_, PublicKey), (_, ADec) -> f2, f1
            | _ -> assert false
          in
          (* we omit the check_zero_arities from Completion *)
          (* dec(enc(m, r, pk(k)), k) -> m *)
          begin match List.map (fun str ->
              Why3.(Term.create_vsymbol (Ident.id_fresh str)
                      (Ty.ty_app msg_symb []))) ["m"; "r"; "k"] with
          | [vm; vr; vk] as vars ->
            ("axiom_aenc",
             t_equ (t_app_infer (find_fn dec) (* TODO utility for t_app_infer + find_fn *)
                      [ilist_to_wterm [];
                       t_app_infer (find_fn fname) (* fname = enc *)
                         [ilist_to_wterm [];
                          t_var vm; t_var vr;
                          t_app_infer (find_fn pk)
                            [ilist_to_wterm []; t_var vk]];
                       t_var vk])
               (t_var vm) |> t_forall_close vars [])
            :: acc
          | _ -> assert false
          end
        | SEnc, AssociatedFunctions [sdec] ->
          (* dec(enc(m, r, k), k) -> m *)
          begin match List.map (fun str ->
              Why3.(Term.create_vsymbol (Ident.id_fresh str)
                      (Ty.ty_app msg_symb []))) ["m"; "r"; "k"] with
          | [vm; vr; vk] as vars ->
            ("axiom_senc",
             t_equ (t_app_infer (find_fn sdec)
                      [ilist_to_wterm [];
                       t_app_infer (find_fn fname)
                         [ilist_to_wterm [];
                          t_var vm; t_var vr; t_var vk];
                       t_var vk])
               (t_var vm) |> t_forall_close vars [])
            :: acc
          | _ -> assert false
          end
        | CheckSign, AssociatedFunctions [f1; f2] ->
          let msig, pk = (* from Completion.sig_pk  *)
            match Function.get_def f1 table, Function.get_def f2 table with
            | (_, Sign), (_, PublicKey) -> f1, f2
            | (_, PublicKey), (_, Sign) -> f2, f1
            | _ -> assert false
          in
          (* mcheck(msig(m, k), pk(k)) -> true  *)
          begin match List.map (fun str ->
              Why3.(Term.create_vsymbol (Ident.id_fresh str)
                      (Ty.ty_app msg_symb []))) ["m"; "k"] with
          | [vm; vk] as vars ->
            ("axiom_sig",
             t_equ (t_app_infer (find_fn fname)
                      [ilist_to_wterm [];
                       t_app_infer (find_fn msig)
                         [ilist_to_wterm []; t_var vm; t_var vk];
                       t_app_infer (find_fn pk)
                         [ilist_to_wterm []; t_var vk]])
               (t_app_infer (find_fn Symbols.fs_true) [ilist_to_wterm []])
             |> t_forall_close vars [])
            :: acc
          | _ -> assert false
          end
        | _ -> acc
      ) [("axiom_pair", axiom_pair)] table in

  let macro_axioms = ref [] in
  (* NOTE: for now we don't handle input/frame *)
  action_iter (fun descr ->
      (* TODO: some code below (handling var scope) is taken from msg_to_fmla_q
       *       this should be factored into an auxiliary function *)
      let name_str = Symbols.to_string descr.name in
      (* TODO: quantified_vars is a recurring pattern *)
      let quantified_vars = List.map (fun v ->
          let str = Vars.name v in
          let vsymb = create_vsymbol (Why3.Ident.id_fresh str)
              (Why3.Ty.ty_app index_symb []) in
          (* add to scope (shadow previous hash table binding) *)
          Hashtbl.add indices_tbl str (t_var vsymb);
          vsymb) descr.indices in
      (* the call to ilist_to_wterm below already requires
       * that the index variables be in scope *)
      let ts = t_app_infer act_symb
          [t_app_infer (Hashtbl.find actions_tbl name_str) [];
           ilist_to_wterm descr.indices] in
      (* special handling for cond@ because it's a boolean
       * -> translated to formula, not term of type message unlike other macros
       * happens(A(i,...)) => (cond@A(i,...) <=> <the definition>) *)
      let ax_cond = t_implies (t_app_infer happens_symb [ts])
          (t_iff
             (t_app_infer macro_cond_symb [ts])
             (msg_to_fmla (snd descr.Action.condition))) in
      macro_axioms := ("expand_cond_" ^ name_str,
                       t_forall_close quantified_vars [] ax_cond) ::
                      !macro_axioms;
      (* the following partially copied on _get_definition (private) in macros.ml *)
      Symbols.Macro.iter (fun mn mdef mdata ->
          let m_str  = Symbols.to_string mn in
          let m_symb = Hashtbl.find macros_tbl m_str in
          let macro_wterm_eq is msg = t_equ (t_app_infer m_symb [is; ts]) msg in
          let ax_option = match mdef with
            | Symbols.Output ->
              (* output@A(i1,...) = output *)
              Some (macro_wterm_eq
                      (ilist_to_wterm [])
                      (msg_to_wterm (snd descr.Action.output)))
            | Symbols.State _ ->
              let quantified_ilist = Why3.(Term.create_vsymbol
                                             (Ident.id_fresh "ii")
                                             (Ty.ty_app ilist_symb [])) in
              let ilist = t_var quantified_ilist in
              let expansion =
                let same_as_pred =
                  t_app_infer m_symb [ilist; t_app_infer pred_symb [ts]] in
                try
                  (* TODO: wait, can an action update multiple state macros
                   *       with the same name and different indices?
                   *       if so then the below is incomplete
                   *       (but macros.ml looks like it behaves the same way?) *)
                  let (ns, msg) = List.find (fun (ns,_) -> ns.Term.s_symb = mn)
                      descr.Action.updates in
                  let expansion_ok = msg_to_wterm msg in
                  if descr.Action.name = Symbols.init_action
                  then expansion_ok
                  else
                    t_if (t_equ ilist (ilist_to_wterm ns.s_indices))
                      expansion_ok
                      same_as_pred
                with Not_found -> same_as_pred in
              Some (t_forall_close [quantified_ilist] []
                      (macro_wterm_eq ilist expansion))
            | Symbols.Global _ -> begin match Macros.get_global_data mdata with
                (* partially copied on get_def_glob from macros.ml  *)
                | Some ({action = (strict, glob_a); inputs = g_inputs;
                         indices = g_indices; ts = g_ts} as g_data)
                  when Macros.is_prefix strict glob_a (Action.get_shape descr.action) ->
                  let ts_subst = Term.ESubst (Term.mk_var g_ts,
                                              SystemExpr.action_to_term
                                                table system descr.action) in
                  let rev_action =
                    let rec drop n l =
                      if n=0 then l else drop (n-1) (List.tl l) in
                    drop (List.length descr.action - List.length g_inputs)
                      (List.rev descr.action)
                  in
                  let subst,_ =
                    List.fold_left
                      (fun (subst,action_prefix) x ->
                         let a_ts = SystemExpr.action_to_term
                             table system (List.rev action_prefix) in
                         let in_tm = Term.mk_macro Term.in_macro [] a_ts in
                         (Term.ESubst (Term.mk_var x, in_tm) :: subst,
                          List.tl action_prefix))
                      ([ts_subst], rev_action)
                      g_inputs
                  in
                  let t = Term.subst subst (Macros.get_body system g_data) in
                  (* TODO: quantify over g_indices (counterpart to idx_subst)
                   *       what relationship is required between g_indices and
                   *       the action indices??? *)
                  None
                | _  -> None
              end
            | _ -> None
          in
          match ax_option with
          | None -> ()
          | Some ax ->
            (* forall i1 ... in : index. happens(A(i1,...)) => ... *)
            macro_axioms := ("expand_" ^ m_str ^ "_" ^ name_str,
                             t_forall_close quantified_vars []
                               (t_implies (t_app_infer happens_symb [ts]) ax))
                            :: !macro_axioms
        ) table;
      (* cleanup scope  *)
      List.iter (fun v -> Hashtbl.remove indices_tbl (Vars.name v)) descr.indices;
    );

  (* names are injective and two different names never collide (almost surely) *)
  let name_inj_axioms = Symbols.Name.fold (fun n1 _ _ acc1 ->
      Symbols.Name.fold (fun n2 _ _ acc2 ->
          if n1 > n2 then acc2 else (* to avoid redundancy *)
            let v1 = Why3.(Term.create_vsymbol (Ident.id_fresh "ii")
                             (Ty.ty_app ilist_symb [])) in
            let v2 = Why3.(Term.create_vsymbol (Ident.id_fresh "jj")
                             (Ty.ty_app ilist_symb [])) in
            let ineq = t_neq
                (t_app_infer (Hashtbl.find names_tbl
                                (Symbols.to_string n1)) [t_var v1])
                (t_app_infer (Hashtbl.find names_tbl
                                (Symbols.to_string n2)) [t_var v2]) in
            t_forall_close [v1; v2] []
              (if n1 = n2
               then t_implies (t_neq (t_var v1) (t_var v2)) ineq
               else ineq)
            :: acc2
        ) acc1 table) [] table in

  (* add distinct_actions_axioms here instead of at the end *)
  let task_header = List.fold_left (fun acc (id_ax, ax) ->
      Why3.Task.add_prop_decl acc Why3.Decl.Paxiom
        (Why3.Decl.create_prsymbol @@ Why3.Ident.id_fresh id_ax)
        ax) task_header (List.map (fun x -> ("axiom_distinct", x))
                           (distinct_actions_axioms @ name_inj_axioms)
                         @ equational_axioms @ !macro_axioms) in


  Why3.Task.add_prop_decl task_header Why3.Decl.Pgoal
    (Why3.Decl.create_prsymbol @@ Why3.Ident.id_fresh "GOOOOAL")
    (List.map trace_lit_to_fmla trace_lits
     @ List.map msg_atom_to_fmla msg_atoms
     @ List.map msg_to_fmla given_axioms
     |> t_and_l |> t_not)

let literals_unsat ~slow table system evars msg_atoms trace_lits axioms =
  (* List.iter (fun a -> Term.pp Format.std_formatter a; Format.printf "\n") axioms; *)
  try
    match get_smt_setup () with
    | None -> Format.printf "smt: setup issue\n"; false
    | Some (tm_theory, _, _) -> begin
        let task =
          build_task_bis table system evars msg_atoms trace_lits axioms tm_theory in
        Format.printf "@[task is:@\n%a@]@." Why3.Pretty.print_task task;
        Utils.omap (fun x -> x.Why3.Call_provers.pr_answer)
          (if slow then run_prover ~limit_opt:60 task else run_prover task)
        = Some Why3.Call_provers.Valid
        (* match if slow then run_prover ~limit_opt:60 task else run_prover task with
         * | None -> false
         * | Some result -> begin
         *     Format.printf "@[result is:@\n%a@]@."
         *       (Why3.Call_provers.print_prover_result ~json:false)
         *       result;
         *     result.pr_answer = Why3.Call_provers.Valid
         *   end *)
      end
  with
  | Unsupported -> Format.printf "smt: unsupported\n"; false
