open Utils

module SE = SystemExpr
module L  = Location

module Sv = Vars.Sv
              
(*------------------------------------------------------------------*)
(** rewrite a rule as much as possible without recursing *)
let rewrite_norec
    (table  : Symbols.table)
    (system : SE.t)
    (venv   : Vars.env)         (* for clean variable naming *)
    (rule   : Rewrite.rw_erule) 
    (t      : Term.term)
  : Term.term 
  =
  assert (rule.rw_conds = []);
  let Term.ESubst (left,right) = rule.rw_rw in
  let pat : Term.term Match.pat = Match.{ 
      pat_tyvars = rule.rw_tyvars; 
      pat_vars   = rule.rw_vars; 
      pat_term   = left;
    } 
  in
  let rw_inst : Match.Pos.f_map = 
    fun occ vars _conds _p ->
      match Match.T.try_match table system occ pat with
      | NoMatch _ | FreeTyv -> `Continue

      (* head matches *)
      | Match mv ->
        let subst = Match.Mvar.to_subst ~mode:`Match mv in
        let left = Term.subst subst left in
        let right = Term.subst subst right in
        assert (left = occ);
        `Map right
  in
  let _, f = Match.Pos.map ~m_rec:false rw_inst venv t in
  f

(*------------------------------------------------------------------*)
(** High-level system cloning function. *)
let clone_system_map
    (table    : Symbols.table)
    (system   : SE.t)
    (s_system : SE.single_system)
    (new_name : Theory.lsymb)
    (fmap     : Term.term -> Term.term)
  : Symbols.table * SE.t * Symbols.system 
  =
  (* We declare the system *)
  let table, new_system_name =
    SystemExpr.clone_system_map
      table system
      new_name (Action.descr_map (fun _ -> fmap))
  in

  let new_s_system, old_s_system, old_system_name =
    match system with
    | Single (Left  s as old) -> SE.Left  new_system_name, old, s
    | Single (Right s as old) -> SE.Right new_system_name, old, s
    |  _ -> assert false
  in

  let global_macro_fold ns dec_def _ table : Symbols.table =
    Macros.update_global_data
      table ns dec_def
      s_system new_s_system fmap
  in

  let table = Symbols.Macro.fold global_macro_fold table table in

  let new_system_e = SystemExpr.pair table old_s_system new_s_system in

  table, new_system_e, old_system_name

(*------------------------------------------------------------------*)
let parse_single_system_name table sdecl =
  match SE.parse_se table sdecl.Decl.from_sys with
  | Single s as res -> res, s
  | _ -> 
    Tactics.soft_failure ~loc:(L.loc sdecl.Decl.from_sys)
      (Failure "a single system must be provided")

(*------------------------------------------------------------------*)
(** Convertion of system modifiers arguments.
    - [bnds] are additional binded variables. *)
let conv_term ?pat table system ~bnds (term : Theory.term)
  : Vars.env * Vars.vars * Term.term
  =
  let env = Env.init ~table ~system:system () in
  let env,is = Theory.convert_p_bnds env bnds in

  Vars.check_type_vars is [Type.Index]
    (fun () ->
       let loc =
         let hloc = L.loc @@ snd @@ List.hd   bnds in
         let eloc = L.loc @@ snd @@ List.last bnds in
         L.merge hloc eloc
       in
       Tactics.hard_failure ~loc
         (Tactics.Failure "Only index variables can be bound."));

  let conv_env = Theory.{ env; cntxt = InGoal } in
  let t, _ = Theory.convert ?pat conv_env term in
  env.vars, is, t

(*------------------------------------------------------------------*)
(** {2 Renaming} *)

let global_rename table sdecl (gf : Theory.global_formula) =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in
  let env = Env.init ~table ~system:old_system () in
  let conv_env = Theory.{ env; cntxt = InGoal } in

  let f = Theory.convert_global_formula conv_env gf in

  let vs, f = Equiv.Smart.decompose_forall f in

  Vars.check_type_vars vs [Type.Index]
    (fun () -> Tactics.hard_failure ~loc:(L.loc gf)
        (Tactics.Failure "Only index variables can be bound."));

  let ns1, ns2, n1, n2 =
    match f with
    |  Atom (Equiv ([Term.Diff (Term.Name ns1, Term.Name ns2)])) ->
      ns1, ns2, Term.mk_name ns1, Term.mk_name ns2

    | _ ->
      Tactics.hard_failure ~loc:(L.loc gf) (Failure "arguments ill-formed")
  in

  (* We check that n2 does not occur in the old system using fresh. *)
  let cntxt = Constr.{ table  = table;
                       system = old_system;
                       models = None; }
  in
  let iter = new Fresh.find_name ~cntxt true ns2.s_symb in
  let () =
    try
      SystemExpr.iter_descrs
        cntxt.table cntxt.system
        (fun action_descr ->
           iter#visit_message (snd action_descr.output) ;
           iter#visit_message (snd action_descr.condition) ;
           List.iter (fun (_,m) -> iter#visit_message m) action_descr.updates
        );
    with Fresh.Name_found ->
      Tactics.hard_failure
        (Tactics.Failure "The name on the right-hand side already \
                          occurs in the left-hand side.")
  in

  (* We now build the rewrite rule *)
  let evars = Term.get_vars n1 in
  let vs, subs = Term.refresh_vars `Global evars in
  let n1', n2' = (Term.subst subs n1, Term.subst subs n2) in
  let rw_rule = Rewrite.{
      rw_tyvars = [];
      rw_vars   = Vars.Sv.of_list vs;
      rw_conds  = [];
      rw_rw     = Term.ESubst (n1', n2');
    }
  in

  let fmap t : Term.term =
    rewrite_norec table old_system env.vars rw_rule t
  in
  
  let table, new_system_e, old_system_name =
    clone_system_map
      table old_system old_single_system sdecl.Decl.name fmap
  in 
  
  let axiom_name =
    "rename_from_" ^ Symbols.to_string old_system_name ^
    "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_new Type.Message "mess" in
  let enrich = [Term.mk_var fresh_x_var] in

  let make_conclusion equiv =
    let fimpl =
      Equiv.Impl(
        Equiv.mk_forall evars
          (Atom (Equiv [Term.mk_var fresh_x_var; Term.mk_diff n1 n2])),
        equiv)
    in
    `Equiv (Equiv.mk_forall [fresh_x_var] fimpl)
  in
  (axiom_name, enrich, make_conclusion, new_system_e, table)


(*------------------------------------------------------------------*)
(** {2 PRF} *)

let global_prf
    (table : Symbols.table)
    (sdecl : Decl.system_modifier)
    (bnds  : Theory.bnds)
    (hash  : Theory.term)
  : string *
    Term.term list *
    (Equiv.global_form -> [> `Equiv of Equiv.global_form ]) *
    SE.t *
    Symbols.table
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  let venv, is, hash = conv_term table old_system ~bnds hash in

  let cntxt = Constr.{
      table  = table;
      system = old_system;
      models = None}
  in

  let param = Prf.prf_param hash in
  
  (* Check syntactic side condition. *)
  let errors =
    Euf.key_ssc
      ~elems:[] ~allow_functions:(fun x -> false)
      ~cntxt param.h_fn param.h_key.s_symb
  in
  if errors <> [] then
    Tactics.soft_failure (Tactics.BadSSCDetailed errors);

  (* We first refresh globably the indices to create the left pattern *)
  let is1, left_subst = Term.refresh_vars `Global is in

  let left_key =  Term.subst left_subst (Term.mk_name param.h_key) in
  let left_key_ids = match left_key with
    | Term.Name s -> s.s_indices
    | _ -> assert false
  in
  (* We create the pattern for the hash *)
  let fresh_x_var = Vars.make_new Type.Message "x" in
  let hash_pattern =
    Term.mk_fun table param.h_fn [] [Term.mk_var fresh_x_var; left_key ]
  in

  (* Instantiation of the fresh name *)
  let ndef =
    let ty_args = List.map Vars.ty is in
    Symbols.{ n_fty = Type.mk_ftype 0 [] ty_args Type.Message ; }
  in
  let table,n =
    Symbols.Name.declare cntxt.table (L.mk_loc L._dummy "n_PRF") ndef
  in
  
  (* the hash h of a message m will be replaced by tryfind is s.t = fresh mess
     in fresh else h *)
  let mk_tryfind =
    let ns = Term.mk_isymb n Message (is) in
    Term.mk_find is Term.(
        mk_and
          (mk_atom `Eq (Term.mk_var fresh_x_var) param.h_cnt)
          (mk_indices_eq left_key_ids param.h_key.s_indices)
      ) (Term.mk_name ns) hash_pattern
  in
  let rw_rule = Rewrite.{
      rw_tyvars = [];
      rw_vars   = Vars.Sv.of_list (fresh_x_var :: is1);
      rw_conds  = [];
      rw_rw     = Term.ESubst (hash_pattern, mk_tryfind);
    }
  in

  let fmap t =
    rewrite_norec table old_system venv rw_rule t
  in

  let table, new_system_e, old_system_name =
    clone_system_map
      table old_system old_single_system sdecl.Decl.name fmap
  in 
  
  let axiom_name =
    "prf_from_" ^ Symbols.to_string old_system_name ^
    "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_new Type.Message "mess" in
  let enrich = [Term.mk_var fresh_x_var] in
  let make_conclusion equiv =
    let atom =
      Equiv.Atom (
        Equiv [Term.mk_var fresh_x_var;
               Term.mk_diff
                 (Term.mk_name param.h_key)
                 (Term.mk_name @@ Term.mk_isymb n Message (is))])
    in
    let concl = 
      Equiv.mk_forall [fresh_x_var]
        (Equiv.Smart.mk_impl ~simpl:false (Equiv.mk_forall is atom) equiv)
    in
    `Equiv concl
  in
  (axiom_name, enrich, make_conclusion, new_system_e, table)


(*------------------------------------------------------------------*)
(** {2 CCA} *)

  
let global_cca table sdecl bnds (p_enc : Theory.term) =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in
  let venv, is, enc = conv_term table old_system ~bnds p_enc in

  let cntxt = Constr.{
      table  = table;
      system = old_system;
      models = None }
  in

  let enc_fn, enc_key, plaintext, enc_pk, enc_rnd =
    match enc with
    | Term.Fun ((fnenc,eis), _,
                [m; Term.Name r;
                 Term.Fun ((fnpk,is), _, [Term.Name sk])])
      when Symbols.is_ftype fnpk Symbols.PublicKey cntxt.table &&
           Symbols.is_ftype fnenc Symbols.AEnc table ->
      fnenc, sk, m, fnpk, r

    | _ ->
      Tactics.soft_failure ~loc:(L.loc p_enc)
        (Tactics.Failure
           "CCA can only be applied on an encryption term enc(t,r,pk(k))")
  in

  let dec_fn =
    match Symbols.Function.get_data enc_fn table with
    (* we check that the encryption function is used with the associated
       public key *)
    | Symbols.AssociatedFunctions [fndec; fnpk2] when fnpk2 = enc_pk ->
      (* Check syntactic side condition. *)
      let errors =
        Euf.key_ssc ~messages:[enc] ~allow_functions:(fun x -> x = enc_pk)
          ~cntxt fndec enc_key.s_symb
      in
      
      if errors <> [] then
        Tactics.soft_failure (Tactics.BadSSCDetailed errors);
      
      fndec

    | _ ->
      Tactics.soft_failure
        (Tactics.Failure
           "The first encryption symbol is not used with the correct \
            public key function.")
  in

  (* TODO: check randomness is used only once, and message is distinct. *)

  (* We first refresh globably the indices to create the left patterns *)
  let is1, left_subst = Term.refresh_vars (`Global) is in

  (* The dec must match all decryption with the corresponding secret key *)
  let fresh_x_var = Vars.make_new Type.Message "x" in
  let dec_pattern =
    Term.mk_fun table dec_fn [] [ Term.mk_var fresh_x_var;
                                  Term.mk_name enc_key ]
  in
  let dec_pattern = Term.subst left_subst dec_pattern in

  (* Instantiation of the fresh replacement *)
  let ndef =
    let ty_args = List.map Vars.ty enc_rnd.s_indices in
    Symbols.{ n_fty = Type.mk_ftype 0 [] ty_args Type.Message ; }
  in
  let table,n =
    Symbols.Name.declare cntxt.table (L.mk_loc L._dummy "n_CCA") ndef
  in
  
  let mess_replacement =
    if Term.is_name plaintext then
      let ns = Term.mk_isymb n Message (enc_rnd.s_indices) in
      Term.mk_name ns
    else
      Term.mk_zeroes (Term.mk_len plaintext) in

  let new_enc =
    let t_pk = Term.mk_fun table enc_pk [] [Term.mk_name enc_key]  in
    Term.mk_fun table enc_fn [] [ mess_replacement;
                                  Term.mk_name enc_rnd;
                                  t_pk ]
  in

  (* We replace
       dec(m,pk(sk(j))) 
     by:
       tryfind i s.t m=new_enc(i) & i =j 
               else enc(m,r,pk(sk)) 
     in plaintext *)
  let tryfind_dec =
    Term.mk_find is Term.(
        (mk_atom `Eq (Term.mk_var fresh_x_var) new_enc)
      ) (plaintext) dec_pattern
  in

  let enc_rw_rule = Rewrite.{
      rw_tyvars = [];
      rw_vars   = Vars.Sv.of_list is;
      rw_conds  = [];
      rw_rw     = Term.ESubst (enc, new_enc);
    }
  in
  let dec_rw_rule = Rewrite.{
      rw_tyvars = [];
      rw_vars   = Vars.Sv.of_list (fresh_x_var :: is1);
      rw_conds  = [];
      rw_rw     = Term.ESubst (dec_pattern, tryfind_dec);
    }
  in

  let fmap t =
    rewrite_norec table old_system venv enc_rw_rule t |>
    rewrite_norec table old_system venv dec_rw_rule 
  in

  let table, new_system_e, old_system_name =
    clone_system_map
      table old_system old_single_system sdecl.Decl.name fmap
  in

  let axiom_name =
    "cca_from_" ^ Symbols.to_string old_system_name ^
    "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_new Type.Message "mess" in
  let rdef =
    let ty_args = List.map Vars.ty is in
    Symbols.{ n_fty = Type.mk_ftype 0 [] ty_args Type.Message ; }
  in
  let table,r =
    Symbols.Name.declare table (L.mk_loc L._dummy "r_CCA") rdef
  in

  let enrich = [Term.mk_var fresh_x_var] in
  let make_conclusion equiv =
    let atom =
      Equiv.Atom (
        Equiv [ Term.mk_var fresh_x_var;
                
                Term.mk_diff
                 (Term.mk_name enc_key)
                 (Term.mk_name @@ Term.mk_isymb n Message (is));
                
               Term.mk_diff
                 (Term.mk_name enc_rnd)
                 (Term.mk_name @@ Term.mk_isymb r Message (is))])
    in
    let concl = Equiv.Impl (Equiv.mk_forall is atom, equiv) in      
    `Equiv (Equiv.mk_forall [fresh_x_var] concl)
  in
  (axiom_name, enrich, make_conclusion, new_system_e, table)

(*------------------------------------------------------------------*)
(** {2 Global PRF with time} *)

let check_fv_finite (fv : Sv.t) =
  Sv.iter (fun v ->
      if not (Type.equal (Vars.ty v) Type.tindex) &&
         not (Type.equal (Vars.ty v) Type.ttimestamp) then
        Tactics.hard_failure
          (Failure
             "system contain quantifiers over types ≠ from \
              Index and Timestamp, which are not supported.")
    ) fv

let global_prf_time
    (table : Symbols.table)
    (sdecl : Decl.system_modifier)
    (bnds  : Theory.bnds)
    (hash  : Theory.term)
  : string *
    Term.term list *
    (Equiv.global_form -> [> `Equiv of Equiv.global_form ]) *
    SE.t *
    Symbols.table
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in
  
  let venv, is, hash = conv_term ~pat:true table old_system ~bnds hash in

  let cntxt = Constr.{
      table  = table;
      system = old_system;
      models = None}
  in

  let param = Prf.prf_param hash in

  (* Check syntactic side condition. *)
  let errors =
    Euf.key_ssc
      ~elems:[] ~allow_functions:(fun x -> false)
      ~cntxt param.h_fn param.h_key.s_symb
  in
  if errors <> [] then
    Tactics.soft_failure (Tactics.BadSSCDetailed errors);

  let occs : Iter.hash_occs =
    SystemExpr.fold_descrs (fun descr occs ->
        Iter.fold_descr ~globals:true (fun msymb m_is _ t occs ->
            let new_occs =
              Iter.get_f_messages_ext
                ~fv:Sv.empty ~cntxt
                param.h_fn param.h_key.s_symb t
            in
            new_occs @ occs
          ) cntxt.table cntxt.system descr occs
      ) cntxt.table cntxt.system []
  in

  (* FIXME: check duplicate module alpha-renaming *)
  let occs = List.remove_duplicate (=) occs in

  (* type of the hash function input *)
  let m_ty = List.hd (param.h_fty.fty_args) in

  (* fresh variable representing the hashed message to rewrite *)
  let x   = Vars.make_new m_ty "x" in
  let x_t = Term.mk_var x in
  
  (* timestamp at which [H(x,k)] occurs  *)
  let tau = Vars.make_new Type.ttimestamp "t" in

  (* [occ_name] is a list of hash occurrence and their associated 
     name symbol. *)
  let table, occ_names =
    List.map_fold (fun table occ ->
        (* check that no occurrence of the hash appears below a binder
           with a non-finite type. *)
        check_fv_finite occ.Iter.occ_vars;

        let ndef =
          let ty_args = List.map Vars.ty (Sv.elements occ.Iter.occ_vars) in
          Symbols.{ n_fty = Type.mk_ftype 0 [] ty_args m_ty ; }
        in
        let table,n =
          Symbols.Name.declare cntxt.table (L.mk_loc L._dummy "n_PRF") ndef
        in
        table, (occ, n)
      ) table occs
  in

  let is, subst = Term.refresh_vars `Global is in
  let key = Term.subst subst (Term.mk_name param.h_key) in
  let key_is = List.map (Term.subst_var subst) param.h_key.s_indices in

  (* term to rewrite *)
  let to_rw =
    Term.mk_fun table param.h_fn [] [x_t; key ]
  in

  (* condition stating that [x] is equal to a hash occurrence. *)
  let mk_occ_cond (occ : Iter.hash_occ) : Term.term =
    let occ_vars, occ_t = occ.occ_cnt in
    Term.mk_and ~simpl:false
      (Term.mk_eq ~simpl:true x_t occ_t)               (* hash content equ. *)
      (Term.mk_indices_eq ~simpl:true key_is occ_vars) (* hash key equ. *)
  in

  (* fresh name corresponding to occurrence [occ]. *)
  let mk_occ_term
      (occ : Iter.hash_occ) (n_occ : Symbols.name) : Term.term
    =
      (* FIXME: use a list of variables and not a set in [occ.occ_vars] *)
      Term.mk_name (Term.mk_isymb n_occ m_ty (Sv.elements occ.occ_vars))
  in
  
  (* we rewrite [H(x,k)] at occurrence occ0 at time tau0 into:
     try find tau, occ s.t. tau <= tau0 && x = s_{occ} 
     then n_{occ}@tau
     else n_occ0@tau0 *)
  let rw_target
      (tau0   : Term.term)
      (occ0   : Iter.hash_occ)
      (n_occ0 : Symbols.name)
    =
    let cond =
      Term.mk_ands ~simpl:false
        [ Term.mk_leq ~simpl:true (Term.mk_var tau) tau0;
          Term.mk_ors (List.map (fst_map mk_occ_cond) occ_names);
          assert false; ]
    in
    let t_else = mk_occ_term occ0 n_occ0 in
    let t_then =
      List.fold_left (fun t_then (occ, occ_name) ->
          let t_cond = mk_occ_cond occ in
          let t_occ = mk_occ_term occ occ_name in
          Term.mk_ite ~simpl:false t_cond t_occ t_then
        ) (Term.mk_witness m_ty) occ_names
      
    in
    Term.mk_find [tau] cond t_then t_else
  in

  let mk_rw_rule (tau0 : Term.term) = Rewrite.{
      rw_tyvars = [];
      rw_vars   = Sv.of_list (x :: is);
      rw_conds  = [];
      rw_rw     = Term.ESubst (to_rw, assert false(* rw_target tau0 *));
    } in

  let fmap (tau0 : Term.term) _ (t : Term.term) : Term.term =
    rewrite_norec table old_system venv (mk_rw_rule tau0) t
  in

  let table, new_system_e, old_system_name =
    clone_system_map
      table old_system old_single_system sdecl.Decl.name (assert false) (* fmap *)
  in 
  assert false
  
(*------------------------------------------------------------------*)
let declare_system
    (table   : Symbols.table)
    (hint_db : Hint.hint_db)
    (sdecl   : Decl.system_modifier)
  : Goal.statement * Symbols.table
  =
  let new_axiom_name, enrich, make_conclusion, new_system, table = 
    match sdecl.Decl.modifier with
    | Rename gf        -> global_rename table sdecl        gf
    | PRF (bnds, hash) -> global_prf    table sdecl bnds hash
    | CCA (bnds, enc)  -> global_cca    table sdecl bnds  enc
  in
  let `Equiv formula, _ =
    Goal.make_obs_equiv ~enrich table hint_db new_system 
  in
  let formula = make_conclusion formula in
  let lemma = Goal.{ 
      name    = new_axiom_name; 
      system  = new_system; 
      ty_vars = []; 
      formula }
  in
  lemma, table
