open Utils
open Env

module L = Location

type lsymb = string L.located

(*------------------------------------------------------------------*)
(** {2 Types} *)

type p_ty_i =
  | P_message
  | P_boolean
  | P_index
  | P_timestamp
  | P_tbase of lsymb
  | P_tvar  of lsymb

type p_ty = p_ty_i L.located

let pp_p_ty_i fmt = function
  | P_message   -> Fmt.pf fmt "message"
  | P_boolean   -> Fmt.pf fmt "boolean"
  | P_index     -> Fmt.pf fmt "index"
  | P_timestamp -> Fmt.pf fmt "timestamp"
  | P_tbase s   -> Fmt.pf fmt "%s" (L.unloc s)
  | P_tvar s    -> Fmt.pf fmt "'%s" (L.unloc s)

let pp_p_ty fmt pty = pp_p_ty_i fmt (L.unloc pty)

(*------------------------------------------------------------------*)
(** Parsed binder *)
type bnd  = lsymb * p_ty

(** Parsed binders *)
type bnds = (lsymb * p_ty) list

(*------------------------------------------------------------------*)
(** {2 Terms} *)

type term_i =
  | Tpat
  | Diff  of term * term
  | Seq   of bnds * term
  | Find  of lsymb list * term * term * term

  | App of lsymb * term list
  (** An application of a symbol to some arguments which as not been
      disambiguated yet (it can be a name, a function symbol
      application, a variable, ...)
      [App(f,t1 :: ... :: tn)] is [f (t1, ..., tn)] *)

  | AppAt of lsymb * term list * term
  (** An application of a symbol to some arguments, at a given
      timestamp.  As for [App _], the head function symbol has not been
      disambiguated yet.
      [AppAt(f,t1 :: ... :: tn,tau)] is [f (t1, ..., tn)@tau] *)

  | ForAll  of bnds * term
  | Exists  of bnds * term

and term = term_i L.located

type formula = term

(*------------------------------------------------------------------*)
let equal_p_ty t t' = match L.unloc t, L.unloc t' with
  | P_message  , P_message
  | P_boolean  , P_boolean
  | P_index    , P_index
  | P_timestamp, P_timestamp -> true

  | P_tbase b, P_tbase b' -> L.unloc b = L.unloc b'
  | P_tvar v, P_tvar v' -> L.unloc v = L.unloc v'

  | _, _ -> false

(*------------------------------------------------------------------*)
let rec equal t t' = match L.unloc t, L.unloc t' with
  | Diff (a,b), Diff (a',b') ->
    equal a a' && equal b b'

  | Seq (l, a),    Seq (l', a')
  | ForAll (l, a), ForAll (l', a')
  | Exists (l, a), Exists (l', a') ->
    List.length l = List.length l' &&
    List.for_all2 (fun (s,k) (s',k') ->
        L.unloc s = L.unloc s' && equal_p_ty k k'
      ) l l'
    && equal a a'

  | Find (l, a, b, c), Find (l', a', b', c') ->
    List.length l = List.length l' &&
    List.for_all2 (fun s s' ->
        L.unloc s = L.unloc s'
      ) l l'
    && equals [a; b; c] [a'; b'; c']

  | AppAt (s, ts, t), AppAt (s', ts', t') ->
    L.unloc s = L.unloc s' &&
    equals (t :: ts) (t' :: ts')

  | App (s, ts), App (s', ts') ->
    L.unloc s = L.unloc s' &&
    equals ts ts'

  | _ -> false

and equals l l' = List.for_all2 equal l l'

(*------------------------------------------------------------------*)
let var_i loc x : term_i = App (L.mk_loc loc x,[])

let var   loc x : term = L.mk_loc loc (var_i loc x)

let var_of_lsymb s : term = var (L.loc s) (L.unloc s)

let destr_var = function
  | App (v, []) -> Some v
  | _ -> None

(*------------------------------------------------------------------*)
let pp_var_list ppf l =
  let rec aux cur_vars (cur_type : p_ty_i) = function
    | (v,vty) :: vs when L.unloc vty = cur_type ->
      aux ((L.unloc v) :: cur_vars) cur_type vs
    | vs ->
      if cur_vars <> [] then begin
        Fmt.list
          ~sep:(fun fmt () -> Fmt.pf fmt ",")
          Fmt.string ppf (List.rev cur_vars) ;
        Fmt.pf ppf ":%a" pp_p_ty_i cur_type ;
        if vs <> [] then Fmt.pf ppf ",@,"
      end ;
      match vs with
      | [] -> ()
      | (v, vty) :: vs -> aux [L.unloc v] (L.unloc vty) vs
  in
  aux [] P_message l


let rec pp_term_i ppf t = match t with
  | Tpat -> Fmt.pf ppf "_"

  | Find (vs,c,t,e) ->
      Fmt.pf ppf
        "@[%a@ %a@ %a@ %a@ %a@ %a@ %a@ %a@]"
        (Printer.kws `TermCondition) "try find"
        (Utils.pp_list Fmt.string) (L.unlocs vs)
        (Printer.kws `TermCondition) "such that"
        pp_term c
        (Printer.kws `TermCondition) "in"
        pp_term t
        (Printer.kws `TermCondition) "else"
        pp_term e

  | Diff (l,r) ->
      Fmt.pf ppf "%a(%a,%a)"
        (Printer.kws `TermDiff) "diff"
        pp_term l
        pp_term r

  | App (f,[t1;t2]) when L.unloc f = "exp" ->
    Fmt.pf ppf "%a^%a" pp_term t1 pp_term t2

  | App (f,[i;t;e]) when L.unloc f = "if" ->
      Fmt.pf ppf
        "@[%a@ %a@ %a@ %a@ %a@ %a@]"
        (Printer.kws `TermCondition) "if"
        pp_term i
        (Printer.kws `TermCondition) "then"
        pp_term t
        (Printer.kws `TermCondition) "else"
        pp_term e

  | App (f, [L.{ pl_desc = App (f1,[bl1;br1])};
             L.{ pl_desc = App (f2,[br2;bl2])}])
    when L.unloc f = "&&" && L.unloc f1 = "=>" && L.unloc f2 = "=>" &&
         bl1 = bl2 && br1 = br2 ->
    Fmt.pf ppf "@[<1>(%a@ <=>@ %a)@]"
      pp_term bl1 pp_term br1

  | App (f,[bl;br]) when Symbols.is_infix_str (L.unloc f) ->
    Fmt.pf ppf "@[<1>(%a@ %s@ %a)@]"
      pp_term bl (L.unloc f) pp_term br

  | App (f,[b]) when L.unloc f = "not" ->
    Fmt.pf ppf "not(@[%a@])" pp_term b

  | App (f,[]) when L.unloc f = "true" -> Printer.kws `TermBool ppf "True"

  | App (f,[]) when L.unloc f = "false" -> Printer.kws `TermBool ppf "False"

  | App (f,terms) ->
    Fmt.pf ppf "%s%a"
      (L.unloc f)
      (Utils.pp_list pp_term) terms

  | AppAt (f,terms,ts) ->
    Fmt.pf ppf "%s%a%a"
      (L.unloc f)
      (Utils.pp_list pp_term) terms
      pp_ts ts

  | Seq (vs, b) ->
      Fmt.pf ppf "@[%a(@[%a->%a@])@]"
        (Printer.kws `TermSeq) "seq"
        pp_var_list vs
        pp_term b

  | ForAll (vs, b) ->
      Fmt.pf ppf "@[%a (@[%a@]),@ %a@]"
        (Printer.kws `TermQuantif) "forall"
        pp_var_list vs
        pp_term b

  | Exists (vs, b) ->
      Fmt.pf ppf "@[%a (@[%a@]),@ %a@]"
        (Printer.kws `TermQuantif) "exists"
        pp_var_list vs
        pp_term b


and pp_ts ppf ts = Fmt.pf ppf "@%a" pp_term ts

and pp_term ppf t =
  Fmt.pf ppf "%a" pp_term_i (L.unloc t)

let pp   = pp_term
let pp_i = pp_term_i


(*------------------------------------------------------------------*)
(** {2 Higher-order terms} *)

(** For now, we need (and allow) almost no higher-order terms. *)
type hterm_i =
  | Lambda of bnds * term

type hterm = hterm_i L.located

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)

type equiv = term list

type pquant = PForAll | PExists

type global_formula = global_formula_i Location.located

and global_formula_i =
  | PEquiv  of equiv
  | PReach  of formula
  | PImpl   of global_formula * global_formula
  | PAnd    of global_formula * global_formula
  | POr     of global_formula * global_formula
  | PQuant  of pquant * bnds * global_formula

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type conversion_error_i =
  | Arity_error          of string*int*int
  | Untyped_symbol       of string
  | Index_error          of string*int*int
  | Undefined            of string
  | UndefinedOfKind      of string * Symbols.namespace
  | Type_error           of term_i * Type.ty
  | Timestamp_expected   of term_i
  | Timestamp_unexpected of term_i
  (* | Untypable_equality   of term_i *)
  | Unsupported_ord      of term_i
  | String_expected      of term_i (* TODO: move *)
  | Int_expected         of term_i (* TODO: move *)
  | Tactic_type          of string (* TODO: move *)
  | Index_not_var        of term_i
  | Assign_no_state      of string
  | BadNamespace         of string * Symbols.namespace
  | Freetyunivar
  | UnknownTypeVar       of string
  | BadPty               of Type.ty list
  | BadInfixDecl
  | PatNotAllowed
  | ExplicitTSInProc
  | UndefInSystem of SystemExpr.t

type conversion_error = L.t * conversion_error_i

exception Conv of conversion_error

let conv_err loc e = raise (Conv (loc,e))

let pp_error_i ppf = function
  | Arity_error (s,i,j) -> Fmt.pf ppf "Symbol %s used with arity %i, but \
                                       defined with arity %i" s i j

  | Untyped_symbol s -> Fmt.pf ppf "Symbol %s is not typed" s

  | Index_error (s,i,j) -> Fmt.pf ppf "Symbol %s used with %i indices, but \
                                       defined with %i indices" s i j

  | Undefined s -> Fmt.pf ppf "symbol %s is undefined" s

  | UndefinedOfKind (s,n) ->
    Fmt.pf ppf "%a %s is undefined" Symbols.pp_namespace n s

  | Type_error (s, ty) ->
    Fmt.pf ppf "Term %a is not of type %a" pp_i s Type.pp ty

  | Timestamp_expected t ->
    Fmt.pf ppf "The term %a must be given a timestamp" pp_i t

  | Timestamp_unexpected t ->
    Fmt.pf ppf "The term %a must not be given a timestamp" pp_i t

  | Unsupported_ord t ->
    Fmt.pf ppf
      "comparison %a cannot be typed@ \
       (operands have a type@ for which the comparison is allowed)"
      pp_i t

  | String_expected t ->
    Fmt.pf ppf
      "The term %a cannot be seen as a string"
      pp_i t

  | Int_expected t ->
    Fmt.pf ppf
      "The term %a cannot be seen as a int"
      pp_i t

  | Tactic_type s ->
    Fmt.pf ppf "The tactic arguments could not be parsed: %s" s

  | Index_not_var i ->
    Fmt.pf ppf "An index must be a variable, the term %a \
                cannot be seen as an index" pp_i i

  | Assign_no_state s ->
    Fmt.pf ppf "Only mutables can be assigned values, and the \
                symbols %s is not a mutable" s

  | BadNamespace (s,n) ->
    Fmt.pf ppf "Kind error: %s has kind %a" s
      Symbols.pp_namespace n

  | Freetyunivar -> Fmt.pf ppf "some type variable(s) could not \
                                       be instantiated"

  | UnknownTypeVar ty ->
    Fmt.pf ppf "undefined type variable %s" ty

  | BadPty l ->
    Fmt.pf ppf "type must be of type %a"
      (Fmt.list ~sep:Fmt.comma Type.pp) l

  | BadInfixDecl -> Fmt.pf ppf "bad infix symbol declaration"

  | PatNotAllowed -> Fmt.pf ppf "pattern not allowed"

  | ExplicitTSInProc ->
    Fmt.pf ppf "macros cannot be written at explicit \
                timestamps in procedure"

  | UndefInSystem t ->
    Fmt.pf ppf "action not defined in system @[%a@]"
      SystemExpr.pp t

let pp_error pp_loc_err ppf (loc,e) =
  Fmt.pf ppf "%a%a"
    pp_loc_err loc
    pp_error_i e

(*------------------------------------------------------------------*)
(** {2 Parsing types } *)

let parse_p_ty (env : Env.t) (pty : p_ty) : Type.ty =
  match L.unloc pty with
  | P_message        -> Message  
  | P_boolean        -> Boolean  
  | P_index          -> Index    
  | P_timestamp      -> Timestamp

  | P_tvar tv_l ->
    let tv =
      try
        List.find (fun tv' ->
            let tv' = Type.ident_of_tvar tv' in
            Ident.name tv' = L.unloc tv_l
          ) env.ty_vars
      with Not_found ->
        conv_err (L.loc tv_l) (UnknownTypeVar (L.unloc tv_l))
    in
    TVar tv

  | P_tbase tb_l ->
    let s = Symbols.BType.of_lsymb tb_l env.table in
    Type.TBase (Symbols.to_string s) (* TODO: remove to_string *)


(*------------------------------------------------------------------*)
(** {2 Type checking} *)

let check_arity_i loc s (actual : int) (expected : int) =
  if actual <> expected then
    conv_err loc (Arity_error (s,actual,expected))

let check_arity (lsymb : lsymb) (actual : int) (expected : int) =
  check_arity_i (L.loc lsymb) (L.unloc lsymb) actual expected

(** Type of a macro *)
type mtype = Type.ty list * Type.ty (* args, out *)

(** Macro or function type *)
type mf_type = [`Fun of Type.ftype | `Macro of mtype]

let ftype_arity (fty : Type.ftype) =
  fty.Type.fty_iarr + (List.length fty.Type.fty_args)

let mf_type_arity (ty : mf_type) =
  match ty with
  | `Fun ftype   -> ftype_arity ftype
  | `Macro (l,_) -> List.length l

(** Get the kind of a function or macro definition.
  * In the latter case, the timestamp argument is not accounted for. *)
let function_kind table (f : lsymb) : mf_type =
  let open Symbols in
  match def_of_lsymb f table with
  (* we should never encounter a situation where we
     try to type a reserved symbol. *)
  | Reserved _ -> assert false

  | Exists d -> match d with
    | Function (fty, _) -> `Fun fty

    | Macro (Global (arity, ty)) ->
      let targs = (List.init arity (fun _ -> Type.tindex)) in
      `Macro (targs, ty)

    | Macro (Input|Output|Frame) ->
      (* TODO: subtypes*)
      `Macro ([], Type.Message)

    | Macro (Cond|Exec) ->
      `Macro ([], Type.Boolean)

    | _ -> conv_err (L.loc f) (Untyped_symbol (L.unloc f))

let check_state table (s : lsymb) n : Type.ty =
  match Symbols.Macro.def_of_lsymb s table with
    | Symbols.State (arity,ty) ->
        check_arity s n arity ;
        ty

    | _ -> conv_err (L.loc s) (Assign_no_state (L.unloc s))

let check_name table (s : lsymb) n : Type.ty =
    let ndef = Symbols.Name.def_of_lsymb s table in
    let arity = ndef.n_iarr in
    if arity <> n then conv_err (L.loc s) (Index_error (L.unloc s,n,arity));
    ndef.n_ty

let check_action (env : Env.t) (s : lsymb) (n : int) : unit =
  let l,action = Action.find_symbol s env.table in
  let arity = List.length l in

  if arity <> n then conv_err (L.loc s) (Index_error (L.unloc s,n,arity));

  let _ = 
    try SystemExpr.descr_of_action env.table env.system action with
    | Not_found -> conv_err (L.loc s) (UndefInSystem env.system)
  in
  ()


(*------------------------------------------------------------------*)
(** Applications *)


(** Type of an application ([App _] or [AppAt _]) that has been
    dis-ambiguated *)
type app_i =
  | Name of lsymb * term list
  (** A name, whose arguments will always be indices. *)

  | Get of lsymb * Term.term option * term list
  (** [Get (s,ots,terms)] reads the contents of memory cell
    * [(s,terms)] where [terms] are evaluated as indices.
    * The second argument [ots] is for the optional timestamp at which the
    * memory read is performed. This is used for the terms appearing in
    * goals. *)

  | Fun of lsymb * term list * Term.term option
  (** Function symbol application,
    * where terms will be evaluated as indices or messages
    * depending on the type of the function symbol.
    * The third argument is an optional timestamp, used when
    * writing meta-logic formulas but not in processes. *)

  | Taction of lsymb * term list

  | AVar of lsymb

and app = app_i L.located

let[@warning "-32"] pp_app_i ppf = function
  | Taction (a,l) ->
    Fmt.pf ppf "%s%a"
      (L.unloc a)
      (Utils.pp_list pp_term) l

  | Fun (f,[t1;t2],ots) when L.unloc f="exp"->
    Fmt.pf ppf "%a^%a" pp_term t1 pp_term t2
  | Fun (f,terms,ots) ->
    Fmt.pf ppf "%s%a%a"
      (L.unloc f)
      (Utils.pp_list pp_term) terms
      (Fmt.option Term.pp) ots

  | Name (n,terms) ->
    Fmt.pf ppf "%a%a"
      (* Pretty-printing names with nice colors
       * is well worth violating the type system ;) *)
      Term.pp_name (Obj.magic n)
      (Utils.pp_list pp_term) terms

  | Get (s,ots,terms) ->
    Fmt.pf ppf "!%s%a%a"
      (L.unloc s)
      (Utils.pp_list pp_term) terms
      (Fmt.option Term.pp) ots

  | AVar s -> Fmt.pf ppf "%s" (L.unloc s)

(** Context of a application construction. *)
type app_cntxt =
  | At      of Term.term   (* for explicit timestamp, e.g. [s@ts] *)
  | MaybeAt of Term.term   (* for potentially implicit timestamp,
                                   e.g. [s] in a process parsing. *)
  | NoTS                        (* when there is no timestamp, even implicit. *)

let is_at = function At _ -> true | _ -> false
let get_ts = function At ts | MaybeAt ts -> Some ts | _ -> None

let make_app_i table cntxt (lsymb : lsymb) (l : term list) : app_i =
  let loc = L.loc lsymb in

  let arity_error i =
    conv_err loc (Arity_error (L.unloc lsymb, List.length l, i)) in
  let ts_unexpected () =
    conv_err loc (Timestamp_unexpected (App (lsymb,l))) in

  match Symbols.def_of_lsymb lsymb table with
  | Symbols.Reserved _ -> Fmt.epr "%s@." (L.unloc lsymb); assert false

  | Symbols.Exists d ->
    begin match d with
    | Symbols.Function (ftype,fdef) ->
      if is_at cntxt then ts_unexpected ();

      let farity = ftype_arity ftype in
      if List.length l <> farity then raise (arity_error farity) ;

      Fun (lsymb,l,None)

    | Symbols.Name ndef ->
      if is_at cntxt then ts_unexpected ();
      check_arity lsymb (List.length l) ndef.n_iarr ;
      Name (lsymb,l)

    | Symbols.Macro (Symbols.State (arity,_)) ->
      check_arity lsymb (List.length l) arity ;
      Get (lsymb,get_ts cntxt,l)

    | Symbols.Macro (Symbols.Global (arity,_)) ->
      if List.length l <> arity then arity_error arity;
      Fun (lsymb,l,get_ts cntxt)

    | Symbols.Macro (Symbols.Input|Symbols.Output|Symbols.Cond|Symbols.Exec
                    |Symbols.Frame) ->
      if cntxt = NoTS then
        conv_err loc (Timestamp_expected (App (lsymb,l)));
      if l <> [] then arity_error 0;
      Fun (lsymb,[],get_ts cntxt)

    | Symbols.Action arity ->
      if arity <> List.length l then arity_error arity ;
      Taction (lsymb,l)

    | Symbols.Channel _
    | Symbols.BType _
    | Symbols.Process _
    | Symbols.System  _ ->
      let s = L.unloc lsymb in
      conv_err loc (BadNamespace (s,
                                  oget(Symbols.get_namespace table s)))
    end

  | exception Symbols.SymbError (loc, Symbols.Unbound_identifier s) ->
    (* By default we interpret s as a variable,  but this is only
       possible if it is not indexed. If that is not the case, the
       user probably meant for this symbol to not be a variable,
       hence  we raise Unbound_identifier. We could also raise
       Type_error because a variable is never of  a sort that can be
       applied to indices. *)
      if l <> [] then
        raise (Symbols.SymbError (loc, Symbols.Unbound_identifier s));
      AVar lsymb

let make_app loc table cntxt (lsymb : lsymb) (l : term list) : app =
  L.mk_loc loc (make_app_i table cntxt lsymb l)


(*------------------------------------------------------------------*)
(** {2 Substitution} *)

type esubst = ESubst : string * Term.term -> esubst

type subst = esubst list

(** Apply a partial substitution to a term.
  * This is meant for formulas and local terms in processes,
  * and does not support optional timestamps.
  * TODO substitution does not avoid capture. *)
let subst t (s : (string * term_i) list) =
  let rec aux_i = function
    (* Variable *)
    | App (x, []) as t ->
      begin try
          let ti = List.assoc (L.unloc x) s in
          ti
        with Not_found -> t
      end
    | Tpat              -> Tpat
    | App (s,l)         -> App (s, List.map aux l)
    | AppAt (s,l,ts)    -> AppAt (s, List.map aux l, aux ts)
    | Seq (vs,t)        -> Seq (vs, aux t)
    | ForAll (vs,f)     -> ForAll (vs, aux f)
    | Exists (vs,f)     -> Exists (vs, aux f)
    | Diff (l,r)        -> Diff (aux l, aux r)
    | Find (is,c,t,e)   -> Find (is, aux c, aux t, aux e)

  and aux t = L.mk_loc (L.loc t) (aux_i (L.unloc t))

  in aux t

(*------------------------------------------------------------------*)
(** {2 Conversion contexts and states} *)

(** Conversion contexts.
  * - [InGoal]: we are converting a term in a goal (or tactic). All
  *   timestamps must be explicitely given.
  * - [InProc ts]: we are converting a term in a process at an implicit
  *   timestamp [ts]. *)
type conv_cntxt =
  | InProc of Term.term
  | InGoal

let is_in_proc = function InProc _ -> true | InGoal -> false

(** Exported conversion environments. *)
type conv_env = { 
  env   : Env.t;
  cntxt : conv_cntxt; 
}

(** Internal conversion states, containing:
    - all the fields of a [conv_env]
    - free type variables
    - a type unification environment
    - a variable substitution  *)
type conv_state = {
  env       : Env.t;
  cntxt     : conv_cntxt;
  allow_pat : bool;

  ty_env    : Type.Infer.env;
}

let mk_state env cntxt allow_pat ty_env =
  { cntxt; env; allow_pat; ty_env; }

(*------------------------------------------------------------------*)
(** {2 Types} *)

let ty_error ty_env tm ty =
  let ty = Type.Infer.norm ty_env ty in
  Conv (L.loc tm, Type_error (L.unloc tm, ty))

let check_ty_leq state ~of_t (t_ty : Type.ty) (ty : Type.ty) : unit =
  match Type.Infer.unify_leq state.ty_env t_ty ty with
  | `Ok -> ()
  | `Fail ->
    raise (ty_error state.ty_env of_t ty)

(* let check_ty_eq state ~of_t (t_ty : Type.ty) (ty : 'b Type.ty) : unit =
 *   match Type.Infer.unify_eq state.ty_env t_ty ty with
 *   | `Ok -> ()
 *   | `Fail -> raise (ty_error state.ty_env of_t ty) *)

let check_term_ty state ~of_t (t : Term.term) (ty : Type.ty) : unit =
  check_ty_leq state ~of_t (Term.ty ~ty_env:state.ty_env t) ty

(*------------------------------------------------------------------*)
(** {2 Conversion} *)

let convert_var 
    (state : conv_state)
    (st    : lsymb)
    (ty    : Type.ty) 
  : Term.term
  =
  try
    let v = Vars.find state.env.vars (L.unloc st) in

    let of_t = var_of_lsymb st in

    check_ty_leq state ~of_t (Vars.ty v) ty;

    Term.mk_var v
  with
  | Not_found -> conv_err (L.loc st) (Undefined (L.unloc st))

let convert_bnds (env : Env.t) (vars : (lsymb * Type.ty) list) =
  let do1 (vars, v_acc) (vsymb, s) =
    let vars, v  = Vars.make `Shadow vars s (L.unloc vsymb) in
    vars, v :: v_acc
  in
  let venv, v_acc = List.fold_left do1 (env.vars, []) vars in
  { env with vars = venv }, List.rev v_acc

let convert_p_bnds (env : Env.t) (vars : bnds) =
  let vs = List.map (fun (v,s) -> v, parse_p_ty env s) vars in
  convert_bnds env vs 

let get_fun table lsymb =
  match Symbols.Function.of_lsymb_opt lsymb table with
  | Some n -> n
  | None ->
    conv_err (L.loc lsymb) (UndefinedOfKind (L.unloc lsymb, Symbols.NFunction))

let get_name table lsymb =
  match Symbols.Name.of_lsymb_opt lsymb table with
  | Some n -> n
  | None ->
    conv_err (L.loc lsymb) (UndefinedOfKind (L.unloc lsymb, Symbols.NName))

let get_action (env : Env.t) lsymb =
  match Symbols.Action.of_lsymb_opt lsymb env.table with
  | Some n -> n
  | None ->
    conv_err (L.loc lsymb) (UndefinedOfKind (L.unloc lsymb, Symbols.NAction))

let get_macro (env : Env.t) lsymb =
  match Symbols.Macro.of_lsymb_opt lsymb env.table with
  | Some n -> n
  | None ->
    conv_err (L.loc lsymb) (UndefinedOfKind (L.unloc lsymb, Symbols.NMacro))

(*------------------------------------------------------------------*)
(* internal function to Theory.ml *)
let rec convert 
    (state : conv_state)
    (tm    : term)
    (ty    : Type.ty) 
  : Term.term
  =
  let t = convert0 state tm ty in
  check_term_ty state ~of_t:tm t ty;
  t

and convert0 
    (state : conv_state)
    (tm : term)
    (ty : Type.ty) : Term.term 
  =
  let loc = L.loc tm in

  let conv ?(env=state.env) s t =
    let state = { state with env } in
    convert state t s in

  let type_error () = raise (ty_error state.ty_env tm ty) in

  match L.unloc tm with
  | Tpat ->
    if not state.allow_pat then
      conv_err (L.loc tm) PatNotAllowed;

    let _, p = Vars.make ~allow_pat:true `Approx state.env.vars ty "_" in
    Term.mk_var p

  (*------------------------------------------------------------------*)
  (* particular cases for init and happens *)

  | App ({ pl_desc = "init" },terms) ->
    if terms <> [] then type_error ();
    Term.mk_action Symbols.init_action []

  (* happens distributes over its arguments *)
  | App ({ pl_desc = "happens" },ts) ->
    let atoms = List.map (fun t ->
        Term.mk_happens (conv Type.Timestamp t)
      ) ts in
    Term.mk_ands atoms

  (* end of special cases *)
  (*------------------------------------------------------------------*)

  | App   (f,terms) ->
    if terms = [] && Vars.mem_s state.env.vars (L.unloc f)
    then convert_var state f ty

    (* otherwise build the application and convert it. *)
    else
      let app_cntxt = match state.cntxt with
        | InGoal -> NoTS |
          InProc ts -> MaybeAt ts in

      conv_app state app_cntxt
        (tm, make_app loc state.env.table app_cntxt f terms)
        ty

  | AppAt (f,terms,ts) ->
    if is_in_proc state.cntxt then conv_err loc ExplicitTSInProc;

    let app_cntxt = At (conv Type.Timestamp ts) in
    conv_app state app_cntxt
      (tm, make_app loc state.env.table app_cntxt f terms)
      ty

  | Diff (l,r) -> Term.mk_diff (conv ty l) (conv ty r)

  | Find (vs,c,t,e) ->
    let env, is =
      convert_bnds state.env (List.map (fun x -> x, Type.tindex) vs)
    in
    
    Vars.check_type_vars is [Type.Index] (type_error ());

    let c = conv ~env Type.Boolean c in
    let t = conv ~env ty t in
    let e = conv ty e in
    Term.mk_find is c t e

  | ForAll (vs,f) | Exists (vs,f) ->
    let env, evs = convert_p_bnds state.env vs in
    let f = conv ~env Type.Boolean f in
    begin match L.unloc tm with
      | ForAll _ -> Term.mk_forall evs f
      | Exists _ -> Term.mk_exists evs f
      | _ -> assert false
    end

  | Seq (vs,t) ->
    let env, evs = convert_p_bnds state.env vs in

    let tyv = Type.Infer.mk_univar state.ty_env in

    let t = conv ~env (Type.TUnivar tyv) t in

    let () =
      Vars.check_type_vars evs [Type.Index; Type.Timestamp] (type_error ())
    in
    Term.mk_seq0 ~simpl:false evs t

and conv_index state t = 
  match convert state t Type.Index with
    | Term.Var x -> x
    | _ -> conv_err (L.loc t) (Index_not_var (L.unloc t))

(* The term [tm] in argument is here for error messages. *)
and conv_app 
    (state     : conv_state)
    (app_cntxt : app_cntxt)
    ((tm,app)  : (term * app)) 
    (ty        : Type.ty) 
  : Term.term
  = 
  (* We should have [make_app app = t].
     [t] is here to have meaningful exceptions. *)
  let loc = L.loc tm in
  let t_i = L.unloc tm in

  let conv ?(env=state.env) s t =
    let state = { state with env } in
    convert state t s in

  let get_at ts_opt =
    match ts_opt, get_ts app_cntxt with
    | Some ts, _ -> ts
    | None, Some ts -> ts
    | None, None -> conv_err loc (Timestamp_expected (L.unloc tm))
  in
  let conv_fapp (f : lsymb) l ts_opt : Term.term =
    let mfty = function_kind state.env.table f in
    let () = check_arity f (List.length l) (mf_type_arity mfty) in

    match Symbols.of_lsymb f state.env.table with
    | Symbols.Wrapped (symb, Function (_,_)) ->
      assert (ts_opt = None);

      let fty = match mfty with `Fun x -> x | _ -> assert false in

      (* refresh all type variables in [fty] *)
      let fty_op = Type.open_ftype state.ty_env fty in

      let l_indices, l_messages = List.takedrop fty_op.Type.fty_iarr l in
      let indices =
        List.map (fun x -> conv_index state x) l_indices
      in

      let rmessages =
        List.fold_left2 (fun rmessages t ty ->
            let t = conv ty t in
            t :: rmessages
          ) [] l_messages fty_op.Type.fty_args
      in
      let messages = List.rev rmessages in

      let t = Term.mk_fun0 (symb,indices) fty messages in

      (* additional type check between the type of [t] and the output
         type in [fty].
         Note that [convert] checks that the type of [t] is a subtype
         of [ty], hence we do not need to do it here. *)
      check_term_ty state ~of_t:tm t fty_op.Type.fty_out;

      t

    (* FIXME: messy code *)
    | Wrapped (s, Symbols.Macro macro) ->
      let ty_args, ty_out =
        match mfty with `Macro x -> x | _ -> assert false
      in
      begin match macro with
        | Symbols.State _ -> assert false

        | Symbols.Global _ ->
          assert (List.for_all (fun x -> x = Type.Index) ty_args);
          let indices = List.map (conv_index state) l in
          let ms = Term.mk_isymb s ty_out indices in
          Term.mk_macro ms [] (get_at ts_opt)

        | Input | Output | Frame ->
          check_arity_i (L.loc f) "input" (List.length l) 0 ;
          (* TODO: subtypes *)
          let ms = Term.mk_isymb s ty_out [] in
          Term.mk_macro ms [] (get_at ts_opt)

        | Cond | Exec ->
          check_arity_i (L.loc f) "cond" (List.length l) 0 ;
          let ms = Term.mk_isymb s ty_out [] in
          Term.mk_macro ms [] (get_at ts_opt)

      end

    | Wrapped (_, _) -> assert false
  in


  match L.unloc app with
  | AVar s -> convert_var state s ty

  | Fun (f,l,ts_opt) -> conv_fapp f l ts_opt

  | Get (s,opt_ts,is) ->
    let k = check_state state.env.table s (List.length is) in
    let is = List.map (conv_index state) is in
    let s = get_macro state.env s in
    let ts =
      (* TODO: check this *)
      match opt_ts with
      | Some ts -> ts
      | None -> conv_err loc (Timestamp_expected t_i)
    in
    let ms = Term.mk_isymb s k is in
    Term.mk_macro ms [] ts

  | Name (s, is) ->
    let sty = check_name state.env.table s (List.length is) in
    let is = List.map (conv_index state) is in
    let ns = Term.mk_isymb (get_name state.env.table s) sty is in
    Term.mk_name ns

  | Taction (a,is) ->
    check_action state.env a (List.length is) ;
    Term.mk_action
      (get_action state.env a)
      (List.map (conv_index state) is)

(*------------------------------------------------------------------*)
(** convert HO terms *)
let conv_ht (state : conv_state) (t : hterm) : Type.hty * Term.hterm =
  match L.unloc t with
  | Lambda (bnds, t0) ->
    let env, evs = convert_p_bnds state.env bnds in
    let state = { state with env } in

    let tyv = Type.Infer.mk_univar state.ty_env in
    let ty = Type.TUnivar tyv in

    let ht = Term.Lambda (evs, convert state t0 ty) in

    let bnd_tys = List.map Vars.ty evs in
    let hty = Type.Lambda (bnd_tys, ty) in

    hty, ht

(*------------------------------------------------------------------*)
(** {2 Function declarations} *)

let mk_ftype iarr vars args out =
  let mdflt ty = odflt Type.Message ty in
  Type.mk_ftype iarr vars (List.map mdflt args) (mdflt out)

let declare_ddh table ?group_ty ?exp_ty gen exp (f_info : Symbols.symb_type) =
  let open Symbols in
  let gen_fty = mk_ftype 0 [] [] group_ty in
  let exp_fty = mk_ftype 0 [] [group_ty; exp_ty] group_ty in

  let table, exp = Function.declare_exact table exp (exp_fty,Abstract f_info) in
  let data = AssociatedFunctions [exp] in
  fst (Function.declare_exact table ~data gen (gen_fty,DDHgen))

let declare_hash table ?index_arity ?m_ty ?k_ty ?h_ty s =
  let index_arity = odflt 0 index_arity in
  let ftype = mk_ftype index_arity [] [m_ty; k_ty] h_ty in
  let def = ftype, Symbols.Hash in
  fst (Symbols.Function.declare_exact table s def)

let declare_aenc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?sk_ty ?pk_ty enc dec pk =
  let open Symbols in
  let dec_fty = mk_ftype 0 [] [ctxt_ty; sk_ty] ptxt_ty in
  let enc_fty = mk_ftype 0 [] [ptxt_ty; rnd_ty; pk_ty] ctxt_ty in
  let pk_fty  = mk_ftype 0 [] [sk_ty] pk_ty in

  let table, pk = Function.declare_exact table pk (pk_fty,PublicKey) in
  let dec_data = AssociatedFunctions [Function.cast_of_string (L.unloc enc); pk] in
  let table, dec = Function.declare_exact table dec ~data:dec_data (dec_fty,ADec) in
  let data = AssociatedFunctions [dec; pk] in
  fst (Function.declare_exact table enc ~data (enc_fty,AEnc))

let declare_senc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty enc dec =
  let open Symbols in
  let data = AssociatedFunctions [Function.cast_of_string (L.unloc enc)] in
  let dec_fty = mk_ftype 0 [] [ctxt_ty; k_ty] ptxt_ty in
  let enc_fty = mk_ftype 0 [] [ptxt_ty; rnd_ty; k_ty] ctxt_ty in

  let table, dec = Function.declare_exact table dec ~data (dec_fty,SDec) in
  let data = AssociatedFunctions [dec] in
  fst (Function.declare_exact table enc ~data (enc_fty,SEnc))

let declare_senc_joint_with_hash
    table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty enc dec h =
  let open Symbols in
  let data = AssociatedFunctions [Function.cast_of_string (L.unloc enc);
                                  get_fun table h] in
  let dec_fty = mk_ftype 0 [] [ctxt_ty; k_ty] ptxt_ty in
  let enc_fty = mk_ftype 0 [] [ptxt_ty; rnd_ty; k_ty] ctxt_ty in
  let table, dec = Function.declare_exact table dec ~data (dec_fty,SDec) in
  let data = AssociatedFunctions [dec] in
  fst (Function.declare_exact table enc ~data (enc_fty,SEnc))

let declare_signature table
    ?m_ty ?sig_ty ?check_ty ?sk_ty ?pk_ty
    sign checksign pk =
  let open Symbols in
  let sig_fty   = mk_ftype 0 [] [m_ty; sk_ty] sig_ty in

  (* TODO: change output type to booleans ? *)
  let check_fty = mk_ftype 0 [] [sig_ty; pk_ty] check_ty in

  let pk_fty    = mk_ftype 0 [] [sk_ty] pk_ty in

  let table,sign = Function.declare_exact table sign (sig_fty, Sign) in
  let table,pk = Function.declare_exact table pk (pk_fty,PublicKey) in
  let data = AssociatedFunctions [sign; pk] in
  fst (Function.declare_exact table checksign ~data (check_fty,CheckSign))

let check_signature table checksign pk =
  let def x = Symbols.Function.get_def x table in
  let correct_type = match def checksign, def pk  with
    | (_,Symbols.CheckSign), (_,Symbols.PublicKey) -> true
    | _ -> false
  in
  if correct_type then
    match Symbols.Function.get_data checksign table with
      | Symbols.AssociatedFunctions [sign; pk2] when pk2 = pk -> Some sign
      | _ -> None
  else None

let declare_name table s ndef =
  fst (Symbols.Name.declare_exact table s ndef)

let declare_abstract 
    table ~index_arity ~ty_args ~in_tys ~out_ty 
    (s : lsymb) (f_info : Symbols.symb_type) 
  =
  (* if we declare an infix symbol, run some sanity checks *)
  let () = match f_info with
    | `Prefix -> ()
    | `Infix ->
      if not (index_arity = 0) ||
         not (List.length ty_args = 0) ||
         not (List.length in_tys = 2) then
        conv_err (L.loc s) BadInfixDecl;
  in

  let ftype = Type.mk_ftype index_arity ty_args in_tys out_ty in
  fst (Symbols.Function.declare_exact table s (ftype, Symbols.Abstract f_info))


(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

(** Empty *)
let empty loc = L.mk_loc loc (App (L.mk_loc loc "empty", []))

(*------------------------------------------------------------------*)
(** {2 Exported conversion and type-checking functions} *)


let convert_ht
    ?ty_env
    ?(pat=false) 
    (cenv : conv_env)
    (ht0 : hterm)
  : Type.hty * Term.hterm 
  = 
  let must_close, ty_env = match ty_env with
    | None -> true, Type.Infer.mk_env ()
    | Some ty_env -> false, ty_env
  in

  let state = mk_state cenv.env cenv.cntxt pat ty_env in
  let hty, ht = conv_ht state ht0 in

  if must_close then
    begin
      if not (Type.Infer.is_closed state.ty_env) then
        conv_err (L.loc ht0) Freetyunivar;

      let tysubst = Type.Infer.close ty_env in
      Type.tsubst_ht tysubst hty, Term.tsubst_ht tysubst ht
    end
  else
    Type.Infer.htnorm state.ty_env hty, ht


(*------------------------------------------------------------------*)
let check
    (env : Env.t) ?(local=false) ?(pat=false) 
    (ty_env : Type.Infer.env)
    t (s : Type.ty) 
  : unit 
  =
  let dummy_var s =
    Term.mk_var (snd (Vars.make `Approx Vars.empty_env s "#dummy"))
  in
  let cntxt = if local then InProc (dummy_var Type.Timestamp) else InGoal in
  
  let state = mk_state env cntxt pat ty_env in
  ignore (convert state t s)

(** exported outside Theory.ml *)
let convert 
    ?(ty     : Type.ty option)
    ?(ty_env : Type.Infer.env option) 
    ?(pat    : bool = false)
    (cenv    : conv_env) 
    (tm      : term) 
  : Term.term * Type.ty
  =
  let must_close, ty_env = match ty_env with
    | None        -> true, Type.Infer.mk_env ()
    | Some ty_env -> false, ty_env
  in
  let ty = match ty with
    | None    -> Type.TUnivar (Type.Infer.mk_univar ty_env) 
    | Some ty -> ty 
  in
  let state = mk_state cenv.env cenv.cntxt pat ty_env in
  let t = convert state tm ty in

  if must_close then
    begin
      if not (Type.Infer.is_closed state.ty_env) then
        conv_err (L.loc tm) Freetyunivar;

      let tysubst = Type.Infer.close ty_env in
      Term.tsubst tysubst t, Type.tsubst tysubst ty
    end
  else
    t, Type.Infer.norm ty_env ty

(*------------------------------------------------------------------*)
(** {2 Convert equiv formulas} *)

let convert_equiv cenv (e : equiv) =
  let convert_el el : Term.term =
    let t, _ = convert cenv el in
    t
  in
  List.map convert_el e

let convert_global_formula (cenv : conv_env) (p : global_formula) =
  let rec conve (cenv : conv_env) p =
    let conve ?(env=cenv.env) p = conve { cenv with env } p in

    match L.unloc p with
    | PImpl (f1, f2) -> Equiv.Impl (conve f1, conve f2)
    | PAnd  (f1, f2) -> Equiv.And  (conve f1, conve f2)
    | POr   (f1, f2) -> Equiv.Or   (conve f1, conve f2)

    | PEquiv e ->
      Equiv.Atom (Equiv.Equiv (convert_equiv cenv e))

    | PReach f ->
      let f, _ = convert ~ty:Type.Boolean cenv f in
      Equiv.Atom (Equiv.Reach f)


    | PQuant (q, bnds, e) ->
      let env, evs = convert_p_bnds cenv.env bnds in
      let e = conve ~env e in
      let q = match q with
        | PForAll -> Equiv.ForAll
        | PExists -> Equiv.Exists
      in
      Equiv.mk_quant q evs e
  in

  conve cenv p

(*------------------------------------------------------------------*)
(** {2 State and substitution parsing} *)

let parse_subst (env : Env.t) (uvars : Vars.var list) (ts : term list)
  : Term.subst =
  let conv_env = { env; cntxt = InGoal; } in
  let f t u =
    let t, _ = convert ~ty:(Vars.ty u) conv_env t in
    Term.ESubst (Term.mk_var u, t)
  in
  List.map2 f ts uvars

type Symbols.data += StateInit_data of Vars.var list * Term.term

let declare_state
    (table      : Symbols.table)
    (s          : lsymb) 
    (typed_args : bnds) 
    (pty        : p_ty) 
    (t          : term) 
  =
  let ts_init = Term.mk_action Symbols.init_action [] in
  
  let env = Env.init ~table () in
  let conv_env = { env; cntxt = InProc ts_init; } in

  let env, indices = convert_p_bnds env typed_args in
  let conv_env = { conv_env with env } in
  
  Vars.check_type_vars indices [Type.Index]
    (conv_err (L.loc pty) (BadPty [Type.Index]));

  (* parse the macro type *)
  let ty = parse_p_ty env pty in

  let t, _ = convert ~ty conv_env t in

  let data = StateInit_data (indices,t) in
  let table, _ =
    Symbols.Macro.declare_exact table
      s
      ~data
      (Symbols.State (List.length typed_args,ty)) in
  table

let get_init_states table : (Term.state * Term.term) list =
  Symbols.Macro.fold (fun s def data acc ->
      match (def,data) with
      | ( Symbols.State (arity,kind), StateInit_data (l,t) ) ->
        assert (Type.equal kind (Term.ty t));
        let state = Term.mk_isymb s kind l in
        (state,t) :: acc
      | _ -> acc
    ) [] table

(* TODO could be generalized into a generic fold function
 * fold : (term -> 'a -> 'a) -> term -> 'a -> 'a *)
let find_app_terms t (names : string list) =
  let rec aux (name : string) acc t = match L.unloc t with
    | App (x',l) ->
      let acc = if L.unloc x' = name then L.unloc x'::acc else acc in
      aux_list name acc l

    | AppAt (x',l,ts) ->
      let acc = if L.unloc x' = name then L.unloc x'::acc else acc in
      aux_list name acc (ts :: l)

    | Exists (_,t')
    | ForAll (_,t') -> aux name acc t'

    (* FIXME: I think some cases may be missing *)
    | _                 -> acc

  and aux_list name acc l =
    List.fold_left (aux name) acc l in

  let acc = List.fold_left (fun acc name -> aux name acc t) [] names in
  List.sort_uniq Stdlib.compare acc

(*------------------------------------------------------------------*)
(** {2 Apply arguments} *)

(** proof term *)
type p_pt = {
  p_pt_head : lsymb;
  p_pt_args : p_pt_arg list;
  p_pt_loc  : L.t;
}

(** proof term argument *)
and p_pt_arg =
  | PT_term of term
  | PT_sub  of p_pt             (* sub proof term *)
  | PT_obl  of L.t              (* generate a proof obligation *)

(*------------------------------------------------------------------*)
(** {2 Tests} *)
let () =
  let mk x = L.mk_loc L._dummy x in
  Checks.add_suite "Theory" [
    "Declarations", `Quick,
    begin fun () ->
      ignore (declare_hash Symbols.builtins_table (mk "h") : Symbols.table);
      let table = declare_hash Symbols.builtins_table (mk "h") in
      Alcotest.check_raises
        "h cannot be defined twice"
        (Symbols.SymbError (L._dummy, Multiple_declarations "h"))
        (fun () -> ignore (declare_hash table (mk "h") : Symbols.table)) ;
      let table = declare_hash Symbols.builtins_table (mk "h") in
      Alcotest.check_raises
        "h cannot be defined twice"
        (Symbols.SymbError (L._dummy, Multiple_declarations "h"))
        (fun () -> ignore (declare_aenc table (mk "h") (mk "dec") (mk "pk")
                           : Symbols.table) )
    end;

    "Term building", `Quick,
    begin fun () ->
      let table = declare_hash Symbols.builtins_table (mk "h") in
      ignore (make_app L._dummy table NoTS (mk "x") []) ;
      Alcotest.check_raises
        "hash function expects two arguments"
        (Conv (L._dummy, Arity_error ("h",1,2)))
        (fun () ->
           ignore (make_app L._dummy table NoTS (mk "h") [mk (App (mk "x",[]))])) ;
      ignore (make_app
                L._dummy table NoTS (mk "h") [mk (App (mk "x",[]));
                                              mk (App (mk "y",[]))])
    end ;

    "Type checking", `Quick,
    begin fun () ->
      let table =
        declare_aenc Symbols.builtins_table (mk "e") (mk "dec") (mk "pk")
      in
      let table = declare_hash table (mk "h") in
      let x = mk (App (mk "x", [])) in
      let y = mk (App (mk "y", [])) in

      let vars = Vars.empty_env in
      let vars, _ = Vars.make `Approx vars Type.Message "x" in
      let vars, _ = Vars.make `Approx vars Type.Message "y" in
      let env = Env.init ~vars ~table () in

      let t_i = App (mk "e", [mk (App (mk "h", [x;y]));x;y]) in
      let t = mk t_i in
      let ty_env = Type.Infer.mk_env () in
      check env ty_env t Type.tmessage ;
      Alcotest.check_raises
        "message is not a boolean"
        (Conv (L._dummy, Type_error (t_i, Type.tboolean)))
        (fun () -> check env ty_env t Type.tboolean)
    end
  ]
