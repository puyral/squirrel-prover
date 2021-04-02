(** {2 SSCs checking} *)

(** Exception thrown when the axiom syntactic side-conditions do not hold. *)
exception Bad_ssc

(** Iterate on terms, raise Bad_ssc if the hash key occurs other than
  * in key position or if a message variable is used.
  *
  * We use the inexact version of [iter_approx_macros]: it allows
  * some macros to be undefined, though such instaces will not be
  * supported when collecting hashes; more importantly, it avoids
  * inspecting each of the multiple expansions of a same macro. *)
class check_key
    ~allow_vars ~allow_functions
    ~cntxt head_fn key_n = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~full:true ~cntxt as super
  method visit_message t = match t with
    | Term.Fun ((fn,_), [m;Term.Name _]) when fn = head_fn ->
      self#visit_message m
    | Term.Fun ((fn,_), [m1;m2;Term.Name _]) when fn = head_fn ->
      self#visit_message m1; self#visit_message m2
    | Term.Fun ((fn,_), [Term.Name _])
    | Term.Fun ((fn,_), [Term.Diff (Term.Name _, Term.Name _)])
    | Term.Fun ((fn,_), [_; Term.Name _])
    | Term.Fun ((fn,_), [_; Term.Diff (Term.Name _, Term.Name _)])
      when allow_functions fn -> ()
    | Term.Name (n,_) when n = key_n -> raise Bad_ssc
    | Term.Var m -> if not(allow_vars) then raise Bad_ssc
    | _ -> super#visit_message t
end

(** Collect occurences of some function and key,
  * as in [Iter.get_f_messages] but ignoring boolean terms,
  * cf. Koutsos' PhD. *)
class get_f_messages ~drop_head ~cntxt head_fn key_n = object (self)
  inherit Iter.get_f_messages ~drop_head ~cntxt head_fn key_n
  method visit_formula _ = ()
end

(** Check the key syntactic side-condition in the given list of messages
  * and in the outputs, conditions and updates of all system actions:
  * [key_n] must appear only in key position of [head_fn].
  * Return unit on success, raise [Bad_ssc] otherwise. *)
let key_ssc
    ?(allow_vars=false) ?(messages=[]) ?(elems=[]) ~allow_functions
    ~cntxt head_fn key_n =
  let ssc = 
    new check_key ~allow_vars ~allow_functions ~cntxt head_fn key_n 
  in
  List.iter ssc#visit_message messages ;
  List.iter ssc#visit_term elems ;
  SystemExpr.(iter_descrs cntxt.table cntxt.system
    (fun action_descr ->
       ssc#visit_formula (snd action_descr.condition) ;
       ssc#visit_message (snd action_descr.output) ;
       List.iter (fun (_,t) -> ssc#visit_message t) action_descr.updates))

(** Same as [hash_key_ssc] but returning a boolean.
  * This is used in the collision tactic, which looks for all h(_,k)
  * such that k satisfies the SSC. *)
let check_key_ssc
    ?(allow_vars=false) ?(messages=[]) ?(elems=[]) ~allow_functions 
    ~cntxt head_fn key_n =
  try
    key_ssc
      ~allow_vars ~messages ~elems ~allow_functions
      ~cntxt head_fn key_n ;
    true
  with Bad_ssc -> false

(*------------------------------------------------------------------*)
(** [hashes_of_action_descr ~system action_descr head_fn key_n]
  * returns the list of pairs [is,m] such that [head_fn(m,key_n[is])]
  * occurs in [action_descr]. *)
let hashes_of_action_descr
    ?(drop_head=true) ~cntxt action_descr head_fn key_n =
  let iter = new get_f_messages ~drop_head ~cntxt head_fn key_n in
  iter#visit_message (snd action_descr.Action.output) ;
  List.iter (fun (_,m) -> iter#visit_message m) action_descr.Action.updates ;
  List.sort_uniq Stdlib.compare iter#get_occurrences

(*------------------------------------------------------------------*)
(** {2 Euf rules datatypes} *)

type euf_schema = { message : Term.message;
                    key_indices : Vars.index list;
                    action_descr : Action.descr;
                    env : Vars.env }

let pp_euf_schema ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*action:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Action.pp_descr_short case.action_descr
    Term.pp case.message

(** Type of a direct euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices]. *)
type euf_direct = { d_key_indices : Vars.index list;
                    d_message : Term.message }

let pp_euf_direct ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*key indices:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Vars.pp_list case.d_key_indices
    Term.pp case.d_message

type euf_rule = { hash : Term.fname;
                  key : Term.name;
                  case_schemata : euf_schema list;
                  cases_direct : euf_direct list }

let pp_euf_rule ppf rule =
  Fmt.pf ppf "@[<v>*hash: @[<hov>%a@]@;\
              *key: @[<hov>%a@]@;\
              *case schemata:@;<1;2>@[<v>%a@]@;\
              *direct cases:@;<1;2>@[<v>%a@]@]"
    Term.pp_fname rule.hash
    Term.pp_name rule.key
    (Fmt.list pp_euf_schema) rule.case_schemata
    (Fmt.list pp_euf_direct) rule.cases_direct

(*------------------------------------------------------------------*)
(** {2 Build the Euf rule} *)

let mk_rule ?(elems=[]) ?(drop_head=true)
    ~allow_functions ~cntxt ~env ~mess ~sign ~head_fn ~key_n ~key_is =

  let mk_of_hash action_descr (is,m) =
    (* Indices [key_is] from [env] must correspond to [is],
     * which contains indices from [action_descr.indices]
     * but also bound variables.
     *
     * Rather than refreshing all action indices, and generating
     * new variable names for bound variables, we avoid it in
     * simple cases: if a variable only occurs once in
     * [is] then the only equality constraint on it is that
     * it must be equal to the corresponding variable of [key_is],
     * hence we can replace it by that variable rather
     * than creating a new variable and an equality constraint.
     * This is not sound with multiple occurrences in [is] since
     * they induce equalities on the indices that pre-exist in
     * [key_is].
     *
     * We compute next the list [safe_is] of simple cases,
     * and the substitution for them. *)
    let env = ref env in

    let safe_is,subst_is =
      let multiple i =
        let n = List.length (List.filter ((=) i) is) in
        assert (n > 0) ;
        n > 1
      in
      List.fold_left2 (fun (safe_is,subst) i j ->
          if multiple i then safe_is,subst else
            i::safe_is,
            Term.(ESubst (Var i, Var j))::subst
        ) ([],[]) is key_is
    in

    (* Refresh action indices other than [safe_is] indices. *)
    let subst_fresh =
      List.map (fun i ->
          Term.(ESubst (Var i,
                        Var (Vars.make_fresh_from_and_update env i))))
        (List.filter
           (fun x -> not (List.mem x safe_is))
           action_descr.Action.indices)
    in

    (* Refresh bound variables from m and is, except those already
     * handled above. *)
    let subst_bv =
      (* Compute variables from m, add those from is
       * while preserving unique occurrences in the list. *)
      let vars = Term.get_vars m in
      let vars =
        List.fold_left (fun vars i ->
            if List.mem (Vars.EVar i) vars then vars else
              Vars.EVar i :: vars
          ) vars is
      in
      (* Remove already handled variables, create substitution. *)
      let index_not_seen i =
        not (List.mem i safe_is) &&
        not (List.mem i action_descr.Action.indices)
      in
      let not_seen = function
        | Vars.EVar v -> match Vars.ty v with
          | Type.Index -> index_not_seen v
          | _ -> true
      in

      let vars = List.filter not_seen vars in
      List.map
        (function Vars.EVar v ->
           Term.(ESubst (Var v,
                         Var (Vars.make_fresh_from_and_update env v))))
        vars
    in
    
    let subst = subst_fresh @ subst_is @ subst_bv in
    let new_action_descr = Action.subst_descr subst action_descr in
    { message = Term.subst subst m ;
      key_indices = List.map (Term.subst_var subst) is ;
      action_descr = new_action_descr;
      env = !env }
  in

  let mk_case_schema action_descr =
    let hashes = 
      hashes_of_action_descr ~drop_head ~cntxt action_descr head_fn key_n
    in

    List.map (mk_of_hash action_descr) hashes
  in

  (* indirect cases *)
  let case_schemata = 
    SystemExpr.map_descrs cntxt.table cntxt.system mk_case_schema 
  in

  (* direct cases *)
  let cases_direct = 
    let hashes =
      let iter = 
        new get_f_messages ~drop_head ~cntxt head_fn key_n 
      in
      iter#visit_message mess ;
      iter#visit_message sign ;
      List.iter iter#visit_term elems ;
      iter#get_occurrences
    in
    List.map
      (fun (d_key_indices,d_message) -> {d_key_indices;d_message})
      hashes
  in

  { hash          = head_fn;
    key           = key_n;
    case_schemata = List.flatten case_schemata;
    cases_direct  = cases_direct; }
