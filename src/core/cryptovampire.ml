open Utils
open Yojson 
open Ppx_yojson_conv_lib.Yojson_conv.Primitives
open Term 
open Type
module SE = SystemExpr
module S = Symbols

type descr = Action.descr
type json = Yojson.Safe.t

let (<$>) = List.map


  (* let (<@>) (`Assoc l) (`Assoc l') =  `Assoc (l @ l')

let (<<@>) (e: string * json) (`Assoc l) = `Assoc (e::l)
let (<@>>) (`Assoc l) (e: string * json) = `Assoc (e::l) *)
let (<<@>>) (e: string * json) (e': string * json) = `Assoc ([e; e'])
let (<<@) (e:string) (d:json) = `Assoc [e, d]

(* Let's go with PascalCase everywhere if possible *)

let rec yojson_of_term : Term.term -> json = function
  |App (f,tl) -> 
    `Assoc ["constructor", `String "App";
      "f", yojson_of_term f;
      "args", `List (List.map yojson_of_term tl)]
  |Fun (f,_) -> 
    `Assoc ["constructor", `String "Fun";
      "symb", `String (Symbols.to_string f)]
  |Name (n,tl) -> 
    `Assoc ["constructor", `String "Name";
      "symb", `String (Symbols.to_string n.s_symb);
      "arguments", `List (List.map yojson_of_term tl)]
  |Macro (m,tl,ts) -> 
    `Assoc ["constructor", `String "Macro";
      "symb", `String (Symbols.to_string m.s_symb);
      "arguments", `List (List.map yojson_of_term tl);
      "timestamp", yojson_of_term ts]
  |Action (a,tl) -> 
    `Assoc ["constructor", `String "Action";
      "symb", `String (Symbols.to_string a);
      "arguments", `List (List.map yojson_of_term tl)]
  |Var (v) -> 
    `Assoc ["constructor", `String "Var" ;
      "id", `Int (Vars.hash v);
      "name", `String (Vars.name v) ]
  |Let (v,t1,t2) -> 
    `Assoc ["constructor", `String "Let" ;
      "var", yojson_of_term (mk_var v);
      "decl", yojson_of_term t1;
      "body", yojson_of_term t2 ]
  |Tuple (tl) -> 
    `Assoc ["constructor", `String "Tuple";
      "elements",`List (List.map yojson_of_term tl)]
  |Proj (i,t1) -> 
    `Assoc ["constructor", `String "Proj" ;
      "id", `Int i;
      "body", yojson_of_term t1]
  |Diff (Explicit td) -> ignore td;
    `Assoc ["constructor", `String "Diff" ;
      "terms", `List (List.map (fun (p,t') ->
         `Assoc ["proj", `String (proj_to_string p); "term", yojson_of_term t'])
        td) ]
  |Find (vl,t1,t2,t3) ->
      `Assoc ["constructor", `String "Find";
        "vars", `List (List.map (fun v -> (yojson_of_term (mk_var v))) vl);
        "condition", yojson_of_term t1;
        "success", yojson_of_term t2;
        "faillure", yojson_of_term t3]
  |Quant (q,vl,t1) -> ignore q;
    `Assoc ["constructor", `String "Quant";
      "quantficator", Term.yojson_of_quant q;
      "vars", `List (List.map (fun v -> (yojson_of_term (mk_var v))) vl);
      "body", yojson_of_term t1]


(* let abs_symb f table = 
  if Symbols.OpData.is_abstract f table then 
    let def,assoc_fun = Symbols.OpData.get_abstract_data f table in 
    let ls = List.map 
      (fun f -> let f_def,_ = Symbols.OpData.get_abstract_data f table in 
        `Assoc ["Name", `String (Symbols.to_string f);
        "Def", `String (Format.asprintf "%a" Symbols.OpData.pp_abstract_def f_def)]) 
    assoc_fun in 
    Some (`Assoc ["Def",`String (Format.asprintf "%a" Symbols.OpData.pp_abstract_def def); "AssocFun", `List ls])
  else
    None *)

let get_actions_descr_list (table: S.table) (system: SE.fset) : Action.descr list =
  SystemExpr.map_descrs (fun x -> x) table system

(* let cryptovampire_export (s:TraceSequent.t) : unit = 
  let env = TraceSequent.env s in 
  let system = match SystemExpr.to_fset env.system.set with 
    | exception SystemExpr.(Error (_,Expected_fset)) -> Tactics.(hard_failure (Failure "I was told to error out in this case"))
    | fsys -> fsys 
  in 
  let evars = Vars.to_vars_list env.vars 
  and table = env.table in 
  let actions  = SystemExpr.map_descrs (fun x -> x)  table system in
  (* let all_actions = SE.actions table system in *)
  let fun_table =
    Symbols.Operator.fold
    (fun fname _ acc -> 
      ((Symbols.OpData.get_data fname table).ftype, Symbols.to_string fname, abs_symb fname table)::acc)
    []
    table
  and name_table = 
    Symbols.Name.fold 
      (fun name _ acc -> 
        ((Symbols.get_name_data name table).n_fty, Symbols.to_string name,None)::acc  
      )  
      [] 
      table
  and macro_table = 
    Symbols.Macro.fold 
    (fun mn _ acc -> 
      let def = Symbols.get_macro_data mn table 
      and str = Symbols.to_string mn in  
      let indices,ty = match def with 
        | Input | Output | Frame -> 0,Message 
        | Exec | Cond -> 0, Boolean 
        | State (i,t,_) | Global (i,t,_) -> i,t   
      in (str,indices,ty)::acc
    )
    [] 
    table
  in
  let conclusion = LowTraceSequent.conclusion s in 
  let hypotheses = 
    List.filter_map 
      (function 
        |_,Hyps.LHyp (Equiv.Local h) -> Some h
        | _, Hyps.LHyp (Equiv.(Global Atom (Reach f))) -> Some f
        | _ -> None(*TODO*))
    (LowTraceSequent.Hyps.to_list s)
  in 
  let j_export = `Assoc ["Conclusion", yojson_of_term conclusion;
  "Hypotheses", `List (List.map yojson_of_term hypotheses);
  "Variables", `List (List.map Vars.yojson_of_var evars);
  (* "Functions", `List (List.map operator_to_json fun_table); *)
  (* "Names", `List (List.map operator_to_json name_table); *)
  (* "Macros", `List (List.map macro_to_json macro_table)] in  *)
  (* Format.printf "%s@." (Basic.pretty_to_string j_export) ; *)
  ] in

  let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sq.json" in 
  let ppf = Format.formatter_of_out_channel oc in 
  Format.fprintf ppf "%s@." (Safe.to_string j_export)  *)


module type MSymbol = sig
include S.SymbolKind
  type mdata
[@@deriving yojson_of]
  val mdata_of_data : S.data -> mdata option

  val name: string
end

module MExtra (N : MSymbol) = struct
  let yojson_of_symb x = `String (S.to_string x)
  
  type content = 
  { symb: N.ns S.t; data: N.mdata}

  let yojson_of_content ({symb; data}:content) =
  ("symb", yojson_of_symb symb) <<@>> ("data", N.yojson_of_mdata data)

  let get_content_list (table: S.table): content list =
    N.fold (fun symb data acc -> {symb; data=Option.get (N.mdata_of_data data)}::acc) [] table
end


(* let json_of_ftype ({fty_vars; fty_args; fty_out}:Type.ftype)  =
  ("Vars", `List (json_of_tvar <$> fty_vars)) 
    <<@>> ("Args", `List (json_of_ty <$> fty_args)) 
    <@>> ("Out", json_of_ty fty_out) *)

module MType : MSymbol = struct
  include S.BType
  type mdata = S.TyInfo.t list
[@@deriving yojson_of]
  let mdata_of_data = function
  | S.TyInfo.Type l -> Some l
  | _ -> None

  let name = "Type"
end

module MOperator : MSymbol = struct
  include S.Operator
  type mdata = S.OpData.op_data
  let mdata_of_data = function
    | S.OpData.Operator data -> Some data
    | _ -> None
  
    let name = "Operator"
  let yojson_of_mdata ({ftype; def}: mdata) =

    let json_of_concrete ({name; ty_vars; args; out_ty; body}: Operator.concrete_operator) =
      `Assoc [
        "name", `String name;
        "type_variables", `List (yojson_of_tvar <$> ty_vars);
        "args", `List (Vars.yojson_of_var <$> args);
        "out_type", yojson_of_ty out_ty;
        "body", yojson_of_term body
      ]
    in
    let json_of_def = function
      | S.OpData.Abstract (adef, afun) -> ("abstract_def", S.OpData.yojson_of_abstract_def adef) <<@>> 
      ("associated_fun", `List  ((fun s -> `String (S.to_string s)) <$>  afun))
      | S.OpData.Concrete (Operator.Val c) -> json_of_concrete c
      | _ -> assert false
  in ("type", Type.yojson_of_ftype ftype) <<@>> ("def", json_of_def def)
end
module MOperatorExtra = MExtra(MOperator)


module MName : MSymbol = struct
  include S.Name
  type mdata = S.name_data
  let mdata_of_data = function
    | S.Name data -> Some data
    | _ -> None
    let name = "Name"

  let yojson_of_mdata ({n_fty}:mdata) = Type.yojson_of_ftype n_fty
end
module MNameExtra = MExtra(MName)

module MMacro : MSymbol = struct
  include S.Macro
  type mdata =  S.macro_data
  let mdata_of_data = function
  | S.Macro d -> Some d
  | _ -> None

    (* TODO *)
  let yojson_of_mdata = 
    (* let yojson_of_state_macro_def = function
      | Theory.State *)
    function
    | S.Input -> `String "Input"
    | S.Output -> `String "Output"
    | S.Cond -> `String "Cond"
    | S.Exec -> `String "Exec"
    | S.Frame -> `String "Frame"
    | S.State (arity, ty, _) -> "State" <<@ `Assoc [
      "arity", yojson_of_int arity;
      "type", yojson_of_ty ty;
      (* state_macro_def is unreachable *)
    ]
    | S.Global _ -> `String "Global" (* not supported by cv anyway *)

  let name = "Macro"
end
module MMacroExtra = MExtra(MMacro)

module MAction: MSymbol = struct 
  include S.Action
  type mdata = Vars.var list * Action.action_v
  let mdata_of_data = function
  | Action.ActionData (Action.Def (vars, a)) -> Some (vars, Action.to_action_v a)
  | _ -> None

  let yojson_of_mdata _ = 
    `Assoc []
  let name = "Action"
end

(* module MLemma: MSymbol = struct
include S.Lemma
type mdata = 
end *)

let yojson_of_descr (a:descr): json = 
  let yojson_of_lvars v:json = `List (Vars.yojson_of_var <$> v) in
  let yojson_of_updates lu:json =
    let aux (symb, args, body) =
      `Assoc ["symb", `String (S.to_string symb);
              "args", `List (yojson_of_term <$> args);
              "body", yojson_of_term body]
    in `List (aux <$> lu) in
  let open Action in
  let {
    name;
    action;
input;
indices;
condition=(cvars, cond);
updates=lu;
output=(c, msg);
globals
  } = a in
  `Assoc [
  "name", `String (S.to_string name) ;
  "action", Action.yojson_of_action_v action ;
  "input", `String (S.to_string input) ;
  "indices",  yojson_of_lvars indices;
  "condition", ("vars", yojson_of_lvars cvars) <<@>> ("term", yojson_of_term cond) ;
  "updates", yojson_of_updates lu;
  "output", ("channel", `String (S.to_string c)) <<@>> ("term", yojson_of_term msg);
  "globals", `List ((fun x -> `String  (S.to_string x)) <$> globals)
]

(** Context surounding cv, this gather all the sq info that needs to be sent *)
type cv_context = {
  query: term; (** the query to be proven*)
  hypotheses : term list; (** list of hypothesis *)
  variables: Vars.var list; (** list of free variables in `hypotheses` and `query`*)
  actions: descr list;
  names: MNameExtra.content list;
  operators: MOperatorExtra.content list;
  macros: MMacroExtra.content list
  (* table: S.table; * the symbol table *)
  (* types: Sy *)
}
[@@deriving yojson_of]
let yojson_of_cv_context x = Json.to_assoc (yojson_of_cv_context x)

let make_cv_context (s:TraceSequent.t): cv_context =
  (* shortcuts *)
  let module LTS = LowTraceSequent in
  let module TS = TraceSequent in

  (* gather containers *)
  let env = TS.env s in
  let system = match SystemExpr.to_fset env.system.set with 
    | exception SystemExpr.(Error (_,Expected_fset)) -> Tactics.(hard_failure (Failure "I was told to error out in this case"))
    | fsys -> fsys 
  in 
  let table = env.table in

  (* then we build the cv_context *)
  let query = LTS.conclusion s in
  let hypotheses = List.filter_map (* ty Stan *)
      (function 
        |_,Hyps.LHyp (Equiv.Local h) -> Some h
        | _, Hyps.LHyp (Equiv.(Global Atom (Reach f))) -> Some f
        | _ -> None(*TODO*))
    (LTS.Hyps.to_list s) in
  let variables = Vars.to_vars_list env.vars in
  let actions = get_actions_descr_list table system in
  let names = MNameExtra.get_content_list table in
  let operators = MOperatorExtra.get_content_list table in
  let macros = MMacroExtra.get_content_list table in
  {query;hypotheses; variables; actions; names; operators; macros}

(** paramerters to be passed on to cv *)
type cv_parameters = {
  num_retry : int; (** number of retries*)
  timeout: int (** timeout for each solvers*)
}
[@@deriving yojson_of]
let yojson_of_cv_parameters x = Json.to_assoc (yojson_of_cv_parameters x)

let default_parameters = {
  num_retry = 5;
  timeout = 1;
}

type to_cv = {
  parameters: cv_parameters;
  context: cv_context
}
[@@deriving yojson_of]
let yojson_of_to_cv x = Json.to_assoc (yojson_of_to_cv x)


let run_cryptovampire (parameters: cv_parameters) (s: LowTraceSequent.t)  =
    let context = make_cv_context s in
    let json = yojson_of_to_cv {context; parameters} in

    (* print to file *)
    let file = "/tmp/sq.json" in
    let oc = open_out_gen [Open_creat] 0o644 file in 
    let ppf = Format.formatter_of_out_channel oc in 
    begin
      Format.fprintf ppf "%s@." (Safe.pretty_to_string json);
      Format.printf "outputed to %s@\n" file;

      (* give up for now *)
      Error "running CryptoVampire is not implemented yet"
    end

module L = Location
module TA = TacticsArgs
(** parse the arguments for the `cryptovampire` tactic *)
let parse_args =
  let aux acc = function 
  (* ~nt=[x] for num of retry *)
  | TA.NList ({L.pl_desc="nt"}, [{L.pl_desc=nt}]) -> (
    match int_of_string_opt nt with
    | Some(nt) -> {acc with num_retry=nt}
    | None -> Tactics.(hard_failure (Failure (Printf.sprintf "%s in not a number" nt))))
  (* ~t=[x] for timeout *)
  | TA.NList ({L.pl_desc="t"}, [{L.pl_desc=nt}]) -> (
    match int_of_string_opt nt with
    | Some(nt) -> {acc with timeout=nt}
    | None -> Tactics.(hard_failure (Failure (Printf.sprintf "%s in not a number" nt))))
  
  | _ -> Tactics.(hard_failure (Failure "unrecognized argument"))
  in List.fold_left aux default_parameters

(* register the tactic *)
let () =
  ProverTactics.register_general "cryptovampire" 
    ~pq_sound:false
    (* ^^^^^^^^^^^^ don't know if cv is post-quantum safe, so I'll assume it's not *)
    (fun args s sk fk -> 
      
      let args = match args with
         | [Named_args args] -> args
         | [] -> []
         | _ -> assert false
      in let s = match s with
         | Goal.Global _ -> Tactics.(hard_failure (Failure "CryptoVampire doesn't support global goals"))
         | Goal.Local s -> s
      in let parameters = parse_args args
    in match run_cryptovampire parameters s with
    | Ok () -> sk [] fk
    | Error e -> fk (None, Tactics.Failure e)
      )