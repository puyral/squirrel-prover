open Yojson 
open Ppx_yojson_conv_lib.Yojson_conv.Primitives
open Term 
open Type
module SE = SystemExpr
module S = Symbols

let (<$>) = List.map


  let (<@>) (`Assoc l) (`Assoc l') =  `Assoc (l @ l')

let (<<@>) (e: string * Yojson.Safe.t) (`Assoc l) = `Assoc (e::l)
let (<@>>) (`Assoc l) (e: string * Yojson.Safe.t) = `Assoc (e::l)
let (<<@>>) (e: string * Yojson.Safe.t) (e': string * Yojson.Safe.t) = `Assoc ([e; e'])

(* Let's go with PascalCase everywhere if possible *)

let rec term_to_json t = match t with 
  |App (f,tl) -> 
    `Assoc ["constructor", `String "App";
      "f", term_to_json f;
      "args", `List (List.map term_to_json tl)]
  |Fun (f,_) -> 
    `Assoc ["constructor", `String "Fun";
      "Fname", `String (Symbols.to_string f)]
  |Name (n,tl) -> 
    `Assoc ["Constructor", `String "Name";
      "Nsymb", `String (Symbols.to_string n.s_symb);
      "Arguments", `List (List.map term_to_json tl)]
  |Macro (m,tl,ts) -> 
    `Assoc ["Constructor", `String "Macro";
      "Msymb", `String (Symbols.to_string m.s_symb);
      "Arguments", `List (List.map term_to_json tl);
      "Timestamp", term_to_json ts]
  |Action (a,tl) -> 
    `Assoc ["Constructor", `String "Action";
      "Asymb", `String (Symbols.to_string a);
      "Arguments", `List (List.map term_to_json tl)]
  |Var (v) -> 
    `Assoc ["Constructor", `String "Var" ;
      "Id", `Int (Vars.hash v);
      "Name", `String (Vars.name v) ]
  |Let (v,t1,t2) -> 
    `Assoc ["Constructor", `String "Let" ;
      "Var", term_to_json (mk_var v);
      "Term1", term_to_json t1;
      "Term2", term_to_json t2 ]
  |Tuple (tl) -> 
    `Assoc ["Constructor", `String "Tuple";
      "Elements",`List (List.map term_to_json tl)]
  |Proj (i,t1) -> 
    `Assoc ["Constructor", `String "Proj" ;
      "Id", `Int i;
      "Term", term_to_json t1]
  |Diff (Explicit td) -> ignore td;
    `Assoc ["Constructor", `String "Diff" ;
      "Terms", `List (List.map (fun (p,t') ->
         `Assoc ["Proj", `String (proj_to_string p); "Term", term_to_json t'])
        td) ]
  |Find (vl,t1,t2,t3) ->
      `Assoc ["Constructor", `String "Find";
        "Vars", `List (List.map (fun v -> (term_to_json (mk_var v))) vl);
        "Term1", term_to_json t1;
        "Term2", term_to_json t2;
        "Term3", term_to_json t3]
  |Quant (q,vl,t1) -> ignore q;
    `Assoc ["Constructor", `String "Quant";
      "Quantficator", Term.yojson_of_quant q;
      "Vars", `List (List.map (fun v -> (term_to_json (mk_var v))) vl);
      "Term", term_to_json t1]

(* let operator_to_json (ftype,str,abs_dt) = 
  let base = 
    ["Name", `String str; 
    "TypeArgs", `List (List.map type_to_json (ftype.fty_args));
    "TypeOut", type_to_json (ftype.fty_out)]
  in match abs_dt with
    | Some (`Assoc abs_dt) ->
          `Assoc (base @ abs_dt)
    | None -> `Assoc base *)

(* let macro_to_json (str,indices,ty) = 
  `Assoc ["Name", `String str; 
  "IndexArity", `Int indices;
  "TypeOut", type_to_json ty] *)


let abs_symb f table = 
  if Symbols.OpData.is_abstract f table then 
    let def,assoc_fun = Symbols.OpData.get_abstract_data f table in 
    let ls = List.map 
      (fun f -> let f_def,_ = Symbols.OpData.get_abstract_data f table in 
        `Assoc ["Name", `String (Symbols.to_string f);
        "Def", `String (Format.asprintf "%a" Symbols.OpData.pp_abstract_def f_def)]) 
    assoc_fun in 
    Some (`Assoc ["Def",`String (Format.asprintf "%a" Symbols.OpData.pp_abstract_def def); "AssocFun", `List ls])
  else
    None

let cryptovampire_export (s:TraceSequent.t) = 
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
  let j_export = `Assoc ["Conclusion", term_to_json conclusion;
  "Hypotheses", `List (List.map term_to_json hypotheses);
  "Variables", `List (List.map var_to_json evars);
  "Functions", `List (List.map operator_to_json fun_table);
  "Names", `List (List.map operator_to_json name_table);
  "Macros", `List (List.map macro_to_json macro_table)] in 
  (* Format.printf "%s@." (Basic.pretty_to_string j_export) ; *)

  let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sq.json" in 
  let ppf = Format.formatter_of_out_channel oc in 
  Format.fprintf ppf "%s@." (Safe.to_string j_export) 


module type MSymbol = sig
include S.SymbolKind
  type mdata
[@@deriving yojson_of]
  val mdata_of_data : S.data -> mdata option

  val name: string
end

module GetSymbolList (N : MSymbol) = struct
  let get_data_symbol_list (table: S.table) : (N.ns S.t * N.mdata) list =
    N.fold (fun symb data acc -> (symb, Option.get (N.mdata_of_data data))::acc) [] table

  let get_symbol_list (table: S.table) : N.ns S.t list =
    List.map fst (get_data_symbol_list table)
  
    let json_of_symb x = `String (S.to_string x)
  
  let json_of  (symb: N.ns S.t)  (data: N.mdata) =
  ("symb", json_of_symb symb) <<@>> ("data", N.yojson_of_mdata data)
  
  let yojson_of_table (table: S.table)  =
    `Assoc [N.name, `List (List.map (fun (n, d) -> json_of n d) (get_data_symbol_list table))]
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
      `Assoc []
    in
    let json_of_def = function
      | S.OpData.Abstract (adef, afun) -> ("abstract_def", S.OpData.yojson_of_abstract_def adef) <<@>> 
      ("associated_fun", `List  ((fun s -> `String (S.to_string s)) <$>  afun))
      | S.OpData.Concrete (Operator.Val c) -> json_of_concrete c
      | _ -> assert false
  in ("type", Type.yojson_of_ftype ftype) <<@>> ("def", json_of_def def)

end


module MName : MSymbol = struct
  include S.Name
  type mdata = S.name_data
  let mdata_of_data = function
    | S.Name data -> Some data
    | _ -> None
    let name = "Name"

  let yojson_of_mdata ({n_fty}:mdata) = Type.yojson_of_ftype n_fty
end

module MMacro : MSymbol = struct
  include S.Macro
  type mdata =  S.macro_data
  let mdata_of_data = function
  | S.Macro d -> Some d
  | _ -> None

    (* TODO *)
  let yojson_of_mdata d = `Assoc []

  let name = "Macro"
end

module MAction: MSymbol = struct 
  include S.Action
  type mdata = Action.data
  let mdata_of_data = function
  | Action.ActionData a -> Some a
  | _ -> None

  let yojson_of_mdata d = `Assoc []
  let name = "Action"
end


(** Context surounding cv, this gather all the sq info that needs to be sent *)
type cv_context = {
  hypotheses : term list; (** list of hypothesis *)
  query: term; (** the query to be proven*)
  variables: Vars.var list; (** list of free variables in `hypotheses` and `query`*)
  actions: MAction.mdata list;
  (* table: S.table; * the symbol table *)
  (* types: Sy *)
}


(** paramerters to be passed on to cv *)
type cv_parameters = {
  num_retry : int; (** number of retries*)
  timeout: int (** timeout for each solvers*)
}
[@@deriving yojson_of]

let default_parameters = {
  num_retry = 5;
  timeout = 1;
}

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
(* let () =
  ProverTactics.register_general "cryptovampire" 
    ~pq_sound:false
    (* ^^^^^^^^^^^^ don't know if cv is post-quantum safe, so I'll assume it's not *)
    (fun args s sk fk -> 
      
      let args = match args with
         | [Named_args args] -> args
         | _ -> assert false
      in let s = match s with
         | Goal.Global _ -> Tactics.(hard_failure (Failure "CryptoVampire doesn't support global goals"))
         | Goal.Local s -> s
      in let parameters = parse_args args
    in match is_sequent_valid s with
    | Ok () -> sk [] fk
    | Error e -> fk (None, Tactics.Failure e)
      ) *)