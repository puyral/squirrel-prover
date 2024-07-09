open Yojson 
open Term 
open Type

let quant_to_json q =  match q with 
  |ForAll -> `String "ForAll"
  |Exists -> `String "Exists"
  |Seq -> `String "Seq"
  |Lambda -> `String "Lambda"

let rec term_to_json t = match t with 
  |App (f,tl) -> 
    `Assoc ["Constructor", `String "App";
      "Fsymb", term_to_json f;
      "Arguments", `List (List.map term_to_json tl)]
  |Fun (f,_) -> 
    `Assoc ["Constructor", `String "Fun";
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
      "Quantficator", quant_to_json q;
      "Vars", `List (List.map (fun v -> (term_to_json (mk_var v))) vl);
      "Term", term_to_json t1]

let rec type_to_json ty = match ty with 
    |Message -> `Assoc ["Constructor", `String "Message"]
    |Boolean -> `Assoc ["Constructor", `String "Boolean"]
    |Index -> `Assoc ["Constructor", `String "Index"]
    |Timestamp -> `Assoc ["Constructor", `String "Timestamp"]
    |TBase s -> `Assoc ["Constructor", `String "TBase"; "String", `String s]
    |TVar tv -> 
      `Assoc ["Constructor", `String "TVar";
        "Id", `Int (Ident.tag (ident_of_tvar tv));
        "Name", `String (Ident.name (ident_of_tvar tv))]
    |TUnivar tu -> ignore tu;
      `Assoc ["Constructor", `String "TUnivar";
        "Id", `String "TODO";
        "Name", `String "TODO"]
    |Tuple tl ->
      `Assoc ["Constructor", `String "Tuple";
        "Elements",`List (List.map type_to_json tl)]
    |Fun (t1,t2) ->
      `Assoc ["Constructor", `String "Fun";
        "Type1", type_to_json t1;
        "Type2", type_to_json t2]

let var_to_json v = 
  `Assoc ["Id", `Int (Vars.hash v);
  "Name", `String (Vars.name v);
  "Type", type_to_json (Vars.ty v)]

let operator_to_json (ftype,str,abs_def) = 
    `Assoc ["Name", `String str; 
    "Type_Args", `List (List.map type_to_json (ftype.fty_args));
    "Type_Out", type_to_json (ftype.fty_out);
    "Crypto_fun", `String (match abs_def with 
    |None -> "None"
    |Some d -> Format.asprintf "%a" Symbols.OpData.pp_abstract_def d)]

let macro_to_json (str,indices,ty) = 
  `Assoc ["Name", `String str; 
  "Index_arity", `Int indices;
  "Type_Out", type_to_json ty]


let abs_symb f table = 
  if Symbols.OpData.is_abstract f table then 
    let def,_ = Symbols.OpData.get_abstract_data f table in 
    Some def
  else
    None

let cryptovampire_export (s:TraceSequent.t) = 
  let env = TraceSequent.env s in 
  let evars = Vars.to_vars_list env.vars 
  and table = env.table in 
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
  Format.printf "%s@." (Basic.pretty_to_string j_export) ;







