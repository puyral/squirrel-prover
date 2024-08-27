open Utils
open Ppx_yojson_conv_lib.Yojson_conv.Primitives
open Term
open Type
module SE = SystemExpr
module S = Symbols

type descr = Action.descr
type json = Yojson.Safe.t

(** quick accest to the main compenent required for the export *)
type query_context = {
  system : SystemExpr.fset;
  table : S.table;
  sequent : LowTraceSequent.t;
  variables : Vars.var list;
}

(** get a `query_context`*)
let make_query_context (sequent : LowTraceSequent.t) : query_context =
  let module LTS = LowTraceSequent in
  let module TS = TraceSequent in
  let env = TS.env sequent in
  let system =
    match SystemExpr.to_fset env.system.set with
    | exception SystemExpr.(Error (_, Expected_fset)) ->
        Tactics.(hard_failure (Failure "I was told to error out in this case"))
    | fsys -> fsys
  in
  let table = env.table in
  let variables = Vars.to_vars_list env.vars in
  { sequent; table; system; variables }

(* ------------------------------------------------------------------------- *)
(** {2 Shortcuts}
  A bunch of syntactic sugar for the rest of the file *)

(** haskel-style `fmap` *)
let ( <$> ) = List.map

(** syntactic sugar to be able to write something like `("a", t) <<@>> ("b", t')` *)
let ( <<@>> ) (e : string * json) (e' : string * json) = `Assoc [ e; e' ]

(** base case for a chain of `<<@>>`. This is useful for enum discriminants *)
let ( <<@ ) (e : string) (d : json) = `Assoc [ (e, d) ]

(** {2 Terms}
  export terms to json.

  Doing this so late in the program prevents us from enjoying most of Yojson's
  power, but it was the least intrusive thing I could think of *)

let rec yojson_of_term : Term.term -> json = function
  | App (f, tl) ->
      "App" <<@ `Assoc
        [
          ("f", yojson_of_term f);
          ("args", `List (List.map yojson_of_term tl));
        ]
  | Fun (f, _) ->
      "Fun" <<@ `Assoc [ ("symb", S.yojson_of_path f) ]
  | Name (n, tl) ->
      "Name" <<@ `Assoc
        [
          ("symb", yojson_of_nsymb n);
          ("args", `List (List.map yojson_of_term tl));
        ]
  | Macro (m, tl, ts) ->
      "Macro" <<@ `Assoc
        [
          ("symb", yojson_of_msymb m);
          ("args", `List (List.map yojson_of_term tl));
          ("timestamp", yojson_of_term ts);
        ]
  | Action (a, tl) ->
      "Action" <<@ `Assoc
        [
          ("symb", S.yojson_of_path a);
          ("args", `List (List.map yojson_of_term tl));
        ]
  | Var v -> "Var" <<@ Vars.yojson_of_var v
  | Let (v, t1, t2) ->
      "Let" <<@ `Assoc
        [
          ("var", yojson_of_term (mk_var v));
          ("decl", yojson_of_term t1);
          ("body", yojson_of_term t2);
        ]
  | Tuple tl ->
      "Tuple" <<@ `Assoc
        [
          ("elements", `List (List.map yojson_of_term tl));
        ]
  | Proj (i, t1) ->
      "Proj" <<@ `Assoc
        [
          ("id", `Int i);
          ("body", yojson_of_term t1);
        ]
  | Diff (Explicit td) ->
      ignore td;
      "Diff" <<@ `Assoc
        [
          ( "terms",
            `List
              (List.map
                 (fun (p, t') ->
                   `Assoc
                     [
                       ("proj", `String (proj_to_string p));
                       ("term", yojson_of_term t');
                     ])
                 td) );
        ]
  | Find (vl, t1, t2, t3) ->
      "Find" <<@ `Assoc
        [
          ("constructor", `String "Find");
          ("vars", `List (List.map (fun v -> yojson_of_term (mk_var v)) vl));
          ("condition", yojson_of_term t1);
          ("success", yojson_of_term t2);
          ("faillure", yojson_of_term t3);
        ]
  | Quant (q, vl, t1) ->
      ignore q;
      "Quant" <<@`Assoc
        [
          ("quantificator", Term.yojson_of_quant q);
          ("vars", `List (List.map (fun v -> yojson_of_term (mk_var v)) vl));
          ("body", yojson_of_term t1);
        ]

(** gets the list of action `descr` of a given system

  (for me a system is a `fset`, but I don't fully understand how this type
  works)
*)
let get_actions_descr_list (table : S.table) (system : SE.fset) :
    Action.descr list =
  SystemExpr.map_descrs (fun x -> x) table system

(** {1 Automation }

    I use module black magic to stremline building json objects for things of
    the form (symb, data).system

    In the end each "type" defines it `mdata` type and how to turn it into json,
    the system deals with the rest such that it gets neatly past of to yojosn
    afterwards.
*)

module type MSymbol = sig
  include S.SymbolKind

  (** the "data" associated to this type *)
  type mdata [@@deriving yojson_of]

  (** how to get the data associated to the type.

      Since we are querying into squirrel main table, we get a gigantic enum
      where we are fairly sure of the variant we got, this function aims to
      extract the data hidden in that varian. Possibly, that data may be expanded
      using the context is relevant.
    *)
  val mdata_of_data : query_context -> S.data -> mdata option

  (** because we need names for everything ! *)
  val name : string
end

(** we autobuild a new module with convenience functions and a way to plug into
    the ysojson functions
*)
module MExtra (N : MSymbol) = struct
  let yojson_of_path : N.ns S.path -> json = S.yojson_of_path

  (** the (symb, data) datatype *)
  type content = { symb : N.ns S.path; data : N.mdata }

  let yojson_of_content ({ symb; data } : content) =
    `Assoc [ ("symb", yojson_of_path symb); ("data", N.yojson_of_mdata data) ]

  (** sucks the table out of its data *)
  let get_content_list (ctx : query_context) (table : S.table) : content list =
    N.fold
      (fun symb data acc ->
        { symb; data = Option.get (N.mdata_of_data ctx data) } :: acc)
      [] table
end

(** {2 Data types}

  implenting the modules defined above
*)

module MType : MSymbol = struct
  include S.BType

  type mdata = S.TyInfo.t list [@@deriving yojson_of]

  let mdata_of_data _ = function S.TyInfo.Type l -> Some l | _ -> None
  let name = "Type"
end

module MTypeExtra = MExtra (MType)

module MOperator : MSymbol = struct
  include S.Operator

  type mdata = S.OpData.op_data

  let mdata_of_data _ = function
    | S.OpData.Operator data -> Some data
    | _ -> None

  let name = "Operator"

  let yojson_of_mdata ({ ftype; def } : mdata) =
    let json_of_concrete
        ({ name; ty_vars; args; out_ty; body } : Operator.concrete_operator) :
        json =
      `Assoc
        [
          ("name", S.yojson_of_path name);
          ("type_variables", `List (yojson_of_tvar <$> ty_vars));
          ("args", `List (Vars.yojson_of_var <$> args));
          ("out_type", yojson_of_ty out_ty);
          ("body", yojson_of_term body);
        ]
    in
    (* sligh evil choice here: there is no discriminant between the to enum variant
       instead their data format distinguish them from one another *)
    let json_of_def = function
      | S.OpData.Abstract (adef, afun) ->
          `Assoc
            [
              ("abstract_def", S.OpData.yojson_of_abstract_def adef);
              ("associated_fun", `List (S.yojson_of_path <$> afun));
            ]
      | S.OpData.Concrete (Operator.Val c) -> json_of_concrete c
      | _ -> assert false
    in
    `Assoc [ ("type", Type.yojson_of_ftype ftype); ("def", json_of_def def) ]
end

module MOperatorExtra = MExtra (MOperator)

module MName : MSymbol = struct
  include S.Name

  type mdata = S.name_data

  let mdata_of_data _ = function S.Name data -> Some data | _ -> None
  let name = "Name"
  let yojson_of_mdata ({ n_fty } : mdata) = Type.yojson_of_ftype n_fty
end

module MNameExtra = MExtra (MName)

module MMacro : MSymbol = struct
  include S.Macro

  type mdata = { ctx : query_context; data : S.macro_data }

  let mdata_of_data ctx = function
    | S.Macro data -> Some { ctx; data }
    | _ -> None

  let yojson_of_mdata { ctx; data } =
    (* Macros are a bit of a mess given how many different thing they can
       reprensent, hence the size of the function. Nothing is worth noting
       in the design. I couldn't use the yojson auto deriving procedure
       because some type didn't feature their translation to json (mainly
       the `Term` type) *)
    let yojson_of_global_data
        ({ action; inputs; indices; ts; bodies = _; ty } as global_data :
          Macros.global_data) =
      let action =
        let kind, shape = action in
        let kind =
          `String (match kind with `Large -> "Large" | `Strict -> "Strict")
        in
        let shape = Action.yojson_of_shape shape in
        `Assoc [ ("kind", kind); ("shape", shape) ]
      in
      let inputs = `List (Vars.yojson_of_var <$> inputs) in
      let indices = `List (Vars.yojson_of_var <$> indices) in
      let ts = Vars.yojson_of_var ts in
      let ty = Type.yojson_of_ty ty in
      let body = Macros.get_body ctx.table ctx.system global_data in
      `Assoc
        [
          ("action", action);
          ("inputs", inputs);
          ("indices", indices);
          ("ts", ts);
          ("ty", ty);
          ("body", yojson_of_term body);
        ]
    in
    let yojson_of_structed_macro_data
        ({ name; default; tinit; body = var, body; rec_ty; ty } :
          Macros.structed_macro_data) : json =
      let name = S.yojson_of_path name in
      let default = yojson_of_term default in
      let tinit = yojson_of_term tinit in
      let body =
        `Assoc
          [ ("var", Vars.yojson_of_var var); ("body", yojson_of_term body) ]
      in
      let rec_ty = Type.yojson_of_ty rec_ty in
      let ty = Type.yojson_of_ty ty in
      `Assoc
        [
          ("name", name);
          ("default", default);
          ("tinit", tinit);
          ("body", body);
          ("rec_ty", rec_ty);
          ("ty", ty);
        ]
    in
    let yojson_of_general_macro_data = function
      (* untagged enum: i.e., no disciminant between variants *)
      | Macros.ProtocolMacro `Output -> `String "Output"
      | Macros.ProtocolMacro `Cond -> `String "Cond"
      | Macros.Structured s -> yojson_of_structed_macro_data s
    in
    let yojson_of_state_macro_def = function
      | Macros.StateInit_data (vars, term) ->
          `Assoc
            [
              ("vars", yojson_of_list Vars.yojson_of_var vars);
              ("init", yojson_of_term term);
            ]
      | _ -> assert false
    in
    (* tagged enum *)
    match data with
    | S.General (Macros.Macro_data gmd) ->
        "General" <<@ yojson_of_general_macro_data gmd
    | S.State (arity, ty, smd) ->
        "State"
        <<@ `Assoc
              [
                ("arity", yojson_of_int arity);
                ("type", yojson_of_ty ty);
                ("init", yojson_of_state_macro_def smd);
              ]
    | S.Global (arity, ty, Macros.Global_data global) ->
        "Global"
        <<@ `Assoc
              [
                ("arity", yojson_of_int arity);
                ("type", yojson_of_ty ty);
                ("data", yojson_of_global_data global);
              ]
    | _ -> assert false

  let name = "Macro"
end

module MMacroExtra = MExtra (MMacro)

module MAction : MSymbol = struct
  include S.Action

  type mdata = Vars.var list * Action.action_v

  let mdata_of_data _ = function
    | Action.ActionData (Action.Def (vars, a)) ->
        Some (vars, Action.to_action_v a)
    | _ -> None

  let yojson_of_mdata _ = `Assoc []
  let name = "Action"
end

let yojson_of_descr : descr -> json =
  let yojson_of_lvars v : json = `List (Vars.yojson_of_var <$> v) in
  let yojson_of_updates lu : json =
    let aux (symb, args, body) =
      `Assoc
        [
          ("symb", S.yojson_of_path symb);
          ("args", `List (yojson_of_term <$> args));
          ("body", yojson_of_term body);
        ]
    in
    `List (aux <$> lu)
  in
  let open Action in
  function
  | {
      name;
      action;
      input;
      indices;
      condition = cvars, cond;
      updates = lu;
      output = c, msg;
      globals;
    } ->
      `Assoc
        [
          ("name", S.yojson_of_path name);
          ("action", Action.yojson_of_action_v action);
          ("input", S.yojson_of_path input);
          ("indices", yojson_of_lvars indices);
          ( "condition",
            ("vars", yojson_of_lvars cvars) <<@>> ("term", yojson_of_term cond)
          );
          ("updates", yojson_of_updates lu);
          ( "output",
            ("channel", S.yojson_of_path c) <<@>> ("term", yojson_of_term msg)
          );
          ("globals", `List (S.yojson_of_path <$> globals));
        ]

(** {1 Final export} *)

(** This is the record as it is finally exported to json *)
type sequent_context = {
  query : term;
  hypotheses : term list;
  variables : Vars.var list;
  actions : descr list;
  names : MNameExtra.content list;
  operators : MOperatorExtra.content list;
  macros : MMacroExtra.content list;
  types : MTypeExtra.content list;
}
[@@deriving yojson_of]

let yojson_of_sequent_context x = Json.to_assoc (yojson_of_sequent_context x)

(** main logic *)
let make_sequent_context (ctx : query_context) : sequent_context =
  let { sequent = s; system; table; variables } = ctx in
  (* shortcuts *)
  let module LTS = LowTraceSequent in
  (* gather containers *)
  let query = LTS.conclusion s in
  let hypotheses =
    List.filter_map (* ty Stan *)
      (function
        | _, Hyps.LHyp (Equiv.Local h) -> Some h
        | _, Hyps.LHyp Equiv.(Global (Atom (Reach f))) -> Some f
        | _ -> None (*TODO*))
      (LTS.Hyps.to_list s)
  in
  let actions = get_actions_descr_list table system in
  let names = MNameExtra.get_content_list ctx table in
  let operators = MOperatorExtra.get_content_list ctx table in
  let macros = MMacroExtra.get_content_list ctx table in
  let types = MTypeExtra.get_content_list ctx table in
  (* and we get our context ! *)
  { query; hypotheses; variables; actions; names; operators; macros; types }

(** see `make_sequent_context` *)
let json_of_low_trace_sequent s =
  yojson_of_sequent_context (make_sequent_context (make_query_context s))
