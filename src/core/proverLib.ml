type pending_proof = 
  | ProofObl of Goal.t          
  (** proof obligation *)
  | UnprovedLemma of Goal.statement * Goal.t
  (** lemma remaining to be proved *)

type prover_mode = GoalMode | ProofMode | WaitQed | AllDone

(** {2 User printing query} *)
(** User printing query *)
type print_query = (* [None] means current system *)
  | Pr_system    of SystemExpr.Parse.t option 
  | Pr_any of Theory.lsymb (* print any lemma, function, name or macro
                              with given lsymb *)


(** {2 User search query} *)
type search_query = (* [None] means current system *)
  | Srch_term    of Theory.any_term
  | Srch_inSys   of Theory.any_term * SystemExpr.Parse.t 

(*---------------- Errors in proverlib -----------------------*)(* {↓{ *)
(** TOMOVE Error handling in prover *)
type error = Location.t * string

exception Error of error

let error loc s = raise (Error (loc, s))

let pp_error pp_loc_err fmt (loc,s) =
  Fmt.pf fmt "%aError: %s"
    pp_loc_err loc
    s
(* }↑} *)

(* XXX This cpt has side effects : maybe keep it in the state ? 
 * Same name goal generates error ! *)
let unnamed_goal =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    Location.mk_loc Location._dummy ("unnamedgoal" ^ string_of_int !cpt)

(*------------------------------------------------------------------*)
(** {2 Utilities for parsing} *)

type lpath = 
  | Name of string Location.located
  | Path of string Location.located

let get_pathlsymb = function
  | Name s
  | Path s -> s

type include_param = { th_name : lpath; 
                       params : Theory.lsymb list }


type bulleted_tactic =
  | Bullet of string
  | Brace of [`Open | `Close]
  | BTactic of ProverTactics.AST.t

type bulleted_tactics = bulleted_tactic list

(* This should move somewhere else *)
type toplevel_input =
  | Undo    of int

type prover_input = 
  | InputDescr of Decl.declarations
  | SetOption  of Config.p_set_param
  | Tactic of bulleted_tactics
  | Print   of print_query
  | Search of search_query
  | Reset
  | Goal    of Goal.Parsed.t Location.located
  | Proof
  | Qed
  | Abort
  | Hint of Hint.p_hint
  | EOF
  | Include of include_param
  | Help of TacticsArgs.parser_args 

type input =
  | Prover of prover_input
  | Toplvl of toplevel_input

let get_prover_command = function
  | Prover c -> c
  | _ -> assert false
