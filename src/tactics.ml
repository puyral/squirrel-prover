type tac_error =
  | More
  | Failure of string
  | AndThen_Failure of tac_error
  | CannotConvert
  | NotEqualArguments
  | Bad_SSC
  | NoSSC
  | NoAssumpSystem
  | NotDepends of string * string
  | Undefined of string
  | NotDDHContext
  | SEncNoRandom
  | SEncSharedRandom
  | SEncRandomNotFresh
  | NoRefl
  | NoReflMacros
  | TacTimeout
  | DidNotFail
  | FailWithUnexpected of tac_error
  | SystemError     of System.system_error
  | SystemExprError of SystemExpr.system_expr_err
  | GoalNotClosed

let tac_error_strings =
  [ (More, "More");
   (NotEqualArguments, "NotEqualArguments");
   (Bad_SSC, "BadSSC");
   (NoSSC, "NoSSC");
   (NoAssumpSystem, "NoAssumpSystem");
   (NotDDHContext, "NotDDHContext");
   (SEncNoRandom, "SEncNoRandom");
   (SEncSharedRandom, "SEncSharedRandom");
   (SEncRandomNotFresh, "SEncRandomNotFresh");
   (NoRefl , "NoRefl");
   (NoReflMacros , "NoReflMacros");
   (TacTimeout, "TacTimeout");
   (CannotConvert, "CannotConvert");
   (DidNotFail, "DidNotFail")]

let rec tac_error_to_string = function
  | Failure s -> Format.sprintf "Failure %S" s
  | AndThen_Failure te -> "AndThenFailure, "^(tac_error_to_string te)
  | NotDepends (s1, s2) -> "NotDepends, "^s1^", "^s2
  | Undefined s -> "Undefined, "^s
  | FailWithUnexpected te -> "FailWithUnexpected, "^(tac_error_to_string te)
  | More
  | NotEqualArguments
  | Bad_SSC
  | NoSSC
  | NoAssumpSystem
  | NotDDHContext
  | SEncNoRandom
  | SEncSharedRandom
  | SEncRandomNotFresh
  | NoRefl
  | NoReflMacros
  | TacTimeout
  | CannotConvert
  | DidNotFail as e -> List.assoc e tac_error_strings
  | SystemExprError _ -> "SystemExpr_Error"
  | SystemError _ -> "System_Error"
  | GoalNotClosed -> "GoalNotClosed"

let rec pp_tac_error ppf = function
  | More -> Fmt.string ppf "More results required"
  | Failure s -> Fmt.pf ppf "%s" s
  | AndThen_Failure t ->
      Fmt.pf ppf
        "A sequence of tactic applications eventually failed \
         with the following error: %a"
        pp_tac_error t
  | NotEqualArguments -> Fmt.pf ppf "Arguments not equals"
  | Bad_SSC -> Fmt.pf ppf "Key does not satisfy the syntactic side condition"
  | NoSSC ->
      Fmt.pf ppf
        "No key which satisfies the syntactic condition has been found"
  | Undefined x -> Fmt.pf ppf "Undefined use of %s" x
  | NotDepends (a, b) ->
      Fmt.pf ppf "Action %s does not depend on action %s" a b
  | NoAssumpSystem ->
      Fmt.pf ppf "No assumption with given name for the current system"
  | NotDDHContext ->
      Fmt.pf ppf "The current system cannot be seen as a context \
                  of the given DDH shares"
  | SystemExprError e -> SystemExpr.pp_system_expr_err ppf e
  | SystemError e -> System.pp_system_error ppf e
  | SEncNoRandom ->
    Fmt.string ppf "An encryption is performed without a random name"
  | SEncSharedRandom ->
    Fmt.string ppf "Two encryptions share the same random"
  | SEncRandomNotFresh ->
    Fmt.string ppf "A random used for an encryption is used elsewhere"
  | NoRefl  ->
    Fmt.string ppf "Frames not identical"
  | NoReflMacros ->
    Fmt.string ppf "Frames contain macros that may not be diff-equivalent"
  | TacTimeout -> Fmt.pf ppf "Time-out"
  | DidNotFail -> Fmt.pf ppf "The tactic did not fail"
  | CannotConvert -> Fmt.pf ppf "Conversion error"
  | FailWithUnexpected t -> Fmt.pf ppf "The tactic did not fail with the expected \
                                      exception, but failed with: %s"
                            (tac_error_to_string t)
  | GoalNotClosed -> Fmt.pf ppf "Cannot close goal"


let strings_tac_error =
  let (a,b) = List.split tac_error_strings in
  List.combine b a

let rec tac_error_of_strings = function
  | [] -> raise (Failure "exception name expected")
  | ["Failure"] -> Failure ""
  | [s] ->
    (match List.assoc_opt s strings_tac_error with
      | None -> raise (Failure "exception name unknown")
      | Some e -> e
    )
  | "AndThenFailure"::q -> AndThen_Failure (tac_error_of_strings q)
  | ["NotDepends"; s1; s2] -> NotDepends (s1, s2)
  | ["Undefined"; s] -> Undefined s
  | _ ->  raise (Failure "exception name unknown")


exception Tactic_soft_failure of tac_error

exception Tactic_hard_failure of tac_error

let () =
  Printexc.register_printer
    (function
       | Tactic_hard_failure e ->
           Some
             (Format.sprintf "Tactic_hard_failure(%s)" (tac_error_to_string e))
       | Tactic_soft_failure e ->
           Some
             (Format.sprintf "Tactic_soft_failure(%s)" (tac_error_to_string e))
       | _ -> None)

type a

type fk = tac_error -> a

type 'a sk = 'a -> fk -> a

type 'a tac = 'a -> 'a list sk -> fk -> a

(** Basic Tactics *)

let fail sk fk = fk (Failure "fail")

(** [map t [e1;..;eN]] returns all possible lists [l1@..@lN]
  * where [li] is a result of [t e1]. *)
let map t l sk fk =
  let rec aux acc l fk = match l with
    | [] -> sk (List.rev acc) fk
    | e::l ->
        t e
          (fun r fk ->
             aux (List.rev_append r acc) l fk)
          fk
  in aux [] l fk

let orelse_nojudgment a b sk fk = a sk (fun _ -> b sk fk)

let orelse a b j sk fk = orelse_nojudgment (a j) (b j) sk fk

let orelse_list l j =
  List.fold_right (fun t t' -> orelse_nojudgment (t j) t') l fail

let andthen ?(cut=false) tac1 tac2 judge sk fk : a =
  let sk =
    if cut then
      fun l fk' -> map tac2 l sk fk
    else
      fun l fk' -> map tac2 l sk fk'
  in
  tac1 judge sk fk

let rec andthen_list = function
  | [] -> raise (Tactic_hard_failure (Failure "empty anthen_list"))
  | [t] -> t
  | t::l -> andthen t (andthen_list l)

let by_tac tac judge sk fk =
  let sk l fk = match l with
    | [] -> sk [] fk
    | _ -> raise (Tactic_soft_failure GoalNotClosed) in
  tac judge sk fk

let not_branching tac j sk fk =
  tac j
    (fun l _ -> if List.length l <= 1 then sk l fk else
        fk (Failure "branching tactic under non branching instruction"))
    fk

let id j sk fk = sk [j] fk

let try_tac t j sk fk =
  let succeeded = ref false in
  let sk l fk = succeeded := true ; sk l fk in
  let fk e = if !succeeded then fk e else sk [j] fk in
  t j sk fk

let checkfail_tac exc t j sk fk =
  try
    let sk l fk = raise (Tactic_soft_failure DidNotFail) in
    t j sk fk
  with Tactic_soft_failure e when e = exc -> sk [j] fk
     | Theory.Conv _ when exc=CannotConvert -> sk [j] fk
     | Tactic_soft_failure (Failure _) when exc=Failure "" -> sk [j] fk
     | Tactic_soft_failure e
     | Tactic_hard_failure e ->
       raise (Tactic_hard_failure (FailWithUnexpected e))

let repeat t j sk fk =
  let rec aux j sk fk =
    t j
      (fun l fk -> map aux l sk fk)
      (fun e -> sk [j] fk)
  in aux j sk fk

let eval_all (t : 'a tac) x =
  let l = ref [] in
  let exception End in
  try
    let sk r fk = l := r :: !l ; fk More in
    let fk _ = raise End in
    ignore (t x sk fk) ;
    assert false
  with End -> List.rev !l

let () =
  Checks.add_suite "Tacticals" [
    "OrElse", `Quick, begin fun () ->
      let t1 = fun x sk fk -> sk [x] fk in
      let t2 = fun _ sk fk -> sk [(1,1)] fk in
      assert (eval_all (orelse_list [t1;t2]) (0,0) = [[(0,0)];[(1,1)]]) ;
      assert (eval_all (orelse t2 t1) (0,0) = [[(1,1)];[(0,0)]])
    end ;
    "AndThen", `Quick, begin fun () ->
      let t1 = fun _ sk fk -> sk [(0,0);(0,1)] (fun _ -> sk [(1,0)] fk) in

      let t2 = fun (x,y) sk fk -> sk [(-x,-y);(-2*x,-2*y)] fk in
      let expected = [ [0,0; 0,0; 0,-1; 0,-2]; [-1,0; -2,0] ] in
      assert (eval_all (andthen_list [t1;t2]) (11,12) = expected) ;
      assert (eval_all (andthen t1 t2) (11,12) = expected) ;

      let t3 = fun (x,y) sk fk -> if x+y = 1 then sk [] fk else sk [x,y] fk in
      let expected = [ [0,0] ; [] ] in
      assert (eval_all (andthen_list [t1;t3]) (11,12) = expected) ;
      assert (eval_all (andthen t1 t3) (11,12) = expected) ;

      let t3 = fun (x,y) sk fk -> if x+y = 0 then fk More else sk [y,x] fk in
      let expected = [ [0,1] ] in
      assert (eval_all (andthen_list [t1;t3]) (11,12) = expected) ;
      assert (eval_all (andthen t1 t3) (11,12) = expected) ;
    end ;
    "Try", `Quick, begin fun () ->
      let t = fun _ sk fk -> sk [1] (fun _ -> sk [] fk) in
      assert (eval_all (try_tac (fun _ -> fail)) 0 = [[0]]) ;
      assert (eval_all (try_tac t) 0 = [[1];[]])
    end
  ]

(** Generic tactic syntax trees *)

module type S = sig

  type arg
  val pp_arg : Format.formatter -> arg -> unit

  type judgment

  val eval_abstract : string list -> string -> arg list -> judgment tac
  val pp_abstract : pp_args:(Format.formatter -> arg list -> unit) ->
    string -> arg list -> Format.formatter -> unit

end

(** AST for tactics, with abstract leaves corresponding to prover-specific
  * tactics, with prover-specific arguments. Modifiers have no internal
  * semantics: they are printed, but ignored during evaluation -- they
  * can only be used for cheap tricks now, but may be used to guide tactic
  * evaluation in richer ways in the future. *)
type 'a ast =
  | Abstract of string * 'a list
  | AndThen : 'a ast list -> 'a ast
  | OrElse : 'a ast list -> 'a ast
  | Try : 'a ast -> 'a ast
  | NotBranching : 'a ast -> 'a ast
  | Repeat : 'a ast -> 'a ast
  | Ident : 'a ast
  | Modifier : string * 'a ast -> 'a ast
  | CheckFail : tac_error * 'a ast -> 'a ast
  | By : 'a ast -> 'a ast

module type AST_sig = sig

  type arg
  type judgment
  type t = arg ast

  val eval : string list -> t -> judgment tac

  val eval_judgment : t -> judgment -> judgment list

  val pp : Format.formatter -> t -> unit

end

module AST (M:S) = struct

  open M

  (** AST for tactics, with abstract leaves corresponding to prover-specific
    * tactics, with prover-specific arguments. *)
  type t = arg ast

  type arg = M.arg
  type judgment = M.judgment

  let rec eval modifiers = function
    | Abstract (id,args) -> eval_abstract modifiers id args
    | AndThen tl -> andthen_list (List.map (eval modifiers) tl)
    | OrElse tl -> orelse_list (List.map (eval modifiers) tl)
    | Try t -> try_tac (eval modifiers t)
    | By t -> by_tac (eval modifiers t)
    | NotBranching t -> not_branching (eval modifiers t)
    | Repeat t -> repeat (eval modifiers t)
    | Ident -> id
    | Modifier (id,t) -> eval (id::modifiers) t
    | CheckFail (e,t) -> checkfail_tac e (eval modifiers t)

  let pp_args fmt l =
    Fmt.list
      ~sep:(fun ppf () -> Fmt.pf ppf ",@ ")
      pp_arg fmt l

  let rec pp ppf = function
    | Abstract (i,args) ->
        begin try
          pp_abstract ~pp_args i args ppf
        with _ ->
          if args = [] then Fmt.string ppf i else
            Fmt.pf ppf "@[(%s@ %a)@]" i pp_args args
        end
    | Modifier (i,t) -> Fmt.pf ppf "(%s(%a))" i pp t
    | AndThen ts ->
      Fmt.pf ppf "@[(%a)@]"
        (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ";@,") pp) ts
    | OrElse ts ->
      Fmt.pf ppf "@[(%a)@]"
        (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "+@,") pp) ts
    | By t -> Fmt.pf ppf "@[by %a@]" pp t
    | Ident -> Fmt.pf ppf "id"
    | Try t ->
      Fmt.pf ppf "(try @[%a@])" pp t
    | NotBranching t ->
      Fmt.pf ppf "(nobranch @[%a@])" pp t
    | Repeat t ->
      Fmt.pf ppf "(repeat @[%a@])" pp t
    | CheckFail (e, t) ->
        Fmt.pf ppf "(checkfail %s @[%a@])" (tac_error_to_string e) pp t

  exception Return of M.judgment list

  (** The evaluation of a tactic, may either raise a soft failure or a hard
    * failure (cf tactics.ml). A soft failure should be formatted inside the
    * [Tactic_Soft_Failure] exception.
    * A hard failure inside Tactic_hard_failure. Those exceptions are caught
    * inside the interactive loop. *)
  let eval_judgment ast j =
    let tac = eval [] ast in
    (* The failure should raise the soft failure,
     * according to [pp_tac_error]. *)
    let fk tac_error = raise @@ Tactic_soft_failure tac_error in
    let sk l _ = raise (Return l) in
    try ignore (tac j sk fk) ; assert false with Return l -> l

end


let soft_failure e = raise (Tactic_soft_failure e)
let hard_failure e = raise (Tactic_hard_failure e)

let timeout_get = function
  | Utils.Result a -> a
  | Utils.Timeout -> hard_failure TacTimeout
