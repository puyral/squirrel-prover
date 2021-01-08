open Utils

(** Type of symbols *)
type 'a t = string

type kind = Sorts.esort

type function_def =
  | Hash
  | AEnc
  | ADec
  | SEnc
  | SDec
  | Sign
  | CheckSign
  | PublicKey
  | Abstract of int

type macro_def =
  | Input | Output | Cond | Exec | Frame
  | State of int * kind
  | Global of int
  | Local of kind list * kind

type channel
type name
type action
type fname
type macro

type _ def =
  | Channel : unit -> channel def
  | Name : int -> name def
  | Action : int -> action def
  | Function : (int * function_def) -> fname def
  | Macro : macro_def -> macro def

type edef =
  | Exists : 'a def -> edef
  | Reserved

type data = ..
type data += Empty
type data += AssociatedFunctions of (fname t) list

let to_string s = s

type table = (edef * data) Ms.t

let dummy_table = assert false

let empty_table = Ms.empty

(* TODO: remove the ref *)
let builtins_table = ref empty_table

let prefix_count_regexp = Pcre.regexp "([^0-9]*)([0-9]*)"

(* TODO: remove the builtin option *)
let table_add ?(builtin=false) table name d =
  if builtin then builtins_table := Ms.add name d !builtins_table;
  Ms.add name d table

let restore_builtin () = !builtins_table

let fresh prefix table =
  let substrings = Pcre.exec ~rex:prefix_count_regexp prefix in
  let prefix = Pcre.get_substring substrings 1 in
  let i0 = Pcre.get_substring substrings 2 in
  let i0 = if i0 = "" then 0 else int_of_string i0 in
  let rec find i =
    let s = if i=0 then prefix else prefix ^ string_of_int i in
    if Ms.mem s table then find (i+1) else s
  in
  find i0

exception Unbound_identifier of string
exception Incorrect_namespace
exception Multiple_declarations of string

let def_of_string s table =
  try fst (Ms.find s table) with Not_found -> raise @@ Unbound_identifier s

type wrapped = Wrapped : 'a t * 'a def -> wrapped

let of_string s table =
  try match Ms.find s table with
    | Exists d, _ -> Wrapped (s,d)
    | Reserved, _ -> raise @@ Unbound_identifier s
  with Not_found -> raise @@ Unbound_identifier s

module type Namespace = sig
  type ns
  type def
  val reserve : table -> string -> table * data t
  val define : table -> data t -> ?data:data -> def -> table
  val redefine : table -> data t -> ?data:data -> def -> table
  val declare :
    table -> string -> ?builtin:bool -> ?data:data -> def -> table * ns t
  val declare_exact :
    table -> string -> ?builtin:bool -> ?data:data -> def -> table * ns t
  val of_string : string -> table -> ns t
  val cast_of_string : string -> ns t

  val get_all        : ns t   -> table -> def * data
  val get_def        : ns t   -> table -> def
  val def_of_string  : string -> table -> def
  val get_data       : ns t   -> table -> data
  val data_of_string : string -> table -> data

  val iter : (ns t -> def -> data -> unit) -> table -> unit
  val fold : (ns t -> def -> data -> 'a -> 'a) -> 'a -> table -> 'a
end

module type S = sig
  type ns
  type local_def
  val construct : local_def -> ns def
  val deconstruct : edef -> local_def
end

module Make (N:S) : Namespace 
  with type ns = N.ns with type def = N.local_def = struct

  type ns = N.ns
  type def = N.local_def

  let reserve table name =
    let symb = fresh name table in 
    let table = Ms.add symb (Reserved,Empty) table in
    table,symb

  let define table symb ?(data=Empty) value =
    assert (fst (Ms.find symb table) = Reserved) ;
    Ms.add symb (Exists (N.construct value), data) table

  let redefine table symb ?(data=Empty) value =
    assert (Ms.mem symb table) ;
    Ms.add symb (Exists (N.construct value), data) table

  let declare table name ?(builtin=false) ?(data=Empty) value =
    let symb = fresh name table in
    let table = 
      table_add ~builtin table symb (Exists (N.construct value), data) 
    in
    table, symb

  let declare_exact table name ?(builtin=false) ?(data=Empty) value =
    if Ms.mem name table then raise @@ Multiple_declarations name;
    let table = 
      table_add ~builtin table name (Exists (N.construct value), data) 
    in
    table, name

  let get_all (name:ns t) table =
    (* We know that [name] is bound in [table]. *)
    let def,data = Ms.find name table in
    N.deconstruct def, data

  let get_def name table = fst (get_all name table)
  let get_data name table = snd (get_all name table)

  let cast_of_string name =
    name

  let of_string name table =
    try
      ignore (N.deconstruct (fst (Ms.find name table))) ;
      name
    with Not_found -> raise @@ Unbound_identifier name

  let def_of_string s table =
    try
      N.deconstruct (fst (Ms.find s table))
    with Not_found -> raise @@ Unbound_identifier s

  let data_of_string s table =
    try
      let def,data = Ms.find s table in
        (* Check that we are in the current namespace
         * before returning the associated data. *)
        ignore (N.deconstruct def) ;
        data
    with Not_found -> raise @@ Unbound_identifier s

  let iter f table =
    Ms.iter
      (fun s (def,data) ->
         try f s (N.deconstruct def) data with
           | Incorrect_namespace -> ())
      table

  let fold f acc table =
    Ms.fold
      (fun s (def,data) acc ->
         try
           let def = N.deconstruct def in
           f s def data acc
         with Incorrect_namespace -> acc)
      table acc

end

module Action = Make (struct
  type ns = action
  type local_def = int
  let construct d = Action d
  let deconstruct s = match s with
    | Exists (Action d) -> d
    | _ -> raise Incorrect_namespace
end)

module Name = Make (struct
  type ns = name
  type local_def = int
  let construct d = Name d
  let deconstruct = function
    | Exists (Name d) -> d
    | _ -> raise Incorrect_namespace
end)

module Channel = Make (struct
  type ns = channel
  type local_def = unit
  let construct d = Channel d
  let deconstruct = function
    | Exists (Channel d) -> d
    | _ -> raise Incorrect_namespace
end)

module Function = Make (struct
  type ns = fname
  type local_def = int * function_def
  let construct d = Function d
  let deconstruct = function
    | Exists (Function d) -> d
    | _ -> raise Incorrect_namespace
end)

let is_ftype s ftype table =
  match Function.get_def s table with
    | _,t when t = ftype -> true
    | _ -> false
    | exception Not_found -> raise @@ Unbound_identifier s

module Macro = Make (struct
  type ns = macro
  type local_def = macro_def
  let construct d = Macro d
  let deconstruct = function
    | Exists (Macro d) -> d
    | _ -> raise Incorrect_namespace
end)

(*------------------------------------------------------------------*)
(** {2 Builtins} *)


(* reference used to build the table. Must not be exported in the .mli *)
let builtin_ref = ref empty_table

(** {3 Macro builtins} *)

let mk_macro m def =
  let table, m = Macro.declare_exact !builtin_ref m def in
  builtin_ref := table;
  m

let inp   = mk_macro "input"  Input
let out   = mk_macro "output" Output
let cond  = mk_macro "cond"   Cond
let exec  = mk_macro "exec"   Exec
let frame = mk_macro "frame"  Frame

(** {3 Channel builtins} *)

let dummy_channel_string = "ø" 
let table,dummy_channel = 
  Channel.declare_exact !builtin_ref dummy_channel_string ()
let () = builtin_ref := table

(** {3 Function symbols builtins} *)

let mk_fsymb f arity =
  let info = 0, Abstract arity in
  let table, f = Function.declare_exact !builtin_ref f info in
  builtin_ref := table;
  f

(** Diff *)

let fs_diff  = mk_fsymb "diff" 2

(** Boolean connectives *)

let fs_false  = mk_fsymb "false" 0
let fs_true   = mk_fsymb "true" 0
let fs_and    = mk_fsymb "and" 2
let fs_or     = mk_fsymb "or" 2
let fs_not    = mk_fsymb "not" 1
let fs_ite    = mk_fsymb "if" 3

(** Fail *)

let fs_fail   = mk_fsymb "fail" 0

(** Xor and its unit *)

let fs_xor    = mk_fsymb "xor" 2
let fs_zero   = mk_fsymb "zero" 0

(** Successor over natural numbers *)

let fs_succ   = mk_fsymb "succ" 1

(** Pairing *)

let fs_pair   = mk_fsymb "pair" 2
let fs_fst    = mk_fsymb "fst" 1
let fs_snd    = mk_fsymb "snd" 1

(** Exp **)

let fs_exp    = mk_fsymb "exp" 2
let fs_g      = mk_fsymb "g" 0

(** Empty *)

let fs_empty  = mk_fsymb "empty" 0

(** Length *)

let fs_len    = mk_fsymb "len" 1
let fs_zeroes = mk_fsymb "zeroes" 1


(** {3 Builtins table} *)

let builtins_table = !builtin_ref
