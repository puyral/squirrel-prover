type unknown

(** Type of symbols *)
type 'a t = string

type kind = Vars.sort

type function_def =
  | Hash
  | AEnc
  | Abstract of kind list * kind

type macro_def =
  | Input | Output
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

type some_def =
  | Exists : 'a def -> some_def
  | Reserved

type data = ..
type data += Empty

let to_string s = s

let table : (string,some_def*data) Hashtbl.t = Hashtbl.create 97

let prefix_count_regexp = Pcre.regexp "([^0-9]*)([0-9]*)"

let fresh prefix =
  let substrings = Pcre.exec ~rex:prefix_count_regexp prefix in
  let prefix = Pcre.get_substring substrings 1 in
  let i0 = Pcre.get_substring substrings 2 in
  let i0 = if i0 = "" then 0 else int_of_string i0 in
  let rec find i =
    let s = if i=0 then prefix else prefix ^ string_of_int i in
    if Hashtbl.mem table s then find (i+1) else s
  in
  find i0

exception Unbound_identifier
exception Incorrect_namespace
exception Multiple_declarations

let exists s = Hashtbl.mem table s

let get_data s = snd (Hashtbl.find table s)

let def_of_string s =
  try fst (Hashtbl.find table s) with Not_found -> raise Unbound_identifier

type wrapped = Wrapped : 'a t * 'a def -> wrapped

let of_string s =
  try match Hashtbl.find table s with
    | Exists d, _ -> Wrapped (s,d)
    | Reserved, _ -> raise Unbound_identifier
  with Not_found -> raise Unbound_identifier

let run_restore f () =
  let copy = Hashtbl.copy table in
  let restore () =
    Hashtbl.clear table ;
    Hashtbl.iter
      (fun k v -> Hashtbl.replace table k v)
      copy
  in
  try ignore (f ()) ; restore () with e -> restore () ; raise e

module type Namespace = sig
  type ns
  type def
  val reserve : string -> data t
  val define : data t -> ?data:data -> def -> unit
  val declare : string -> ?data:data -> def -> ns t
  val declare_exact : string -> ?data:data -> def -> ns t
  val of_string : string -> ns t
  val get_def : ns t -> def
  val def_of_string : string -> def
  val get_data : ns t -> data
  val data_of_string : string -> data
  val get_all : ns t -> def * data
  val iter : (ns t -> def -> data -> unit) -> unit
end

module type S = sig
  type ns
  type local_def
  val construct : local_def -> ns def
  val deconstruct : some_def -> local_def
end

module Make (M:S) : Namespace with type ns = M.ns with type def = M.local_def = struct

  type ns = M.ns
  type def = M.local_def

  let reserve name =
    let symb = fresh name in
      Hashtbl.add table symb (Reserved,Empty) ;
      symb

  let define symb ?(data=Empty) value =
    assert (fst (Hashtbl.find table symb) = Reserved) ;
    Hashtbl.replace table symb (Exists (M.construct value), data)

  let declare name ?(data=Empty) value =
    let symb = fresh name in
      Hashtbl.add table symb (Exists (M.construct value), data) ;
      symb

  let declare_exact name ?(data=Empty) value =
    if Hashtbl.mem table name then raise Multiple_declarations ;
    Hashtbl.add table name (Exists (M.construct value), data) ;
    name

  let get_all (name:ns t) =
    (* We know that [name] is bound in [table]. *)
    let def,data = Hashtbl.find table name in
      M.deconstruct def, data

  let get_def name = fst (get_all name)
  let get_data name = snd (get_all name)

  let of_string name =
    try
      ignore (M.deconstruct (fst (Hashtbl.find table name))) ;
      name
    with Not_found -> raise Unbound_identifier

  let def_of_string s =
    try
      M.deconstruct (fst (Hashtbl.find table s))
    with Not_found -> raise Unbound_identifier

  let data_of_string s =
    try
      let def,data = Hashtbl.find table s in
        (* Check that we are in the current namespace
         * before returning the associated data. *)
        ignore (M.deconstruct def) ;
        data
    with Not_found -> raise Unbound_identifier

  let iter f =
    Hashtbl.iter
      (fun s (def,data) ->
         try f s (M.deconstruct def) data with
           | Unbound_identifier -> ())
      table

end

module Action = Make (struct
  type ns = action
  type local_def = int
  let construct d = Action d
  let deconstruct = function
    | Exists (Action d) -> d
    | _ -> raise Unbound_identifier
end)

module Name = Make (struct
  type ns = name
  type local_def = int
  let construct d = Name d
  let deconstruct = function
    | Exists (Name d) -> d
    | _ -> raise Unbound_identifier
end)

module Channel = Make (struct
  type ns = channel
  type local_def = unit
  let construct d = Channel d
  let deconstruct = function
    | Exists (Channel d) -> d
    | _ -> raise Unbound_identifier
end)

module Function = Make (struct
  type ns = fname
  type local_def = int * function_def
  let construct d = Function d
  let deconstruct = function
    | Exists (Function d) -> d
    | _ -> raise Unbound_identifier
end)

module Macro = Make (struct
  type ns = macro
  type local_def = macro_def
  let construct d = Macro d
  let deconstruct = function
    | Exists (Macro d) -> d
    | _ -> raise Unbound_identifier
end)
