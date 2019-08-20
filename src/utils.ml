module List = struct
  include List

  (** [init n f] returns the list containing the results of
      [(f 0)],[(f 1)] ... [(f (n-1))].  *)
  let init n f =
    if n < 0 then raise (Failure "List.init")
    else
      let rec ini i = if i = n then [] else (f i) :: ini (i + 1) in
      ini 0

  let rec map3 f l1 l2 l3 =
    match (l1, l2, l3) with
      ([], [], []) -> []
    | (a1::l1, a2::l2, a3::l3) -> let r = f a1 a2 a3 in r :: map3 f l1 l2 l3
    | (_, _, _) -> invalid_arg "Utils.List.map3"

  (** [merge_uniq cmp l1 l2] behaves like [List.merge cmp l1 l2], except that
      it removes duplicates, w.r.t. [cmp], between [l1] and [l2].
      Duplicates already in [l1] or [l2] may remains. *)
  let rec merge_uniq cmp l1 l2 =
    match l1, l2 with
    | [], l2 -> l2
    | l1, [] -> l1
    | h1 :: t1, h2 :: t2 ->
      let c = cmp h1 h2 in
      if c = 0 then h1 :: merge cmp t1 t2
      else if c < 0
      then h1 :: merge cmp t1 l2
      else h2 :: merge cmp l1 t2

  (** [split_pred f l] split [l] into the list of elements where [f] holds and
      the list of elements where [f] does not hold, while respecting the
      ordering in [l]. *)
  let split_pred f l =
    let rec aux t_l f_l = function
      | [] -> (t_l, f_l)
      | a :: l' ->
        if f a then aux (a :: t_l) f_l l' else aux t_l (a :: f_l) l' in
    aux [] [] l

  let rec split3 = function
      [] -> ([], [], [])
    | (x,y,z)::l ->
      let (rx, ry, rz) = split3 l in (x::rx, y::ry, z::rz)
end

module Imap = Map.Make (struct
  type t = int
  let compare = Pervasives.compare
end)

module type Ordered = sig
  type t
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end


(** Variable size persistent union-find data-structure on integers. *)
module Vuf : sig
  type t

  val create : int -> t

  (** Add a new element to the partition, which is alone in its class. *)
  val extend : t -> int * t

  val find : t -> int -> int

  (** [union t u v] always uses the representent of [v], i.e.
    [find [union t u v] u] = [find t v] *)
  val union : t -> int -> int -> t

end = struct

  (** Variable size persistent union-find, by leaving some unused elements:
      - [uf] contains a partition of [0,...,max_size - 1]
      - Only classes in [0,...,size-1] may be modified by union and find. *)
  type t = { uf : Puf.t;
             size : int;
             max_size : int }

  let create i =
    (* If [n] is 0 or 1, extend will fail. *)
    let n = max i 2 in
    { uf = Puf.create (2 * n); (* The factor 2 is arbitrary. *)
      size = n;
      max_size = 2 * n }

  let extend t =
    if t.size < t.max_size then (t.size, { t with size = t.size + 1 })
    else begin
      let uf' = ref (Puf.create (t.max_size * 2)) in
      for i = 0 to t.size - 1 do
        uf' := Puf.union !uf' i (Puf.find t.uf i);
      done;
      (t.size, { uf = !uf'; size = t.size + 1; max_size = t.max_size * 2 } )
    end

  let find t i =
    if i >= t.size then raise (Failure "Vuf: out of range")
    else Puf.find t.uf i

  (** [union t u v] always uses the representent of [v], i.e.
    [find [union t u v] u] = [find t v] *)
  let union t i j =
    if i >= t.size || j >= t.size then raise (Failure "Vuf: out of range")
    else { t with uf = Puf.union t.uf i j }
end


(** Create a union-find data-structure over elements of type 'a. *)
module Uf (Ord: Ordered) = struct
  type v = Ord.t
  module Vmap = Map.Make(Ord)

  (** [rmap] is the inverse of map.
     [cpt] counts the number of non-trivial unions *)
  type t = { map : int Vmap.t;
             rmap : v Imap.t;
             puf : Vuf.t;
             cpt : int }

  let print ppf t =
    let binds = Imap.bindings t.rmap
                |> List.sort (fun (i,_) (i',_) -> Pervasives.compare i i') in
    Fmt.pf ppf "@[<v 0>%a@]"
      (Fmt.list (fun ppf (i,u) ->
           let ri = Vuf.find t.puf i in
           Fmt.pf ppf "@[%d->%d : @,%a->%a@]"
             i ri Ord.print u Ord.print (Imap.find ri t.rmap)
         )) binds

  let create l =
    let _,m,rm =
      List.fold_left (fun ( i, m, rm ) a ->
          ( i+1, Vmap.add a i m, Imap.add i a rm ))
        ( 0, Vmap.empty, Imap.empty ) l in

    { map = m;
      rmap = rm;
      puf = Vuf.create (List.length l);
      cpt = 0 }

  (** [extend t v] add the element [v] to [t], if necessary. *)
  let extend t v =
    if Vmap.mem v t.map then t
    else let i, uf = Vuf.extend t.puf in
      { t with puf = uf;
               map = Vmap.add v i t.map;
               rmap = Imap.add i v t.rmap }

  let find t u =
    let ru_eqc = Vmap.find u t.map |> Vuf.find t.puf in
    Imap.find ru_eqc t.rmap

  let swap t u u' =
    let i = Vmap.find u t.map
    and i' = Vmap.find u' t.map in

    { t with map = Vmap.add u i' t.map
                   |> Vmap.add u' i;
             rmap = Imap.add i u' t.rmap
                    |> Imap.add i' u }

  (** [union t u v] always uses the representent of [v], i.e.
      [find [union t u v] u] = [find t v] *)
  let union t u u' =
    let iu,iu' = Vmap.find u t.map, Vmap.find u' t.map in
    let ri,ri' = Vuf.find t.puf iu, Vuf.find t.puf iu' in

    let t' = { t with puf = Vuf.union t.puf iu iu';
                      cpt = if ri <> ri' then t.cpt + 1 else t.cpt } in

    let n_ri' = Vmap.find u' t'.map |> Vuf.find t'.puf in

    if ri' <> n_ri' then swap t' u u' else t'

  let add_acc a acc = match acc with
    | [] -> raise (Failure "Uf: add_acc")
    | l :: t -> (a :: l) :: t

  (** [classes t] return the list of equivalence classes of [t], where a class
      is represented by the list of its elements. *)
  let classes t =
    let l = List.init (Imap.cardinal t.rmap) (fun i -> (Vuf.find t.puf i, i))
            |> List.sort (fun (a,_) (a',_) -> Pervasives.compare a a') in

    let l_eqc = match l with
      | [] -> []
      | (x,_) :: _ ->
        List.fold_left (fun (acc,x_old) (x,y) ->
            if x = x_old then (add_acc y acc, x)
            else ([y] :: acc, x)
          ) ([[]], x) l
        |> fst in

    List.map (List.map (fun x -> Imap.find x t.rmap)) l_eqc

  (** [union_count t] is the number of non-trivial unions done building [t] *)
  let union_count t = t.cpt
end


let rec fpt f a =
  let b = f a in
  if b = a then b else fpt f b

(* Option type functions *)
let opt_get = function
  | Some u -> u
  | None -> raise Not_found

let some x = Some x

let opt_map a f = match a with
  | None -> None
  | Some x -> f x


(** [classes f_eq l] returns the equivalence classes of [l] modulo [f_eq],
    assuming [f_eq] is an equivalence relation. *)
let classes (f_eq : 'a -> 'a -> bool) (l : 'a list) : 'a list list =
  let rec get_cl cl rem x = function
    | [] -> cl,rem
    | y :: l ->
      if f_eq x y then get_cl (y :: cl) rem x l
      else get_cl cl (y :: rem) x l in

  let rec comp cls = function
    | [] -> cls
    | x :: rem ->
      let cl, rem' = get_cl [x] [] x rem in
      comp (cl :: cls) rem' in

  comp [] l

let ident ppf s = Fmt.pf ppf "%s" s
let kw style = (Fmt.styled style ident)

let pp_ne_list s pp_list ppf l =
  if l = [] then Fmt.pf ppf "" else Fmt.pf ppf s pp_list l

let map_of_iter (iter : ('a -> unit) -> unit) (f : 'a -> 'b) =
  let l = ref [] in
  let f_side x = l := (f x) :: !l in
  iter f_side;
  !l
