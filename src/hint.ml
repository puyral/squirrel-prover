open Utils

module L = Location
module Sv = Vars.Sv

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
type rw_hint = { 
  name : string; 
  rule : Rewrite.rw_erule;
}

let pp_rw_hint fmt rwh : unit =
  Fmt.pf fmt "%s : %a" rwh.name Rewrite.pp_rw_erule rwh.rule

(*------------------------------------------------------------------*)
module Hm = Match.Hm

type rewrite_db = rw_hint list Hm.t

let pp_rewrite_db fmt (db : rewrite_db) : unit =
  let pp_el fmt (hd, hints) =
    Fmt.pf fmt "@[<v>@[<v 2>%a@;%a@]@]"
      Match.pp_term_head hd
      (Fmt.list pp_rw_hint) hints
  in
  Fmt.pf fmt "@[<v>%a@]" (Fmt.list pp_el) (Hm.bindings db)

let empty_rewrite_db : rewrite_db = Hm.empty
let add_rewrite_rule (h : Match.term_head) (r : rw_hint) db : rewrite_db = 
  let l = odflt [] (Hm.find_opt h db) in
  Hm.add h (r :: l) db

let rules = []

(*------------------------------------------------------------------*)

type hint_db = { db_rewrite : rewrite_db; }
  
let empty_hint_db = { db_rewrite = empty_rewrite_db; }

let get_rewrite_db db = db.db_rewrite

(*------------------------------------------------------------------*)
type p_hint =
  | Hint_rewrite of lsymb

let add_hint_rewrite (s : lsymb) tyvars form db =
  let pat = Match.pat_of_form form in
  let pat = Match.{ pat with pat_tyvars = tyvars; } in      
  let rule = Rewrite.pat_to_rw_erule ~loc:(L.loc s) `LeftToRight pat in
  let h = { name = L.unloc s; rule; } in
  let head = 
    let Term.ESubst (src, _) = rule.Rewrite.rw_rw in
    Match.get_head src 
  in
  { db_rewrite = add_rewrite_rule head h db.db_rewrite; }
