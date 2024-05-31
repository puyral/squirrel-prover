type lemma = { 
  stmt : Goal.statement;
  kind : [`Axiom | `Lemma];
} 

val pp : Format.formatter -> lemma -> unit

val as_lemma : Symbols.data -> lemma

(*------------------------------------------------------------------*)
val add_lemma :
  ?loc:Location.t ->
  [ `Axiom | `Lemma ] -> Goal.statement -> Symbols.table ->
  Symbols.table

val print_all : Format.formatter -> Symbols.table -> unit

(*------------------------------------------------------------------*)
(** Get proved or assumed statement. *)

val find : Symbols.p_path -> Symbols.table -> lemma

val find_stmt : Symbols.p_path -> Symbols.table -> Goal.statement
val find_kind : Symbols.p_path -> Symbols.table -> [`Axiom | `Lemma] 

val find_stmt_local  : Symbols.p_path -> Symbols.table -> Goal.local_statement
val find_stmt_global : Symbols.p_path -> Symbols.table -> Goal.global_statement

(*------------------------------------------------------------------*)
val mem        : Symbols.p_path -> Symbols.table -> bool
val mem_local  : Symbols.p_path -> Symbols.table -> bool
val mem_global : Symbols.p_path -> Symbols.table -> bool

(*------------------------------------------------------------------*)
val pp_kind : Format.formatter -> [`Axiom | `Lemma] -> unit

(*------------------------------------------------------------------*)
(** {2 Depends, Mutex } *)

(** Add to the symbol table the sequential dependencies and mutual
    exclusion lemmas for a given system. *)
val add_depends_mutex_lemmas : Symbols.table -> Symbols.system -> Symbols.table
