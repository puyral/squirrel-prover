

type T
type NL [large]
type NFL [name_fixed_length]
type N [large,name_fixed_length]

abstract f : index -> message.

abstract to_T : message -> T.
abstract from_T : T -> message.

abstract to_N : message -> N.
abstract from_N : N -> message.

abstract N_to_T : N -> T.

abstract gg  ['a] : 'a -> 'a.

name nn : index -> NL.
name nfl : index -> NFL.
name nt : index -> T.

system null.

axiom _ (x : message) : gg(zero) = zero.

axiom _ (x,y : message) : to_T(x) = to_T(y) => x = y.

axiom _ (x : message) : from_T(to_T(x)) = x.

axiom _ (x : message) : N_to_T(to_N(x)) = to_T(x).

(* gg is polymorphique *)
axiom _ (x : message) : gg(N_to_T(gg(to_N(gg(x))))) = gg(to_T(gg(x))).

(*------------------------------------------------------------------*)
(* check that len is polymorphique *)
axiom _ (i,j : index) : 
len(nn(i)) = len(empty) && len(nn(j)) = len(nt(j)) => i = j.

(*------------------------------------------------------------------*)
(* check the [large] type info  *)
lemma _ (i,j : index) : nn(i) = nn(j) => i = j.
Proof. auto. Qed.

lemma _ (i,j : index) : nt(i) = nt(j) => i = j.
Proof. checkfail auto exn GoalNotClosed. Abort.

(*------------------------------------------------------------------*)
(* check the [named_fixed_length] type info  *)
lemma _ (i,j : index) : len(nfl(i)) = len(nfl(j)).
Proof.
by rewrite !namelength_nfl.
Qed.

lemma _ (i,j : index) : len(nn(i)) = len(nn(j)).
Proof.
checkfail rewrite namelength_nn exn Failure.
Abort.

(*------------------------------------------------------------------*)
(* check that names of different types do not necessarily have same length *)
type NFL2 [name_fixed_length]
name nfl2 : index -> NFL2.

lemma _ (i,j : index) : len(nfl(i)) = len(nfl2(j)).
Proof.
rewrite namelength_nfl namelength_nfl2.
checkfail auto exn GoalNotClosed.
Abort.
