(* declares an abstract operator *)
op abs_op : message.

(*------------------------------------------------------------------*)
(* test concrete operators *)

op triple (x, y, z : message) : message = <x, <y, z>>.

(* implicit return type *)
op triple' (x, y, z : message) = <x, <y, z>>.

(* generic pairs *)
abstract gpair ['a] : 'a -> 'a -> 'a.

op gtriple ['a] (x, y, z : 'a) = gpair x (gpair y z).

op foo ['a] (x : 'a) = gtriple x x x.

system null.

axiom [any] gpair_ax (x,y : message) : gpair x y = <x,y>.

(*------------------------------------------------------------------*)
lemma _ (a,b,c : message) : gtriple a b c = triple a b c.
Proof.
  rewrite /gtriple /triple !gpair_ax. 
  auto.
Qed.

(* same goal with [any] *)
lemma [any] _ (a,b,c : message) : gtriple a b c = triple a b c.
Proof.
  rewrite /gtriple /triple !gpair_ax. 
  auto.
Qed.

(*------------------------------------------------------------------*)
(* check unfolding of infix operators *)

op (~<) (x : message, y : message) : message = zero.

lemma _ (x, y : message) : x ~< y = zero.
Proof. by rewrite /(~<). Qed.

(* same goal with [any] *)
lemma [any] _ (x, y : message) : x ~< y = zero.
Proof. by rewrite /(~<). Qed.

(*------------------------------------------------------------------*)
op fst_p ((x,y) : message * message) = x.
op snd_p ((x,y) : message * message) = y.

lemma [any] fst_p_charac (x, y : message) : fst_p (x,y) = x.
Proof. auto. Qed.

lemma [any] snd_p_charac (x, y : message) : snd_p (x,y) = y.
Proof. auto. Qed.

(* sanity check *)
lemma [any] _ (x, y : message) : fst_p (x,y) = y.
Proof. checkfail auto exn GoalNotClosed. Abort.

(* sanity check *)
lemma [any] _ (x, y : message) : snd_p (x,y) = x.
Proof. checkfail auto exn GoalNotClosed. Abort.


(*------------------------------------------------------------------*)
op third_triple ((x,y,z) : message * message * message) = z.

lemma [any] _ (a,b,c : message) : third_triple (a,b,c) = c.
Proof. auto. Qed.

(* sanity check *)
lemma [any] _ (a,b,c : message) : third_triple (a,b,c) = b.
Proof. checkfail auto exn GoalNotClosed. Abort.

