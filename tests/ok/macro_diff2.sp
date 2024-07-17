channel c

abstract ok : message
abstract ko : message

system s1 = in(c,x); let S=diff(ok,ko) in A : out(c,S).

system s2 = in(c,x); let St=diff(ko, ok) in A : out(c,St).

global lemma [s1/left,s1/right] _ (t : timestamp[const]) : 
  [happens(t)] -> [ok = ko] -> equiv(frame@t).
Proof. 
  intro H U.
  induction t.

  + auto.

  + expand frame, exec, cond, output, S. 
    rewrite U.
    (* The output should simplify into <input@A,ok> or,
       equivalently, diff(<input@A,ok>,<input@A,ok>).
       The goal, where input macros expand to bi-terms,
       is correct: dup can be used. *)
    fa <_,_>.
    by apply IH.
Qed.

abstract f : message -> message.
abstract g : message -> message.

system s3 = 
  in(c,x); 
  let X = diff(ok, ko) in 
  let X1 = diff(f(X), g(X)) in
  A: out(c, <X, X1>).

lemma [s3/left] _ (t : timestamp) : happens(A) => X1@A = f(ok).
Proof.
  intro H @/X1 @/X; congruence.
Qed.

lemma [s3/right] _ (t : timestamp) : happens(A) => X1@A = g(ko).
Proof.
  intro H @/X1 @/X; congruence.
Qed.

lemma [s3/right, s3/left] _ (t : timestamp) : 
  happens(A) => X1@A = diff(g(ko),f(ok)).
Proof.
  intro H.
  rewrite /X1; rewrite /X.
  project; congruence.
Qed.

(* same swapping systems *)
lemma [s3/left, s3/right] _ (t : timestamp) : 
  happens(A) => X1@A = diff(f(ok),g(ko)).
Proof.
  intro H.
  rewrite /X1; rewrite /X; project; congruence.
Qed.
