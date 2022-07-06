

(* Check `assert (ip := pt)` tactic *)

name k:message

system null.

axiom axiom1 (ma : message): exists (m:message), k = m && m = ma.

goal _ (ma : message) : ma = k.
Proof.
 have H := axiom1 ma. 
 destruct H as [m [H1 H2]].
 rewrite -H2 -H1.
 clear H1 H2.
 congruence.
Qed.

(* with an intro pattern *)
goal _ (ma : message) : ma = k.
Proof.
 have [m [H1 H2]] := axiom1 ma. 
 rewrite -H2 -H1.
 clear H1 H2.
 congruence.
Qed.

(*------------------------------------------------------------------*)
axiom axiom2 (ma : message): ma = k => k = ma.

(* check that implications are not introduced by default *)
goal _ (ma : message) : ma = k => k = ma.
Proof.
 intro Hyp.
 have H := axiom2 ma. 
 apply H.
 assumption.
Qed.

(*------------------------------------------------------------------*)

abstract P : bool.
abstract Q : bool.
abstract R : bool.

goal _ (ma : message) : (P => Q => R) => P => Q => R.
Proof.
  intro H1 H2 H3.
  have M := H1 _.
  + clear H1 H3. 
    assumption. 
  + clear H1 H2. 
    apply M. 
    assumption. 
Qed.

abstract Pi : index -> bool.
abstract Qi : index -> index -> bool.
abstract Ri : index -> index -> bool.

goal _ (ma : message, j : index) : 
  (forall (i : index), Pi(i) => Qi(i,i) => Ri(i,i)) => 
  Qi(j,j) =>
  Pi(j) =>
  Ri(j,j).
Proof.
  intro H1 H2 H3.
  have M := H1 _ _ H2. 
  + clear H1 H2.
    assumption.
  + clear H1 H2 H3.
    assumption.
Qed.
