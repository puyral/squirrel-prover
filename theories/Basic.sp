set autoIntro=false.

(*------------------------------------------------------------------*)
(* equality *)

axiom [any] eq_iff (x, y : boolean) : (x = y) = (x <=> y).

axiom [any] eq_not (x, y : boolean) : (not(x) = not(y)) = (x = y).

goal [any] eq_sym ['a] (x,y : 'a) : (x = y) = (y = x).
Proof. by rewrite eq_iff. Qed.

goal [any] neq_sym ['a] (x,y : 'a) : (x <> y) = (y <> x).
Proof. by rewrite eq_iff. Qed.

goal [any] eq_refl ['a] (x : 'a) : (x = x) = true.
Proof. 
  by rewrite eq_iff. 
Qed.
hint rewrite eq_refl.

(*------------------------------------------------------------------*)
(* true/false *)

axiom [any] true_false : (true = false) = false.
hint rewrite true_false.

goal [any] false_true : (false = true) = false.
Proof. 
  by rewrite (eq_sym false true).
Qed.
hint rewrite false_true.

(*------------------------------------------------------------------*)
(* not *)

axiom [any] not_true : not(true) = false.
hint rewrite not_true.

axiom [any] not_false : not(false) = true.
hint rewrite not_false.


goal [any] not_not (b : boolean): not (not b) = b.
Proof.
  by case b.
Qed.
hint rewrite not_not.

goal [any] not_eq ['a] (x, y : 'a): not (x = y) = (x <> y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_eq.

goal [any] not_neq ['a] (x, y : 'a): not (x <> y) = (x = y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_neq.

(*------------------------------------------------------------------*)
(* disequality *)

goal [any] eq_false ['a] (x, y : 'a): ((x = y) = false) = (x <> y).
Proof. 
rewrite -not_eq. case (x = y) => _. simpl. auto.
by rewrite eq_iff. 
Qed.
hint rewrite eq_false.

(*------------------------------------------------------------------*)
(* and *)

axiom [any] and_comm (b,b' : boolean) : (b && b') = (b' && b).

axiom [any] and_true_l (b : boolean) : (true && b) = b.
hint rewrite and_true_l.

goal [any] and_true_r (b : boolean) : (b && true) = b.
Proof. by rewrite and_comm and_true_l. Qed.
hint rewrite and_true_r.

axiom [any] and_false_l (b : boolean) : (false && b) = false.
hint rewrite and_false_l.

goal [any] and_false_r (b : boolean) : (b && false) = false.
Proof. by rewrite and_comm and_false_l. Qed.
hint rewrite and_false_r.

(*------------------------------------------------------------------*)
(* or *)
axiom [any] or_comm (b,b' : boolean) : (b || b') = (b' || b).

axiom [any] or_false_l (b : boolean) : (false || b) = b.
hint rewrite or_false_l.

goal [any] or_false_r (b : boolean) : (b || false) = b.
Proof. by rewrite or_comm or_false_l. Qed.
hint rewrite or_false_r.

axiom [any] or_true_l (b : boolean) : (true || b) = true.
hint rewrite or_true_l.

goal [any] or_true_r (b : boolean) : (b || true) = true.
Proof. by rewrite or_comm or_true_l. Qed.
hint rewrite or_true_r.


(*------------------------------------------------------------------*)
(* not: more lemmas *)

goal [any] not_and (a, b : boolean): not (a && b) = (not a || not b).
Proof. 
  rewrite eq_iff. 
  case a; case b => //=.
Qed.

goal [any] not_or (a, b : boolean): not (a || b) = (not a && not b).
Proof. 
  rewrite eq_iff. 
  case a; case b => //=.
Qed.

(*------------------------------------------------------------------*)
(* if *)

goal [any] if_true ['a] (b : boolean, x,y : 'a):
 b => if b then x else y = x.
Proof.
  intro *.
  case (if b then x else y).
  + auto.
  + intro [HH _]. by use HH.
Qed.

goal [any] if_true0 ['a] (x,y : 'a):
 if true then x else y = x.
Proof.
  by rewrite if_true. 
Qed.
hint rewrite if_true0.

goal [any] if_false ['a] (b : boolean, x,y : 'a):
 (not b) => if b then x else y = y.
Proof.
  intro *; case (if b then x else y).
  + intro [HH _]. by use H.
  + auto.
Qed.

goal [any] if_false0 ['a] (x,y : 'a):
 if false then x else y = y.
Proof.
  by rewrite if_false.
Qed.
hint rewrite if_false0.

goal [any] if_then_then ['a] (b,b' : boolean, x,y : 'a):
  if b then (if b' then x else y) else y = if (b && b') then x else y.
Proof.  
  by case b; case b'.
Qed.

goal [any] if_then_implies ['a] (b,b' : boolean, x,y,z : 'a):
  if b then (if b' then x else y) else z =
  if b then (if b => b' then x else y) else z.
Proof.
  case b; intro H; case b'; intro H'; simpl; try auto.
  + by rewrite if_true.
  + rewrite if_false.
    intro Habs; by use Habs.
    auto.
Qed.

goal [any] if_same ['a] (b : boolean, x : 'a):
  if b then x else x = x.
Proof.
  by case b.
Qed.
hint rewrite if_same.

goal [any] if_then ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then (if b' then x else y) else z = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then.

goal [any] if_else ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then x else (if b' then y else z) = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_else.

goal [any] if_then_not ['a] (b,b' : boolean, x,y,z : 'a):
 b = not b' => 
 if b then (if b' then x else y) else z = 
 if b then y else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then_not.

goal [any] if_else_not ['a] (b,b' : boolean, x,y,z : 'a):
  b = not b' => 
 if b then x else (if b' then y else z) = 
 if b then x else y.
Proof.  
  by intro ->; case b'.
Qed.
hint rewrite if_else_not.

(*------------------------------------------------------------------*)
(* some functional properties *)

goal [any] fst_pair (x,y : message) : fst (<x,y>) = x.
Proof. auto. Qed.
hint rewrite fst_pair.

goal [any] snd_pair (x,y : message) : snd (<x,y>) = y.
Proof. auto. Qed.
hint rewrite snd_pair.

(*------------------------------------------------------------------*)
(* if-and-only-if *)

goal [any] iff_refl (x : boolean) : (x <=> x) = true.
Proof.
 by rewrite eq_iff. 
Qed.
hint rewrite iff_refl.

goal [any] iff_sym (x, y: boolean) : (x <=> y) = (y <=> x).
Proof.
 by rewrite eq_iff. 
Qed.

goal [any] true_iff_false : (true <=> false) = false.
Proof.
 by rewrite -eq_iff. 
Qed.
hint rewrite true_iff_false.

goal [any] false_iff_true : (false <=> true) = false.
Proof.
 by rewrite -eq_iff. 
Qed.
hint rewrite false_iff_true.
