set autoIntro=false.

hash h
name k:message
channel c

name n : message
name m : message

name secret : message

system !_a in(c,x); if True || x<> k then out(c,h(n,k)).

goal unforgeable :
  forall (tau:timestamp),
  happens(tau) => output@tau <> h(m,k).

Proof.
  intro tau Hap Heq.
  (* we cannot directly use euf, as k appears as a condition.
     But the condition True || x<> k is equivalent to True, so we can remove it.
  *)
  systemsubstitute simplified,a,cond@A(a),True,cond@A1(a),False.
  intro a. 
  expand cond@A(a); expand cond@A1(a). split; split. 
  by auto. 
  by intro _; left. 
  by intro H; notleft H; auto.
  by auto.
  by euf Heq; auto.
Qed.
