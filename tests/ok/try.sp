name k : index -> message

abstract ok : message
channel c

system !_i (
in(c,x);
try find j such that x=k(j) in
out(c,ok) else out(c,x)).

goal not_else :
forall (i:index,j:index), happens(A1(i)) => output@A1(i) <> k(j).
Proof.
  intro i j Hap Heq.
  apply C to j.
Qed.
