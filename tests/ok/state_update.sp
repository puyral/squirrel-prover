mutable s : index->message
abstract f : message->message

system !_i s(i):=f(s(i)).

goal update : forall (i:index) s(i)@A(i) = f(s(i)@pred(A(i))).
Proof.
  auto.
Qed.

goal not_update: forall (i,j:index), i<>j => s(i)@A(j) = s(i)@pred(A(j)).
Proof.
  intro i j Hneq.
  expand s(i)@A(j).
  by noif; auto.
Qed.
