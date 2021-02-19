set autoIntro=false.

channel c

system !_i in(c,x);out(c,x);in(c,x);out(c,x).

goal _ (i:index): happens(A1(i)) => A(i) < A1(i).
Proof.
  intro i Hap.
  depends A(i), A1(i).
  by auto.
Qed.

(* Not true if only A1(i) happens *)
goal _ (i:index): happens(A(i)) => A(i) < A1(i).
Proof.
  intro i Hap.
  depends A(i), A1(i).
  checkfail auto exn GoalNotClosed.
Abort.
