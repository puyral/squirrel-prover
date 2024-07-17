channel c.

system (
  in(c,x); 
  if x = x then A: out(c, empty) else B: out(c, empty)
).

lemma _ : not (happens B) || not (happens A).
Proof. by apply mutex_default_B_A. Qed.

(*------------------------------------------------------------------*)
system foo = (
  !_a
  in(c,x); 
  if x = x then !_i (C: out(c, empty); out(c, empty)) else !_i !_j D: out(c, empty)
).

print mutex_foo_C_D.

lemma [foo] _ (a,i,j,k : index) : 
  not (happens (C a i)) || not (happens(D a j k)).
Proof. by apply mutex_foo_C_D. Qed.

lemma [foo] _ (a,i,j,k : index) : 
  not (happens (C1 a i)) || not (happens(D a j k)).
Proof. by apply mutex_foo_C1_D. Qed.

lemma [foo] _ (a,a0,i,j,k : index) : 
  not (happens (C a i)) || not (happens(D a0 j k)).
Proof. 
  checkfail (try apply mutex_foo_C_D); auto exn GoalNotClosed. 
Abort.

lemma [foo] _ (a,i,j,k : index) : 
  not (happens (C1 a i)) || not (happens(C a j)).
Proof. 
  checkfail (try apply mutex_foo_C_C1); auto exn GoalNotClosed.
  checkfail (try apply mutex_foo_C1_C); auto exn GoalNotClosed.
Abort.

lemma [foo] _ (a,i,j,k : index) : 
  not (happens (C a i)) || not (happens(C a j)).
Proof. 
  checkfail (try apply mutex_foo_C_C); auto exn GoalNotClosed.
  checkfail (try apply mutex_foo_C_C1); auto exn GoalNotClosed.
  checkfail (try apply mutex_foo_C1_C); auto exn GoalNotClosed.
Abort.
