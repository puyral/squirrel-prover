set autoIntro=false.

system null.

goal forall (t:timestamp), not (happens (init)).
Proof.
  intro t. 
Qed.
