set autoIntro=false.

system null.
goal forall (t:timestamp), not(happens(t)) => not(happens(t)).
Proof.
  nosimpl(intro t Hnot H).
  nosimpl(use Hnot; assumption). 
Qed.
