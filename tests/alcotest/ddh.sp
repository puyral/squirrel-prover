

name a : index -> message
name b : index -> message
name k : index -> message

ddh g, (^) where group:message exponents:message.

channel c

system (!_i ( out(c, diff((g ^ a(i)) ^ b(i),g ^ k(i))))
       | !_j ( in(c,x);out(c,g ^ x ^ a(j)))
       ).


equiv ddh_goal.
Proof.
 nosimpl(induction t).
 expandall; refl + assumption.
 try (expandall; refl + assumption).
 try (expandall; refl + assumption).
 cycle 1.
 expandall.
 try (expandall; refl + assumption).
 fa !<_,_>, (if _ then _).
 ddh g, a, b, k.
Qed.
