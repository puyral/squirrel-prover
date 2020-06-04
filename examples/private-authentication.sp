(*******************************************************************************
PRIVATE AUTHENTICATION

[F] G. Bana and H. Comon-Lundh. A computationally complete symbolic
attacker for equivalence properties. In 2014 ACM Conference on
Computer and Communications Security, CCS ’14, pages 609–620.
ACM, 2014

A -> B : enc(<pkA,n0>,r0,pkB)
B -> A : enc(<n0,n0>,r,pkA)

This is a "light" model without the last check of A.
*******************************************************************************)

channel cA
channel cB

name kA : message
name kAbis : message
name kB : message

aenc enc,dec,pk

name n0 : index -> message
name r0 : index -> message

name n : index -> message
name r : index -> message
name r2 : index -> message

abstract plus : message -> message -> message

axiom length :
  forall (m1:message, m2:message) len(<m1,m2>) = plus(len(m1),len(m2))

process A(i:index) =
  out(cA,  enc(<pk(kA),n0(i)>,r0(i),pk(kB)))

process B(i:index) =
  in(cB, mess);
  let dmess = dec(mess, kB) in
  out(cB,
    if fst(dmess) = diff(pk(kA),pk(kAbis)) && len(snd(dmess)) = len(n(i)) then
      enc(<snd(dmess), n(i)>, r(i), pk(diff(kA,kAbis)))
    else
      enc(<n(i), n(i)>, r(i), pk(diff(kA,kAbis)))
  )

system out(cA,<pk(kA),pk(kB)>); (!_i A(i) | !_j B(j)).

equiv secrecy.
Proof.
  enrich pk(kA); enrich pk(kB).

  induction t.

  (* Case A *)
  expandall.
  fa 2.

  (* Case A1 *)
  expandall.
  fa 2. fa 3.  fa 3.
  cca1 3.
  fa 3. fa 3. fresh 3. yesif 3.

  (* Case B *)
  expandall.
  fa 2. fa 3.
  enckp 3. enckp 3.
  fa 3.
  cca1 3.

  (* length reasoning *)
  equivalent
    len(<snd(dec(input@B(j),kB)),n(j)>),
    plus(len(snd(dec(input@B(j),kB))),len(n(j))).
  apply length to snd(dec(input@B(j),kB)),n(j).

  ifeq 3, len(snd(dec(input@B(j),kB))), len(n(j)).

  trivialif 3.
  apply length to n(j),n(j).
  fa 3. fa 3. fa 3.
  fresh 3. yesif 3.
  fresh 3.  yesif 3.
Qed.
