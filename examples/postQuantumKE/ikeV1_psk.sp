(*******************************************************************************

Internet Key Exchange (IKE) Version 1, with Pre-Shared Key.

Defined in RFC2409: https://datatracker.ietf.org/doc/html/rfc2409

Claimed to be Post-Quantum secure in https://datatracker.ietf.org/doc/html/rfc8784

# Protocol Description

We consider the phase 1 of the aggressive mode.

Each pairing of agents as a pre-shared key, psk, that will be used only once.


The key exchange is given as

            Initiator(i)                      Responder(j)
           -----------                      -----------
             g^ai, Nii, IDi -->
                                  <--    g^bj, Nrj, IDj, HASH_R
             HASH_I           -->


where
    SKEYID := prf(psk(i,j), Nii | Nrj),
    HASH_I = prf(SKEYID, g^ai | g^bj | Idi )
    HASH_R = prf(SKEYID, g^bj | g^ar | IDij )

The final derived key is
        SKEYID_d = prf(SKEYID, g^aibj)


Remark that we abstract away from some implementation details, and do not model the
cookies or the headers.


# Threat Model

We consider a set of pre-shared keys psk(i,j) between a set of i distinct Initiator and j Responder.
We consider the system `((!_j R: ResponderI(j)) | (!_i I: InitiatorI(i)))`
Where responder j is willing to talk to any of the initiators.

The attacker does not have any pre-shared key.

*******************************************************************************)

set postQuantumSound = true.

hash h

(* pre-shared keys *)
name psk : index -> index -> message

(* DDH randomnesses *)
name a : index -> message
name b : index -> message

abstract g : message
abstract exp : message -> message -> message

(* fresh randomness *)
name Ni : index -> message
name Nr : index -> message

(* identities *)
name IdI : index -> message
name IdR : index -> message

abstract ok:message
abstract ko:message

channel cI
channel cR.

name sk : message.

(***********************************)
(* Main expression of the protocol *)

process Initiator(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that fst(snd(snd(m)))(*RIdR*) = IdR(j) in
    if  snd(snd(snd(m)))(*HashR*) =  h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > , h(<Ni(i), fst(snd(m))(*Nr*) > ,psk(i,j))) then
       let finalkey = h( exp( fst(m)(*gB*) ,a(i)),  h(<Ni(i), fst(snd(m)) > ,psk(i,j))) in
       out(cI,  h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > , h(<Ni(i), fst(snd(m))(*Nr*) > ,psk(i,j)))  )

process Responder(j:index) =
  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that snd(snd(m))(*RIdi*) = IdI(i) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > , h(< fst(snd(m)),Nr(j) > ,psk(i,j)))   >  >  > );

    in(cR, m2);
    if m2 =  h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > , h(< fst(snd(m)),Nr(j) > ,psk(i,j))) then
       out(cR, ok)

system [Main] ((!_j R: Responder(j)) | (!_i I: Initiator(i))).



(***********************************)
(*       Idealized version 1       *)

(* The keys obtained with the first prf application are all randoms. Some are
honest and shared by the two parties, and some correspond to garbage keys. *)

name Ininr : index -> index  -> message
name IgarbI : index -> index -> message
name IgarbR : index -> index -> message

process InitiatorI(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that fst(snd(snd(m)))(*RIdR*) = IdR(j) in
    if  snd(snd(snd(m)))(*HashR*) =  h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,
        (* idealized key computation *)
        try find il, jl such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             Ininr(i,j)
        else
             IgarbI(i,j)
          ) then
       let finalkey = h( exp( fst(m)(*gB*) ,a(i)),
        (* idealized key computation *)
        try find il, jl such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             Ininr(i,j)
        else
             IgarbI(i,j)
       ) in
       out(cI,  h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > ,
        (* idealized key computation *)
        try find il, jl such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             Ininr(i,j)
        else
             IgarbI(i,j)
)  )


process ResponderI(j:index) =
  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that snd(snd(m))(*RIdi*) = IdI(i) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,
        (* idealized key computation *)
        try find il, jl such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             Ininr(i,j)
        else
             IgarbR(i,j)
        )   >  >  > );

    in(cR, m2);
    if m2 =  h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,
        (* idealized key computation *)
        try find il, jl such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             Ininr(i,j)
        else
             IgarbR(i,j)
        ) then
       out(cR, ok)

system [Ideal1] ((!_j R: ResponderI(j)) | (!_i I: InitiatorI(i))).



(* We prove that the main expression and the ideal 1 are equivalent. *)

(* We start with 3 global prf applications, renaming the prf name to the one we want after each application. *)
system Main1 = [Main/left] with gprf (il,jl:index),  h(<Ni(il), Nr(jl) > ,psk(il,jl)).
system Main2 = [Main1/left] with rename forall (i,j:index), equiv(diff(n_PRF(i,j), Ininr(i,j))).


system Main3 = [Main2/left] with gprf (il,jl:index),  h(<Ni(il), fst(snd(input@I1(il,jl))) > ,psk(il,jl)).
system Main4 = [Main3/left] with rename forall (i,j:index), equiv(diff(n_PRF1(i,j), IgarbI(i,j))).

system Main5 = [Main4/left] with gprf (il,jl:index),  h(<fst(snd(input@R(jl,il))),Nr(jl) > ,psk(il,jl)).
system Main6 = [Main5/left] with rename forall (i,j:index), equiv(diff(n_PRF2(i,j), IgarbR(i,j))).


axiom  [Main6/left,Ideal1/right] tryfind : forall (i,j:index), pred(I1(i,j)) = pred(I2(i,j)).

equiv [Main6/left,Ideal1/right] test.
Proof.

diffeq.
(* From here, we need to prove that we indede get ideal keys everywhere. Mostly dumb manipulations of all the conditions introduced by the prf tactic, that are all contractory.
 *)

case  try find il0,jl0 such that
    _
   in IgarbI(il0,jl0)
   else
    _.
rewrite Meq.
fa.
use H3 with i,j.
rewrite tryfind.


case try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
rewrite Meq.
fa.
use H3 with i,j.

case  try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
rewrite Meq.
fa.
use H3 with i,j.

expand exec.

case try find il,jl such that _ in Ininr(i,j) else IgarbR(i,j).
rewrite Meq.

case try find il0,jl0 such that _  in Ininr(il0,jl0) else _.


use H8 with il,jl.


case try find il0,jl0 such that _ in Ininr(il0,jl0) else _.
use H8 with i,j.

case try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
use H9 with i,j.

case try find il,jl such that _ in IgarbR(il,jl) else _.
use H11 with i,j.

case try find il,jl such that _ in Ininr(i,j) else IgarbR(i,j).
rewrite Meq.

case try find il0,jl0 such that _ in Ininr(il0,jl0) else _.
rewrite Meq1.
use H4 with il,jl.

case try find il0,jl0 such that _ in Ininr(il0,jl0) else _.
use H4 with i,j.

case try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
use H5 with i,j.

case try find il,jl such that _ in IgarbR(il,jl) else _.
case try find il,jl such that _ in IgarbR(il,jl) else _.
rewrite Meq3.

use H7 with i,j.
use H7 with i,j.

case try find il,jl such that _ in Ininr(i,j) else IgarbR(i,j).
rewrite Meq.
case try find il0,jl0 such that _ in Ininr(il0,jl0) else _.
use H3 with il,jl.

case try find il0,jl0 such that _ in Ininr(il0,jl0) else _.
use H3 with i,j.

case try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
use H4 with i,j.

case try find il,jl such that _ in IgarbR(il,jl) else _.
use H6 with i,j.
Qed.


(***********************************)
(*       Idealized version 2       *)

(* In this next game, we just push one level up the tryfinds, with a syntactic manipulation. *)

process InitiatorI2(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that fst(snd(snd(m)))(*RIdR*) = IdR(j) in
    if  snd(snd(snd(m)))(*HashR*) =
        (* idealized key computation *)
        try find jl, il such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
         h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,    Ininr(j,i))
        else
           h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,  IgarbI(j,i))
           then
       out(cI,
        (* idealized key computation *)
        try find jl, il such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > ,Ininr(j,i))
        else
            h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > , IgarbI(j,i))
)


process ResponderI2(j:index) =
  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that snd(snd(m))(*RIdi*) = IdI(i) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,
        (* idealized key computation *)
        try find jl, il such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
            h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,   Ininr(j,i))
        else
          h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,     IgarbR(j,i))
           >  >  > );

    in(cR, m2);
    if m2 =
        (* idealized key computation *)
        try find jl, il such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  Ininr(j,i))
        else
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  IgarbR(j,i))
         then
       out(cR, ok)

system [Ideal2] ((!_j R: ResponderI2(j)) | (!_i I: InitiatorI2(i))).

(* We now prove the authentication on this ideal system. *)
goal [Ideal2] fst_pair (x,y : message) : fst (<x, y >) = x.
Proof. auto. Qed.
hint rewrite fst_pair.
goal [Ideal2] snd_pair (x,y : message) : snd (<x, y >) = y.
Proof. auto. Qed.
hint rewrite fst_pair.

goal [Ideal2] wa_1 :
  forall (i,j:index),
    happens(I1(i,j)) =>
    cond@I1(i,j) =>
    (exists (i0:index), happens(R(j,i0)) && R(j,i0) < I1(i,j) &&

      fst(output@R(j,i0)) = fst(input@I1(i,j)) &&
      fst(snd(output@R(j,i0))) = fst(snd(input@I1(i,j))) &&
      fst(snd(snd(output@R(j,i0)))) = fst(snd(snd(input@I1(i,j)))) &&
     fst(input@R(j,i0)) = fst(output@I(i))
     ).
Proof.
 intro i j.

 expand cond.

case  try find jl,il such that
       (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> &&
        (il = i && jl = j))
     in h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,Ininr(j,i))
     else h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,IgarbI(j,i)).

 (* Case 1 -> honnest skeyid *)
substeq Meq1.
euf Meq.

exists il.
expand output. repeat split.
by rewrite fst_pair.
by rewrite snd_pair fst_pair.
by rewrite snd_pair snd_pair fst_pair.
by depends I(il), I1(il,jl).

 (* Case 2 -> dishonnest skeyid, trivial as no one else computes this key *)
substeq Meq1.
euf Meq.
Qed.

goal [Ideal2] wa_2 :
  forall (i,j:index),
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
     happens(I(i)) &&
  fst(input@R(j,i)) = fst(output@I(i)) &&
    fst(snd(input@R(j,i))) = fst(snd(output@I(i))) &&
   snd(snd(input@R(j,i))) = snd(snd(output@I(i))).

Proof.
 intro i j.
expand exec.
 expand cond.

case  try find jl,il such that
      (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il),Nr(jl)> && (il = i && jl = j))
    in h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,Ininr(j,i))
    else h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,IgarbR(j,i)).
substeq Meq.

  (* honest case *)
  euf H0.

  depends I(il), I1(il,jl).
  by case H1.

  executable pred(R1(jl,il)).
  depends R(jl,il), R1(jl,il).
  use H2 with R(jl,il).
  expand exec. expand cond.

substeq Meq.
 euf H0.
Qed.


(*********************************)
(* Final game for Real or Random *)

(* this is ideal 2, where in addition each party IdI(i) in the end either outputs the derived key, or an idealied key ideal(i,j) if it thinks it is talking to party IdR(j). *)

name idealkeys : index -> index -> message

process InitiatorRoR(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that fst(snd(snd(m)))(*RIdR*) = IdR(j) in
    if  snd(snd(snd(m)))(*HashR*) =
        (* idealized key computation *)
        try find il, jl such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
         h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,    Ininr(j,i))
        else
           h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,  IgarbI(j,i))
           then
       out(cI,
        (* idealized key computation *)
        try find il, jl such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > ,Ininr(j,i))
        else
            h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > , IgarbI(j,i)));

       out(cI,diff(      try find il, jl such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             h( exp(fst(m),a(i)), Ininr(j,i))
        else
             h( exp(fst(m),a(i)),  IgarbI(j,i)), idealkeys(i,j))).


process ResponderRoR(j:index) =
  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that snd(snd(m))(*RIdi*) = IdI(i) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,
        (* idealized key computation *)
        try find il, jl such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
            h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,   Ininr(j,i))
        else
          h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,     IgarbR(j,i))
           >  >  > );

    in(cR, m2);
    if m2 =
        (* idealized key computation *)
        try find il, jl such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  Ininr(j,i))
        else
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  IgarbR(j,i))
         then
       out(cR,diff(
        try find il, jl such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
              h( exp(fst(m),b(j)), Ininr(j,i))
        else
               h( exp(fst(m),b(j)),  IgarbR(j,i))
, idealkeys(i,j))).

system [Ror] ((!_j R: ResponderRoR(j)) | (!_i I: InitiatorRoR(i))).



axiom [Ror] ddhcommu : forall (i,j:index), exp(exp(g,a(i)),b(j)) =  exp(exp(g,b(j)),a(i)) .
axiom [Ror] ddhnotuple : forall (m1,m2,m3,m4:message), exp(m3,m4) <> <m1,m2>.

(* we first prove two small authentication lemmas, so that if we reach the ideal key computation, we now we have the correct parameters. *)

goal [Ror] helper_wa :
  forall (i,j:index),
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
    fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i))
.

Proof.
 intro i j.
 expand exec.
 expand cond.
 case try find il,jl such that
      (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il),Nr(jl)> && (il = i && jl = j))
    in h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,Ininr(j,i))
    else h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,IgarbR(j,i)).

substeq Meq.
euf H0.
case H1.
depends R(jl,il), R1(jl,il).

by use ddhnotuple with  fst(input@R(jl,il)),<exp(g,b(jl)),IdI(il)>, fst(input@I1(il,jl)),a(il).

substeq Meq.
euf H0.
case H2.
depends R(j,i), R1(j,i).
Qed.




goal [Ror] helper_wa2 :
  forall (i,j:index),
    happens(I1(i,j)) =>
    exec@I1(i,j) =>

      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j))
     .
Proof.
 intro i j.
 expand exec.
 expand cond.

 case    try find il,jl such that
       (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> &&
        (il = i && jl = j))
     in h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,Ininr(j,i))
     else h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,IgarbI(j,i)).
substeq Meq1.
euf Meq.
by use ddhnotuple with fst(input@I1(il,jl)),<exp(g,a(il)),IdR(jl)>, fst(input@R(jl,il)),b(jl).
by depends I1(il,jl),I14(il,jl).

substeq Meq1.
euf Meq.
by use ddhnotuple with fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>, fst(input@I1(i,j)),a(i).
Qed.

system Ror2 = [Ror/left] with gprf (il,jl:index),   h( exp(exp(g,a(il)),b(jl)), Ininr(jl,il))   .
system Ror3 =  [Ror2/left] with rename forall (i,j:index), equiv(diff(n_PRF3(i,j), idealkeys(i,j))).



axiom  [Ror3/left, Ror/right] ddhcommu2 : forall (i,j:index), exp(exp(g,a(i)),b(j)) =  exp(exp(g,b(j)),a(i)) .
axiom  [Ror3/left, Ror/right] ddhnotuple1 : forall (m1,m2,m3,m4:message), exp(m3,m4) <> <m1,m2>.


(* By transitivity, we inherit the lemma on Ror to Ror2 *)
global goal [Ror/left,Ror2/left] helper_wa_equiv (i, j:index):
    [happens(R1(j,i))] ->
   equiv(
  exec@R1(j,i) =>
     input@R1(j,i) = input@R1(j,i) &&
    (fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i)))
).
Proof.
intro H2.
lemmas.
use prf_from_Ror_to_Ror2 with <a(i),Ni(i)>.
cycle 1.
intro i0 j0.
fresh 1.
use H with R(j,i) => //.
use H with R1(j,i) => //.
fa 0.
enrich frame@R(j,i).
enrich frame@R1(j,i).
repeat fa 1.
repeat fa 2.
repeat fa 3.
apply H1.

depends R(j,i), R1(j,i).
Qed.

goal [Ror2/left] helper_wa_aux3 :
  forall (i,j:index),
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
     input@R1(j,i) = input@R1(j,i) &&
    (fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i)))
.
Proof.

nosimpl(intro i j Hap).
rewrite equiv helper_wa_equiv  i j.

use helper_wa with i,j.
Qed.



global goal [Ror2/left,Ror3/left] helper_wa_equiv1 (i, j:index):
  [happens(R1(j,i))] ->
   equiv(
  exec@R1(j,i) =>
input@R1(j,i) = input@R1(j,i) &&
    (fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i)))
).
Proof.

intro H2.
use rename_from_Ror2_to_Ror3 with <a(i),Ni(i)>.
cycle 1.
intro i0 j0.
fresh 1.
use H with R(j,i) => //.
use H with R1(j,i) => //.
fa 0.
enrich frame@R(j,i).
enrich frame@R1(j,i).
repeat fa 1.
repeat fa 2.
apply H1.

depends R(j,i), R1(j,i).
Qed.


goal [Ror3/left] helper_wa_aux4 :
  forall (i,j:index),
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
     input@R1(j,i) = input@R1(j,i) &&
    (fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i)))
.
Proof.

nosimpl(intro i j Hap).
rewrite equiv helper_wa_equiv1  i j.

use helper_wa_aux3 with i,j.
Qed.




goal [Ror3/left, Ror/right] helper_wa3 :
  forall (i,j:index),
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
    fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i))
.
Proof.
intro i j.
project.
use helper_wa_aux4 with i,j.

use helper_wa with i,j.
Qed.


(* We now export helper wa 2 all the way to Ror3 *)
global goal [Ror/left,Ror2/left] helper_wa_equiv_2 :
  forall (i,j:index),
    [happens(I1(i,j))] ->
   equiv(
    exec@I1(i,j) =>

      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j))
)
     .
Proof.
intro i j Hap.
use prf_from_Ror_to_Ror2 with <b(j),Nr(j)>.
cycle 1.
intro i0 j0.
fresh 1.
use H with I1(i,j) => //.
fa 0.
repeat fa 1.
repeat fa 2.
repeat fa 3.

enrich frame@I1(i,j).

apply H0.
Qed.


goal [Ror2/left] helper_wa_aux2 :
  forall (i,j:index),
    happens(I1(i,j)) =>
    exec@I1(i,j) =>

      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j))
     .
Proof.

nosimpl(intro i j Hap).
rewrite equiv helper_wa_equiv_2  i j.
use helper_wa2 with i, j.
Qed.

global goal [Ror2/left,Ror3/left] helper_wa_equiv_3 :
  forall (i,j:index),
    [happens(I1(i,j))] ->
   equiv(
    exec@I1(i,j) =>

      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j))
)
     .
Proof.
intro i j Hap.
use rename_from_Ror2_to_Ror3 with <b(j),Nr(j)>.
cycle 1.
intro i0 j0.
fresh 1.
use H with I1(i,j) => //.
fa 0.
repeat fa 1.
repeat fa 2.
repeat fa 3.

enrich frame@I1(i,j).
apply H0.
Qed.

goal [Ror3/left] helper_wa_aux5 :
  forall (i,j:index),
    happens(I1(i,j)) =>
    exec@I1(i,j) =>

      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j))
     .
Proof.

nosimpl(intro i j Hap).
rewrite equiv helper_wa_equiv_3  i j.
use helper_wa_aux2 with i, j.
Qed.


goal [Ror3/left, Ror/right] helper_wa4 :
  forall (i,j:index),
    happens(I1(i,j)) =>
    exec@I1(i,j) =>

      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j))
     .
Proof.
intro i j.
project.

use helper_wa_aux5 with i,j.
use helper_wa2 with i,j.
Qed.

equiv [Ror3/left,Ror/right] final.
Proof.



diffeq.

case    try find il,jl such that
_
   in idealkeys(il,jl)
   else _.
by use ddhnotuple1 with  fst(input@I2(i,j)),<exp(g,a(i)),IdR(j)>, exp(g,a(i)),b(j).

fa.


use helper_wa4 with i,j.

case  try find il,jl such that _ in idealkeys(il,jl) else _.
rewrite Meq1.

case try find il0,jl0 such that _ in idealkeys(i,j) else _.
use H2 with i,j.

case try find il0,jl0 such that _ in  h(exp(fst(att(frame@pred(I1(i,j)))),a(i)),Ininr(j,i))
 else _.

use H2 with i,j.
rewrite ddhcommu2.

use H3 with i,j.
expand exec.

case try find il,jl such that _
   in idealkeys(il,jl)
   else _.
rewrite Meq.
by use ddhnotuple1 with  fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>, exp(g,a(i)),b(j).
by fa.

case    try find il,jl such that _
   in idealkeys(il,jl)
   else _.
by use ddhnotuple1 with  exp(g,a(i)),<fst(input@I1(i,j)),IdI(i)>, exp(g,a(i)),b(j).
by fa.

case    try find il,jl such that
       _
   in idealkeys(il,jl)
   else _.
by use ddhnotuple1 with  fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>, exp(g,a(i)),b(j).
by fa.

case    try find il,jl such that _
   in idealkeys(il,jl)
   else _.
by use ddhnotuple1 with  fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>, exp(g,a(i)),b(j).
by fa.


use helper_wa3 with i,j.
case try find il0,jl0 such that
   _
 in
   _
 else  h(exp(fst(att(frame@pred(R(j,i)))),b(j)),IgarbR(j,i)).
rewrite Meq1.

case (try find il,jl such that _
 in idealkeys(il,jl) else _).
use H2 with i,j.
use H2 with i,j.

case    try find il,jl such that _
   in idealkeys(il,jl)
   else _.
by use ddhnotuple1 with exp(g,b(j)),<fst(input@R(j,i)),IdR(j)>,exp(g,a(i)),b(j).

fa.
Qed.
