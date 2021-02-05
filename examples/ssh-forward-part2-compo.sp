(*******************************************************************************
SSH (WITH FORWARDING AGENT)

We refer to P and S as the two processes of ssh-forward-part1-comp.sp

In this protocol,

 - PFA is a process which first runs P, and then starts a forwarded agent
process, which accepts to sign queries received on the secure channel
established through P

 - PDIS is a protocol which first runs S, and then can run P on the distant
server. When P while require a signature, it will request it on the channel
established by S, to contact some forwarded agent.

 - SDIS is the server that will communicated with P run by PDIS.


PFA <-> PDIS : SSH key exchange, deriving an ideal key k11.

PDIS -> SDIS : g^a
SDIS-> PDIS : g^b, pkS, sign(h(g^a,g^b, g^ab),skS) )
PDIS -> PFA : enc(<"sign request",h(g^a,g^b, g^ab)>,k11 )
PFA -> PDIS : enc(<"sign answer",sign(h(g^a,g^b, g^ab),skP)>,k11 )
PDIS -> SDIS : enc( sign(g(g^a,g^b,g^ab),skP) , g^ab)


We prove that one session of the second key exchange is secure, when it is using
a secure channel with an idealized key k11, and the attacker has access to an
oracle that allows to simulate either other sessions of the forwarded key
exchange, or sessions of the original key exchange.

This proof, is split into authentication and secrecy, as in
ssh-forward-part1-comp.sp.

The security of a forwarded session when using a previously derived key is
proved in the file ssh-forward-part2-compo.sp. Together with [1], those two
files prove the security of SSH with one session forwarding for an unbounded
number of sessions.

[1] : Hubert Comon, Charlie Jacomme, and Guillaume Scerri. Oracle simula-
tion: a technique for protocol composition with long term shared secrets.
In Proceedings of the 2020 ACM SIGSAC Conference on Computer and
Communications Security, pages 1427–1444, 2020.
*******************************************************************************)

abstract ok : message
abstract ko : message
abstract forwarded : message
abstract reqsign : message
abstract anssign : message

name kP : message
name kS : message

channel cP
channel cS
channel c

name ake1 : index -> message
name bke1 : index -> message
name ake11 : message
name bke11 : message
name k11 : message

name a1 : message
name b1 : message
name c11 : message
name a : index -> message
name b : index -> message
name k : index -> index -> message

name r : message
name r2 : index -> message
name r3 : message
name r4 : message
name r5 : message

(* As ssh uses a non keyed hash function, we rely on a fixed key hKey known to the attacker *)
(* Note that hKey has to be a name and not a constant and this key is revealed at the beginning *)

name hKey : message
hash h with oracle forall (m:message,sk:message), sk = hKey

(* We assume that the encryption is INT-CTXT. This is assumed to hold even when the key appears under some hash functions. *)
senc enc,dec with h


signature sign,checksign,pk with oracle forall (m:message,sk:message)
(sk <> kP
 || exists (i:index, m1:message, m2:message)
      m = <forwarded, h(<<g^a(i),m1>,m2>, hKey)> (* O_FPS *)
 || exists (i:index, m1:message, m2:message)
      m = h(<<g^ake1(i),m1>,m2>, hKey) (* O_KE1 *)
 )
  &&
(sk <> kS
 || exists (i:index, m1:message, m2:message)
      m = <forwarded, h(<<m1,g^b(i)>,m2>, hKey)> (* O_FPS *)
 || exists (i:index, m1:message, m2:message)
      m = h(<<m1,g^bke1(i)>,m2>, hKey) (* O_KE1 *)
)


(** We first present the general SSH process. *)

process P1FA =
  in(cP,gB);
  out(cP,ok);
  (* begin P1 *)
  in(cP,t);
  let sidP = h(<<g^ake11,gB>,k11>, hKey) in
  let pkS = fst(t) in
  if pkS = pk(kS) && checksign(snd(t),pkS) = sidP then
  out(cP, enc(sign(sidP,kP),r,k11));
  (* end P1 *)

  (* begin FA *)
  !_i (
    in(cP,y);
    let x = dec(y,k11) in
    if x <> fail then
    if fst(x) = reqsign then
    out(cP, enc(<anssign, sign(<forwarded,snd(x)>,kP)>,r2(i),k11))
  ).

process PDIS =
  (* begin S0 *)
  in(cS, gP0);
  out(cS, g^bke11);
  (* end S0 *)
  (* begin S1 *)
  in(cS,garbage);
  let sidS0 = h(<<gP0,g^bke11>,k11>, hKey) in
  out(cS, <<pk(kS),g^bke11>,sign(sidS0, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP0^bke11),pk(kP)) = sidS0 then
      out(cS,ok);
  (* end S1 *)
  (* begin Pdis0 *)
  out(cP, g^a1);
  in(cP, gB);
  (* end Pdis0 *)
  out(cP,ok);
  (* begin Pdis1 *)
  in(cP,t);
  let sidP = h(<<g^a1,gB>,gB^a1>, hKey) in
  let pkS = fst(t) in
  if pkS = pk(kS) && checksign(snd(t),pkS) = sidP then
    out(cP, enc( <reqsign, sidP>,r3,k11));
    in(cP, signans);
    let y = dec(signans,k11) in
    if y <> fail then
    if fst(y) = anssign then
    Pok: out(cP, enc(snd(y),r4,gB^a1)).


process SDIS =
  (* begin SDIS0 *)
  in(cS, gP);
  out(cS, g^b1);
  (* end SDIS0 *)

  (* begin SDIS1 *)
  in(cS,garbage);
  let sidS = h(<<gP,g^b1>,gP^b1>, hKey) in
  out(cS, <<pk(kS),g^b1>,sign(sidS, kS)>);
  in(cS, encP );
  let x = dec(encP,gP^b1) in
  if checksign(x,pk(kP)) = <forwarded,sidS> then
    Sok : out(cS,ok).

system [fullSSH] K: (P1FA | SDIS | PDIS).

(* Now the process for the secrecy *)

process P1FADDH =
  in(cP,gB);
  out(cP,ok);
  (* begin P1 *)
  in(cP,t);
  let sidP = h(<<g^ake11,gB>,k11>, hKey) in
  let pkS = fst(t) in
  if pkS = pk(kS) && checksign(snd(t),pkS) = sidP then
  out(cP, enc(sign(sidP,kP),r,k11));
  (* end P1 *)

  (* begin FA *)
  !_i (
    in(cP,y);
    let x2= dec(y,k11) in
    if x2 <> fail then
    if fst(x2) = reqsign then
    out(cP, enc(<anssign, sign(<forwarded,snd(x2)>,kP)>,r2(i),k11))
  )

process PDISDDH =
  (* begin S0 *)
  in(cS, gP0);
  out(cS, g^bke11);
  (* end S0 *)
  (* begin S1 *)
  in(cS,garbage);
  let sidS0 = h(<<gP0,g^bke11>,k11>, hKey) in
  out(cS, <<pk(kS),g^bke11>,sign(sidS0, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP0^bke11),pk(kP)) = sidS0 then
  out(cS,ok);
  (* end S1 *)
  (* begin Pdis0 *)
  out(cP, g^a1);
  in(cP, gB);
  (* end Pdis0 *)
  if gB = g^b1 then
  out(cP,diff(g^a1^b1,g^c11))


process SDISDDH =
  (* begin SDIS0 *)
  in(cS, gP);
  out(cS, g^b1);
  (* end SDIS0 *)

  (* begin SDIS1 *)
  if gP = g^a1 then
  out(cP,diff(g^a1^b1,g^c11))

system [secret] K: (P1FADDH | SDISDDH | PDISDDH).


equiv [left,secret] [right,secret] secret.
Proof.
   ddh a1, b1, c11.
Qed.


(** And now the authentication process. *)

process P1FAauth =
  in(cP,gB);
  out(cP,ok);
  (* begin P1 *)
  in(cP,t);
  let sidPaF = h(<<g^ake11,gB>,k11>, hKey) in
  let pkSaF = fst(t) in
  if pkSaF = pk(kS) && checksign(snd(t),pkS) = sidPaF then
  out(cP, enc(sign(sidPaF,kP),r,k11));
  (* end P1 *)

  (* begin FA *)
  !_i (
    in(cP,y3);
    let x3 = dec(y3,k11) in
    if x3 <> fail then
    if fst(x3) = reqsign then
    out(cP, enc(<anssign, sign(<forwarded,snd(x3)>,kP)>,r2(i),k11))
  )

process PDISauth =
  (* begin S0 *)
  in(cS, gP1);
  out(cS, g^bke11);
  (* end S0 *)
  (* begin S1 *)
  in(cS,garbage);
  let sidS0a = h(<<gP1,g^bke11>,k11>, hKey) in
  out(cS, <<pk(kS),g^bke11>,sign(sidS0a, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP1^bke11),pk(kP)) = sidS0a then
  out(cS,ok);
  (* end S1 *)
  (* begin Pdis0 *)
  out(cP, g^a1);
  in(cP, gB);
  (* end Pdis0 *)
  out(cP,ok);
  (* begin Pdis1 *)

  in(cP,t);
  let sidPa = h(<<g^a1,gB>,gB^a1>, hKey) in
  let pkSa = fst(t) in
  if pkSa = pk(kS) && checksign(snd(t),pkSa) = sidPa then
  out(cP, enc( <reqsign, sidPa>,r3,k11));
  in(cP, signans);
  let ya = dec(signans,k11) in
  if ya <> fail then
  if fst(ya) = anssign then
  out(cP, enc(snd(ya),r4,gB^a1));
  in(cP,challenge);
  try find i such that
    gB = g^b(i) || gB = g^b1 || gB=g^bke1(i) || gB = g^bke11
  in out(cP,ok)
  else Pfail : out(cP,diff(ok,ko))


process SDISauth =
  (* begin SDIS0 *)
  in(cS, gP);
  out(cS, g^b1);
  (* end SDIS0 *)

  (* begin SDIS1 *)
  in(cS,garbage);
  let sidSa = h(<<gP,g^b1>,gP^b1>, hKey) in
  out(cS, <<pk(kS),g^b1>,sign(sidSa, kS)>);
  in(cS, encP );
  let x4 = dec(encP,gP^b1) in
  if checksign(x4,pk(kP)) = <forwarded,sidSa> then
    out(cS,ok);
    in(cS,challenge);
    try find i such that gP = g^a(i) || gP = g^a1 in
      out(cS,ok)
    else
      Sfail :  out(cS,diff(ok,ko))

system [auth] K: ( P1FAauth | SDISauth | PDISauth).


(* Based on a difference between the bitstring lengths, we can assume that it is
impossible to confuse a hash with the tag forwarded, and another hash. *)

axiom [auth] hashlengthnotpair : forall (m1,m2:message),
   <forwarded,h(m1,hKey)> <> h(m2, hKey)

(* The following axiom is a modelling trick. We need at some point to apply an
hypothesis that require to instantiate an index, but this index is not used. *)
axiom [auth] freshindex : exists (l:index), True

axiom [auth] signnottag :
  forall (m1,m2:message),
  fst(sign(m1,m2)) <> anssign &&
  fst(sign(m1,m2)) <> reqsign

axiom [auth] difftags :
  anssign <> forwarded &&
  forwarded <> reqsign && reqsign <> anssign.



goal [none, auth] P_charac :
  exec@PDIS5 => (cond@Pfail => False) .
Proof.
  expand exec@PDIS5.
  expand cond@PDIS5; expand cond@Pfail.
  substitute pkSa@PDIS5,pk(kS).
  euf Meq0.

  (* oracle case *)
  case H2.
  case H2.
  apply hashlengthnotpair to <<m,g^b(i)>,m1>, <<g^a1,input@PDIS4>,input@PDIS4^a1>.

  apply signnottag to sidPa@P2, kP.
  apply H0 to i1.
  left; right.
  by collision.

  (* honest case SDIS *)
  collision.
  apply freshindex.
  by apply H0 to l.

  apply freshindex.
  apply H0 to l.
  right.
  collision.
Qed.


(* This is the most complex case, as the received signature was not performed by PDis, but queried by PDis to FA. *)
goal [none, auth] S_charac :
   exec@Sok =>(cond@Sfail => False).
Proof.
  expand exec@Sok; expand cond@Sok; expand cond@Sfail.

  euf H1.

(* oracle clase *)

  case H2.
  case H3.
(* sub case with wrong tag *)
  apply H0 to i.
  assert h(<<input@SDIS,g^b1>,input@SDIS^b1>,hKey) = h(<<g^a(i),m>,m1>,hKey). 
  by collision.

  by apply hashlengthnotpair to <<input@SDIS,g^b1>,input@SDIS^b1>, <<g^ake1(i1),m2>,m3>.

(* else, it comes from P2, and is not well tagged *)

  by apply hashlengthnotpair to <<input@SDIS,g^b1>,input@SDIS^b1>, <<g^ake11,input@P1>,k11>.

(* Honest case of signature produced by Fa.
   We need to prove that the sign req received by FA comes from PDIS. *)

  executable pred(Sok).

  depends SDIS, Sok.
  apply H4 to P3(i).
  expand exec@P3(i).
  expand cond@P3(i).

(* We have that x3 is a message encrypted with the secret key, we use the intctxt of encryption *)
  intctxt D.

(* Ill-tagged cases *)
  apply signnottag to sidPaF@P2,kP.
  apply difftags.

(* Honest case *)
  assert PDIS5 <= Sok.
  case H6.
  apply H4 to PDIS5.
  expand exec@PDIS5.
  expand cond@PDIS5. 
  apply H1 to i.
  right.
  collision.
Qed.

(* The equivalence for authentication is obtained by using the unreachability
   proofs over the two actions. The rest of the protocol can be handled through
   some simple enriching of the induction hypothesis, and then dup applications. *)

equiv [left, auth] [right, auth] auth.
Proof.
  enrich a1; enrich b1; enrich seq(i-> b(i)); enrich seq(i-> a(i)); enrich kP; enrich kS;
  enrich ake11; enrich bke11; enrich seq(i-> bke1(i)); enrich seq(i-> ake1(i)); enrich k11; enrich hKey; enrich r; enrich seq(i->r2(i)); enrich r3; enrich r4; enrich r5.

  induction t.

  (* P1 *)
  expandall; fa 17.
  (* P2 *)
  expandall; fa 17.
 (* P3 *)
  expandall; fa 17.
  expand seq(i -> r2(i)),i.
 (* A *)
  expandall; fa 17.
  (* A1 *)
  expandall; fa 17.
  (* A 2 *)
  expandall; fa 17.
  (* SDIS *)
  expandall; fa 17.
  (* SDIS1 *)
  expandall; fa 17.
  (* Sok *)
  expandall; fa 17.
  (* SDISauth3 *)
  expandall; fa 17.
  expand seq(i -> a(i)),i.
  (* Sfail *)
  expand frame@Sfail.

  equivalent exec@Sfail, false.
  apply S_charac.
  depends Sok, Sfail.
  executable Sfail.
  apply H1 to Sok.
  expand exec@Sfail.

  fa 17. fa 18. noif 18.
  (* A3 *)
  expandall; fa 17.
  (* PDIS *)
  expandall; fa 17.
  (* PDIS1 *)
  expandall; fa 17.
  (* PDSI2 *)
  expandall; fa 17.
  (* PDIS3 *)
  expandall; fa 17.
  (* PDIS4 *)
  expandall; fa 17.
  (* PDIS5 *)
  expandall; fa 17.
  (* Pok *)
  expandall; fa 17.
  (* PDISauth7 *)
  expandall; fa 17.
  expand seq(i -> b(i)),i. expand seq(i -> bke1(i)),i.
  (* Pfail *)
  expand frame@Pfail.

  equivalent exec@Pfail, false.
  apply P_charac.
  depends PDIS5, Pfail.
  executable Pfail.
  by apply H to PDIS5.
  expand exec@Pfail.

  by fa 17. fa 18. noif 18.
 (* A4 *)
  by expandall; fa 17.
 (* A5 *)
  by expandall; fa 17.
 (* A6 *)
  by expandall; fa 17.
  (* A7 *)
  by expandall; fa 17.
Qed.
