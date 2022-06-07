(*******************************************************************************
MW

[E] David Molnar and David A. Wagner. Privacy and security in library
RFID: issues, practices, and architectures. In Vijayalakshmi Atluri,
Birgit Pfitzmann, and Patrick D. McDaniel, editors, Proceedings of the
11th ACM Conference on Computer and Communications Security, CCS
2004, Washington, DC, USA, October 25-29, 2004, pages 210–219.
ACM, 2004.

R --> T: nr
T --> R: nt, id + H(<c0, nr, nt>,k)
R --> T: id + H(<c1, nr, nt>,k)

This is a "light" model without the last check of T.
*******************************************************************************)

set postQuantumSound=true.

hash H

abstract id : index -> message
abstract id': index -> index -> message

name dummy : message

name key : index -> message
name key': index -> index -> message

abstract error : message
abstract tag0 : message
abstract tag1 : message

channel c.

process tag(i:index, t:index)=
  in(c,x);
  new nt;
  out(c,<nt,xor(diff(id(i),id'(i,t)),H(<tag0,<x,nt>>,diff(key(i),key'(i,t))))>).

process reader =
  new nr;
  out(c,nr);
  in(c,m);
  if exists (i,t:index),
     xor(diff(id(i),id'(i,t)),snd(m)) =
     H(<tag0,<nr,fst(m)>>,diff(key(i),key'(i,t)))
  then
    out(c, try find i,t such that
             xor(diff(id(i),id'(i,t)),snd(m)) = H(<tag0,<nr,fst(m)>>,diff(key(i),key'(i,t))) in
           xor(diff(id(i),id'(i,t)),H(<tag1,<nr,fst(m)>>,diff(key(i),key'(i,t)))))
  else
    out(c,error).

system (!_r R: reader | !_i !_t T: tag(i,t)).

include Basic.

axiom len_id (i:index)   : len(id(i))    = len(dummy)
axiom len_id' (i,t:index): len(id'(i,t)) = len(dummy)

axiom tags_neq : tag0 <> tag1.

(* Well-authentication for R1 and R2's condition. *)
goal wa_R1_R2 (tau:timestamp,r:index):
  (exists (i,t:index),
   xor(diff(id(i),id'(i,t)),snd(input@tau)) =
   H(<tag0,<nr(r),fst(input@tau)>>,diff(key(i),key'(i,t))))
  =
  (exists (i,t:index),
   T(i,t) < tau &&
   fst(output@T(i,t)) = fst(input@tau) &&
   snd(output@T(i,t)) = snd(input@tau) &&
   R(r) < T(i,t) &&
   output@R(r) = input@T(i,t)).
Proof.
  rewrite eq_iff; split.

  (* Cond => WA *)
  + intro [i t Meq].
    project.
    (* left *)
    - euf Meq => _ _ _.
      * by use tags_neq.
      * exists i,t0; simpl.
        assert (input@T(i,t0) = nr(r)) as F by auto.
        fresh F => [_|_|_] //.
        ** by depends R(r), R1(r).
        ** by depends R(r), R2(r).
    (* right *)
    - euf Meq => _ _ _.
      * by use tags_neq.
      * exists i,t; simpl.
        assert (input@T(i,t) = nr(r)) as F by auto.
        fresh F => [_|_|_] //.
        ** by depends R(r),R1(r).
        ** by depends R(r),R2(r).

  (* WA => Cond *)
  + by intro [i t _]; expand output; exists i,t.
Qed.

(** Same as before, but more precise wrt i, for the left process.
    There has to remain an existential quantification on t,
    because it is not involved in the condition. *)
goal [default/left] wa_R1_left (i,r:index):
  (xor(id(i),snd(input@R1(r))) =
   H(<tag0,<nr(r),fst(input@R1(r))>>,key(i)))
  =
  (exists t:index,
   T(i,t) < R1(r) &&
   fst(output@T(i,t)) = fst(input@R1(r)) &&
   snd(output@T(i,t)) = snd(input@R1(r)) &&
   R(r) < T(i,t) &&
   output@R(r) = input@T(i,t)).
Proof.
  rewrite eq_iff; split; 2: by intro [_ _]; expand output.
  intro Meq; euf Meq => _ _ _; 1: auto.
  exists t; simpl.
  assert input@T(i,t) = nr(r) as F by auto.
  fresh F => C.
  by case C; 3:depends R(r), R2(r).
Qed.

(** Precise version of wa_R1 on the right: no more existentials. *)
goal [default/right] wa_R1_right (i,t,r:index):
  (xor(id'(i,t),snd(input@R1(r))) =
   H(<tag0,<nr(r),fst(input@R1(r))>>,key'(i,t)))
  =
  (T(i,t) < R1(r) &&
   fst(output@T(i,t)) = fst(input@R1(r)) &&
   snd(output@T(i,t)) = snd(input@R1(r)) &&
   R(r) < T(i,t) &&
   output@R(r) = input@T(i,t)).
Proof.
  rewrite eq_iff; split; 2: by intro [_ _]; expand output.
  intro Meq; euf Meq => _ _ _; 1: auto.
  assert input@T(i,t) = nr(r) as F by auto.
  fresh F => C.
  by case C; 3:depends R(r), R2(r).
Qed.

(** Equality used to rewrite the try-find in R1
    so that its condition can be discharged using fadup:
    change condition to honest transcript formula,
    and insert exec conjunct. *)
goal wa_R1_tryfind (r:index) : happens(R1(r)) =>
  (if exec@pred(R1(r)) && cond@R1(r) then
   try find i,t such that
     xor(diff(id(i),id'(i,t)),snd(input@R1(r))) =
     H(<tag0,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t))) in
   xor(diff(id(i),id'(i,t)),H(<tag1,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t)))))
  =
  (if exec@pred(R1(r)) && cond@R1(r) then
   try find i,t such that
     exec@pred(R1(r)) &&
     (T(i,t) < R1(r) &&
      fst(output@T(i,t)) = fst(input@R1(r)) &&
      snd(output@T(i,t)) = snd(input@R1(r)) &&
      R(r) < T(i,t) &&
      output@R(r) = input@T(i,t))
   in
   xor(diff(id(i),id'(i,t)),H(<tag1,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t))))).
Proof.
  intro Hap.
  case exec@pred(R1(r)) => // Hexec.
  case cond@R1(r) => // Hcond.
  simpl.
  (* Projection must be performed before fa
     so that useless indices are handled smartly. *)
  project.
  + fa => // Heq.
    (* Timestamp t introduced by fa is unused. *)
    by rewrite wa_R1_left in Heq.
  + fa => // Heq.
    by rewrite wa_R1_right in Heq.
Qed.

equiv unlinkability.
Proof.
  induction t; try auto.

  (* Case R *)
  + expand frame, exec, cond, output.
    fa !<_,_>, if _ then _.
    fresh 1.
    rewrite if_true //.
    by (repeat split => r0 _;
        try (depends R(r0), R1(r0) by auto);
        try (depends R(r0), R2(r0) by auto)).

  (* Case R1 *)
  + expand frame, exec, output.
    fa !<_,_>.

    rewrite wa_R1_tryfind; 1:auto.
    rewrite /cond wa_R1_R2.
    fa 2; fadup 1.
    fa 1; fadup 1.

    prf 1.
    rewrite if_true.
    by use tags_neq; project.
    xor 1,n_PRF.
    rewrite if_true.
    by use len_id with i; use len_id' with i,t; namelength n_PRF, dummy.
    by fresh 1.

  (* Case R2 *)
  + expand frame, exec, cond, output.
    fa !<_,_>.
    rewrite wa_R1_R2.
    by fadup 1.

  (* Case T *)
  + expand frame, exec, cond, output.
    fa !<_,_>, if _ then _, <_,_>.

    prf 2. (* we use PRF under XOR to be able to use XOR tactic later on *)
    rewrite if_true. {
      use tags_neq.
      simpl; project;
      by (repeat split => > _;
          repeat split => > _ [_ [_ Meq]];
          fresh Meq).
    }
    fresh 1.
    rewrite if_true //.
    xor 1, n_PRF.
    rewrite if_true.
    by use len_id with i; use len_id' with i,t; namelength n_PRF,dummy.
    by fresh 1.
Qed.
