(**# BASIC HASH

The Basic Hash protocol as described in [A] is an RFID protocol involving:

* a tag associated to a secret key;
* generic readers having access to a database containing all these keys.

The protocol is as follows:

T --> R : <nT, h(nT,key)>
R --> T : ok

In this file, we prove two security properties for this protocol.

* We first prove an **authentication** property for the reader
(both for the then and the else branches).
* We then prove **unlinkability**, _i.e._ equivalence between a **real** system
(where each tag can play multiple sessions) and an **ideal** system
(where each tag plays only one session).

[A] Mayla Brusò, Kostas Chatzikokolakis, and Jerry den Hartog. Formal
Verification of Privacy for RFID Systems. pages 75–88, July 2010.

*******************************************************************************)
(**
When this option is set to `true`, Squirrel checks whether each tactic invoked
for the proof is also sound for quantum attackers.
*)
set postQuantumSound=true.

(**
We start by declaring the function symbol `h` for the hash function,
as well as two public constants `ok` and `ko` (used by the reader).
*)

hash h

abstract ok : message
abstract ko : message.

(**
In order to model the real system and the ideal system, we will use two
different name symbols for the tags' secret keys.
The symbol `key` has index arity 1 and will be used in the real system, while
the symbol `key'` has index arity 2 and will be used in the ideal system
so that each new session of a tag uses a new key.
*)

name key  : index -> message
name key' : index -> index -> message
(**
Finally, we declare the channels used by the protocol.
*)

channel cT
channel cR.

(**
The tag's role is modelled by the following process, indexed by `i` (for
the identity of the tag) and by `k` (for the session of a given identity).
The tag starts by generating a fresh random name `nT`, then outputs a message
built using `key(i)` in the real system and `key'(i,k)` in the ideal system.
*)

process tag(i:index,k:index) =
  new nT;
  out(cT, <nT, h(nT,diff(key(i),key'(i,k)))>).

(**
The reader's role is modelled by the following process. Since readers are
generic, the process is indexed only by `j` (for the session).
The reader starts by inputting a message `x` before checking whether this
message corresponds to a legitimate output performed by a tag.
On the left side (the real system), the reader looks up for a key `key(i)`
in the database (the one corresponding to the tag of identity `i`).
On the right side (the ideal system), the reader looks up for a key `key(i,k)`
in the database (the one used by the tag of identity `i` at session `k`).
*)

process reader(j:index) =
  in(cT,x);
  if exists (i,k:index), snd(x) = h(fst(x),diff(key(i),key'(i,k))) then
    out(cR,ok)
  else
    out(cR,ko).

(**
The system is finally defined by putting an unbounded number of tag's and
reader's processes in parallel.
This system is automatically translated to a set of actions:

* the initial action (`init`);
* one action for the tag (`T`);
* two actions for the reader, corresponding to the two branches of the
conditional (respectively `R` and `R1`).
*)

system ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

(** Include basic standard library, important helper lemmas and
    setting proof mode to autoIntro=false. *)
include Basic.

(**
This first authentication property is a reachability property expressed by a first-order
logic formula.
This property states that whenever a reader accepts a message (_i.e._ the
condition of the action `R(j)` evaluates to `true`), then there exists
an action `T(i,k)` that has been executed before the reader, and such that the input
of the reader corresonds to the output of this tag (and conversely).
Note that we express this correspondence on each projection. Indeed, for some
implementations of the pairing primitive, the equality of projections does not imply
the equality of pairs.
*)

goal wa_R :
  forall (j:index),
    happens(R(j)) =>
    (cond@R(j) =
      (exists (i,k:index), T(i,k) < R(j) &&
       fst(output@T(i,k)) = fst(input@R(j)) &&
       snd(output@T(i,k)) = snd(input@R(j)))).
(**
The high-level idea of the proof is to use the EUF cryptographic axiom:
only the tag `T(i,k)` can forge `h(nT(i,k),key(i))` because the secret key
is not known by the attacker.
Therefore, any message accepted by the reader must come from a tag that has
played before.
The converse implication is trivial because any honest tag's output is
accepted by the reader.
*)
Proof.
  (** We start by introducing the variable `j` and the hypothesis
  `happens(R(j))`, before unfolding the definiton of the `cond` macro,
  which corresponds to an existential quantification.*)
  intro j Hap.
  expand cond.
  (** We have to prove two implications (`<=>`): we thus split the proof
  in two parts. We now have two different goals to prove.*)
  rewrite eq_iff; split => [i k Meq].
  (** For the first implication (=>), we actually prove it separately for the
  real system (left) and the ideal system (right).*)
  project.
  (** The proof is very similar on both sides and relies on the `euf` tactic.
  Applying the `euf` tactic on the `Meq` hypothesis generates a new hypothesis
  stating that `fst(input@R(j))` must be equal to some message that has
  already been hashed before.nn
  The only possibility is that this hash comes from the output of a tag that
  has played before (thus the new hypothesis on timestamps).*)
  (* LEFT *) euf Meq => *. by exists i,k0.
  (* RIGHT *) euf Meq => *. by exists i,k.
  (** For the second implication (<=), the conclusion of the goal can directly
  be obtained from the hypotheses.*)
  by exists i,k.
Qed.

(**
This second authentication property is the counterpart of the previous one,
but for the else branch of the reader.
This property states that whenever a reader **rejects** a message (_i.e._ the
condition of the action `R1(j)` evaluates to `true`), then there does **not**
exist an action `T(i,k)` that was executed before the reader, and such that the
input of the reader corresonds to the output of this tag (and conversely).
*)

goal wa_R1 :
  forall (j:index),
    happens(R1(j)) =>
    cond@R1(j) =
    (not(exists (i,k:index), T(i,k) < R1(j) &&
      fst(output@T(i,k)) = fst(input@R1(j)) &&
      snd(output@T(i,k)) = snd(input@R1(j)))).
Proof.
  intro *.
  rewrite /cond eq_not eq_iff; split => [i k Meq].

  (** The first implication (=>) relies on the EUF assumption and is also
  proved by contradiction. *)
  project.
  (* LEFT  *) euf Meq => *. by exists i,k0.
  (* RIGHT *) euf Meq => *. by exists i,k.

  (** The second implication (<=) is trivial. *)
  by exists i,k.
Qed.

(**
We now prove an equivalence property expressing unlinkability of the protocol.
This property is expressed by the logic formula `forall t:timestamp, frame@t`
where `frame@t` is actually a bi-frame. We will have to prove that the left
projection of `frame@t` (_i.e._ the real system) is indistinguishable from the
right projection of `frame@t` (_i.e._ the ideal system).
*)

equiv unlinkability.
(**
The high-level idea of the proof is as follows:

* if `t` corresponds to a reader's action, we show that the outcome of the
conditional is the same on both sides and that this outcome only depends on
information already available to the attacker;
* if `t` corresponds to a tag's action, we show that the new message added
in the frame (_i.e._ the tag's output) does not give any information to the
attacker to distinguish the real system from the ideal one since hashes can
intuitively be seen as fresh names thanks to the PRF cryptographic axiom.
*)
Proof.
  (** The proof is done by induction over the timestamp `t`.
  The `induction` tactic also automatically introduces a case analysis over
  all the possible values for `t`.
  The first case, where `t = init`, is trivial.
  The other cases correspond to the 3 different actions of the protocol. *)
  induction t; 1: auto.

  (** Case where t = R(j).
  We start by expanding the macros and splitting the pairs. *)
  expand frame. fa 0. fa 1.
  expand exec, output.
  (** Using the authentication goal `wa_R` previously proved, we replace the
  formula `cond@R(j)` by an equivalent formula expressing the fact that a tag
  `T(i,k)` has played before and that the output of this tag is the message
  inputted by the reader. *)
  rewrite (wa_R j H).
  (** We are now able to remove this formula from the frame because the attacker
  is able to compute it using information obtained in the past. Indeed, each
  element of this formula is already available in `frame@pred(R(j))`.
  This is done by the `fadup` tactic. *)
  by fadup 1.

  (** Case where t = R1(j).
  This case is similar to the previous one. *)
  expand frame. fa 0. fa 1.
  expand exec, output.
  rewrite (wa_R1 j H).
  by fadup 1.

  (** Case where t = T(i,k).
  We start by expanding the macros and splitting the pairs. *)
  expand frame, exec, cond, output.
  fa 0; fa 1; fa 1; fa 1.
  (** We now apply the `prf` tactic, in order to replace the hash by a fresh
  name. The tactic actually replaces the hash by a conditional term in which
  the then branch is the fresh name.
  The goal is now to prove that this condition always evaluate to `true`. *)
  prf 2.
  yesif 2.
  split; 1: true.
  (** Several conjuncts must now be proved, the same tactic can be
      used on all of them. Here are representative cases:

      - In one case, `nT(i,k)` cannot occur in `input@R(j)`
        because `R(j) < T(i,k)`.
      - In another case, `nT(i,k) = nT(i0,k0)` implies that `i=i0` and `k=k0`,
        contradicting `T(i0,k0)<T(i,k)`.

      In both cases, the reasoning is performed by the fresh tactic on the
      message equality hypothesis `Meq` whose negation must initially be
      proved.
      To be able to use (split and) fresh, we first project the goal into
      into one goal for the left projection and one goal for the right
      projection of the initial bi-system. *)
  project; repeat split; intro *; by fresh Meq.

  (** We have now replaced the hash by a fresh name occurring nowhere else,
  so we can remove it using the `fresh` tactic. *)
  fresh 2.
  (** We can also remove the name `nT(i,k)`, and conclude by induction
  hypothesis. *)
  fresh 1. by yesif 1.
Qed.
