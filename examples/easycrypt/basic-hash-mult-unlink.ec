(* Simple modeling of the Basic Hash protocol, multiple tags. *)
require import AllCore Int List FSet SmtMap IntDiv StdBigop Distr DBool Mu_mem.
(*---*) import Bigint Bigreal BRA BIA.
require FelTactic.

(* Key space *)
type key.

(* Full, lossless and uniform distribution over keys. *)
op dkey: { key distr |     is_lossless dkey
                        /\ is_full dkey
                        /\ is_uniform dkey } as dkey_llfuuni.

(* Ptxt space *)
type ptxt.

(* Lossless and uniform distribution over ptxts (not full). *)
op dnonce: { ptxt distr |    is_lossless dnonce
                          /\ is_uniform dnonce } as dnonce_lluni.
lemma dnonce_ll (i : int) : is_lossless dnonce by smt (dnonce_lluni).
lemma dnonce_uni (i : int) : is_uniform dnonce by smt (dnonce_lluni).

op nonce_witness : ptxt.        (* exemple of a nonce in [dnonce] domain. *)
axiom maxu_dnonce x: mu1 dnonce x <= mu1 dnonce nonce_witness.

hint exact random : dnonce_ll.

(*-----------------------------------------------------------------------*)
(* multiple PRF *)
op F : key -> ptxt -> ptxt.

module type PRFs = {
  proc init (n : int) : unit
  proc f(i : int, x : ptxt) : ptxt
  proc check(i : int, x : ptxt, s : ptxt) : bool
}.

module type PRFs_Oracles = {
  include PRFs[-init]
}.

module PRFs = {
  var ks : key list
  
  proc init(n : int) : unit = {
    var i, k;
    i <- 0;
    while (i < n){
     k <$ dkey;
     ks <- k :: ks;
    } 
  }
  
  proc f(i : int, x : ptxt) : ptxt = {
    var k;
    i <- if (size ks <= i) then 0 else i;
    k <- nth witness ks i;
    return F k x;
  }

  proc check(i : int, x : ptxt, s : ptxt) = {
    var k;
    i <- if (size ks <= i) then 0 else i;
    k <- nth witness ks i;
    return (F k x = s);
  }
}.

(* Unforgeable multiple RF *)
(* We assume that: 
   i) the hash functions are indistinguishable from a lossless and uniform
   distributions over ptxts (not full).
   ii) the hash functions are unforgeable.
   
   ii) is a consequence of i) whenever the hash function image set is large. *)
op drf (i : int) : ptxt distr.
axiom drf_lluni (i : int) : is_lossless (drf i) /\ is_uniform (drf i).
lemma drf_ll (i : int) : is_lossless (drf i) by smt (drf_lluni).
lemma drf_uni (i : int) : is_uniform (drf i) by smt (drf_lluni).

(* The PRFs are all i.i.d. *)
axiom drf_iid (i j : int) : forall (r : ptxt), mu1 (drf i) r = mu1 (drf j) r.

lemma drf_sup (i j : int) : forall (r : ptxt), r \in drf i <=> r \in drf j 
by smt (drf_iid).

hint exact random : drf_iid.
hint exact random : drf_sup.
hint exact random : drf_ll.

module EUF_RF = {
  var n : int
  var m : (int * ptxt, ptxt) fmap
  
  proc init(i : int) : unit = {
    n <- i;
    m <- empty;
  }
  
  proc f(i : int, x : ptxt) : ptxt = {
    var r : ptxt;
    i <- if (n <= i) then 0 else i;

    if ((i,x) \notin m) {
      r <$ drf i;
      m.[(i,x)] <- r;
    }
    
    return oget m.[(i,x)];
  }

  proc check(i : int, x : ptxt, s : ptxt) = {
    i <- if (n <= i) then 0 else i;
    return ((i,x) \in m && oget m.[(i,x)] = s);
  }
}.


(*-----------------------------------------------------------------------*)
(* Basic Hash protocol, multiple tags (multiple sessions) and one reader. *)

op n_tag : int.             (* number of tags *)
axiom n_tag_p : 0 < n_tag.  (* We have at least one tag. *)

op n_session : int.                 (* number of sessions per tag *)
axiom n_session_p : 0 < n_session.  (* We have at least one session. *)

(* Without initialization *)
module Multiple0 (H : PRFs_Oracles) = {
  var s_cpt : (int, int) fmap   (* Map a tag number to its session number. *)

  (* Each tag runs at most n_session. *)
  proc tag (i : int) : (ptxt * ptxt) option = {
    var n, h, r, s_n;
    i <- if (n_tag <= i) then 0 else i;
    r <- None;

    if (i \in s_cpt) {
      s_n <- oget s_cpt.[i];
      if (s_n < n_session) {
        n <$ dnonce;
        h <@ H.f(i,n);
        r <- Some (n, h);
        s_cpt.[i] <- s_n + 1;
      } 
    }
    return r;
  }    
  
  proc reader (n h : ptxt) : bool = {    
    var r, b, i;
    b <- false;
    i <- 0;
    while (i < n_tag) {
      r <- H.check(i, n, h);
      b <- b || r;
      i <- i + 1;
    }
    return b;
  } 
}.

(* With initialization *)
module Multiple (H : PRFs) = {
  module BH0 = Multiple0(H)
  include BH0

  proc init () : unit = { 
    var i;
    H.init(n_tag); 
    
    Multiple0.s_cpt <- empty;
    i <- 0;
    while (i < n_tag) {
      Multiple0.s_cpt.[i] <- 0;
      i <- i + 1;
    }
  }
}.

(*-----------------------------------------------------------------------*)
(* Basic Hash protocol, multiple tags (single session) and one reader. *)

(* Without initialization *)
module Single0 (H : PRFs_Oracles) = {

  (* Each tag runs at most n_session. *)
  proc tag (i : int) : (ptxt * ptxt) option = {
    var n, h, r, s_n;
    i <- if (n_tag <= i) then 0 else i;
    r <- None;

    if (i \in Multiple0.s_cpt) {
      s_n <- oget Multiple0.s_cpt.[i];
      if (s_n < n_session) {
        n <$ dnonce;
        (* each hash function is used at most once *)
        h <@ H.f(i * n_session + s_n,n); 
        r <- Some (n, h);
        Multiple0.s_cpt.[i] <- s_n + 1;
      } 
    }
    return r;
  }    
  
  proc reader (n h : ptxt) : bool = {    
    var r, b0, b, i, j;
    b <- false;
    i <- 0;
    j <- 0;
    b0 <- false;
    while (i < n_tag) {
      j <- 0;
      b0 <- false;
      while (j < n_session) {
        r <- H.check(i * n_session + j, n, h);
        b0 <- b0 || r;
        j <- j + 1;
      }
      b <- b || b0;
      i <- i + 1;
    }
    return b;
  } 
}.

(* With initialization *)
module Single (H : PRFs) = {
  module BH0 = Single0(H)
  include BH0

  proc init () : unit = { 
    var i;
    H.init(n_tag * n_session); 
    
    Multiple0.s_cpt <- empty;
    i <- 0;
    while (i < n_tag) {
      Multiple0.s_cpt.[i] <- 0;
      i <- i + 1;
    }
  }
}.


(*-----------------------------------------------------------------------*)
(* Distinguisher against n_tag PRFs. *)
module type Distinguisher (F : PRFs_Oracles) = {
  proc distinguish(): bool
}.

(* Indistinguishability game for unforgeable PRFs, [n_tag] keys. *)
module EUF_PRF_IND (F : PRFs) (D : Distinguisher) = {
  proc main(): bool = {
    var b;

    F.init(n_tag);
    b <@ D(F).distinguish();
    return b;
  }
}.

(* Indistinguishability game for unforgeable PRFs, [n_tag * n_session] keys. *)
module EUF_PRF_INDb (F : PRFs) (D : Distinguisher) = {
  proc main(): bool = {
    var b;

    F.init(n_tag * n_session);
    b <@ D(F).distinguish();
    return b;
  }
}.


(*-----------------------------------------------------------------------*)
module type BasicHashT = {
  proc init () : unit
  proc tag (_ : int) : (ptxt * ptxt) option
  proc reader (_: ptxt * ptxt) : bool
}.

module type BasicHashT0 = {
  include BasicHashT[-init]
}.

module type BasicHashF (H : PRFs) = {
  include BasicHashT
}.

module type BasicHashF0 (H : PRFs_Oracles) = {
  include BasicHashT0
}.

(*-----------------------------------------------------------------------*)
(* Adversary against the Basic Hash protocol unlinkability *)
module type Adv (BH : BasicHashT0) = {
  proc a () : bool
}.


(* Basic Hash protocol unlinkability game *)
module Unlink (Adv : Adv) (BH : BasicHashF) (H : PRFs) = {
  module BH = BH(H)
  module Adv = Adv (BH)

  proc main () = {
    var b : bool;
    BH.init ();
    b <- Adv.a();
    return b;
  }
}.

(*-----------------------------------------------------------------------*)
(* The PRF/RF distinguisher. *)
module D (A : Adv) (BH : BasicHashF0) (F : PRFs_Oracles) = {
  module BH = BH(F)
  module A = A (BH)
  
  proc distinguish () = {
    var i, b;
    Multiple0.s_cpt <- empty;
    i <- 0;
    while (i < n_tag) {
      Multiple0.s_cpt.[i] <- 0;
      i <- i + 1;
    }

    b <@ A.a();
    return b; 
  } 
}.


(*-----------------------------------------------------------------------*)
(* Game-hope, PRF to RF for the multiple session protocol.  *)
lemma eq_mult_RF &m (A <: Adv {Multiple0, EUF_RF}) : 
    Pr[Unlink(A, Multiple, EUF_RF).main() @ &m : res] =
    Pr[EUF_PRF_IND(EUF_RF, D(A, Multiple0)).main() @ &m : res]
by byequiv; auto; proc; inline *; wp; sim; auto. 

lemma eq_mult_PRF &m (A <: Adv {Multiple0, PRFs}) : 
    Pr[Unlink(A, Multiple, PRFs).main() @ &m : res] =
    Pr[EUF_PRF_IND(PRFs, D(A, Multiple0)).main() @ &m : res]
by byequiv; auto; proc; inline *; wp; sim; auto. 

(* Idem with the single session protocol. *)
lemma eq_single_RF &m (A <: Adv {Multiple0, EUF_RF}) : 
    Pr[Unlink(A, Single, EUF_RF).main() @ &m : res] =
    Pr[EUF_PRF_INDb(EUF_RF, D(A, Single0)).main() @ &m : res]
by byequiv; auto; proc; inline *; wp; sim.

lemma eq_single_PRF &m (A <: Adv {Multiple0, PRFs}) : 
    Pr[Unlink(A, Single, PRFs).main() @ &m : res] =
    Pr[EUF_PRF_INDb(PRFs, D(A, Single0)).main() @ &m : res]
by byequiv; auto; proc; inline *; wp; sim.


(*-----------------------------------------------------------------------*)
(* Second game-hope, where we bound the collision probability for all
   the nonces sample by each tag.  *)

(* The EUF_RF module, where we set a boolean bad to true if we hash twice the 
   same value. Since we only hash nonces, this is equivalent to setting bad to
   true if a tag has a collision between two nonces it samples.
   In case of collision, a message may have several hashes, which we store. *)
search (oget _ = _).

module RF_bad = {
  var bad : bool
  var m : (int * ptxt, ptxt list) fmap

  proc init(i : int) : unit = {
    EUF_RF.init(i);
    bad <- false;
    m <- empty;
  }
  
  proc f(i : int, x : ptxt) : ptxt = {
    var r : ptxt;
    i <- if (EUF_RF.n <= i) then 0 else i;

    (* If we already hashed [x] under key [i], we set bad to true. *)
    bad <- bad || (i,x) \in m;

    r <$ drf i;
    m.[(i,x)] <- r :: odflt [] m.[(i,x)];
    
    return r;
  }

  proc check(i : int, x : ptxt, s : ptxt) = {
    i <- if (EUF_RF.n <= i) then 0 else i;
    return ((i,x) \in m && s \in oget m.[(i,x)]);
  }
}.

lemma map_support ['a, 'b] (m : ('a,'b) fmap) (m' : ('a,'b list) fmap) :
    (forall x, omap (transpose (::) []) m.[x] = m'.[x]) =>
    forall x, x \in m <=> x \in m'
by move => H x; rewrite 2! domE; smt (). 

lemma coll_multiple &m (A <: Adv {EUF_RF, RF_bad, Multiple0}) : 
    (forall (BH <: BasicHashT0{A}),
      islossless BH.tag => islossless BH.reader => islossless A(BH).a) =>
    Pr[Unlink(A, Multiple, EUF_RF).main() @ &m : res] <=
    Pr[Unlink(A, Multiple, RF_bad).main() @ &m : res] +
    Pr[Unlink(A, Multiple, RF_bad).main() @ &m : RF_bad.bad].
proof.
  move => Hll; byequiv => //.
  proc.
  call(_: RF_bad.bad, 
    ={glob Single0, EUF_RF.n} /\
    (* (forall x i, (x,i) \in EUF_RF.m{1} <=> (x,i) \in RF_bad.m{2}) /\ *)
    (forall (x), omap (fun x => [x]) (EUF_RF.m.[(x)]{1}) = RF_bad.m.[(x)]{2})).
  + proc; inline *; sp; if; 1,3 : by auto.
    sp; if; 1, 3 : by auto. 
    seq 4 4 : (#pre /\ ={n, i0, x}); 1 : by auto => /#.
    wp; if {1}; 1 : by auto => />; smt(get_setE). 
    by auto; smt (map_support).
  + by move => &2 Hb; islossless.
  + move => &2. proc; inline *; auto; sp; if; sp; auto. 
    by if; auto; smt (drf_ll dnonce_ll). 
  + proc; inline *. while (#pre /\ ={b,i}); auto => />. 
    move => &1 &2 Hbad Hind Hle />. 
    pose j := if EUF_RF.n{2} <= i{2} then 0 else i{2}.
    rewrite -(Hind (j,n{2})). 
    case ((j, n{2}) \in EUF_RF.m{1}); 
    case ((j, n{2}) \in RF_bad.m{2}) 
    => Hin1 Hin2 //=; 1 : by rewrite get_some => //=; smt ().
    by have Hsup := (map_support (EUF_RF.m{1}) (RF_bad.m{2}) Hind); smt ().
    by have Hsup := (map_support (EUF_RF.m{1}) (RF_bad.m{2}) Hind); smt ().
  + move => &2 Hb; islossless. 
    while true (n_tag - i); auto; 2 : by smt ().
    conseq (:true); 1 : by smt (). 
    by islossless. 
  + move => _; proc; conseq />.
    while true (n_tag - i); auto; 2 : by smt ().
    conseq (:true); 1 : by smt (). 
    by islossless. 
  + by inline *; sp => />; while (={i, Multiple0.s_cpt}); auto; smt (empty_valE).
qed.

lemma coll_single &m (A <: Adv {EUF_RF, RF_bad, Multiple0}) : 
    (forall (BH <: BasicHashT0{A}),
      islossless BH.tag => islossless BH.reader => islossless A(BH).a) =>
    Pr[Unlink(A, Single, EUF_RF).main() @ &m : res] <=
    Pr[Unlink(A, Single, RF_bad).main() @ &m : res] +
    Pr[Unlink(A, Single, RF_bad).main() @ &m : RF_bad.bad].
proof.
  move => Hll; byequiv => //.
  proc.
  call(_: RF_bad.bad, 
    ={glob Single0, EUF_RF.n} /\
    (* (forall x i, (x,i) \in EUF_RF.m{1} <=> (x,i) \in RF_bad.m{2}) /\ *)
    (forall (x), omap (fun x => [x]) (EUF_RF.m.[(x)]{1}) = RF_bad.m.[(x)]{2})).
  + proc; inline *; sp; if; 1,3 : by auto. 
    sp; if; 1, 3 : by auto. 
    seq 4 4 : (#pre /\ ={n, i0, x}); 1 : by auto => /> /#.
    wp; if {1}; 1 : by auto => />; smt(get_setE). 
    by auto; smt (map_support).
  + by move => &2 Hb; islossless.
  + move => &2. proc; inline *; auto; sp; if; sp; auto. 
    by if; auto; smt (drf_ll dnonce_ll). 
  + proc; inline *; while (#pre /\ ={b,b0,j,i}); auto => />. 
    while (#pre); auto => />. 
    move => &1 &2 Hbad Hind Hle Hlt />. 
    pose k := if EUF_RF.n{2} <= i{2} * n_session + j{2} then 0 else i{2} * n_session + j{2}.
    rewrite -(Hind (k,n{2})). 
    case ((k, n{2}) \in EUF_RF.m{1}); 
    case ((k, n{2}) \in RF_bad.m{2}) 
    => Hin1 Hin2 //=; 1 : by rewrite get_some => //=; smt ().
    by have Hsup := (map_support (EUF_RF.m{1}) (RF_bad.m{2}) Hind); smt ().
    by have Hsup := (map_support (EUF_RF.m{1}) (RF_bad.m{2}) Hind); smt ().
  + move => &2 Hb; islossless. 
    while true (n_tag - i); auto; 2 : by smt ().
    while true (n_session - j); auto; 2 : by smt ().
    conseq (:true); 1 : by smt (). 
    by islossless. 
  + move => _; proc; conseq />.
    while true (n_tag - i); auto; 2 : by smt ().
    while true (n_session - j); auto; 2 : by smt ().
    conseq (:true); 1 : by smt (). 
    by islossless. 
  + by inline *; sp => />; while (={i, Multiple0.s_cpt}); auto; smt (empty_valE).
qed.


(*-----------------------------------------------------------------------*)
(* We bound the probability of bad in the single sessions setting. *)

(* For the single session protocol, this should be 0. *)
lemma coll_bound_single &m (A <: Adv {EUF_RF, RF_bad, Multiple0}) : 
    (forall (BH <: BasicHashT0{A}),
      islossless BH.tag => islossless BH.reader => islossless A(BH).a) =>
    Pr[Unlink(A, Single, RF_bad).main() @ &m : RF_bad.bad] <= 0%r.
proof.
  move => Hll.
  byphoare => //; hoare.
  proc. 
  call (_: EUF_RF.n = n_tag * n_session /\
     RF_bad.bad = false /\
     (forall (j : int), 0 <= j < n_tag <=> Multiple0.s_cpt.[j] <> None) /\
     (forall (j : int), 0 <= j < n_tag => 0 <= oget Multiple0.s_cpt.[j]) /\
     (forall (j k : int) (x : ptxt), 
       Multiple0.s_cpt.[j] <> None => oget Multiple0.s_cpt.[j] <= k < n_session => 
         RF_bad.m.[(j * n_session + k,x)] = None)). 
  + proc; inline *; auto; sp.
    if; 2 : by auto; smt ().
    sp; if; 2 : by auto; smt ().
    seq 1 :(#pre); 1 : by move => />; auto. 
    auto.
    move => /> &hr i1. 
    pose i2 := (if n_tag <= i1 then 0 else i1).
    move => *.
    have -> /= : !(n_tag * n_session <= 
                   i2 * n_session + oget Multiple0.s_cpt{hr}.[i2]); 
    1 : smt ().
    rewrite Tactics.eq_iff /dom => /=. 
    split; 1: by apply H1; smt().
    rewrite /dom in H2; progress; 1,2,3,4 : smt (get_setE). 
    have := euclideU n_session i2 j (oget Multiple0.s_cpt{hr}.[i2]) k.
    have := (H1 i2 (oget Multiple0.s_cpt{hr}.[i2])) => *.
    have := (H1 j k) => *.   
    smt (get_setE). 
  + by conseq />; auto.
  inline *; sp 6. 
  while (0 <= i <= n_tag /\
   (forall (j : int), 0 <= j && j < i <=> Multiple0.s_cpt.[j] <> None) /\
   (forall (j : int), 0 <= j && j < i => Multiple0.s_cpt.[j] = Some 0));
  1 : by auto; move => /> *; smt (get_setE). 
  by auto => />; smt (empty_valE n_tag_p). 
qed.


(*-----------------------------------------------------------------------*)
(* We bound the probability of bad in the multiple sessions setting. *)

op pr_bad_step_r : real.
op pr_bad_step (k : int) = pr_bad_step_r.
op pr_bad = pr_bad_step_r * (RField.ofint (n_session * n_tag)).

(* Number of plain-texts hashed for tag [i]. *)
op ptxt_hashed_l (i : int) (m : (int * ptxt, ptxt list) fmap) =
  List.filter (fun x => fst x = i) (FSet.elems (SmtMap.fdom m)).

op ptxt_hashed (i : int) (m : (int * ptxt, ptxt list) fmap)  =
  List.size (ptxt_hashed_l i m).

lemma ptxt_hashed_supp (i : int) (x : ptxt) (m : (int * ptxt, ptxt list) fmap) :
    (i,x) \in m <=> (i,x) \in (ptxt_hashed_l i m).
proof.
rewrite /ptxt_hashed_l. 

lemma coll_bound_multiple &m (A <: Adv {EUF_RF, RF_bad, Multiple0}) : 
    (forall (BH <: BasicHashT0{A}),
      islossless BH.tag => islossless BH.reader => islossless A(BH).a) =>
    Pr[Unlink(A, Multiple, RF_bad).main() @ &m : RF_bad.bad] <= pr_bad.
proof.
  move => Hll.
  fel
    1   (* initialization phase  *)
    (BIA.bigi 
      predT
      (fun (k : int) => oget Multiple0.s_cpt.[k]) 
      0 n_tag) (* counter *)
    (fun k => pr_bad_step k) (* update to the upper-bound w.r.t. the counter *)
    (n_tag * n_session) (* upper-bound on the number of steps *)
    (RF_bad.bad) (* failure event *)
    [Multiple(RF_bad).tag : 
      (let j = if (n_tag <= i) then 0 else i in
       j \in Multiple0.s_cpt /\ 
       oget Multiple0.s_cpt.[j] < n_session)
    ] (* pre-condition for the counter increase *)
    (* invariant *)
    (EUF_RF.n = n_tag /\
     RF_bad.bad = false /\
     (forall (j : int), 0 <= j < n_tag <=> Multiple0.s_cpt.[j] <> None) /\
     (forall (j : int), 0 <= j < n_tag => 
         0 <= oget Multiple0.s_cpt.[j] <= n_session) /\
     (forall (j : int), Multiple0.s_cpt.[j] <> None =>
         ptxt_hashed j RF_bad.m = oget Multiple0.s_cpt.[j])
   ).  
  + admit. (* by rewrite StdBigop.Bigreal.BRA.big1_eq. *)
  + smt (n_tag_p n_session_p).
  + inline *; sp 6.
    while (0 <= i <= n_tag /\
     (forall (j : int), 0 <= j && j < i <=> Multiple0.s_cpt.[j] <> None) /\
     (forall (j : int), 0 <= j && j < i => Multiple0.s_cpt.[j] = Some 0));
    1 : by auto; move => /> *; smt (get_setE).
    auto => />; split; 1 : smt (empty_valE n_tag_p).
    move => *; split. 
    + rewrite (eq_big_int 0 n_tag _ (fun k => 0)); 
      1 : by move => *; smt (get_setE).
      by rewrite big1_eq.
    move => *; split; 1 :  smt (empty_valE n_tag_p).
    move => *; split; 1 :  smt (empty_valE n_session_p).
    by move => *; rewrite /ptxt_hashed fdom0 elems_fset0 /#.

  + rewrite /pr_bad_step /=.
    proc; inline *; 
    do 2! (sp; if; 2 : by hoare; auto). 
   seq 5 : (#post) (pr_bad_step_r) 1%r (1%r - pr_bad_step_r) 0%r => //;
   2 : by hoare; conseq />.
   wp; rnd; skip => /> &hr i1. 
   pose i2 := (if n_tag <= i1 then 0 else i1).
   have -> /= : !(n_tag <= i2) by smt (n_tag_p).
   move => *.
   search (mu _ (fun _ => _ List.\in _) <= _ ).
   print Mu_mem.mu_mem_le_size.
   print ptxt_hashed.
   have := Mu_mem.mu_mem_le_size (RF_bad.m{hr}) dnonce (mu1 dnonce maxu_dnonce) _.
   rewrite /(\in).
   admit.

  (* if the precondition for [tag] holds, the counter increases. *)
  + admit.
  (* if the precondition for [tag] does not holds, the counter does not 
     increase. *)
  + move => b _; proc; inline *; auto; sp.
    if; 2 : by auto; smt ().
    sp; if; 2 : by auto; smt ().
    seq 1 :(#pre); 1 : by move => />; auto.
    auto.
    move => /> &hr i1.
    pose i2 := (if n_tag <= i1 then 0 else i1).
    move => *.
    have -> /= : !(n_tag * n_session <=
                   i2 * n_session + oget Multiple0.s_cpt{hr}.[i2]);
    1 : smt ().
   rewrite Tactics.eq_iff /dom => /=.
   split.                       (* why is there a issue with '; 1 :' here ? *)
   + by apply H1; smt().
   split.                       (* why is there a issue with '; 1 :' here ? *)
   + by apply H1; smt().
   rewrite /dom in H2; progress; 1,2,3,4 : smt (get_setE).
   have := euclideU n_session i2 j (oget Multiple0.s_cpt{hr}.[i2]) k.
   have := (H1 i2 (oget Multiple0.s_cpt{hr}.[i2])) => *.
   have := (H1 j k) => *.
   smt (get_setE).




(*-----------------------------------------------------------------------*)
(* Assuming there are no collision, the single and multiple sessions
   protocols coincide. *)
lemma eq_single_mult &m (A <: Adv {EUF_RF, RF_bad, Multiple0}) :
    Pr[Unlink(A, Multiple, RF_bad).main() @ &m : res] =
    Pr[Unlink(A, Single, RF_bad).main() @ &m : res].
proof.
  byequiv => //; proc; inline *; sp 5 5. 
  seq 4 4 : (#pre /\ ={Multiple0.s_cpt, i} /\ 
             (forall j, (0 <= j < n_tag) <=> Multiple0.s_cpt.[j]{2} <> None) /\
             (forall j, (0 <= j < n_tag) => Multiple0.s_cpt.[j]{2} = Some 0) /\
              forall x i r, r \in odflt [] RF_bad.m.[(i,x)]{1} <=> 
               exists j, 0 <= j < n_session /\ 
                              r \in odflt [] RF_bad.m.[(i * n_session + j, x)]{2}).
  + sp; while (={Multiple0.s_cpt, i} /\ 0 <= i{2} <= n_tag /\
         (forall j, (0 <= j < i{2}) <=> Multiple0.s_cpt.[j]{2} <> None) /\
         (forall j, (0 <= j < i{2}) => Multiple0.s_cpt.[j]{2} = Some 0) /\
          forall x i r, r \in odflt [] RF_bad.m.[(i,x)]{1} <=> 
           exists j, 0 <= j < n_session /\ 
                          r \in odflt [] RF_bad.m.[(i * n_session + j, x)]{2}); 
    1 : by auto; smt (get_setE).
    by auto => />; smt (empty_valE n_tag_p). 
  call (_: ={glob Multiple0} /\
    EUF_RF.n{1} = n_tag /\ EUF_RF.n{2} = n_tag * n_session /\ 
    (forall j, (0 <= j < n_tag) <=> Multiple0.s_cpt.[j]{2} <> None) /\
    (forall j, (0 <= j < n_tag) => 0 <= oget Multiple0.s_cpt.[j]{1}) /\
    forall x i r, r \in odflt [] RF_bad.m.[(i,x)]{1} <=> 
      exists j, 0 <= j < n_session /\ 
                     r \in odflt [] RF_bad.m.[(i * n_session + j, x)]{2}). 
  (* tag *) 
  - move => />; 1 : by move => />; auto.
    proc; inline *; sp; if => //.
      (* 4 *)
    + sp; if => //. 
        (* 5 *)
      + seq 1 1 : (#pre /\ ={n}); 1 : by auto => />.
        wp; sp 3 3; seq 1 1 : (#pre); 1: by auto.
        move => />; rnd (fun x => x); auto.
        move => /> &1 &2 i_R; pose iR := (if n_tag <= i_R then 0 else i_R).
        have -> /= : !(n_tag <= iR) by smt (n_tag_p).
        move => *.
        have -> /= : 
          !(n_tag * n_session <= 
            iR * n_session + oget Multiple0.s_cpt{2}.[iR]) 
        by smt (n_tag_p n_session_p).
        split; 1 : by smt(drf_sup).
        move => /> *; split; 1: smt (get_setE).
        move => /> *; split; 1: smt (get_setE).
        move => /> *; split => *. 
          (* 6 *)
        + move :H6; case (iR = i00 /\ n{2} = x0) => [[Heq1 Heq2] | Hdeq] => H6.
          + rewrite Heq1 Heq2 get_set_eqE /= in H6; 1 : smt (). 
            have H7 := (H1 x0 i00 r1); case H6 => [->> | Hrin]. 
            + exists (oget Multiple0.s_cpt{2}.[iR]). 
              split; 1: smt(n_session_p n_tag_p).
              rewrite get_set_eqE //. 
              by smt (). 
            case H7 => [H7 _]; have [j H8] := (H7 Hrin); exists j.
            by case :(oget Multiple0.s_cpt{2}.[iR] = j); smt (get_setE).
          rewrite get_set_neqE // in H6; 1 : smt ().
          have H7 := (H1 x0 i00 r1).
          case H7 => [H7 _]; have [j H8] := (H7 H6); exists j.
          by case :(oget Multiple0.s_cpt{2}.[iR] = j); smt (get_setE).
        move :H8;
        (* Four almost identical cases. *)
        case :(oget Multiple0.s_cpt{2}.[iR] = j); 
        case (iR = i00 /\ n{2} = x0). 
        + move => [Heq1 Heq2 Heq3]; 
          rewrite Heq1 Heq2 -Heq3 get_set_eqE /=; 1 : smt (). 
          rewrite get_set_eqE /=; 1 : smt(). 
          move => [H8 | H8]; 1 : smt(). 
          by right; apply H1; exists j; smt (get_setE).
        + move => Hdeq Heq.
          rewrite -Heq; rewrite !get_set_neqE /=; 1,2 : smt (). 
          by move => H8; apply H1; exists j; smt (get_setE).
        + move => [Heq1 Heq2 Hdeq]; 
          rewrite Heq1 Heq2 !get_setE /=. 
          have ->/= : !(i00 * n_session + j = 
                        i00 * n_session + oget Multiple0.s_cpt{2}.[i00]) 
          by smt ().
          by move => H8; right; apply H1; exists j; smt (get_setE).
        move => Hdeq Hdeq2.
        rewrite !get_set_neqE /=; 2 : smt (). 
        + have := euclideU n_session i00 iR j (oget Multiple0.s_cpt{2}.[iR]).
          smt().
        by move => H8; apply H1; exists j; smt (get_setE).        
    auto; move => /> *; split; 1 : smt (). 
    move => *; split; 1 : smt (). 
    move => *; split; 1 : smt (). 
    by move => *; rewrite H1; exists j; smt ().
  auto; move => /> *; split; 1 : smt (). 
  move => *; split; 1 : smt (). 
  move => *; split; 1 : smt (). 
  by move => *; rewrite H1; exists j; smt ().

  (* reader *) 
  - proc; inline *; auto => />. 
    while (#pre /\ 0 <= i{1} /\ ={i,b}); 2: by conseq />; auto; smt (n_session_p n_tag_p). 
    conseq />; wp. 
    while {2} 
        (0 <= j{2} <= n_session /\
         (b0{2} <=> exists k, 0 <= k < j{2} /\
           let i2 = i{2} * n_session + k in
           (h{2} \in odflt [] RF_bad.m{2}.[(if EUF_RF.n{2} <= i2 then 0 else i2, n{2})])))
      (n_session - j{2}).
    + auto => /> *; progress; 1,2,5: smt (). 
      + case H2; 1 : by move => [k H2]; exists k; smt(). 
        move => *; exists (j{hr}); split; 1 : by smt (). 
        by move :H3; rewrite /dom; case :(RF_bad.m{hr}.[_]); smt (). 
      case (k = j{hr}) => [->> |Hk]. 
      + by right => *; move :H4; rewrite /dom; case :(RF_bad.m{hr}.[_]); smt ().
      by left; exists k; smt (). 
    auto => /> *; split; 1 : by smt (n_session_p).
    move => *; split; 1 : smt (). 
    move => *; split; 1 : smt (). 
    congr.
    have ->> : (j_R = n_session); 1 : smt ().
    have He := (H1 n{2} i{2} h{2}).
    have -> /= : !(n_tag <= i{2}) by smt ().
    have <- /= : 
      (h{2} \in odflt [] RF_bad.m{1}.[i{2}, n{2}]) = 
      (((i{2}, n{2}) \in RF_bad.m{1}) && (h{2} \in oget RF_bad.m{1}.[i{2}, n{2}])). 
    + by rewrite /dom; case (RF_bad.m{1}.[i{2}, n{2}]); smt ().
    rewrite He. 
    rewrite Tactics.eq_iff; progress.
    + by exists j0; smt ().
    exists k; smt ().

  (* invariant implies the post *)
  - auto => &1 &2 *; move :H => />; move => H j; smt ().
qed.
