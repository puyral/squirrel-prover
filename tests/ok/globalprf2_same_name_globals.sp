channel c.

abstract m : message.

name k : message

hash h

(* NEW *)
process P =
  let x = h(m, k) in
  if x = m then (!_i P: out(c, m)) else Q: out(c, empty).

system default = P.

system PP = [default/left] 
   with gprf time, h(_,k).

(* global macros in mutually exclusive branches re-use the same name *)
lemma [PP] _ : 
  happens(P) => 
  x@P = 
  try find t such that
    (((t = Q) && (t < P) && (m = m)) || ((t = P) && (t < P) && (m = m)))
  in
    try find  such that ((t = Q) && (t < P) && (m = m))
    in n_PRF
    else try find  such that ((t = P) && (t < P) && (m = m))
    in n_PRF
    else error
  else n_PRF.
Proof. intro H @/x. congruence. Qed.


(* global macros in mutually exclusive branches re-use the same name *)
lemma [PP] _ (i : index): 
  happens(Q) => 
  x@Q = 
  try find t such that
    (((t = Q) && (t < Q) && (m = m)) || ((t = P) && (t < Q) && (m = m)))
  in
    try find  such that ((t = Q) && (t < Q) && (m = m))
    in n_PRF
    else try find  such that ((t = P) && (t < Q) && (m = m))
    in n_PRF
    else error
  else n_PRF.
Proof. intro H @/x. congruence. Qed.
