senc enc,dec
name k1 : message
name k2 : message
name r : message
name n : message
abstract ok : message

system null.

equiv fail : <k1,enc(n,r,diff(k1,k2))>.
Proof.
  enckp 0.
