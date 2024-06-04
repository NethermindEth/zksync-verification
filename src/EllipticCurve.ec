require import AllCore Group Ring Int IntDiv ZModP. 

const p : { int | prime p } as prime_p.
const q : { int | prime q } as prime_q.


clone include ZModPCyclic
  with op order <- q
  rename "zmod" as "g1"
  rename "ge2_order" as "ge2_order_g1"
  rename "ZModRing" as "ZModG1"
  rename "ZModC" as "CyclicG1".
  
clone include ZModPCyclic
  with op order <- q
  rename "zmod" as "g2"
  rename "ge2_order" as "ge2_order_g2"
  rename "ZModRing" as "ZModG2"
  rename "ZModC" as "CyclicG2".

type gt.

op ( + ) = CyclicG1.( * ).
op ( ** ) = CyclicG2.( * ).
 

clone include CyclicGroup with type group <- gt.

op pairing : g1 -> g2 -> gt.

axiom pairing_bilin (m : g1) (n : g2) : pairing m n = (pairing CyclicG1.g CyclicG2.g) ^ (CyclicG1.log m * CyclicG2.log n).

axiom pairing_nondegenerate : pairing (CyclicG1.g) (CyclicG2.g) <> e.  

(*Should it actually take uint256? *)
op ec_add (x y : g1) : g1 = x + y.
op ec_mul (s x : g1) : g1 = x ^ s.

op coordinates: g1 -> fq*fq.

op ( . ) : fq -> g1 -> 

axiom injective_coord : injective coordinates.
axiom coordinates_e : coordinates e = (Fq.zeror, Fq.zeror).

axiom ec_equation (g : g1) (x y : fq) : x = fst (coordinates g) => y = snd (coordinates g) => y * y = x * x * x + Fq.oner + Fq.oner + Fq.oner.

axiom 
