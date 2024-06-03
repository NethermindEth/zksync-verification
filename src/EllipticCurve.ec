require import AllCore Group Ring Int IntDiv ZModP. 

const p : { int | prime p } as prime_p.
const q : { int | prime q } as prime_q.

clone ZModPCyclic as G1 with op order <- q.
clone ZModPCyclic as G2 with op order <- q.

type g1 = G1.zmod.
type g2 = G2.zmod.

clone Group as Gt.

type gt = Gt.group.

op pairing : g1 -> g2 -> gt.

op test = G1.ZModRing.zero.

axiom pairing_bilin (m : g1) (n : g2) : pairing m n = (pairing G1.ZModC.e G2.ZModC.e) ^ (G1.ZModC.log m * G2.ZModC.log n).


op coordinates: g1 -> fq*fq.

op ( . ) : fq -> g1 -> 

axiom injective_coord : injective coordinates.
axiom coordinates_e : coordinates e = (Fq.zeror, Fq.zeror).

axiom ec_equation (g : g1) (x y : fq) : x = fst (coordinates g) => y = snd (coordinates g) => y * y = x * x * x + Fq.oner + Fq.oner + Fq.oner.

axiom 
