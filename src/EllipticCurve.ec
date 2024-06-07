require import AllCore Group Ring Int IntDiv ZModP. 

type g1, g2.

clone CyclicGroup as G1 with type group <- g1.

abbrev q = G1.order.

axiom prime_q : prime q.

clone G1.PowZMod as G1Pow with
  lemma prime_order <- prime_q
  rename "exp" as "fq".

type fq = G1Pow.fq.
  
clone CyclicGroup as G2 with type group <- g2.

clone G2.PowZMod as G2Pow with
  type exp <- fq.

import G1Pow.ZModE.

(* The group operation in the group G1. *)
op ( + ) = G1.( * ).
(* The group operation in the group G2. *)
op ( ++ ) = G2.( * ).

type gt.

clone CyclicGroup as Gt with
  type group <- gt
  rename "( * )" as "( ** )".

import Gt.

clone Gt.PowZMod as GtPow with
  type exp <- fq.

import GtPow.

(* Bilinear pairing operation. *)
op "_.[_]" : g1 -> g2 -> gt.

op [\1] (x : fq) = G1Pow.( ^ ) G1.g x.
op [\2] (x : fq) = G2Pow.( ^ ) G2.g x.

op unit : fq = G1Pow.ZModE.one.

axiom pairing_nondeg : G1.g.[G2.g] <> e.
axiom pairing_bilin (m n: fq) : (\1 m).[\2 n] = (\1 unit).[\2 unit] ^ (m * n).

import G1Pow.

lemma pairing_bilin_int (m n : int) : (G1.( ^ ) G1.g m).[G2.( ^ ) G2.g n] = Gt.( ^ ) (G1.g).[G2.g] (m*n).
proof.
  have -> : G1.( ^ ) G1.g m = G1Pow.( ^ ) G1.g (inzmod m).
  rewrite -G1.expE.
  rewrite - G1Pow.expE.
  apply G1Pow.log_bij.

  smt(@G1Pow).
  smt(@G1Pow @G2Pow @GtPow pairing_bilin).

lemma pairing_bilin_left (x0 x1 : g1) (y : g2) : (x0 + x1).[y] = x0.[y] * x1.[y]. 
proof.
  rewrite -{1} (G1.expgK x0) -{1} (G1.expgK x1) -{1} G2.expgK.
  have -> : (G1.( ^ ) G1.g (G1.log x0)) + (G1.( ^ ) G1.g (G1.log x1)) = G1.( ^ ) G1.g (G1.log x0 + G1.log x1) by smt(@G1).
  rewrite pairing_bilin.
  smt(@G1).
 
  rewrite - (G1.expD G1.g).
  rewrite -G2.expgK.
  rewrite - {1} (G1.expgK x1).
  rewrite - {1} (G2.expgK y).
  simplify.
  have H : 
  rewrite - {1} (G1.expD).
  unfold ( + ).
