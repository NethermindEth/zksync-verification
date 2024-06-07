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

