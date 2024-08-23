pragma Goals:printall.

require import Array.
require import Memory.
require import Ring.
        import Ring.IntID.
require export UInt256.
require import Utils.

theory PurePrimops.

import MemoryMap.

(* definitions ========== *)

(* uninterpreted functions *)
op calldata : mem.
op calldatasize: uint256.
op callvalue : uint256.
op keccak256_f : uint8 array -> uint256.


op iszero(v : uint256) : uint256 = if (v = W256.zero) then W256.one else  W256.zero
axiomatized by iszeroE.
op eq_uint256(a : uint256, b : uint256) : uint256  = if a = b then W256.one else W256.zero
axiomatized by eq_uint256E.
op gt_uint256 (x y : uint256)  = if y < x then W256.one else W256.zero
axiomatized by gt_uint256E.
op lt_uint256 (x y : uint256)  = if x < y then W256.one else W256.zero
axiomatized by lt_uint256E.
op slt_uint256 (x y : uint256) = if uint256_as_signed x < uint256_as_signed y then W256.one else W256.zero
axiomatized by slt_uint256E.

abbrev mload = load.
abbrev mstore = store.

op mulmod(a b n : uint256) : uint256 =
  let a_int = W256.to_uint a in
  let b_int = W256.to_uint b in
  let n_int = W256.to_uint n in
  W256.of_int ((a_int * b_int) %% n_int)
axiomatized by mulmodE.

op addmod(a b n : uint256) : uint256 =
  let a_int = W256.to_uint a in
  let b_int = W256.to_uint b in
  let n_int = W256.to_uint n in
  W256.of_int ((a_int + b_int) %% n_int)
axiomatized by addmodE.

op bit_and(a : uint256, b : uint256) : uint256 = a `&` b
axiomatized by bit_andE.

op shl(a : uint256, b : uint256) : uint256 = b `<<<` (W256.to_uint a)
axiomatized by shlE.

op shr(a : uint256, b : uint256) : uint256 = b `>>>` (W256.to_uint a)
axiomatized by shrE.

op modexp(base: uint256, exponent: uint256, mod: uint256) = W256.of_int (((W256.to_uint base) ^ (W256.to_uint exponent)) %% (W256.to_uint mod))
axiomatized by modexpE.


(* lemmas =========== *)

(* iszero *)
lemma iszero_zeroE : iszero (W256.zero) = W256.one.
    proof.
      rewrite /iszero.
      simplify.
      trivial.
  qed.
lemma iszero_nonzeroE (val: uint256) : val <> W256.zero => iszero val = W256.zero.
    proof.
      progress.
      rewrite /iszero.
      smt ().
  qed.

end PurePrimops.
