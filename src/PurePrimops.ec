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

(* parsing calldata *)
op load_calldata_offset_1 = load calldata (W256.of_int 4).
op load_calldata_offset_2 = load calldata (W256.of_int 36).
op load_calldata_offset_3 = load calldata (W256.of_int 68).
op load_calldata_public_input_length = load calldata (load_calldata_offset_1 + W256.of_int 4).
op load_calldata_public_input = load calldata (load_calldata_offset_1 + W256.of_int 36).
op load_calldata_proof_length = load calldata (load_calldata_offset_2 + W256.of_int 4).
op load_calldata_state_poly_0 = load_pair calldata (load_calldata_offset_2 + W256.of_int 36).
op load_calldata_state_poly_1 = load_pair calldata (load_calldata_offset_2 + W256.of_int 100).
op load_calldata_state_poly_2 = load_pair calldata (load_calldata_offset_2 + W256.of_int 164).
op load_calldata_state_poly_3 = load_pair calldata (load_calldata_offset_2 + W256.of_int 228).
op load_calldata_copy_permutation_grand_product = load_pair calldata (load_calldata_offset_2 + W256.of_int 292).
op load_calldata_lookup_s_poly = load_pair calldata (load_calldata_offset_2 + W256.of_int 356).
op load_calldata_lookup_grand_product = load_pair calldata (load_calldata_offset_2 + W256.of_int 420).
op load_calldata_quotient_poly_part_0 = load_pair calldata (load_calldata_offset_2 + W256.of_int 484).
op load_calldata_quotient_poly_part_1 = load_pair calldata (load_calldata_offset_2 + W256.of_int 548).
op load_calldata_quotient_poly_part_2 = load_pair calldata (load_calldata_offset_2 + W256.of_int 612).
op load_calldata_quotient_poly_part_3 = load_pair calldata (load_calldata_offset_2 + W256.of_int 676).
op load_calldata_state_poly_0_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 740).
op load_calldata_state_poly_1_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 772).
op load_calldata_state_poly_2_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 804).
op load_calldata_state_poly_3_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 836).
op load_calldata_state_poly_3_opening_at_z_omega = load calldata (load_calldata_offset_2 + W256.of_int 868).
op load_calldata_gate_selector_0_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 900).
op load_calldata_copy_permutation_poly_0_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 932).
op load_calldata_copy_permutation_poly_1_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 964).
op load_calldata_copy_permutation_poly_2_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 996).
op load_calldata_copy_permutation_grand_product_opening_at_z_omega = load calldata (load_calldata_offset_2 + W256.of_int 1028).
op load_calldata_lookup_s_poly_opening_at_z_omega = load calldata (load_calldata_offset_2 + W256.of_int 1060).
op load_calldata_lookup_grand_product_opening_at_z_omega = load calldata (load_calldata_offset_2 + W256.of_int 1092).
op load_calldata_lookup_t_poly_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 1124).
op load_calldata_lookup_t_poly_opening_at_z_omega = load calldata (load_calldata_offset_2 + W256.of_int 1156).
op load_calldata_lookup_selector_poly_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 1188).
op load_calldata_lookup_table_type_poly_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 1220).
op load_calldata_quotient_poly_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 1252).
op load_calldata_linearisation_poly_opening_at_z = load calldata (load_calldata_offset_2 + W256.of_int 1284).
op load_calldata_opening_proof_at_z = load_pair calldata (load_calldata_offset_2 + W256.of_int 1316).
op load_calldata_opening_proof_at_z_omega = load_pair calldata (load_calldata_offset_2 + W256.of_int 1380).
op load_calldata_recursive_proof_length = load calldata (load_calldata_offset_3 + W256.of_int 4).
op load_calldata_recursive_part_p1 = load_pair calldata (load_calldata_offset_3 + W256.of_int 36).
op load_calldata_recursive_part_p2 = load_pair calldata (load_calldata_offset_3 + W256.of_int 100).


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
