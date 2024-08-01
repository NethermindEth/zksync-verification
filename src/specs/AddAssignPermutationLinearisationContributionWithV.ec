require        Constants.
require import PointMulIntoDest.
require import PointSubAssign.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

module AddAssignPermutationLinearisationContributionWithV = {
  proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256, stateOpening3AtZ : uint256): unit = {
    var factor, _1, _3, gamma, _4, intermediateValue, _6, _7, _9, _10, _12, _13, l0AtZ, _16, _17, _18, _20, _21, _23, beta', gamma_1, _25, _26, _27, intermediateValue_1, _29, _30, _31, _33, _34, _35, _36;
    factor <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    _1 <@ Primops.mload(STATE_BETA_SLOT);
    _3 <@ Primops.mload(STATE_Z_SLOT);
    gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    _4 <- (PurePrimops.addmod (PurePrimops.mulmod _3 _1 R_MOD) gamma R_MOD);
    intermediateValue <- (PurePrimops.addmod _4 stateOpening0AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue R_MOD);
    _6 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 R_MOD) NON_RESIDUES_0 R_MOD);
    _7 <- (PurePrimops.addmod _6 gamma R_MOD);
    intermediateValue <- (PurePrimops.addmod _7 stateOpening1AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue R_MOD);
    _9 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 R_MOD) NON_RESIDUES_1 R_MOD);
    _10 <- (PurePrimops.addmod _9 gamma R_MOD);
    intermediateValue <- (PurePrimops.addmod _10 stateOpening2AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue R_MOD);
    _12 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 R_MOD) NON_RESIDUES_2 R_MOD);
    _13 <- (PurePrimops.addmod _12 gamma R_MOD);
    intermediateValue <- (PurePrimops.addmod _13 stateOpening3AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue R_MOD);
    l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _16 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    _17 <- (PurePrimops.mulmod l0AtZ _16 R_MOD);
    factor <- (PurePrimops.addmod factor _17 R_MOD);
    _18 <@ Primops.mload(STATE_V_SLOT);
    factor <- (PurePrimops.mulmod factor _18 R_MOD);
    Primops.mstore(COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF, factor);
    _20 <@ Primops.mload(STATE_BETA_SLOT);
    _21 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    factor <- (PurePrimops.mulmod _21 _20 R_MOD);
    _23 <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    factor <- (PurePrimops.mulmod factor _23 R_MOD);
    beta' <@ Primops.mload(STATE_BETA_SLOT);
    gamma_1 <@ Primops.mload(STATE_GAMMA_SLOT);
    _25 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _26 <- (PurePrimops.mulmod _25 beta' R_MOD);
    _27 <- (PurePrimops.addmod _26 gamma_1 R_MOD);
    intermediateValue_1 <- (PurePrimops.addmod _27 stateOpening0AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue_1 R_MOD);
    _29 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _30 <- (PurePrimops.mulmod _29 beta' R_MOD);
    _31 <- (PurePrimops.addmod _30 gamma_1 R_MOD);
    intermediateValue_1 <- (PurePrimops.addmod _31 stateOpening1AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue_1 R_MOD);
    _33 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _34 <- (PurePrimops.mulmod _33 beta' R_MOD);
    _35 <- (PurePrimops.addmod _34 gamma_1 R_MOD);
    intermediateValue_1 <- (PurePrimops.addmod _35 stateOpening2AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue_1 R_MOD);
    _36 <@ Primops.mload(STATE_V_SLOT);
    factor <- (PurePrimops.mulmod factor _36 R_MOD);
    PointMulIntoDest.low(VK_PERMUTATION_3_X_SLOT, factor, QUERIES_BUFFER_POINT_SLOT);
    PointSubAssign.low(dest, QUERIES_BUFFER_POINT_SLOT);
  }

  proc mid(point: (int*int), vk_permutation_3: (int*int), stateOpening0AtZ: int, stateOpening1AtZ: int, stateOpening2AtZ: int, stateOpening3AtZ: int, state_beta: int, state_v: int, state_z: int, state_gamma: int, state_alpha4: int, state_alpha5: int, state_gp_omega: int, state_l0AtZ: int, poly0_opening: int, poly1_opening: int, poly2_opening: int): (int * (int*int)) option = {
      var mul_factor, buffer_point, ret_point, ret_factor,
      ret;
    mul_factor <- ((
      (state_alpha4 * state_beta * state_gp_omega) *
      ((poly0_opening * state_beta) + state_gamma + stateOpening0AtZ) *
      ((poly1_opening * state_beta) + state_gamma + stateOpening1AtZ) *
      ((poly2_opening * state_beta) + state_gamma + stateOpening2AtZ)
    ) * state_v) %% Constants.R;
    buffer_point <@ PointMulIntoDest.mid(vk_permutation_3.`1, vk_permutation_3.`2, mul_factor);
    if (is_none buffer_point) {
      ret_point <- None;
    } else {
      ret_point <@ PointSubAssign.mid(point, odflt (0,0) buffer_point);
    }

    if (is_none ret_point) {
      ret <- None;
    } else {
      ret_factor <- ((
        state_alpha4 *
        (state_z * state_beta + state_gamma + stateOpening0AtZ) *
        (state_z * state_beta * Constants.NON_RESIDUE_0 + state_gamma + stateOpening1AtZ) *
        (state_z * state_beta * Constants.NON_RESIDUE_1 + state_gamma + stateOpening2AtZ) *
        (state_z * state_beta * Constants.NON_RESIDUE_2 + state_gamma + stateOpening3AtZ) +
        state_l0AtZ * state_alpha5
      ) * state_v) %% Constants.R;
      ret <- Some (ret_factor, odflt (0, 0) ret_point);
    }

    return ret;
  }
}.

(* requries sub assign extracted fix *)
(* lemma addAssignPermutationLinearisationContributionWithV_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_addAssignPermutationLinearisationContributionWithV ~ AddAssignPermutationLinearisationContributionWithV.low :
      ={arg, glob AddAssignPermutationLinearisationContributionWithV} ==>
      ={res, glob AddAssignPermutationLinearisationContributionWithV}
    ].
proof.
  proc.
  call (pointSubAssign_extracted_equiv_low). wp.
  call (pointMulIntoDest_extracted_equiv_low).
  inline*. wp. skip. rewrite /Constants.R. by progress.
qed. *)

lemma addAssignPermutationLinearisationContributionWithV_low_equiv_mid (mem_0: mem) :
    equiv [
      AddAssignPermutationLinearisationContributionWithV.low ~ AddAssignPermutationLinearisationContributionWithV.mid :
      arg{2}.`1.`1 = W256.to_uint (load mem_0 arg{1}.`1) /\
      arg{2}.`1.`2 = W256.to_uint (load mem_0 (arg{1}.`1 + W256.of_int 32)) /\
      arg{2}.`2.`1 = W256.to_uint (load mem_0 VK_PERMUTATION_3_X_SLOT) /\
      arg{2}.`2.`2 = W256.to_uint (load mem_0 VK_PERMUTATION_3_Y_SLOT) /\
      arg{2}.`3 = W256.to_uint arg{1}.`2 /\
      arg{2}.`4 = W256.to_uint arg{1}.`3 /\
      arg{2}.`5 = W256.to_uint arg{1}.`4 /\
      arg{2}.`6 = W256.to_uint arg{1}.`5 /\
      arg{2}.`7 = W256.to_uint (load mem_0 STATE_BETA_SLOT)
    ].

















