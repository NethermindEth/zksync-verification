require        Constants.
require import PointMulIntoDest.
require import PointSubAssign.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

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
}.

lemma addAssignPermutationLinearisationContributionWithV_extracted_equiv_low :
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
qed.
