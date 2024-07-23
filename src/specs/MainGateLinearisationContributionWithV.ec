require        Constants.
require import PointAddAssign.
require import PointMulAndAddIntoDest.
require import PointMulIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module MainGateLinearisationContributionWithV = {
  proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256, stateOpening3AtZ : uint256): unit = {
  var _6, _8, _12, _15, _17, coeff;
    PointMulIntoDest.low(VK_GATE_SETUP_0_X_SLOT, stateOpening0AtZ, dest);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_1_X_SLOT, stateOpening1AtZ, dest);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_2_X_SLOT, stateOpening2AtZ, dest);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_3_X_SLOT, stateOpening3AtZ, dest);
    _6 <- (PurePrimops.mulmod stateOpening0AtZ stateOpening1AtZ R_MOD);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_4_X_SLOT, _6, dest);
    _8 <- (PurePrimops.mulmod stateOpening0AtZ stateOpening2AtZ R_MOD);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_5_X_SLOT, _8, dest);
    PointAddAssign.low(dest, VK_GATE_SETUP_6_X_SLOT);
    _12 <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT);
    PointMulAndAddIntoDest.low(VK_GATE_SETUP_7_X_SLOT, _12, dest);
    _15 <@ Primops.mload(STATE_V_SLOT);
    _17 <@ Primops.mload(PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT);
    coeff <- (PurePrimops.mulmod _17 _15 R_MOD);
    PointMulIntoDest.low(dest, coeff, dest);
  }
}.

lemma mainGateLinearisationContributionWithV_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_mainGateLinearisationContributionWithV ~ MainGateLinearisationContributionWithV.low :
      ={arg, glob MainGateLinearisationContributionWithV} ==>
      ={res, glob MainGateLinearisationContributionWithV}
    ].
proof.
  proc.
  inline Primops.mload.
  call (pointMulIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointAddAssign_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  call (pointMulIntoDest_extracted_equiv_low). wp.
  skip. rewrite /Constants.R. by progress.
qed.
