require        Constants.
require import PointAddAssign.
require import PointMulAndAddIntoDest.
require import PointMulIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module AddAssignRescueCustomGateLinearisationContributionWithV = {
  proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256, stateOpening3AtZ : uint256): unit = {
    var accumulator, intermediateValue, _4, _7, _10, _12;
    accumulator <- (PurePrimops.mulmod stateOpening0AtZ stateOpening0AtZ R_MOD);
    accumulator <- (PurePrimops.addmod accumulator (R_MOD - stateOpening1AtZ) R_MOD);
    _4 <@ Primops.mload(STATE_ALPHA_SLOT);
    accumulator <- (PurePrimops.mulmod accumulator _4 R_MOD);
    intermediateValue <- (PurePrimops.mulmod stateOpening1AtZ stateOpening1AtZ R_MOD);
    intermediateValue <- (PurePrimops.addmod intermediateValue (R_MOD - stateOpening2AtZ) R_MOD);
    _7 <@ Primops.mload(STATE_POWER_OF_ALPHA_2_SLOT);
    intermediateValue <- (PurePrimops.mulmod intermediateValue _7 R_MOD);
    accumulator <- (PurePrimops.addmod accumulator intermediateValue R_MOD);
    intermediateValue <- (PurePrimops.mulmod stateOpening2AtZ stateOpening0AtZ R_MOD);
    intermediateValue <- (PurePrimops.addmod intermediateValue (R_MOD - stateOpening3AtZ) R_MOD);
    _10 <@ Primops.mload(STATE_POWER_OF_ALPHA_3_SLOT);
    intermediateValue <- (PurePrimops.mulmod intermediateValue _10 R_MOD);
    accumulator <- (PurePrimops.addmod accumulator intermediateValue R_MOD);
    _12 <@ Primops.mload(STATE_V_SLOT);
    accumulator <- (PurePrimops.mulmod accumulator _12 R_MOD);
    PointMulAndAddIntoDest.low(VK_GATE_SELECTORS_1_X_SLOT, accumulator, dest);
  }

  proc mid(stateOpening0AtZ: int, stateOpening1AtZ: int, stateOpening2AtZ: int, stateOpening3AtZ: int, alpha: int): (int*int) option {
    var accumulator, intermediateValue, _4, _7, _10, _12;
    accumulator <- (stateOpening0AtZ * stateOpening0AtZ) %% Constants.R;
    accumulator <- (accumulator + (Constants.R - stateOpening1AtZ)) %% Constants.R;
    (* _4 <@ Primops.mload(STATE_ALPHA_SLOT); -- alpha *)
    accumulator <- (PurePrimops.mulmod accumulator alpha R_MOD);
    intermediateValue <- (PurePrimops.mulmod stateOpening1AtZ stateOpening1AtZ R_MOD);
    intermediateValue <- (PurePrimops.addmod intermediateValue (R_MOD - stateOpening2AtZ) R_MOD);
    _7 <@ Primops.mload(STATE_POWER_OF_ALPHA_2_SLOT);
    intermediateValue <- (PurePrimops.mulmod intermediateValue _7 R_MOD);
    accumulator <- (PurePrimops.addmod accumulator intermediateValue R_MOD);
    intermediateValue <- (PurePrimops.mulmod stateOpening2AtZ stateOpening0AtZ R_MOD);
    intermediateValue <- (PurePrimops.addmod intermediateValue (R_MOD - stateOpening3AtZ) R_MOD);
    _10 <@ Primops.mload(STATE_POWER_OF_ALPHA_3_SLOT);
    intermediateValue <- (PurePrimops.mulmod intermediateValue _10 R_MOD);
    accumulator <- (PurePrimops.addmod accumulator intermediateValue R_MOD);
    _12 <@ Primops.mload(STATE_V_SLOT);
    accumulator <- (PurePrimops.mulmod accumulator _12 R_MOD);
    PointMulAndAddIntoDest.low(VK_GATE_SELECTORS_1_X_SLOT, accumulator, dest);
  }
}.

lemma addAssignRescueCustomGateLinearisationContributionWithV_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_addAssignRescueCustomGateLinearisationContributionWithV ~ AddAssignRescueCustomGateLinearisationContributionWithV.low :
      ={arg, glob AddAssignRescueCustomGateLinearisationContributionWithV} ==>
      ={res, glob AddAssignRescueCustomGateLinearisationContributionWithV}
    ].
proof.
  proc.
  call (pointMulAndAddIntoDest_extracted_equiv_low).
  inline*. wp. skip. rewrite /Constants.R. by progress.
qed.
