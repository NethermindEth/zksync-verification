require        Constants.
require import PointAddAssign.
require import PointMulAndAddIntoDest.
require import PointMulIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module AddAssignRescueCustomGateLinearisationContributionWithV = {
  proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256, stateOpening3AtZ : uint256): unit = {
    var accumulator, intermediateValue, _4, _7, _10, _12;
    accumulator <- (PurePrimops.mulmod stateOpening0AtZ stateOpening0AtZ (W256.of_int Constants.R));
    accumulator <- (PurePrimops.addmod accumulator ((W256.of_int Constants.R) - stateOpening1AtZ) (W256.of_int Constants.R));
    _4 <@ Primops.mload(W256.of_int 3520);
    accumulator <- (PurePrimops.mulmod accumulator _4 (W256.of_int Constants.R));
    intermediateValue <- (PurePrimops.mulmod stateOpening1AtZ stateOpening1AtZ (W256.of_int Constants.R));
    intermediateValue <- (PurePrimops.addmod intermediateValue ((W256.of_int Constants.R) - stateOpening2AtZ) (W256.of_int Constants.R));
    _7 <@ Primops.mload(W256.of_int 3616);
    intermediateValue <- (PurePrimops.mulmod intermediateValue _7 (W256.of_int Constants.R));
    accumulator <- (PurePrimops.addmod accumulator intermediateValue (W256.of_int Constants.R));
    intermediateValue <- (PurePrimops.mulmod stateOpening2AtZ stateOpening0AtZ (W256.of_int Constants.R));
    intermediateValue <- (PurePrimops.addmod intermediateValue ((W256.of_int Constants.R) - stateOpening3AtZ) (W256.of_int Constants.R));
    _10 <@ Primops.mload(W256.of_int 3648);
    intermediateValue <- (PurePrimops.mulmod intermediateValue _10 (W256.of_int Constants.R));
    accumulator <- (PurePrimops.addmod accumulator intermediateValue (W256.of_int Constants.R));
    _12 <@ Primops.mload(W256.of_int 4000);
    accumulator <- (PurePrimops.mulmod accumulator _12 (W256.of_int Constants.R));
    PointMulAndAddIntoDest.low(W256.of_int 1088, accumulator, dest);
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
