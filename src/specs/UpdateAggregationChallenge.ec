require        Constants.
require import PointMulAndAddIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module UpdateAggregationChallenge = {
  proc low(queriesCommitmentPoint : uint256, valueAtZ : uint256, curAggregationChallenge : uint256, curAggregatedOpeningAtZ : uint256): (uint256 * uint256) = {
    var newAggregationChallenge, newAggregatedOpeningAtZ, _3, _5, _6;
    _3 <@ Primops.mload(W256.of_int 4000);
    newAggregationChallenge <- (PurePrimops.mulmod curAggregationChallenge _3 (W256.of_int Constants.R));
    PointMulAndAddIntoDest.low(queriesCommitmentPoint, newAggregationChallenge, W256.of_int 4480);
    _5 <@ Primops.mload(valueAtZ);
    _6 <- (PurePrimops.mulmod newAggregationChallenge _5 (W256.of_int Constants.R));
    newAggregatedOpeningAtZ <- (PurePrimops.addmod curAggregatedOpeningAtZ _6 (W256.of_int Constants.R));
    return (newAggregationChallenge, newAggregatedOpeningAtZ);
  }
}.

lemma updateAggregationChallenge_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_updateAggregationChallenge ~ UpdateAggregationChallenge.low :
      ={arg, glob UpdateAggregationChallenge} ==>
      ={res, glob UpdateAggregationChallenge}
    ].
proof.
  proc.
  inline Primops.mload. wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  skip. rewrite /Constants.R. by progress.
qed.
