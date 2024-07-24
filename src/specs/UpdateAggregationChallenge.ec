require        Constants.
require import PointMulAndAddIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module UpdateAggregationChallenge = {
  proc low(queriesCommitmentPoint : uint256, valueAtZ : uint256, curAggregationChallenge : uint256, curAggregatedOpeningAtZ : uint256): (uint256 * uint256) = {
    var newAggregationChallenge, newAggregatedOpeningAtZ, _3, _5, _6;
    _3 <@ Primops.mload(STATE_V_SLOT);
    newAggregationChallenge <- (PurePrimops.mulmod curAggregationChallenge _3 R_MOD);
    PointMulAndAddIntoDest.low(queriesCommitmentPoint, newAggregationChallenge, AGGREGATED_AT_Z_X_SLOT);
    _5 <@ Primops.mload(valueAtZ);
    _6 <- (PurePrimops.mulmod newAggregationChallenge _5 R_MOD);
    newAggregatedOpeningAtZ <- (PurePrimops.addmod curAggregatedOpeningAtZ _6 R_MOD);
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
