require        Constants.
require import PointMulAndAddIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module UpdateAggregationChallenge_105 = {
  proc low(queriesCommitmentPoint : uint256, valueAtZ_Omega : uint256, previousCoeff : uint256, curAggregationChallenge : uint256, curAggregatedOpeningAtZ_Omega : uint256): (uint256 * uint256) = {
    var newAggregationChallenge, newAggregatedOpeningAtZ_Omega, _3, _5, _6, finalCoeff, tmp375, _8, _9;
    _3 <@ Primops.mload(W256.of_int 4000);
    newAggregationChallenge <- (PurePrimops.mulmod curAggregationChallenge _3 (W256.of_int Constants.R));
    _5 <@ Primops.mload(W256.of_int 4032);
    _6 <- (PurePrimops.mulmod newAggregationChallenge _5 (W256.of_int Constants.R));
    finalCoeff <- (PurePrimops.addmod previousCoeff _6 (W256.of_int Constants.R));
    tmp375 <@ PointMulAndAddIntoDest.low(queriesCommitmentPoint, finalCoeff, W256.of_int 4544);
    _8 <@ Primops.mload(valueAtZ_Omega);
    _9 <- (PurePrimops.mulmod newAggregationChallenge _8 (W256.of_int Constants.R));
    newAggregatedOpeningAtZ_Omega <- (PurePrimops.addmod curAggregatedOpeningAtZ_Omega _9 (W256.of_int Constants.R));
    return (newAggregationChallenge, newAggregatedOpeningAtZ_Omega);
    }
}.

lemma updateAggregationChallenge_105_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_updateAggregationChallenge_105 ~ UpdateAggregationChallenge_105.low :
      ={arg, glob UpdateAggregationChallenge_105} ==>
      ={res, glob UpdateAggregationChallenge_105}
    ].
proof.
  proc.
  inline Primops.mload. wp.
  call (pointMulAndAddIntoDest_extracted_equiv_low). wp.
  skip. rewrite /Constants.R. by progress.
qed.
