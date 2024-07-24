require        Constants.
require import PointMulAndAddIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module UpdateAggregationChallenge_105 = {
  proc low(queriesCommitmentPoint : uint256, valueAtZ_Omega : uint256, previousCoeff : uint256, curAggregationChallenge : uint256, curAggregatedOpeningAtZ_Omega : uint256): (uint256 * uint256) = {
    var newAggregationChallenge, newAggregatedOpeningAtZ_Omega, _3, _5, _6, finalCoeff, tmp375, _8, _9;
    _3 <@ Primops.mload(STATE_V_SLOT);
    newAggregationChallenge <- (PurePrimops.mulmod curAggregationChallenge _3 R_MOD);
    _5 <@ Primops.mload(STATE_U_SLOT);
    _6 <- (PurePrimops.mulmod newAggregationChallenge _5 R_MOD);
    finalCoeff <- (PurePrimops.addmod previousCoeff _6 R_MOD);
    tmp375 <@ PointMulAndAddIntoDest.low(queriesCommitmentPoint, finalCoeff, AGGREGATED_AT_Z_OMEGA_X_SLOT);
    _8 <@ Primops.mload(valueAtZ_Omega);
    _9 <- (PurePrimops.mulmod newAggregationChallenge _8 R_MOD);
    newAggregatedOpeningAtZ_Omega <- (PurePrimops.addmod curAggregatedOpeningAtZ_Omega _9 R_MOD);
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
