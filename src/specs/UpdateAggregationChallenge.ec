require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module UpdateAggregationChallenge = {
  proc low(usr_queriesCommitmentPoint : uint256, usr_valueAtZ : uint256, usr_curAggregationChallenge : uint256, usr_curAggregatedOpeningAtZ : uint256): (uint256 * uint256) = {
    var usr_newAggregationChallenge, usr_newAggregatedOpeningAtZ, _1, _2, _3, tmp370, _4, tmp371, _5, tmp372, _6;
    _1 <- (W256.of_int 21888242871839275222246405745257275088548364400416034343698204186575808495617);
    _2 <- (W256.of_int 4000);
    tmp370 <@ Primops.mload(_2);
    _3 <- tmp370;
    usr_newAggregationChallenge <- (PurePrimops.mulmod usr_curAggregationChallenge _3 _1);
    _4 <- (W256.of_int 4480);
    tmp371 <@ usr_pointMulAndAddIntoDest(usr_queriesCommitmentPoint, usr_newAggregationChallenge, _4);
    tmp372 <@ Primops.mload(usr_valueAtZ);
    _5 <- tmp372;
    _6 <- (PurePrimops.mulmod usr_newAggregationChallenge _5 _1);
    usr_newAggregatedOpeningAtZ <- (PurePrimops.addmod usr_curAggregatedOpeningAtZ _6 _1);
    return (usr_newAggregationChallenge, usr_newAggregatedOpeningAtZ);
    }
}.

lemma addAssignRescueCustomGateLinearisationContributionWithV_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_updateAggregationChallenge ~ AddAssignRescueCustomGateLinearisationContributionWithV.low :
      ={arg, glob AddAssignRescueCustomGateLinearisationContributionWithV} ==>
      ={res, glob AddAssignRescueCustomGateLinearisationContributionWithV}
    ].
proof.
  proc.
  call (pointMulAndAddIntoDest_extracted_equiv_low).
  inline*. wp. skip. rewrite /Constants.R. by progress.
qed.
