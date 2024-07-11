require        Constants.
require import PointAddIntoDest.
require import PointMulIntoDest.
require import PurePrimops.
require import UInt256.
require import UpdateAggregationChallenge.
require import UpdateAggregationChallenge105.
require import Verifier.
require import YulPrimops.

module PrepareAggregatedCommitment = {
  proc low(): unit = {
  var aggregationChallenge, firstDCoeff, firstTCoeff, _2, _5, aggregatedOpeningAtZ, _11, _13, _14, _21, _23, _24, _33, _35, _36, _42, _44, _45, _47, copyPermutationCoeff, _51, aggregatedOpeningAtZOmega, _55, _59, u, _66, _67, _68, aggregatedValue;
    aggregationChallenge <- W256.one;
    _2 <@ Primops.mload(W256.of_int 4288);
    Primops.mstore(W256.of_int 4480, _2);
    _5 <@ Primops.mload(W256.of_int 4320);
    Primops.mstore(W256.of_int 4512, _5);
    aggregatedOpeningAtZ <@ Primops.mload(W256.of_int 3072);
    PointAddIntoDest.low(W256.of_int 4480, W256.of_int 4352, W256.of_int 4480);
    _11 <@ Primops.mload(W256.of_int 4000);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _11 (W256.of_int Constants.R));
    _13 <@ Primops.mload(W256.of_int 3104);
    _14 <- (PurePrimops.mulmod aggregationChallenge _13 (W256.of_int Constants.R));
    aggregatedOpeningAtZ <- (PurePrimops.addmod aggregatedOpeningAtZ _14 (W256.of_int Constants.R));
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(W256.of_int 1856, W256.of_int 2560, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(W256.of_int 1920, W256.of_int 2592, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(W256.of_int 1984, W256.of_int 2624, aggregationChallenge, aggregatedOpeningAtZ);
    _21 <@ Primops.mload(W256.of_int 4000);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _21 (W256.of_int Constants.R));
    firstDCoeff <- aggregationChallenge;
    _23 <@ Primops.mload(W256.of_int 2656);
    _24 <- (PurePrimops.mulmod aggregationChallenge _23 (W256.of_int Constants.R));
    aggregatedOpeningAtZ <- (PurePrimops.addmod aggregatedOpeningAtZ _24 (W256.of_int Constants.R));
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(W256.of_int 1024, W256.of_int 2720, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(W256.of_int 1152, W256.of_int 2752, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(W256.of_int 1216, W256.of_int 2784, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(W256.of_int 1280, W256.of_int 2816, aggregationChallenge, aggregatedOpeningAtZ);
    _33 <@ Primops.mload(W256.of_int 4000);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _33 (W256.of_int Constants.R));
    firstTCoeff <- aggregationChallenge;
    _35 <@ Primops.mload(W256.of_int 2944);
    _36 <- (PurePrimops.mulmod aggregationChallenge _35 (W256.of_int Constants.R));
    aggregatedOpeningAtZ <- (PurePrimops.addmod aggregatedOpeningAtZ _36 (W256.of_int Constants.R));
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(W256.of_int 1408, W256.of_int 3008, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(W256.of_int 1728, W256.of_int 3040, aggregationChallenge, aggregatedOpeningAtZ);
    Primops.mstore(W256.of_int 4608, aggregatedOpeningAtZ);
    _42 <@ Primops.mload(W256.of_int 4000);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _42 (W256.of_int Constants.R));
    _44 <@ Primops.mload(W256.of_int 4032);
    _45 <- (PurePrimops.mulmod aggregationChallenge _44 (W256.of_int Constants.R));
    _47 <@ Primops.mload(W256.of_int 4928);
    copyPermutationCoeff <- (PurePrimops.addmod _47 _45 (W256.of_int Constants.R));
    PointMulIntoDest.low(W256.of_int 2112, copyPermutationCoeff, W256.of_int 4544);
    _51 <@ Primops.mload(W256.of_int 2848);
    aggregatedOpeningAtZOmega <- (PurePrimops.mulmod _51 aggregationChallenge (W256.of_int Constants.R));
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(W256.of_int 2048, W256.of_int 2688, firstDCoeff, aggregationChallenge, aggregatedOpeningAtZOmega);
    _55 <@ Primops.mload(W256.of_int 4992);
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(W256.of_int 2176, W256.of_int 2880, _55, aggregationChallenge, aggregatedOpeningAtZOmega);
    _59 <@ Primops.mload(W256.of_int 4960);
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(W256.of_int 2240, W256.of_int 2912, _59, aggregationChallenge, aggregatedOpeningAtZOmega);
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(W256.of_int 4416, W256.of_int 2976, firstTCoeff, aggregationChallenge, aggregatedOpeningAtZOmega);
    Primops.mstore(W256.of_int 4640, aggregatedOpeningAtZOmega);
    u <@ Primops.mload(W256.of_int 4032);
    PointAddIntoDest.low(W256.of_int 4480, W256.of_int 4544, W256.of_int 4736);
    _66 <@ Primops.mload(W256.of_int 4608);
    _67 <@ Primops.mload(W256.of_int 4640);
    _68 <- (PurePrimops.mulmod _67 u (W256.of_int Constants.R));
    aggregatedValue <- (PurePrimops.addmod _68 _66 (W256.of_int Constants.R));
    Primops.mstore(W256.of_int 4672, W256.one);
    Primops.mstore(W256.of_int 4704, W256.of_int 2);
    PointMulIntoDest.low(W256.of_int 4672, aggregatedValue, W256.of_int 4672);
  }
}.

lemma prepareAggregatedCommitment_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_prepareAggregatedCommitment ~ PrepareAggregatedCommitment.low:
      ={arg, glob PrepareAggregatedCommitment} ==>
      ={res, glob PrepareAggregatedCommitment}
    ].
    proof.
      proc.
      seq 11 5: (#pre /\ _3{1} = W256.of_int 4480 /\ usr_aggregationChallenge{1} = aggregationChallenge{2}). inline*. wp. skip. by progress.
      seq 5 2: (#pre /\ usr_aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2}). inline Primops.mload. sp. call pointAddIntoDest_extracted_equiv_low. skip. by progress.
      seq 22 8: (#pre /\ _9{1} = W256.of_int Constants.R /\ _10{1} = W256.of_int 4000). wp. do 3! (call updateAggregationChallenge_extracted_equiv_low; wp). inline Primops.mload. wp. skip. rewrite /Constants.R. by progress.
      seq 25 10: (#pre /\ usr_firstDCoeff{1} = firstDCoeff{2}). wp. do 4! (call updateAggregationChallenge_extracted_equiv_low; wp). inline*. wp. skip. by progress.
      seq 17 8: (#pre /\ usr_firstTCoeff{1} = firstTCoeff{2} ). wp. do 2! (call updateAggregationChallenge_extracted_equiv_low; wp). inline*. wp. skip. by progress.
      seq 16 8: (#pre /\ _41{1} = W256.of_int 4608 /\ _43{1} = W256.of_int 4032 /\_48{1} = W256.of_int 4544). call pointMulIntoDest_extracted_equiv_low. inline*. wp. skip. by progress.
      seq 26 8: (#pre /\ usr_aggregatedOpeningAtZOmega{1} = aggregatedOpeningAtZOmega{2}). wp. inline Primops.mload. do 4! (call updateAggregationChallenge_105_extracted_equiv_low; wp). skip. by progress.
      call pointMulIntoDest_extracted_equiv_low.
      inline Primops.mstore Primops.mload. wp.
      call pointAddIntoDest_extracted_equiv_low.
      wp. skip. by progress.
    qed.
