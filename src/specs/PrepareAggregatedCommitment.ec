require        Constants.
require import PointAddIntoDest.
require import PointMulIntoDest.
require import PurePrimops.
require import UInt256.
require import UpdateAggregationChallenge.
require import UpdateAggregationChallenge105.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module PrepareAggregatedCommitment = {
  proc low(): unit = {
  var aggregationChallenge, firstDCoeff, firstTCoeff, _2, _5, aggregatedOpeningAtZ, _11, _13, _14, _21, _23, _24, _33, _35, _36, _42, _44, _45, _47, copyPermutationCoeff, _51, aggregatedOpeningAtZOmega, _55, _59, u, _66, _67, _68, aggregatedValue;
    aggregationChallenge <- W256.one;
    _2 <@ Primops.mload(QUERIES_AT_Z_0_X_SLOT);
    Primops.mstore(AGGREGATED_AT_Z_X_SLOT, _2);
    _5 <@ Primops.mload(QUERIES_AT_Z_0_Y_SLOT);
    Primops.mstore(AGGREGATED_AT_Z_Y_SLOT, _5);
    aggregatedOpeningAtZ <@ Primops.mload(PROOF_QUOTIENT_POLY_OPENING_AT_Z_SLOT);
    PointAddIntoDest.low(AGGREGATED_AT_Z_X_SLOT, QUERIES_AT_Z_1_X_SLOT, AGGREGATED_AT_Z_X_SLOT);
    _11 <@ Primops.mload(STATE_V_SLOT);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _11 R_MOD);
    _13 <@ Primops.mload(PROOF_LINEARISATION_POLY_OPENING_AT_Z_SLOT);
    _14 <- (PurePrimops.mulmod aggregationChallenge _13 R_MOD);
    aggregatedOpeningAtZ <- (PurePrimops.addmod aggregatedOpeningAtZ _14 R_MOD);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(PROOF_STATE_POLYS_0_X_SLOT, PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(PROOF_STATE_POLYS_1_X_SLOT, PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(PROOF_STATE_POLYS_2_X_SLOT, PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ);
    _21 <@ Primops.mload(STATE_V_SLOT);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _21 R_MOD);
    firstDCoeff <- aggregationChallenge;
    _23 <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    _24 <- (PurePrimops.mulmod aggregationChallenge _23 R_MOD);
    aggregatedOpeningAtZ <- (PurePrimops.addmod aggregatedOpeningAtZ _24 R_MOD);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_GATE_SELECTORS_0_X_SLOT, PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_PERMUTATION_0_X_SLOT, PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_PERMUTATION_1_X_SLOT, PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_PERMUTATION_2_X_SLOT, PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ);
    _33 <@ Primops.mload(STATE_V_SLOT);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _33 R_MOD);
    firstTCoeff <- aggregationChallenge;
    _35 <@ Primops.mload(PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT);
    _36 <- (PurePrimops.mulmod aggregationChallenge _35 R_MOD);
    aggregatedOpeningAtZ <- (PurePrimops.addmod aggregatedOpeningAtZ _36 R_MOD);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_LOOKUP_SELECTOR_X_SLOT, PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ);
    (aggregationChallenge,aggregatedOpeningAtZ) <@ UpdateAggregationChallenge.low(VK_LOOKUP_TABLE_TYPE_X_SLOT, PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT, aggregationChallenge, aggregatedOpeningAtZ);
    Primops.mstore(AGGREGATED_OPENING_AT_Z_SLOT, aggregatedOpeningAtZ);
    _42 <@ Primops.mload(STATE_V_SLOT);
    aggregationChallenge <- (PurePrimops.mulmod aggregationChallenge _42 R_MOD);
    _44 <@ Primops.mload(STATE_U_SLOT);
    _45 <- (PurePrimops.mulmod aggregationChallenge _44 R_MOD);
    _47 <@ Primops.mload(COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF);
    copyPermutationCoeff <- (PurePrimops.addmod _47 _45 R_MOD);
    PointMulIntoDest.low(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_X_SLOT, copyPermutationCoeff, AGGREGATED_AT_Z_OMEGA_X_SLOT);
    _51 <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    aggregatedOpeningAtZOmega <- (PurePrimops.mulmod _51 aggregationChallenge R_MOD);
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(PROOF_STATE_POLYS_3_X_SLOT, PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT, firstDCoeff, aggregationChallenge, aggregatedOpeningAtZOmega);
    _55 <@ Primops.mload(LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF);
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(PROOF_LOOKUP_S_POLY_X_SLOT, PROOF_LOOKUP_S_POLY_OPENING_AT_Z_OMEGA_SLOT, _55, aggregationChallenge, aggregatedOpeningAtZOmega);
    _59 <@ Primops.mload(LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF);
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(PROOF_LOOKUP_GRAND_PRODUCT_X_SLOT, PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT, _59, aggregationChallenge, aggregatedOpeningAtZOmega);
    (aggregationChallenge,aggregatedOpeningAtZOmega) <@ UpdateAggregationChallenge_105.low(QUERIES_T_POLY_AGGREGATED_X_SLOT, PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT, firstTCoeff, aggregationChallenge, aggregatedOpeningAtZOmega);
    Primops.mstore(AGGREGATED_OPENING_AT_Z_OMEGA_SLOT, aggregatedOpeningAtZOmega);
    u <@ Primops.mload(STATE_U_SLOT);
    PointAddIntoDest.low(AGGREGATED_AT_Z_X_SLOT, AGGREGATED_AT_Z_OMEGA_X_SLOT, PAIRING_PAIR_WITH_GENERATOR_X_SLOT);
    _66 <@ Primops.mload(AGGREGATED_OPENING_AT_Z_SLOT);
    _67 <@ Primops.mload(AGGREGATED_OPENING_AT_Z_OMEGA_SLOT);
    _68 <- (PurePrimops.mulmod _67 u R_MOD);
    aggregatedValue <- (PurePrimops.addmod _68 _66 R_MOD);
    Primops.mstore(PAIRING_BUFFER_POINT_X_SLOT, W256.one);
    Primops.mstore(PAIRING_BUFFER_POINT_Y_SLOT, W256.of_int 2);
    PointMulIntoDest.low(PAIRING_BUFFER_POINT_X_SLOT, aggregatedValue, PAIRING_BUFFER_POINT_X_SLOT);
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
      seq 11 5: (#pre /\ _3{1} = AGGREGATED_AT_Z_X_SLOT /\ usr_aggregationChallenge{1} = aggregationChallenge{2}). inline*. wp. skip. by progress.
      seq 5 2: (#pre /\ usr_aggregatedOpeningAtZ{1} = aggregatedOpeningAtZ{2}). inline Primops.mload. sp. call pointAddIntoDest_extracted_equiv_low. skip. by progress.
      seq 22 8: (#pre /\ _9{1} = R_MOD /\ _10{1} = STATE_V_SLOT). wp. do 3! (call updateAggregationChallenge_extracted_equiv_low; wp). inline Primops.mload. wp. skip. rewrite /Constants.R. by progress.
      seq 25 10: (#pre /\ usr_firstDCoeff{1} = firstDCoeff{2}). wp. do 4! (call updateAggregationChallenge_extracted_equiv_low; wp). inline*. wp. skip. by progress.
      seq 17 8: (#pre /\ usr_firstTCoeff{1} = firstTCoeff{2} ). wp. do 2! (call updateAggregationChallenge_extracted_equiv_low; wp). inline*. wp. skip. by progress.
      seq 16 8: (#pre /\ _41{1} = AGGREGATED_OPENING_AT_Z_SLOT /\ _43{1} = STATE_U_SLOT /\_48{1} = AGGREGATED_AT_Z_OMEGA_X_SLOT). call pointMulIntoDest_extracted_equiv_low. inline*. wp. skip. by progress.
      seq 26 8: (#pre /\ usr_aggregatedOpeningAtZOmega{1} = aggregatedOpeningAtZOmega{2}). wp. inline Primops.mload. do 4! (call updateAggregationChallenge_105_extracted_equiv_low; wp). skip. by progress.
      call pointMulIntoDest_extracted_equiv_low.
      inline Primops.mstore Primops.mload. wp.
      call pointAddIntoDest_extracted_equiv_low.
      wp. skip. by progress.
    qed.
