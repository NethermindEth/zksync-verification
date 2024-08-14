pragma Goals:printall.

require import AddAssignPermutationLinearisationContributionWithV.
require import AddAssignRescueCustomGateLinearisationContributionWithV.
require import AddAssignLookupLinearisationContributionWithV.
require import MainGateLinearisationContributionWithV.
require import PointMulAndAddIntoDest.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

module PrepareQueries = {
  proc low(): unit = {
    var _1, zInDomainSize, currentZ, _3, _6, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ, _18, _21, eta', currentEta;
    _1 <- ();
    zInDomainSize <@ Primops.mload(STATE_Z_IN_DOMAIN_SIZE);
    currentZ <- zInDomainSize;
    _3 <@ Primops.mload(PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT);
    Primops.mstore(QUERIES_AT_Z_0_X_SLOT, _3);
    _6 <@ Primops.mload(PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT);
    Primops.mstore(QUERIES_AT_Z_0_Y_SLOT, _6);
    PointMulAndAddIntoDest.low(PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT, zInDomainSize, QUERIES_AT_Z_0_X_SLOT);
    currentZ <- (PurePrimops.mulmod zInDomainSize zInDomainSize R_MOD);
    PointMulAndAddIntoDest.low(PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT, currentZ, QUERIES_AT_Z_0_X_SLOT);
    currentZ <- (PurePrimops.mulmod currentZ zInDomainSize R_MOD);
    PointMulAndAddIntoDest.low(PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT, currentZ, QUERIES_AT_Z_0_X_SLOT);
    stateOpening0AtZ <@ Primops.mload(PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT);
    stateOpening1AtZ <@ Primops.mload(PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT);
    stateOpening2AtZ <@ Primops.mload(PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT);
    stateOpening3AtZ <@ Primops.mload(PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT);
    MainGateLinearisationContributionWithV.low(QUERIES_AT_Z_1_X_SLOT, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ);
    AddAssignRescueCustomGateLinearisationContributionWithV.low(QUERIES_AT_Z_1_X_SLOT, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ);
    AddAssignPermutationLinearisationContributionWithV.low(QUERIES_AT_Z_1_X_SLOT, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ);
    AddAssignLookupLinearisationContributionWithV.low(QUERIES_AT_Z_1_X_SLOT, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ);
    _18 <@ Primops.mload(VK_LOOKUP_TABLE_0_X_SLOT);
    Primops.mstore(QUERIES_T_POLY_AGGREGATED_X_SLOT, _18);
    _21 <@ Primops.mload(VK_LOOKUP_TABLE_0_Y_SLOT);
    Primops.mstore(QUERIES_T_POLY_AGGREGATED_Y_SLOT, _21);
    eta' <@ Primops.mload(STATE_ETA_SLOT);
    currentEta <- eta';
    PointMulAndAddIntoDest.low(VK_LOOKUP_TABLE_1_X_SLOT, eta', QUERIES_T_POLY_AGGREGATED_X_SLOT);
    currentEta <- (PurePrimops.mulmod eta' eta' R_MOD);
    PointMulAndAddIntoDest.low(VK_LOOKUP_TABLE_2_X_SLOT, currentEta, QUERIES_T_POLY_AGGREGATED_X_SLOT);
    currentEta <- (PurePrimops.mulmod currentEta eta' R_MOD);
    PointMulAndAddIntoDest.low(VK_LOOKUP_TABLE_3_X_SLOT, currentEta, QUERIES_T_POLY_AGGREGATED_X_SLOT);
  }

  proc mid(zInDomainSize: int, quotient_poly_part_0: int*int, quotient_poly_part_1: int*int, quotient_poly_part_2: int*int, quotient_poly_part_2: int*int, stateOpening0AtZ: int, stateOpening1AtZ: int, stateOpening2AtZ: int, stateOpening3AtZ: int, vk_lookup_table_0: int*int, vk_lookup_table_1: int*int, vk_lookup_table_2: int*int, vk_lookup_table_3: int*int, state_eta: int): unit = {
    var currentZ, _3, _6, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ, _18, _21, eta', currentEta;
    var query_at_z_0;
    currentZ <- zInDomainSize;
    query_at_z_0 <- quotient_poly_part_0;
    query_at_z_0 <@ PointMulAndAddIntoDest.mid(quotient_poly_part_1.`1 quotient_poly_part_1.`2, zInDomainSize, query_at_z_0.`1, query_at_z_0.`2);
    currentZ <- (zInDomainSize * zInDomainSize) %% Constants.R;
    query_at_z_0 <@ PointMulAndAddIntoDest.mid(quotient_poly_part_2.`1, quotient_poly_part_2.`2, currentZ, query_at_z_0.`1, query_at_z_0.`2);
    currentZ <- (currentZ * zInDomainSize) %% Constants.R;
    query_at_z_0 <@ PointMulAndAddIntoDest.mid(quotient_poly_part_3.`1, quotient_poly_part_3.`2, currentZ, query_at_z_0.`1, query_at_z_0.`2);
    (* todo *)
    MainGateLinearisationContributionWithV.low(QUERIES_AT_Z_1_X_SLOT, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ);
    AddAssignRescueCustomGateLinearisationContributionWithV.low(QUERIES_AT_Z_1_X_SLOT, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ);
    AddAssignPermutationLinearisationContributionWithV.low(QUERIES_AT_Z_1_X_SLOT, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ);
    AddAssignLookupLinearisationContributionWithV.low(QUERIES_AT_Z_1_X_SLOT, stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ);
    (* todo *)

    var query_t_poly_aggregated: int*int;
    query_t_poly_aggregated <- vk_lookup_table_0; 
    currentEta <- state_eta;
    query_t_poly_aggregated <@ PointMulAndAddIntoDest.low(vk_lookup_table_1.`1, vk_lookup_table_1.`2, currentEta, query_t_poly_aggregated.`1, query_t_poly_aggregated.`2);
    currentEta <- (state_eta * state_eta) %% Constants.R;
    query_t_poly_aggregated <@ PointMulAndAddIntoDest.low(vk_lookup_table_2.`1, vk_lookup_table_2.`2, currentEta, query_t_poly_aggregated.`1, query_t_poly_aggregated.`2);
    currentEta <- (currentEta * state_eta) %% Constants.R;
    query_t_poly_aggregated <@ PointMulAndAddIntoDest.low(vk_lookup_table_3.`1, vk_lookup_table_3.`2, currentEta, query_t_poly_aggregated.`1, query_t_poly_aggregated.`2);

    (* todo returns *)
  }
}.

lemma prepareQueries_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_prepareQueries ~ PrepareQueries.low:
      ={arg, glob PrepareQueries} ==>
      ={res, glob PrepareQueries}
    ].
    proof.
      proc.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      inline Primops.mload Primops.mstore. wp.
      call addAssignLookupLinearisationContributionWithV_extracted_equiv_low.
      call addAssignPermutationLinearisationContributionWithV_extracted_equiv_low.
      call addAssignRescueCustomGateLinearisationContributionWithV_extracted_equiv_low.
      call mainGateLinearisationContributionWithV_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      call pointMulAndAddIntoDest_extracted_equiv_low. wp.
      skip. rewrite /Constants.R. by progress.
    qed.

    
