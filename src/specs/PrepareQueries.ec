pragma Goals:printall.

require import AddAssignPermutationLinearisationContributionWithV.
require import AddAssignRescueCustomGateLinearisationContributionWithV.
require import AddAssignLookupLinearisationContributionWithV.
require import EllipticCurve.
require import Field.
require import MainGateLinearisationContributionWithV.
require import PointAddAssign.
require import PointAddIntoDest.
require import PointMulIntoDest.
require import PointMulAndAddIntoDest.
require import PointNegate.
require import PointSubAssign.
require import PurePrimops.
require import UInt256.
require import Utils.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

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

  proc mid(
    zInDomainSize: int,
    quotient_poly_part_0: int*int,
    quotient_poly_part_1: int*int,
    quotient_poly_part_2: int*int,
    quotient_poly_part_3: int*int,
    stateOpening0AtZ: int,
    stateOpening1AtZ: int,
    stateOpening2AtZ: int,
    stateOpening3AtZ: int,
    vk_lookup_table_0: int*int,
    vk_lookup_table_1: int*int,
    vk_lookup_table_2: int*int,
    vk_lookup_table_3: int*int,
    state_eta: int,
    vk_gate_setup_0: int*int,
    vk_gate_setup_1: int*int,
    vk_gate_setup_2: int*int,
    vk_gate_setup_3: int*int,
    vk_gate_setup_4: int*int,
    vk_gate_setup_5: int*int,
    vk_gate_setup_6: int*int,
    vk_gate_setup_7: int*int,
    poly3_omega: int,
    v: int,
    z: int,
    gate_selector_0_opening: int,
    alpha: int,
    alpha2: int,
    alpha3: int,
    alpha4: int,
    alpha5: int,
    alpha6: int,
    alpha7: int,
    alpha8: int,
    state_beta: int,
    gamma: int,
    vk_gate_selector_1: int*int,
    vk_permutation_3: int*int,
    gp_omega: int,
    l0AtZ: int,
    poly0_opening: int,
    poly1_opening: int,
    poly2_opening: int,
    proofLookupGrandProductOpeningAtZOmega: int,
    zMinusLastOmega: int,
    proofLookupTPolyOpeningAtZOmega: int,
    betaLookup: int,
    proofLookupTPolyOpeningAtZ: int,
    betaGammaPlusGamma: int,
    proofLookupTableTypePolyOpeningAtZ: int,
    proofLookupSelectorPolyOpeningAtZ: int,
    gammaLookup: int,
    betaPlusOne: int,
    lNMinusOneAtZ: int
  ): ((int*int) * (int*int) * int * int * int * (int*int)) option = {
      var currentEta, currentZ: int;
      var query_at_z_0, query_t_poly_aggregated, query_at_z_1: int*int;
      var query_at_z_0_opt, query_t_poly_aggregated_opt, query_at_z_1_opt: (int*int) option;
      var failed: bool;
      var result: (int * (int*int)) option;
      var copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient: int;
      var ret;
      failed <- false;

      query_at_z_0 <- quotient_poly_part_0;
      query_at_z_0_opt <@ PointMulAndAddIntoDest.mid(
        quotient_poly_part_1.`1, quotient_poly_part_1.`2,
        zInDomainSize,
        query_at_z_0.`1, query_at_z_0.`2
      );
      failed <- failed \/ is_none query_at_z_0_opt;
      query_at_z_0 <- odflt (0,0) query_at_z_0_opt;

    
      currentZ <- (zInDomainSize * zInDomainSize) %% Constants.R;
      query_at_z_0_opt <@ PointMulAndAddIntoDest.mid(
        quotient_poly_part_2.`1, quotient_poly_part_2.`2,
        currentZ,
        query_at_z_0.`1, query_at_z_0.`2
      );
      failed <- failed \/ is_none query_at_z_0_opt;
      query_at_z_0 <- odflt (0,0) query_at_z_0_opt;

    
      currentZ <- (currentZ * zInDomainSize) %% Constants.R;
      query_at_z_0_opt <@ PointMulAndAddIntoDest.mid(
        quotient_poly_part_3.`1, quotient_poly_part_3.`2,
        currentZ,
        query_at_z_0.`1, query_at_z_0.`2
      );
      failed <- failed \/ is_none query_at_z_0_opt;
      query_at_z_0 <- odflt (0,0) query_at_z_0_opt;


      query_at_z_1_opt <@ MainGateLinearisationContributionWithV.mid(
        vk_gate_setup_0, vk_gate_setup_1, vk_gate_setup_2, vk_gate_setup_3, vk_gate_setup_4, vk_gate_setup_5, vk_gate_setup_6, vk_gate_setup_7,
        stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ,
        poly3_omega, v, gate_selector_0_opening
      );
      failed <- failed \/ is_none query_at_z_1_opt;
      query_at_z_1 <- odflt (0,0) query_at_z_1_opt;

      query_at_z_1_opt <@ AddAssignRescueCustomGateLinearisationContributionWithV.mid (
        query_at_z_1,
        stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ,
        alpha, alpha2, alpha3, v,
        vk_gate_selector_1
      );
      failed <- failed \/ is_none query_at_z_1_opt;
      query_at_z_1 <- odflt (0,0) query_at_z_1_opt;
  
      result <@ AddAssignPermutationLinearisationContributionWithV.mid(
        query_at_z_1, vk_permutation_3,
        stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ,
        state_beta, v, z, gamma, alpha4, alpha5, gp_omega, l0AtZ,
        poly0_opening, poly1_opening, poly2_opening
      );
      failed <- failed \/ is_none result;
      (copy_permutation_first_aggregated_commitment_coeff, query_at_z_1) <- odflt (0,(0,0)) result;

      (lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient) <@ AddAssignLookupLinearisationContributionWithV.mid(
        stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ,
        proofLookupGrandProductOpeningAtZOmega,
        alpha6,
        zMinusLastOmega,
        v,
        proofLookupTPolyOpeningAtZOmega,
        betaLookup,
        proofLookupTPolyOpeningAtZ,
        betaGammaPlusGamma,
        state_eta,
        proofLookupTableTypePolyOpeningAtZ,
        proofLookupSelectorPolyOpeningAtZ,
        gammaLookup,
        betaPlusOne,
        alpha7,
        l0AtZ,
        alpha8,
        lNMinusOneAtZ
      );
    

      query_t_poly_aggregated <- vk_lookup_table_0;
      currentEta <- state_eta;
      query_t_poly_aggregated_opt <@ PointMulAndAddIntoDest.mid(vk_lookup_table_1.`1, vk_lookup_table_1.`2, currentEta, query_t_poly_aggregated.`1, query_t_poly_aggregated.`2);
      failed <- failed \/ is_none query_t_poly_aggregated_opt;
      query_t_poly_aggregated <- odflt (0,0) query_t_poly_aggregated_opt;

      currentEta <- (state_eta * state_eta) %% Constants.R;
      query_t_poly_aggregated_opt <@ PointMulAndAddIntoDest.mid(vk_lookup_table_2.`1, vk_lookup_table_2.`2, currentEta, query_t_poly_aggregated.`1, query_t_poly_aggregated.`2);
      failed <- failed \/ is_none query_t_poly_aggregated_opt;
      query_t_poly_aggregated <- odflt (0,0) query_t_poly_aggregated_opt;

      currentEta <- (currentEta * state_eta) %% Constants.R;
      query_t_poly_aggregated_opt <@ PointMulAndAddIntoDest.mid(vk_lookup_table_3.`1, vk_lookup_table_3.`2, currentEta, query_t_poly_aggregated.`1, query_t_poly_aggregated.`2);
      failed <- failed \/ is_none query_t_poly_aggregated_opt;
      query_t_poly_aggregated <- odflt (0,0) query_t_poly_aggregated_opt;
        
      if (failed) {
        ret <- None;
      } else {
        ret <- Some(
          query_at_z_0,
          query_at_z_1,
          copy_permutation_first_aggregated_commitment_coeff,
          lookupSFirstAggregatedCommitment,
          lookupGrandProductFirstAggregatedCoefficient,
          query_t_poly_aggregated
        );
      }
      return ret;
  }

  proc high_encapsulated(
    zInDomainSize: FieldR.F,
    quotient_poly_part_0: g,
    quotient_poly_part_1: g,
    quotient_poly_part_2: g,
    quotient_poly_part_3: g,
    stateOpening0AtZ: FieldR.F,
    stateOpening1AtZ: FieldR.F,
    stateOpening2AtZ: FieldR.F,
    stateOpening3AtZ: FieldR.F,
    vk_lookup_table_0: g,
    vk_lookup_table_1: g,
    vk_lookup_table_2: g,
    vk_lookup_table_3: g,
    state_eta: FieldR.F,
    vk_gate_setup_0: g,
    vk_gate_setup_1: g,
    vk_gate_setup_2: g,
    vk_gate_setup_3: g,
    vk_gate_setup_4: g,
    vk_gate_setup_5: g,
    vk_gate_setup_6: g,
    vk_gate_setup_7: g,
    poly3_omega: FieldR.F,
    v: FieldR.F,
    z: FieldR.F,
    gate_selector_0_opening: FieldR.F,
    alpha: FieldR.F,
    alpha2: FieldR.F,
    alpha3: FieldR.F,
    alpha4: FieldR.F,
    alpha5: FieldR.F,
    alpha6: FieldR.F,
    alpha7: FieldR.F,
    alpha8: FieldR.F,
    state_beta: FieldR.F,
    gamma: FieldR.F,
    vk_gate_selector_1: g,
    vk_permutation_3: g,
    gp_omega: FieldR.F,
    l0AtZ: FieldR.F,
    poly0_opening: FieldR.F,
    poly1_opening: FieldR.F,
    poly2_opening: FieldR.F,
    proofLookupGrandProductOpeningAtZOmega: FieldR.F,
    zMinusLastOmega: FieldR.F,
    proofLookupTPolyOpeningAtZOmega: FieldR.F,
    betaLookup: FieldR.F,
    proofLookupTPolyOpeningAtZ: FieldR.F,
    betaGammaPlusGamma: FieldR.F,
    proofLookupTableTypePolyOpeningAtZ: FieldR.F,
    proofLookupSelectorPolyOpeningAtZ: FieldR.F,
    gammaLookup: FieldR.F,
    betaPlusOne: FieldR.F,
    lNMinusOneAtZ: FieldR.F
  ): (g * g * FieldR.F * FieldR.F * FieldR.F * g) = {
      var currentEta, currentZ: FieldR.F;
      var query_at_z_0, query_t_poly_aggregated, query_at_z_1: g;
      var copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient: FieldR.F;

      query_at_z_0 <- quotient_poly_part_0;
      query_at_z_0 <@ PointMulAndAddIntoDest.high(
        quotient_poly_part_1,
        zInDomainSize,
        query_at_z_0
      );

    
      currentZ <- zInDomainSize * zInDomainSize;
      query_at_z_0 <@ PointMulAndAddIntoDest.high(
        quotient_poly_part_2,
        currentZ,
        query_at_z_0
      );

    
      currentZ <- currentZ * zInDomainSize;
      query_at_z_0 <@ PointMulAndAddIntoDest.high(
        quotient_poly_part_3,
        currentZ,
        query_at_z_0
      );


      query_at_z_1 <@ MainGateLinearisationContributionWithV.high(
        vk_gate_setup_0, vk_gate_setup_1, vk_gate_setup_2, vk_gate_setup_3, vk_gate_setup_4, vk_gate_setup_5, vk_gate_setup_6, vk_gate_setup_7,
        stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ,
        poly3_omega, v, gate_selector_0_opening
      );

      query_at_z_1 <@ AddAssignRescueCustomGateLinearisationContributionWithV.high (
        query_at_z_1,
        stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ,
        alpha, alpha2, alpha3, v,
        vk_gate_selector_1
      );
  
      (copy_permutation_first_aggregated_commitment_coeff, query_at_z_1) <@ AddAssignPermutationLinearisationContributionWithV.high(
        query_at_z_1, vk_permutation_3,
        stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ, stateOpening3AtZ,
        state_beta, v, z, gamma, alpha4, alpha5, gp_omega, l0AtZ,
        poly0_opening, poly1_opening, poly2_opening
      );

      (lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient) <@ AddAssignLookupLinearisationContributionWithV.high(
        stateOpening0AtZ, stateOpening1AtZ, stateOpening2AtZ,
        proofLookupGrandProductOpeningAtZOmega,
        alpha6,
        zMinusLastOmega,
        v,
        proofLookupTPolyOpeningAtZOmega,
        betaLookup,
        proofLookupTPolyOpeningAtZ,
        betaGammaPlusGamma,
        state_eta,
        proofLookupTableTypePolyOpeningAtZ,
        proofLookupSelectorPolyOpeningAtZ,
        gammaLookup,
        betaPlusOne,
        alpha7,
        l0AtZ,
        alpha8,
        lNMinusOneAtZ
      );
    

      query_t_poly_aggregated <- vk_lookup_table_0;
      currentEta <- state_eta;
      query_t_poly_aggregated <@ PointMulAndAddIntoDest.high(vk_lookup_table_1, currentEta, query_t_poly_aggregated);

      currentEta <- state_eta * state_eta;
      query_t_poly_aggregated <@ PointMulAndAddIntoDest.high(vk_lookup_table_2, currentEta, query_t_poly_aggregated);

      currentEta <- currentEta * state_eta;
      query_t_poly_aggregated <@ PointMulAndAddIntoDest.high(vk_lookup_table_3, currentEta, query_t_poly_aggregated);
        
      return (
        query_at_z_0,
        query_at_z_1,
        copy_permutation_first_aggregated_commitment_coeff,
        lookupSFirstAggregatedCommitment,
        lookupGrandProductFirstAggregatedCoefficient,
        query_t_poly_aggregated
      );
  }

  proc high(
    zInDomainSize: FieldR.F,
    quotient_poly_part_0: g,
    quotient_poly_part_1: g,
    quotient_poly_part_2: g,
    quotient_poly_part_3: g,
    stateOpening0AtZ: FieldR.F,
    stateOpening1AtZ: FieldR.F,
    stateOpening2AtZ: FieldR.F,
    stateOpening3AtZ: FieldR.F,
    vk_lookup_table_0: g,
    vk_lookup_table_1: g,
    vk_lookup_table_2: g,
    vk_lookup_table_3: g,
    state_eta: FieldR.F,
    vk_gate_setup_0: g,
    vk_gate_setup_1: g,
    vk_gate_setup_2: g,
    vk_gate_setup_3: g,
    vk_gate_setup_4: g,
    vk_gate_setup_5: g,
    vk_gate_setup_6: g,
    vk_gate_setup_7: g,
    poly3_omega: FieldR.F,
    v: FieldR.F,
    z: FieldR.F,
    gate_selector_0_opening: FieldR.F,
    alpha: FieldR.F,
    alpha2: FieldR.F,
    alpha3: FieldR.F,
    alpha4: FieldR.F,
    alpha5: FieldR.F,
    alpha6: FieldR.F,
    alpha7: FieldR.F,
    alpha8: FieldR.F,
    state_beta: FieldR.F,
    gamma: FieldR.F,
    vk_gate_selector_1: g,
    vk_permutation_3: g,
    gp_omega: FieldR.F,
    l0AtZ: FieldR.F,
    poly0_opening: FieldR.F,
    poly1_opening: FieldR.F,
    poly2_opening: FieldR.F,
    proofLookupGrandProductOpeningAtZOmega: FieldR.F,
    zMinusLastOmega: FieldR.F,
    proofLookupTPolyOpeningAtZOmega: FieldR.F,
    betaLookup: FieldR.F,
    proofLookupTPolyOpeningAtZ: FieldR.F,
    betaGammaPlusGamma: FieldR.F,
    proofLookupTableTypePolyOpeningAtZ: FieldR.F,
    proofLookupSelectorPolyOpeningAtZ: FieldR.F,
    gammaLookup: FieldR.F,
    betaPlusOne: FieldR.F,
    lNMinusOneAtZ: FieldR.F
  ): (g * g * FieldR.F * FieldR.F * FieldR.F * g) = {
      var query_at_z_0, query_t_poly_aggregated, query_at_z_1: g;
      var copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient: FieldR.F;

      query_at_z_0 <- 
        quotient_poly_part_0 +
        (zInDomainSize * quotient_poly_part_1) +
        ((zInDomainSize * zInDomainSize) * quotient_poly_part_2) +
        ((zInDomainSize * zInDomainSize * zInDomainSize) * quotient_poly_part_3);

  
      copy_permutation_first_aggregated_commitment_coeff <- (
        alpha4 * (z * state_beta + gamma + stateOpening0AtZ) *
        (z * state_beta * (FieldR.inF Constants.NON_RESIDUE_0) + gamma + stateOpening1AtZ) *
        (z * state_beta * (FieldR.inF Constants.NON_RESIDUE_1) + gamma + stateOpening2AtZ) *
        (z * state_beta * (FieldR.inF Constants.NON_RESIDUE_2) + gamma + stateOpening3AtZ) +
        l0AtZ * alpha5
      ) * v;


      query_at_z_1 <- (((
        ((stateOpening0AtZ * stateOpening0AtZ - stateOpening1AtZ) * alpha) +
        ((stateOpening1AtZ * stateOpening1AtZ - stateOpening2AtZ) * alpha2) +
        ((stateOpening2AtZ * stateOpening0AtZ - stateOpening3AtZ) * alpha3)
      ) * v) * vk_gate_selector_1) + ((v * gate_selector_0_opening) * (
        (stateOpening0AtZ * vk_gate_setup_0) +
        (stateOpening1AtZ * vk_gate_setup_1) +
        (stateOpening2AtZ * vk_gate_setup_2) +
        (stateOpening3AtZ * vk_gate_setup_3) +
        ((stateOpening0AtZ * stateOpening1AtZ) * vk_gate_setup_4) +
        ((stateOpening0AtZ * stateOpening2AtZ) * vk_gate_setup_5) +
        vk_gate_setup_6 +
        (poly3_omega * vk_gate_setup_7)
      )) + (G.inv ((
        alpha4 * state_beta * gp_omega *
        (poly0_opening * state_beta + gamma + stateOpening0AtZ) *
        (poly1_opening * state_beta + gamma + stateOpening1AtZ) *
        (poly2_opening * state_beta + gamma + stateOpening2AtZ) *
        v
      ) * vk_permutation_3));


      lookupSFirstAggregatedCommitment <- v * zMinusLastOmega * alpha6 * proofLookupGrandProductOpeningAtZOmega;
      lookupGrandProductFirstAggregatedCoefficient 
            <- ((- (proofLookupTPolyOpeningAtZOmega * betaLookup +
            proofLookupTPolyOpeningAtZ + betaGammaPlusGamma) *
            ((stateOpening0AtZ + state_eta * stateOpening1AtZ +
              state_eta * state_eta * stateOpening2AtZ +
              state_eta * state_eta * state_eta * proofLookupTableTypePolyOpeningAtZ) *
            proofLookupSelectorPolyOpeningAtZ + gammaLookup)) *
        betaPlusOne * alpha6 * zMinusLastOmega + alpha7 * l0AtZ +
        alpha8 * lNMinusOneAtZ) *
          v;
    

      query_t_poly_aggregated <-
        vk_lookup_table_0 +
        (state_eta * vk_lookup_table_1) +
        (state_eta * state_eta) * vk_lookup_table_2 +
        (state_eta * state_eta * state_eta) * vk_lookup_table_3;
        
      return (
        query_at_z_0,
        query_at_z_1,
        copy_permutation_first_aggregated_commitment_coeff,
        lookupSFirstAggregatedCommitment,
        lookupGrandProductFirstAggregatedCoefficient,
        query_t_poly_aggregated
      );
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

op prepareQueries_memory_footprint
  (mem_0: mem)
  (x0 x32 x64 x96 buffer_x buffer_y: uint256)
  (query_at_z_0 query_at_z_1 query_t_poly_aggregated: (int*int))
  (copy_permutation_first_aggregated_commitment_coeff lookupSFirstAggregatedCommitment lookupGrandProductFirstAggregatedCoefficient: int) =
  (* scratch space *)
  let mem_1 = store mem_0 W256.zero x0 in
  let mem_2 = store mem_1 (W256.of_int 32) x32 in
  let mem_3 = store mem_2 (W256.of_int 64) x64 in
  let mem_4 = store mem_3 (W256.of_int 96) x96 in
  let mem_5 = store mem_4 QUERIES_BUFFER_POINT_SLOT buffer_x in
  let mem_6 = store mem_5 (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32) buffer_y in
  (* important stuff *)
  let mem_7 = store mem_6 QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0.`1) in
  let mem_8 = store mem_7 QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0.`2) in
  let mem_9 = store mem_8 QUERIES_AT_Z_1_X_SLOT (W256.of_int query_at_z_1.`1) in
  let mem_10 = store mem_9 QUERIES_AT_Z_1_Y_SLOT (W256.of_int query_at_z_1.`2) in
  let mem_11 = store mem_10 COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int copy_permutation_first_aggregated_commitment_coeff) in
  let mem_12 = store mem_11 LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int lookupSFirstAggregatedCommitment) in
  let mem_13 = store mem_12 LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int lookupGrandProductFirstAggregatedCoefficient) in
  let mem_14 = store mem_13 QUERIES_T_POLY_AGGREGATED_X_SLOT (W256.of_int query_t_poly_aggregated.`1) in
  store mem_14 QUERIES_T_POLY_AGGREGATED_Y_SLOT (W256.of_int query_t_poly_aggregated.`2).

lemma prepareQueries_low_equiv_mid (mem_0: mem):
equiv [
    PrepareQueries.low ~ PrepareQueries.mid:
    !Primops.reverted{1} /\
    Primops.memory{1} = mem_0 /\
    zInDomainSize{2} = W256.to_uint (load mem_0 STATE_Z_IN_DOMAIN_SIZE) /\
    quotient_poly_part_0{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT) /\
    quotient_poly_part_0{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT) /\
    quotient_poly_part_1{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT) /\
    quotient_poly_part_1{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT) /\
    quotient_poly_part_2{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT) /\
    quotient_poly_part_2{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT) /\
    quotient_poly_part_3{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT) /\
    quotient_poly_part_3{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT) /\
    stateOpening0AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) /\
    stateOpening1AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) /\
    stateOpening2AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) /\
    stateOpening3AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) /\
    vk_gate_setup_0{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_X_SLOT) /\
    vk_gate_setup_0{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_Y_SLOT) /\
    vk_gate_setup_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_X_SLOT) /\
    vk_gate_setup_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_Y_SLOT) /\
    vk_gate_setup_2{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_X_SLOT) /\
    vk_gate_setup_2{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_Y_SLOT) /\
    vk_gate_setup_3{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_X_SLOT) /\
    vk_gate_setup_3{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_Y_SLOT) /\
    vk_gate_setup_4{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_X_SLOT) /\
    vk_gate_setup_4{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_Y_SLOT) /\
    vk_gate_setup_5{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_X_SLOT) /\
    vk_gate_setup_5{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_Y_SLOT) /\
    vk_gate_setup_6{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_X_SLOT) /\
    vk_gate_setup_6{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_Y_SLOT) /\
    vk_gate_setup_7{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_X_SLOT) /\
    vk_gate_setup_7{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_Y_SLOT) /\
    poly3_omega{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
    v{2} = W256.to_uint (load mem_0 STATE_V_SLOT) /\
    gate_selector_0_opening{2} = W256.to_uint (load mem_0 PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
    vk_gate_selector_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_X_SLOT) /\
    vk_gate_selector_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_Y_SLOT) /\
    alpha{2} = W256.to_uint (load mem_0 STATE_ALPHA_SLOT) /\
    alpha2{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_2_SLOT) /\
    alpha3{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_3_SLOT) /\
    state_beta{2} = W256.to_uint (load mem_0 STATE_BETA_SLOT) /\
    vk_permutation_3{2}.`1 = W256.to_uint (load mem_0 VK_PERMUTATION_3_X_SLOT) /\
    vk_permutation_3{2}.`2 = W256.to_uint (load mem_0 VK_PERMUTATION_3_Y_SLOT) /\
    state_beta{2} = W256.to_uint (load mem_0 STATE_BETA_SLOT) /\
    z{2} = W256.to_uint (load mem_0 STATE_Z_SLOT) /\
    gamma{2} = W256.to_uint (load mem_0 STATE_GAMMA_SLOT) /\
    alpha4{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_4_SLOT) /\
    alpha5{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_5_SLOT) /\
    gp_omega{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
    l0AtZ{2} = W256.to_uint (load mem_0 STATE_L_0_AT_Z_SLOT) /\
    poly0_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) /\
    poly1_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) /\
    poly2_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) /\
    proofLookupGrandProductOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
    alpha6{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_6_SLOT) /\
    zMinusLastOmega{2} = W256.to_uint(load mem_0 STATE_Z_MINUS_LAST_OMEGA_SLOT) /\
    proofLookupTPolyOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) /\
    betaLookup{2} = W256.to_uint(load mem_0 STATE_BETA_LOOKUP_SLOT) /\
    proofLookupTPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) /\
    betaGammaPlusGamma{2} = W256.to_uint(load mem_0 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) /\
    state_eta{2} = W256.to_uint(load mem_0 STATE_ETA_SLOT) /\
    proofLookupTableTypePolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) /\
    proofLookupSelectorPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) /\
    gammaLookup{2} = W256.to_uint(load mem_0 STATE_GAMMA_LOOKUP_SLOT) /\
    betaPlusOne{2} = W256.to_uint(load mem_0 STATE_BETA_PLUS_ONE_SLOT) /\
    alpha7{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_7_SLOT) /\
    alpha8{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_8_SLOT) /\
    lNMinusOneAtZ{2} = W256.to_uint(load mem_0 STATE_L_N_MINUS_ONE_AT_Z_SLOT) /\
    vk_lookup_table_0{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_X_SLOT) /\
    vk_lookup_table_0{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_Y_SLOT) /\
    vk_lookup_table_1{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_X_SLOT) /\
    vk_lookup_table_1{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_Y_SLOT) /\
    vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
    vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
    vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
    vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
    vk_permutation_3{2}.`1 < Constants.Q /\
    vk_permutation_3{2}.`2 < Constants.Q /\
    vk_gate_setup_0{2}.`1 < FieldQ.p /\
    vk_gate_setup_0{2}.`2 < FieldQ.p /\
    vk_gate_setup_1{2}.`1 < FieldQ.p /\
    vk_gate_setup_1{2}.`2 < FieldQ.p /\
    vk_gate_setup_2{2}.`1 < FieldQ.p /\
    vk_gate_setup_2{2}.`2 < FieldQ.p /\
    vk_gate_setup_3{2}.`1 < FieldQ.p /\
    vk_gate_setup_3{2}.`2 < FieldQ.p /\
    vk_gate_setup_4{2}.`1 < FieldQ.p /\
    vk_gate_setup_4{2}.`2 < FieldQ.p /\
    vk_gate_setup_5{2}.`1 < FieldQ.p /\
    vk_gate_setup_5{2}.`2 < FieldQ.p /\
    vk_gate_setup_6{2}.`1 < FieldQ.p /\
    vk_gate_setup_6{2}.`2 < FieldQ.p /\
    vk_gate_setup_7{2}.`1 < FieldQ.p /\
    vk_gate_setup_7{2}.`2 < FieldQ.p /\
    0 <= quotient_poly_part_0{2}.`1 < FieldQ.p /\
    0 <= quotient_poly_part_0{2}.`2 < FieldQ.p /\
    0 <= quotient_poly_part_1{2}.`1 < FieldQ.p /\
    0 <= quotient_poly_part_1{2}.`2 < FieldQ.p /\
    0 <= quotient_poly_part_2{2}.`1 < FieldQ.p /\
    0 <= quotient_poly_part_2{2}.`2 < FieldQ.p /\
    0 <= quotient_poly_part_3{2}.`1 < FieldQ.p /\
    0 <= quotient_poly_part_3{2}.`2 < FieldQ.p /\
    0 <= vk_lookup_table_0{2}.`1 < FieldQ.p /\
    0 <= vk_lookup_table_0{2}.`2 < FieldQ.p /\
    0 <= vk_lookup_table_1{2}.`1 < FieldQ.p /\
    0 <= vk_lookup_table_1{2}.`2 < FieldQ.p /\
    0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
    0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
    0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
    0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
    0 <= vk_gate_selector_1{2}.`1 < Constants.Q /\
    0 <= vk_gate_selector_1{2}.`2 < Constants.Q /\
    stateOpening0AtZ{2} < Constants.R /\ 
    stateOpening1AtZ{2} < Constants.R /\ 
    stateOpening2AtZ{2} < Constants.R /\ 
    stateOpening3AtZ{2} < Constants.R /\
    0 <= proofLookupGrandProductOpeningAtZOmega{2} < Constants.R /\
    0 <= alpha6{2} < Constants.R /\
    0 <= zMinusLastOmega{2} < Constants.R /\
    0 <= v{2} < Constants.R /\
    0 <= proofLookupTPolyOpeningAtZOmega{2} < Constants.R /\
    0 <= betaLookup{2} < Constants.R /\
    0 <= betaGammaPlusGamma{2} < Constants.R /\
    0 <= state_eta{2} < Constants.R /\
    0 <= proofLookupTableTypePolyOpeningAtZ{2} < Constants.R /\
    0 <= proofLookupSelectorPolyOpeningAtZ{2} < Constants.R /\
    0 <= gammaLookup{2} < Constants.R /\
    0 <= betaPlusOne{2} < Constants.R /\
    0 <= alpha7{2} < Constants.R /\
    0 <= alpha8{2} < Constants.R /\
    0 <= l0AtZ{2} < Constants.R /\
    0 <= lNMinusOneAtZ{2} < Constants.R ==>
    (Primops.reverted{1} /\ res{2} = None) \/
    (
      !Primops.reverted{1} /\
      exists (x0 x32 x64 x96 buffer_x buffer_y: uint256),
      exists (query_at_z_0 query_at_z_1 query_t_poly_aggregated: int*int),
      exists (copy_permutation_first_aggregated_commitment_coeff lookupSFirstAggregatedCommitment lookupGrandProductFirstAggregatedCoefficient: int),
      Primops.memory{1} = prepareQueries_memory_footprint
        mem_0
        x0 x32 x64 x96 buffer_x buffer_y
        query_at_z_0 query_at_z_1 query_t_poly_aggregated
        copy_permutation_first_aggregated_commitment_coeff lookupSFirstAggregatedCommitment lookupGrandProductFirstAggregatedCoefficient /\
      res{2} = Some(
        query_at_z_0,
        query_at_z_1,
        copy_permutation_first_aggregated_commitment_coeff,
        lookupSFirstAggregatedCommitment,
        lookupGrandProductFirstAggregatedCoefficient,
        query_t_poly_aggregated
      ) /\
      0 <= query_at_z_0.`1 < FieldQ.p /\
      0 <= query_at_z_0.`2 < FieldQ.p /\
      0 <= query_at_z_1.`1 < FieldQ.p /\
      0 <= query_at_z_1.`2 < FieldQ.p /\
      0 <= query_t_poly_aggregated.`1 < FieldQ.p /\
      0 <= query_t_poly_aggregated.`2 < FieldQ.p /\
      0 <= copy_permutation_first_aggregated_commitment_coeff < FieldR.p /\
      0 <= lookupSFirstAggregatedCommitment < FieldR.p /\
      0 <= lookupGrandProductFirstAggregatedCoefficient < FieldR.p
    )
    ].
    proof.
      proc.
      seq 7 0: (
        !Primops.reverted{1} /\
        Primops.memory{1} = store(store mem_0 QUERIES_AT_Z_0_X_SLOT (W256.of_int quotient_poly_part_0{2}.`1)) QUERIES_AT_Z_0_Y_SLOT (W256.of_int quotient_poly_part_0{2}.`2) /\
        currentZ{1} = zInDomainSize{1} /\
        zInDomainSize{2} = W256.to_uint zInDomainSize{1} /\
        0 <= quotient_poly_part_0{2}.`1 < FieldQ.p /\
        0 <= quotient_poly_part_0{2}.`2 < FieldQ.p /\
        0 <= quotient_poly_part_1{2}.`1 < FieldQ.p /\
        0 <= quotient_poly_part_1{2}.`2 < FieldQ.p /\
        0 <= quotient_poly_part_2{2}.`1 < FieldQ.p /\
        0 <= quotient_poly_part_2{2}.`2 < FieldQ.p /\
        0 <= quotient_poly_part_3{2}.`1 < FieldQ.p /\
        0 <= quotient_poly_part_3{2}.`2 < FieldQ.p /\
        quotient_poly_part_0{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_0_X_SLOT) /\
        quotient_poly_part_0{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT) /\
        quotient_poly_part_1{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT) /\
        quotient_poly_part_1{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_1_Y_SLOT) /\
        quotient_poly_part_2{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT) /\
        quotient_poly_part_2{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT) /\
        quotient_poly_part_3{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT) /\
        quotient_poly_part_3{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT) /\
        stateOpening0AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) /\
        stateOpening1AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) /\
        stateOpening2AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) /\
        stateOpening3AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) /\
        vk_gate_setup_0{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_X_SLOT) /\
        vk_gate_setup_0{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_Y_SLOT) /\
        vk_gate_setup_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_X_SLOT) /\
        vk_gate_setup_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_Y_SLOT) /\
        vk_gate_setup_2{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_X_SLOT) /\
        vk_gate_setup_2{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_Y_SLOT) /\
        vk_gate_setup_3{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_X_SLOT) /\
        vk_gate_setup_3{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_Y_SLOT) /\
        vk_gate_setup_4{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_X_SLOT) /\
        vk_gate_setup_4{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_Y_SLOT) /\
        vk_gate_setup_5{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_X_SLOT) /\
        vk_gate_setup_5{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_Y_SLOT) /\
        vk_gate_setup_6{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_X_SLOT) /\
        vk_gate_setup_6{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_Y_SLOT) /\
        vk_gate_setup_7{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_X_SLOT) /\
        vk_gate_setup_7{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_Y_SLOT) /\
        poly3_omega{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
        v{2} = W256.to_uint (load mem_0 STATE_V_SLOT) /\
        gate_selector_0_opening{2} = W256.to_uint (load mem_0 PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
        vk_gate_selector_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_X_SLOT) /\
        vk_gate_selector_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_Y_SLOT) /\
        alpha{2} = W256.to_uint (load mem_0 STATE_ALPHA_SLOT) /\
        alpha2{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_2_SLOT) /\
        alpha3{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_3_SLOT) /\
        vk_permutation_3{2}.`1 = W256.to_uint (load mem_0 VK_PERMUTATION_3_X_SLOT) /\
        vk_permutation_3{2}.`2 = W256.to_uint (load mem_0 VK_PERMUTATION_3_Y_SLOT) /\
        state_beta{2} = W256.to_uint (load mem_0 STATE_BETA_SLOT) /\
        z{2} = W256.to_uint (load mem_0 STATE_Z_SLOT) /\
        gamma{2} = W256.to_uint (load mem_0 STATE_GAMMA_SLOT) /\
        alpha4{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_4_SLOT) /\
        alpha5{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_5_SLOT) /\
        gp_omega{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
        l0AtZ{2} = W256.to_uint (load mem_0 STATE_L_0_AT_Z_SLOT) /\
        poly0_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) /\
        poly1_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) /\
        poly2_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) /\
        proofLookupGrandProductOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
        alpha6{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_6_SLOT) /\
        zMinusLastOmega{2} = W256.to_uint(load mem_0 STATE_Z_MINUS_LAST_OMEGA_SLOT) /\
        proofLookupTPolyOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) /\
        betaLookup{2} = W256.to_uint(load mem_0 STATE_BETA_LOOKUP_SLOT) /\
        proofLookupTPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) /\
        betaGammaPlusGamma{2} = W256.to_uint(load mem_0 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) /\
        state_eta{2} = W256.to_uint(load mem_0 STATE_ETA_SLOT) /\
        proofLookupTableTypePolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) /\
        proofLookupSelectorPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) /\
        gammaLookup{2} = W256.to_uint(load mem_0 STATE_GAMMA_LOOKUP_SLOT) /\
        betaPlusOne{2} = W256.to_uint(load mem_0 STATE_BETA_PLUS_ONE_SLOT) /\
        alpha7{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_7_SLOT) /\
        alpha8{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_8_SLOT) /\
        lNMinusOneAtZ{2} = W256.to_uint(load mem_0 STATE_L_N_MINUS_ONE_AT_Z_SLOT) /\
        vk_lookup_table_0{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_X_SLOT) /\
        vk_lookup_table_0{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_Y_SLOT) /\
        vk_lookup_table_1{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_X_SLOT) /\
        vk_lookup_table_1{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_Y_SLOT) /\
        vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
        vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
        vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
        vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
        vk_permutation_3{2}.`1 < Constants.Q /\
        vk_permutation_3{2}.`2 < Constants.Q /\
        vk_gate_setup_0{2}.`1 < FieldQ.p /\
        vk_gate_setup_0{2}.`2 < FieldQ.p /\
        vk_gate_setup_1{2}.`1 < FieldQ.p /\
        vk_gate_setup_1{2}.`2 < FieldQ.p /\
        vk_gate_setup_2{2}.`1 < FieldQ.p /\
        vk_gate_setup_2{2}.`2 < FieldQ.p /\
        vk_gate_setup_3{2}.`1 < FieldQ.p /\
        vk_gate_setup_3{2}.`2 < FieldQ.p /\
        vk_gate_setup_4{2}.`1 < FieldQ.p /\
        vk_gate_setup_4{2}.`2 < FieldQ.p /\
        vk_gate_setup_5{2}.`1 < FieldQ.p /\
        vk_gate_setup_5{2}.`2 < FieldQ.p /\
        vk_gate_setup_6{2}.`1 < FieldQ.p /\
        vk_gate_setup_6{2}.`2 < FieldQ.p /\
        vk_gate_setup_7{2}.`1 < FieldQ.p /\
        vk_gate_setup_7{2}.`2 < FieldQ.p /\
        0 <= vk_lookup_table_0{2}.`1 < FieldQ.p /\
        0 <= vk_lookup_table_0{2}.`2 < FieldQ.p /\
        0 <= vk_lookup_table_1{2}.`1 < FieldQ.p /\
        0 <= vk_lookup_table_1{2}.`2 < FieldQ.p /\
        0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
        0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
        0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
        0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
        0 <= vk_gate_selector_1{2}.`1 < Constants.Q /\
        0 <= vk_gate_selector_1{2}.`2 < Constants.Q /\
        stateOpening0AtZ{2} < Constants.R /\ 
        stateOpening1AtZ{2} < Constants.R /\ 
        stateOpening2AtZ{2} < Constants.R /\ 
        stateOpening3AtZ{2} < Constants.R /\
        0 <= proofLookupGrandProductOpeningAtZOmega{2} < Constants.R /\
        0 <= alpha6{2} < Constants.R /\
        0 <= zMinusLastOmega{2} < Constants.R /\
        0 <= v{2} < Constants.R /\
        0 <= proofLookupTPolyOpeningAtZOmega{2} < Constants.R /\
        0 <= betaLookup{2} < Constants.R /\
        0 <= betaGammaPlusGamma{2} < Constants.R /\
        0 <= state_eta{2} < Constants.R /\
        0 <= proofLookupTableTypePolyOpeningAtZ{2} < Constants.R /\
        0 <= proofLookupSelectorPolyOpeningAtZ{2} < Constants.R /\
        0 <= gammaLookup{2} < Constants.R /\
        0 <= betaPlusOne{2} < Constants.R /\
        0 <= alpha7{2} < Constants.R /\
        0 <= alpha8{2} < Constants.R /\
        0 <= l0AtZ{2} < Constants.R /\
        0 <= lNMinusOneAtZ{2} < Constants.R
      ).
      inline*. wp. skip. progress.
      rewrite load_store_diff.
      rewrite /PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT. by progress.
      rewrite /PROOF_QUOTIENT_POLY_PARTS_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT. by progress.
      rewrite H0 H1. by progress.


      seq 1 5: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          zInDomainSize{2} = W256.to_uint zInDomainSize{1} /\
          0 <= query_at_z_0{2}.`1 < FieldQ.p /\
          0 <= query_at_z_0{2}.`2 < FieldQ.p /\
          0 <= quotient_poly_part_2{2}.`1 < FieldQ.p /\
          0 <= quotient_poly_part_2{2}.`2 < FieldQ.p /\
          0 <= quotient_poly_part_3{2}.`1 < FieldQ.p /\
          0 <= quotient_poly_part_3{2}.`2 < FieldQ.p /\
          quotient_poly_part_2{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT) /\
          quotient_poly_part_2{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_2_Y_SLOT) /\
          quotient_poly_part_3{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT) /\
          quotient_poly_part_3{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT) /\
          stateOpening0AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) /\
          stateOpening1AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) /\
          stateOpening2AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) /\
          stateOpening3AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) /\
          vk_gate_setup_0{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_X_SLOT) /\
          vk_gate_setup_0{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_Y_SLOT) /\
          vk_gate_setup_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_X_SLOT) /\
          vk_gate_setup_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_Y_SLOT) /\
          vk_gate_setup_2{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_X_SLOT) /\
          vk_gate_setup_2{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_Y_SLOT) /\
          vk_gate_setup_3{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_X_SLOT) /\
          vk_gate_setup_3{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_Y_SLOT) /\
          vk_gate_setup_4{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_X_SLOT) /\
          vk_gate_setup_4{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_Y_SLOT) /\
          vk_gate_setup_5{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_X_SLOT) /\
          vk_gate_setup_5{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_Y_SLOT) /\
          vk_gate_setup_6{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_X_SLOT) /\
          vk_gate_setup_6{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_Y_SLOT) /\
          vk_gate_setup_7{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_X_SLOT) /\
          vk_gate_setup_7{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_Y_SLOT) /\
          poly3_omega{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
          v{2} = W256.to_uint (load mem_0 STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load mem_0 PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          vk_gate_selector_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_X_SLOT) /\
          vk_gate_selector_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_Y_SLOT) /\
          alpha{2} = W256.to_uint (load mem_0 STATE_ALPHA_SLOT) /\
          alpha2{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_2_SLOT) /\
          alpha3{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_3_SLOT) /\
          vk_permutation_3{2}.`1 = W256.to_uint (load mem_0 VK_PERMUTATION_3_X_SLOT) /\
          vk_permutation_3{2}.`2 = W256.to_uint (load mem_0 VK_PERMUTATION_3_Y_SLOT) /\
          state_beta{2} = W256.to_uint (load mem_0 STATE_BETA_SLOT) /\
          z{2} = W256.to_uint (load mem_0 STATE_Z_SLOT) /\
          gamma{2} = W256.to_uint (load mem_0 STATE_GAMMA_SLOT) /\
          alpha4{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_4_SLOT) /\
          alpha5{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_5_SLOT) /\
          gp_omega{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          l0AtZ{2} = W256.to_uint (load mem_0 STATE_L_0_AT_Z_SLOT) /\
          poly0_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) /\
          poly1_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) /\
          poly2_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) /\
          proofLookupGrandProductOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          alpha6{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_6_SLOT) /\
          zMinusLastOmega{2} = W256.to_uint(load mem_0 STATE_Z_MINUS_LAST_OMEGA_SLOT) /\
          proofLookupTPolyOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) /\
          betaLookup{2} = W256.to_uint(load mem_0 STATE_BETA_LOOKUP_SLOT) /\
          proofLookupTPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) /\
          betaGammaPlusGamma{2} = W256.to_uint(load mem_0 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) /\
          state_eta{2} = W256.to_uint(load mem_0 STATE_ETA_SLOT) /\
          proofLookupTableTypePolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) /\
          proofLookupSelectorPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) /\
          gammaLookup{2} = W256.to_uint(load mem_0 STATE_GAMMA_LOOKUP_SLOT) /\
          betaPlusOne{2} = W256.to_uint(load mem_0 STATE_BETA_PLUS_ONE_SLOT) /\
          alpha7{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_7_SLOT) /\
          alpha8{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_8_SLOT) /\
          lNMinusOneAtZ{2} = W256.to_uint(load mem_0 STATE_L_N_MINUS_ONE_AT_Z_SLOT) /\
          vk_lookup_table_0{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_X_SLOT) /\
          vk_lookup_table_0{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_Y_SLOT) /\
          vk_lookup_table_1{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_X_SLOT) /\
          vk_lookup_table_1{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_Y_SLOT) /\
          vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
          vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
          vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
          vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
          vk_permutation_3{2}.`1 < Constants.Q /\
          vk_permutation_3{2}.`2 < Constants.Q /\
          vk_gate_setup_0{2}.`1 < FieldQ.p /\
          vk_gate_setup_0{2}.`2 < FieldQ.p /\
          vk_gate_setup_1{2}.`1 < FieldQ.p /\
          vk_gate_setup_1{2}.`2 < FieldQ.p /\
          vk_gate_setup_2{2}.`1 < FieldQ.p /\
          vk_gate_setup_2{2}.`2 < FieldQ.p /\
          vk_gate_setup_3{2}.`1 < FieldQ.p /\
          vk_gate_setup_3{2}.`2 < FieldQ.p /\
          vk_gate_setup_4{2}.`1 < FieldQ.p /\
          vk_gate_setup_4{2}.`2 < FieldQ.p /\
          vk_gate_setup_5{2}.`1 < FieldQ.p /\
          vk_gate_setup_5{2}.`2 < FieldQ.p /\
          vk_gate_setup_6{2}.`1 < FieldQ.p /\
          vk_gate_setup_6{2}.`2 < FieldQ.p /\
          vk_gate_setup_7{2}.`1 < FieldQ.p /\
          vk_gate_setup_7{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_0{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_0{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
          0 <= vk_gate_selector_1{2}.`1 < Constants.Q /\
          0 <= vk_gate_selector_1{2}.`2 < Constants.Q /\
          stateOpening0AtZ{2} < Constants.R /\ 
          stateOpening1AtZ{2} < Constants.R /\ 
          stateOpening2AtZ{2} < Constants.R /\ 
          stateOpening3AtZ{2} < Constants.R /\
          0 <= proofLookupGrandProductOpeningAtZOmega{2} < Constants.R /\
          0 <= alpha6{2} < Constants.R /\
          0 <= zMinusLastOmega{2} < Constants.R /\
          0 <= v{2} < Constants.R /\
          0 <= proofLookupTPolyOpeningAtZOmega{2} < Constants.R /\
          0 <= betaLookup{2} < Constants.R /\
          0 <= betaGammaPlusGamma{2} < Constants.R /\
          0 <= state_eta{2} < Constants.R /\
          0 <= proofLookupTableTypePolyOpeningAtZ{2} < Constants.R /\
          0 <= proofLookupSelectorPolyOpeningAtZ{2} < Constants.R /\
          0 <= gammaLookup{2} < Constants.R /\
          0 <= betaPlusOne{2} < Constants.R /\
          0 <= alpha7{2} < Constants.R /\
          0 <= alpha8{2} < Constants.R /\
          0 <= l0AtZ{2} < Constants.R /\
          0 <= lNMinusOneAtZ{2} < Constants.R /\
          exists (x0 x32 x64 x96: uint256), Primops.memory{1} = store(store(store(store(store(store mem_0
                      W256.zero x0)
                    (W256.of_int 32) x32)
                  (W256.of_int 64) x64)
                (W256.of_int 96) x96)
              QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0{2}.`1))
            QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0{2}.`2)
        )
      ).
      wp. sp.
      exists* quotient_poly_part_1{2}, query_at_z_0{2}, zInDomainSize{2}, Primops.memory{1}.
      elim*=> quotient_poly_part_1_r query_at_z_0_r zInDomainSize_r memory_l.
      call (pointMulAndAddIntoDest_low_equiv_mid quotient_poly_part_1_r.`1 quotient_poly_part_1_r.`2 query_at_z_0_r.`1 query_at_z_0_r.`2 zInDomainSize_r PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT QUERIES_AT_Z_0_X_SLOT memory_l).
      skip. progress.
      exact to_uint_ge_zero.
      exact to_uint_lt_mod.
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT; rewrite W256.of_intN'; progress.
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT; simplify; rewrite W256.of_intN'; progress.      
      by rewrite /QUERIES_AT_Z_0_X_SLOT; simplify; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_AT_Z_0_X_SLOT; simplify; rewrite W256.of_intN'; progress.
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT load_store_diff; [
        progress |
        progress |
        rewrite load_store_diff; [
          progress |
          progress |
          rewrite H18; progress
        ]
      ].
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT load_store_diff; [
        progress |
        progress |
        rewrite load_store_diff; [
          progress |
          progress |
          rewrite H19; progress
        ]
      ].
      by rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT load_store_diff; [
        progress |
        progress |
        exact load_store_same
      ].
      exact load_store_same.
      case H149. progress. case H150. progress.
      exact F_to_int_point_1_ge_zero.
      exact F_to_int_point_1_lt_p.
      exact F_to_int_point_2_ge_zero.
      exact F_to_int_point_2_lt_p.
      rewrite /F_to_int_point. simplify.
      exists (W256.of_int (FieldQ.asint x)).
      exists (W256.of_int (FieldQ.asint y)).      
      exists (W256.of_int quotient_poly_part_0{2}.`1).
      exists (W256.of_int quotient_poly_part_0{2}.`2).
      rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT. simplify.
      do 2! (rewrite (store_store_swap_diff _ _ W256.zero); progress).
      do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); progress).
      do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); progress).
      do 2! (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); progress).
      rewrite (store_store_swap_diff _ (W256.of_int 4320)); progress.
      do 2! rewrite store_store_same.
      reflexivity.
      
      by progress. by progress.
      

      seq 2 4: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          zInDomainSize{2} = W256.to_uint zInDomainSize{1} /\
          currentZ{2} = W256.to_uint currentZ{1} /\
          0 <= query_at_z_0{2}.`1 < FieldQ.p /\
          0 <= query_at_z_0{2}.`2 < FieldQ.p /\
          0 <= quotient_poly_part_3{2}.`1 < FieldQ.p /\
          0 <= quotient_poly_part_3{2}.`2 < FieldQ.p /\
          quotient_poly_part_3{2}.`1 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT) /\
          quotient_poly_part_3{2}.`2 = W256.to_uint (load mem_0 PROOF_QUOTIENT_POLY_PARTS_3_Y_SLOT) /\
          stateOpening0AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) /\
          stateOpening1AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) /\
          stateOpening2AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) /\
          stateOpening3AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) /\
          vk_gate_setup_0{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_X_SLOT) /\
          vk_gate_setup_0{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_Y_SLOT) /\
          vk_gate_setup_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_X_SLOT) /\
          vk_gate_setup_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_Y_SLOT) /\
          vk_gate_setup_2{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_X_SLOT) /\
          vk_gate_setup_2{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_Y_SLOT) /\
          vk_gate_setup_3{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_X_SLOT) /\
          vk_gate_setup_3{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_Y_SLOT) /\
          vk_gate_setup_4{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_X_SLOT) /\
          vk_gate_setup_4{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_Y_SLOT) /\
          vk_gate_setup_5{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_X_SLOT) /\
          vk_gate_setup_5{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_Y_SLOT) /\
          vk_gate_setup_6{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_X_SLOT) /\
          vk_gate_setup_6{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_Y_SLOT) /\
          vk_gate_setup_7{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_X_SLOT) /\
          vk_gate_setup_7{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_Y_SLOT) /\
          poly3_omega{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
          v{2} = W256.to_uint (load mem_0 STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load mem_0 PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          vk_gate_selector_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_X_SLOT) /\
          vk_gate_selector_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_Y_SLOT) /\
          alpha{2} = W256.to_uint (load mem_0 STATE_ALPHA_SLOT) /\
          alpha2{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_2_SLOT) /\
          alpha3{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_3_SLOT) /\
          vk_permutation_3{2}.`1 = W256.to_uint (load mem_0 VK_PERMUTATION_3_X_SLOT) /\
          vk_permutation_3{2}.`2 = W256.to_uint (load mem_0 VK_PERMUTATION_3_Y_SLOT) /\
          state_beta{2} = W256.to_uint (load mem_0 STATE_BETA_SLOT) /\
          z{2} = W256.to_uint (load mem_0 STATE_Z_SLOT) /\
          gamma{2} = W256.to_uint (load mem_0 STATE_GAMMA_SLOT) /\
          alpha4{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_4_SLOT) /\
          alpha5{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_5_SLOT) /\
          gp_omega{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          l0AtZ{2} = W256.to_uint (load mem_0 STATE_L_0_AT_Z_SLOT) /\
          poly0_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) /\
          poly1_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) /\
          poly2_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) /\
          alpha6{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_6_SLOT) /\
          proofLookupGrandProductOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          zMinusLastOmega{2} = W256.to_uint(load mem_0 STATE_Z_MINUS_LAST_OMEGA_SLOT) /\
          proofLookupTPolyOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) /\
          betaLookup{2} = W256.to_uint(load mem_0 STATE_BETA_LOOKUP_SLOT) /\
          proofLookupTPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) /\
          betaGammaPlusGamma{2} = W256.to_uint(load mem_0 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) /\
          state_eta{2} = W256.to_uint(load mem_0 STATE_ETA_SLOT) /\
          proofLookupTableTypePolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) /\
          proofLookupSelectorPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) /\
          gammaLookup{2} = W256.to_uint(load mem_0 STATE_GAMMA_LOOKUP_SLOT) /\
          betaPlusOne{2} = W256.to_uint(load mem_0 STATE_BETA_PLUS_ONE_SLOT) /\
          alpha7{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_7_SLOT) /\
          alpha8{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_8_SLOT) /\
          lNMinusOneAtZ{2} = W256.to_uint(load mem_0 STATE_L_N_MINUS_ONE_AT_Z_SLOT) /\
          vk_lookup_table_0{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_X_SLOT) /\
          vk_lookup_table_0{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_Y_SLOT) /\
          vk_lookup_table_1{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_X_SLOT) /\
          vk_lookup_table_1{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_Y_SLOT) /\
          vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
          vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
          vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
          vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
          vk_permutation_3{2}.`1 < Constants.Q /\
          vk_permutation_3{2}.`2 < Constants.Q /\
          vk_gate_setup_0{2}.`1 < FieldQ.p /\
          vk_gate_setup_0{2}.`2 < FieldQ.p /\
          vk_gate_setup_1{2}.`1 < FieldQ.p /\
          vk_gate_setup_1{2}.`2 < FieldQ.p /\
          vk_gate_setup_2{2}.`1 < FieldQ.p /\
          vk_gate_setup_2{2}.`2 < FieldQ.p /\
          vk_gate_setup_3{2}.`1 < FieldQ.p /\
          vk_gate_setup_3{2}.`2 < FieldQ.p /\
          vk_gate_setup_4{2}.`1 < FieldQ.p /\
          vk_gate_setup_4{2}.`2 < FieldQ.p /\
          vk_gate_setup_5{2}.`1 < FieldQ.p /\
          vk_gate_setup_5{2}.`2 < FieldQ.p /\
          vk_gate_setup_6{2}.`1 < FieldQ.p /\
          vk_gate_setup_6{2}.`2 < FieldQ.p /\
          vk_gate_setup_7{2}.`1 < FieldQ.p /\
          vk_gate_setup_7{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_0{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_0{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
          0 <= vk_gate_selector_1{2}.`1 < Constants.Q /\
          0 <= vk_gate_selector_1{2}.`2 < Constants.Q /\
          stateOpening0AtZ{2} < Constants.R /\ 
          stateOpening1AtZ{2} < Constants.R /\ 
          stateOpening2AtZ{2} < Constants.R /\ 
          stateOpening3AtZ{2} < Constants.R /\
          0 <= proofLookupGrandProductOpeningAtZOmega{2} < Constants.R /\
          0 <= alpha6{2} < Constants.R /\
          0 <= zMinusLastOmega{2} < Constants.R /\
          0 <= v{2} < Constants.R /\
          0 <= proofLookupTPolyOpeningAtZOmega{2} < Constants.R /\
          0 <= betaLookup{2} < Constants.R /\
          0 <= betaGammaPlusGamma{2} < Constants.R /\
          0 <= state_eta{2} < Constants.R /\
          0 <= proofLookupTableTypePolyOpeningAtZ{2} < Constants.R /\
          0 <= proofLookupSelectorPolyOpeningAtZ{2} < Constants.R /\
          0 <= gammaLookup{2} < Constants.R /\
          0 <= betaPlusOne{2} < Constants.R /\
          0 <= alpha7{2} < Constants.R /\
          0 <= alpha8{2} < Constants.R /\
          0 <= l0AtZ{2} < Constants.R /\
          0 <= lNMinusOneAtZ{2} < Constants.R /\
          exists (x0 x32 x64 x96: uint256), Primops.memory{1} = store(store(store(store(store(store mem_0
                      W256.zero x0)
                    (W256.of_int 32) x32)
                  (W256.of_int 64) x64)
                (W256.of_int 96) x96)
              QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0{2}.`1))
            QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0{2}.`2)
        )
      ).
      exists* Primops.reverted{1}. elim*=> reverted.
      case reverted. progress.
      conseq (_ : Primops.reverted{1} /\ failed{2}  ==> Primops.reverted{1} /\ failed{2}).
      by progress.
      by progress; left; progress.
      inline PointMulAndAddIntoDest.mid. wp. sp.
      call{1} pointMulAndAddIntoDest_low_pspec_revert.
      skip. progress. left. by progress.

      progress.
      wp. sp.
      exists* quotient_poly_part_2{2}, query_at_z_0{2}, currentZ{2}, Primops.memory{1}.
      elim*=> quotient_poly_part_2_r query_at_z_0_r currentZ_r memory_l.
      call (pointMulAndAddIntoDest_low_equiv_mid quotient_poly_part_2_r.`1 quotient_poly_part_2_r.`2 query_at_z_0_r.`1 query_at_z_0_r.`2 currentZ_r PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT QUERIES_AT_Z_0_X_SLOT memory_l).
      skip. progress.
      rewrite /Constants.R; exact modz_ge0.
      rewrite /Constants.R; smt (ltz_pmod).
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT; rewrite W256.of_intN'; progress.
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT; simplify; rewrite W256.of_intN'; progress.      
      by rewrite /QUERIES_AT_Z_0_X_SLOT; simplify; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_AT_Z_0_X_SLOT; simplify; rewrite W256.of_intN'; progress.
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H13; progress.
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_2_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H14; progress.
      by rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT load_store_diff; [
        progress |
        progress |
        exact load_store_same
      ].
      exact load_store_same.
      by rewrite /mulmod -Constants.R_int; progress.
      case H142. progress. case H143. progress.
      right. progress.
      by rewrite /mulmod -Constants.R_int; progress; rewrite W256.of_uintK mod_R_W256_mod_R; reflexivity.
      exact F_to_int_point_1_ge_zero.
      exact F_to_int_point_1_lt_p.
      exact F_to_int_point_2_ge_zero.
      exact F_to_int_point_2_lt_p.
      rewrite /F_to_int_point. simplify.
      exists (W256.of_int (FieldQ.asint x)).
      exists (W256.of_int (FieldQ.asint y)).      
      exists (W256.of_int query_at_z_0{2}.`1).
      exists (W256.of_int query_at_z_0{2}.`2).
      rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT. simplify.
      exact mulAndAddIntoDest_after_mulAndAddIntoDest.
      
      by progress. by progress.


      seq 2 4: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          stateOpening0AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) /\
          stateOpening1AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) /\
          stateOpening2AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) /\
          stateOpening3AtZ{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) /\
          vk_gate_setup_0{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_X_SLOT) /\
          vk_gate_setup_0{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_0_Y_SLOT) /\
          vk_gate_setup_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_X_SLOT) /\
          vk_gate_setup_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_1_Y_SLOT) /\
          vk_gate_setup_2{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_X_SLOT) /\
          vk_gate_setup_2{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_2_Y_SLOT) /\
          vk_gate_setup_3{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_X_SLOT) /\
          vk_gate_setup_3{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_3_Y_SLOT) /\
          vk_gate_setup_4{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_X_SLOT) /\
          vk_gate_setup_4{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_4_Y_SLOT) /\
          vk_gate_setup_5{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_X_SLOT) /\
          vk_gate_setup_5{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_5_Y_SLOT) /\
          vk_gate_setup_6{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_X_SLOT) /\
          vk_gate_setup_6{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_6_Y_SLOT) /\
          vk_gate_setup_7{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_X_SLOT) /\
          vk_gate_setup_7{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SETUP_7_Y_SLOT) /\
          poly3_omega{2} = W256.to_uint (load mem_0 PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT) /\
          v{2} = W256.to_uint (load mem_0 STATE_V_SLOT) /\
          gate_selector_0_opening{2} = W256.to_uint (load mem_0 PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT) /\
          vk_gate_selector_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_X_SLOT) /\
          vk_gate_selector_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_Y_SLOT) /\
          alpha{2} = W256.to_uint (load mem_0 STATE_ALPHA_SLOT) /\
          alpha2{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_2_SLOT) /\
          alpha3{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_3_SLOT) /\
          vk_permutation_3{2}.`1 = W256.to_uint (load mem_0 VK_PERMUTATION_3_X_SLOT) /\
          vk_permutation_3{2}.`2 = W256.to_uint (load mem_0 VK_PERMUTATION_3_Y_SLOT) /\
          state_beta{2} = W256.to_uint (load mem_0 STATE_BETA_SLOT) /\
          z{2} = W256.to_uint (load mem_0 STATE_Z_SLOT) /\
          gamma{2} = W256.to_uint (load mem_0 STATE_GAMMA_SLOT) /\
          alpha4{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_4_SLOT) /\
          alpha5{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_5_SLOT) /\
          gp_omega{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          l0AtZ{2} = W256.to_uint (load mem_0 STATE_L_0_AT_Z_SLOT) /\
          poly0_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) /\
          poly1_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) /\
          poly2_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) /\
          proofLookupGrandProductOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          alpha6{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_6_SLOT) /\
          zMinusLastOmega{2} = W256.to_uint(load mem_0 STATE_Z_MINUS_LAST_OMEGA_SLOT) /\
          proofLookupTPolyOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) /\
          betaLookup{2} = W256.to_uint(load mem_0 STATE_BETA_LOOKUP_SLOT) /\
          proofLookupTPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) /\
          betaGammaPlusGamma{2} = W256.to_uint(load mem_0 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) /\
          state_eta{2} = W256.to_uint(load mem_0 STATE_ETA_SLOT) /\
          proofLookupTableTypePolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) /\
          proofLookupSelectorPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) /\
          gammaLookup{2} = W256.to_uint(load mem_0 STATE_GAMMA_LOOKUP_SLOT) /\
          betaPlusOne{2} = W256.to_uint(load mem_0 STATE_BETA_PLUS_ONE_SLOT) /\
          alpha7{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_7_SLOT) /\
          alpha8{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_8_SLOT) /\
          lNMinusOneAtZ{2} = W256.to_uint(load mem_0 STATE_L_N_MINUS_ONE_AT_Z_SLOT) /\
          vk_lookup_table_0{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_X_SLOT) /\
          vk_lookup_table_0{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_Y_SLOT) /\
          vk_lookup_table_1{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_X_SLOT) /\
          vk_lookup_table_1{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_Y_SLOT) /\
          vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
          vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
          vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
          vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
          vk_permutation_3{2}.`1 < Constants.Q /\
          vk_permutation_3{2}.`2 < Constants.Q /\
          vk_gate_setup_0{2}.`1 < FieldQ.p /\
          vk_gate_setup_0{2}.`2 < FieldQ.p /\
          vk_gate_setup_1{2}.`1 < FieldQ.p /\
          vk_gate_setup_1{2}.`2 < FieldQ.p /\
          vk_gate_setup_2{2}.`1 < FieldQ.p /\
          vk_gate_setup_2{2}.`2 < FieldQ.p /\
          vk_gate_setup_3{2}.`1 < FieldQ.p /\
          vk_gate_setup_3{2}.`2 < FieldQ.p /\
          vk_gate_setup_4{2}.`1 < FieldQ.p /\
          vk_gate_setup_4{2}.`2 < FieldQ.p /\
          vk_gate_setup_5{2}.`1 < FieldQ.p /\
          vk_gate_setup_5{2}.`2 < FieldQ.p /\
          vk_gate_setup_6{2}.`1 < FieldQ.p /\
          vk_gate_setup_6{2}.`2 < FieldQ.p /\
          vk_gate_setup_7{2}.`1 < FieldQ.p /\
          vk_gate_setup_7{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_0{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_0{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
          0 <= vk_gate_selector_1{2}.`1 < Constants.Q /\
          0 <= vk_gate_selector_1{2}.`2 < Constants.Q /\
          stateOpening0AtZ{2} < Constants.R /\ 
          stateOpening1AtZ{2} < Constants.R /\ 
          stateOpening2AtZ{2} < Constants.R /\ 
          stateOpening3AtZ{2} < Constants.R /\
          0 <= proofLookupGrandProductOpeningAtZOmega{2} < Constants.R /\
          0 <= alpha6{2} < Constants.R /\
          0 <= zMinusLastOmega{2} < Constants.R /\
          0 <= v{2} < Constants.R /\
          0 <= proofLookupTPolyOpeningAtZOmega{2} < Constants.R /\
          0 <= betaLookup{2} < Constants.R /\
          0 <= betaGammaPlusGamma{2} < Constants.R /\
          0 <= state_eta{2} < Constants.R /\
          0 <= proofLookupTableTypePolyOpeningAtZ{2} < Constants.R /\
          0 <= proofLookupSelectorPolyOpeningAtZ{2} < Constants.R /\
          0 <= gammaLookup{2} < Constants.R /\
          0 <= betaPlusOne{2} < Constants.R /\
          0 <= alpha7{2} < Constants.R /\
          0 <= alpha8{2} < Constants.R /\
          0 <= l0AtZ{2} < Constants.R /\
          0 <= lNMinusOneAtZ{2} < Constants.R /\
          0 <= query_at_z_0{2}.`1 < FieldQ.p /\
          0 <= query_at_z_0{2}.`2 < FieldQ.p /\
          exists (x0 x32 x64 x96: uint256), Primops.memory{1} = store(store(store(store(store(store mem_0
                      W256.zero x0)
                    (W256.of_int 32) x32)
                  (W256.of_int 64) x64)
                (W256.of_int 96) x96)
              QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0{2}.`1))
            QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0{2}.`2)
        )
      ).
      exists* Primops.reverted{1}. elim*=> reverted.
      case reverted. progress.
      conseq (_ : Primops.reverted{1} /\ failed{2}  ==> Primops.reverted{1} /\ failed{2}).
      by progress.
      by progress; left; progress.
      inline PointMulAndAddIntoDest.mid. wp. sp.
      call{1} pointMulAndAddIntoDest_low_pspec_revert.
      skip. progress. left. by progress.

      progress.
      wp. sp.
      exists* quotient_poly_part_3{2}, query_at_z_0{2}, currentZ{2}, Primops.memory{1}.
      elim*=> quotient_poly_part_3_r query_at_z_0_r currentZ_r memory_l.
      progress.
      call (pointMulAndAddIntoDest_low_equiv_mid quotient_poly_part_3_r.`1 quotient_poly_part_3_r.`2 query_at_z_0_r.`1 query_at_z_0_r.`2 currentZ_r PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT QUERIES_AT_Z_0_X_SLOT memory_l).
      skip. progress.
      rewrite /Constants.R; exact modz_ge0.
      rewrite /Constants.R; smt (ltz_pmod).
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT; rewrite W256.of_intN'; progress.
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT; simplify; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_AT_Z_0_X_SLOT; simplify; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_AT_Z_0_X_SLOT; simplify; rewrite W256.of_intN'; progress.
      rewrite /PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress).
        rewrite H9; progress.
      by rewrite /PROOF_QUOTIENT_POLY_PARTS_3_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H10; progress.
      by rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT load_store_diff; [
        progress |
        progress |
        exact load_store_same
      ].
      exact load_store_same.
      by rewrite /mulmod -Constants.R_int; progress.
      case H136. progress. case H137. progress.
      right. progress.
      exact F_to_int_point_1_ge_zero.
      exact F_to_int_point_1_lt_p.
      exact F_to_int_point_2_ge_zero.
      exact F_to_int_point_2_lt_p.
      by rewrite /F_to_int_point; simplify;
        exists (W256.of_int (FieldQ.asint x));
        exists (W256.of_int (FieldQ.asint y));      
        exists (W256.of_int query_at_z_0{2}.`1);
        exists (W256.of_int query_at_z_0{2}.`2);
        rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT; simplify;
        exact mulAndAddIntoDest_after_mulAndAddIntoDest.
      
      by progress. by progress.


      seq 5 3: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          vk_gate_selector_1{2}.`1 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_X_SLOT) /\
          vk_gate_selector_1{2}.`2 = W256.to_uint (load mem_0 VK_GATE_SELECTORS_1_Y_SLOT) /\
          v{2} = W256.to_uint (load mem_0 STATE_V_SLOT) /\
          alpha{2} = W256.to_uint (load mem_0 STATE_ALPHA_SLOT) /\
          alpha2{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_2_SLOT) /\
          alpha3{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_3_SLOT) /\
          vk_permutation_3{2}.`1 = W256.to_uint (load mem_0 VK_PERMUTATION_3_X_SLOT) /\
          vk_permutation_3{2}.`2 = W256.to_uint (load mem_0 VK_PERMUTATION_3_Y_SLOT) /\
          stateOpening0AtZ{2} = W256.to_uint stateOpening0AtZ{1} /\
          stateOpening1AtZ{2} = W256.to_uint stateOpening1AtZ{1} /\
          stateOpening2AtZ{2} = W256.to_uint stateOpening2AtZ{1} /\
          stateOpening3AtZ{2} = W256.to_uint stateOpening3AtZ{1} /\
          state_beta{2} = W256.to_uint (load mem_0 STATE_BETA_SLOT) /\
          z{2} = W256.to_uint (load mem_0 STATE_Z_SLOT) /\
          gamma{2} = W256.to_uint (load mem_0 STATE_GAMMA_SLOT) /\
          alpha4{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_4_SLOT) /\
          alpha5{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_5_SLOT) /\
          gp_omega{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          l0AtZ{2} = W256.to_uint (load mem_0 STATE_L_0_AT_Z_SLOT) /\
          poly0_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) /\
          poly1_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) /\
          poly2_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) /\
          proofLookupGrandProductOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          alpha6{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_6_SLOT) /\
          zMinusLastOmega{2} = W256.to_uint(load mem_0 STATE_Z_MINUS_LAST_OMEGA_SLOT) /\
          proofLookupTPolyOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) /\
          betaLookup{2} = W256.to_uint(load mem_0 STATE_BETA_LOOKUP_SLOT) /\
          proofLookupTPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) /\
          betaGammaPlusGamma{2} = W256.to_uint(load mem_0 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) /\
          state_eta{2} = W256.to_uint(load mem_0 STATE_ETA_SLOT) /\
          proofLookupTableTypePolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) /\
          proofLookupSelectorPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) /\
          gammaLookup{2} = W256.to_uint(load mem_0 STATE_GAMMA_LOOKUP_SLOT) /\
          betaPlusOne{2} = W256.to_uint(load mem_0 STATE_BETA_PLUS_ONE_SLOT) /\
          alpha7{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_7_SLOT) /\
          alpha8{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_8_SLOT) /\
          lNMinusOneAtZ{2} = W256.to_uint(load mem_0 STATE_L_N_MINUS_ONE_AT_Z_SLOT) /\
          vk_lookup_table_0{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_X_SLOT) /\
          vk_lookup_table_0{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_Y_SLOT) /\
          vk_lookup_table_1{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_X_SLOT) /\
          vk_lookup_table_1{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_Y_SLOT) /\
          vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
          vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
          vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
          vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
          0 <= vk_lookup_table_0{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_0{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
          vk_permutation_3{2}.`1 < Constants.Q /\
          vk_permutation_3{2}.`2 < Constants.Q /\
          0 <= query_at_z_1{2}.`1 < Constants.Q /\
          0 <= query_at_z_1{2}.`2 < Constants.Q /\
          0 <= vk_gate_selector_1{2}.`1 < Constants.Q /\
          0 <= vk_gate_selector_1{2}.`2 < Constants.Q /\
          stateOpening0AtZ{2} < Constants.R /\
          stateOpening1AtZ{2} < Constants.R /\
          stateOpening2AtZ{2} < Constants.R /\
          stateOpening3AtZ{2} < Constants.R /\
          0 <= proofLookupGrandProductOpeningAtZOmega{2} < Constants.R /\
          0 <= alpha6{2} < Constants.R /\
          0 <= zMinusLastOmega{2} < Constants.R /\
          0 <= v{2} < Constants.R /\
          0 <= proofLookupTPolyOpeningAtZOmega{2} < Constants.R /\
          0 <= betaLookup{2} < Constants.R /\
          0 <= betaGammaPlusGamma{2} < Constants.R /\
          0 <= state_eta{2} < Constants.R /\
          0 <= proofLookupTableTypePolyOpeningAtZ{2} < Constants.R /\
          0 <= proofLookupSelectorPolyOpeningAtZ{2} < Constants.R /\
          0 <= gammaLookup{2} < Constants.R /\
          0 <= betaPlusOne{2} < Constants.R /\
          0 <= alpha7{2} < Constants.R /\
          0 <= alpha8{2} < Constants.R /\
          0 <= l0AtZ{2} < Constants.R /\
          0 <= lNMinusOneAtZ{2} < Constants.R /\
          0 <= query_at_z_0{2}.`1 < FieldQ.p /\
          0 <= query_at_z_0{2}.`2 < FieldQ.p /\
          exists (x0 x32 x64 x96: uint256), Primops.memory{1} = store(store(store(store(store(store(store(store mem_0
                          QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0{2}.`1))
                        QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0{2}.`2))
                      W256.zero x0)
                    (W256.of_int 32) x32)
                  (W256.of_int 64) x64)
                (W256.of_int 96) x96)
              QUERIES_AT_Z_1_X_SLOT (W256.of_int query_at_z_1{2}.`1))
            QUERIES_AT_Z_1_Y_SLOT (W256.of_int query_at_z_1{2}.`2)
        )
      ).
      exists* Primops.reverted{1}. elim*=> reverted.
      case reverted. progress.
      conseq (_ : Primops.reverted{1} /\ failed{2}  ==> Primops.reverted{1} /\ failed{2}).
      by progress.
      by progress; left; progress.
      inline MainGateLinearisationContributionWithV.mid PointMulIntoDest.mid PointMulAndAddIntoDest.mid PointAddIntoDest.mid. wp.
      inline MainGateLinearisationContributionWithV.low.
      call{1} pointMulIntoDest_low_pspec_revert. wp.
      call{1} ConcretePrimops.mload_pspec_revert.
      call{1} ConcretePrimops.mload_pspec_revert.
      call{1} pointMulAndAddIntoDest_low_pspec_revert.
      call{1} ConcretePrimops.mload_pspec_revert.
      call{1} pointAddAssign_low_pspec_revert.
      call{1} pointMulAndAddIntoDest_low_pspec_revert. wp.
      call{1} pointMulAndAddIntoDest_low_pspec_revert. wp.
      call{1} pointMulAndAddIntoDest_low_pspec_revert.
      call{1} pointMulAndAddIntoDest_low_pspec_revert.
      call{1} pointMulAndAddIntoDest_low_pspec_revert.
      call{1} pointMulIntoDest_low_pspec_revert. wp.
      do 4! call{1} ConcretePrimops.mload_pspec_revert.
      skip. progress. left. by progress.

      progress.
      exists* Primops.memory{1}. elim*=>memory_L. wp.
      call (mainGateLinearisationContributionWithV_low_equiv_mid memory_L QUERIES_AT_Z_1_X_SLOT).
      inline*. wp. skip. progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT W256.of_intN'; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /VK_GATE_SETUP_0_X_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /VK_GATE_SETUP_0_X_SLOT /VK_GATE_SETUP_7_Y_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /STATE_V_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /STATE_V_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT; progress.
      by rewrite /VK_GATE_SETUP_0_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H1; progress.
      by rewrite /VK_GATE_SETUP_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H2; progress.
      by rewrite /VK_GATE_SETUP_1_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H3; progress.
      by rewrite /VK_GATE_SETUP_1_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H4; progress.
      by rewrite /VK_GATE_SETUP_2_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H5; progress.
      by rewrite /VK_GATE_SETUP_2_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H6; progress.
      by rewrite /VK_GATE_SETUP_3_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H7; progress.
      by rewrite /VK_GATE_SETUP_3_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H8; progress.
      by rewrite /VK_GATE_SETUP_4_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H9; progress.
      by rewrite /VK_GATE_SETUP_4_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H10; progress.
      by rewrite /VK_GATE_SETUP_5_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H11; progress.
      by rewrite /VK_GATE_SETUP_5_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H12; progress.
      by rewrite /VK_GATE_SETUP_6_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H13; progress.
      by rewrite /VK_GATE_SETUP_6_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H14; progress.
      by rewrite /VK_GATE_SETUP_7_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H15; progress.
      by rewrite /VK_GATE_SETUP_7_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H16; progress.
      by rewrite /PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_STATE_POLYS_3_OPENING_AT_Z_OMEGA_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_V_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_GATE_SELECTORS_0_OPENING_AT_Z_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT;
        do 6! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      case H156. by progress. progress. right. progress.
      rewrite /mainGateLinearisation_memory_footprint. simplify.
      exists (W256.of_int prev.`1).
      exists (W256.of_int prev.`2).
      exists (W256.of_int factor).
      exists x960.
      rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT. simplify.
      rewrite (store_store_swap_diff _ (W256.of_int 96) (W256.of_int 4288)). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 64) (W256.of_int 4288)). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 32) (W256.of_int 4288)). by progress. by progress.
      rewrite (store_store_swap_diff _ W256.zero (W256.of_int 4288)). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 96) (W256.of_int 4320)). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 64) (W256.of_int 4320)). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 32) (W256.of_int 4320)). by progress. by progress.
      rewrite (store_store_swap_diff _ W256.zero (W256.of_int 4320)). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 96) W256.zero). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 64) W256.zero). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 32) W256.zero). by progress. by progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ (W256.of_int 96) (W256.of_int 32)). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 64) (W256.of_int 32)). by progress. by progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ (W256.of_int 96) (W256.of_int 64)). by progress. by progress.
      rewrite store_store_same.
      rewrite store_store_same.
      reflexivity.


      seq 1 3: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          vk_permutation_3{2}.`1 = W256.to_uint (load mem_0 VK_PERMUTATION_3_X_SLOT) /\
          vk_permutation_3{2}.`2 = W256.to_uint (load mem_0 VK_PERMUTATION_3_Y_SLOT) /\
          state_beta{2} = W256.to_uint (load mem_0 STATE_BETA_SLOT) /\
          v{2} = W256.to_uint (load mem_0 STATE_V_SLOT) /\
          z{2} = W256.to_uint (load mem_0 STATE_Z_SLOT) /\
          gamma{2} = W256.to_uint (load mem_0 STATE_GAMMA_SLOT) /\
          alpha4{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_4_SLOT) /\
          alpha5{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_5_SLOT) /\
          gp_omega{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          l0AtZ{2} = W256.to_uint (load mem_0 STATE_L_0_AT_Z_SLOT) /\
          poly0_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) /\
          poly1_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) /\
          poly2_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) /\
          stateOpening0AtZ{2} = W256.to_uint stateOpening0AtZ{1} /\
          stateOpening1AtZ{2} = W256.to_uint stateOpening1AtZ{1} /\
          stateOpening2AtZ{2} = W256.to_uint stateOpening2AtZ{1} /\
          stateOpening3AtZ{2} = W256.to_uint stateOpening3AtZ{1} /\
          proofLookupGrandProductOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          alpha6{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_6_SLOT) /\
          zMinusLastOmega{2} = W256.to_uint(load mem_0 STATE_Z_MINUS_LAST_OMEGA_SLOT) /\
          proofLookupTPolyOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) /\
          betaLookup{2} = W256.to_uint(load mem_0 STATE_BETA_LOOKUP_SLOT) /\
          proofLookupTPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) /\
          betaGammaPlusGamma{2} = W256.to_uint(load mem_0 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) /\
          state_eta{2} = W256.to_uint(load mem_0 STATE_ETA_SLOT) /\
          proofLookupTableTypePolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) /\
          proofLookupSelectorPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) /\
          gammaLookup{2} = W256.to_uint(load mem_0 STATE_GAMMA_LOOKUP_SLOT) /\
          betaPlusOne{2} = W256.to_uint(load mem_0 STATE_BETA_PLUS_ONE_SLOT) /\
          alpha7{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_7_SLOT) /\
          alpha8{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_8_SLOT) /\
          lNMinusOneAtZ{2} = W256.to_uint(load mem_0 STATE_L_N_MINUS_ONE_AT_Z_SLOT) /\
          vk_lookup_table_0{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_X_SLOT) /\
          vk_lookup_table_0{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_Y_SLOT) /\
          vk_lookup_table_1{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_X_SLOT) /\
          vk_lookup_table_1{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_Y_SLOT) /\
          vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
          vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
          vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
          vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
          0 <= vk_lookup_table_0{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_0{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
          vk_permutation_3{2}.`1 < Constants.Q /\
          vk_permutation_3{2}.`2 < Constants.Q /\
          0 <= query_at_z_1{2}.`1 < Constants.Q /\
          0 <= query_at_z_1{2}.`2 < Constants.Q /\
          stateOpening0AtZ{2} < Constants.R /\
          stateOpening1AtZ{2} < Constants.R /\
          stateOpening2AtZ{2} < Constants.R /\
          stateOpening3AtZ{2} < Constants.R /\
          0 <= proofLookupGrandProductOpeningAtZOmega{2} < Constants.R /\
          0 <= alpha6{2} < Constants.R /\
          0 <= zMinusLastOmega{2} < Constants.R /\
          0 <= v{2} < Constants.R /\
          0 <= proofLookupTPolyOpeningAtZOmega{2} < Constants.R /\
          0 <= betaLookup{2} < Constants.R /\
          0 <= betaGammaPlusGamma{2} < Constants.R /\
          0 <= state_eta{2} < Constants.R /\
          0 <= proofLookupTableTypePolyOpeningAtZ{2} < Constants.R /\
          0 <= proofLookupSelectorPolyOpeningAtZ{2} < Constants.R /\
          0 <= gammaLookup{2} < Constants.R /\
          0 <= betaPlusOne{2} < Constants.R /\
          0 <= alpha7{2} < Constants.R /\
          0 <= alpha8{2} < Constants.R /\
          0 <= l0AtZ{2} < Constants.R /\
          0 <= lNMinusOneAtZ{2} < Constants.R /\
          0 <= query_at_z_0{2}.`1 < FieldQ.p /\
          0 <= query_at_z_0{2}.`2 < FieldQ.p /\
          exists (x0 x32 x64 x96: uint256), Primops.memory{1} = store(store(store(store(store(store(store(store mem_0
                          QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0{2}.`1))
                        QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0{2}.`2))
                      W256.zero x0)
                    (W256.of_int 32) x32)
                  (W256.of_int 64) x64)
                (W256.of_int 96) x96)
              QUERIES_AT_Z_1_X_SLOT (W256.of_int query_at_z_1{2}.`1))
            QUERIES_AT_Z_1_Y_SLOT (W256.of_int query_at_z_1{2}.`2)
        )
      ).
      exists* Primops.reverted{1}. elim*=> reverted.
      case reverted. progress.
      conseq (_ : Primops.reverted{1} /\ failed{2}  ==> Primops.reverted{1} /\ failed{2}).
      by progress.
      by progress; left; progress.
      inline AddAssignRescueCustomGateLinearisationContributionWithV.mid PointMulAndAddIntoDest.mid. wp.
      inline AddAssignRescueCustomGateLinearisationContributionWithV.low.
      call{1} pointMulAndAddIntoDest_low_pspec_revert. wp.
      call{1} ConcretePrimops.mload_pspec_revert. wp.
      call{1} ConcretePrimops.mload_pspec_revert. wp.
      call{1} ConcretePrimops.mload_pspec_revert. wp.
      call{1} ConcretePrimops.mload_pspec_revert. wp.
      skip. progress. left. by progress.

      progress. wp.
      exists* Primops.memory{1}, stateOpening0AtZ{1}, stateOpening1AtZ{1}, stateOpening2AtZ{1}, stateOpening3AtZ{1}, stateOpening0AtZ{2}, stateOpening1AtZ{2}, stateOpening2AtZ{2}, stateOpening3AtZ{2}, alpha{2}, alpha2{2}, alpha3{2}, v{2}, query_at_z_1{2}, vk_gate_selector_1{2}.
      elim*=> memory_l stateOpening0AtZ_l stateOpening1AtZ_l stateOpening2AtZ_l stateOpening3AtZ_l stateOpening0AtZ_r stateOpening1AtZ_r stateOpening2AtZ_r stateOpening3AtZ_r alpha_r alpha2_r alpha3_r v_r query_at_z_1_r vk_gate_selector_1_r.
      call (addAssignRescueCustomGateLinearisationContributionWithV_low_equiv_mid memory_l QUERIES_AT_Z_1_X_SLOT stateOpening0AtZ_l stateOpening1AtZ_l stateOpening2AtZ_l stateOpening3AtZ_l stateOpening0AtZ_r stateOpening1AtZ_r stateOpening2AtZ_r stateOpening3AtZ_r alpha_r alpha2_r alpha3_r v_r query_at_z_1_r vk_gate_selector_1_r).
      skip. progress.
      exact to_uint_ge_zero.
      exact to_uint_ge_zero.
      exact to_uint_ge_zero.
      exact to_uint_ge_zero.
      by rewrite /QUERIES_AT_Z_1_X_SLOT W256.of_intN'; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT load_store_diff; [
        progress |
        progress |
        rewrite load_store_same W256.of_uintK pmod_small; [progress; rewrite /Constants.Q in H2; smt () | reflexivity]
      ].
      by rewrite load_store_same W256.of_uintK pmod_small; [progress; rewrite /Constants.Q in H4; smt () | reflexivity].
      by rewrite H1 /VK_GATE_SELECTORS_1_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite H2 /VK_GATE_SELECTORS_1_X_SLOT /VK_GATE_SELECTORS_1_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      rewrite /STATE_V_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT.
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      rewrite /STATE_ALPHA_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT.
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      rewrite /STATE_POWER_OF_ALPHA_2_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT.
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      rewrite /STATE_POWER_OF_ALPHA_3_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT.
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      case H105. progress. right. progress.
      rewrite /addAssignRescue_memory_footprint. simplify.
      rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT.
      rewrite mulAndAddIntoDest_after_mulAndAddIntoDest. by progress. by progress.
      exists (scratch1). exists(scratch2). exists(scratch3). exists(scratch4). reflexivity.
      by progress.


      seq 1 3: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          stateOpening0AtZ{2} = W256.to_uint stateOpening0AtZ{1} /\
          stateOpening1AtZ{2} = W256.to_uint stateOpening1AtZ{1} /\
          stateOpening2AtZ{2} = W256.to_uint stateOpening2AtZ{1} /\
          stateOpening3AtZ{2} = W256.to_uint stateOpening3AtZ{1} /\
          v{2} = W256.to_uint (load mem_0 STATE_V_SLOT) /\
          l0AtZ{2} = W256.to_uint (load mem_0 STATE_L_0_AT_Z_SLOT) /\
          proofLookupGrandProductOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
          alpha6{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_6_SLOT) /\
          zMinusLastOmega{2} = W256.to_uint(load mem_0 STATE_Z_MINUS_LAST_OMEGA_SLOT) /\
          proofLookupTPolyOpeningAtZOmega{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT) /\
          betaLookup{2} = W256.to_uint(load mem_0 STATE_BETA_LOOKUP_SLOT) /\
          proofLookupTPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT) /\
          betaGammaPlusGamma{2} = W256.to_uint(load mem_0 STATE_BETA_GAMMA_PLUS_GAMMA_SLOT) /\
          state_eta{2} = W256.to_uint(load mem_0 STATE_ETA_SLOT) /\
          proofLookupTableTypePolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT) /\
          proofLookupSelectorPolyOpeningAtZ{2} = W256.to_uint(load mem_0 PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT) /\
          gammaLookup{2} = W256.to_uint(load mem_0 STATE_GAMMA_LOOKUP_SLOT) /\
          betaPlusOne{2} = W256.to_uint(load mem_0 STATE_BETA_PLUS_ONE_SLOT) /\
          alpha7{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_7_SLOT) /\
          alpha8{2} = W256.to_uint(load mem_0 STATE_POWER_OF_ALPHA_8_SLOT) /\
          lNMinusOneAtZ{2} = W256.to_uint(load mem_0 STATE_L_N_MINUS_ONE_AT_Z_SLOT) /\
          vk_lookup_table_0{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_X_SLOT) /\
          vk_lookup_table_0{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_Y_SLOT) /\
          vk_lookup_table_1{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_X_SLOT) /\
          vk_lookup_table_1{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_Y_SLOT) /\
          vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
          vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
          vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
          vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
          0 <= vk_lookup_table_0{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_0{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
          stateOpening0AtZ{2} < Constants.R /\
          stateOpening1AtZ{2} < Constants.R /\
          stateOpening2AtZ{2} < Constants.R /\
          stateOpening3AtZ{2} < Constants.R /\
          0 <= proofLookupGrandProductOpeningAtZOmega{2} < Constants.R /\
          0 <= alpha6{2} < Constants.R /\
          0 <= zMinusLastOmega{2} < Constants.R /\
          0 <= v{2} < Constants.R /\
          0 <= proofLookupTPolyOpeningAtZOmega{2} < Constants.R /\
          0 <= betaLookup{2} < Constants.R /\
          0 <= betaGammaPlusGamma{2} < Constants.R /\
          0 <= state_eta{2} < Constants.R /\
          0 <= proofLookupTableTypePolyOpeningAtZ{2} < Constants.R /\
          0 <= proofLookupSelectorPolyOpeningAtZ{2} < Constants.R /\
          0 <= gammaLookup{2} < Constants.R /\
          0 <= betaPlusOne{2} < Constants.R /\
          0 <= alpha7{2} < Constants.R /\
          0 <= alpha8{2} < Constants.R /\
          0 <= l0AtZ{2} < Constants.R /\
          0 <= lNMinusOneAtZ{2} < Constants.R /\
          0 <= query_at_z_0{2}.`1 < FieldQ.p /\
          0 <= query_at_z_0{2}.`2 < FieldQ.p /\
          0 <= query_at_z_1{2}.`1 < FieldQ.p /\
          0 <= query_at_z_1{2}.`2 < FieldQ.p /\
          0 <= copy_permutation_first_aggregated_commitment_coeff{2} < FieldR.p /\
          exists (x0 x32 x64 x96 buffer_x buffer_y: uint256), Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store mem_0
                              QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0{2}.`1))
                            QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0{2}.`2))
                          W256.zero x0)
                        (W256.of_int 32) x32)
                      (W256.of_int 64) x64)
                    (W256.of_int 96) x96)
                  QUERIES_AT_Z_1_X_SLOT (W256.of_int query_at_z_1{2}.`1))
                QUERIES_AT_Z_1_Y_SLOT (W256.of_int query_at_z_1{2}.`2))
              COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int copy_permutation_first_aggregated_commitment_coeff{2}))
            QUERIES_BUFFER_POINT_SLOT buffer_x)
          (QUERIES_BUFFER_POINT_SLOT + (W256.of_int 32)) buffer_y
        )
      ).
      exists* Primops.reverted{1}. elim*=> reverted.
      case reverted. progress.
      conseq (_ : Primops.reverted{1} /\ failed{2}  ==> Primops.reverted{1} /\ failed{2}).
      by progress.
      by progress; left; progress.
      inline AddAssignPermutationLinearisationContributionWithV.mid PointSubAssign.mid PointAddIntoDest.mid PointMulIntoDest.mid PointNegate.mid. wp.
      inline AddAssignPermutationLinearisationContributionWithV.low.
      call{1} pointSubAssign_low_pspec_revert.
      call{1} pointMulIntoDest_low_pspec_revert. wp.
      call{1} ConcretePrimops.mload_pspec_revert. wp.
      call{1} ConcretePrimops.mload_pspec_revert. wp.
      call{1} ConcretePrimops.mload_pspec_revert. wp.
      do 3! call{1} ConcretePrimops.mload_pspec_revert. wp.
      call{1} ConcretePrimops.mload_pspec_revert. wp.
      do 2! call{1} ConcretePrimops.mload_pspec_revert.
      call{1} ConcretePrimops.mstore_pspec_revert. wp.
      call{1} ConcretePrimops.mload_pspec_revert. wp.
      do 2! call{1} ConcretePrimops.mload_pspec_revert. wp.
      do 4! call{1} ConcretePrimops.mload_pspec_revert. wp.
      skip. by progress.

      progress.
      wp.
      exists* Primops.memory{1}, alpha4{2}, alpha5{2}, state_beta{2}, gamma{2}, l0AtZ{2}, stateOpening0AtZ{2}, stateOpening1AtZ{2}, stateOpening2AtZ{2}, stateOpening3AtZ{2}, v{2}, z{2}.
      elim*=> memory_l alpha4_r alpha5_r beta_r gamma_r l0AtZ_r stateOpening0AtZ_r stateOpening1AtZ_r stateOpening2AtZ_r stateOpening3AtZ_r v_r z_r.
      call (addAssignPermutationLinearisationContributionWithV_low_equiv_mid memory_l QUERIES_AT_Z_1_X_SLOT alpha4_r alpha5_r beta_r gamma_r l0AtZ_r stateOpening0AtZ_r stateOpening1AtZ_r stateOpening2AtZ_r stateOpening3AtZ_r v_r z_r).
      skip. progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT W256.of_intN'; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT; progress; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT load_store_diff; [
        progress |
        progress |
        rewrite load_store_same W256.of_uintK pmod_small; progress; rewrite /Constants.Q in H2; smt ()
      ].
      rewrite load_store_same W256.of_uintK pmod_small; progress; rewrite /Constants.Q in H4; smt ().
      by rewrite /VK_PERMUTATION_3_X_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H1 /VK_PERMUTATION_3_X_SLOT; reflexivity.      
      by rewrite /VK_PERMUTATION_3_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H2 /VK_PERMUTATION_3_Y_SLOT; reflexivity.
      by rewrite /STATE_BETA_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_V_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_Z_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_GAMMA_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_POWER_OF_ALPHA_4_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_POWER_OF_ALPHA_5_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_L_0_AT_Z_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT;
        do 8! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      case H104. by progress. progress. right. progress.
      by rewrite -Constants.q_eq_fieldq_p; assumption.
      by rewrite -Constants.q_eq_fieldq_p; assumption.
      by rewrite -Constants.r_eq_fieldr_p; assumption.
      rewrite /addAssignPermutation_memory_footprint. simplify.
      rewrite (load_store_diff _ _ VK_PERMUTATION_3_X_SLOT).
        by rewrite /VK_PERMUTATION_3_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /VK_PERMUTATION_3_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (load_store_diff _ _ VK_PERMUTATION_3_X_SLOT).
        by rewrite /VK_PERMUTATION_3_X_SLOT /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /VK_PERMUTATION_3_X_SLOT /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_PERMUTATION_3_X_SLOT).
        by rewrite /VK_PERMUTATION_3_X_SLOT /QUERIES_AT_Z_1_X_SLOT; progress.
        by rewrite /VK_PERMUTATION_3_X_SLOT /QUERIES_AT_Z_1_X_SLOT; progress.
      do 4! ((rewrite (load_store_diff _ _ VK_PERMUTATION_3_X_SLOT); first  by rewrite /VK_PERMUTATION_3_X_SLOT; progress); first by rewrite /VK_PERMUTATION_3_X_SLOT; progress).
      rewrite (load_store_diff _ _ VK_PERMUTATION_3_X_SLOT).
        by rewrite /VK_PERMUTATION_3_X_SLOT /QUERIES_AT_Z_0_Y_SLOT; progress.
        by rewrite /VK_PERMUTATION_3_X_SLOT /QUERIES_AT_Z_0_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_PERMUTATION_3_X_SLOT).
        by rewrite /VK_PERMUTATION_3_X_SLOT /QUERIES_AT_Z_0_X_SLOT; progress.
        by rewrite /VK_PERMUTATION_3_X_SLOT /QUERIES_AT_Z_0_X_SLOT; progress.
      rewrite (load_store_diff _ _ VK_PERMUTATION_3_Y_SLOT).
        by rewrite /VK_PERMUTATION_3_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /VK_PERMUTATION_3_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (load_store_diff _ _ VK_PERMUTATION_3_Y_SLOT).
        by rewrite /VK_PERMUTATION_3_Y_SLOT /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /VK_PERMUTATION_3_Y_SLOT /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_PERMUTATION_3_Y_SLOT).
        by rewrite /VK_PERMUTATION_3_Y_SLOT /QUERIES_AT_Z_1_X_SLOT; progress.
        by rewrite /VK_PERMUTATION_3_Y_SLOT /QUERIES_AT_Z_1_X_SLOT; progress.
      do 4! ((rewrite (load_store_diff _ _ VK_PERMUTATION_3_Y_SLOT); first  by rewrite /VK_PERMUTATION_3_Y_SLOT; progress); first by rewrite /VK_PERMUTATION_3_Y_SLOT; progress).
      rewrite (load_store_diff _ _ VK_PERMUTATION_3_Y_SLOT).
        by rewrite /VK_PERMUTATION_3_Y_SLOT /QUERIES_AT_Z_0_Y_SLOT; progress.
        by rewrite /VK_PERMUTATION_3_Y_SLOT /QUERIES_AT_Z_0_Y_SLOT; progress.
      rewrite (load_store_diff _ _ VK_PERMUTATION_3_Y_SLOT).
        by rewrite /VK_PERMUTATION_3_Y_SLOT /QUERIES_AT_Z_0_X_SLOT; progress.
        by rewrite /VK_PERMUTATION_3_Y_SLOT /QUERIES_AT_Z_0_X_SLOT; progress.
      rewrite (store_store_swap_diff _ COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF W256.zero).
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_Y_SLOT W256.zero).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_X_SLOT W256.zero).
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
      rewrite (store_store_swap_diff _ (W256.of_int 96) W256.zero). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 64) W256.zero). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 32) W256.zero). by progress. by progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int 32)).
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_Y_SLOT (W256.of_int 32)).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_X_SLOT (W256.of_int 32)).
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
      rewrite (store_store_swap_diff _ (W256.of_int 96) (W256.of_int 32)). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 64) (W256.of_int 32)). by progress. by progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int 64)).
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_Y_SLOT (W256.of_int 64)).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_X_SLOT (W256.of_int 64)).
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
      rewrite (store_store_swap_diff _ (W256.of_int 96) (W256.of_int 64)). by progress. by progress.
      rewrite store_store_same.
      rewrite /pointSubAssign_memory_footprint. simplify.
      rewrite (load_store_diff _ _ QUERIES_AT_Z_1_Y_SLOT).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (load_store_diff _ _ QUERIES_AT_Z_1_Y_SLOT).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (load_store_diff _ _ QUERIES_AT_Z_1_Y_SLOT).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite load_store_same.
      rewrite (load_store_diff _ _ QUERIES_AT_Z_1_X_SLOT).
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (load_store_diff _ _ QUERIES_AT_Z_1_X_SLOT).
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (load_store_diff _ _ QUERIES_AT_Z_1_X_SLOT).
        by rewrite /QUERIES_AT_Z_1_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (load_store_diff _ _ QUERIES_AT_Z_1_X_SLOT).
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite load_store_same.
      rewrite (store_store_swap_diff _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32) W256.zero).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_BUFFER_POINT_SLOT W256.zero).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF W256.zero).
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_Y_SLOT W256.zero).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_X_SLOT W256.zero).
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
      rewrite (store_store_swap_diff _ (W256.of_int 96) W256.zero). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 64) W256.zero). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 32) W256.zero). by progress. by progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32) (W256.of_int 32)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_BUFFER_POINT_SLOT (W256.of_int 32)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int 32)).
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_Y_SLOT (W256.of_int 32)).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_X_SLOT (W256.of_int 32)).
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
      rewrite (store_store_swap_diff _ (W256.of_int 96) (W256.of_int 32)). by progress. by progress.
      rewrite (store_store_swap_diff _ (W256.of_int 64) (W256.of_int 32)). by progress. by progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32) (W256.of_int 64)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_BUFFER_POINT_SLOT (W256.of_int 64)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int 64)).
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_Y_SLOT (W256.of_int 64)).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_X_SLOT (W256.of_int 64)).
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
      rewrite (store_store_swap_diff _ (W256.of_int 96) (W256.of_int 64)). by progress. by progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32) (W256.of_int 96)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_BUFFER_POINT_SLOT (W256.of_int 96)).
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int 96)).
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_Y_SLOT (W256.of_int 96)).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_X_SLOT (W256.of_int 96)).
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT; progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32) QUERIES_AT_Z_1_X_SLOT).
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_BUFFER_POINT_SLOT QUERIES_AT_Z_1_X_SLOT).
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF QUERIES_AT_Z_1_X_SLOT).
        by rewrite /QUERIES_AT_Z_1_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite (store_store_swap_diff _ QUERIES_AT_Z_1_Y_SLOT QUERIES_AT_Z_1_X_SLOT).
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT; progress.
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32) QUERIES_AT_Z_1_Y_SLOT).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ QUERIES_BUFFER_POINT_SLOT QUERIES_AT_Z_1_Y_SLOT).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite (store_store_swap_diff _ COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF QUERIES_AT_Z_1_Y_SLOT).
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
        by rewrite /QUERIES_AT_Z_1_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF; progress.
      rewrite store_store_same.
      exists (W256.of_int query_at_z_1{2}.`1).
      exists (W256.of_int query_at_z_1{2}.`2).
      exists x640.
      exists x960.
      exists (W256.of_int buffer_p.`1).
      exists (W256.of_int buffer_p.`2).
      reflexivity.      


      seq 1 1: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          state_eta{2} = W256.to_uint(load mem_0 STATE_ETA_SLOT) /\
          vk_lookup_table_0{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_X_SLOT) /\
          vk_lookup_table_0{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_0_Y_SLOT) /\
          vk_lookup_table_1{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_X_SLOT) /\
          vk_lookup_table_1{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_Y_SLOT) /\
          vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
          vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
          vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
          vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
          0 <= vk_lookup_table_0{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_0{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
          0 <= query_at_z_0{2}.`1 < FieldQ.p /\
          0 <= query_at_z_0{2}.`2 < FieldQ.p /\
          0 <= query_at_z_1{2}.`1 < FieldQ.p /\
          0 <= query_at_z_1{2}.`2 < FieldQ.p /\
          0 <= copy_permutation_first_aggregated_commitment_coeff{2} < FieldR.p /\
          0 <= lookupSFirstAggregatedCommitment{2} < FieldR.p /\
          0 <= lookupGrandProductFirstAggregatedCoefficient{2} < FieldR.p /\
          exists (x0 x32 x64 x96 buffer_x buffer_y: uint256), Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
                                  QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0{2}.`1))
                                QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0{2}.`2))
                              W256.zero x0)
                            (W256.of_int 32) x32)
                          (W256.of_int 64) x64)
                        (W256.of_int 96) x96)
                      QUERIES_AT_Z_1_X_SLOT (W256.of_int query_at_z_1{2}.`1))
                    QUERIES_AT_Z_1_Y_SLOT (W256.of_int query_at_z_1{2}.`2))
                  COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int copy_permutation_first_aggregated_commitment_coeff{2}))
                QUERIES_BUFFER_POINT_SLOT buffer_x)
              (QUERIES_BUFFER_POINT_SLOT + (W256.of_int 32)) buffer_y)
            LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int lookupSFirstAggregatedCommitment{2}))
          LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int lookupGrandProductFirstAggregatedCoefficient{2})
        )
      ).
      exists* Primops.reverted{1}. elim*=> reverted.
      case reverted. progress.
      conseq (_ : Primops.reverted{1} /\ failed{2}  ==> Primops.reverted{1} /\ failed{2}).
      by progress.
      by progress; left; progress.
      inline AddAssignLookupLinearisationContributionWithV.mid.
      inline AddAssignLookupLinearisationContributionWithV.low.
      inline*. wp. skip. by progress.

      progress.
      wp.
      exists* Primops.memory{1}, stateOpening0AtZ{1}, stateOpening1AtZ{1}, stateOpening2AtZ{1}, stateOpening0AtZ{2}, stateOpening1AtZ{2}, stateOpening2AtZ{2}, proofLookupGrandProductOpeningAtZOmega{2}, alpha6{2}, zMinusLastOmega{2}, v{2}, proofLookupTPolyOpeningAtZOmega{2}, betaLookup{2}, proofLookupTPolyOpeningAtZ{2}, betaGammaPlusGamma{2}, state_eta{2}, proofLookupTableTypePolyOpeningAtZ{2}, proofLookupSelectorPolyOpeningAtZ{2}, gammaLookup{2}, betaPlusOne{2}, alpha7{2}, l0AtZ{2}, alpha8{2}, lNMinusOneAtZ{2}.
      elim*=> memory_l stateOpening0AtZ_l stateOpening1AtZ_l stateOpening2AtZ_l stateOpening0AtZ_r stateOpening1AtZ_r stateOpening2AtZ_r proofLookupGrandProductOpeningAtZOmega_r alpha6_r zMinusLastOmega_r v_r proofLookupTPolyOpeningAtZOmega_r betaLookup_r proofLookupTPolyOpeningAtZ_r betaGammaPlusGamma_r state_eta_r proofLookupTableTypePolyOpeningAtZ_r proofLookupSelectorPolyOpeningAtZ_r gammaLookup_r betaPlusOne_r alpha7_r l0AtZ_r alpha8_r lNMinusOneAtZ_r.
      call (addAssignLookupLinearisationContributionWithV_low_equiv_mid memory_l QUERIES_AT_Z_1_X_SLOT stateOpening0AtZ_l stateOpening1AtZ_l stateOpening2AtZ_l stateOpening0AtZ_r stateOpening1AtZ_r stateOpening2AtZ_r proofLookupGrandProductOpeningAtZOmega_r alpha6_r zMinusLastOmega_r v_r proofLookupTPolyOpeningAtZOmega_r betaLookup_r proofLookupTPolyOpeningAtZ_r betaGammaPlusGamma_r state_eta_r proofLookupTableTypePolyOpeningAtZ_r proofLookupSelectorPolyOpeningAtZ_r gammaLookup_r betaPlusOne_r alpha7_r l0AtZ_r alpha8_r lNMinusOneAtZ_r).
      skip. progress.
      exact to_uint_ge_zero.
      exact to_uint_ge_zero.
      exact to_uint_ge_zero.
      by rewrite /PROOF_LOOKUP_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_POWER_OF_ALPHA_6_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_Z_MINUS_LAST_OMEGA_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_V_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_OMEGA_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_BETA_LOOKUP_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_LOOKUP_T_POLY_OPENING_AT_Z_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_BETA_GAMMA_PLUS_GAMMA_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_ETA_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_LOOKUP_TABLE_TYPE_POLY_OPENING_AT_Z_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /PROOF_LOOKUP_SELECTOR_POLY_OPENING_AT_Z_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_GAMMA_LOOKUP_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_BETA_PLUS_ONE_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_POWER_OF_ALPHA_7_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_L_0_AT_Z_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_POWER_OF_ALPHA_8_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /STATE_L_N_MINUS_ONE_AT_Z_SLOT /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_0_X_SLOT;
        do 11! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite -Constants.r_eq_fieldr_p; assumption.
      by rewrite -Constants.r_eq_fieldr_p; assumption.
      by rewrite /addAssignLookupLinearisationContributionWithV_memory_footprint;
        exists (x0); exists (x32); exists (x64); exists (x96); exists (buffer_x); exists (buffer_y); progress.


      seq 6 2: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          state_eta{2} = W256.to_uint eta'{1} /\
          currentEta{2} = W256.to_uint currentEta{1} /\
          currentEta{2} = state_eta{2} /\
          vk_lookup_table_1{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_X_SLOT) /\
          vk_lookup_table_1{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_1_Y_SLOT) /\
          vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
          vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
          vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
          vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
          0 <= query_t_poly_aggregated{2}.`1 < FieldQ.p /\
          0 <= query_t_poly_aggregated{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_1{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
          0 <= query_at_z_0{2}.`1 < FieldQ.p /\
          0 <= query_at_z_0{2}.`2 < FieldQ.p /\
          0 <= query_at_z_1{2}.`1 < FieldQ.p /\
          0 <= query_at_z_1{2}.`2 < FieldQ.p /\
          0 <= copy_permutation_first_aggregated_commitment_coeff{2} < FieldR.p /\
          0 <= lookupSFirstAggregatedCommitment{2} < FieldR.p /\
          0 <= lookupGrandProductFirstAggregatedCoefficient{2} < FieldR.p /\
          exists (x0 x32 x64 x96 buffer_x buffer_y: uint256), Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
                                      QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0{2}.`1))
                                    QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0{2}.`2))
                                  W256.zero x0)
                                (W256.of_int 32) x32)
                              (W256.of_int 64) x64)
                            (W256.of_int 96) x96)
                          QUERIES_AT_Z_1_X_SLOT (W256.of_int query_at_z_1{2}.`1))
                        QUERIES_AT_Z_1_Y_SLOT (W256.of_int query_at_z_1{2}.`2))
                      COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int copy_permutation_first_aggregated_commitment_coeff{2}))
                    QUERIES_BUFFER_POINT_SLOT buffer_x)
                  (QUERIES_BUFFER_POINT_SLOT + (W256.of_int 32)) buffer_y)
                LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int lookupSFirstAggregatedCommitment{2}))
              LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int lookupGrandProductFirstAggregatedCoefficient{2}))
            QUERIES_T_POLY_AGGREGATED_X_SLOT (W256.of_int query_t_poly_aggregated{2}.`1))
          QUERIES_T_POLY_AGGREGATED_Y_SLOT (W256.of_int query_t_poly_aggregated{2}.`2)
        )
      ).
      exists* Primops.reverted{1}. elim*=>reverted.
      case reverted.
      progress.
      inline*. wp. skip. by progress.

      progress.
      inline*. wp. skip. progress.
      by rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /VK_LOOKUP_TABLE_0_X_SLOT /VK_LOOKUP_TABLE_0_Y_SLOT /STATE_ETA_SLOT;
        do 15! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /VK_LOOKUP_TABLE_0_X_SLOT /VK_LOOKUP_TABLE_0_Y_SLOT /STATE_ETA_SLOT;
        do 15! ((rewrite load_store_diff; first by progress); first by progress);
        reflexivity.
      by rewrite H1 H2 /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /VK_LOOKUP_TABLE_0_X_SLOT /VK_LOOKUP_TABLE_0_Y_SLOT /STATE_ETA_SLOT;
        do 27! ((rewrite load_store_diff; first by progress); first by progress);
        smt ().

      seq 1 3: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          state_eta{2} = W256.to_uint eta'{1} /\
          currentEta{2} = W256.to_uint currentEta{1} /\
          vk_lookup_table_2{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_X_SLOT) /\
          vk_lookup_table_2{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_2_Y_SLOT) /\
          vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
          vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
          0 <= query_t_poly_aggregated{2}.`1 < FieldQ.p /\
          0 <= query_t_poly_aggregated{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_2{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
          0 <= query_at_z_0{2}.`1 < FieldQ.p /\
          0 <= query_at_z_0{2}.`2 < FieldQ.p /\
          0 <= query_at_z_1{2}.`1 < FieldQ.p /\
          0 <= query_at_z_1{2}.`2 < FieldQ.p /\
          0 <= copy_permutation_first_aggregated_commitment_coeff{2} < FieldR.p /\
          0 <= lookupSFirstAggregatedCommitment{2} < FieldR.p /\
          0 <= lookupGrandProductFirstAggregatedCoefficient{2} < FieldR.p /\
          exists (x0 x32 x64 x96 buffer_x buffer_y: uint256), Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
                                      QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0{2}.`1))
                                    QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0{2}.`2))
                                  W256.zero x0)
                                (W256.of_int 32) x32)
                              (W256.of_int 64) x64)
                            (W256.of_int 96) x96)
                          QUERIES_AT_Z_1_X_SLOT (W256.of_int query_at_z_1{2}.`1))
                        QUERIES_AT_Z_1_Y_SLOT (W256.of_int query_at_z_1{2}.`2))
                      COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int copy_permutation_first_aggregated_commitment_coeff{2}))
                    QUERIES_BUFFER_POINT_SLOT buffer_x)
                  (QUERIES_BUFFER_POINT_SLOT + (W256.of_int 32)) buffer_y)
                LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int lookupSFirstAggregatedCommitment{2}))
              LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int lookupGrandProductFirstAggregatedCoefficient{2}))
            QUERIES_T_POLY_AGGREGATED_X_SLOT (W256.of_int query_t_poly_aggregated{2}.`1))
          QUERIES_T_POLY_AGGREGATED_Y_SLOT (W256.of_int query_t_poly_aggregated{2}.`2)
        )
      ).
      exists* Primops.reverted{1}. elim*=> reverted.
      case reverted.
      progress.
      call{1} pointMulAndAddIntoDest_low_pspec_revert.
      inline*. wp. skip. progress. left. progress. left. assumption.

      progress.
      wp.
      exists* vk_lookup_table_1{2}, query_t_poly_aggregated{2}, currentEta{2}, Primops.memory{1}.
      elim*=> vk_lookup_table_1_r query_t_poly_aggregated_r currentEta_r memory_l.
      call (pointMulAndAddIntoDest_low_equiv_mid vk_lookup_table_1_r.`1 vk_lookup_table_1_r.`2 query_t_poly_aggregated_r.`1 query_t_poly_aggregated_r.`2 currentEta_r VK_LOOKUP_TABLE_1_X_SLOT QUERIES_T_POLY_AGGREGATED_X_SLOT memory_l).
      skip.
      progress.
      exact to_uint_ge_zero.
      exact to_uint_lt_mod.
      by rewrite /VK_LOOKUP_TABLE_1_X_SLOT W256.of_intN'; progress.
      by rewrite /VK_LOOKUP_TABLE_1_X_SLOT; progress; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT W256.of_intN'; progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT; progress; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /VK_LOOKUP_TABLE_0_X_SLOT /VK_LOOKUP_TABLE_0_Y_SLOT /VK_LOOKUP_TABLE_1_X_SLOT;
        do 15! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H2;
        by progress.
      by rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /VK_LOOKUP_TABLE_0_X_SLOT /VK_LOOKUP_TABLE_0_Y_SLOT /VK_LOOKUP_TABLE_1_X_SLOT;
        do 15! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H3;
        by progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT;
        ((rewrite load_store_diff; first by progress); first by progress);
        rewrite load_store_same; reflexivity.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT;
        rewrite load_store_same; reflexivity.
      by apply uint256_eq_of_eq; rewrite H1; reflexivity.
      case H60. progress. case H61. progress. right. progress.
      exact F_to_int_point_1_ge_zero.
      exact F_to_int_point_1_lt_p.
      exact F_to_int_point_2_ge_zero.
      exact F_to_int_point_2_lt_p.
      rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT.
      do 12! ((rewrite (store_store_swap_diff _ _ W256.zero); first by progress); first by progress).
      rewrite store_store_same.
      do 11! ((rewrite (store_store_swap_diff _ _ (W256.of_int 32)); first by progress); first by progress).
      rewrite store_store_same.
      do 10! ((rewrite (store_store_swap_diff _ _ (W256.of_int 64)); first by progress); first by progress).
      rewrite store_store_same.
      do 9! ((rewrite (store_store_swap_diff _ _ (W256.of_int 96)); first by progress); first by progress).
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ QUERIES_T_POLY_AGGREGATED_X_SLOT).
        rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT. by progress.
        rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT. by progress.
      rewrite store_store_same.
      rewrite store_store_same.
      rewrite /F_to_int_point. simplify.
      exists (W256.of_int (FieldQ.asint x)).
      exists (W256.of_int (FieldQ.asint y)).
      exists (W256.of_int query_t_poly_aggregated{2}.`1).
      exists (W256.of_int query_t_poly_aggregated{2}.`2).
      exists (buffer_x). exists (buffer_y).
      reflexivity.

      by progress. by progress.
      

      seq 2 4: (
        (Primops.reverted{1} /\ failed{2}) \/
        (
          !Primops.reverted{1} /\
          !failed{2} /\
          state_eta{2} = W256.to_uint eta'{1} /\
          currentEta{2} = W256.to_uint currentEta{1} /\
          vk_lookup_table_3{2}.`1 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_X_SLOT) /\
          vk_lookup_table_3{2}.`2 = W256.to_uint(load mem_0 VK_LOOKUP_TABLE_3_Y_SLOT) /\
          0 <= query_t_poly_aggregated{2}.`1 < FieldQ.p /\
          0 <= query_t_poly_aggregated{2}.`2 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`1 < FieldQ.p /\
          0 <= vk_lookup_table_3{2}.`2 < FieldQ.p /\
          0 <= query_at_z_0{2}.`1 < FieldQ.p /\
          0 <= query_at_z_0{2}.`2 < FieldQ.p /\
          0 <= query_at_z_1{2}.`1 < FieldQ.p /\
          0 <= query_at_z_1{2}.`2 < FieldQ.p /\
          0 <= copy_permutation_first_aggregated_commitment_coeff{2} < FieldR.p /\
          0 <= lookupSFirstAggregatedCommitment{2} < FieldR.p /\
          0 <= lookupGrandProductFirstAggregatedCoefficient{2} < FieldR.p /\
          exists (x0 x32 x64 x96 buffer_x buffer_y: uint256), Primops.memory{1} = store(store(store(store(store(store(store(store(store(store(store(store(store(store(store mem_0
                                      QUERIES_AT_Z_0_X_SLOT (W256.of_int query_at_z_0{2}.`1))
                                    QUERIES_AT_Z_0_Y_SLOT (W256.of_int query_at_z_0{2}.`2))
                                  W256.zero x0)
                                (W256.of_int 32) x32)
                              (W256.of_int 64) x64)
                            (W256.of_int 96) x96)
                          QUERIES_AT_Z_1_X_SLOT (W256.of_int query_at_z_1{2}.`1))
                        QUERIES_AT_Z_1_Y_SLOT (W256.of_int query_at_z_1{2}.`2))
                      COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int copy_permutation_first_aggregated_commitment_coeff{2}))
                    QUERIES_BUFFER_POINT_SLOT buffer_x)
                  (QUERIES_BUFFER_POINT_SLOT + (W256.of_int 32)) buffer_y)
                LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int lookupSFirstAggregatedCommitment{2}))
              LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int lookupGrandProductFirstAggregatedCoefficient{2}))
            QUERIES_T_POLY_AGGREGATED_X_SLOT (W256.of_int query_t_poly_aggregated{2}.`1))
          QUERIES_T_POLY_AGGREGATED_Y_SLOT (W256.of_int query_t_poly_aggregated{2}.`2)
        )
      ).
      exists* Primops.reverted{1}. elim*=> reverted.
      case reverted.
      progress.
      call{1} pointMulAndAddIntoDest_low_pspec_revert.
      inline*. wp. skip. progress. left. progress. left. assumption.

      progress.
      wp. sp.
      exists* vk_lookup_table_2{2}, query_t_poly_aggregated{2}, currentEta{2}, Primops.memory{1}.
      elim*=> vk_lookup_table_2_r query_t_poly_aggregated_r currentEta_r memory_l.
      progress.
      call (pointMulAndAddIntoDest_low_equiv_mid vk_lookup_table_2_r.`1 vk_lookup_table_2_r.`2 query_t_poly_aggregated_r.`1 query_t_poly_aggregated_r.`2 currentEta_r VK_LOOKUP_TABLE_2_X_SLOT QUERIES_T_POLY_AGGREGATED_X_SLOT memory_l).
      skip. progress.
      by rewrite /Constants.R; exact modz_ge0.
      by apply (lt_trans _ Constants.R); rewrite /Constants.R; [exact ltz_pmod | progress].
      by rewrite /VK_LOOKUP_TABLE_2_X_SLOT W256.of_intN'; progress.
      by rewrite /VK_LOOKUP_TABLE_2_X_SLOT; progress; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT W256.of_intN'; progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT; progress; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT /VK_LOOKUP_TABLE_2_X_SLOT;
        do 15! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H1; by progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT /VK_LOOKUP_TABLE_2_X_SLOT;
        do 15! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H2; by progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT load_store_diff; [
        progress |
        progress |
        rewrite load_store_same; reflexivity
      ].
      by rewrite load_store_same; reflexivity.
      by rewrite /mulmod -Constants.R_int; progress.
      case H54. progress. case H55. progress. right. progress.
      by rewrite /mulmod -Constants.R_int; progress; rewrite W256.of_uintK mod_R_W256_mod_R; reflexivity.
      exact F_to_int_point_1_ge_zero.
      exact F_to_int_point_1_lt_p.
      exact F_to_int_point_2_ge_zero.
      exact F_to_int_point_2_lt_p.
      rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT.
      do 12! ((rewrite (store_store_swap_diff _ _ W256.zero); first by progress); first by progress).
      rewrite store_store_same.
      do 11! ((rewrite (store_store_swap_diff _ _ (W256.of_int 32)); first by progress); first by progress).
      rewrite store_store_same.
      do 10! ((rewrite (store_store_swap_diff _ _ (W256.of_int 64)); first by progress); first by progress).
      rewrite store_store_same.
      do 9! ((rewrite (store_store_swap_diff _ _ (W256.of_int 96)); first by progress); first by progress).
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ QUERIES_T_POLY_AGGREGATED_X_SLOT).
        rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT. by progress.
        rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT. by progress.
      rewrite store_store_same.
      rewrite store_store_same.
      rewrite /F_to_int_point. simplify.
      exists (W256.of_int (FieldQ.asint x)).
      exists (W256.of_int (FieldQ.asint y)).
      exists (W256.of_int query_t_poly_aggregated{2}.`1).
      exists (W256.of_int query_t_poly_aggregated{2}.`2).
      exists (buffer_x). exists (buffer_y).
      reflexivity.

      by progress. by progress.
      
      (* final segment *)
      exists* Primops.reverted{1}. elim*=> reverted.
      case reverted. progress.
      conseq (_ : (Primops.reverted{1} /\ failed{2}) ==> (Primops.reverted{1} /\ ret{2} = None)).
      by progress. by progress.
      sp. wp.
      call{1} pointMulAndAddIntoDest_low_pspec_revert.
      inline*. wp. skip. progress. left. assumption.

      progress.
      sp.
      exists* vk_lookup_table_3{2}, query_t_poly_aggregated{2}, currentEta{2}, Primops.memory{1}.
      elim*=> vk_lookup_table_3_r query_t_poly_aggregated_r currentEta_r memory_l.
      progress. wp.
      call (pointMulAndAddIntoDest_low_equiv_mid vk_lookup_table_3_r.`1 vk_lookup_table_3_r.`2 query_t_poly_aggregated_r.`1 query_t_poly_aggregated_r.`2 currentEta_r VK_LOOKUP_TABLE_3_X_SLOT QUERIES_T_POLY_AGGREGATED_X_SLOT memory_l).
      skip. progress.
      by rewrite /Constants.R; exact modz_ge0.
      by apply (lt_trans _ Constants.R); rewrite /Constants.R; [exact ltz_pmod | progress].
      by rewrite /VK_LOOKUP_TABLE_3_X_SLOT W256.of_intN'; progress.
      by rewrite /VK_LOOKUP_TABLE_3_X_SLOT; progress; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT W256.of_intN'; progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT; progress; rewrite W256.of_intN'; progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /VK_LOOKUP_TABLE_3_X_SLOT;
        do 15! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H1; by progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT /VK_LOOKUP_TABLE_3_X_SLOT;
        do 15! ((rewrite load_store_diff; first by progress); first by progress);
        rewrite H2; by progress.
      by rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT load_store_diff; [
        progress |
        progress |
        rewrite load_store_same; reflexivity
      ].
      by rewrite load_store_same; reflexivity.
      by rewrite /mulmod -Constants.R_int; progress; rewrite W256.of_uintK mod_R_W256_mod_R; reflexivity.
      case H48. progress. case H49. by progress. progress. case H50. by progress. by progress. by progress.
      case H48. progress. case H50. by progress. by progress. by progress.
      case H48. progress. case H50. progress.
      rewrite /prepareQueries_memory_footprint. simplify.
      exists (W256.of_int (FieldQ.asint x)).
      exists (W256.of_int (FieldQ.asint y)).
      exists (W256.of_int (query_t_poly_aggregated{2}.`1)).
      exists (W256.of_int (query_t_poly_aggregated{2}.`2)).
      exists (buffer_x). exists (buffer_y).
      exists (query_at_z_0{2}).
      exists (query_at_z_1{2}).
      exists (F_to_int_point (x', y')).
      exists (copy_permutation_first_aggregated_commitment_coeff{2}).
      exists (lookupSFirstAggregatedCommitment{2}).
      exists (lookupGrandProductFirstAggregatedCoefficient{2}).
      rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT /QUERIES_T_POLY_AGGREGATED_Y_SLOT /LOOKUP_GRAND_PRODUCT_FIRST_AGGREGATED_COMMITMENT_COEFF /LOOKUP_S_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_BUFFER_POINT_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /QUERIES_AT_Z_1_X_SLOT /QUERIES_AT_Z_1_Y_SLOT.
      do 12! ((rewrite (store_store_swap_diff _ _ W256.zero); first by progress); first by progress).
      rewrite store_store_same.
      do 11! ((rewrite (store_store_swap_diff _ _ (W256.of_int 32)); first by progress); first by progress).
      rewrite store_store_same.
      do 10! ((rewrite (store_store_swap_diff _ _ (W256.of_int 64)); first by progress); first by progress).
      rewrite store_store_same.
      do 9! ((rewrite (store_store_swap_diff _ _ (W256.of_int 96)); first by progress); first by progress).
      rewrite store_store_same.
      rewrite (store_store_swap_diff _ _ QUERIES_T_POLY_AGGREGATED_X_SLOT).
        rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT. by progress.
        rewrite /QUERIES_T_POLY_AGGREGATED_X_SLOT. by progress.
      rewrite store_store_same.
      rewrite store_store_same.
      rewrite /QUERIES_AT_Z_0_X_SLOT /QUERIES_AT_Z_0_Y_SLOT.
      (rewrite (store_store_swap_diff _ _ W256.zero); first by progress); first by progress.
      (rewrite (store_store_swap_diff _ _ W256.zero); first by progress); first by progress.
      (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); first by progress); first by progress.
      (rewrite (store_store_swap_diff _ _ (W256.of_int 32)); first by progress); first by progress.
      (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); first by progress); first by progress.
      (rewrite (store_store_swap_diff _ _ (W256.of_int 64)); first by progress); first by progress.
      (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); first by progress); first by progress.
      (rewrite (store_store_swap_diff _ _ (W256.of_int 96)); first by progress); first by progress.
      rewrite /F_to_int_point. progress.
      (rewrite (store_store_swap_diff _ _ QUERIES_BUFFER_POINT_SLOT); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      (rewrite (store_store_swap_diff _ _ QUERIES_BUFFER_POINT_SLOT); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      (rewrite (store_store_swap_diff _ _ QUERIES_BUFFER_POINT_SLOT); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      (rewrite (store_store_swap_diff _ _ QUERIES_BUFFER_POINT_SLOT); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      (rewrite (store_store_swap_diff _ _ QUERIES_BUFFER_POINT_SLOT); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      (rewrite (store_store_swap_diff _ _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32)); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      (rewrite (store_store_swap_diff _ _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32)); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      (rewrite (store_store_swap_diff _ _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32)); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      (rewrite (store_store_swap_diff _ _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32)); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      (rewrite (store_store_swap_diff _ _ (QUERIES_BUFFER_POINT_SLOT + W256.of_int 32)); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress); first by rewrite /QUERIES_BUFFER_POINT_SLOT; progress.
      rewrite /QUERIES_BUFFER_POINT_SLOT; by progress.
      exact FieldQ.ge0_asint.
      exact FieldQ.gtp_asint.
      exact FieldQ.ge0_asint.
      exact FieldQ.gtp_asint.
      by progress.
      by progress.
qed.

lemma prepareQueries_mid_equiv_high_encapsulated:
    equiv [
      PrepareQueries.mid ~ PrepareQueries.high_encapsulated:
      zInDomainSize{1} = FieldR.asint zInDomainSize{2} /\
      quotient_poly_part_0{1} = F_to_int_point(aspoint_G1 quotient_poly_part_0{2}) /\
      quotient_poly_part_1{1} = F_to_int_point(aspoint_G1 quotient_poly_part_1{2}) /\
      quotient_poly_part_2{1} = F_to_int_point(aspoint_G1 quotient_poly_part_2{2}) /\
      quotient_poly_part_3{1} = F_to_int_point(aspoint_G1 quotient_poly_part_3{2}) /\
      stateOpening0AtZ{1} = FieldR.asint stateOpening0AtZ{2} /\
      stateOpening1AtZ{1} = FieldR.asint stateOpening1AtZ{2} /\
      stateOpening2AtZ{1} = FieldR.asint stateOpening2AtZ{2} /\
      stateOpening3AtZ{1} = FieldR.asint stateOpening3AtZ{2} /\
      vk_lookup_table_0{1} = F_to_int_point(aspoint_G1 vk_lookup_table_0{2}) /\
      vk_lookup_table_1{1} = F_to_int_point(aspoint_G1 vk_lookup_table_1{2}) /\
      vk_lookup_table_2{1} = F_to_int_point(aspoint_G1 vk_lookup_table_2{2}) /\
      vk_lookup_table_3{1} = F_to_int_point(aspoint_G1 vk_lookup_table_3{2}) /\
      state_eta{1} = FieldR.asint state_eta{2} /\
      vk_gate_setup_0{1} = F_to_int_point(aspoint_G1 vk_gate_setup_0{2}) /\
      vk_gate_setup_1{1} = F_to_int_point(aspoint_G1 vk_gate_setup_1{2}) /\
      vk_gate_setup_2{1} = F_to_int_point(aspoint_G1 vk_gate_setup_2{2}) /\
      vk_gate_setup_3{1} = F_to_int_point(aspoint_G1 vk_gate_setup_3{2}) /\
      vk_gate_setup_4{1} = F_to_int_point(aspoint_G1 vk_gate_setup_4{2}) /\
      vk_gate_setup_5{1} = F_to_int_point(aspoint_G1 vk_gate_setup_5{2}) /\
      vk_gate_setup_6{1} = F_to_int_point(aspoint_G1 vk_gate_setup_6{2}) /\
      vk_gate_setup_7{1} = F_to_int_point(aspoint_G1 vk_gate_setup_7{2}) /\
      poly3_omega{1} = FieldR.asint poly3_omega{2} /\
      v{1} = FieldR.asint v{2} /\
      z{1} = FieldR.asint z{2} /\
      gate_selector_0_opening{1} = FieldR.asint gate_selector_0_opening{2} /\
      alpha{1} = FieldR.asint alpha{2} /\
      alpha2{1} = FieldR.asint alpha2{2} /\
      alpha3{1} = FieldR.asint alpha3{2} /\
      alpha4{1} = FieldR.asint alpha4{2} /\
      alpha5{1} = FieldR.asint alpha5{2} /\
      alpha6{1} = FieldR.asint alpha6{2} /\
      alpha7{1} = FieldR.asint alpha7{2} /\
      alpha8{1} = FieldR.asint alpha8{2} /\
      state_beta{1} = FieldR.asint state_beta{2} /\
      gamma{1} = FieldR.asint gamma{2} /\
      vk_gate_selector_1{1} = F_to_int_point(aspoint_G1 vk_gate_selector_1{2}) /\
      vk_permutation_3{1} = F_to_int_point(aspoint_G1 vk_permutation_3{2}) /\
      gp_omega{1} = FieldR.asint gp_omega{2} /\
      l0AtZ{1} = FieldR.asint l0AtZ{2} /\
      poly0_opening{1} = FieldR.asint poly0_opening{2} /\
      poly1_opening{1} = FieldR.asint poly1_opening{2} /\
      poly2_opening{1} = FieldR.asint poly2_opening{2} /\
      proofLookupGrandProductOpeningAtZOmega{1} = FieldR.asint proofLookupGrandProductOpeningAtZOmega{2} /\
      zMinusLastOmega{1} = FieldR.asint zMinusLastOmega{2} /\
      proofLookupTPolyOpeningAtZOmega{1} = FieldR.asint proofLookupTPolyOpeningAtZOmega{2} /\
      betaLookup{1} = FieldR.asint betaLookup{2} /\
      proofLookupTPolyOpeningAtZ{1} = FieldR.asint proofLookupTPolyOpeningAtZ{2} /\
      betaGammaPlusGamma{1} = FieldR.asint betaGammaPlusGamma{2} /\
      proofLookupTableTypePolyOpeningAtZ{1} = FieldR.asint proofLookupTableTypePolyOpeningAtZ{2} /\
      proofLookupSelectorPolyOpeningAtZ{1} = FieldR.asint proofLookupSelectorPolyOpeningAtZ{2} /\
      gammaLookup{1} = FieldR.asint gammaLookup{2} /\
      betaPlusOne{1} = FieldR.asint betaPlusOne{2} /\
      lNMinusOneAtZ{1} = FieldR.asint lNMinusOneAtZ{2} ==>
      res{1} = Some(
        F_to_int_point(aspoint_G1 res{2}.`1),
        F_to_int_point(aspoint_G1 res{2}.`2),
        FieldR.asint res{2}.`3,
        FieldR.asint res{2}.`4,
        FieldR.asint res{2}.`5,
        F_to_int_point(aspoint_G1 res{2}.`6)
      )
    ].
    proof.
      proc.
      simplify.
      seq 5 2: (
        #pre /\
        !failed{1} /\
        zInDomainSize{1} = FieldR.asint zInDomainSize{2} /\
        query_at_z_0{1} = F_to_int_point(aspoint_G1 query_at_z_0{2})
      ).
      wp.
      call pointMulAndAddIntoDest_mid_equiv_high.
      wp. skip. by progress.
      seq 4 2: (
        #pre /\
        currentZ{1} = FieldR.asint currentZ{2}
      ).
      wp.
      call pointMulAndAddIntoDest_mid_equiv_high.
      wp. skip. progress.
      rewrite Constants.r_eq_fieldr_p.
      rewrite FieldR.mulE. reflexivity.

      seq 4 2: #pre.
      wp.
      call pointMulAndAddIntoDest_mid_equiv_high.
      wp. skip. progress.
      rewrite Constants.r_eq_fieldr_p.
      rewrite FieldR.mulE. reflexivity.

      seq 3 1: (
        #pre /\
        query_at_z_1{1} = F_to_int_point(aspoint_G1 query_at_z_1{2})
      ).
      wp.
      call mainGateLinearisation_mid_equiv_high.
      skip. by progress.

      seq 3 1: #pre.
      wp.
      call addAssignRescueCustomGateLinearisationContributionWithV_mid_equiv_high.
      skip. by progress.

      seq 3 1: (
        #pre /\
        copy_permutation_first_aggregated_commitment_coeff{1} = FieldR.asint copy_permutation_first_aggregated_commitment_coeff{2}
      ).
      wp.
      call addAssignPermutationLinearisationContributionWithV_mid_equiv_high.
      skip. by progress.

      seq 1 1: (
        #pre /\
        lookupSFirstAggregatedCommitment{1} = FieldR.asint lookupSFirstAggregatedCommitment{2} /\
        lookupGrandProductFirstAggregatedCoefficient{1} = FieldR.asint lookupGrandProductFirstAggregatedCoefficient{2}
      ).
      call addAssignLookupLinearisationContributionWithV_mid_equiv_high.
      wp. skip. by progress.

      seq 5 3: (
        #pre /\
        currentEta{1} = FieldR.asint currentEta{2} /\
        query_t_poly_aggregated{1} = F_to_int_point(aspoint_G1 query_t_poly_aggregated{2})
      ).
      wp.
      call pointMulAndAddIntoDest_mid_equiv_high.
      wp. skip. by progress.

      seq 4 2: #pre.
      wp.
      call pointMulAndAddIntoDest_mid_equiv_high.
      wp. skip. progress.
      rewrite Constants.r_eq_fieldr_p FieldR.mulE. reflexivity.

      seq 4 2: #pre.
      wp.
      call pointMulAndAddIntoDest_mid_equiv_high.
      wp. skip. progress.
      rewrite Constants.r_eq_fieldr_p FieldR.mulE. reflexivity.

      wp. skip. by progress.
qed.

lemma prepareQueries_mid_equiv_high:
    equiv [
      PrepareQueries.mid ~ PrepareQueries.high:
      zInDomainSize{1} = FieldR.asint zInDomainSize{2} /\
      quotient_poly_part_0{1} = F_to_int_point(aspoint_G1 quotient_poly_part_0{2}) /\
      quotient_poly_part_1{1} = F_to_int_point(aspoint_G1 quotient_poly_part_1{2}) /\
      quotient_poly_part_2{1} = F_to_int_point(aspoint_G1 quotient_poly_part_2{2}) /\
      quotient_poly_part_3{1} = F_to_int_point(aspoint_G1 quotient_poly_part_3{2}) /\
      stateOpening0AtZ{1} = FieldR.asint stateOpening0AtZ{2} /\
      stateOpening1AtZ{1} = FieldR.asint stateOpening1AtZ{2} /\
      stateOpening2AtZ{1} = FieldR.asint stateOpening2AtZ{2} /\
      stateOpening3AtZ{1} = FieldR.asint stateOpening3AtZ{2} /\
      vk_lookup_table_0{1} = F_to_int_point(aspoint_G1 vk_lookup_table_0{2}) /\
      vk_lookup_table_1{1} = F_to_int_point(aspoint_G1 vk_lookup_table_1{2}) /\
      vk_lookup_table_2{1} = F_to_int_point(aspoint_G1 vk_lookup_table_2{2}) /\
      vk_lookup_table_3{1} = F_to_int_point(aspoint_G1 vk_lookup_table_3{2}) /\
      state_eta{1} = FieldR.asint state_eta{2} /\
      vk_gate_setup_0{1} = F_to_int_point(aspoint_G1 vk_gate_setup_0{2}) /\
      vk_gate_setup_1{1} = F_to_int_point(aspoint_G1 vk_gate_setup_1{2}) /\
      vk_gate_setup_2{1} = F_to_int_point(aspoint_G1 vk_gate_setup_2{2}) /\
      vk_gate_setup_3{1} = F_to_int_point(aspoint_G1 vk_gate_setup_3{2}) /\
      vk_gate_setup_4{1} = F_to_int_point(aspoint_G1 vk_gate_setup_4{2}) /\
      vk_gate_setup_5{1} = F_to_int_point(aspoint_G1 vk_gate_setup_5{2}) /\
      vk_gate_setup_6{1} = F_to_int_point(aspoint_G1 vk_gate_setup_6{2}) /\
      vk_gate_setup_7{1} = F_to_int_point(aspoint_G1 vk_gate_setup_7{2}) /\
      poly3_omega{1} = FieldR.asint poly3_omega{2} /\
      v{1} = FieldR.asint v{2} /\
      z{1} = FieldR.asint z{2} /\
      gate_selector_0_opening{1} = FieldR.asint gate_selector_0_opening{2} /\
      alpha{1} = FieldR.asint alpha{2} /\
      alpha2{1} = FieldR.asint alpha2{2} /\
      alpha3{1} = FieldR.asint alpha3{2} /\
      alpha4{1} = FieldR.asint alpha4{2} /\
      alpha5{1} = FieldR.asint alpha5{2} /\
      alpha6{1} = FieldR.asint alpha6{2} /\
      alpha7{1} = FieldR.asint alpha7{2} /\
      alpha8{1} = FieldR.asint alpha8{2} /\
      state_beta{1} = FieldR.asint state_beta{2} /\
      gamma{1} = FieldR.asint gamma{2} /\
      vk_gate_selector_1{1} = F_to_int_point(aspoint_G1 vk_gate_selector_1{2}) /\
      vk_permutation_3{1} = F_to_int_point(aspoint_G1 vk_permutation_3{2}) /\
      gp_omega{1} = FieldR.asint gp_omega{2} /\
      l0AtZ{1} = FieldR.asint l0AtZ{2} /\
      poly0_opening{1} = FieldR.asint poly0_opening{2} /\
      poly1_opening{1} = FieldR.asint poly1_opening{2} /\
      poly2_opening{1} = FieldR.asint poly2_opening{2} /\
      proofLookupGrandProductOpeningAtZOmega{1} = FieldR.asint proofLookupGrandProductOpeningAtZOmega{2} /\
      zMinusLastOmega{1} = FieldR.asint zMinusLastOmega{2} /\
      proofLookupTPolyOpeningAtZOmega{1} = FieldR.asint proofLookupTPolyOpeningAtZOmega{2} /\
      betaLookup{1} = FieldR.asint betaLookup{2} /\
      proofLookupTPolyOpeningAtZ{1} = FieldR.asint proofLookupTPolyOpeningAtZ{2} /\
      betaGammaPlusGamma{1} = FieldR.asint betaGammaPlusGamma{2} /\
      proofLookupTableTypePolyOpeningAtZ{1} = FieldR.asint proofLookupTableTypePolyOpeningAtZ{2} /\
      proofLookupSelectorPolyOpeningAtZ{1} = FieldR.asint proofLookupSelectorPolyOpeningAtZ{2} /\
      gammaLookup{1} = FieldR.asint gammaLookup{2} /\
      betaPlusOne{1} = FieldR.asint betaPlusOne{2} /\
      lNMinusOneAtZ{1} = FieldR.asint lNMinusOneAtZ{2} ==>
      res{1} = Some(
        F_to_int_point(aspoint_G1 res{2}.`1),
        F_to_int_point(aspoint_G1 res{2}.`2),
        FieldR.asint res{2}.`3,
        FieldR.asint res{2}.`4,
        FieldR.asint res{2}.`5,
        F_to_int_point(aspoint_G1 res{2}.`6)
      )
    ].
    transitivity PrepareQueries.high_encapsulated
    (
      zInDomainSize{1} = FieldR.asint zInDomainSize{2} /\
      quotient_poly_part_0{1} = F_to_int_point(aspoint_G1 quotient_poly_part_0{2}) /\
      quotient_poly_part_1{1} = F_to_int_point(aspoint_G1 quotient_poly_part_1{2}) /\
      quotient_poly_part_2{1} = F_to_int_point(aspoint_G1 quotient_poly_part_2{2}) /\
      quotient_poly_part_3{1} = F_to_int_point(aspoint_G1 quotient_poly_part_3{2}) /\
      stateOpening0AtZ{1} = FieldR.asint stateOpening0AtZ{2} /\
      stateOpening1AtZ{1} = FieldR.asint stateOpening1AtZ{2} /\
      stateOpening2AtZ{1} = FieldR.asint stateOpening2AtZ{2} /\
      stateOpening3AtZ{1} = FieldR.asint stateOpening3AtZ{2} /\
      vk_lookup_table_0{1} = F_to_int_point(aspoint_G1 vk_lookup_table_0{2}) /\
      vk_lookup_table_1{1} = F_to_int_point(aspoint_G1 vk_lookup_table_1{2}) /\
      vk_lookup_table_2{1} = F_to_int_point(aspoint_G1 vk_lookup_table_2{2}) /\
      vk_lookup_table_3{1} = F_to_int_point(aspoint_G1 vk_lookup_table_3{2}) /\
      state_eta{1} = FieldR.asint state_eta{2} /\
      vk_gate_setup_0{1} = F_to_int_point(aspoint_G1 vk_gate_setup_0{2}) /\
      vk_gate_setup_1{1} = F_to_int_point(aspoint_G1 vk_gate_setup_1{2}) /\
      vk_gate_setup_2{1} = F_to_int_point(aspoint_G1 vk_gate_setup_2{2}) /\
      vk_gate_setup_3{1} = F_to_int_point(aspoint_G1 vk_gate_setup_3{2}) /\
      vk_gate_setup_4{1} = F_to_int_point(aspoint_G1 vk_gate_setup_4{2}) /\
      vk_gate_setup_5{1} = F_to_int_point(aspoint_G1 vk_gate_setup_5{2}) /\
      vk_gate_setup_6{1} = F_to_int_point(aspoint_G1 vk_gate_setup_6{2}) /\
      vk_gate_setup_7{1} = F_to_int_point(aspoint_G1 vk_gate_setup_7{2}) /\
      poly3_omega{1} = FieldR.asint poly3_omega{2} /\
      v{1} = FieldR.asint v{2} /\
      z{1} = FieldR.asint z{2} /\
      gate_selector_0_opening{1} = FieldR.asint gate_selector_0_opening{2} /\
      alpha{1} = FieldR.asint alpha{2} /\
      alpha2{1} = FieldR.asint alpha2{2} /\
      alpha3{1} = FieldR.asint alpha3{2} /\
      alpha4{1} = FieldR.asint alpha4{2} /\
      alpha5{1} = FieldR.asint alpha5{2} /\
      alpha6{1} = FieldR.asint alpha6{2} /\
      alpha7{1} = FieldR.asint alpha7{2} /\
      alpha8{1} = FieldR.asint alpha8{2} /\
      state_beta{1} = FieldR.asint state_beta{2} /\
      gamma{1} = FieldR.asint gamma{2} /\
      vk_gate_selector_1{1} = F_to_int_point(aspoint_G1 vk_gate_selector_1{2}) /\
      vk_permutation_3{1} = F_to_int_point(aspoint_G1 vk_permutation_3{2}) /\
      gp_omega{1} = FieldR.asint gp_omega{2} /\
      l0AtZ{1} = FieldR.asint l0AtZ{2} /\
      poly0_opening{1} = FieldR.asint poly0_opening{2} /\
      poly1_opening{1} = FieldR.asint poly1_opening{2} /\
      poly2_opening{1} = FieldR.asint poly2_opening{2} /\
      proofLookupGrandProductOpeningAtZOmega{1} = FieldR.asint proofLookupGrandProductOpeningAtZOmega{2} /\
      zMinusLastOmega{1} = FieldR.asint zMinusLastOmega{2} /\
      proofLookupTPolyOpeningAtZOmega{1} = FieldR.asint proofLookupTPolyOpeningAtZOmega{2} /\
      betaLookup{1} = FieldR.asint betaLookup{2} /\
      proofLookupTPolyOpeningAtZ{1} = FieldR.asint proofLookupTPolyOpeningAtZ{2} /\
      betaGammaPlusGamma{1} = FieldR.asint betaGammaPlusGamma{2} /\
      proofLookupTableTypePolyOpeningAtZ{1} = FieldR.asint proofLookupTableTypePolyOpeningAtZ{2} /\
      proofLookupSelectorPolyOpeningAtZ{1} = FieldR.asint proofLookupSelectorPolyOpeningAtZ{2} /\
      gammaLookup{1} = FieldR.asint gammaLookup{2} /\
      betaPlusOne{1} = FieldR.asint betaPlusOne{2} /\
      lNMinusOneAtZ{1} = FieldR.asint lNMinusOneAtZ{2} ==>
      res{1} = Some(
        F_to_int_point(aspoint_G1 res{2}.`1),
        F_to_int_point(aspoint_G1 res{2}.`2),
        FieldR.asint res{2}.`3,
        FieldR.asint res{2}.`4,
        FieldR.asint res{2}.`5,
        F_to_int_point(aspoint_G1 res{2}.`6)
      )
    )
    (
      ={arg} ==> ={res}
    ).
    progress. exists arg{2}. by progress.
    by progress.
    exact prepareQueries_mid_equiv_high_encapsulated.
    proc.
      inline*. wp. skip. progress.
      smt (@G).
      smt (@G).
qed.


