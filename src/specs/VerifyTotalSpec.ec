pragma Goals:printall.

require import AllCore.
require import Int.
require import IntDiv.
require import AddAssignLookupLinearisationContributionWithV.
require import EvaluateLagrangePolyOutOfDomain.
require import InitializeTranscript.
require import Field.
require import FinalPairing.
require import Keccak.
require import LoadProof.
require import LoadVerificationKey.
require import PointAddIntoDest.
require import PointMulIntoDest.
require import PointMulAndAddIntoDest.
require import PrepareAggregatedCommitment.
require import PrepareQueries.
require import UInt256.
require import UpdateAggregationChallenge.
require import UpdateAggregationChallenge105.
require import Utils.
require import Verifier.
require import VerifyQuotientEvaluation.
require import YulPrimops.
require import PurePrimops.
require import Utils.
require import VerifierConsts.
require import Verify.
require import VerifyLowToMid.
require import VerifyMidCanonicalisation.
require import VerifyMidToHighEncapsulated.
require import VerifyHighEncapsulatedToHigh.

import MemoryMap PurePrimops.

pred inputs_castable_to_curve (
  state_poly_0_i
  state_poly_1_i
  state_poly_2_i
  state_poly_3_i
  copy_permutation_grand_product_i
  lookup_s_poly_i
  lookup_grand_product_i
  quotient_poly_part_0_i
  quotient_poly_part_1_i
  quotient_poly_part_2_i
  quotient_poly_part_3_i
  opening_proof_at_z_i
  opening_proof_at_z_omega_i: (int*int)
) = 
  exists (
    state_poly_0_g: g,
    state_poly_1_g: g,
    state_poly_2_g: g,
    state_poly_3_g: g,
    copy_permutation_grand_product_g: g,
    lookup_s_poly_g: g,
    lookup_grand_product_g: g,
    quotient_poly_part_0_g: g,
    quotient_poly_part_1_g: g,
    quotient_poly_part_2_g: g,
    quotient_poly_part_3_g: g,
    opening_proof_at_z_g: g,
    opening_proof_at_z_omega_g: g
  ), (
    (FieldQ.inF state_poly_0_i.`1, FieldQ.inF state_poly_0_i.`2) = aspoint_G1 state_poly_0_g /\
    (FieldQ.inF state_poly_1_i.`1, FieldQ.inF state_poly_1_i.`2) = aspoint_G1 state_poly_1_g /\
    (FieldQ.inF state_poly_2_i.`1, FieldQ.inF state_poly_2_i.`2) = aspoint_G1 state_poly_2_g /\
    (FieldQ.inF state_poly_3_i.`1, FieldQ.inF state_poly_3_i.`2) = aspoint_G1 state_poly_3_g /\
    (FieldQ.inF copy_permutation_grand_product_i.`1, FieldQ.inF copy_permutation_grand_product_i.`2) = aspoint_G1 copy_permutation_grand_product_g /\
    (FieldQ.inF lookup_s_poly_i.`1, FieldQ.inF lookup_s_poly_i.`2) = aspoint_G1 lookup_s_poly_g /\
    (FieldQ.inF lookup_grand_product_i.`1, FieldQ.inF lookup_grand_product_i.`2) = aspoint_G1 lookup_grand_product_g /\
    (FieldQ.inF quotient_poly_part_0_i.`1, FieldQ.inF quotient_poly_part_0_i.`2) = aspoint_G1 quotient_poly_part_0_g /\
    (FieldQ.inF quotient_poly_part_1_i.`1, FieldQ.inF quotient_poly_part_1_i.`2) = aspoint_G1 quotient_poly_part_1_g /\
    (FieldQ.inF quotient_poly_part_2_i.`1, FieldQ.inF quotient_poly_part_2_i.`2) = aspoint_G1 quotient_poly_part_2_g /\
    (FieldQ.inF quotient_poly_part_3_i.`1, FieldQ.inF quotient_poly_part_3_i.`2) = aspoint_G1 quotient_poly_part_3_g /\
    (FieldQ.inF opening_proof_at_z_i.`1, FieldQ.inF opening_proof_at_z_i.`2) = aspoint_G1 opening_proof_at_z_g /\
    (FieldQ.inF opening_proof_at_z_omega_i.`1, FieldQ.inF opening_proof_at_z_omega_i.`2) = aspoint_G1 opening_proof_at_z_omega_g
).

pred calldata_castable_to_curve =
  inputs_castable_to_curve
    (point_to_uint PurePrimops.load_calldata_state_poly_0)
    (point_to_uint PurePrimops.load_calldata_state_poly_1)
    (point_to_uint PurePrimops.load_calldata_state_poly_2)
    (point_to_uint PurePrimops.load_calldata_state_poly_3)
    (point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product)
    (point_to_uint PurePrimops.load_calldata_lookup_s_poly)
    (point_to_uint PurePrimops.load_calldata_lookup_grand_product)
    (point_to_uint PurePrimops.load_calldata_quotient_poly_part_0)
    (point_to_uint PurePrimops.load_calldata_quotient_poly_part_1)
    (point_to_uint PurePrimops.load_calldata_quotient_poly_part_2)
    (point_to_uint PurePrimops.load_calldata_quotient_poly_part_3)
    (point_to_uint PurePrimops.load_calldata_opening_proof_at_z)
    (point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega).

pred point_i_matches (p: g) (p_i: (int*int)) = aspoint_G1 p = (FieldQ.inF p_i.`1, FieldQ.inF p_i.`2).
pred point_matches (p: g) (p_256: (uint256*uint256)) = point_i_matches p (point_to_uint p_256).



lemma verify_total_spec (inputs_on_curve: bool):
    equiv [
      Verifier_1261.fun_verify ~ Verify.high:
      public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
      public_input{2} = FieldR.inF (W256.to_uint (PurePrimops.load_calldata_public_input `&` (W256.masklsb 253))) /\
      proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
      a_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z) /\
      b_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z) /\
      c_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z) /\
      d_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z) /\
      d_at_z_omega{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega) /\
      main_gate_selector_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z) /\
      sigma_0_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z) /\
      sigma_1_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z) /\
      sigma_2_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z) /\
      z_perm_at_z_omega{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega) /\
      s_at_z_omega{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega) /\
      z_lookup_at_z_omega{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega) /\
      t_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z) /\
      t_at_z_omega{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega) /\
      lookup_selector_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z) /\
      table_type_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z) /\
      quotient_poly_opening_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z) /\
      r_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z) /\
      recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
      ((inputs_on_curve /\
        point_matches a{2} PurePrimops.load_calldata_state_poly_0 /\
        point_matches b{2} PurePrimops.load_calldata_state_poly_1 /\
        point_matches c{2} PurePrimops.load_calldata_state_poly_2 /\
        point_matches d{2} PurePrimops.load_calldata_state_poly_3 /\
        point_matches z_perm{2} PurePrimops.load_calldata_copy_permutation_grand_product /\
        point_matches s{2} PurePrimops.load_calldata_lookup_s_poly /\
        point_matches z_lookup{2} PurePrimops.load_calldata_lookup_grand_product /\
        point_matches t_0{2} PurePrimops.load_calldata_quotient_poly_part_0 /\
        point_matches t_1{2} PurePrimops.load_calldata_quotient_poly_part_1 /\
        point_matches t_2{2} PurePrimops.load_calldata_quotient_poly_part_2 /\
        point_matches t_3{2} PurePrimops.load_calldata_quotient_poly_part_3 /\
        point_matches w{2} PurePrimops.load_calldata_opening_proof_at_z /\
        point_matches w'{2} PurePrimops.load_calldata_opening_proof_at_z_omega
      ) \/ (
        !inputs_on_curve /\ !calldata_castable_to_curve
      )) /\
      !Primops.reverted{1} /\
      load Primops.memory{1} TRANSCRIPT_STATE_0_SLOT = W256.zero /\
      load Primops.memory{1} TRANSCRIPT_STATE_1_SLOT = W256.zero
        ==>
      (
        inputs_on_curve /\
        (
          (Primops.reverted{1} /\ !res{2}) \/
          (!Primops.reverted{1} /\ res{2})
        )
      ) \/ (
        !inputs_on_curve /\
        Primops.reverted{1}
      )
    ].
    proof.
      (* ===== EXTRACTED ===== *)
      transitivity Verify.low
      (
        ={arg, glob Verify} ==>
        ={res, glob Verify}
      )
      (
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = FieldR.inF (W256.to_uint (PurePrimops.load_calldata_public_input `&` (W256.masklsb 253))) /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        a_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z) /\
        b_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z) /\
        c_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z) /\
        d_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z) /\
        d_at_z_omega{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega) /\
        main_gate_selector_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z) /\
        sigma_0_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z) /\
        sigma_1_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z) /\
        sigma_2_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z) /\
        z_perm_at_z_omega{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega) /\
        s_at_z_omega{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega) /\
        z_lookup_at_z_omega{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega) /\
        t_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z) /\
        t_at_z_omega{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega) /\
        lookup_selector_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z) /\
        table_type_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z) /\
        quotient_poly_opening_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z) /\
        r_at_z{2} = FieldR.inF (W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z) /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        ((inputs_on_curve /\
          point_matches a{2} PurePrimops.load_calldata_state_poly_0 /\
          point_matches b{2} PurePrimops.load_calldata_state_poly_1 /\
          point_matches c{2} PurePrimops.load_calldata_state_poly_2 /\
          point_matches d{2} PurePrimops.load_calldata_state_poly_3 /\
          point_matches z_perm{2} PurePrimops.load_calldata_copy_permutation_grand_product /\
          point_matches s{2} PurePrimops.load_calldata_lookup_s_poly /\
          point_matches z_lookup{2} PurePrimops.load_calldata_lookup_grand_product /\
          point_matches t_0{2} PurePrimops.load_calldata_quotient_poly_part_0 /\
          point_matches t_1{2} PurePrimops.load_calldata_quotient_poly_part_1 /\
          point_matches t_2{2} PurePrimops.load_calldata_quotient_poly_part_2 /\
          point_matches t_3{2} PurePrimops.load_calldata_quotient_poly_part_3 /\
          point_matches w{2} PurePrimops.load_calldata_opening_proof_at_z /\
          point_matches w'{2} PurePrimops.load_calldata_opening_proof_at_z_omega
        ) \/ (
          !inputs_on_curve /\ !calldata_castable_to_curve
        )) /\
        !Primops.reverted{1} /\
        load Primops.memory{1} TRANSCRIPT_STATE_0_SLOT = W256.zero /\
        load Primops.memory{1} TRANSCRIPT_STATE_1_SLOT = W256.zero
          ==>
        (
          inputs_on_curve /\
          (
            (Primops.reverted{1} /\ !res{2}) \/
            (!Primops.reverted{1} /\ res{2})
          )
        ) \/ (
          !inputs_on_curve /\
          Primops.reverted{1}
        )    
      ).
        progress.
          exists Primops.memory{1}.
          exists Primops.ret_data{1}.
          exists Primops.reverted{1}.
          exists arg{1}.
          by progress.
  
        by progress.
        exact verify_extracted_equiv_low.
  
      (* ===== LOW ===== *)
      transitivity Verify.mid
      (
        !Primops.reverted{1} /\
        (* load proof from calldata *)
        public_input_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_public_input_length /\
        public_input{2} = W256.to_uint PurePrimops.load_calldata_public_input /\
        proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_proof_length /\
        state_poly_0{2} = point_to_uint PurePrimops.load_calldata_state_poly_0 /\
        state_poly_1{2} = point_to_uint PurePrimops.load_calldata_state_poly_1 /\
        state_poly_2{2} = point_to_uint PurePrimops.load_calldata_state_poly_2 /\
        state_poly_3{2} = point_to_uint PurePrimops.load_calldata_state_poly_3 /\
        copy_permutation_grand_product{2} = point_to_uint PurePrimops.load_calldata_copy_permutation_grand_product /\
        lookup_s_poly{2} = point_to_uint PurePrimops.load_calldata_lookup_s_poly /\
        lookup_grand_product{2} = point_to_uint PurePrimops.load_calldata_lookup_grand_product /\
        quotient_poly_part_0{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_0 /\
        quotient_poly_part_1{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_1 /\
        quotient_poly_part_2{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_2 /\
        quotient_poly_part_3{2} = point_to_uint PurePrimops.load_calldata_quotient_poly_part_3 /\
        state_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_0_opening_at_z /\
        state_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_1_opening_at_z /\
        state_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_2_opening_at_z /\
        state_poly_3_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z /\
        state_poly_3_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_state_poly_3_opening_at_z_omega /\
        gate_selector_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_gate_selector_0_opening_at_z /\
        copy_permutation_poly_0_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_0_opening_at_z /\
        copy_permutation_poly_1_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_1_opening_at_z /\
        copy_permutation_poly_2_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_poly_2_opening_at_z /\
        copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
        lookup_s_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_s_poly_opening_at_z_omega /\
        lookup_grand_product_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_grand_product_opening_at_z_omega /\
        lookup_t_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z /\
        lookup_t_poly_opening_at_z_omega{2} = W256.to_uint PurePrimops.load_calldata_lookup_t_poly_opening_at_z_omega /\
        lookup_selector_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_selector_poly_opening_at_z /\
        lookup_table_type_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_lookup_table_type_poly_opening_at_z /\
        quotient_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_quotient_poly_opening_at_z /\
        linearisation_poly_opening_at_z{2} = W256.to_uint PurePrimops.load_calldata_linearisation_poly_opening_at_z /\
        opening_proof_at_z{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z /\
        opening_proof_at_z_omega{2} = point_to_uint PurePrimops.load_calldata_opening_proof_at_z_omega /\
        recursive_proof_length_in_words{2} = W256.to_uint PurePrimops.load_calldata_recursive_proof_length /\
        recursive_part_p1{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p1 /\
        recursive_part_p2{2} = point_to_uint PurePrimops.load_calldata_recursive_part_p2 /\
        (* Assumption that EVM memory starts zeroed *)
        mload Primops.memory{1} TRANSCRIPT_STATE_0_SLOT = W256.zero /\
        mload Primops.memory{1} TRANSCRIPT_STATE_1_SLOT = W256.zero
          ==>
        (!Primops.reverted{1} /\ res{2} = true) \/
        (Primops.reverted{1} /\ res{2} = false)
      )
      (
        public_input_length_in_words{2} = public_input_length_in_words{1} /\
        public_input{2} = FieldR.inF (public_input{1} %% (2^253)) /\
        proof_length_in_words{2} = proof_length_in_words{1} /\
        a_at_z{2} = FieldR.inF state_poly_0_opening_at_z{1} /\
        b_at_z{2} = FieldR.inF state_poly_1_opening_at_z{1} /\
        c_at_z{2} = FieldR.inF state_poly_2_opening_at_z{1} /\
        d_at_z{2} = FieldR.inF state_poly_3_opening_at_z{1} /\
        d_at_z_omega{2} = FieldR.inF state_poly_3_opening_at_z_omega{1} /\
        main_gate_selector_at_z{2} = FieldR.inF gate_selector_0_opening_at_z{1} /\
        sigma_0_at_z{2} = FieldR.inF copy_permutation_poly_0_opening_at_z{1} /\
        sigma_1_at_z{2} = FieldR.inF copy_permutation_poly_1_opening_at_z{1} /\
        sigma_2_at_z{2} = FieldR.inF copy_permutation_poly_2_opening_at_z{1} /\
        z_perm_at_z_omega{2} = FieldR.inF copy_permutation_grand_product_opening_at_z_omega{1} /\
        s_at_z_omega{2} = FieldR.inF lookup_s_poly_opening_at_z_omega{1} /\
        z_lookup_at_z_omega{2} = FieldR.inF lookup_grand_product_opening_at_z_omega{1} /\
        t_at_z{2} = FieldR.inF lookup_t_poly_opening_at_z{1} /\
        t_at_z_omega{2} = FieldR.inF lookup_t_poly_opening_at_z_omega{1} /\
        lookup_selector_at_z{2} = FieldR.inF lookup_selector_poly_opening_at_z{1} /\
        table_type_at_z{2} = FieldR.inF lookup_table_type_poly_opening_at_z{1} /\
        quotient_poly_opening_at_z{2} = FieldR.inF quotient_poly_opening_at_z{1} /\
        r_at_z{2} = FieldR.inF linearisation_poly_opening_at_z{1} /\
        recursive_proof_length_in_words{2} = recursive_proof_length_in_words{1} /\
        ((inputs_on_curve /\
          point_i_matches a{2} state_poly_0{1} /\
          point_i_matches b{2} state_poly_1{1} /\
          point_i_matches c{2} state_poly_2{1} /\
          point_i_matches d{2} state_poly_3{1} /\
          point_i_matches z_perm{2} copy_permutation_grand_product{1} /\
          point_i_matches s{2} lookup_s_poly{1} /\
          point_i_matches z_lookup{2} lookup_grand_product{1} /\
          point_i_matches t_0{2} quotient_poly_part_0{1} /\
          point_i_matches t_1{2} quotient_poly_part_1{1} /\
          point_i_matches t_2{2} quotient_poly_part_2{1} /\
          point_i_matches t_3{2} quotient_poly_part_3{1} /\
          point_i_matches w{2} opening_proof_at_z{1} /\
          point_i_matches w'{2} opening_proof_at_z_omega{1}
        ) \/ (
          !inputs_on_curve /\ !(
            inputs_castable_to_curve
              state_poly_0{1}
              state_poly_1{1}
              state_poly_2{1}
              state_poly_3{1}
              copy_permutation_grand_product{1}
              lookup_s_poly{1}
              lookup_grand_product{1}
              quotient_poly_part_0{1}
              quotient_poly_part_1{1}
              quotient_poly_part_2{1}
              quotient_poly_part_3{1}
              opening_proof_at_z{1}
              opening_proof_at_z_omega{1}
          )
        ))
          ==>
        (
          inputs_on_curve /\ ={res}
        ) \/ (
          !inputs_on_curve /\ !res{1}
        )
      ).
        progress.
          exists (
            W256.to_uint load_calldata_public_input_length,
            W256.to_uint load_calldata_public_input,
            W256.to_uint load_calldata_proof_length,
            point_to_uint load_calldata_state_poly_0,
            point_to_uint load_calldata_state_poly_1,
            point_to_uint load_calldata_state_poly_2,
            point_to_uint load_calldata_state_poly_3,
            point_to_uint load_calldata_copy_permutation_grand_product,
            point_to_uint load_calldata_lookup_s_poly,
            point_to_uint load_calldata_lookup_grand_product,
            point_to_uint load_calldata_quotient_poly_part_0,
            point_to_uint load_calldata_quotient_poly_part_1,
            point_to_uint load_calldata_quotient_poly_part_2,
            point_to_uint load_calldata_quotient_poly_part_3,
            W256.to_uint load_calldata_state_poly_0_opening_at_z,
            W256.to_uint load_calldata_state_poly_1_opening_at_z,
            W256.to_uint load_calldata_state_poly_2_opening_at_z,
            W256.to_uint load_calldata_state_poly_3_opening_at_z,
            W256.to_uint load_calldata_state_poly_3_opening_at_z_omega,
            W256.to_uint load_calldata_gate_selector_0_opening_at_z,
            W256.to_uint load_calldata_copy_permutation_poly_0_opening_at_z,
            W256.to_uint load_calldata_copy_permutation_poly_1_opening_at_z,
            W256.to_uint load_calldata_copy_permutation_poly_2_opening_at_z,
            W256.to_uint load_calldata_copy_permutation_grand_product_opening_at_z_omega,
            W256.to_uint load_calldata_lookup_s_poly_opening_at_z_omega,
            W256.to_uint load_calldata_lookup_grand_product_opening_at_z_omega,
            W256.to_uint load_calldata_lookup_t_poly_opening_at_z,
            W256.to_uint load_calldata_lookup_t_poly_opening_at_z_omega,
            W256.to_uint load_calldata_lookup_selector_poly_opening_at_z,
            W256.to_uint load_calldata_lookup_table_type_poly_opening_at_z,
            W256.to_uint load_calldata_quotient_poly_opening_at_z,
            W256.to_uint load_calldata_linearisation_poly_opening_at_z,
            point_to_uint load_calldata_opening_proof_at_z,
            point_to_uint load_calldata_opening_proof_at_z_omega,
            W256.to_uint load_calldata_recursive_proof_length,
            point_to_uint load_calldata_recursive_part_p1,
            point_to_uint load_calldata_recursive_part_p2
          ).
          simplify.
          split.
            rewrite H22 H23 H24. by progress.
          split. assumption.
          split.
            rewrite H0.
            have ->: load_calldata_public_input `&` (W256.masklsb 253) = (W256.splitMask (W256.masklsb 253) load_calldata_public_input).`1.
              rewrite /splitMask. simplify. by trivial.
            have ->: W256.to_uint (splitAt 253 load_calldata_public_input).`1 = to_uint load_calldata_public_input %% 2^253.
              have H_range : forall b, (0 <= 253 && 253 < 256 => b) => b by progress.
              have H_split := W256.splitAtP 253 load_calldata_public_input.
              apply (weaken_and_left _ (W256.to_uint
                (W256.splitMask (W256.masklsb 253) load_calldata_public_input).`2 =
                2 ^ 253 * (W256.to_uint load_calldata_public_input %/ 2 ^ 253))).
              apply H_range.
              exact H_split.
            reflexivity.
          by progress.

        progress.
          case H0.
            progress. rewrite H0. progress. case H. by progress. by progress.
            case H.
              by progress.
              progress. rewrite H0. by progress.

        exists* Primops.memory{1}. elim*=> memory.
        conseq (_ :
          !Primops.reverted{1} /\
          Primops.memory{1} = memory /\
          public_input_length_in_words{2} = W256.to_uint load_calldata_public_input_length /\
          public_input{2} = W256.to_uint load_calldata_public_input /\
          proof_length_in_words{2} = W256.to_uint load_calldata_proof_length /\
          state_poly_0{2} = point_to_uint load_calldata_state_poly_0 /\
          state_poly_1{2} = point_to_uint load_calldata_state_poly_1 /\
          state_poly_2{2} = point_to_uint load_calldata_state_poly_2 /\
          state_poly_3{2} = point_to_uint load_calldata_state_poly_3 /\
          copy_permutation_grand_product{2} = point_to_uint load_calldata_copy_permutation_grand_product /\
          lookup_s_poly{2} = point_to_uint load_calldata_lookup_s_poly /\
          lookup_grand_product{2} = point_to_uint load_calldata_lookup_grand_product /\
          quotient_poly_part_0{2} = point_to_uint load_calldata_quotient_poly_part_0 /\
          quotient_poly_part_1{2} = point_to_uint load_calldata_quotient_poly_part_1 /\
          quotient_poly_part_2{2} = point_to_uint load_calldata_quotient_poly_part_2 /\
          quotient_poly_part_3{2} = point_to_uint load_calldata_quotient_poly_part_3 /\
          state_poly_0_opening_at_z{2} = W256.to_uint load_calldata_state_poly_0_opening_at_z /\
          state_poly_1_opening_at_z{2} = W256.to_uint load_calldata_state_poly_1_opening_at_z /\
          state_poly_2_opening_at_z{2} = W256.to_uint load_calldata_state_poly_2_opening_at_z /\
          state_poly_3_opening_at_z{2} = W256.to_uint load_calldata_state_poly_3_opening_at_z /\
          state_poly_3_opening_at_z_omega{2} = W256.to_uint load_calldata_state_poly_3_opening_at_z_omega /\
          gate_selector_0_opening_at_z{2} = W256.to_uint load_calldata_gate_selector_0_opening_at_z /\
          copy_permutation_poly_0_opening_at_z{2} = W256.to_uint load_calldata_copy_permutation_poly_0_opening_at_z /\
          copy_permutation_poly_1_opening_at_z{2} = W256.to_uint load_calldata_copy_permutation_poly_1_opening_at_z /\
          copy_permutation_poly_2_opening_at_z{2} = W256.to_uint load_calldata_copy_permutation_poly_2_opening_at_z /\
          copy_permutation_grand_product_opening_at_z_omega{2} = W256.to_uint load_calldata_copy_permutation_grand_product_opening_at_z_omega /\
          lookup_s_poly_opening_at_z_omega{2} = W256.to_uint load_calldata_lookup_s_poly_opening_at_z_omega /\
          lookup_grand_product_opening_at_z_omega{2} = W256.to_uint load_calldata_lookup_grand_product_opening_at_z_omega /\
          lookup_t_poly_opening_at_z{2} = W256.to_uint load_calldata_lookup_t_poly_opening_at_z /\
          lookup_t_poly_opening_at_z_omega{2} = W256.to_uint load_calldata_lookup_t_poly_opening_at_z_omega /\
          lookup_selector_poly_opening_at_z{2} = W256.to_uint load_calldata_lookup_selector_poly_opening_at_z /\
          lookup_table_type_poly_opening_at_z{2} = W256.to_uint load_calldata_lookup_table_type_poly_opening_at_z /\
          quotient_poly_opening_at_z{2} = W256.to_uint load_calldata_quotient_poly_opening_at_z /\
          linearisation_poly_opening_at_z{2} = W256.to_uint load_calldata_linearisation_poly_opening_at_z /\
          opening_proof_at_z{2} = point_to_uint load_calldata_opening_proof_at_z /\
          opening_proof_at_z_omega{2} = point_to_uint load_calldata_opening_proof_at_z_omega /\
          recursive_proof_length_in_words{2} = W256.to_uint load_calldata_recursive_proof_length /\
          recursive_part_p1{2} = point_to_uint load_calldata_recursive_part_p1 /\
          recursive_part_p2{2} = point_to_uint load_calldata_recursive_part_p2 /\
          mload memory TRANSCRIPT_STATE_0_SLOT = W256.zero /\
          mload memory TRANSCRIPT_STATE_1_SLOT = W256.zero
            ==>
          _
        ).
        by progress.
        exact (verify_low_equiv_mid memory).

      (* ===== MID ===== *)
      case inputs_on_curve.
        progress.
        transitivity Verify.mid
        (
          ={public_input_length_in_words} /\
          public_input{2} = public_input{1} %% (2^253) /\
          ={proof_length_in_words} /\
          state_poly_0{2}.`1 = state_poly_0{1}.`1 %% FieldQ.p /\
          state_poly_0{2}.`2 = state_poly_0{1}.`2 %% FieldQ.p /\
          state_poly_1{2}.`1 = state_poly_1{1}.`1 %% FieldQ.p /\
          state_poly_1{2}.`2 = state_poly_1{1}.`2 %% FieldQ.p /\
          state_poly_2{2}.`1 = state_poly_2{1}.`1 %% FieldQ.p /\
          state_poly_2{2}.`2 = state_poly_2{1}.`2 %% FieldQ.p /\
          state_poly_3{2}.`1 = state_poly_3{1}.`1 %% FieldQ.p /\
          state_poly_3{2}.`2 = state_poly_3{1}.`2 %% FieldQ.p /\
          copy_permutation_grand_product{2}.`1 = copy_permutation_grand_product{1}.`1 %% FieldQ.p /\
          copy_permutation_grand_product{2}.`2 = copy_permutation_grand_product{1}.`2 %% FieldQ.p /\
          lookup_s_poly{2}.`1 = lookup_s_poly{1}.`1 %% FieldQ.p /\
          lookup_s_poly{2}.`2 = lookup_s_poly{1}.`2 %% FieldQ.p /\
          lookup_grand_product{2}.`1 = lookup_grand_product{1}.`1 %% FieldQ.p /\
          lookup_grand_product{2}.`2 = lookup_grand_product{1}.`2 %% FieldQ.p /\
          quotient_poly_part_0{2}.`1 = quotient_poly_part_0{1}.`1 %% FieldQ.p /\
          quotient_poly_part_0{2}.`2 = quotient_poly_part_0{1}.`2 %% FieldQ.p /\
          quotient_poly_part_1{2}.`1 = quotient_poly_part_1{1}.`1 %% FieldQ.p /\
          quotient_poly_part_1{2}.`2 = quotient_poly_part_1{1}.`2 %% FieldQ.p /\
          quotient_poly_part_2{2}.`1 = quotient_poly_part_2{1}.`1 %% FieldQ.p /\
          quotient_poly_part_2{2}.`2 = quotient_poly_part_2{1}.`2 %% FieldQ.p /\
          quotient_poly_part_3{2}.`1 = quotient_poly_part_3{1}.`1 %% FieldQ.p /\
          quotient_poly_part_3{2}.`2 = quotient_poly_part_3{1}.`2 %% FieldQ.p /\
          state_poly_0_opening_at_z{2} = state_poly_0_opening_at_z{1} %% FieldR.p /\
          state_poly_1_opening_at_z{2} = state_poly_1_opening_at_z{1} %% FieldR.p /\
          state_poly_2_opening_at_z{2} = state_poly_2_opening_at_z{1} %% FieldR.p /\
          state_poly_3_opening_at_z{2} = state_poly_3_opening_at_z{1} %% FieldR.p /\
          state_poly_3_opening_at_z_omega{2} = state_poly_3_opening_at_z_omega{1} %% FieldR.p /\
          gate_selector_0_opening_at_z{2} = gate_selector_0_opening_at_z{1} %% FieldR.p /\
          copy_permutation_poly_0_opening_at_z{2} = copy_permutation_poly_0_opening_at_z{1} %% FieldR.p /\
          copy_permutation_poly_1_opening_at_z{2} = copy_permutation_poly_1_opening_at_z{1} %% FieldR.p /\
          copy_permutation_poly_2_opening_at_z{2} = copy_permutation_poly_2_opening_at_z{1} %% FieldR.p /\
          copy_permutation_grand_product_opening_at_z_omega{2} = copy_permutation_grand_product_opening_at_z_omega{1} %% FieldR.p /\
          lookup_s_poly_opening_at_z_omega{2} = lookup_s_poly_opening_at_z_omega{1} %% FieldR.p /\
          lookup_grand_product_opening_at_z_omega{2} = lookup_grand_product_opening_at_z_omega{1} %% FieldR.p /\
          lookup_t_poly_opening_at_z{2} = lookup_t_poly_opening_at_z{1} %% FieldR.p /\
          lookup_t_poly_opening_at_z_omega{2} = lookup_t_poly_opening_at_z_omega{1} %% FieldR.p /\
          lookup_selector_poly_opening_at_z{2} = lookup_selector_poly_opening_at_z{1} %% FieldR.p /\
          lookup_table_type_poly_opening_at_z{2} = lookup_table_type_poly_opening_at_z{1} %% FieldR.p /\
          quotient_poly_opening_at_z{2} = quotient_poly_opening_at_z{1} %% FieldR.p /\
          linearisation_poly_opening_at_z{2} = linearisation_poly_opening_at_z{1} %% FieldR.p /\
          opening_proof_at_z{2}.`1 = opening_proof_at_z{1}.`1 %% FieldQ.p /\
          opening_proof_at_z{2}.`2 = opening_proof_at_z{1}.`2 %% FieldQ.p /\
          opening_proof_at_z_omega{2}.`1 = opening_proof_at_z_omega{1}.`1 %% FieldQ.p /\
          opening_proof_at_z_omega{2}.`2 = opening_proof_at_z_omega{1}.`2 %% FieldQ.p /\
          ={recursive_proof_length_in_words} /\
          recursive_part_p1{2}.`1 = recursive_part_p1{1}.`1 %% FieldQ.p /\
          recursive_part_p1{2}.`2 = recursive_part_p1{1}.`2 %% FieldQ.p /\
          recursive_part_p2{2}.`1 = recursive_part_p2{1}.`1 %% FieldQ.p /\
          recursive_part_p2{2}.`2 = recursive_part_p2{1}.`2 %% FieldQ.p ==> 
          ={res}
        )
        (
          ={public_input_length_in_words} /\
          public_input{1} = FieldR.asint public_input{2} /\ 0 <= public_input{1} < (2^253) /\
          ={proof_length_in_words} /\
          state_poly_0{1} = F_to_int_point(aspoint_G1 a{2}) /\
          state_poly_1{1} = F_to_int_point(aspoint_G1 b{2}) /\
          state_poly_2{1} = F_to_int_point(aspoint_G1 c{2}) /\
          state_poly_3{1} = F_to_int_point(aspoint_G1 d{2}) /\
          copy_permutation_grand_product{1} = F_to_int_point(aspoint_G1 z_perm{2}) /\
          lookup_s_poly{1} = F_to_int_point(aspoint_G1 s{2}) /\
          lookup_grand_product{1} = F_to_int_point(aspoint_G1 z_lookup{2}) /\
          quotient_poly_part_0{1} = F_to_int_point(aspoint_G1 t_0{2}) /\
          quotient_poly_part_1{1} = F_to_int_point(aspoint_G1 t_1{2}) /\
          quotient_poly_part_2{1} = F_to_int_point(aspoint_G1 t_2{2}) /\
          quotient_poly_part_3{1} = F_to_int_point(aspoint_G1 t_3{2}) /\
          state_poly_0_opening_at_z{1} = FieldR.asint a_at_z{2} /\
          state_poly_1_opening_at_z{1} = FieldR.asint b_at_z{2} /\
          state_poly_2_opening_at_z{1} = FieldR.asint c_at_z{2} /\
          state_poly_3_opening_at_z{1} = FieldR.asint d_at_z{2} /\
          state_poly_3_opening_at_z_omega{1} = FieldR.asint d_at_z_omega{2} /\
          gate_selector_0_opening_at_z{1} = FieldR.asint main_gate_selector_at_z{2} /\
          copy_permutation_poly_0_opening_at_z{1} = FieldR.asint sigma_0_at_z{2} /\
          copy_permutation_poly_1_opening_at_z{1} = FieldR.asint sigma_1_at_z{2} /\
          copy_permutation_poly_2_opening_at_z{1} = FieldR.asint sigma_2_at_z{2} /\
          copy_permutation_grand_product_opening_at_z_omega{1} = FieldR.asint z_perm_at_z_omega{2} /\
          lookup_s_poly_opening_at_z_omega{1} = FieldR.asint s_at_z_omega{2} /\
          lookup_grand_product_opening_at_z_omega{1} = FieldR.asint z_lookup_at_z_omega{2} /\
          lookup_t_poly_opening_at_z{1} = FieldR.asint t_at_z{2} /\
          lookup_t_poly_opening_at_z_omega{1} = FieldR.asint t_at_z_omega{2} /\
          lookup_selector_poly_opening_at_z{1} = FieldR.asint lookup_selector_at_z{2} /\
          lookup_table_type_poly_opening_at_z{1} = FieldR.asint table_type_at_z{2} /\
          quotient_poly_opening_at_z{1} = FieldR.asint quotient_poly_opening_at_z{2} /\
          linearisation_poly_opening_at_z{1} = FieldR.asint r_at_z{2} /\
          opening_proof_at_z{1} = F_to_int_point(aspoint_G1 w{2}) /\
          opening_proof_at_z_omega{1} = F_to_int_point(aspoint_G1 w'{2}) /\
          ={recursive_proof_length_in_words}
          (* only necessary if we generalise over vk_recursive_flag /\
          recursive_part_p1{1} = F_to_int_point(aspoint_G1 recursive_part_p1{2} /\
          recursive_part_p2{1} = F_to_int_point(aspoint_G1 recursive_part_p2{2}) *) ==> 
          ={res}
        ).
          progress.
          exists (
            public_input_length_in_words{1},
            public_input{1} %% (2^253),
            proof_length_in_words{1},
            (state_poly_0{1}.`1 %% FieldQ.p, state_poly_0{1}.`2 %% FieldQ.p),
            (state_poly_1{1}.`1 %% FieldQ.p, state_poly_1{1}.`2 %% FieldQ.p),
            (state_poly_2{1}.`1 %% FieldQ.p, state_poly_2{1}.`2 %% FieldQ.p),
            (state_poly_3{1}.`1 %% FieldQ.p, state_poly_3{1}.`2 %% FieldQ.p),
            (copy_permutation_grand_product{1}.`1 %% FieldQ.p, copy_permutation_grand_product{1}.`2 %% FieldQ.p),
            (lookup_s_poly{1}.`1 %% FieldQ.p, lookup_s_poly{1}.`2 %% FieldQ.p),
            (lookup_grand_product{1}.`1 %% FieldQ.p, lookup_grand_product{1}.`2 %% FieldQ.p),
            (quotient_poly_part_0{1}.`1 %% FieldQ.p, quotient_poly_part_0{1}.`2 %% FieldQ.p),
            (quotient_poly_part_1{1}.`1 %% FieldQ.p, quotient_poly_part_1{1}.`2 %% FieldQ.p),
            (quotient_poly_part_2{1}.`1 %% FieldQ.p, quotient_poly_part_2{1}.`2 %% FieldQ.p),
            (quotient_poly_part_3{1}.`1 %% FieldQ.p, quotient_poly_part_3{1}.`2 %% FieldQ.p),
            state_poly_0_opening_at_z{1} %% FieldR.p,
            state_poly_1_opening_at_z{1} %% FieldR.p,
            state_poly_2_opening_at_z{1} %% FieldR.p,
            state_poly_3_opening_at_z{1} %% FieldR.p,
            state_poly_3_opening_at_z_omega{1} %% FieldR.p,
            gate_selector_0_opening_at_z{1} %% FieldR.p,
            copy_permutation_poly_0_opening_at_z{1} %% FieldR.p,
            copy_permutation_poly_1_opening_at_z{1} %% FieldR.p,
            copy_permutation_poly_2_opening_at_z{1} %% FieldR.p,
            copy_permutation_grand_product_opening_at_z_omega{1} %% FieldR.p,
            lookup_s_poly_opening_at_z_omega{1} %% FieldR.p,
            lookup_grand_product_opening_at_z_omega{1} %% FieldR.p,
            lookup_t_poly_opening_at_z{1} %% FieldR.p,
            lookup_t_poly_opening_at_z_omega{1} %% FieldR.p,
            lookup_selector_poly_opening_at_z{1} %% FieldR.p,
            lookup_table_type_poly_opening_at_z{1} %% FieldR.p,
            quotient_poly_opening_at_z{1} %% FieldR.p,
            linearisation_poly_opening_at_z{1} %% FieldR.p,
            (opening_proof_at_z{1}.`1 %% FieldQ.p, opening_proof_at_z{1}.`2 %% FieldQ.p),
            (opening_proof_at_z_omega{1}.`1 %% FieldQ.p, opening_proof_at_z_omega{1}.`2 %% FieldQ.p),
            recursive_proof_length_in_words{1},
            (recursive_part_p1{1}.`1 %% FieldQ.p, recursive_part_p1{1}.`2 %% FieldQ.p),
            (recursive_part_p2{1}.`1 %% FieldQ.p, recursive_part_p2{1}.`2 %% FieldQ.p)
          ).
          simplify.
          progress.
          rewrite H0. reflexivity.
          rewrite H1. rewrite FieldR.inFK. rewrite -Constants.r_eq_fieldr_p.
            rewrite (pmod_small _ Constants.R). rewrite /Constants.R. progress.
              exact modz_ge0.
              apply (int_lt_lt_trans _ (2^253)). exact ltz_pmod. by trivial. reflexivity.
          exact modz_ge0.
          exact ltz_pmod.
          rewrite H2. reflexivity.
          rewrite /point_i_matches in H22. rewrite H22. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H23. rewrite H23. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H24. rewrite H24. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H25. rewrite H25. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H26. rewrite H26. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H27. rewrite H27. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H28. rewrite H28. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H29. rewrite H29. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H30. rewrite H30. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H31. rewrite H31. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H32. rewrite H32. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite H3. rewrite FieldR.inFK. reflexivity.
          rewrite H4. rewrite FieldR.inFK. reflexivity.
          rewrite H5. rewrite FieldR.inFK. reflexivity.
          rewrite H6. rewrite FieldR.inFK. reflexivity.
          rewrite H7. rewrite FieldR.inFK. reflexivity.
          rewrite H8. rewrite FieldR.inFK. reflexivity.
          rewrite H9. rewrite FieldR.inFK. reflexivity.
          rewrite H10. rewrite FieldR.inFK. reflexivity.
          rewrite H11. rewrite FieldR.inFK. reflexivity.
          rewrite H12. rewrite FieldR.inFK. reflexivity.
          rewrite H13. rewrite FieldR.inFK. reflexivity.
          rewrite H14. rewrite FieldR.inFK. reflexivity.
          rewrite H15. rewrite FieldR.inFK. reflexivity.
          rewrite H16. rewrite FieldR.inFK. reflexivity.
          rewrite H17. rewrite FieldR.inFK. reflexivity.
          rewrite H18. rewrite FieldR.inFK. reflexivity.
          rewrite H19. rewrite FieldR.inFK. reflexivity.
          rewrite H20. rewrite FieldR.inFK. reflexivity.
          rewrite /point_i_matches in H33. rewrite H33. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.
          rewrite /point_i_matches in H34. rewrite H34. rewrite /F_to_int_point. simplify.
            rewrite FieldQ.inFK. rewrite FieldQ.inFK. by progress.          
          rewrite H21. reflexivity.
          
          by progress.
          exact verify_mid_canonicalisation.

        (* ===== MID CANONICAL ===== *)
        transitivity Verify.high_encapsulated
        (
          ={public_input_length_in_words} /\
          public_input{1} = FieldR.asint public_input{2} /\ 0 <= public_input{1} < (2^253) /\
          ={proof_length_in_words} /\
          state_poly_0{1} = F_to_int_point(aspoint_G1 state_poly_0{2}) /\
          state_poly_1{1} = F_to_int_point(aspoint_G1 state_poly_1{2}) /\
          state_poly_2{1} = F_to_int_point(aspoint_G1 state_poly_2{2}) /\
          state_poly_3{1} = F_to_int_point(aspoint_G1 state_poly_3{2}) /\
          copy_permutation_grand_product{1} = F_to_int_point(aspoint_G1 copy_permutation_grand_product{2}) /\
          lookup_s_poly{1} = F_to_int_point(aspoint_G1 lookup_s_poly{2}) /\
          lookup_grand_product{1} = F_to_int_point(aspoint_G1 lookup_grand_product{2}) /\
          quotient_poly_part_0{1} = F_to_int_point(aspoint_G1 quotient_poly_part_0{2}) /\
          quotient_poly_part_1{1} = F_to_int_point(aspoint_G1 quotient_poly_part_1{2}) /\
          quotient_poly_part_2{1} = F_to_int_point(aspoint_G1 quotient_poly_part_2{2}) /\
          quotient_poly_part_3{1} = F_to_int_point(aspoint_G1 quotient_poly_part_3{2}) /\
          state_poly_0_opening_at_z{1} = FieldR.asint state_poly_0_opening_at_z{2} /\
          state_poly_1_opening_at_z{1} = FieldR.asint state_poly_1_opening_at_z{2} /\
          state_poly_2_opening_at_z{1} = FieldR.asint state_poly_2_opening_at_z{2} /\
          state_poly_3_opening_at_z{1} = FieldR.asint state_poly_3_opening_at_z{2} /\
          state_poly_3_opening_at_z_omega{1} = FieldR.asint state_poly_3_opening_at_z_omega{2} /\
          gate_selector_0_opening_at_z{1} = FieldR.asint gate_selector_0_opening_at_z{2} /\
          copy_permutation_poly_0_opening_at_z{1} = FieldR.asint copy_permutation_poly_0_opening_at_z{2} /\
          copy_permutation_poly_1_opening_at_z{1} = FieldR.asint copy_permutation_poly_1_opening_at_z{2} /\
          copy_permutation_poly_2_opening_at_z{1} = FieldR.asint copy_permutation_poly_2_opening_at_z{2} /\
          copy_permutation_grand_product_opening_at_z_omega{1} = FieldR.asint copy_permutation_grand_product_opening_at_z_omega{2} /\
          lookup_s_poly_opening_at_z_omega{1} = FieldR.asint lookup_s_poly_opening_at_z_omega{2} /\
          lookup_grand_product_opening_at_z_omega{1} = FieldR.asint lookup_grand_product_opening_at_z_omega{2} /\
          lookup_t_poly_opening_at_z{1} = FieldR.asint lookup_t_poly_opening_at_z{2} /\
          lookup_t_poly_opening_at_z_omega{1} = FieldR.asint lookup_t_poly_opening_at_z_omega{2} /\
          lookup_selector_poly_opening_at_z{1} = FieldR.asint lookup_selector_poly_opening_at_z{2} /\
          lookup_table_type_poly_opening_at_z{1} = FieldR.asint lookup_table_type_poly_opening_at_z{2} /\
          quotient_poly_opening_at_z{1} = FieldR.asint quotient_poly_opening_at_z{2} /\
          linearisation_poly_opening_at_z{1} = FieldR.asint linearisation_poly_opening_at_z{2} /\
          opening_proof_at_z{1} = F_to_int_point(aspoint_G1 opening_proof_at_z{2}) /\
          opening_proof_at_z_omega{1} = F_to_int_point(aspoint_G1 opening_proof_at_z_omega{2}) /\
          ={recursive_proof_length_in_words}
            ==> 
          ={res}
        )
        (
          ={arg} ==> ={res}
        ).
        progress.
          exists arg{2}. by progress.
          by progress.
          exact verify_mid_equiv_high_encapsulated.

        (* ===== HIGH ENCAPSULATED ===== *)
        exact verify_high_encapsulated_equiv_high.
      
      (* ===== INPUTS NOT ON CURVE ===== *)
      progress.
      proc.
        simplify.
        kill{2} 1 ! 55. wp. skip. by progress.
        cfold{1} 1.
        cfold{1} 1.
        sp 1 0.
        do 41! (cfold{1} 1).
        seq 2 0: failed{1}.
          wp. inline LoadProof.mid.
          rcondf{1} 54. progress. wp. skip. by progress.
            sp 40 0.
            seq 13 0: (!isValid{1}).
              rewrite /inputs_castable_to_curve.
              case (on_curve_int state_poly_0{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H1. reflexivity.
              case (on_curve_int state_poly_1{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H2. reflexivity.
              case (on_curve_int state_poly_2{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H3. reflexivity.
              case (on_curve_int state_poly_3{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H4. reflexivity.
              case (on_curve_int copy_permutation_grand_product{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H5. reflexivity.
              case (on_curve_int lookup_s_poly{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H6. reflexivity.
              case (on_curve_int lookup_grand_product{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H7. reflexivity.
              case (on_curve_int quotient_poly_part_0{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H8. reflexivity.
              case (on_curve_int quotient_poly_part_1{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H9. reflexivity.
              case (on_curve_int quotient_poly_part_2{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H10. reflexivity.
              case (on_curve_int quotient_poly_part_3{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H11. reflexivity.
              case (on_curve_int opening_proof_at_z{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H12. reflexivity.
              case (on_curve_int opening_proof_at_z_omega{1}).
                seq 1 0: #pre. wp. skip. progress. rewrite H13. reflexivity.
              skip. progress.
              have H_on_curve_int : forall (p_i: int*int),
                on_curve_int (p_i.`1, p_i.`2) =>
                exists p, (FieldQ.inF p_i.`1, FieldQ.inF p_i.`2) = aspoint_G1 p.
                  rewrite /on_curve_int. progress.
                  have H_on_curve : on_curve (FieldQ.inF p_i.`1, FieldQ.inF p_i.`2).
                    rewrite /on_curve. simplify.
                    rewrite Constants.q_eq_fieldq_p in H14.
                    rewrite -FieldQ.inFM.
                    rewrite FieldQ.inF_mod.
                    rewrite -H14.
                    rewrite -FieldQ.inFD.
                    rewrite FieldQ.inFK.
                    pose x_mod := p_i.`1 %% FieldQ.p.
                    rewrite -FieldQ.inFM.
                    rewrite FieldQ.inFK.
                    pose x2_mod := (p_i.`1*p_i.`1) %% FieldQ.p.
                    rewrite -modzMml.
                    rewrite -/x_mod.
                    rewrite modzDml.
                    rewrite -FieldQ.inF_mod.
                    reflexivity.
                  have H_point : exists (p: g), aspoint_G1 p = (FieldQ.inF p_i.`1, FieldQ.inF p_i.`2).
                    exact (on_curve_as_point (FieldQ.inF p_i.`1) (FieldQ.inF p_i.`2)).
                  case H_point. progress.
                  exists p. rewrite H15. reflexivity.
              have H_contr: (exists (state_poly_0_g state_poly_1_g state_poly_2_g state_poly_3_g
                copy_permutation_grand_product_g lookup_s_poly_g
                lookup_grand_product_g quotient_poly_part_0_g quotient_poly_part_1_g
                quotient_poly_part_2_g quotient_poly_part_3_g opening_proof_at_z_g
                opening_proof_at_z_omega_g : g),
                ((FieldQ.inF state_poly_0{1}.`1), (FieldQ.inF state_poly_0{1}.`2)) =
                aspoint_G1 state_poly_0_g /\
                ((FieldQ.inF state_poly_1{1}.`1), (FieldQ.inF state_poly_1{1}.`2)) =
                aspoint_G1 state_poly_1_g /\
                ((FieldQ.inF state_poly_2{1}.`1), (FieldQ.inF state_poly_2{1}.`2)) =
                aspoint_G1 state_poly_2_g /\
                ((FieldQ.inF state_poly_3{1}.`1), (FieldQ.inF state_poly_3{1}.`2)) =
                aspoint_G1 state_poly_3_g /\
                ((FieldQ.inF copy_permutation_grand_product{1}.`1),
                 (FieldQ.inF copy_permutation_grand_product{1}.`2)) =
                aspoint_G1 copy_permutation_grand_product_g /\
                ((FieldQ.inF lookup_s_poly{1}.`1), (FieldQ.inF lookup_s_poly{1}.`2)) =
                aspoint_G1 lookup_s_poly_g /\
                ((FieldQ.inF lookup_grand_product{1}.`1),
                 (FieldQ.inF lookup_grand_product{1}.`2)) =
                aspoint_G1 lookup_grand_product_g /\
                ((FieldQ.inF quotient_poly_part_0{1}.`1),
                 (FieldQ.inF quotient_poly_part_0{1}.`2)) =
                aspoint_G1 quotient_poly_part_0_g /\
                ((FieldQ.inF quotient_poly_part_1{1}.`1),
                 (FieldQ.inF quotient_poly_part_1{1}.`2)) =
                aspoint_G1 quotient_poly_part_1_g /\
                ((FieldQ.inF quotient_poly_part_2{1}.`1),
                 (FieldQ.inF quotient_poly_part_2{1}.`2)) =
                aspoint_G1 quotient_poly_part_2_g /\
                ((FieldQ.inF quotient_poly_part_3{1}.`1),
                 (FieldQ.inF quotient_poly_part_3{1}.`2)) =
                aspoint_G1 quotient_poly_part_3_g /\
                ((FieldQ.inF opening_proof_at_z{1}.`1),
                 (FieldQ.inF opening_proof_at_z{1}.`2)) =
                aspoint_G1 opening_proof_at_z_g /\
                ((FieldQ.inF opening_proof_at_z_omega{1}.`1),
                 (FieldQ.inF opening_proof_at_z_omega{1}.`2)) =
                aspoint_G1 opening_proof_at_z_omega_g).
              have H_c_1 := H_on_curve_int state_poly_0{1} H1.
              have H_c_2 := H_on_curve_int state_poly_1{1} H2.
              have H_c_3 := H_on_curve_int state_poly_2{1} H3.
              have H_c_4 := H_on_curve_int state_poly_3{1} H4.
              have H_c_5 := H_on_curve_int copy_permutation_grand_product{1} H5.
              have H_c_6 := H_on_curve_int lookup_s_poly{1} H6.
              have H_c_7 := H_on_curve_int lookup_grand_product{1} H7.
              have H_c_8 := H_on_curve_int quotient_poly_part_0{1} H8.
              have H_c_9 := H_on_curve_int quotient_poly_part_1{1} H9.
              have H_c_10 := H_on_curve_int quotient_poly_part_2{1} H10.
              have H_c_11 := H_on_curve_int quotient_poly_part_3{1} H11.
              have H_c_12 := H_on_curve_int opening_proof_at_z{1} H12.
              have H_c_13 := H_on_curve_int opening_proof_at_z_omega{1} H13.
              case H_c_1. move => p1 H_p1. exists p1.
              case H_c_2. move => p2 H_p2. exists p2.
              case H_c_3. move => p3 H_p3. exists p3.
              case H_c_4. move => p4 H_p4. exists p4.
              case H_c_5. move => p5 H_p5. exists p5.
              case H_c_6. move => p6 H_p6. exists p6.
              case H_c_7. move => p7 H_p7. exists p7.
              case H_c_8. move => p8 H_p8. exists p8.
              case H_c_9. move => p9 H_p9. exists p9.
              case H_c_10. move => p10 H_p10. exists p10.
              case H_c_11. move => p11 H_p11. exists p11.
              case H_c_12. move => p12 H_p12. exists p12.
              case H_c_13. move => p13 H_p13. exists p13.
              by progress.
              by progress.
              wp. skip. progress. rewrite H13. by trivial.
              wp. skip. progress. rewrite H12. by trivial.
              wp. skip. progress. rewrite H11. by trivial.
              wp. skip. progress. rewrite H10. by trivial.
              wp. skip. progress. rewrite H9. by trivial.
              wp. skip. progress. rewrite H8. by trivial.
              wp. skip. progress. rewrite H7. by trivial.
              wp. skip. progress. rewrite H6. by trivial.
              wp. skip. progress. rewrite H5. by trivial.
              wp. skip. progress. rewrite H4. by trivial.
              wp. skip. progress. rewrite H3. by trivial.
              wp. skip. progress. rewrite H2. by trivial.
              wp. skip. progress. rewrite H1. by trivial.
            rcondf{1} 4. progress. wp. skip. progress. rewrite H0. by trivial.
            wp. skip. by progress.
            sp 1 0. conseq (_ : failed{1} ==> _). by progress.
            inline InitializeTranscript.mid.
              sp 47 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) GetTranscriptChallenge.GetTranscriptChallenge.mid.
                sp 4 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) GetTranscriptChallenge.GetTranscriptChallenge.mid.
                sp 4 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) GetTranscriptChallenge.GetTranscriptChallenge.mid.
                sp 4 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) GetTranscriptChallenge.GetTranscriptChallenge.mid.
                sp 4 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) GetTranscriptChallenge.GetTranscriptChallenge.mid.
                sp 4 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) GetTranscriptChallenge.GetTranscriptChallenge.mid.
                sp 4 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) GetTranscriptChallenge.GetTranscriptChallenge.mid.
                sp 4 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) Modexp.Modexp.mid.
                sp 3 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) GetTranscriptChallenge.GetTranscriptChallenge.mid.
                sp 4 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) UpdateTranscript.UpdateTranscript.mid.
                sp 6 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) GetTranscriptChallenge.GetTranscriptChallenge.mid.
                sp 4 0. conseq (_ : failed{1} ==> _). by progress.
            sp 1 0. conseq (_ : failed{1} ==> _). by progress.
            inline VerifyQuotientEvaluation.mid.
              sp 28 0. conseq (_ : failed{1} ==> _). by progress.
              inline EvaluateLagrangePolyOutOfDomain.mid.
                sp 5 0. conseq (_ : failed{1} ==> _). by progress.
                sp 1 0. conseq (_ : failed{1} ==> _). progress. case H0; by progress.
                sp 1 0. conseq (_ : failed{1} ==> _). by progress.
                seq 1 0: #pre.
                  if {1}.
                    wp. skip. by progress.
                    sp 11 0. conseq (_ : failed{1} ==> _). progress. case H0; by progress.
                    inline{1} (1) PermutationQuotientContribution.PermutationQuotientContribution.mid.
                      sp 21 0. conseq (_ : failed{1} ==> _). by progress.
                    inline{1} (1) LookupQuotientContribution.LookupQuotientContribution.mid.
                      sp 14 0. conseq (_ : failed{1} ==> _). by progress.
                    inline Modexp.Modexp.mid. sp. skip. by progress.
            sp 2 0. conseq (_ : failed{1} ==> _). progress. left. assumption.
            inline PrepareQueries.mid.
              sp 56 0. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) PointMulAndAddIntoDest.mid.
                sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
              inline{1} (1) PointMulAndAddIntoDest.mid.
                sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
              inline{1} (1) PointMulAndAddIntoDest.mid.
                sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
              inline{1} (1) MainGateLinearisationContributionWithV.MainGateLinearisationContributionWithV.mid.
                sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                inline{1} (1) PointAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                inline{1} (1) PointMulIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
              inline AddAssignRescueCustomGateLinearisationContributionWithV.AddAssignRescueCustomGateLinearisationContributionWithV.mid.
                sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
              inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
                sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                inline{1} (1) PointSubAssign.PointSubAssign.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                  inline{1} (1) PointNegate.PointNegate.mid.
                    sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                    seq 3 0: #pre.
                      if{1}.
                        sp. skip. by progress; case H0; progress.
                        inline{1} (1) PointAddIntoDest.mid.
                          sp 12 0. conseq (_ : failed{1} ==> _). by progress.
                        sp. skip. by progress; case H0; progress.
                sp 3 0. conseq (_ : failed{1} ==> _). by progress.
              inline AddAssignLookupLinearisationContributionWithV.mid.
                sp. conseq (_ : failed{1} ==> _). by progress.
              inline{1} (1) PointMulAndAddIntoDest.mid.
                sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
              inline{1} (1) PointMulAndAddIntoDest.mid.
                sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
              inline{1} (1) PointMulAndAddIntoDest.mid.
                sp. conseq (_ : failed{1} ==> _). progress.
                  case H1. by progress. progress. case H3. by progress. by progress.
            inline PrepareAggregatedCommitment.mid.
              sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) UpdateAggregationChallenge.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) PointMulIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) UpdateAggregationChallenge_105.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge_105.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge_105.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) UpdateAggregationChallenge_105.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulAndAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. progress. case H2. by progress. by progress. progress. case H2. by progress. by progress.
                inline{1} (1) PointAddIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointMulIntoDest.mid.
                  sp. conseq (_ : failed{1} ==> _). progress. case H1. by progress. by progress.
              inline FinalPairing.mid.
                sp. conseq (_ : failed{1} ==> _). by progress.
                inline{1} (1) PointSubAssign.PointSubAssign.mid.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                  inline{1} (1) PointNegate.PointNegate.mid.
                    sp. conseq (_ : failed{1} ==> _). progress. case H0. by progress. by progress.
                  seq 1 0: #pre.
                    if{1}. sp. skip. by progress.
                      inline PointAddIntoDest.mid.
                      sp. skip. by progress.
                  sp. conseq (_ : failed{1} ==> _). by progress.
                  inline{1} (1) PointMulAndAddIntoDest.mid.
                    sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                  inline{1} (1) PointMulAndAddIntoDest.mid.
                    sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                  inline{1} (1) PointMulAndAddIntoDest.mid.
                    sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                  inline{1} (1) PointNegate.PointNegate.mid.
                    sp. conseq (_ : failed{1} ==> _). progress. case H0. by progress. by progress.
                  seq 1 0: #pre.
                    if{1}.
                      inline{1} (1) PointMulAndAddIntoDest.mid.
                        sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                      inline{1} (1) PointMulAndAddIntoDest.mid.
                        sp. conseq (_ : failed{1} ==> _). by progress; case H0; progress.
                      skip. by progress.
                    skip. by progress.
                sp. skip. progress. left. assumption.
qed.
