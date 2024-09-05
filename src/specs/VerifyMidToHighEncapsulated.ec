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

import MemoryMap PurePrimops.

lemma verify_mid_equiv_high_encapsulated:
    equiv [
      Verify.mid ~ Verify.high_encapsulated:
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
        (* only necessary if we generalise over vk_recursive_flag /\
        recursive_part_p1{1} = F_to_int_point(aspoint_G1 recursive_part_p1{2} /\
        recursive_part_p2{1} = F_to_int_point(aspoint_G1 recursive_part_p2{2}) *) ==> 
        ={res}
    ].
    proof.
      proc.
      simplify.
      cfold{1} 1.
      cfold{1} 1.
      seq 42 2: (
        #pre /\
        !failed{1} /\ !failed{2} /\
        !vk_recursive_flag{1} /\ !vk_recursive_flag{2} /\
        (vk_gate_setup_0X{1}, vk_gate_setup_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_0) /\
        (vk_gate_setup_1X{1}, vk_gate_setup_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_1) /\
        (vk_gate_setup_2X{1}, vk_gate_setup_2Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_2) /\
        (vk_gate_setup_3X{1}, vk_gate_setup_3Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_3) /\
        (vk_gate_setup_4X{1}, vk_gate_setup_4Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_4) /\
        (vk_gate_setup_5X{1}, vk_gate_setup_5Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_5) /\
        (vk_gate_setup_6X{1}, vk_gate_setup_6Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_6) /\
        (vk_gate_setup_7X{1}, vk_gate_setup_7Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_7) /\
        (vk_gate_selectors_0X{1}, vk_gate_selectors_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_0) /\
        (vk_gate_selectors_1X{1}, vk_gate_selectors_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_1) /\
        (vk_permutation_0X{1}, vk_permutation_0Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_0) /\
        (vk_permutation_1X{1}, vk_permutation_1Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_1) /\
        (vk_permutation_2X{1}, vk_permutation_2Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_2) /\
        (vk_permutation_3X{1}, vk_permutation_3Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_3) /\
        (vk_lookup_table_0X{1}, vk_lookup_table_0Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_0) /\
        (vk_lookup_table_1X{1}, vk_lookup_table_1Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_1) /\
        (vk_lookup_table_2X{1}, vk_lookup_table_2Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_2) /\
        (vk_lookup_table_3X{1}, vk_lookup_table_3Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_3) /\
        (vk_lookup_selector_X{1}, vk_lookup_selector_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_selector) /\
        (vk_lookup_table_type_X{1}, vk_lookup_table_type_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_type)
      ).
      wp. skip. progress.
      rewrite vk_gate_setup_0_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_gate_setup_1_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_gate_setup_2_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_gate_setup_3_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_gate_setup_4_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_gate_setup_5_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_gate_setup_6_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_gate_setup_7_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_gate_selectors_0_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_gate_selectors_1_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_permutation_0_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_permutation_1_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_permutation_2_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_permutation_3_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_lookup_table_0_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_lookup_table_1_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_lookup_table_2_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_lookup_table_3_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_lookup_selector_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      rewrite vk_lookup_table_type_F /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK -Constants.q_eq_fieldq_p /Constants.Q. rewrite pmod_small. by progress. rewrite pmod_small. by progress. by progress.
      sp.
      seq 3 3: (
        (failed{1} /\ failed{2}) \/
        (!failed{1} /\ !failed{2} /\
        _public_input{1} = FieldR.asint _public_input{2} /\ 0 <= public_input{1} < (2^253) /\
        _state_poly_0{1} = F_to_int_point(aspoint_G1 _state_poly_0{2}) /\
        _state_poly_1{1} = F_to_int_point(aspoint_G1 _state_poly_1{2}) /\
        _state_poly_2{1} = F_to_int_point(aspoint_G1 _state_poly_2{2}) /\
        _state_poly_3{1} = F_to_int_point(aspoint_G1 _state_poly_3{2}) /\
        _copy_permutation_grand_product{1} = F_to_int_point(aspoint_G1 _copy_permutation_grand_product{2}) /\
        _lookup_s_poly{1} = F_to_int_point(aspoint_G1 _lookup_s_poly{2}) /\
        _lookup_grand_product{1} = F_to_int_point(aspoint_G1 _lookup_grand_product{2}) /\
        _quotient_poly_part_0{1} = F_to_int_point(aspoint_G1 _quotient_poly_part_0{2}) /\
        _quotient_poly_part_1{1} = F_to_int_point(aspoint_G1 _quotient_poly_part_1{2}) /\
        _quotient_poly_part_2{1} = F_to_int_point(aspoint_G1 _quotient_poly_part_2{2}) /\
        _quotient_poly_part_3{1} = F_to_int_point(aspoint_G1 _quotient_poly_part_3{2}) /\
        _state_poly_0_opening_at_z{1} = FieldR.asint _state_poly_0_opening_at_z{2} /\
        _state_poly_1_opening_at_z{1} = FieldR.asint _state_poly_1_opening_at_z{2} /\
        _state_poly_2_opening_at_z{1} = FieldR.asint _state_poly_2_opening_at_z{2} /\
        _state_poly_3_opening_at_z{1} = FieldR.asint _state_poly_3_opening_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = FieldR.asint _state_poly_3_opening_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = FieldR.asint _gate_selector_0_opening_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = FieldR.asint _copy_permutation_poly_0_opening_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = FieldR.asint _copy_permutation_poly_1_opening_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = FieldR.asint _copy_permutation_poly_2_opening_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = FieldR.asint _copy_permutation_grand_product_opening_at_z_omega{2} /\
        _lookup_s_poly_opening_at_z_omega{1} = FieldR.asint _lookup_s_poly_opening_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = FieldR.asint _lookup_grand_product_opening_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = FieldR.asint _lookup_t_poly_opening_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = FieldR.asint _lookup_t_poly_opening_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = FieldR.asint _lookup_selector_poly_opening_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = FieldR.asint _lookup_table_type_poly_opening_at_z{2} /\
        _quotient_poly_opening_at_z{1} = FieldR.asint _quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = FieldR.asint _linearisation_poly_opening_at_z{2} /\
        _opening_proof_at_z{1} = F_to_int_point(aspoint_G1 _opening_proof_at_z{2}) /\
        _opening_proof_at_z_omega{1} = F_to_int_point(aspoint_G1 _opening_proof_at_z_omega{2}) /\
        _recursive_part_p1{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p1{2}) /\
        _recursive_part_p2{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p2{2}) /\
        !vk_recursive_flag{1} /\ !vk_recursive_flag{2} /\
        (vk_gate_setup_0X{1}, vk_gate_setup_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_0) /\
        (vk_gate_setup_1X{1}, vk_gate_setup_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_1) /\
        (vk_gate_setup_2X{1}, vk_gate_setup_2Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_2) /\
        (vk_gate_setup_3X{1}, vk_gate_setup_3Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_3) /\
        (vk_gate_setup_4X{1}, vk_gate_setup_4Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_4) /\
        (vk_gate_setup_5X{1}, vk_gate_setup_5Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_5) /\
        (vk_gate_setup_6X{1}, vk_gate_setup_6Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_6) /\
        (vk_gate_setup_7X{1}, vk_gate_setup_7Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_7) /\
        (vk_gate_selectors_0X{1}, vk_gate_selectors_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_0) /\
        (vk_gate_selectors_1X{1}, vk_gate_selectors_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_1) /\
        (vk_permutation_0X{1}, vk_permutation_0Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_0) /\
        (vk_permutation_1X{1}, vk_permutation_1Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_1) /\
        (vk_permutation_2X{1}, vk_permutation_2Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_2) /\
        (vk_permutation_3X{1}, vk_permutation_3Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_3) /\
        (vk_lookup_table_0X{1}, vk_lookup_table_0Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_0) /\
        (vk_lookup_table_1X{1}, vk_lookup_table_1Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_1) /\
        (vk_lookup_table_2X{1}, vk_lookup_table_2Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_2) /\
        (vk_lookup_table_3X{1}, vk_lookup_table_3Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_3) /\
        (vk_lookup_selector_X{1}, vk_lookup_selector_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_selector) /\
        (vk_lookup_table_type_X{1}, vk_lookup_table_type_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_type)
      )).
      wp.
      call (loadProof_mid_equiv_high false). skip.
      progress.
      rewrite H3 H4. by progress.
      rewrite H3. by progress.
      case H25. by progress. progress. right. by progress.

      seq 1 1: (
        (failed{1} /\ failed{2}) \/ (
          !failed{1} /\  !failed{2} /\
          _public_input{1} = FieldR.asint _public_input{2} /\ 0 <= public_input{1} < (2^253) /\
          _state_poly_0{1} = F_to_int_point (aspoint_G1 _state_poly_0{2}) /\
          _state_poly_1{1} = F_to_int_point (aspoint_G1 _state_poly_1{2}) /\
           _state_poly_2{1} = F_to_int_point (aspoint_G1 _state_poly_2{2}) /\
          _state_poly_3{1} = F_to_int_point (aspoint_G1 _state_poly_3{2}) /\
          _copy_permutation_grand_product{1} = F_to_int_point (aspoint_G1 _copy_permutation_grand_product{2}) /\
          _lookup_s_poly{1} = F_to_int_point (aspoint_G1 _lookup_s_poly{2}) /\
          _lookup_grand_product{1} = F_to_int_point (aspoint_G1 _lookup_grand_product{2}) /\
          _quotient_poly_part_0{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_0{2}) /\
          _quotient_poly_part_1{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_1{2}) /\
          _quotient_poly_part_2{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_2{2}) /\
          _quotient_poly_part_3{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_3{2}) /\
          _state_poly_0_opening_at_z{1} = FieldR.asint _state_poly_0_opening_at_z{2} /\
          _state_poly_1_opening_at_z{1} = FieldR.asint _state_poly_1_opening_at_z{2} /\
          _state_poly_2_opening_at_z{1} = FieldR.asint _state_poly_2_opening_at_z{2} /\
          _state_poly_3_opening_at_z{1} = FieldR.asint _state_poly_3_opening_at_z{2} /\
          _state_poly_3_opening_at_z_omega{1} = FieldR.asint _state_poly_3_opening_at_z_omega{2} /\
          _gate_selector_0_opening_at_z{1} = FieldR.asint _gate_selector_0_opening_at_z{2} /\
          _copy_permutation_poly_0_opening_at_z{1} = FieldR.asint _copy_permutation_poly_0_opening_at_z{2} /\
          _copy_permutation_poly_1_opening_at_z{1} = FieldR.asint _copy_permutation_poly_1_opening_at_z{2} /\
          _copy_permutation_poly_2_opening_at_z{1} = FieldR.asint _copy_permutation_poly_2_opening_at_z{2} /\
          _copy_permutation_grand_product_opening_at_z_omega{1} = FieldR.asint _copy_permutation_grand_product_opening_at_z_omega{2} /\
          _lookup_s_poly_opening_at_z_omega{1} = FieldR.asint _lookup_s_poly_opening_at_z_omega{2} /\
          _lookup_grand_product_opening_at_z_omega{1} = FieldR.asint _lookup_grand_product_opening_at_z_omega{2} /\
          _lookup_t_poly_opening_at_z{1} = FieldR.asint _lookup_t_poly_opening_at_z{2} /\
          _lookup_t_poly_opening_at_z_omega{1} = FieldR.asint _lookup_t_poly_opening_at_z_omega{2} /\
          _lookup_selector_poly_opening_at_z{1} = FieldR.asint _lookup_selector_poly_opening_at_z{2} /\
           _lookup_table_type_poly_opening_at_z{1} = FieldR.asint _lookup_table_type_poly_opening_at_z{2} /\
          _quotient_poly_opening_at_z{1} = FieldR.asint _quotient_poly_opening_at_z{2} /\
          _linearisation_poly_opening_at_z{1} = FieldR.asint _linearisation_poly_opening_at_z{2} /\
          _opening_proof_at_z{1} = F_to_int_point (aspoint_G1 _opening_proof_at_z{2}) /\
          _opening_proof_at_z_omega{1} = F_to_int_point (aspoint_G1 _opening_proof_at_z_omega{2}) /\
          _recursive_part_p1{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p1{2}) /\
          _recursive_part_p2{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p2{2}) /\
          state_alpha{1} = FieldR.asint state_alpha{2} /\
          state_beta{1} = FieldR.asint state_beta{2} /\
          state_beta_lookup{1} = FieldR.asint state_beta_lookup{2} /\
          state_gamma{1} = FieldR.asint state_gamma{2} /\
          state_gamma_lookup{1} = FieldR.asint state_gamma_lookup{2} /\
          state_eta{1} = FieldR.asint state_eta{2} /\
          state_z{1} = FieldR.asint state_z{2} /\
          state_z_in_domain{1} = FieldR.asint state_z_in_domain{2} /\
          state_v{1} = FieldR.asint state_v{2} /\
          state_u{1} = FieldR.asint state_u{2} /\
          !vk_recursive_flag{1} /\ !vk_recursive_flag{2} /\
          (vk_gate_setup_0X{1}, vk_gate_setup_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_0) /\
          (vk_gate_setup_1X{1}, vk_gate_setup_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_1) /\
          (vk_gate_setup_2X{1}, vk_gate_setup_2Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_2) /\
          (vk_gate_setup_3X{1}, vk_gate_setup_3Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_3) /\
          (vk_gate_setup_4X{1}, vk_gate_setup_4Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_4) /\
          (vk_gate_setup_5X{1}, vk_gate_setup_5Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_5) /\
          (vk_gate_setup_6X{1}, vk_gate_setup_6Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_6) /\
          (vk_gate_setup_7X{1}, vk_gate_setup_7Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_7) /\
          (vk_gate_selectors_0X{1}, vk_gate_selectors_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_0) /\
          (vk_gate_selectors_1X{1}, vk_gate_selectors_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_1) /\
          (vk_permutation_0X{1}, vk_permutation_0Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_0) /\
          (vk_permutation_1X{1}, vk_permutation_1Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_1) /\
          (vk_permutation_2X{1}, vk_permutation_2Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_2) /\
          (vk_permutation_3X{1}, vk_permutation_3Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_3) /\
          (vk_lookup_table_0X{1}, vk_lookup_table_0Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_0) /\
          (vk_lookup_table_1X{1}, vk_lookup_table_1Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_1) /\
          (vk_lookup_table_2X{1}, vk_lookup_table_2Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_2) /\
          (vk_lookup_table_3X{1}, vk_lookup_table_3Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_3) /\
          (vk_lookup_selector_X{1}, vk_lookup_selector_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_selector) /\
          (vk_lookup_table_type_X{1}, vk_lookup_table_type_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_type)
        )
      ).
      case (failed{1}).
      conseq (_: failed{1} /\ failed{2} ==> failed{1} /\ failed{2}).
      progress. case H. by progress. by progress.
      progress. left. rewrite H1 H2. by progress.
      kill{1} 1. inline*. wp. skip. by progress.
      kill{2} 1. inline*. wp. skip. by progress.
      skip. by progress.
      exists* _public_input{2}, _state_poly_0{2}, _state_poly_1{2}, _state_poly_2{2}, _state_poly_3{2}, _lookup_s_poly{2}, _copy_permutation_grand_product{2}, _lookup_grand_product{2}, _quotient_poly_part_0{2}, _quotient_poly_part_1{2}, _quotient_poly_part_2{2}, _quotient_poly_part_3{2}, _quotient_poly_opening_at_z{2}, _state_poly_0_opening_at_z{2}, _state_poly_1_opening_at_z{2}, _state_poly_2_opening_at_z{2}, _state_poly_3_opening_at_z{2}, _state_poly_3_opening_at_z_omega{2}, _gate_selector_0_opening_at_z{2}, _copy_permutation_poly_0_opening_at_z{2}, _copy_permutation_poly_1_opening_at_z{2}, _copy_permutation_poly_2_opening_at_z{2}, _copy_permutation_grand_product_opening_at_z_omega{2}, _lookup_t_poly_opening_at_z{2}, _lookup_selector_poly_opening_at_z{2}, _lookup_table_type_poly_opening_at_z{2}, _lookup_s_poly_opening_at_z_omega{2}, _lookup_grand_product_opening_at_z_omega{2}, _lookup_t_poly_opening_at_z_omega{2}, _linearisation_poly_opening_at_z{2}, _opening_proof_at_z{2}, _opening_proof_at_z_omega{2}.
      elim* => _public_input_r _state_poly_0_r _state_poly_1_r _state_poly_2_r _state_poly_3_r _lookup_s_poly_r _copy_permutation_grand_product_r _lookup_grand_product_r _quotient_poly_part_0_r _quotient_poly_part_1_r _quotient_poly_part_2_r _quotient_poly_part_3_r _quotient_poly_opening_at_z_r _state_poly_0_opening_at_z_r _state_poly_1_opening_at_z_r _state_poly_2_opening_at_z_r _state_poly_3_opening_at_z_r _state_poly_3_opening_at_z_omega_r _gate_selector_0_opening_at_z_r _copy_permutation_poly_0_opening_at_z_r _copy_permutation_poly_1_opening_at_z_r _copy_permutation_poly_2_opening_at_z_r _copy_permutation_grand_product_opening_at_z_omega_r _lookup_t_poly_opening_at_z_r _lookup_selector_poly_opening_at_z_r _lookup_table_type_poly_opening_at_z_r _lookup_s_poly_opening_at_z_omega_r _lookup_grand_product_opening_at_z_omega_r _lookup_t_poly_opening_at_z_omega_r _linearisation_poly_opening_at_z_r _opening_proof_at_z_r _opening_proof_at_z_omega_r.
      call initializeTranscript_mid_equiv_high.
      wp. skip. progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. by progress.
      case H. by progress. progress. rewrite H H55. by progress.
      
      seq 2 2: (
        (failed{1} /\ failed{2}) \/ (
          !failed{1} /\  !failed{2} /\
          _public_input{1} = FieldR.asint _public_input{2} /\
          _state_poly_0{1} = F_to_int_point (aspoint_G1 _state_poly_0{2}) /\
          _state_poly_1{1} = F_to_int_point (aspoint_G1 _state_poly_1{2}) /\
           _state_poly_2{1} = F_to_int_point (aspoint_G1 _state_poly_2{2}) /\
          _state_poly_3{1} = F_to_int_point (aspoint_G1 _state_poly_3{2}) /\
          _copy_permutation_grand_product{1} = F_to_int_point (aspoint_G1 _copy_permutation_grand_product{2}) /\
          _lookup_s_poly{1} = F_to_int_point (aspoint_G1 _lookup_s_poly{2}) /\
          _lookup_grand_product{1} = F_to_int_point (aspoint_G1 _lookup_grand_product{2}) /\
          _quotient_poly_part_0{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_0{2}) /\
          _quotient_poly_part_1{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_1{2}) /\
          _quotient_poly_part_2{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_2{2}) /\
          _quotient_poly_part_3{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_3{2}) /\
          _state_poly_0_opening_at_z{1} = FieldR.asint _state_poly_0_opening_at_z{2} /\
          _state_poly_1_opening_at_z{1} = FieldR.asint _state_poly_1_opening_at_z{2} /\
          _state_poly_2_opening_at_z{1} = FieldR.asint _state_poly_2_opening_at_z{2} /\
          _state_poly_3_opening_at_z{1} = FieldR.asint _state_poly_3_opening_at_z{2} /\
          _state_poly_3_opening_at_z_omega{1} = FieldR.asint _state_poly_3_opening_at_z_omega{2} /\
          _gate_selector_0_opening_at_z{1} = FieldR.asint _gate_selector_0_opening_at_z{2} /\
          _copy_permutation_poly_0_opening_at_z{1} = FieldR.asint _copy_permutation_poly_0_opening_at_z{2} /\
          _copy_permutation_poly_1_opening_at_z{1} = FieldR.asint _copy_permutation_poly_1_opening_at_z{2} /\
          _copy_permutation_poly_2_opening_at_z{1} = FieldR.asint _copy_permutation_poly_2_opening_at_z{2} /\
          _copy_permutation_grand_product_opening_at_z_omega{1} = FieldR.asint _copy_permutation_grand_product_opening_at_z_omega{2} /\
          _lookup_s_poly_opening_at_z_omega{1} = FieldR.asint _lookup_s_poly_opening_at_z_omega{2} /\
          _lookup_grand_product_opening_at_z_omega{1} = FieldR.asint _lookup_grand_product_opening_at_z_omega{2} /\
          _lookup_t_poly_opening_at_z{1} = FieldR.asint _lookup_t_poly_opening_at_z{2} /\
          _lookup_t_poly_opening_at_z_omega{1} = FieldR.asint _lookup_t_poly_opening_at_z_omega{2} /\
          _lookup_selector_poly_opening_at_z{1} = FieldR.asint _lookup_selector_poly_opening_at_z{2} /\
           _lookup_table_type_poly_opening_at_z{1} = FieldR.asint _lookup_table_type_poly_opening_at_z{2} /\
          _quotient_poly_opening_at_z{1} = FieldR.asint _quotient_poly_opening_at_z{2} /\
          _linearisation_poly_opening_at_z{1} = FieldR.asint _linearisation_poly_opening_at_z{2} /\
          _opening_proof_at_z{1} = F_to_int_point (aspoint_G1 _opening_proof_at_z{2}) /\
          _opening_proof_at_z_omega{1} = F_to_int_point (aspoint_G1 _opening_proof_at_z_omega{2}) /\
          _recursive_part_p1{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p1{2}) /\
          _recursive_part_p2{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p2{2}) /\
          state_alpha{1} = FieldR.asint state_alpha{2} /\
          state_beta{1} = FieldR.asint state_beta{2} /\
          state_beta_lookup{1} = FieldR.asint state_beta_lookup{2} /\
          state_gamma{1} = FieldR.asint state_gamma{2} /\
          state_gamma_lookup{1} = FieldR.asint state_gamma_lookup{2} /\
          state_eta{1} = FieldR.asint state_eta{2} /\
          state_z{1} = FieldR.asint state_z{2} /\
          state_z_in_domain{1} = FieldR.asint state_z_in_domain{2} /\
          state_v{1} = FieldR.asint state_v{2} /\
          state_u{1} = FieldR.asint state_u{2} /\
          alpha2{1} = FieldR.asint alpha2{2} /\
          alpha3{1} = FieldR.asint alpha3{2} /\
          alpha4{1} = FieldR.asint alpha4{2} /\
          alpha5{1} = FieldR.asint alpha5{2} /\
          alpha6{1} = FieldR.asint alpha6{2} /\
          alpha7{1} = FieldR.asint alpha7{2} /\
          alpha8{1} = FieldR.asint alpha8{2} /\
          l0_at_z{1} = FieldR.asint l0_at_z{2} /\
          ln_minus_one_at_z{1} = FieldR.asint ln_minus_one_at_z{2} /\
          beta_plus_one{1} = FieldR.asint beta_plus_one{2} /\
          beta_gamma_plus_gamma{1} = FieldR.asint beta_gamma_plus_gamma{2} /\
          z_minus_last_omega{1} = FieldR.asint z_minus_last_omega{2} /\
        !vk_recursive_flag{1} /\ !vk_recursive_flag{2} /\
        (vk_gate_setup_0X{1}, vk_gate_setup_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_0) /\
        (vk_gate_setup_1X{1}, vk_gate_setup_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_1) /\
        (vk_gate_setup_2X{1}, vk_gate_setup_2Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_2) /\
        (vk_gate_setup_3X{1}, vk_gate_setup_3Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_3) /\
        (vk_gate_setup_4X{1}, vk_gate_setup_4Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_4) /\
        (vk_gate_setup_5X{1}, vk_gate_setup_5Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_5) /\
        (vk_gate_setup_6X{1}, vk_gate_setup_6Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_6) /\
        (vk_gate_setup_7X{1}, vk_gate_setup_7Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_7) /\
        (vk_gate_selectors_0X{1}, vk_gate_selectors_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_0) /\
        (vk_gate_selectors_1X{1}, vk_gate_selectors_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_1) /\
        (vk_permutation_0X{1}, vk_permutation_0Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_0) /\
        (vk_permutation_1X{1}, vk_permutation_1Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_1) /\
        (vk_permutation_2X{1}, vk_permutation_2Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_2) /\
        (vk_permutation_3X{1}, vk_permutation_3Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_3) /\
        (vk_lookup_table_0X{1}, vk_lookup_table_0Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_0) /\
        (vk_lookup_table_1X{1}, vk_lookup_table_1Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_1) /\
        (vk_lookup_table_2X{1}, vk_lookup_table_2Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_2) /\
        (vk_lookup_table_3X{1}, vk_lookup_table_3Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_3) /\
        (vk_lookup_selector_X{1}, vk_lookup_selector_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_selector) /\
        (vk_lookup_table_type_X{1}, vk_lookup_table_type_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_type)
        )
      ).
      case (failed{1}).
      conseq(_ : (failed{1} /\ failed{2}) ==> (failed{1} /\ failed{2})).
      progress. by case H; progress.
      progress. left. rewrite H1 H2. by progress.
      wp. inline*. wp. skip. progress.
      left. assumption.
      left. assumption.
      left. assumption.
      left. assumption.
      left. assumption.

      exists* state_alpha{2}, state_beta{2}, state_beta_lookup{2}, state_gamma{2}, state_gamma_lookup{2}, state_z{2}, _public_input{2}, _copy_permutation_poly_0_opening_at_z{2}, _copy_permutation_poly_1_opening_at_z{2}, _copy_permutation_poly_2_opening_at_z{2}, _state_poly_0_opening_at_z{2}, _state_poly_1_opening_at_z{2}, _state_poly_2_opening_at_z{2}, _state_poly_3_opening_at_z{2}, _lookup_s_poly_opening_at_z_omega{2}, _lookup_grand_product_opening_at_z_omega{2}, _gate_selector_0_opening_at_z{2}, _linearisation_poly_opening_at_z{2}, _copy_permutation_grand_product_opening_at_z_omega{2}, state_z_in_domain{2}, _quotient_poly_opening_at_z{2}.
      elim*=> state_alpha_r state_beta_r state_beta_lookup_r state_gamma_r state_gamma_lookup_r state_z_r _public_input_r _copy_permutation_poly_0_opening_at_z_r _copy_permutation_poly_1_opening_at_z_r _copy_permutation_poly_2_opening_at_z_r _state_poly_0_opening_at_z_r _state_poly_1_opening_at_z_r _state_poly_2_opening_at_z_r _state_poly_3_opening_at_z_r _lookup_s_poly_opening_at_z_omega_r _lookup_grand_product_opening_at_z_omega_r _gate_selector_0_opening_at_z_r _linearisation_poly_opening_at_z_r _copy_permutation_grand_product_opening_at_z_omega_r state_z_in_domain_r _quotient_poly_opening_at_z_r.
      wp.
      call (verifyQuotientEvaluation_mid_equiv_high 
        state_alpha_r state_beta_r state_beta_lookup_r state_gamma_r state_gamma_lookup_r state_z_r _public_input_r _copy_permutation_poly_0_opening_at_z_r _copy_permutation_poly_1_opening_at_z_r _copy_permutation_poly_2_opening_at_z_r _state_poly_0_opening_at_z_r _state_poly_1_opening_at_z_r _state_poly_2_opening_at_z_r _state_poly_3_opening_at_z_r _lookup_s_poly_opening_at_z_omega_r _lookup_grand_product_opening_at_z_omega_r _gate_selector_0_opening_at_z_r _linearisation_poly_opening_at_z_r _copy_permutation_grand_product_opening_at_z_omega_r state_z_in_domain_r _quotient_poly_opening_at_z_r
      ).
      skip. progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      rewrite H0. simplify.
      case H2.
      progress.
      rewrite -H1 H2. by progress.
      rewrite -H1. progress.
      case (result_L.`1). by progress.
      progress.
      case x; first last. by progress.
      progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.

      seq 3 1: (
        (failed{1} /\ failed{2}) \/ (
          !failed{1} /\  !failed{2} /\
          _public_input{1} = FieldR.asint _public_input{2} /\
          _state_poly_0{1} = F_to_int_point (aspoint_G1 _state_poly_0{2}) /\
          _state_poly_1{1} = F_to_int_point (aspoint_G1 _state_poly_1{2}) /\
           _state_poly_2{1} = F_to_int_point (aspoint_G1 _state_poly_2{2}) /\
          _state_poly_3{1} = F_to_int_point (aspoint_G1 _state_poly_3{2}) /\
          _copy_permutation_grand_product{1} = F_to_int_point (aspoint_G1 _copy_permutation_grand_product{2}) /\
          _lookup_s_poly{1} = F_to_int_point (aspoint_G1 _lookup_s_poly{2}) /\
          _lookup_grand_product{1} = F_to_int_point (aspoint_G1 _lookup_grand_product{2}) /\
          _quotient_poly_part_0{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_0{2}) /\
          _quotient_poly_part_1{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_1{2}) /\
          _quotient_poly_part_2{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_2{2}) /\
          _quotient_poly_part_3{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_3{2}) /\
          _state_poly_0_opening_at_z{1} = FieldR.asint _state_poly_0_opening_at_z{2} /\
          _state_poly_1_opening_at_z{1} = FieldR.asint _state_poly_1_opening_at_z{2} /\
          _state_poly_2_opening_at_z{1} = FieldR.asint _state_poly_2_opening_at_z{2} /\
          _state_poly_3_opening_at_z{1} = FieldR.asint _state_poly_3_opening_at_z{2} /\
          _state_poly_3_opening_at_z_omega{1} = FieldR.asint _state_poly_3_opening_at_z_omega{2} /\
          _gate_selector_0_opening_at_z{1} = FieldR.asint _gate_selector_0_opening_at_z{2} /\
          _copy_permutation_poly_0_opening_at_z{1} = FieldR.asint _copy_permutation_poly_0_opening_at_z{2} /\
          _copy_permutation_poly_1_opening_at_z{1} = FieldR.asint _copy_permutation_poly_1_opening_at_z{2} /\
          _copy_permutation_poly_2_opening_at_z{1} = FieldR.asint _copy_permutation_poly_2_opening_at_z{2} /\
          _copy_permutation_grand_product_opening_at_z_omega{1} = FieldR.asint _copy_permutation_grand_product_opening_at_z_omega{2} /\
          _lookup_s_poly_opening_at_z_omega{1} = FieldR.asint _lookup_s_poly_opening_at_z_omega{2} /\
          _lookup_grand_product_opening_at_z_omega{1} = FieldR.asint _lookup_grand_product_opening_at_z_omega{2} /\
          _lookup_t_poly_opening_at_z{1} = FieldR.asint _lookup_t_poly_opening_at_z{2} /\
          _lookup_t_poly_opening_at_z_omega{1} = FieldR.asint _lookup_t_poly_opening_at_z_omega{2} /\
          _lookup_selector_poly_opening_at_z{1} = FieldR.asint _lookup_selector_poly_opening_at_z{2} /\
           _lookup_table_type_poly_opening_at_z{1} = FieldR.asint _lookup_table_type_poly_opening_at_z{2} /\
          _quotient_poly_opening_at_z{1} = FieldR.asint _quotient_poly_opening_at_z{2} /\
          _linearisation_poly_opening_at_z{1} = FieldR.asint _linearisation_poly_opening_at_z{2} /\
          _opening_proof_at_z{1} = F_to_int_point (aspoint_G1 _opening_proof_at_z{2}) /\
          _opening_proof_at_z_omega{1} = F_to_int_point (aspoint_G1 _opening_proof_at_z_omega{2}) /\
          _recursive_part_p1{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p1{2}) /\
          _recursive_part_p2{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p2{2}) /\
          state_alpha{1} = FieldR.asint state_alpha{2} /\
          state_beta{1} = FieldR.asint state_beta{2} /\
          state_beta_lookup{1} = FieldR.asint state_beta_lookup{2} /\
          state_gamma{1} = FieldR.asint state_gamma{2} /\
          state_gamma_lookup{1} = FieldR.asint state_gamma_lookup{2} /\
          state_eta{1} = FieldR.asint state_eta{2} /\
          state_z{1} = FieldR.asint state_z{2} /\
          state_z_in_domain{1} = FieldR.asint state_z_in_domain{2} /\
          state_v{1} = FieldR.asint state_v{2} /\
          state_u{1} = FieldR.asint state_u{2} /\
          alpha2{1} = FieldR.asint alpha2{2} /\
          alpha3{1} = FieldR.asint alpha3{2} /\
          alpha4{1} = FieldR.asint alpha4{2} /\
          alpha5{1} = FieldR.asint alpha5{2} /\
          alpha6{1} = FieldR.asint alpha6{2} /\
          alpha7{1} = FieldR.asint alpha7{2} /\
          alpha8{1} = FieldR.asint alpha8{2} /\
          l0_at_z{1} = FieldR.asint l0_at_z{2} /\
          ln_minus_one_at_z{1} = FieldR.asint ln_minus_one_at_z{2} /\
          beta_plus_one{1} = FieldR.asint beta_plus_one{2} /\
          beta_gamma_plus_gamma{1} = FieldR.asint beta_gamma_plus_gamma{2} /\
          z_minus_last_omega{1} = FieldR.asint z_minus_last_omega{2} /\
          query_at_z_0{1} = F_to_int_point(aspoint_G1 query_at_z_0{2}) /\
          query_at_z_1{1} = F_to_int_point(aspoint_G1 query_at_z_1{2}) /\
          copy_permutation_first_aggregated_commitment_coeff{1} = FieldR.asint copy_permutation_first_aggregated_commitment_coeff{2} /\
          lookup_s_first_aggregated_commitment{1} = FieldR.asint lookupSFirstAggregatedCommitment{2} /\
          lookup_grand_product_first_aggregated_coefficient{1} = FieldR.asint lookupGrandProductFirstAggregatedCoefficient{2} /\
          query_t_poly_aggregated{1} = F_to_int_point(aspoint_G1 query_t_poly_aggregated{2}) /\
        !vk_recursive_flag{1} /\ !vk_recursive_flag{2} /\
        (vk_gate_setup_0X{1}, vk_gate_setup_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_0) /\
        (vk_gate_setup_1X{1}, vk_gate_setup_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_1) /\
        (vk_gate_setup_2X{1}, vk_gate_setup_2Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_2) /\
        (vk_gate_setup_3X{1}, vk_gate_setup_3Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_3) /\
        (vk_gate_setup_4X{1}, vk_gate_setup_4Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_4) /\
        (vk_gate_setup_5X{1}, vk_gate_setup_5Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_5) /\
        (vk_gate_setup_6X{1}, vk_gate_setup_6Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_6) /\
        (vk_gate_setup_7X{1}, vk_gate_setup_7Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_7) /\
        (vk_gate_selectors_0X{1}, vk_gate_selectors_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_0) /\
        (vk_gate_selectors_1X{1}, vk_gate_selectors_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_1) /\
        (vk_permutation_0X{1}, vk_permutation_0Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_0) /\
        (vk_permutation_1X{1}, vk_permutation_1Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_1) /\
        (vk_permutation_2X{1}, vk_permutation_2Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_2) /\
        (vk_permutation_3X{1}, vk_permutation_3Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_3) /\
        (vk_lookup_table_0X{1}, vk_lookup_table_0Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_0) /\
        (vk_lookup_table_1X{1}, vk_lookup_table_1Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_1) /\
        (vk_lookup_table_2X{1}, vk_lookup_table_2Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_2) /\
        (vk_lookup_table_3X{1}, vk_lookup_table_3Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_3) /\
        (vk_lookup_selector_X{1}, vk_lookup_selector_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_selector) /\
        (vk_lookup_table_type_X{1}, vk_lookup_table_type_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_type)
        )
      ).
      wp.
      case (failed{1}).
      conseq (_: (failed{1} /\ failed{2}) ==> (failed{1} /\ failed{2})).
      progress. case H. by progress. by progress.
      progress. left. rewrite H1 H2. by progress.
      inline PrepareQueries.high. wp.
      inline PrepareQueries.mid. sp.
      (* this becomes incredibly slow if not split up like this *)
      seq 11 0: (failed{1} /\ failed{2}). inline*. wp. skip. by progress.
      seq 3 0: (failed{1} /\ failed{2}). inline*. wp. skip. by progress.
      seq 3 0: (failed{1} /\ failed{2}). inline*. wp. skip. by progress.
      seq 3 0: (failed{1} /\ failed{2}). inline*. wp. skip. by progress.
      seq 3 0: (failed{1} /\ failed{2}). inline*. wp. skip. by progress.
      inline*. wp. skip. by progress.

      call prepareQueries_mid_equiv_high.
      skip. progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      right. by case H; progress.

      seq 3 1: (
        (failed{1} /\ failed{2}) \/ (
          !failed{1} /\  !failed{2} /\
          _public_input{1} = FieldR.asint _public_input{2} /\
          _state_poly_0{1} = F_to_int_point (aspoint_G1 _state_poly_0{2}) /\
          _state_poly_1{1} = F_to_int_point (aspoint_G1 _state_poly_1{2}) /\
           _state_poly_2{1} = F_to_int_point (aspoint_G1 _state_poly_2{2}) /\
          _state_poly_3{1} = F_to_int_point (aspoint_G1 _state_poly_3{2}) /\
          _copy_permutation_grand_product{1} = F_to_int_point (aspoint_G1 _copy_permutation_grand_product{2}) /\
          _lookup_s_poly{1} = F_to_int_point (aspoint_G1 _lookup_s_poly{2}) /\
          _lookup_grand_product{1} = F_to_int_point (aspoint_G1 _lookup_grand_product{2}) /\
          _quotient_poly_part_0{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_0{2}) /\
          _quotient_poly_part_1{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_1{2}) /\
          _quotient_poly_part_2{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_2{2}) /\
          _quotient_poly_part_3{1} = F_to_int_point (aspoint_G1 _quotient_poly_part_3{2}) /\
          _state_poly_0_opening_at_z{1} = FieldR.asint _state_poly_0_opening_at_z{2} /\
          _state_poly_1_opening_at_z{1} = FieldR.asint _state_poly_1_opening_at_z{2} /\
          _state_poly_2_opening_at_z{1} = FieldR.asint _state_poly_2_opening_at_z{2} /\
          _state_poly_3_opening_at_z{1} = FieldR.asint _state_poly_3_opening_at_z{2} /\
          _state_poly_3_opening_at_z_omega{1} = FieldR.asint _state_poly_3_opening_at_z_omega{2} /\
          _gate_selector_0_opening_at_z{1} = FieldR.asint _gate_selector_0_opening_at_z{2} /\
          _copy_permutation_poly_0_opening_at_z{1} = FieldR.asint _copy_permutation_poly_0_opening_at_z{2} /\
          _copy_permutation_poly_1_opening_at_z{1} = FieldR.asint _copy_permutation_poly_1_opening_at_z{2} /\
          _copy_permutation_poly_2_opening_at_z{1} = FieldR.asint _copy_permutation_poly_2_opening_at_z{2} /\
          _copy_permutation_grand_product_opening_at_z_omega{1} = FieldR.asint _copy_permutation_grand_product_opening_at_z_omega{2} /\
          _lookup_s_poly_opening_at_z_omega{1} = FieldR.asint _lookup_s_poly_opening_at_z_omega{2} /\
          _lookup_grand_product_opening_at_z_omega{1} = FieldR.asint _lookup_grand_product_opening_at_z_omega{2} /\
          _lookup_t_poly_opening_at_z{1} = FieldR.asint _lookup_t_poly_opening_at_z{2} /\
          _lookup_t_poly_opening_at_z_omega{1} = FieldR.asint _lookup_t_poly_opening_at_z_omega{2} /\
          _lookup_selector_poly_opening_at_z{1} = FieldR.asint _lookup_selector_poly_opening_at_z{2} /\
           _lookup_table_type_poly_opening_at_z{1} = FieldR.asint _lookup_table_type_poly_opening_at_z{2} /\
          _quotient_poly_opening_at_z{1} = FieldR.asint _quotient_poly_opening_at_z{2} /\
          _linearisation_poly_opening_at_z{1} = FieldR.asint _linearisation_poly_opening_at_z{2} /\
          _opening_proof_at_z{1} = F_to_int_point (aspoint_G1 _opening_proof_at_z{2}) /\
          _opening_proof_at_z_omega{1} = F_to_int_point (aspoint_G1 _opening_proof_at_z_omega{2}) /\
          _recursive_part_p1{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p1{2}) /\
          _recursive_part_p2{1} = omap F_to_int_point (omap aspoint_G1 _recursive_part_p2{2}) /\
          state_alpha{1} = FieldR.asint state_alpha{2} /\
          state_beta{1} = FieldR.asint state_beta{2} /\
          state_beta_lookup{1} = FieldR.asint state_beta_lookup{2} /\
          state_gamma{1} = FieldR.asint state_gamma{2} /\
          state_gamma_lookup{1} = FieldR.asint state_gamma_lookup{2} /\
          state_eta{1} = FieldR.asint state_eta{2} /\
          state_z{1} = FieldR.asint state_z{2} /\
          state_z_in_domain{1} = FieldR.asint state_z_in_domain{2} /\
          state_v{1} = FieldR.asint state_v{2} /\
          state_u{1} = FieldR.asint state_u{2} /\
          alpha2{1} = FieldR.asint alpha2{2} /\
          alpha3{1} = FieldR.asint alpha3{2} /\
          alpha4{1} = FieldR.asint alpha4{2} /\
          alpha5{1} = FieldR.asint alpha5{2} /\
          alpha6{1} = FieldR.asint alpha6{2} /\
          alpha7{1} = FieldR.asint alpha7{2} /\
          alpha8{1} = FieldR.asint alpha8{2} /\
          l0_at_z{1} = FieldR.asint l0_at_z{2} /\
          ln_minus_one_at_z{1} = FieldR.asint ln_minus_one_at_z{2} /\
          beta_plus_one{1} = FieldR.asint beta_plus_one{2} /\
          beta_gamma_plus_gamma{1} = FieldR.asint beta_gamma_plus_gamma{2} /\
          z_minus_last_omega{1} = FieldR.asint z_minus_last_omega{2} /\
          query_at_z_0{1} = F_to_int_point(aspoint_G1 query_at_z_0{2}) /\
          query_at_z_1{1} = F_to_int_point(aspoint_G1 query_at_z_1{2}) /\
          copy_permutation_first_aggregated_commitment_coeff{1} = FieldR.asint copy_permutation_first_aggregated_commitment_coeff{2} /\
          lookup_s_first_aggregated_commitment{1} = FieldR.asint lookupSFirstAggregatedCommitment{2} /\
          lookup_grand_product_first_aggregated_coefficient{1} = FieldR.asint lookupGrandProductFirstAggregatedCoefficient{2} /\
          query_t_poly_aggregated{1} = F_to_int_point(aspoint_G1 query_t_poly_aggregated{2}) /\
        !vk_recursive_flag{1} /\ !vk_recursive_flag{2} /\
        (vk_gate_setup_0X{1}, vk_gate_setup_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_0) /\
        (vk_gate_setup_1X{1}, vk_gate_setup_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_1) /\
        (vk_gate_setup_2X{1}, vk_gate_setup_2Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_2) /\
        (vk_gate_setup_3X{1}, vk_gate_setup_3Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_3) /\
        (vk_gate_setup_4X{1}, vk_gate_setup_4Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_4) /\
        (vk_gate_setup_5X{1}, vk_gate_setup_5Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_5) /\
        (vk_gate_setup_6X{1}, vk_gate_setup_6Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_6) /\
        (vk_gate_setup_7X{1}, vk_gate_setup_7Y{1}) = F_to_int_point (aspoint_G1 vk_gate_setup_7) /\
        (vk_gate_selectors_0X{1}, vk_gate_selectors_0Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_0) /\
        (vk_gate_selectors_1X{1}, vk_gate_selectors_1Y{1}) = F_to_int_point (aspoint_G1 vk_gate_selectors_1) /\
        (vk_permutation_0X{1}, vk_permutation_0Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_0) /\
        (vk_permutation_1X{1}, vk_permutation_1Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_1) /\
        (vk_permutation_2X{1}, vk_permutation_2Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_2) /\
        (vk_permutation_3X{1}, vk_permutation_3Y{1}) = F_to_int_point (aspoint_G1 vk_permutation_3) /\
        (vk_lookup_table_0X{1}, vk_lookup_table_0Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_0) /\
        (vk_lookup_table_1X{1}, vk_lookup_table_1Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_1) /\
        (vk_lookup_table_2X{1}, vk_lookup_table_2Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_2) /\
        (vk_lookup_table_3X{1}, vk_lookup_table_3Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_3) /\
        (vk_lookup_selector_X{1}, vk_lookup_selector_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_selector) /\
        (vk_lookup_table_type_X{1}, vk_lookup_table_type_Y{1}) = F_to_int_point (aspoint_G1 vk_lookup_table_type) /\
        aggregated_at_z{1} = F_to_int_point (aspoint_G1 aggregatedAtZSlot{2}) /\
        aggregated_opening_at_z{1} = FieldR.asint aggregatedOpeningAtZSlot{2} /\
        aggregated_at_z_omega{1} = F_to_int_point (aspoint_G1 aggregatedAtZOmegaSlot{2}) /\
        aggregated_opening_at_z_omega{1} = FieldR.asint aggregatedOpeningAtZOmega{2} /\
        pairing_pair_with_generator{1} = F_to_int_point (aspoint_G1 pairingPairWithGeneratorSlot{2}) /\
        pairing_buffer_point{1} = F_to_int_point (aspoint_G1 pairingBufferPointSlot{2})
        )
      ).
      case (failed{1}).
      conseq (_: (failed{1} /\ failed{2}) ==> (failed{1} /\ failed{2})).
      progress. by case H; progress.
      progress. case H. move => [H_fail1 H_fail2]. left. by progress.
      by progress.
      wp.
      conseq (_: (failed{1} /\ failed{2}) ==> (failed{1} /\ failed{2})). progress. left. assumption.
      kill{1} 1. inline PrepareAggregatedCommitment.mid. sp.
        conseq (_ : true ==> true).
        inline PointAddIntoDest.mid. sp.
        inline (1) UpdateAggregationChallenge.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline PointMulIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge_105.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge_105.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge_105.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        inline (1) UpdateAggregationChallenge_105.mid. sp. conseq (_ : true ==> true).
          inline PointMulAndAddIntoDest.mid. sp. conseq (_ : true ==> true).
        skip. by trivial.
      inline *. wp. skip. by progress.

      wp.
      call prepareAggregatedCommitment_mid_equiv_high.
      skip. progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      right. by case H; progress.

      case (failed{1}).
      conseq (_ : (failed{1} /\ failed{2}) ==> (failed{1} /\ failed{2})). progress.
      case H. by progress. by progress.
      progress. case H. progress. rewrite H1 H2. by progress.
      by progress.
      inline FinalPairing.high. wp.
      conseq (_ : (failed{1} /\ failed{2}) ==> (failed{1} /\ failed{2})). progress.
      left. assumption.
      left. assumption.
      left. assumption.
      left. assumption.
      inline*. wp. skip. by progress.

      wp. call finalPairing_mid_equiv_high. skip. progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      by case H; progress.
      case H. by progress. progress. rewrite H2 H3. by progress.
      case H. by progress. progress. rewrite H3. by progress.
      case H. by progress. progress. rewrite H3. by progress.
      case H. by progress. progress.
      rewrite H H3.
      by trivial.
qed.