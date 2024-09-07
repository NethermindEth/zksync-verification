pragma Goals:printall.

require import AllCore.
require import FinalPairing.
require import InitializeTranscript.
require import LoadProof.
require import PrepareAggregatedCommitment.
require import PrepareQueries.
require import Verify.

lemma verify_high_encapsulated_equiv_super:
    equiv [
      Verify.high_encapsulated ~ Verify.high_encapsulated_super:
      ={arg} ==> ={res}
    ].
    proc.
      sp.
      seq 1 1: (
        ={failed, load_proof_opt}
      ). by sim.
      seq 1 1: #pre. by sim.
      seq 1 1: (
        ={failed, _public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, _lookup_s_poly_opening_at_z_omega, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega, _recursive_part_p1, _recursive_part_p2} /\
        _quotient_poly_part_0{1} = t_0{2} /\
        _quotient_poly_part_1{1} = t_1{2} /\
        _quotient_poly_part_2{1} = t_2{2} /\
        _quotient_poly_part_3{1} = t_3{2} /\
        _state_poly_0_opening_at_z{1} = a_at_z{2} /\
        _state_poly_1_opening_at_z{1} = b_at_z{2} /\
        _state_poly_2_opening_at_z{1} = c_at_z{2} /\
        _state_poly_3_opening_at_z{1} = d_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = d_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = main_gate_selector_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = sigma_0_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = sigma_1_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = sigma_2_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = z_perm_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2}
      ). by sim.
      seq 1 1: (
        ={failed, _public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, _lookup_s_poly_opening_at_z_omega, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega, _recursive_part_p1, _recursive_part_p2} /\
        _quotient_poly_part_0{1} = t_0{2} /\
        _quotient_poly_part_1{1} = t_1{2} /\
        _quotient_poly_part_2{1} = t_2{2} /\
        _quotient_poly_part_3{1} = t_3{2} /\
        _state_poly_0_opening_at_z{1} = a_at_z{2} /\
        _state_poly_1_opening_at_z{1} = b_at_z{2} /\
        _state_poly_2_opening_at_z{1} = c_at_z{2} /\
        _state_poly_3_opening_at_z{1} = d_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = d_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = main_gate_selector_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = sigma_0_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = sigma_1_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = sigma_2_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = z_perm_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
        state_alpha{1} = alpha{2} /\
        state_beta{1} = beta_{2} /\
        state_beta_lookup{1} = beta'{2} /\
        state_gamma{1} = gamma{2} /\
        state_gamma_lookup{1} = gamma'{2} /\
        state_eta{1} = eta_{2} /\
        state_z{1} = z{2} /\
        state_z_in_domain{1} = z_in_domain{2} /\
        state_v{1} = v{2} /\
        state_u{1} = u{2}        
      ). by sim.
      seq 1 1: (
        ={failed, _public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, _lookup_s_poly_opening_at_z_omega, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega, _recursive_part_p1, _recursive_part_p2} /\
        _quotient_poly_part_0{1} = t_0{2} /\
        _quotient_poly_part_1{1} = t_1{2} /\
        _quotient_poly_part_2{1} = t_2{2} /\
        _quotient_poly_part_3{1} = t_3{2} /\
        _state_poly_0_opening_at_z{1} = a_at_z{2} /\
        _state_poly_1_opening_at_z{1} = b_at_z{2} /\
        _state_poly_2_opening_at_z{1} = c_at_z{2} /\
        _state_poly_3_opening_at_z{1} = d_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = d_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = main_gate_selector_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = sigma_0_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = sigma_1_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = sigma_2_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = z_perm_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
        state_alpha{1} = alpha{2} /\
        state_beta{1} = beta_{2} /\
        state_beta_lookup{1} = beta'{2} /\
        state_gamma{1} = gamma{2} /\
        state_gamma_lookup{1} = gamma'{2} /\
        state_eta{1} = eta_{2} /\
        state_z{1} = z{2} /\
        state_z_in_domain{1} = z_in_domain{2} /\
        state_v{1} = v{2} /\
        state_u{1} = u{2} /\
        ={verify_quotient_evaluation_opt, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega} /\
        l0_at_z{1} = l_0_at_z{2} /\
        ln_minus_one_at_z{1} = l_n_minus_one_at_z{2}
      ). by sim.
      seq 1 1: #pre. by sim.
      seq 1 1: (
                ={failed, _public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, _lookup_s_poly_opening_at_z_omega, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega, _recursive_part_p1, _recursive_part_p2} /\
        _quotient_poly_part_0{1} = t_0{2} /\
        _quotient_poly_part_1{1} = t_1{2} /\
        _quotient_poly_part_2{1} = t_2{2} /\
        _quotient_poly_part_3{1} = t_3{2} /\
        _state_poly_0_opening_at_z{1} = a_at_z{2} /\
        _state_poly_1_opening_at_z{1} = b_at_z{2} /\
        _state_poly_2_opening_at_z{1} = c_at_z{2} /\
        _state_poly_3_opening_at_z{1} = d_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = d_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = main_gate_selector_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = sigma_0_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = sigma_1_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = sigma_2_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = z_perm_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
        state_alpha{1} = alpha{2} /\
        state_beta{1} = beta_{2} /\
        state_beta_lookup{1} = beta'{2} /\
        state_gamma{1} = gamma{2} /\
        state_gamma_lookup{1} = gamma'{2} /\
        state_eta{1} = eta_{2} /\
        state_z{1} = z{2} /\
        state_z_in_domain{1} = z_in_domain{2} /\
        state_v{1} = v{2} /\
        state_u{1} = u{2} /\
        ={verify_quotient_evaluation_opt, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega} /\
        l0_at_z{1} = l_0_at_z{2} /\
        ln_minus_one_at_z{1} = l_n_minus_one_at_z{2} /\
        ={query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated}        
      ). call prepareQueries_high_equiv_super_high. skip. progress.
      
