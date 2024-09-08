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

lemma verify_high_encapsulated_equiv_high:
    equiv [
      Verify.high_encapsulated ~ Verify.high:
      ={arg} ==> ={res}
    ].
    proof.
      proc.
      seq 5 29: (
        (failed{1} /\ !isValid{2}) \/ (
        !failed{1} /\ isValid{2} /\
        !vk_recursive_flag{1} /\
        _public_input{1} = public_input{2} /\
        _state_poly_0{1} = a{2} /\
        _state_poly_1{1} = b{2} /\
        _state_poly_2{1} = c{2} /\
        _state_poly_3{1} = d{2} /\
        _copy_permutation_grand_product{1} = z_perm{2} /\
        _lookup_s_poly{1} = s{2} /\
        _lookup_grand_product{1} = z_lookup{2} /\
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
        _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
        _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
        _opening_proof_at_z{1} = w{2} /\
        _opening_proof_at_z_omega{1} = w'{2} /\
        _recursive_part_p1{1} = None /\
        _recursive_part_p2{1} = None /\
        k0{2} = FieldR.inF Constants.NON_RESIDUE_0 /\
        k1{2} = FieldR.inF Constants.NON_RESIDUE_1 /\ 
        k2{2} = FieldR.inF Constants.NON_RESIDUE_2 /\
        n{2} = Constants.DOMAIN_SIZE /\
        q_a{2} = vk_gate_setup_0 /\
        q_b{2} = vk_gate_setup_1 /\
        q_c{2} = vk_gate_setup_2 /\
        q_d{2} = vk_gate_setup_3 /\
        q_ab{2} = vk_gate_setup_4 /\
        q_ac{2} = vk_gate_setup_5 /\
        q_const{2} = vk_gate_setup_6 /\
        q_d_next{2} = vk_gate_setup_7 /\
        custom_gate_selector{2} = vk_gate_selectors_1 /\
        sigma_0{2} = vk_permutation_0 /\
        sigma_1{2} = vk_permutation_1 /\
        sigma_2{2} = vk_permutation_2 /\ 
        sigma_3{2} = vk_permutation_3 /\
        lookup_selector{2} = vk_lookup_selector /\
        table_type{2} = vk_lookup_table_type /\
        omega{2} = Constants.OMEGAFr /\
        col_0{2} = vk_lookup_table_0 /\
        col_1{2} = vk_lookup_table_1 /\
        col_2{2} = vk_lookup_table_2 /\
        col_3{2} = vk_lookup_table_3
      )).
        inline LoadProof.high.
        rcondf{1} 43. progress. wp. skip. by progress.
        case (
          public_input_length_in_words{1} = 1 /\
          proof_length_in_words{1} = 44 /\
          recursive_proof_length_in_words{1} = 0
        ).
          rcondt{1} 46. progress. wp. skip. by progress.
          wp. skip. by progress.
        (* false case *)
          rcondf{1} 46. progress. wp. skip. progress. rewrite -andbA. assumption.
          wp. skip. progress. rewrite -andbA. assumption.

      (* load proof done *)

      (* initialize transcript *)
      seq 1 16: (
        (failed{1} /\ !isValid{2}) \/ (
        !failed{1} /\ isValid{2} /\
        !vk_recursive_flag{1} /\
        _public_input{1} = public_input{2} /\
        _state_poly_0{1} = a{2} /\
        _state_poly_1{1} = b{2} /\
        _state_poly_2{1} = c{2} /\
        _state_poly_3{1} = d{2} /\
        _copy_permutation_grand_product{1} = z_perm{2} /\
        _lookup_s_poly{1} = s{2} /\
        _lookup_grand_product{1} = z_lookup{2} /\
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
        _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
        _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
        _opening_proof_at_z{1} = w{2} /\
        _opening_proof_at_z_omega{1} = w'{2} /\
        _recursive_part_p1{1} = None /\
        _recursive_part_p2{1} = None /\
        k0{2} = FieldR.inF Constants.NON_RESIDUE_0 /\
        k1{2} = FieldR.inF Constants.NON_RESIDUE_1 /\ 
        k2{2} = FieldR.inF Constants.NON_RESIDUE_2 /\
        n{2} = Constants.DOMAIN_SIZE /\
        q_a{2} = vk_gate_setup_0 /\
        q_b{2} = vk_gate_setup_1 /\
        q_c{2} = vk_gate_setup_2 /\
        q_d{2} = vk_gate_setup_3 /\
        q_ab{2} = vk_gate_setup_4 /\
        q_ac{2} = vk_gate_setup_5 /\
        q_const{2} = vk_gate_setup_6 /\
        q_d_next{2} = vk_gate_setup_7 /\
        custom_gate_selector{2} = vk_gate_selectors_1 /\
        sigma_0{2} = vk_permutation_0 /\
        sigma_1{2} = vk_permutation_1 /\
        sigma_2{2} = vk_permutation_2 /\ 
        sigma_3{2} = vk_permutation_3 /\
        lookup_selector{2} = vk_lookup_selector /\
        table_type{2} = vk_lookup_table_type /\
        omega{2} = Constants.OMEGAFr /\
        col_0{2} = vk_lookup_table_0 /\
        col_1{2} = vk_lookup_table_1 /\
        col_2{2} = vk_lookup_table_2 /\
        col_3{2} = vk_lookup_table_3 /\
        state_alpha{1} = alpha{2} /\
        state_beta{1} = beta_{2} /\
        state_beta_lookup{1} = beta'{2} /\
        state_gamma{1} = gamma{2} /\
        state_gamma_lookup{1} = gamma'{2} /\
        state_eta{1} = eta_{2} /\
        state_z{1} = z{2} /\
        state_z_in_domain{1} = z{2} ^ n{2} /\
        state_v{1} = v{2} /\
        state_u{1} = u{2} 
      )).
        inline InitializeTranscript.high.
        case (failed{1}).
          conseq (_ : (failed{1} /\ !isValid{2}) ==> (failed{1} /\ !isValid{2})).
            progress. by case H; progress.
            progress. left. by progress.
          wp. skip. by progress.
        (* case !failed{1} *)
          cfold{1} 1. cfold{1} 1.
          sp 32 0.

          conseq (_ : (
            !failed{1} /\
            isValid{2} /\
            !vk_recursive_flag{1} /\
            _public_input{1} = public_input{2} /\
            _state_poly_0{1} = a{2} /\
            _state_poly_1{1} = b{2} /\
            _state_poly_2{1} = c{2} /\
            _state_poly_3{1} = d{2} /\
            _copy_permutation_grand_product{1} = z_perm{2} /\
            _lookup_s_poly{1} = s{2} /\
            _lookup_grand_product{1} = z_lookup{2} /\
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
            _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
            _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
            _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
            _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
            _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
            _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
            _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
            _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
            _opening_proof_at_z{1} = w{2} /\
            _opening_proof_at_z_omega{1} = w'{2} /\
            _recursive_part_p1{1} = None /\
            _recursive_part_p2{1} = None /\
            k0{2} = (FieldR.inF Constants.NON_RESIDUE_0) /\
            k1{2} = (FieldR.inF Constants.NON_RESIDUE_1) /\
            k2{2} = (FieldR.inF Constants.NON_RESIDUE_2) /\
            n{2} = Constants.DOMAIN_SIZE /\
            q_a{2} = vk_gate_setup_0 /\
            q_b{2} = vk_gate_setup_1 /\
            q_c{2} = vk_gate_setup_2 /\
            q_d{2} = vk_gate_setup_3 /\
            q_ab{2} = vk_gate_setup_4 /\
            q_ac{2} = vk_gate_setup_5 /\
            q_const{2} = vk_gate_setup_6 /\
            q_d_next{2} = vk_gate_setup_7 /\
            custom_gate_selector{2} = vk_gate_selectors_1 /\
            sigma_0{2} = vk_permutation_0 /\
            sigma_1{2} = vk_permutation_1 /\
            sigma_2{2} = vk_permutation_2 /\
            sigma_3{2} = vk_permutation_3 /\
            lookup_selector{2} = vk_lookup_selector /\
            table_type{2} = vk_lookup_table_type /\
            omega{2} = Constants.OMEGAFr /\
            col_0{2} = vk_lookup_table_0 /\
            col_1{2} = vk_lookup_table_1 /\
            col_2{2} = vk_lookup_table_2 /\
            col_3{2} = vk_lookup_table_3 /\
            n{2} = Constants.DOMAIN_SIZE /\
            proofOpeningProofAtZ{1} = w{2} /\
            proofOpeningProofAtZOmega{1} = w'{2} /\
            proofQuotientPolyOpeningAtZ{1} = quotient_poly_opening_at_z{2} /\
            proofStatePolys0OpeningAtZ{1} = a_at_z{2} /\
            proofStatePolys1OpeningAtZ{1} = b_at_z{2} /\
            proofStatePolys2OpeningAtZ{1} = c_at_z{2} /\
            proofStatePolys3OpeningAtZ{1} = d_at_z{2} /\
            proofStatePolys3OpeningAtZOmega{1} = d_at_z_omega{2} /\
            proofGateSelectors0OpeningAtZ{1} = main_gate_selector_at_z{2} /\
            proofCopyPermutationPolys0OpeningAtZ{1} = sigma_0_at_z{2} /\
            proofCopyPermutationPolys1OpeningAtZ{1} = sigma_1_at_z{2} /\
            proofCopyPermutationPolys2OpeningAtZ{1} = sigma_2_at_z{2} /\
            proofCopyPermutationGrandProductOpeningAtZOmega{1} = z_perm_at_z_omega{2} /\
            proofLookupTPolyOpeningAtZ{1} = t_at_z{2} /\
            proofLookupSelectorPolyOpeningAtZ{1} = lookup_selector_at_z{2} /\
            proofLookupTableTypePolyOpeningAtZ{1} = table_type_at_z{2} /\
            proofLookupSPolyOpeningAtZOmega{1} = s_at_z_omega{2} /\
            proofLookupGrandProductOpeningAtZOmega{1} = z_lookup_at_z_omega{2} /\
            proofLookupTPolyOpeningAtZOmega{1} = t_at_z_omega{2} /\
            proofLinearisationPolyOpeningAtZ{1} = r_at_z{2} /\
            publicInput{1} = public_input{2} /\
            proofStatePolys0{1} = a{2} /\
            proofStatePolys1{1} = b{2} /\
            proofStatePolys2{1} = c{2} /\
            proofStatePolys3{1} = d{2} /\
            proofLookupSPoly{1} = s{2} /\
            proofCopyPermutationGrandProduct{1} = z_perm{2} /\
            proofLookupGrandProduct{1} = z_lookup{2} /\
            proofQuotientPolyParts0{1} = t_0{2} /\
            proofQuotientPolyParts1{1} = t_1{2} /\
            proofQuotientPolyParts2{1} = t_2{2} /\
            proofQuotientPolyParts3{1} = t_3{2}
          ) ==> _). by progress; case H; progress.
            
          seq 19 2: (
            #pre /\
            state{2} = (state0_8{1}, state1_8{1}) /\
            stateEta{1} = eta_{2}          
          ).
            wp. skip. rewrite /commit_fr /commit_g. by progress.

          seq 6 3: (
            !failed{1} /\
            isValid{2} /\
            !vk_recursive_flag{1} /\
            _public_input{1} = public_input{2} /\
            _state_poly_0{1} = a{2} /\
            _state_poly_1{1} = b{2} /\
            _state_poly_2{1} = c{2} /\
            _state_poly_3{1} = d{2} /\
            _copy_permutation_grand_product{1} = z_perm{2} /\
            _lookup_s_poly{1} = s{2} /\
            _lookup_grand_product{1} = z_lookup{2} /\
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
            _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
            _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
            _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
            _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
            _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
            _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
            _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
            _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
            _opening_proof_at_z{1} = w{2} /\
            _opening_proof_at_z_omega{1} = w'{2} /\
            _recursive_part_p1{1} = None /\
            _recursive_part_p2{1} = None /\
            k0{2} = (FieldR.inF Constants.NON_RESIDUE_0) /\
            k1{2} = (FieldR.inF Constants.NON_RESIDUE_1) /\
            k2{2} = (FieldR.inF Constants.NON_RESIDUE_2) /\
            n{2} = Constants.DOMAIN_SIZE /\
            q_a{2} = vk_gate_setup_0 /\
            q_b{2} = vk_gate_setup_1 /\
            q_c{2} = vk_gate_setup_2 /\
            q_d{2} = vk_gate_setup_3 /\
            q_ab{2} = vk_gate_setup_4 /\
            q_ac{2} = vk_gate_setup_5 /\
            q_const{2} = vk_gate_setup_6 /\
            q_d_next{2} = vk_gate_setup_7 /\
            custom_gate_selector{2} = vk_gate_selectors_1 /\
            sigma_0{2} = vk_permutation_0 /\
            sigma_1{2} = vk_permutation_1 /\
            sigma_2{2} = vk_permutation_2 /\
            sigma_3{2} = vk_permutation_3 /\
            lookup_selector{2} = vk_lookup_selector /\
            table_type{2} = vk_lookup_table_type /\
            omega{2} = Constants.OMEGAFr /\
            col_0{2} = vk_lookup_table_0 /\
            col_1{2} = vk_lookup_table_1 /\
            col_2{2} = vk_lookup_table_2 /\
            col_3{2} = vk_lookup_table_3 /\
            n{2} = Constants.DOMAIN_SIZE /\
            proofOpeningProofAtZ{1} = w{2} /\
            proofOpeningProofAtZOmega{1} = w'{2} /\
            proofQuotientPolyOpeningAtZ{1} = quotient_poly_opening_at_z{2} /\
            proofStatePolys0OpeningAtZ{1} = a_at_z{2} /\
            proofStatePolys1OpeningAtZ{1} = b_at_z{2} /\
            proofStatePolys2OpeningAtZ{1} = c_at_z{2} /\
            proofStatePolys3OpeningAtZ{1} = d_at_z{2} /\
            proofStatePolys3OpeningAtZOmega{1} = d_at_z_omega{2} /\
            proofGateSelectors0OpeningAtZ{1} = main_gate_selector_at_z{2} /\
            proofCopyPermutationPolys0OpeningAtZ{1} = sigma_0_at_z{2} /\
            proofCopyPermutationPolys1OpeningAtZ{1} = sigma_1_at_z{2} /\
            proofCopyPermutationPolys2OpeningAtZ{1} = sigma_2_at_z{2} /\
            proofCopyPermutationGrandProductOpeningAtZOmega{1} = z_perm_at_z_omega{2} /\
            proofLookupTPolyOpeningAtZ{1} = t_at_z{2} /\
            proofLookupSelectorPolyOpeningAtZ{1} = lookup_selector_at_z{2} /\
            proofLookupTableTypePolyOpeningAtZ{1} = table_type_at_z{2} /\
            proofLookupSPolyOpeningAtZOmega{1} = s_at_z_omega{2} /\
            proofLookupGrandProductOpeningAtZOmega{1} = z_lookup_at_z_omega{2} /\
            proofLookupTPolyOpeningAtZOmega{1} = t_at_z_omega{2} /\
            proofLinearisationPolyOpeningAtZ{1} = r_at_z{2} /\
            proofCopyPermutationGrandProduct{1} = z_perm{2} /\
            proofLookupGrandProduct{1} = z_lookup{2} /\
            proofQuotientPolyParts0{1} = t_0{2} /\
            proofQuotientPolyParts1{1} = t_1{2} /\
            proofQuotientPolyParts2{1} = t_2{2} /\
            proofQuotientPolyParts3{1} = t_3{2} /\
            state{2} = (state0_10{1}, state1_10{1}) /\
            stateBeta{1} = beta_{2} /\
            stateGamma{1} = gamma{2} /\
            stateEta{1} = eta_{2}
          ).
            wp. skip. rewrite /commit_fr /commit_g. by progress.

          seq 6 3: (
            !failed{1} /\
            isValid{2} /\
            !vk_recursive_flag{1} /\
            _public_input{1} = public_input{2} /\
            _state_poly_0{1} = a{2} /\
            _state_poly_1{1} = b{2} /\
            _state_poly_2{1} = c{2} /\
            _state_poly_3{1} = d{2} /\
            _copy_permutation_grand_product{1} = z_perm{2} /\
            _lookup_s_poly{1} = s{2} /\
            _lookup_grand_product{1} = z_lookup{2} /\
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
            _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
            _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
            _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
            _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
            _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
            _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
            _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
            _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
            _opening_proof_at_z{1} = w{2} /\
            _opening_proof_at_z_omega{1} = w'{2} /\
            _recursive_part_p1{1} = None /\
            _recursive_part_p2{1} = None /\
            k0{2} = (FieldR.inF Constants.NON_RESIDUE_0) /\
            k1{2} = (FieldR.inF Constants.NON_RESIDUE_1) /\
            k2{2} = (FieldR.inF Constants.NON_RESIDUE_2) /\
            n{2} = Constants.DOMAIN_SIZE /\
            q_a{2} = vk_gate_setup_0 /\
            q_b{2} = vk_gate_setup_1 /\
            q_c{2} = vk_gate_setup_2 /\
            q_d{2} = vk_gate_setup_3 /\
            q_ab{2} = vk_gate_setup_4 /\
            q_ac{2} = vk_gate_setup_5 /\
            q_const{2} = vk_gate_setup_6 /\
            q_d_next{2} = vk_gate_setup_7 /\
            custom_gate_selector{2} = vk_gate_selectors_1 /\
            sigma_0{2} = vk_permutation_0 /\
            sigma_1{2} = vk_permutation_1 /\
            sigma_2{2} = vk_permutation_2 /\
            sigma_3{2} = vk_permutation_3 /\
            lookup_selector{2} = vk_lookup_selector /\
            table_type{2} = vk_lookup_table_type /\
            omega{2} = Constants.OMEGAFr /\
            col_0{2} = vk_lookup_table_0 /\
            col_1{2} = vk_lookup_table_1 /\
            col_2{2} = vk_lookup_table_2 /\
            col_3{2} = vk_lookup_table_3 /\
            n{2} = Constants.DOMAIN_SIZE /\
            proofOpeningProofAtZ{1} = w{2} /\
            proofOpeningProofAtZOmega{1} = w'{2} /\
            proofQuotientPolyOpeningAtZ{1} = quotient_poly_opening_at_z{2} /\
            proofStatePolys0OpeningAtZ{1} = a_at_z{2} /\
            proofStatePolys1OpeningAtZ{1} = b_at_z{2} /\
            proofStatePolys2OpeningAtZ{1} = c_at_z{2} /\
            proofStatePolys3OpeningAtZ{1} = d_at_z{2} /\
            proofStatePolys3OpeningAtZOmega{1} = d_at_z_omega{2} /\
            proofGateSelectors0OpeningAtZ{1} = main_gate_selector_at_z{2} /\
            proofCopyPermutationPolys0OpeningAtZ{1} = sigma_0_at_z{2} /\
            proofCopyPermutationPolys1OpeningAtZ{1} = sigma_1_at_z{2} /\
            proofCopyPermutationPolys2OpeningAtZ{1} = sigma_2_at_z{2} /\
            proofCopyPermutationGrandProductOpeningAtZOmega{1} = z_perm_at_z_omega{2} /\
            proofLookupTPolyOpeningAtZ{1} = t_at_z{2} /\
            proofLookupSelectorPolyOpeningAtZ{1} = lookup_selector_at_z{2} /\
            proofLookupTableTypePolyOpeningAtZ{1} = table_type_at_z{2} /\
            proofLookupSPolyOpeningAtZOmega{1} = s_at_z_omega{2} /\
            proofLookupGrandProductOpeningAtZOmega{1} = z_lookup_at_z_omega{2} /\
            proofLookupTPolyOpeningAtZOmega{1} = t_at_z_omega{2} /\
            proofLinearisationPolyOpeningAtZ{1} = r_at_z{2} /\
            proofLookupGrandProduct{1} = z_lookup{2} /\
            proofQuotientPolyParts0{1} = t_0{2} /\
            proofQuotientPolyParts1{1} = t_1{2} /\
            proofQuotientPolyParts2{1} = t_2{2} /\
            proofQuotientPolyParts3{1} = t_3{2} /\
            state{2} = (state0_12{1}, state1_12{1}) /\
            stateBeta{1} = beta_{2} /\
            stateGamma{1} = gamma{2} /\
            stateBetaLookup{1} = beta'{2} /\
            stateGammaLookup{1} = gamma'{2} /\
            stateEta{1} = eta_{2}
          ).
            wp. skip. rewrite /commit_fr /commit_g. by progress.

          seq 5 2: (
            !failed{1} /\
            isValid{2} /\
            !vk_recursive_flag{1} /\
            _public_input{1} = public_input{2} /\
            _state_poly_0{1} = a{2} /\
            _state_poly_1{1} = b{2} /\
            _state_poly_2{1} = c{2} /\
            _state_poly_3{1} = d{2} /\
            _copy_permutation_grand_product{1} = z_perm{2} /\
            _lookup_s_poly{1} = s{2} /\
            _lookup_grand_product{1} = z_lookup{2} /\
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
            _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
            _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
            _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
            _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
            _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
            _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
            _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
            _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
            _opening_proof_at_z{1} = w{2} /\
            _opening_proof_at_z_omega{1} = w'{2} /\
            _recursive_part_p1{1} = None /\
            _recursive_part_p2{1} = None /\
            k0{2} = (FieldR.inF Constants.NON_RESIDUE_0) /\
            k1{2} = (FieldR.inF Constants.NON_RESIDUE_1) /\
            k2{2} = (FieldR.inF Constants.NON_RESIDUE_2) /\
            n{2} = Constants.DOMAIN_SIZE /\
            q_a{2} = vk_gate_setup_0 /\
            q_b{2} = vk_gate_setup_1 /\
            q_c{2} = vk_gate_setup_2 /\
            q_d{2} = vk_gate_setup_3 /\
            q_ab{2} = vk_gate_setup_4 /\
            q_ac{2} = vk_gate_setup_5 /\
            q_const{2} = vk_gate_setup_6 /\
            q_d_next{2} = vk_gate_setup_7 /\
            custom_gate_selector{2} = vk_gate_selectors_1 /\
            sigma_0{2} = vk_permutation_0 /\
            sigma_1{2} = vk_permutation_1 /\
            sigma_2{2} = vk_permutation_2 /\
            sigma_3{2} = vk_permutation_3 /\
            lookup_selector{2} = vk_lookup_selector /\
            table_type{2} = vk_lookup_table_type /\
            omega{2} = Constants.OMEGAFr /\
            col_0{2} = vk_lookup_table_0 /\
            col_1{2} = vk_lookup_table_1 /\
            col_2{2} = vk_lookup_table_2 /\
            col_3{2} = vk_lookup_table_3 /\
            n{2} = Constants.DOMAIN_SIZE /\
            proofOpeningProofAtZ{1} = w{2} /\
            proofOpeningProofAtZOmega{1} = w'{2} /\
            proofQuotientPolyOpeningAtZ{1} = quotient_poly_opening_at_z{2} /\
            proofStatePolys0OpeningAtZ{1} = a_at_z{2} /\
            proofStatePolys1OpeningAtZ{1} = b_at_z{2} /\
            proofStatePolys2OpeningAtZ{1} = c_at_z{2} /\
            proofStatePolys3OpeningAtZ{1} = d_at_z{2} /\
            proofStatePolys3OpeningAtZOmega{1} = d_at_z_omega{2} /\
            proofGateSelectors0OpeningAtZ{1} = main_gate_selector_at_z{2} /\
            proofCopyPermutationPolys0OpeningAtZ{1} = sigma_0_at_z{2} /\
            proofCopyPermutationPolys1OpeningAtZ{1} = sigma_1_at_z{2} /\
            proofCopyPermutationPolys2OpeningAtZ{1} = sigma_2_at_z{2} /\
            proofCopyPermutationGrandProductOpeningAtZOmega{1} = z_perm_at_z_omega{2} /\
            proofLookupTPolyOpeningAtZ{1} = t_at_z{2} /\
            proofLookupSelectorPolyOpeningAtZ{1} = lookup_selector_at_z{2} /\
            proofLookupTableTypePolyOpeningAtZ{1} = table_type_at_z{2} /\
            proofLookupSPolyOpeningAtZOmega{1} = s_at_z_omega{2} /\
            proofLookupGrandProductOpeningAtZOmega{1} = z_lookup_at_z_omega{2} /\
            proofLookupTPolyOpeningAtZOmega{1} = t_at_z_omega{2} /\
            proofLinearisationPolyOpeningAtZ{1} = r_at_z{2} /\
            proofQuotientPolyParts0{1} = t_0{2} /\
            proofQuotientPolyParts1{1} = t_1{2} /\
            proofQuotientPolyParts2{1} = t_2{2} /\
            proofQuotientPolyParts3{1} = t_3{2} /\
            state{2} = (state0_14{1}, state1_14{1}) /\
            stateAlpha{1} = alpha{2} /\
            stateBeta{1} = beta_{2} /\
            stateGamma{1} = gamma{2} /\
            stateBetaLookup{1} = beta'{2} /\
            stateGammaLookup{1} = gamma'{2} /\
            stateEta{1} = eta_{2}            
          ).
            wp. skip. rewrite /commit_fr /commit_g. by progress.

          seq 17 2: (
            !failed{1} /\
            isValid{2} /\
            !vk_recursive_flag{1} /\
            _public_input{1} = public_input{2} /\
            _state_poly_0{1} = a{2} /\
            _state_poly_1{1} = b{2} /\
            _state_poly_2{1} = c{2} /\
            _state_poly_3{1} = d{2} /\
            _copy_permutation_grand_product{1} = z_perm{2} /\
            _lookup_s_poly{1} = s{2} /\
            _lookup_grand_product{1} = z_lookup{2} /\
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
            _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
            _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
            _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
            _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
            _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
            _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
            _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
            _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
            _opening_proof_at_z{1} = w{2} /\
            _opening_proof_at_z_omega{1} = w'{2} /\
            _recursive_part_p1{1} = None /\
            _recursive_part_p2{1} = None /\
            k0{2} = (FieldR.inF Constants.NON_RESIDUE_0) /\
            k1{2} = (FieldR.inF Constants.NON_RESIDUE_1) /\
            k2{2} = (FieldR.inF Constants.NON_RESIDUE_2) /\
            n{2} = Constants.DOMAIN_SIZE /\
            q_a{2} = vk_gate_setup_0 /\
            q_b{2} = vk_gate_setup_1 /\
            q_c{2} = vk_gate_setup_2 /\
            q_d{2} = vk_gate_setup_3 /\
            q_ab{2} = vk_gate_setup_4 /\
            q_ac{2} = vk_gate_setup_5 /\
            q_const{2} = vk_gate_setup_6 /\
            q_d_next{2} = vk_gate_setup_7 /\
            custom_gate_selector{2} = vk_gate_selectors_1 /\
            sigma_0{2} = vk_permutation_0 /\
            sigma_1{2} = vk_permutation_1 /\
            sigma_2{2} = vk_permutation_2 /\
            sigma_3{2} = vk_permutation_3 /\
            lookup_selector{2} = vk_lookup_selector /\
            table_type{2} = vk_lookup_table_type /\
            omega{2} = Constants.OMEGAFr /\
            col_0{2} = vk_lookup_table_0 /\
            col_1{2} = vk_lookup_table_1 /\
            col_2{2} = vk_lookup_table_2 /\
            col_3{2} = vk_lookup_table_3 /\
            n{2} = Constants.DOMAIN_SIZE /\
            proofOpeningProofAtZ{1} = w{2} /\
            proofOpeningProofAtZOmega{1} = w'{2} /\
            proofQuotientPolyOpeningAtZ{1} = quotient_poly_opening_at_z{2} /\
            proofStatePolys0OpeningAtZ{1} = a_at_z{2} /\
            proofStatePolys1OpeningAtZ{1} = b_at_z{2} /\
            proofStatePolys2OpeningAtZ{1} = c_at_z{2} /\
            proofStatePolys3OpeningAtZ{1} = d_at_z{2} /\
            proofStatePolys3OpeningAtZOmega{1} = d_at_z_omega{2} /\
            proofGateSelectors0OpeningAtZ{1} = main_gate_selector_at_z{2} /\
            proofCopyPermutationPolys0OpeningAtZ{1} = sigma_0_at_z{2} /\
            proofCopyPermutationPolys1OpeningAtZ{1} = sigma_1_at_z{2} /\
            proofCopyPermutationPolys2OpeningAtZ{1} = sigma_2_at_z{2} /\
            proofCopyPermutationGrandProductOpeningAtZOmega{1} = z_perm_at_z_omega{2} /\
            proofLookupTPolyOpeningAtZ{1} = t_at_z{2} /\
            proofLookupSelectorPolyOpeningAtZ{1} = lookup_selector_at_z{2} /\
            proofLookupTableTypePolyOpeningAtZ{1} = table_type_at_z{2} /\
            proofLookupSPolyOpeningAtZOmega{1} = s_at_z_omega{2} /\
            proofLookupGrandProductOpeningAtZOmega{1} = z_lookup_at_z_omega{2} /\
            proofLookupTPolyOpeningAtZOmega{1} = t_at_z_omega{2} /\
            proofLinearisationPolyOpeningAtZ{1} = r_at_z{2} /\
            state{2} = (state0_22{1}, state1_22{1}) /\
            stateAlpha{1} = alpha{2} /\
            stateBeta{1} = beta_{2} /\
            stateGamma{1} = gamma{2} /\
            stateBetaLookup{1} = beta'{2} /\
            stateGammaLookup{1} = gamma'{2} /\
            stateEta{1} = eta_{2} /\
            stateZ{1} = z{2}
          ).
            wp. skip. rewrite /commit_fr /commit_g. by progress.

          seq 1 0: (
            #pre /\
            stateZInDomain{1} = z{2} ^ n{2}
          ).
            wp. skip. by progress.

          seq 6 0: (
            #pre /\
            (state0_25{1}, state1_25{1}) = commit_fr(commit_fr(commit_fr state{2} quotient_poly_opening_at_z{2}) a_at_z{2}) b_at_z{2}
          ).
            wp. skip. by progress.

          seq 6 0: (
            #pre /\
            (state0_28{1}, state1_28{1}) = commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr state{2} quotient_poly_opening_at_z{2}) a_at_z{2}) b_at_z{2}) c_at_z{2}) d_at_z{2}) d_at_z_omega{2}
          ).
            wp. skip. progress.
            rewrite -H2 /commit_fr.
            reflexivity.

          seq 6 0: (
            #pre /\
            (state0_31{1}, state1_31{1}) = commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr state{2} quotient_poly_opening_at_z{2}) a_at_z{2}) b_at_z{2}) c_at_z{2}) d_at_z{2}) d_at_z_omega{2}) main_gate_selector_at_z{2}) sigma_0_at_z{2}) sigma_1_at_z{2}
          ).
            wp. skip. progress.
            rewrite -H3 /commit_fr.
            reflexivity.

          seq 6 0: (
            #pre /\
            (state0_34{1}, state1_34{1}) = commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr state{2} quotient_poly_opening_at_z{2}) a_at_z{2}) b_at_z{2}) c_at_z{2}) d_at_z{2}) d_at_z_omega{2}) main_gate_selector_at_z{2}) sigma_0_at_z{2}) sigma_1_at_z{2}) sigma_2_at_z{2}) z_perm_at_z_omega{2}) t_at_z{2}
          ).
            wp. skip. progress.
            rewrite -H4 /commit_fr.
            reflexivity.

          seq 6 0: (
            #pre /\
            (state0_37{1}, state1_37{1}) = commit_fr(commit_fr(commit_fr( commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr state{2} quotient_poly_opening_at_z{2}) a_at_z{2}) b_at_z{2}) c_at_z{2}) d_at_z{2}) d_at_z_omega{2}) main_gate_selector_at_z{2}) sigma_0_at_z{2}) sigma_1_at_z{2}) sigma_2_at_z{2}) z_perm_at_z_omega{2}) t_at_z{2}) lookup_selector_at_z{2}) table_type_at_z{2} ) s_at_z_omega{2}
          ).
            wp. skip. progress.
            rewrite -H5 /commit_fr.
            reflexivity.

          seq 6 0: (
            #pre /\
            (state0_40{1}, state1_40{1}) = commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr(commit_fr state{2} quotient_poly_opening_at_z{2}) a_at_z{2}) b_at_z{2}) c_at_z{2}) d_at_z{2}) d_at_z_omega{2}) main_gate_selector_at_z{2}) sigma_0_at_z{2}) sigma_1_at_z{2}) sigma_2_at_z{2}) z_perm_at_z_omega{2}) t_at_z{2}) lookup_selector_at_z{2}) table_type_at_z{2}) s_at_z_omega{2}) z_lookup_at_z_omega{2}) t_at_z_omega{2}) r_at_z{2}
          ).
            wp. skip. progress.
            rewrite -H6 /commit_fr.
            reflexivity.

          seq 1 2: (
            !failed{1} /\
            isValid{2} /\
            !vk_recursive_flag{1} /\
            _public_input{1} = public_input{2} /\
            _state_poly_0{1} = a{2} /\
            _state_poly_1{1} = b{2} /\
            _state_poly_2{1} = c{2} /\
            _state_poly_3{1} = d{2} /\
            _copy_permutation_grand_product{1} = z_perm{2} /\
            _lookup_s_poly{1} = s{2} /\
            _lookup_grand_product{1} = z_lookup{2} /\
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
            _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
            _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
            _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
            _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
            _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
            _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
            _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
            _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
            _opening_proof_at_z{1} = w{2} /\
            _opening_proof_at_z_omega{1} = w'{2} /\
            _recursive_part_p1{1} = None /\
            _recursive_part_p2{1} = None /\
            k0{2} = (FieldR.inF Constants.NON_RESIDUE_0) /\
            k1{2} = (FieldR.inF Constants.NON_RESIDUE_1) /\
            k2{2} = (FieldR.inF Constants.NON_RESIDUE_2) /\
            n{2} = Constants.DOMAIN_SIZE /\
            q_a{2} = vk_gate_setup_0 /\
            q_b{2} = vk_gate_setup_1 /\
            q_c{2} = vk_gate_setup_2 /\
            q_d{2} = vk_gate_setup_3 /\
            q_ab{2} = vk_gate_setup_4 /\
            q_ac{2} = vk_gate_setup_5 /\
            q_const{2} = vk_gate_setup_6 /\
            q_d_next{2} = vk_gate_setup_7 /\
            custom_gate_selector{2} = vk_gate_selectors_1 /\
            sigma_0{2} = vk_permutation_0 /\
            sigma_1{2} = vk_permutation_1 /\
            sigma_2{2} = vk_permutation_2 /\
            sigma_3{2} = vk_permutation_3 /\
            lookup_selector{2} = vk_lookup_selector /\
            table_type{2} = vk_lookup_table_type /\
            omega{2} = Constants.OMEGAFr /\
            col_0{2} = vk_lookup_table_0 /\
            col_1{2} = vk_lookup_table_1 /\
            col_2{2} = vk_lookup_table_2 /\
            col_3{2} = vk_lookup_table_3 /\
            state{2} = (state0_40{1}, state1_40{1}) /\
            proofOpeningProofAtZ{1} = w{2} /\
            proofOpeningProofAtZOmega{1} = w'{2} /\
            state{2} = (state0_40{1}, state1_40{1}) /\
            stateAlpha{1} = alpha{2} /\
            stateBeta{1} = beta_{2} /\
            stateGamma{1} = gamma{2} /\
            stateBetaLookup{1} = beta'{2} /\
            stateGammaLookup{1} = gamma'{2} /\
            stateEta{1} = eta_{2} /\
            stateZ{1} = z{2} /\
            stateZInDomain{1} = z{2} ^ n{2} /\
            stateV{1} = v{2}
          ).
            wp. skip. progress. rewrite H7. reflexivity.
            rewrite -H7. by progress.
            rewrite -H7 /get_commitment. by progress.

          wp. skip. progress. right. by progress.
      (* initialize transcript done *)

      (* verify quotient evaluation *)
      seq 2 4: (
        (failed{1} /\ !isValid{2}) \/ (
        !failed{1} /\ isValid{2} /\
        !vk_recursive_flag{1} /\
        _public_input{1} = public_input{2} /\
        _state_poly_0{1} = a{2} /\
        _state_poly_1{1} = b{2} /\
        _state_poly_2{1} = c{2} /\
        _state_poly_3{1} = d{2} /\
        _copy_permutation_grand_product{1} = z_perm{2} /\
        _lookup_s_poly{1} = s{2} /\
        _lookup_grand_product{1} = z_lookup{2} /\
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
        _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
        _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
        _opening_proof_at_z{1} = w{2} /\
        _opening_proof_at_z_omega{1} = w'{2} /\
        _recursive_part_p1{1} = None /\
        _recursive_part_p2{1} = None /\
        k0{2} = FieldR.inF Constants.NON_RESIDUE_0 /\
        k1{2} = FieldR.inF Constants.NON_RESIDUE_1 /\ 
        k2{2} = FieldR.inF Constants.NON_RESIDUE_2 /\
        n{2} = Constants.DOMAIN_SIZE /\
        q_a{2} = vk_gate_setup_0 /\
        q_b{2} = vk_gate_setup_1 /\
        q_c{2} = vk_gate_setup_2 /\
        q_d{2} = vk_gate_setup_3 /\
        q_ab{2} = vk_gate_setup_4 /\
        q_ac{2} = vk_gate_setup_5 /\
        q_const{2} = vk_gate_setup_6 /\
        q_d_next{2} = vk_gate_setup_7 /\
        custom_gate_selector{2} = vk_gate_selectors_1 /\
        sigma_0{2} = vk_permutation_0 /\
        sigma_1{2} = vk_permutation_1 /\
        sigma_2{2} = vk_permutation_2 /\ 
        sigma_3{2} = vk_permutation_3 /\
        lookup_selector{2} = vk_lookup_selector /\
        table_type{2} = vk_lookup_table_type /\
        omega{2} = Constants.OMEGAFr /\
        col_0{2} = vk_lookup_table_0 /\
        col_1{2} = vk_lookup_table_1 /\
        col_2{2} = vk_lookup_table_2 /\
        col_3{2} = vk_lookup_table_3 /\
        state_alpha{1} = alpha{2} /\
        state_beta{1} = beta_{2} /\
        state_beta_lookup{1} = beta'{2} /\
        state_gamma{1} = gamma{2} /\
        state_gamma_lookup{1} = gamma'{2} /\
        state_eta{1} = eta_{2} /\
        state_z{1} = z{2} /\
        state_z_in_domain{1} = z{2} ^ n{2} /\
        state_v{1} = v{2} /\
        state_u{1} = u{2} /\
        alpha2{1} = alpha{2}^2 /\
        alpha3{1} = alpha{2}^3 /\
        alpha4{1} = alpha{2}^4 /\
        alpha5{1} = alpha{2}^5 /\
        alpha6{1} = alpha{2}^6 /\
        alpha7{1} = alpha{2}^7 /\
        alpha8{1} = alpha{2}^8 /\
        l0_at_z{1} = l_0_at_z{2} /\
        ln_minus_one_at_z{1} = l_n_minus_one_at_z{2} /\
        beta_plus_one{1} = FieldR.one + beta'{2} /\
        beta_gamma_plus_gamma{1} = gamma'{2} * (FieldR.one + beta'{2}) /\
        z_minus_last_omega{1} = z{2} - omega{2}^(n{2} - 1)
      )).
        case (failed{1}).
        conseq (_: (failed{1} /\ !isValid{2}) ==> (failed{1} /\ !isValid{2})).
          progress. by case H; progress.
          progress. left. by progress.
          inline VerifyQuotientEvaluation.high.
          wp. skip. progress.
            rewrite H0. by progress.
            left. assumption.
            rewrite H0. by progress.

        (* case !failed{1} *)
          inline VerifyQuotientEvaluation.high.
          case (z{2} ^ Constants.DOMAIN_SIZE = FieldR.one).
            rcondt{1} 22. progress.
            wp. skip. progress. by case H; progress.
            wp. skip. progress. rewrite H1. by progress.

          (* case z{2} ^ Constants.DOMAIN_SIZE = FieldR.one *)
            rcondf{1} 22. progress.
            wp. skip. progress. by case H; progress.      
            wp. skip. progress. rewrite H0 H1. case H. by progress.
            progress. rewrite H2 H3. progress.
            have ->: beta'{2} + FieldR.one = FieldR.one + beta'{2} by exact FieldR.ZModule.addrC.
            have ->: gamma'{2} * beta'{2} + gamma'{2} = gamma'{2} * (FieldR.one + beta'{2}) by
              rewrite (FieldR.ZrRing.mulrC _ (FieldR.one + _));
              rewrite FieldR.ComRing.mulrDl;
              rewrite FieldR.ComRing.mul1r;
              rewrite FieldR.ZModule.addrC;
              rewrite FieldR.ZrRing.mulrC;
              reflexivity.
            progress.
            pose a8 := FieldR.( * ) (FieldR.( * ) (alpha{2}^8)  _) _.
            pose a7 := FieldR.( * ) (alpha{2}^7)  _.
            pose a6 := FieldR.( * ) (FieldR.( * ) (FieldR.( * ) (alpha{2}^6)  _) _) _.
            have ->: alpha{2} ^ 6 *
              (s_at_z_omega{2} * beta'{2} + gamma'{2} * (FieldR.one + beta'{2})) *
              (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) *
              z_lookup_at_z_omega{2} = a6 by
                pose x1 := alpha{2}^6 * (s_at_z_omega{2} * beta'{2} + gamma'{2} * (FieldR.one + beta'{2}));
                pose x2 := (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1));
                rewrite -FieldR.ComRing.mulrA;
                rewrite (FieldR.ZrRing.mulrC x2);
                rewrite FieldR.ComRing.mulrA;
                progress.
            pose a5 := FieldR.( * ) (alpha{2}^5)  _.
            pose a4 := FieldR.( * ) (FieldR.( * ) (FieldR.( * ) (FieldR.( * ) (FieldR.( * ) (alpha{2}^4)  _) _) _) _) _.
            pose y1 := quotient_poly_opening_at_z{2} * (z{2} ^ Constants.DOMAIN_SIZE + -FieldR.one).
            pose y2 := FieldR.( + ) _ _.
            case (y1 = y2); by progress.

      (* verify quotient evaluation done *)

      (* prepare queries *)
      seq 1 4: (
        (failed{1} /\ !isValid{2}) \/ (
        !failed{1} /\ isValid{2} /\
        !vk_recursive_flag{1} /\
        _public_input{1} = public_input{2} /\
        _state_poly_0{1} = a{2} /\
        _state_poly_1{1} = b{2} /\
        _state_poly_2{1} = c{2} /\
        _state_poly_3{1} = d{2} /\
        _copy_permutation_grand_product{1} = z_perm{2} /\
        _lookup_s_poly{1} = s{2} /\
        _lookup_grand_product{1} = z_lookup{2} /\
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
        _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
        _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
        _opening_proof_at_z{1} = w{2} /\
        _opening_proof_at_z_omega{1} = w'{2} /\
        _recursive_part_p1{1} = None /\
        _recursive_part_p2{1} = None /\
        k0{2} = FieldR.inF Constants.NON_RESIDUE_0 /\
        k1{2} = FieldR.inF Constants.NON_RESIDUE_1 /\ 
        k2{2} = FieldR.inF Constants.NON_RESIDUE_2 /\
        n{2} = Constants.DOMAIN_SIZE /\
        q_a{2} = vk_gate_setup_0 /\
        q_b{2} = vk_gate_setup_1 /\
        q_c{2} = vk_gate_setup_2 /\
        q_d{2} = vk_gate_setup_3 /\
        q_ab{2} = vk_gate_setup_4 /\
        q_ac{2} = vk_gate_setup_5 /\
        q_const{2} = vk_gate_setup_6 /\
        q_d_next{2} = vk_gate_setup_7 /\
        custom_gate_selector{2} = vk_gate_selectors_1 /\
        sigma_0{2} = vk_permutation_0 /\
        sigma_1{2} = vk_permutation_1 /\
        sigma_2{2} = vk_permutation_2 /\ 
        sigma_3{2} = vk_permutation_3 /\
        lookup_selector{2} = vk_lookup_selector /\
        table_type{2} = vk_lookup_table_type /\
        omega{2} = Constants.OMEGAFr /\
        col_0{2} = vk_lookup_table_0 /\
        col_1{2} = vk_lookup_table_1 /\
        col_2{2} = vk_lookup_table_2 /\
        col_3{2} = vk_lookup_table_3 /\
        state_alpha{1} = alpha{2} /\
        state_beta{1} = beta_{2} /\
        state_beta_lookup{1} = beta'{2} /\
        state_gamma{1} = gamma{2} /\
        state_gamma_lookup{1} = gamma'{2} /\
        state_eta{1} = eta_{2} /\
        state_z{1} = z{2} /\
        state_z_in_domain{1} = z{2} ^ n{2} /\
        state_v{1} = v{2} /\
        state_u{1} = u{2} /\
        alpha2{1} = alpha{2}^2 /\
        alpha3{1} = alpha{2}^3 /\
        alpha4{1} = alpha{2}^4 /\
        alpha5{1} = alpha{2}^5 /\
        alpha6{1} = alpha{2}^6 /\
        alpha7{1} = alpha{2}^7 /\
        alpha8{1} = alpha{2}^8 /\
        l0_at_z{1} = l_0_at_z{2} /\
        ln_minus_one_at_z{1} = l_n_minus_one_at_z{2} /\
        beta_plus_one{1} = FieldR.one + beta'{2} /\
        beta_gamma_plus_gamma{1} = gamma'{2} * (FieldR.one + beta'{2}) /\
        z_minus_last_omega{1} = z{2} - omega{2}^(n{2} - 1) /\
        query_at_z_0{1} = d0{2} /\
        query_at_z_1{1} = v{2} * (
          main_gate_selector_at_z{2} * (
            (a_at_z{2} * q_a{2}) +
            (b_at_z{2} * q_b{2}) +
            (c_at_z{2} * q_c{2}) +
            (d_at_z{2} * q_d{2}) +
            (a_at_z{2} * b_at_z{2} * q_ab{2}) +
            (a_at_z{2} * c_at_z{2} * q_ac{2}) +
            q_const{2} +
            (d_at_z_omega{2} * q_d_next{2})
          ) + 
          alpha{2} * (
            (
              (a_at_z{2}^2 - b_at_z{2}) +
              (b_at_z{2}^2 - c_at_z{2}) * alpha{2} +
              (a_at_z{2} * c_at_z{2} - d_at_z{2}) * alpha{2}^2
            )
          )* custom_gate_selector{2} +
          G.inv (alpha{2}^4 * z_perm_at_z_omega{2} * beta_{2} *
            (sigma_0_at_z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
            (sigma_1_at_z{2} * beta_{2} + gamma{2} + b_at_z{2}) *
            (sigma_2_at_z{2} * beta_{2} + gamma{2} + c_at_z{2}) *
            sigma_3{2})
          ) /\
        copy_permutation_first_aggregated_commitment_coeff{1} = (                                
          alpha{2}^4 * (z{2} * beta_{2} + gamma{2} + a_at_z{2}) *                               
          (z{2} * beta_{2} * k0{2} + gamma{2} + b_at_z{2}) * 
          (z{2} * beta_{2} * k1{2} + gamma{2} + c_at_z{2}) * 
          (z{2} * beta_{2} * k2{2} + gamma{2} + d_at_z{2}) + 
          l_0_at_z{2} * alpha{2}^5
        ) * v{2} /\
        lookupSFirstAggregatedCommitment{1} = v{2} * alpha{2}^6 * z_lookup_at_z_omega{2} * (z{2} - omega{2}^(n{2}-1)) /\
        lookupGrandProductFirstAggregatedCoefficient{1} = ((
          - alpha{2}^6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z{2}) * (z{2} - omega{2}^(n{2}-1)) * (
            gamma'{2}*(FieldR.one + beta'{2}) + t_at_z{2} + beta'{2} * t_at_z_omega{2}
          )) +
          alpha{2}^7 * l_0_at_z{2} +
          alpha{2}^8 * l_n_minus_one_at_z{2}) * v{2} /\
        query_t_poly_aggregated{1} = t{2} /\
        d1{2} = main_gate_selector_at_z{2} * (
            (a_at_z{2} * q_a{2}) +
            (b_at_z{2} * q_b{2}) +
            (c_at_z{2} * q_c{2}) +
            (d_at_z{2} * q_d{2}) +
            (a_at_z{2} * b_at_z{2} * q_ab{2}) +
            (a_at_z{2} * c_at_z{2} * q_ac{2}) +
            q_const{2} +
            (d_at_z_omega{2} * q_d_next{2})
        ) 
        + alpha{2} * (
          (
            (a_at_z{2}^2 - b_at_z{2}) +
            (b_at_z{2}^2 - c_at_z{2}) * alpha{2} +
            (a_at_z{2} * c_at_z{2} - d_at_z{2}) * alpha{2}^2
          )
        )* custom_gate_selector{2}
        + alpha{2}^4 *
          (a_at_z{2} + beta_{2} * z{2}         + gamma{2}) *                               
          (b_at_z{2} + beta_{2} * z{2} * k0{2} + gamma{2}) * 
          (c_at_z{2} + beta_{2} * z{2} * k1{2} + gamma{2}) * 
          (d_at_z{2} + beta_{2} * z{2} * k2{2} + gamma{2}) * z_perm{2}
        + G.inv (alpha{2}^4 * z_perm_at_z_omega{2} * beta_{2} *
          (a_at_z{2} + beta_{2} * sigma_0_at_z{2} + gamma{2}) *
          (b_at_z{2} + beta_{2} * sigma_1_at_z{2} + gamma{2}) *
          (c_at_z{2} + beta_{2} * sigma_2_at_z{2} + gamma{2}) *
          sigma_3{2})
        + alpha{2}^5 * l_0_at_z{2} * z_perm{2}
        + G.inv (alpha{2}^6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z{2}) * (z{2} - omega{2}^(n{2}-1)) *
          (gamma'{2}*(FieldR.one + beta'{2}) + t_at_z{2} + beta'{2} * t_at_z_omega{2}) * z_lookup{2}
        ) 
          + alpha{2}^6 * z_lookup_at_z_omega{2} * (z{2} - omega{2}^(n{2}-1)) * s{2}
          + alpha{2}^7 * l_0_at_z{2} * z_lookup{2}
          + alpha{2}^8 * l_n_minus_one_at_z{2} * z_lookup{2}  /\
        f_at_z{2} = lookup_selector_at_z{2} * (a_at_z{2} + eta_{2} * b_at_z{2} + eta_{2}^2 * c_at_z{2} + eta_{2}^3 * table_type_at_z{2})
      )).
        case (failed{1}).
        conseq (_: (failed{1} /\ !isValid{2}) ==> (failed{1} /\ !isValid{2})).
          progress. by case H; progress.
          progress. left. by progress.
          inline PrepareQueries.high.
          wp. skip. by progress.

        (* case failed{1} *)
          transitivity{1} 
            { (query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated) <@ PrepareQueries.super_high(
              state_alpha,
              state_beta,
              state_gamma,
              state_v,
              state_z,
              Constants.DOMAIN_SIZE,
              _quotient_poly_part_0,
              _quotient_poly_part_1,
              _quotient_poly_part_2,
              _quotient_poly_part_3,
              _gate_selector_0_opening_at_z,
              _state_poly_0_opening_at_z,
              _state_poly_1_opening_at_z,
              _state_poly_2_opening_at_z,
              _state_poly_3_opening_at_z,
              vk_gate_setup_0,
              vk_gate_setup_1,
              vk_gate_setup_2,
              vk_gate_setup_3,
              vk_gate_setup_4,
              vk_gate_setup_5,
              vk_gate_setup_6,
              vk_gate_setup_7,
              _state_poly_3_opening_at_z_omega,
              vk_gate_selectors_1,
              _copy_permutation_grand_product_opening_at_z_omega,
              _copy_permutation_poly_0_opening_at_z,
              _copy_permutation_poly_1_opening_at_z,
              _copy_permutation_poly_2_opening_at_z,
              vk_permutation_3,
              FieldR.inF Constants.NON_RESIDUE_0,
              FieldR.inF Constants.NON_RESIDUE_1,
              FieldR.inF Constants.NON_RESIDUE_2,
              l0_at_z,
              Constants.OMEGAFr, 
              _lookup_grand_product_opening_at_z_omega,
              vk_lookup_table_0,
              vk_lookup_table_1,
              vk_lookup_table_2,
              vk_lookup_table_3,
              state_eta,
              _lookup_selector_poly_opening_at_z,
              _lookup_table_type_poly_opening_at_z,
              state_beta_lookup,
              state_gamma_lookup,
              _lookup_t_poly_opening_at_z,
              _lookup_t_poly_opening_at_z_omega,
              ln_minus_one_at_z
            );} (
              ={failed, _public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, vk_recursive_flag ,_copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_t_poly_opening_at_z_omega, _lookup_selector_poly_opening_at_z, _lookup_table_type_poly_opening_at_z, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega, _recursive_part_p1, _recursive_part_p2, state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_eta, state_z, state_z_in_domain, state_v, state_u, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega} /\
              alpha2{1} = state_alpha{2}^2 /\
              alpha3{1} = state_alpha{2}^3 /\
              alpha4{1} = state_alpha{2}^4 /\
              alpha5{1} = state_alpha{2}^5 /\
              alpha6{1} = state_alpha{2}^6 /\
              alpha7{1} = state_alpha{2}^7 /\
              alpha8{1} = state_alpha{2}^8 /\ 
              state_z_in_domain{1} = state_z{2} ^ Constants.DOMAIN_SIZE /\
              z_minus_last_omega{1} = (state_z{2} - Constants.OMEGAFr^(Constants.DOMAIN_SIZE-1)) /\
              beta_gamma_plus_gamma{1} = state_gamma_lookup{2}*(FieldR.one + state_beta_lookup{2}) /\
              beta_plus_one{1} = (FieldR.one + state_beta_lookup{2})
                 ==>
              ={query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated, failed, _public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, vk_recursive_flag ,_copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_t_poly_opening_at_z_omega, _lookup_selector_poly_opening_at_z, _lookup_table_type_poly_opening_at_z, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, _opening_proof_at_z, _opening_proof_at_z_omega, _recursive_part_p1, _recursive_part_p2, state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_eta, state_z, state_z_in_domain, state_v, state_u, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega}
            ) (
              !failed{1} /\
              isValid{2} /\
              !vk_recursive_flag{1} /\
              _public_input{1} = public_input{2} /\
              _state_poly_0{1} = a{2} /\
              _state_poly_1{1} = b{2} /\
              _state_poly_2{1} = c{2} /\
              _state_poly_3{1} = d{2} /\
              _copy_permutation_grand_product{1} = z_perm{2} /\
              _lookup_s_poly{1} = s{2} /\
              _lookup_grand_product{1} = z_lookup{2} /\
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
              _copy_permutation_grand_product_opening_at_z_omega{1} =
              z_perm_at_z_omega{2} /\
              _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
              _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
              _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
              _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
              _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
              _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
              _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
              _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
              _opening_proof_at_z{1} = w{2} /\
              _opening_proof_at_z_omega{1} = w'{2} /\
              _recursive_part_p1{1} = None /\
              _recursive_part_p2{1} = None /\
              k0{2} = (FieldR.inF Constants.NON_RESIDUE_0) /\
              k1{2} = (FieldR.inF Constants.NON_RESIDUE_1) /\
              k2{2} = (FieldR.inF Constants.NON_RESIDUE_2) /\
              n{2} = Constants.DOMAIN_SIZE /\
              q_a{2} = vk_gate_setup_0 /\
              q_b{2} = vk_gate_setup_1 /\
              q_c{2} = vk_gate_setup_2 /\
              q_d{2} = vk_gate_setup_3 /\
              q_ab{2} = vk_gate_setup_4 /\
              q_ac{2} = vk_gate_setup_5 /\
              q_const{2} = vk_gate_setup_6 /\
              q_d_next{2} = vk_gate_setup_7 /\
              custom_gate_selector{2} = vk_gate_selectors_1 /\
              sigma_0{2} = vk_permutation_0 /\
              sigma_1{2} = vk_permutation_1 /\
              sigma_2{2} = vk_permutation_2 /\
              sigma_3{2} = vk_permutation_3 /\
              lookup_selector{2} = vk_lookup_selector /\
              table_type{2} = vk_lookup_table_type /\
              omega{2} = Constants.OMEGAFr /\
              col_0{2} = vk_lookup_table_0 /\
              col_1{2} = vk_lookup_table_1 /\
              col_2{2} = vk_lookup_table_2 /\
              col_3{2} = vk_lookup_table_3 /\
              state_alpha{1} = alpha{2} /\
              state_beta{1} = beta_{2} /\
              state_beta_lookup{1} = beta'{2} /\
              state_gamma{1} = gamma{2} /\
              state_gamma_lookup{1} = gamma'{2} /\
              state_eta{1} = eta_{2} /\
              state_z{1} = z{2} /\
              state_z_in_domain{1} = z{2} ^ n{2} /\
              state_v{1} = v{2} /\
              state_u{1} = u{2} /\
              alpha2{1} = alpha{2} ^ 2 /\
              alpha3{1} = alpha{2} ^ 3 /\
              alpha4{1} = alpha{2} ^ 4 /\
              alpha5{1} = alpha{2} ^ 5 /\
              alpha6{1} = alpha{2} ^ 6 /\
              alpha7{1} = alpha{2} ^ 7 /\
              alpha8{1} = alpha{2} ^ 8 /\
              l0_at_z{1} = l_0_at_z{2} /\
              ln_minus_one_at_z{1} = l_n_minus_one_at_z{2} /\
              beta_plus_one{1} = FieldR.one + beta'{2} /\
              beta_gamma_plus_gamma{1} = gamma'{2} * (FieldR.one + beta'{2}) /\
              z_minus_last_omega{1} = z{2} - omega{2} ^ (n{2} - 1)
                ==>
              !failed{1} /\ isValid{2} /\
              !vk_recursive_flag{1} /\
              _public_input{1} = public_input{2} /\
              _state_poly_0{1} = a{2} /\
              _state_poly_1{1} = b{2} /\
              _state_poly_2{1} = c{2} /\
              _state_poly_3{1} = d{2} /\
              _copy_permutation_grand_product{1} = z_perm{2} /\
              _lookup_s_poly{1} = s{2} /\
              _lookup_grand_product{1} = z_lookup{2} /\
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
              _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
              _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
              _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
              _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
              _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
              _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
              _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
              _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
              _opening_proof_at_z{1} = w{2} /\
              _opening_proof_at_z_omega{1} = w'{2} /\
              _recursive_part_p1{1} = None /\
              _recursive_part_p2{1} = None /\
              k0{2} = FieldR.inF Constants.NON_RESIDUE_0 /\
              k1{2} = FieldR.inF Constants.NON_RESIDUE_1 /\ 
              k2{2} = FieldR.inF Constants.NON_RESIDUE_2 /\
              n{2} = Constants.DOMAIN_SIZE /\
              q_a{2} = vk_gate_setup_0 /\
              q_b{2} = vk_gate_setup_1 /\
              q_c{2} = vk_gate_setup_2 /\
              q_d{2} = vk_gate_setup_3 /\
              q_ab{2} = vk_gate_setup_4 /\
              q_ac{2} = vk_gate_setup_5 /\
              q_const{2} = vk_gate_setup_6 /\
              q_d_next{2} = vk_gate_setup_7 /\
              custom_gate_selector{2} = vk_gate_selectors_1 /\
              sigma_0{2} = vk_permutation_0 /\
              sigma_1{2} = vk_permutation_1 /\
              sigma_2{2} = vk_permutation_2 /\ 
              sigma_3{2} = vk_permutation_3 /\
              lookup_selector{2} = vk_lookup_selector /\
              table_type{2} = vk_lookup_table_type /\
              omega{2} = Constants.OMEGAFr /\
              col_0{2} = vk_lookup_table_0 /\
              col_1{2} = vk_lookup_table_1 /\
              col_2{2} = vk_lookup_table_2 /\
              col_3{2} = vk_lookup_table_3 /\
              state_alpha{1} = alpha{2} /\
              state_beta{1} = beta_{2} /\
              state_beta_lookup{1} = beta'{2} /\
              state_gamma{1} = gamma{2} /\
              state_gamma_lookup{1} = gamma'{2} /\
              state_eta{1} = eta_{2} /\
              state_z{1} = z{2} /\
              state_z_in_domain{1} = z{2} ^ n{2} /\
              state_v{1} = v{2} /\
              state_u{1} = u{2} /\
              alpha2{1} = alpha{2}^2 /\
              alpha3{1} = alpha{2}^3 /\
              alpha4{1} = alpha{2}^4 /\
              alpha5{1} = alpha{2}^5 /\
              alpha6{1} = alpha{2}^6 /\
              alpha7{1} = alpha{2}^7 /\
              alpha8{1} = alpha{2}^8 /\
              l0_at_z{1} = l_0_at_z{2} /\
              ln_minus_one_at_z{1} = l_n_minus_one_at_z{2} /\
              beta_plus_one{1} = FieldR.one + beta'{2} /\
              beta_gamma_plus_gamma{1} = gamma'{2} * (FieldR.one + beta'{2}) /\
              z_minus_last_omega{1} = z{2} - omega{2}^(n{2} - 1) /\
              query_at_z_0{1} = d0{2} /\
              query_at_z_1{1} = v{2} * (
                main_gate_selector_at_z{2} * (
                  (a_at_z{2} * q_a{2}) +
                  (b_at_z{2} * q_b{2}) +
                  (c_at_z{2} * q_c{2}) +
                  (d_at_z{2} * q_d{2}) +
                  (a_at_z{2} * b_at_z{2} * q_ab{2}) +
                  (a_at_z{2} * c_at_z{2} * q_ac{2}) +
                  q_const{2} +
                  (d_at_z_omega{2} * q_d_next{2})
                ) + 
                alpha{2} * (
                  (
                    (a_at_z{2}^2 - b_at_z{2}) +
                    (b_at_z{2}^2 - c_at_z{2}) * alpha{2} +
                    (a_at_z{2} * c_at_z{2} - d_at_z{2}) * alpha{2}^2
                  )
                )* custom_gate_selector{2} +
                G.inv (alpha{2}^4 * z_perm_at_z_omega{2} * beta_{2} *
                  (sigma_0_at_z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
                  (sigma_1_at_z{2} * beta_{2} + gamma{2} + b_at_z{2}) *
                  (sigma_2_at_z{2} * beta_{2} + gamma{2} + c_at_z{2}) *
                  sigma_3{2})
                ) /\
              copy_permutation_first_aggregated_commitment_coeff{1} = (                                
                alpha{2}^4 * (z{2} * beta_{2} + gamma{2} + a_at_z{2}) *                               
                (z{2} * beta_{2} * k0{2} + gamma{2} + b_at_z{2}) * 
                (z{2} * beta_{2} * k1{2} + gamma{2} + c_at_z{2}) * 
                (z{2} * beta_{2} * k2{2} + gamma{2} + d_at_z{2}) + 
                l_0_at_z{2} * alpha{2}^5
              ) * v{2} /\
              lookupSFirstAggregatedCommitment{1} = v{2} * alpha{2}^6 * z_lookup_at_z_omega{2} * (z{2} - omega{2}^(n{2}-1)) /\
              lookupGrandProductFirstAggregatedCoefficient{1} = ((
                - alpha{2}^6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z{2}) * (z{2} - omega{2}^(n{2}-1)) * (
                  gamma'{2}*(FieldR.one + beta'{2}) + t_at_z{2} + beta'{2} * t_at_z_omega{2}
                )) +
                alpha{2}^7 * l_0_at_z{2} +
                alpha{2}^8 * l_n_minus_one_at_z{2}) * v{2} /\
              query_t_poly_aggregated{1} = t{2} /\
              d1{2} = main_gate_selector_at_z{2} * (
                  (a_at_z{2} * q_a{2}) +
                  (b_at_z{2} * q_b{2}) +
                  (c_at_z{2} * q_c{2}) +
                  (d_at_z{2} * q_d{2}) +
                  (a_at_z{2} * b_at_z{2} * q_ab{2}) +
                  (a_at_z{2} * c_at_z{2} * q_ac{2}) +
                  q_const{2} +
                  (d_at_z_omega{2} * q_d_next{2})
              ) 
              + alpha{2} * (
                (
                  (a_at_z{2}^2 - b_at_z{2}) +
                  (b_at_z{2}^2 - c_at_z{2}) * alpha{2} +
                  (a_at_z{2} * c_at_z{2} - d_at_z{2}) * alpha{2}^2
                )
              )* custom_gate_selector{2}
              + alpha{2}^4 *
                (a_at_z{2} + beta_{2} * z{2}         + gamma{2}) *                               
                (b_at_z{2} + beta_{2} * z{2} * k0{2} + gamma{2}) * 
                (c_at_z{2} + beta_{2} * z{2} * k1{2} + gamma{2}) * 
                (d_at_z{2} + beta_{2} * z{2} * k2{2} + gamma{2}) * z_perm{2}
              + G.inv (alpha{2}^4 * z_perm_at_z_omega{2} * beta_{2} *
                (a_at_z{2} + beta_{2} * sigma_0_at_z{2} + gamma{2}) *
                (b_at_z{2} + beta_{2} * sigma_1_at_z{2} + gamma{2}) *
                (c_at_z{2} + beta_{2} * sigma_2_at_z{2} + gamma{2}) *
                sigma_3{2})
              + alpha{2}^5 * l_0_at_z{2} * z_perm{2}
              + G.inv (alpha{2}^6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z{2}) * (z{2} - omega{2}^(n{2}-1)) *
                (gamma'{2}*(FieldR.one + beta'{2}) + t_at_z{2} + beta'{2} * t_at_z_omega{2}) * z_lookup{2}
              ) 
                + alpha{2}^6 * z_lookup_at_z_omega{2} * (z{2} - omega{2}^(n{2}-1)) * s{2}
                + alpha{2}^7 * l_0_at_z{2} * z_lookup{2}
                + alpha{2}^8 * l_n_minus_one_at_z{2} * z_lookup{2}  /\
              f_at_z{2} = lookup_selector_at_z{2} * (a_at_z{2} + eta_{2} * b_at_z{2} + eta_{2}^2 * c_at_z{2} + eta_{2}^3 * table_type_at_z{2})
            ).
              progress.
                exists _copy_permutation_grand_product{1}.
                exists _copy_permutation_grand_product_opening_at_z_omega{1}.
                exists _copy_permutation_poly_0_opening_at_z{1}.
                exists _copy_permutation_poly_1_opening_at_z{1}.
                exists _copy_permutation_poly_2_opening_at_z{1}.
                exists _gate_selector_0_opening_at_z{1}.
                exists _linearisation_poly_opening_at_z{1}.
                exists _lookup_grand_product{1}.
                exists _lookup_grand_product_opening_at_z_omega{1}.
                exists _lookup_s_poly{1}.
                exists _lookup_s_poly_opening_at_z_omega{1}.
                exists _lookup_selector_poly_opening_at_z{1}.
                exists _lookup_t_poly_opening_at_z{1}.
                exists _lookup_t_poly_opening_at_z_omega{1}.
                exists _lookup_table_type_poly_opening_at_z{1}.
                exists _opening_proof_at_z{1}.
                exists _opening_proof_at_z_omega{1}.
                exists _public_input{1}.
                exists _quotient_poly_opening_at_z{1}.
                exists _quotient_poly_part_0{1}.
                exists _quotient_poly_part_1{1}.
                exists _quotient_poly_part_2{1}.
                exists _quotient_poly_part_3{1}.
                exists _recursive_part_p1{1}.
                exists _recursive_part_p2{1}.
                exists _state_poly_0{1}.
                exists _state_poly_0_opening_at_z{1}.
                exists _state_poly_1{1}.
                exists _state_poly_1_opening_at_z{1}.
                exists _state_poly_2{1}.
                exists _state_poly_2_opening_at_z{1}.
                exists _state_poly_3{1}.
                exists _state_poly_3_opening_at_z{1}.
                exists _state_poly_3_opening_at_z_omega{1}.
                exists alpha2{1}.
                exists alpha3{1}.
                exists alpha4{1}.
                exists alpha5{1}.
                exists alpha6{1}.
                exists alpha7{1}.
                exists alpha8{1}.
                exists beta_gamma_plus_gamma{1}.
                exists beta_plus_one{1}.
                exists failed{1}.
                exists l0_at_z{1}.
                exists ln_minus_one_at_z{1}.
                exists state_alpha{1}.
                exists state_beta{1}.
                exists state_beta_lookup{1}.
                exists state_eta{1}.
                exists state_gamma{1}.
                exists state_gamma_lookup{1}.
                exists state_u{1}.
                exists state_v{1}.
                exists state_z{1}.
                exists state_z_in_domain{1}.
                exists vk_recursive_flag{1}.
                exists z_minus_last_omega{1}.
                by progress; case H; progress.
                
                progress. right.
                  rewrite H H0 H1.
                  progress.
                call prepareQueries_high_equiv_super_high. skip. progress.
                  by rewrite /Constants.DOMAIN_SIZE; trivial.
             
                inline PrepareQueries.super_high.
                wp. skip. progress.
                rewrite FieldR.ComRing.mulrA. congr.
                exact FieldR.ComRing.mulrA.
      (* prepare queries done *)

      (* prepare aggregated commitment *)
      seq 1 5: (
        (failed{1} /\ !isValid{2}) \/ (
        !failed{1} /\ isValid{2} /\
        !vk_recursive_flag{1} /\
        _public_input{1} = public_input{2} /\
        _state_poly_0{1} = a{2} /\
        _state_poly_1{1} = b{2} /\
        _state_poly_2{1} = c{2} /\
        _state_poly_3{1} = d{2} /\
        _copy_permutation_grand_product{1} = z_perm{2} /\
        _lookup_s_poly{1} = s{2} /\
        _lookup_grand_product{1} = z_lookup{2} /\
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
        _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
        _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
        _opening_proof_at_z{1} = w{2} /\
        _opening_proof_at_z_omega{1} = w'{2} /\
        _recursive_part_p1{1} = None /\
        _recursive_part_p2{1} = None /\
        k0{2} = FieldR.inF Constants.NON_RESIDUE_0 /\
        k1{2} = FieldR.inF Constants.NON_RESIDUE_1 /\ 
        k2{2} = FieldR.inF Constants.NON_RESIDUE_2 /\
        n{2} = Constants.DOMAIN_SIZE /\
        q_a{2} = vk_gate_setup_0 /\
        q_b{2} = vk_gate_setup_1 /\
        q_c{2} = vk_gate_setup_2 /\
        q_d{2} = vk_gate_setup_3 /\
        q_ab{2} = vk_gate_setup_4 /\
        q_ac{2} = vk_gate_setup_5 /\
        q_const{2} = vk_gate_setup_6 /\
        q_d_next{2} = vk_gate_setup_7 /\
        custom_gate_selector{2} = vk_gate_selectors_1 /\
        sigma_0{2} = vk_permutation_0 /\
        sigma_1{2} = vk_permutation_1 /\
        sigma_2{2} = vk_permutation_2 /\ 
        sigma_3{2} = vk_permutation_3 /\
        lookup_selector{2} = vk_lookup_selector /\
        table_type{2} = vk_lookup_table_type /\
        omega{2} = Constants.OMEGAFr /\
        col_0{2} = vk_lookup_table_0 /\
        col_1{2} = vk_lookup_table_1 /\
        col_2{2} = vk_lookup_table_2 /\
        col_3{2} = vk_lookup_table_3 /\
        state_alpha{1} = alpha{2} /\
        state_beta{1} = beta_{2} /\
        state_beta_lookup{1} = beta'{2} /\
        state_gamma{1} = gamma{2} /\
        state_gamma_lookup{1} = gamma'{2} /\
        state_eta{1} = eta_{2} /\
        state_z{1} = z{2} /\
        state_z_in_domain{1} = z{2} ^ n{2} /\
        state_v{1} = v{2} /\
        state_u{1} = u{2} /\
        alpha2{1} = alpha{2}^2 /\
        alpha3{1} = alpha{2}^3 /\
        alpha4{1} = alpha{2}^4 /\
        alpha5{1} = alpha{2}^5 /\
        alpha6{1} = alpha{2}^6 /\
        alpha7{1} = alpha{2}^7 /\
        alpha8{1} = alpha{2}^8 /\
        l0_at_z{1} = l_0_at_z{2} /\
        ln_minus_one_at_z{1} = l_n_minus_one_at_z{2} /\
        beta_plus_one{1} = FieldR.one + beta'{2} /\
        beta_gamma_plus_gamma{1} = gamma'{2} * (FieldR.one + beta'{2}) /\
        z_minus_last_omega{1} = z{2} - omega{2}^(n{2} - 1) /\
        query_at_z_0{1} = d0{2} /\
        query_at_z_1{1} = v{2} * (
          main_gate_selector_at_z{2} * (
            (a_at_z{2} * q_a{2}) +
            (b_at_z{2} * q_b{2}) +
            (c_at_z{2} * q_c{2}) +
            (d_at_z{2} * q_d{2}) +
            (a_at_z{2} * b_at_z{2} * q_ab{2}) +
            (a_at_z{2} * c_at_z{2} * q_ac{2}) +
            q_const{2} +
            (d_at_z_omega{2} * q_d_next{2})
          ) + 
          alpha{2} * (
            (
              (a_at_z{2}^2 - b_at_z{2}) +
              (b_at_z{2}^2 - c_at_z{2}) * alpha{2} +
              (a_at_z{2} * c_at_z{2} - d_at_z{2}) * alpha{2}^2
            )
          )* custom_gate_selector{2} +
          G.inv (alpha{2}^4 * z_perm_at_z_omega{2} * beta_{2} *
            (sigma_0_at_z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
            (sigma_1_at_z{2} * beta_{2} + gamma{2} + b_at_z{2}) *
            (sigma_2_at_z{2} * beta_{2} + gamma{2} + c_at_z{2}) *
            sigma_3{2})
          ) /\
        copy_permutation_first_aggregated_commitment_coeff{1} = (                                
          alpha{2}^4 * (z{2} * beta_{2} + gamma{2} + a_at_z{2}) *                               
          (z{2} * beta_{2} * k0{2} + gamma{2} + b_at_z{2}) * 
          (z{2} * beta_{2} * k1{2} + gamma{2} + c_at_z{2}) * 
          (z{2} * beta_{2} * k2{2} + gamma{2} + d_at_z{2}) + 
          l_0_at_z{2} * alpha{2}^5
        ) * v{2} /\
        lookupSFirstAggregatedCommitment{1} = v{2} * alpha{2}^6 * z_lookup_at_z_omega{2} * (z{2} - omega{2}^(n{2}-1)) /\
        lookupGrandProductFirstAggregatedCoefficient{1} = ((
          - alpha{2}^6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z{2}) * (z{2} - omega{2}^(n{2}-1)) * (
            gamma'{2}*(FieldR.one + beta'{2}) + t_at_z{2} + beta'{2} * t_at_z_omega{2}
          )) +
          alpha{2}^7 * l_0_at_z{2} +
          alpha{2}^8 * l_n_minus_one_at_z{2}) * v{2} /\
        query_t_poly_aggregated{1} = t{2} /\
        d1{2} = main_gate_selector_at_z{2} * (
            (a_at_z{2} * q_a{2}) +
            (b_at_z{2} * q_b{2}) +
            (c_at_z{2} * q_c{2}) +
            (d_at_z{2} * q_d{2}) +
            (a_at_z{2} * b_at_z{2} * q_ab{2}) +
            (a_at_z{2} * c_at_z{2} * q_ac{2}) +
            q_const{2} +
            (d_at_z_omega{2} * q_d_next{2})
        ) 
        + alpha{2} * (
          (
            (a_at_z{2}^2 - b_at_z{2}) +
            (b_at_z{2}^2 - c_at_z{2}) * alpha{2} +
            (a_at_z{2} * c_at_z{2} - d_at_z{2}) * alpha{2}^2
          )
        )* custom_gate_selector{2}
        + alpha{2}^4 *
          (a_at_z{2} + beta_{2} * z{2}         + gamma{2}) *                               
          (b_at_z{2} + beta_{2} * z{2} * k0{2} + gamma{2}) * 
          (c_at_z{2} + beta_{2} * z{2} * k1{2} + gamma{2}) * 
          (d_at_z{2} + beta_{2} * z{2} * k2{2} + gamma{2}) * z_perm{2}
        + G.inv (alpha{2}^4 * z_perm_at_z_omega{2} * beta_{2} *
          (a_at_z{2} + beta_{2} * sigma_0_at_z{2} + gamma{2}) *
          (b_at_z{2} + beta_{2} * sigma_1_at_z{2} + gamma{2}) *
          (c_at_z{2} + beta_{2} * sigma_2_at_z{2} + gamma{2}) *
          sigma_3{2})
        + alpha{2}^5 * l_0_at_z{2} * z_perm{2}
        + G.inv (alpha{2}^6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z{2}) * (z{2} - omega{2}^(n{2}-1)) *
          (gamma'{2}*(FieldR.one + beta'{2}) + t_at_z{2} + beta'{2} * t_at_z_omega{2}) * z_lookup{2}
        ) 
          + alpha{2}^6 * z_lookup_at_z_omega{2} * (z{2} - omega{2}^(n{2}-1)) * s{2}
          + alpha{2}^7 * l_0_at_z{2} * z_lookup{2}
          + alpha{2}^8 * l_n_minus_one_at_z{2} * z_lookup{2}  /\
        f_at_z{2} = lookup_selector_at_z{2} * (a_at_z{2} + eta_{2} * b_at_z{2} + eta_{2}^2 * c_at_z{2} + eta_{2}^3 * table_type_at_z{2}) /\
        aggregatedAtZSlot{1} = d0{2} +
          v{2} *
          (main_gate_selector_at_z{2} *
           (a_at_z{2} * vk_gate_setup_0 + b_at_z{2} * vk_gate_setup_1 +
            c_at_z{2} * vk_gate_setup_2 + d_at_z{2} * vk_gate_setup_3 +
            a_at_z{2} * b_at_z{2} * vk_gate_setup_4 +
            a_at_z{2} * c_at_z{2} * vk_gate_setup_5 + vk_gate_setup_6 +
            d_at_z_omega{2} * vk_gate_setup_7) +
           alpha{2} *
           (a_at_z{2} ^ 2 + -b_at_z{2} + (b_at_z{2} ^ 2 + -c_at_z{2}) * alpha{2} +
            (a_at_z{2} * c_at_z{2} + -d_at_z{2}) * alpha{2} ^ 2) *
           vk_gate_selectors_1 +
           (G.inv
              (alpha{2} ^ 4 * z_perm_at_z_omega{2} * beta_{2} *
               (sigma_0_at_z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
               (sigma_1_at_z{2} * beta_{2} + gamma{2} + b_at_z{2}) *
               (sigma_2_at_z{2} * beta_{2} + gamma{2} + c_at_z{2}) * vk_permutation_3))) +
          v{2} ^ 2 * a{2} + v{2} ^ 3 * b{2} + v{2} ^ 4 * c{2} +
          v{2} ^ 6 * vk_gate_selectors_0 + v{2} ^ 7 * vk_permutation_0 +
          v{2} ^ 8 * vk_permutation_1 + v{2} ^ 9 * vk_permutation_2 +
          v{2} ^ 11 * vk_lookup_selector + v{2} ^ 12 * vk_lookup_table_type /\
        aggregatedOpeningAtZSlot{1} = quotient_poly_opening_at_z{2} + v{2} * r_at_z{2} + v{2} ^ 2 * a_at_z{2} +
          v{2} ^ 3 * b_at_z{2} + v{2} ^ 4 * c_at_z{2} + v{2} ^ 5 * d_at_z{2} +
          v{2} ^ 6 * main_gate_selector_at_z{2} + v{2} ^ 7 * sigma_0_at_z{2} +
          v{2} ^ 8 * sigma_1_at_z{2} + v{2} ^ 9 * sigma_2_at_z{2} +
          v{2} ^ 10 * t_at_z{2} + v{2} ^ 11 * lookup_selector_at_z{2} +
          v{2} ^ 12 * table_type_at_z{2} /\
        aggregatedAtZOmegaSlot{1} = v{2} ^ 5 * d{2} + v{2} ^ 10 * t{2} +
          u{2} *
          (v{2} ^ 13 * z_perm{2} + v{2} ^ 14 * d{2} + v{2} ^ 15 * s{2} +
           v{2} ^ 16 * z_lookup{2} + v{2} ^ 17 * t{2}) +
          ((- alpha{2} ^ 6 * (FieldR.one + beta'{2}) *
              (gamma'{2} +
               lookup_selector_at_z{2} *
               (a_at_z{2} + eta_{2} * b_at_z{2} + eta_{2} ^ 2 * c_at_z{2} +
                eta_{2} ^ 3 * table_type_at_z{2})) *
              (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) *
              (gamma'{2} * (FieldR.one + beta'{2}) + t_at_z{2} +
               beta'{2} * t_at_z_omega{2})) +
           alpha{2} ^ 7 * l_0_at_z{2} + alpha{2} ^ 8 * l_n_minus_one_at_z{2}) *
          v{2} * z_lookup{2} +
          v{2} * alpha{2} ^ 6 * z_lookup_at_z_omega{2} *
          (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) * s{2} +
          (alpha{2} ^ 4 * (z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
           (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_0) + gamma{2} +
            b_at_z{2}) *
           (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_1) + gamma{2} +
            c_at_z{2}) *
           (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_2) + gamma{2} +
            d_at_z{2}) +
           l_0_at_z{2} * alpha{2} ^ 5) *
          v{2} * z_perm{2} /\
        aggregatedOpeningAtZOmega{1} = v{2} ^ 13 * z_perm_at_z_omega{2} + v{2} ^ 14 * d_at_z_omega{2} +
          v{2} ^ 15 * s_at_z_omega{2} + v{2} ^ 16 * z_lookup_at_z_omega{2} +
          v{2} ^ 17 * t_at_z_omega{2} /\
        pairingPairWithGeneratorSlot{1} = d0{2} +
          v{2} *
          (main_gate_selector_at_z{2} *
           (a_at_z{2} * vk_gate_setup_0 + b_at_z{2} * vk_gate_setup_1 +
            c_at_z{2} * vk_gate_setup_2 + d_at_z{2} * vk_gate_setup_3 +
            a_at_z{2} * b_at_z{2} * vk_gate_setup_4 +
            a_at_z{2} * c_at_z{2} * vk_gate_setup_5 + vk_gate_setup_6 +
            d_at_z_omega{2} * vk_gate_setup_7) +
           alpha{2} *
           (a_at_z{2} ^ 2 + -b_at_z{2} + (b_at_z{2} ^ 2 + -c_at_z{2}) * alpha{2} +
            (a_at_z{2} * c_at_z{2} + -d_at_z{2}) * alpha{2} ^ 2) *
           vk_gate_selectors_1 +
           (G.inv
              (alpha{2} ^ 4 * z_perm_at_z_omega{2} * beta_{2} *
               (sigma_0_at_z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
               (sigma_1_at_z{2} * beta_{2} + gamma{2} + b_at_z{2}) *
               (sigma_2_at_z{2} * beta_{2} + gamma{2} + c_at_z{2}) * vk_permutation_3))) +
          v{2} ^ 2 * a{2} + v{2} ^ 3 * b{2} + v{2} ^ 4 * c{2} +
          v{2} ^ 6 * vk_gate_selectors_0 + v{2} ^ 7 * vk_permutation_0 +
          v{2} ^ 8 * vk_permutation_1 + v{2} ^ 9 * vk_permutation_2 +
          v{2} ^ 11 * vk_lookup_selector + v{2} ^ 12 * vk_lookup_table_type +
          (v{2} ^ 5 * d{2} + v{2} ^ 10 * t{2} +
          u{2} *
           (v{2} ^ 13 * z_perm{2} + v{2} ^ 14 * d{2} + v{2} ^ 15 * s{2} +
           v{2} ^ 16 * z_lookup{2} + v{2} ^ 17 * t{2}) +
           ((- alpha{2} ^ 6 * (FieldR.one + beta'{2}) *
              (gamma'{2} +
                lookup_selector_at_z{2} *
               (a_at_z{2} + eta_{2} * b_at_z{2} + eta_{2} ^ 2 * c_at_z{2} +
                 eta_{2} ^ 3 * table_type_at_z{2})) *
               (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) *
               (gamma'{2} * (FieldR.one + beta'{2}) + t_at_z{2} +
                beta'{2} * t_at_z_omega{2})) +
            alpha{2} ^ 7 * l_0_at_z{2} + alpha{2} ^ 8 * l_n_minus_one_at_z{2}) *
           v{2} * z_lookup{2} +
           v{2} * alpha{2} ^ 6 * z_lookup_at_z_omega{2} *
           (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) * s{2} +
           (alpha{2} ^ 4 * (z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
            (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_0) + gamma{2} +
             b_at_z{2}) *
           (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_1) + gamma{2} +
             c_at_z{2}) *
            (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_2) + gamma{2} +
             d_at_z{2}) +
            l_0_at_z{2} * alpha{2} ^ 5) *
           v{2} * z_perm{2}) /\
        pairingBufferPointSlot{1} = (quotient_poly_opening_at_z{2} + v{2} * r_at_z{2} + v{2} ^ 2 * a_at_z{2} +
           v{2} ^ 3 * b_at_z{2} + v{2} ^ 4 * c_at_z{2} + v{2} ^ 5 * d_at_z{2} +
           v{2} ^ 6 * main_gate_selector_at_z{2} + v{2} ^ 7 * sigma_0_at_z{2} +
           v{2} ^ 8 * sigma_1_at_z{2} + v{2} ^ 9 * sigma_2_at_z{2} +
           v{2} ^ 10 * t_at_z{2} + v{2} ^ 11 * lookup_selector_at_z{2} +
           v{2} ^ 12 * table_type_at_z{2} +
           u{2} *
           (v{2} ^ 13 * z_perm_at_z_omega{2} + v{2} ^ 14 * d_at_z_omega{2} +
            v{2} ^ 15 * s_at_z_omega{2} + v{2} ^ 16 * z_lookup_at_z_omega{2} +
            v{2} ^ 17 * t_at_z_omega{2})) *
          g_gen /\
        e{2} = (quotient_poly_opening_at_z{2} (*t(z)*) + v{2} * r_at_z{2}
          + (v{2}^2)*a_at_z{2} + (v{2}^3)+b_at_z{2} + (v{2}^4)*c_at_z{2} + (v{2}^5)*d_at_z{2}
          + (v{2}^6)*main_gate_selector_at_z{2}
          + (v{2}^7)*sigma_0_at_z{2} + (v{2}^8)*sigma_1_at_z{2} + (v{2}^9)*sigma_2_at_z{2}
          + (v{2}^10)*t_at_z{2} + (v{2}^11)*lookup_selector_at_z{2} * (v{2}^12)*table_type_at_z{2}
          + u{2} * ((v{2}^13)*z_perm_at_z_omega{2} + (v{2}^14)*d_at_z_omega{2}
            + (v{2}^15)*s_at_z_omega{2} + (v{2}^16)*z_lookup_at_z_omega{2} + (v{2}^17)*t_at_z_omega{2}
          )
        )* EllipticCurve.g_gen /\
        f{2} = d0{2} + v{2} * d1{2}
          + (v{2}^2)*a{2} + (v{2}^3)*b{2} + (v{2}^4)*c{2} + (v{2}^5)*d{2}
          + (v{2}^6)*vk_permutation_0
          + (v{2}^7)*sigma_0{2} + (v{2}^8)*sigma_1{2} + (v{2}^9)*sigma_2{2}
          + (v{2}^10)*t{2} + (v{2}^11)*lookup_selector{2} + (v{2}^12)*table_type{2}
          + u{2} * ((v{2}^13)*z_perm{2} + (v{2}^14)*d{2}
          + (v{2}^15)*s{2} + (v{2}^16)*z_lookup{2} + (v{2}^17)*t{2}
          ) /\
        pairing_pair_with_generator{2} = (z{2} * w{2})
          + u{2} * z{2} * omega{2} * w'{2}
          + f{2} + (G.inv e{2}) /\
        pairing_pair_with_x{2} = w{2} + u{2} * w'{2}
      )).
        case (failed{1}).
          conseq (_ : failed{1} /\ !isValid{2} ==> failed{1} /\ !isValid{2}).
            by progress; case H; progress.
            by progress; left; progress.
            inline PrepareAggregatedCommitment.high.
            wp. skip. by progress.

        (* case !failed{1} *)
          transitivity{1} 
            { (aggregatedAtZSlot,
              aggregatedOpeningAtZSlot,
              aggregatedAtZOmegaSlot,
              aggregatedOpeningAtZOmega,
              pairingPairWithGeneratorSlot,
              pairingBufferPointSlot) <@
              PrepareAggregatedCommitment.super_high(query_at_z_0,
              _quotient_poly_opening_at_z,
              query_at_z_1,
              state_v,
              _linearisation_poly_opening_at_z,
              _state_poly_0,
              _state_poly_0_opening_at_z,
              _state_poly_1,
              _state_poly_1_opening_at_z,
              _state_poly_2,
              _state_poly_2_opening_at_z,
              _state_poly_3_opening_at_z,
              vk_gate_selectors_0,
              _gate_selector_0_opening_at_z,
              vk_permutation_0,
              _copy_permutation_poly_0_opening_at_z,
              vk_permutation_1,
              _copy_permutation_poly_1_opening_at_z,
              vk_permutation_2,
              _copy_permutation_poly_2_opening_at_z,
              _lookup_t_poly_opening_at_z,
              vk_lookup_selector,
              _lookup_selector_poly_opening_at_z,
              vk_lookup_table_type,
              _lookup_table_type_poly_opening_at_z,
              copy_permutation_first_aggregated_commitment_coeff,
              state_u,
              _copy_permutation_grand_product,
              _copy_permutation_grand_product_opening_at_z_omega,
              _state_poly_3,
              _state_poly_3_opening_at_z_omega,
              _lookup_s_poly,
              _lookup_s_poly_opening_at_z_omega,
              lookupSFirstAggregatedCommitment,
              _lookup_grand_product,
              _lookup_grand_product_opening_at_z_omega,
              lookupGrandProductFirstAggregatedCoefficient,
              query_t_poly_aggregated,
              _lookup_t_poly_opening_at_z_omega);}
            (
              ={query_at_z_0,
                _quotient_poly_opening_at_z,
                query_at_z_1,
                state_v,
                _linearisation_poly_opening_at_z,
                _state_poly_0,
                _state_poly_0_opening_at_z,
                _state_poly_1,
                _state_poly_1_opening_at_z,
                _state_poly_2,
                _state_poly_2_opening_at_z,
                _state_poly_3_opening_at_z,
                _gate_selector_0_opening_at_z,
                _copy_permutation_poly_0_opening_at_z,
                _copy_permutation_poly_1_opening_at_z,
                _copy_permutation_poly_2_opening_at_z,
                _lookup_t_poly_opening_at_z,
                _lookup_selector_poly_opening_at_z,
                _lookup_table_type_poly_opening_at_z,
                copy_permutation_first_aggregated_commitment_coeff,
                state_u,
                _copy_permutation_grand_product,
                _copy_permutation_grand_product_opening_at_z_omega,
                _state_poly_3,
                _state_poly_3_opening_at_z_omega,
                _lookup_s_poly,
                _lookup_s_poly_opening_at_z_omega,
                lookupSFirstAggregatedCommitment,
                _lookup_grand_product,
                _lookup_grand_product_opening_at_z_omega,
                lookupGrandProductFirstAggregatedCoefficient,
                query_t_poly_aggregated,
                _lookup_t_poly_opening_at_z_omega,
                state_z,
                _opening_proof_at_z,
                _opening_proof_at_z_omega,
                vk_recursive_flag,
                _recursive_part_p1,
                _recursive_part_p2
              } /\
              ={_public_input, _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_eta, state_z_in_domain, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega, aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, aggregatedOpeningAtZOmega, failed}
                ==>
              ={
                state_u,
                state_z,
                pairingPairWithGeneratorSlot,
                pairingBufferPointSlot,
                _opening_proof_at_z,
                _opening_proof_at_z_omega,
                vk_recursive_flag,
                _recursive_part_p1,
                _recursive_part_p2,
                failed
              } /\
              ={_public_input, _state_poly_0, _state_poly_1, _state_poly_2, _state_poly_3, _copy_permutation_grand_product, _lookup_s_poly, _lookup_grand_product, _quotient_poly_part_0, _quotient_poly_part_1, _quotient_poly_part_2, _quotient_poly_part_3, _state_poly_0_opening_at_z, _state_poly_1_opening_at_z, _state_poly_2_opening_at_z, _state_poly_3_opening_at_z, _state_poly_3_opening_at_z_omega, _gate_selector_0_opening_at_z, _copy_permutation_poly_0_opening_at_z, _copy_permutation_poly_1_opening_at_z, _copy_permutation_poly_2_opening_at_z, _copy_permutation_grand_product_opening_at_z_omega, _lookup_s_poly_opening_at_z_omega, _lookup_grand_product_opening_at_z_omega, _lookup_t_poly_opening_at_z, _lookup_t_poly_opening_at_z_omega, _lookup_selector_poly_opening_at_z, _lookup_table_type_poly_opening_at_z, _quotient_poly_opening_at_z, _linearisation_poly_opening_at_z, state_alpha, state_beta, state_beta_lookup, state_gamma, state_gamma_lookup, state_eta, state_z_in_domain, state_v, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, l0_at_z, ln_minus_one_at_z, beta_plus_one, beta_gamma_plus_gamma, z_minus_last_omega, query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient, query_t_poly_aggregated, aggregatedAtZSlot, aggregatedOpeningAtZSlot, aggregatedAtZOmegaSlot, aggregatedOpeningAtZOmega}
            )
            (
              !failed{1} /\
              isValid{2} /\
              !vk_recursive_flag{1} /\
              _public_input{1} = public_input{2} /\
              _state_poly_0{1} = a{2} /\
              _state_poly_1{1} = b{2} /\
              _state_poly_2{1} = c{2} /\
              _state_poly_3{1} = d{2} /\
              _copy_permutation_grand_product{1} = z_perm{2} /\
              _lookup_s_poly{1} = s{2} /\
              _lookup_grand_product{1} = z_lookup{2} /\
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
              _copy_permutation_grand_product_opening_at_z_omega{1} =
              z_perm_at_z_omega{2} /\
              _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
              _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
              _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
              _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
              _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
              _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
              _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
              _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
              _opening_proof_at_z{1} = w{2} /\
              _opening_proof_at_z_omega{1} = w'{2} /\
              _recursive_part_p1{1} = None /\
              _recursive_part_p2{1} = None /\
              k0{2} = (FieldR.inF Constants.NON_RESIDUE_0) /\
              k1{2} = (FieldR.inF Constants.NON_RESIDUE_1) /\
              k2{2} = (FieldR.inF Constants.NON_RESIDUE_2) /\
              n{2} = Constants.DOMAIN_SIZE /\
              q_a{2} = vk_gate_setup_0 /\
              q_b{2} = vk_gate_setup_1 /\
              q_c{2} = vk_gate_setup_2 /\
              q_d{2} = vk_gate_setup_3 /\
              q_ab{2} = vk_gate_setup_4 /\
              q_ac{2} = vk_gate_setup_5 /\
              q_const{2} = vk_gate_setup_6 /\
              q_d_next{2} = vk_gate_setup_7 /\
              custom_gate_selector{2} = vk_gate_selectors_1 /\
              sigma_0{2} = vk_permutation_0 /\
              sigma_1{2} = vk_permutation_1 /\
              sigma_2{2} = vk_permutation_2 /\
              sigma_3{2} = vk_permutation_3 /\
              lookup_selector{2} = vk_lookup_selector /\
              table_type{2} = vk_lookup_table_type /\
              omega{2} = Constants.OMEGAFr /\
              col_0{2} = vk_lookup_table_0 /\
              col_1{2} = vk_lookup_table_1 /\
              col_2{2} = vk_lookup_table_2 /\
              col_3{2} = vk_lookup_table_3 /\
              state_alpha{1} = alpha{2} /\
              state_beta{1} = beta_{2} /\
              state_beta_lookup{1} = beta'{2} /\
              state_gamma{1} = gamma{2} /\
              state_gamma_lookup{1} = gamma'{2} /\
              state_eta{1} = eta_{2} /\
              state_z{1} = z{2} /\
              state_z_in_domain{1} = z{2} ^ n{2} /\
              state_v{1} = v{2} /\
              state_u{1} = u{2} /\
              alpha2{1} = alpha{2} ^ 2 /\
              alpha3{1} = alpha{2} ^ 3 /\
              alpha4{1} = alpha{2} ^ 4 /\
              alpha5{1} = alpha{2} ^ 5 /\
              alpha6{1} = alpha{2} ^ 6 /\
              alpha7{1} = alpha{2} ^ 7 /\
              alpha8{1} = alpha{2} ^ 8 /\
              l0_at_z{1} = l_0_at_z{2} /\
              ln_minus_one_at_z{1} = l_n_minus_one_at_z{2} /\
              beta_plus_one{1} = FieldR.one + beta'{2} /\
              beta_gamma_plus_gamma{1} = gamma'{2} * (FieldR.one + beta'{2}) /\
              z_minus_last_omega{1} = z{2} - omega{2} ^ (n{2} - 1) /\
              query_at_z_0{1} = d0{2} /\
              query_at_z_1{1} = v{2} * (main_gate_selector_at_z{2} *
                  (a_at_z{2} * q_a{2} + b_at_z{2} * q_b{2} + c_at_z{2} * q_c{2} +
                  d_at_z{2} * q_d{2} + a_at_z{2} * b_at_z{2} * q_ab{2} +
                  a_at_z{2} * c_at_z{2} * q_ac{2} + q_const{2} +
                  d_at_z_omega{2} * q_d_next{2}) +
                alpha{2} *
                  (a_at_z{2} ^ 2 - b_at_z{2} + (b_at_z{2} ^ 2 - c_at_z{2}) * alpha{2} +
                  (a_at_z{2} * c_at_z{2} - d_at_z{2}) * alpha{2} ^ 2) *
                custom_gate_selector{2} +
                (G.inv
                  (alpha{2} ^ 4 * z_perm_at_z_omega{2} * beta_{2} *
                  (sigma_0_at_z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
                  (sigma_1_at_z{2} * beta_{2} + gamma{2} + b_at_z{2}) *
                  (sigma_2_at_z{2} * beta_{2} + gamma{2} + c_at_z{2}) * sigma_3{2}))) /\
              copy_permutation_first_aggregated_commitment_coeff{1} =
                (alpha{2} ^ 4 * (z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
                 (z{2} * beta_{2} * k0{2} + gamma{2} + b_at_z{2}) *
                 (z{2} * beta_{2} * k1{2} + gamma{2} + c_at_z{2}) *
                 (z{2} * beta_{2} * k2{2} + gamma{2} + d_at_z{2}) +
                 l_0_at_z{2} * alpha{2} ^ 5) * v{2} /\
              lookupSFirstAggregatedCommitment{1} =
                v{2} * alpha{2} ^ 6 * z_lookup_at_z_omega{2} *
                (z{2} - omega{2} ^ (n{2} - 1)) /\
              lookupGrandProductFirstAggregatedCoefficient{1} =
                ((- alpha{2} ^ 6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z{2}) *
                  (z{2} - omega{2} ^ (n{2} - 1)) *
                  (gamma'{2} * (FieldR.one + beta'{2}) + t_at_z{2} +
                   beta'{2} * t_at_z_omega{2})) +
                alpha{2} ^ 7 * l_0_at_z{2} + alpha{2} ^ 8 * l_n_minus_one_at_z{2}) *
                v{2} /\
              query_t_poly_aggregated{1} = t{2} /\
              d1{2} =
              main_gate_selector_at_z{2} *
              (a_at_z{2} * q_a{2} + b_at_z{2} * q_b{2} + c_at_z{2} * q_c{2} +
               d_at_z{2} * q_d{2} + a_at_z{2} * b_at_z{2} * q_ab{2} +
               a_at_z{2} * c_at_z{2} * q_ac{2} + q_const{2} +
               d_at_z_omega{2} * q_d_next{2}) +
              alpha{2} *
              (a_at_z{2} ^ 2 - b_at_z{2} + (b_at_z{2} ^ 2 - c_at_z{2}) * alpha{2} +
               (a_at_z{2} * c_at_z{2} - d_at_z{2}) * alpha{2} ^ 2) *
              custom_gate_selector{2} +
              alpha{2} ^ 4 * (a_at_z{2} + beta_{2} * z{2} + gamma{2}) *
              (b_at_z{2} + beta_{2} * z{2} * k0{2} + gamma{2}) *
              (c_at_z{2} + beta_{2} * z{2} * k1{2} + gamma{2}) *
              (d_at_z{2} + beta_{2} * z{2} * k2{2} + gamma{2}) * z_perm{2} +
              (G.inv
                 (alpha{2} ^ 4 * z_perm_at_z_omega{2} * beta_{2} *
                  (a_at_z{2} + beta_{2} * sigma_0_at_z{2} + gamma{2}) *
                  (b_at_z{2} + beta_{2} * sigma_1_at_z{2} + gamma{2}) *
                  (c_at_z{2} + beta_{2} * sigma_2_at_z{2} + gamma{2}) * sigma_3{2})) +
              alpha{2} ^ 5 * l_0_at_z{2} * z_perm{2} +
              (G.inv
                 (alpha{2} ^ 6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z{2}) *
                  (z{2} - omega{2} ^ (n{2} - 1)) *
                  (gamma'{2} * (FieldR.one + beta'{2}) + t_at_z{2} +
                   beta'{2} * t_at_z_omega{2}) *
                  z_lookup{2})) +
              alpha{2} ^ 6 * z_lookup_at_z_omega{2} * (z{2} - omega{2} ^ (n{2} - 1)) *
              s{2} + alpha{2} ^ 7 * l_0_at_z{2} * z_lookup{2} +
              alpha{2} ^ 8 * l_n_minus_one_at_z{2} * z_lookup{2} /\
              f_at_z{2} =
              lookup_selector_at_z{2} *
              (a_at_z{2} + eta_{2} * b_at_z{2} + eta_{2} ^ 2 * c_at_z{2} +
              eta_{2} ^ 3 * table_type_at_z{2})
                ==>
              !failed{1} /\ isValid{2} /\
              !vk_recursive_flag{1} /\
              _public_input{1} = public_input{2} /\
              _state_poly_0{1} = a{2} /\
              _state_poly_1{1} = b{2} /\
              _state_poly_2{1} = c{2} /\
              _state_poly_3{1} = d{2} /\
              _copy_permutation_grand_product{1} = z_perm{2} /\
              _lookup_s_poly{1} = s{2} /\
              _lookup_grand_product{1} = z_lookup{2} /\
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
              _lookup_s_poly_opening_at_z_omega{1} = s_at_z_omega{2} /\
              _lookup_grand_product_opening_at_z_omega{1} = z_lookup_at_z_omega{2} /\
              _lookup_t_poly_opening_at_z{1} = t_at_z{2} /\
              _lookup_t_poly_opening_at_z_omega{1} = t_at_z_omega{2} /\
              _lookup_selector_poly_opening_at_z{1} = lookup_selector_at_z{2} /\
              _lookup_table_type_poly_opening_at_z{1} = table_type_at_z{2} /\
              _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
              _linearisation_poly_opening_at_z{1} = r_at_z{2} /\
              _opening_proof_at_z{1} = w{2} /\
              _opening_proof_at_z_omega{1} = w'{2} /\
              _recursive_part_p1{1} = None /\
              _recursive_part_p2{1} = None /\
              k0{2} = FieldR.inF Constants.NON_RESIDUE_0 /\
              k1{2} = FieldR.inF Constants.NON_RESIDUE_1 /\ 
              k2{2} = FieldR.inF Constants.NON_RESIDUE_2 /\
              n{2} = Constants.DOMAIN_SIZE /\
              q_a{2} = vk_gate_setup_0 /\
              q_b{2} = vk_gate_setup_1 /\
              q_c{2} = vk_gate_setup_2 /\
              q_d{2} = vk_gate_setup_3 /\
              q_ab{2} = vk_gate_setup_4 /\
              q_ac{2} = vk_gate_setup_5 /\
              q_const{2} = vk_gate_setup_6 /\
              q_d_next{2} = vk_gate_setup_7 /\
              custom_gate_selector{2} = vk_gate_selectors_1 /\
              sigma_0{2} = vk_permutation_0 /\
              sigma_1{2} = vk_permutation_1 /\
              sigma_2{2} = vk_permutation_2 /\ 
              sigma_3{2} = vk_permutation_3 /\
              lookup_selector{2} = vk_lookup_selector /\
              table_type{2} = vk_lookup_table_type /\
              omega{2} = Constants.OMEGAFr /\
              col_0{2} = vk_lookup_table_0 /\
              col_1{2} = vk_lookup_table_1 /\
              col_2{2} = vk_lookup_table_2 /\
              col_3{2} = vk_lookup_table_3 /\
              state_alpha{1} = alpha{2} /\
              state_beta{1} = beta_{2} /\
              state_beta_lookup{1} = beta'{2} /\
              state_gamma{1} = gamma{2} /\
              state_gamma_lookup{1} = gamma'{2} /\
              state_eta{1} = eta_{2} /\
              state_z{1} = z{2} /\
              state_z_in_domain{1} = z{2} ^ n{2} /\
              state_v{1} = v{2} /\
              state_u{1} = u{2} /\
              alpha2{1} = alpha{2}^2 /\
              alpha3{1} = alpha{2}^3 /\
              alpha4{1} = alpha{2}^4 /\
              alpha5{1} = alpha{2}^5 /\
              alpha6{1} = alpha{2}^6 /\
              alpha7{1} = alpha{2}^7 /\
              alpha8{1} = alpha{2}^8 /\
              l0_at_z{1} = l_0_at_z{2} /\
              ln_minus_one_at_z{1} = l_n_minus_one_at_z{2} /\
              beta_plus_one{1} = FieldR.one + beta'{2} /\
              beta_gamma_plus_gamma{1} = gamma'{2} * (FieldR.one + beta'{2}) /\
              z_minus_last_omega{1} = z{2} - omega{2}^(n{2} - 1) /\
              query_at_z_0{1} = d0{2} /\
              query_at_z_1{1} = v{2} * (
                main_gate_selector_at_z{2} * (
                  (a_at_z{2} * q_a{2}) +
                  (b_at_z{2} * q_b{2}) +
                  (c_at_z{2} * q_c{2}) +
                  (d_at_z{2} * q_d{2}) +
                  (a_at_z{2} * b_at_z{2} * q_ab{2}) +
                  (a_at_z{2} * c_at_z{2} * q_ac{2}) +
                  q_const{2} +
                  (d_at_z_omega{2} * q_d_next{2})
                ) + 
                alpha{2} * (
                  (
                    (a_at_z{2}^2 - b_at_z{2}) +
                    (b_at_z{2}^2 - c_at_z{2}) * alpha{2} +
                    (a_at_z{2} * c_at_z{2} - d_at_z{2}) * alpha{2}^2
                  )
                )* custom_gate_selector{2} +
                G.inv (alpha{2}^4 * z_perm_at_z_omega{2} * beta_{2} *
                  (sigma_0_at_z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
                  (sigma_1_at_z{2} * beta_{2} + gamma{2} + b_at_z{2}) *
                  (sigma_2_at_z{2} * beta_{2} + gamma{2} + c_at_z{2}) *
                  sigma_3{2})
                ) /\
              copy_permutation_first_aggregated_commitment_coeff{1} = (                                
                alpha{2}^4 * (z{2} * beta_{2} + gamma{2} + a_at_z{2}) *                               
                (z{2} * beta_{2} * k0{2} + gamma{2} + b_at_z{2}) * 
                (z{2} * beta_{2} * k1{2} + gamma{2} + c_at_z{2}) * 
                (z{2} * beta_{2} * k2{2} + gamma{2} + d_at_z{2}) + 
                l_0_at_z{2} * alpha{2}^5
              ) * v{2} /\
              lookupSFirstAggregatedCommitment{1} = v{2} * alpha{2}^6 * z_lookup_at_z_omega{2} * (z{2} - omega{2}^(n{2}-1)) /\
              lookupGrandProductFirstAggregatedCoefficient{1} = ((
                - alpha{2}^6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z{2}) * (z{2} - omega{2}^(n{2}-1)) * (
                  gamma'{2}*(FieldR.one + beta'{2}) + t_at_z{2} + beta'{2} * t_at_z_omega{2}
                )) +
                alpha{2}^7 * l_0_at_z{2} +
                alpha{2}^8 * l_n_minus_one_at_z{2}) * v{2} /\
              query_t_poly_aggregated{1} = t{2} /\
              d1{2} = main_gate_selector_at_z{2} * (
                  (a_at_z{2} * q_a{2}) +
                  (b_at_z{2} * q_b{2}) +
                  (c_at_z{2} * q_c{2}) +
                  (d_at_z{2} * q_d{2}) +
                  (a_at_z{2} * b_at_z{2} * q_ab{2}) +
                  (a_at_z{2} * c_at_z{2} * q_ac{2}) +
                  q_const{2} +
                  (d_at_z_omega{2} * q_d_next{2})
              ) 
              + alpha{2} * (
                (
                  (a_at_z{2}^2 - b_at_z{2}) +
                  (b_at_z{2}^2 - c_at_z{2}) * alpha{2} +
                  (a_at_z{2} * c_at_z{2} - d_at_z{2}) * alpha{2}^2
                )
              )* custom_gate_selector{2}
              + alpha{2}^4 *
                (a_at_z{2} + beta_{2} * z{2}         + gamma{2}) *                               
                (b_at_z{2} + beta_{2} * z{2} * k0{2} + gamma{2}) * 
                (c_at_z{2} + beta_{2} * z{2} * k1{2} + gamma{2}) * 
                (d_at_z{2} + beta_{2} * z{2} * k2{2} + gamma{2}) * z_perm{2}
              + G.inv (alpha{2}^4 * z_perm_at_z_omega{2} * beta_{2} *
                (a_at_z{2} + beta_{2} * sigma_0_at_z{2} + gamma{2}) *
                (b_at_z{2} + beta_{2} * sigma_1_at_z{2} + gamma{2}) *
                (c_at_z{2} + beta_{2} * sigma_2_at_z{2} + gamma{2}) *
                sigma_3{2})
              + alpha{2}^5 * l_0_at_z{2} * z_perm{2}
              + G.inv (alpha{2}^6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z{2}) * (z{2} - omega{2}^(n{2}-1)) *
                (gamma'{2}*(FieldR.one + beta'{2}) + t_at_z{2} + beta'{2} * t_at_z_omega{2}) * z_lookup{2}
              ) 
                + alpha{2}^6 * z_lookup_at_z_omega{2} * (z{2} - omega{2}^(n{2}-1)) * s{2}
                + alpha{2}^7 * l_0_at_z{2} * z_lookup{2}
                + alpha{2}^8 * l_n_minus_one_at_z{2} * z_lookup{2}  /\
              f_at_z{2} = lookup_selector_at_z{2} * (a_at_z{2} + eta_{2} * b_at_z{2} + eta_{2}^2 * c_at_z{2} + eta_{2}^3 * table_type_at_z{2}) /\
              aggregatedAtZSlot{1} = d0{2} +
                v{2} *
                (main_gate_selector_at_z{2} *
                 (a_at_z{2} * vk_gate_setup_0 + b_at_z{2} * vk_gate_setup_1 +
                  c_at_z{2} * vk_gate_setup_2 + d_at_z{2} * vk_gate_setup_3 +
                  a_at_z{2} * b_at_z{2} * vk_gate_setup_4 +
                  a_at_z{2} * c_at_z{2} * vk_gate_setup_5 + vk_gate_setup_6 +
                  d_at_z_omega{2} * vk_gate_setup_7) +
                 alpha{2} *
                 (a_at_z{2} ^ 2 + -b_at_z{2} + (b_at_z{2} ^ 2 + -c_at_z{2}) * alpha{2} +
                  (a_at_z{2} * c_at_z{2} + -d_at_z{2}) * alpha{2} ^ 2) *
                 vk_gate_selectors_1 +
                 (G.inv
                    (alpha{2} ^ 4 * z_perm_at_z_omega{2} * beta_{2} *
                     (sigma_0_at_z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
                     (sigma_1_at_z{2} * beta_{2} + gamma{2} + b_at_z{2}) *
                     (sigma_2_at_z{2} * beta_{2} + gamma{2} + c_at_z{2}) * vk_permutation_3))) +
                v{2} ^ 2 * a{2} + v{2} ^ 3 * b{2} + v{2} ^ 4 * c{2} +
                v{2} ^ 6 * vk_gate_selectors_0 + v{2} ^ 7 * vk_permutation_0 +
                v{2} ^ 8 * vk_permutation_1 + v{2} ^ 9 * vk_permutation_2 +
                v{2} ^ 11 * vk_lookup_selector + v{2} ^ 12 * vk_lookup_table_type /\
              aggregatedOpeningAtZSlot{1} = quotient_poly_opening_at_z{2} + v{2} * r_at_z{2} + v{2} ^ 2 * a_at_z{2} +
                v{2} ^ 3 * b_at_z{2} + v{2} ^ 4 * c_at_z{2} + v{2} ^ 5 * d_at_z{2} +
                v{2} ^ 6 * main_gate_selector_at_z{2} + v{2} ^ 7 * sigma_0_at_z{2} +
                v{2} ^ 8 * sigma_1_at_z{2} + v{2} ^ 9 * sigma_2_at_z{2} +
                v{2} ^ 10 * t_at_z{2} + v{2} ^ 11 * lookup_selector_at_z{2} +
                v{2} ^ 12 * table_type_at_z{2} /\
              aggregatedAtZOmegaSlot{1} = v{2} ^ 5 * d{2} + v{2} ^ 10 * t{2} +
                u{2} *
                (v{2} ^ 13 * z_perm{2} + v{2} ^ 14 * d{2} + v{2} ^ 15 * s{2} +
                 v{2} ^ 16 * z_lookup{2} + v{2} ^ 17 * t{2}) +
                ((- alpha{2} ^ 6 * (FieldR.one + beta'{2}) *
                    (gamma'{2} +
                     lookup_selector_at_z{2} *
                     (a_at_z{2} + eta_{2} * b_at_z{2} + eta_{2} ^ 2 * c_at_z{2} +
                      eta_{2} ^ 3 * table_type_at_z{2})) *
                    (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) *
                    (gamma'{2} * (FieldR.one + beta'{2}) + t_at_z{2} +
                     beta'{2} * t_at_z_omega{2})) +
                 alpha{2} ^ 7 * l_0_at_z{2} + alpha{2} ^ 8 * l_n_minus_one_at_z{2}) *
                v{2} * z_lookup{2} +
                v{2} * alpha{2} ^ 6 * z_lookup_at_z_omega{2} *
                (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) * s{2} +
                (alpha{2} ^ 4 * (z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
                 (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_0) + gamma{2} +
                  b_at_z{2}) *
                 (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_1) + gamma{2} +
                  c_at_z{2}) *
                 (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_2) + gamma{2} +
                  d_at_z{2}) +
                 l_0_at_z{2} * alpha{2} ^ 5) *
                v{2} * z_perm{2} /\
              aggregatedOpeningAtZOmega{1} = v{2} ^ 13 * z_perm_at_z_omega{2} + v{2} ^ 14 * d_at_z_omega{2} +
                v{2} ^ 15 * s_at_z_omega{2} + v{2} ^ 16 * z_lookup_at_z_omega{2} +
                v{2} ^ 17 * t_at_z_omega{2} /\
              pairingPairWithGeneratorSlot{1} = d0{2} +
                v{2} *
                (main_gate_selector_at_z{2} *
                 (a_at_z{2} * vk_gate_setup_0 + b_at_z{2} * vk_gate_setup_1 +
                  c_at_z{2} * vk_gate_setup_2 + d_at_z{2} * vk_gate_setup_3 +
                  a_at_z{2} * b_at_z{2} * vk_gate_setup_4 +
                  a_at_z{2} * c_at_z{2} * vk_gate_setup_5 + vk_gate_setup_6 +
                  d_at_z_omega{2} * vk_gate_setup_7) +
                 alpha{2} *
                 (a_at_z{2} ^ 2 + -b_at_z{2} + (b_at_z{2} ^ 2 + -c_at_z{2}) * alpha{2} +
                  (a_at_z{2} * c_at_z{2} + -d_at_z{2}) * alpha{2} ^ 2) *
                 vk_gate_selectors_1 +
                 (G.inv
                    (alpha{2} ^ 4 * z_perm_at_z_omega{2} * beta_{2} *
                     (sigma_0_at_z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
                     (sigma_1_at_z{2} * beta_{2} + gamma{2} + b_at_z{2}) *
                     (sigma_2_at_z{2} * beta_{2} + gamma{2} + c_at_z{2}) * vk_permutation_3))) +
                v{2} ^ 2 * a{2} + v{2} ^ 3 * b{2} + v{2} ^ 4 * c{2} +
                v{2} ^ 6 * vk_gate_selectors_0 + v{2} ^ 7 * vk_permutation_0 +
                v{2} ^ 8 * vk_permutation_1 + v{2} ^ 9 * vk_permutation_2 +
                v{2} ^ 11 * vk_lookup_selector + v{2} ^ 12 * vk_lookup_table_type +
                (v{2} ^ 5 * d{2} + v{2} ^ 10 * t{2} +
                 u{2} *
                 (v{2} ^ 13 * z_perm{2} + v{2} ^ 14 * d{2} + v{2} ^ 15 * s{2} +
                  v{2} ^ 16 * z_lookup{2} + v{2} ^ 17 * t{2}) +
                 ((- alpha{2} ^ 6 * (FieldR.one + beta'{2}) *
                     (gamma'{2} +
                      lookup_selector_at_z{2} *
                      (a_at_z{2} + eta_{2} * b_at_z{2} + eta_{2} ^ 2 * c_at_z{2} +
                       eta_{2} ^ 3 * table_type_at_z{2})) *
                     (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) *
                     (gamma'{2} * (FieldR.one + beta'{2}) + t_at_z{2} +
                      beta'{2} * t_at_z_omega{2})) +
                  alpha{2} ^ 7 * l_0_at_z{2} + alpha{2} ^ 8 * l_n_minus_one_at_z{2}) *
                 v{2} * z_lookup{2} +
                 v{2} * alpha{2} ^ 6 * z_lookup_at_z_omega{2} *
                 (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) * s{2} +
                 (alpha{2} ^ 4 * (z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
                  (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_0) + gamma{2} +
                   b_at_z{2}) *
                  (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_1) + gamma{2} +
                   c_at_z{2}) *
                  (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_2) + gamma{2} +
                   d_at_z{2}) +
                  l_0_at_z{2} * alpha{2} ^ 5) *
                 v{2} * z_perm{2}) /\
              pairingBufferPointSlot{1} = (quotient_poly_opening_at_z{2} + v{2} * r_at_z{2} + v{2} ^ 2 * a_at_z{2} +
                 v{2} ^ 3 * b_at_z{2} + v{2} ^ 4 * c_at_z{2} + v{2} ^ 5 * d_at_z{2} +
                 v{2} ^ 6 * main_gate_selector_at_z{2} + v{2} ^ 7 * sigma_0_at_z{2} +
                 v{2} ^ 8 * sigma_1_at_z{2} + v{2} ^ 9 * sigma_2_at_z{2} +
                 v{2} ^ 10 * t_at_z{2} + v{2} ^ 11 * lookup_selector_at_z{2} +
                 v{2} ^ 12 * table_type_at_z{2} +
                 u{2} *
                 (v{2} ^ 13 * z_perm_at_z_omega{2} + v{2} ^ 14 * d_at_z_omega{2} +
                  v{2} ^ 15 * s_at_z_omega{2} + v{2} ^ 16 * z_lookup_at_z_omega{2} +
                  v{2} ^ 17 * t_at_z_omega{2})) *
                g_gen /\
              e{2} = (quotient_poly_opening_at_z{2} (*t(z)*) + v{2} * r_at_z{2}
                + (v{2}^2)*a_at_z{2} + (v{2}^3)+b_at_z{2} + (v{2}^4)*c_at_z{2} + (v{2}^5)*d_at_z{2}
                + (v{2}^6)*main_gate_selector_at_z{2}
                + (v{2}^7)*sigma_0_at_z{2} + (v{2}^8)*sigma_1_at_z{2} + (v{2}^9)*sigma_2_at_z{2}
                + (v{2}^10)*t_at_z{2} + (v{2}^11)*lookup_selector_at_z{2} * (v{2}^12)*table_type_at_z{2}
                + u{2} * ((v{2}^13)*z_perm_at_z_omega{2} + (v{2}^14)*d_at_z_omega{2}
                  + (v{2}^15)*s_at_z_omega{2} + (v{2}^16)*z_lookup_at_z_omega{2} + (v{2}^17)*t_at_z_omega{2}
                )
              )* EllipticCurve.g_gen /\
              f{2} = d0{2} + v{2} * d1{2}
                + (v{2}^2)*a{2} + (v{2}^3)*b{2} + (v{2}^4)*c{2} + (v{2}^5)*d{2}
                + (v{2}^6)*vk_permutation_0
                + (v{2}^7)*sigma_0{2} + (v{2}^8)*sigma_1{2} + (v{2}^9)*sigma_2{2}
                + (v{2}^10)*t{2} + (v{2}^11)*lookup_selector{2} + (v{2}^12)*table_type{2}
                + u{2} * ((v{2}^13)*z_perm{2} + (v{2}^14)*d{2}
                + (v{2}^15)*s{2} + (v{2}^16)*z_lookup{2} + (v{2}^17)*t{2}
                ) /\
              pairing_pair_with_generator{2} = (z{2} * w{2})
                + u{2} * z{2} * omega{2} * w'{2}
                + f{2} + (G.inv e{2}) /\
              pairing_pair_with_x{2} = w{2} + u{2} * w'{2}
            ).
              progress.
                exists _copy_permutation_grand_product{1}.
                exists _copy_permutation_grand_product_opening_at_z_omega{1}.
                exists _copy_permutation_poly_0_opening_at_z{1}.
                exists _copy_permutation_poly_1_opening_at_z{1}.
                exists _copy_permutation_poly_2_opening_at_z{1}.
                exists _gate_selector_0_opening_at_z{1}.
                exists _linearisation_poly_opening_at_z{1}.
                exists _lookup_grand_product{1}.
                exists _lookup_grand_product_opening_at_z_omega{1}.
                exists _lookup_s_poly{1}.
                exists _lookup_s_poly_opening_at_z_omega{1}.
                exists _lookup_selector_poly_opening_at_z{1}.
                exists _lookup_t_poly_opening_at_z{1}.
                exists _lookup_t_poly_opening_at_z_omega{1}.
                exists _lookup_table_type_poly_opening_at_z{1}.
                exists _opening_proof_at_z{1}.
                exists _opening_proof_at_z_omega{1}.
                exists _public_input{1}.
                exists _quotient_poly_opening_at_z{1}.
                exists _quotient_poly_part_0{1}.
                exists _quotient_poly_part_1{1}.
                exists _quotient_poly_part_2{1}.
                exists _quotient_poly_part_3{1}.
                exists _recursive_part_p1{1}.
                exists _recursive_part_p2{1}.
                exists _state_poly_0{1}.
                exists _state_poly_0_opening_at_z{1}.
                exists _state_poly_1{1}.
                exists _state_poly_1_opening_at_z{1}.
                exists _state_poly_2{1}.
                exists _state_poly_2_opening_at_z{1}.
                exists _state_poly_3{1}.
                exists _state_poly_3_opening_at_z{1}.
                exists _state_poly_3_opening_at_z_omega{1}.
                exists aggregatedAtZOmegaSlot{1}.
                exists aggregatedAtZSlot{1}.
                exists aggregatedOpeningAtZOmega{1}.
                exists aggregatedOpeningAtZSlot{1}.
                exists alpha2{1}.
                exists alpha3{1}.
                exists alpha4{1}.
                exists alpha5{1}.
                exists alpha6{1}.
                exists alpha7{1}.
                exists alpha8{1}.
                exists beta_gamma_plus_gamma{1}.
                exists beta_plus_one{1}.
                exists copy_permutation_first_aggregated_commitment_coeff{1}.
                exists failed{1}.
                exists l0_at_z{1}.
                exists ln_minus_one_at_z{1}.
                exists lookupGrandProductFirstAggregatedCoefficient{1}.
                exists lookupSFirstAggregatedCommitment{1}.
                exists query_at_z_0{1}.
                exists query_at_z_1{1}.
                exists query_t_poly_aggregated{1}.
                exists state_alpha{1}.
                exists state_beta{1}.
                exists state_beta_lookup{1}.
                exists state_eta{1}.
                exists state_gamma{1}.
                exists state_gamma_lookup{1}.
                exists state_u{1}.
                exists state_v{1}.
                exists state_z{1}.
                exists state_z_in_domain{1}.
                exists vk_recursive_flag{1}.
                exists z_minus_last_omega{1}.
                by progress; case H; progress.

              progress.
                rewrite H H0 H1.
                by progress.

              call prepareAggregatedCommitment_high_equiv_super_high.
                skip. by progress.

            inline PrepareAggregatedCommitment.super_high.
            wp. skip. by progress.
      (* prepare aggregated commitment done *)

      (* final pairing *)
      case (failed{1}).
        inline FinalPairing.high. wp. skip. progress.
        rewrite H0. progress. case H; progress.
        rewrite H2. by progress.
        rewrite H0. progress. case H; progress.
        rewrite H2. by progress.

      (* case !failed{1} *)
        inline FinalPairing.high. wp. skip. progress.
        pose SUPER := e (pairing_pair_with_generator{2} + pairing_pair_with_x{2}) (Constants.G2_ELEMENT_0_G + Constants.G2_ELEMENT_1_G).
        case H. by progress. by progress.
        pose SUPER := e (pairing_pair_with_generator{2} + pairing_pair_with_x{2}) (Constants.G2_ELEMENT_0_G + Constants.G2_ELEMENT_1_G).
        case H. by progress. progress. rewrite H H2. progress.
        pose u_z_omega_w' := u{2} * z{2} * Constants.OMEGAFr * w'{2}.
        have ->: z{2} * Constants.OMEGAFr * u{2} * w'{2} = u_z_omega_w'.
          rewrite /u_z_omega_w'.
          congr.
          rewrite FieldR.ComRing.mulrC.
          exact FieldR.ComRing.mulrA.
        pose w_plus_u_w' := w{2} + u{2} * w'{2}.
        have ->: u{2} * w'{2} + w{2} = w_plus_u_w' by exact g_comm.
        search EllipticCurve.(+).
        rewrite assoc_g.
        pose z_w_plus_u_z_omega_w' := z{2} * w{2} + u_z_omega_w'.
        have ->: u_z_omega_w' + z{2} * w{2} = z_w_plus_u_z_omega_w' by exact g_comm.
        pose d1_main_gate := main_gate_selector_at_z{2} * (
          a_at_z{2} * vk_gate_setup_0 +
          b_at_z{2} * vk_gate_setup_1 +
          c_at_z{2} * vk_gate_setup_2 +
          d_at_z{2} * vk_gate_setup_3 +
          a_at_z{2} * b_at_z{2} * vk_gate_setup_4 +
          a_at_z{2} * c_at_z{2} * vk_gate_setup_5 +
          vk_gate_setup_6 +
          d_at_z_omega{2} * vk_gate_setup_7
        ).
        pose d1_custom_gate := alpha{2} * (
          (a_at_z{2}^2 - b_at_z{2}) +
          (b_at_z{2}^2 - c_at_z{2}) * alpha{2} +
          (a_at_z{2}*c_at_z{2} - d_at_z{2}) * (alpha{2}^2)
        ) * vk_gate_selectors_1.
        have ->: alpha{2} *
          (a_at_z{2} ^ 2 + -b_at_z{2} + (b_at_z{2} ^ 2 + -c_at_z{2}) * alpha{2} +
           (a_at_z{2} * c_at_z{2} + -d_at_z{2}) * alpha{2} ^ 2) *
          vk_gate_selectors_1 = d1_custom_gate.
          rewrite /d1_custom_gate.
          congr. congr. by progress.
        pose d1_permutation_contribution_neg := alpha{2}^4 * z_perm_at_z_omega{2} * beta_{2} *
           (sigma_0_at_z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
           (sigma_1_at_z{2} * beta_{2} + gamma{2} + b_at_z{2}) *
           (sigma_2_at_z{2} * beta_{2} + gamma{2} + c_at_z{2}) *
           vk_permutation_3.
        pose f_v_2 := v{2}^2 * a{2}.
        pose f_v_3 := v{2}^3 * b{2}.
        pose f_v_4 := v{2}^4 * c{2}.
        pose f_v_5 := v{2}^5 * d{2}.
        pose f_v_6 := v{2}^6 * vk_gate_selectors_0. (*[main_gate_selector]*)
        pose f_v_7 := v{2}^7 * vk_permutation_0. (* [sigma_0] *)
        pose f_v_8 := v{2}^8 * vk_permutation_1. (* [sigma_1] *)
        pose f_v_9 := v{2}^9 * vk_permutation_2. (* [sigma_2] *)
        pose f_v_10 := v{2}^10 * t{2}.
        pose f_v_11 := v{2}^11 * vk_lookup_selector. (* [lookup_selector] *)
        pose f_v_12 := v{2}^12 * vk_lookup_table_type. (* [table_type] *)
        pose f_u := u{2} * (v{2}^13*z_perm{2} + v{2}^14*d{2} + v{2}^15*s{2} + v{2}^16*z_lookup{2} + v{2}^17*t{2}).
        pose d1_lookup_contribution_6 := alpha{2}^6 * z_lookup_at_z_omega{2} * (z{2} - Constants.OMEGAFr^(Constants.DOMAIN_SIZE-1)) * s{2}.
        have ->: v{2} * alpha{2}^6 * z_lookup_at_z_omega{2} * (z{2} + -Constants.OMEGAFr^(Constants.DOMAIN_SIZE-1)) * s{2} = v{2} * d1_lookup_contribution_6.
          rewrite left_assoc_mul_g.
          rewrite /d1_lookup_contribution_6.
          do rewrite left_assoc_mul_g.
          by progress.
        pose f_at_z := lookup_selector_at_z{2} * (a_at_z{2} + eta_{2} * b_at_z{2} + eta_{2}^2 * c_at_z{2} + eta_{2}^3 * table_type_at_z{2}).
        pose d1_lookup_contribution_neg_6 := alpha{2}^6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z) * (z{2} - Constants.OMEGAFr^(Constants.DOMAIN_SIZE-1)) * (gamma'{2}*(FieldR.one + beta'{2}) + t_at_z{2} + beta'{2} * t_at_z_omega{2}) * z_lookup{2}.
        pose d1_lookup_contribution_7 := alpha{2}^7 * l_0_at_z{2} * z_lookup{2}.
        pose d1_lookup_contribution_8 := alpha{2}^8 * l_n_minus_one_at_z{2} * z_lookup{2}.
        have ->:((- alpha{2} ^ 6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z) *
              (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) *
              (gamma'{2} * (FieldR.one + beta'{2}) + t_at_z{2} +
               beta'{2} * t_at_z_omega{2})) +
           alpha{2} ^ 7 * l_0_at_z{2} + alpha{2} ^ 8 * l_n_minus_one_at_z{2}) *
          v{2} * z_lookup{2} = v{2} * (G.inv d1_lookup_contribution_neg_6) + v{2} * d1_lookup_contribution_7 + v{2} * d1_lookup_contribution_8.
          rewrite FieldR.ComRing.mulrC.
          rewrite left_assoc_mul_g.
          rewrite left_distrib_add_g.
          rewrite -/d1_lookup_contribution_8.
          rewrite left_distrib_add_g.
          rewrite -/d1_lookup_contribution_7.
          rewrite /d1_lookup_contribution_neg_6.
          simplify.
          pose x := alpha{2}^6 * (FieldR.one + beta'{2}) * (gamma'{2} + f_at_z) *
            (z{2} + - Constants.OMEGAFr ^ (Constants.DOMAIN_SIZE - 1)) *
            (gamma'{2} * (FieldR.one + beta'{2}) + t_at_z{2} + beta'{2} * t_at_z_omega{2}).
          have ->: (-x) * z_lookup{2} = G.inv (x * z_lookup{2}).
            rewrite /EllipticCurve.( * ).
            rewrite -G.expN.
            have H_log_spec := G.log_spec z_lookup{2}.
            case H_log_spec. rewrite /log_spec. progress.
            rewrite FieldR.oppE.
            rewrite -Constants.r_eq_fieldr_p -Constants.order_g.
            rewrite -G.expM -G.expM.
            rewrite -G.expg_modz.
            rewrite modzMmr.
            rewrite G.expg_modz.
            reflexivity.
          have ->: x * z_lookup{2} = d1_lookup_contribution_neg_6 by progress.
          rewrite left_distrib_g left_distrib_g.
          reflexivity.
          rewrite -left_distrib_g -left_distrib_g.
          pose d1_permutation_contribution_5 := alpha{2}^5 * l_0_at_z{2} * z_perm{2}.
          rewrite (FieldR.ComRing.mulrC _ v{2}).
          rewrite left_assoc_mul_g.
          rewrite left_distrib_add_g.
          have ->: l_0_at_z{2} * alpha{2}^5 * z_perm{2} = d1_permutation_contribution_5.
            rewrite FieldR.ComRing.mulrC.
            reflexivity.
          pose d1_permutation_contribution_4 := alpha{2} ^ 4 *
            (z{2} * beta_{2} + gamma{2} + a_at_z{2}) *
            (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_0) + gamma{2} + b_at_z{2}) *
            (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_1) + gamma{2} + c_at_z{2}) *
            (z{2} * beta_{2} * (FieldR.inF Constants.NON_RESIDUE_2) + gamma{2} + d_at_z{2}) * z_perm{2}.
          pose d1 := d1_main_gate +
            d1_custom_gate +
            d1_permutation_contribution_4 +
            G.inv (d1_permutation_contribution_neg) +
            d1_permutation_contribution_5 +
            G.inv (d1_lookup_contribution_neg_6) +
            d1_lookup_contribution_6 +
            d1_lookup_contribution_7 +
            d1_lookup_contribution_8.
          pose f := d0{2} + v{2} * d1 +
            f_v_2 + f_v_3 + f_v_4 + f_v_5 + f_v_6 + f_v_7 + f_v_8 + f_v_9 +
            f_v_10 + f_v_11 + f_v_12 + f_u.
          have ->: d0{2} +
            v{2} *
            (d1_main_gate + d1_custom_gate +
             (G.inv d1_permutation_contribution_neg)) +
            f_v_2 + f_v_3 + f_v_4 + f_v_6 + f_v_7 + f_v_8 + f_v_9 + f_v_11 + f_v_12 +
            (f_v_5 + f_v_10 + f_u +
             v{2} *
             ((G.inv d1_lookup_contribution_neg_6)%G + d1_lookup_contribution_7 +
              d1_lookup_contribution_8) +
             v{2} * d1_lookup_contribution_6 +
             v{2} * (d1_permutation_contribution_4 + d1_permutation_contribution_5)) = f.
            rewrite /f /d1.
            pose x := d1_main_gate + d1_custom_gate.
            do rewrite -assoc_g.
            pose y := (v{2} *
              ((G.inv d1_lookup_contribution_neg_6) +
               (d1_lookup_contribution_7 + d1_lookup_contribution_8)) +
              (v{2} * d1_lookup_contribution_6 +
               v{2} *
               (d1_permutation_contribution_4 + d1_permutation_contribution_5))).
            congr.
            rewrite (g_comm f_u).
            have H_move_left : forall (a b c: g), a + (b + c) = b + (a + c).
              progress. rewrite assoc_g. rewrite (g_comm a0). rewrite assoc_g.
              reflexivity.
            do 11! rewrite (H_move_left _ y).
            rewrite /y.
            have ->: forall k, v{2} *
              (d1_main_gate + (d1_custom_gate + (G.inv d1_permutation_contribution_neg))) +
              (v{2} *
               ((G.inv d1_lookup_contribution_neg_6) +
                (d1_lookup_contribution_7 + d1_lookup_contribution_8)) +
               (v{2} * d1_lookup_contribution_6 +
                v{2} * (d1_permutation_contribution_4 + d1_permutation_contribution_5)) +
               k) = v{2} *
               (d1_main_gate +
                (d1_custom_gate +
                 (d1_permutation_contribution_4 +
                  ((G.inv d1_permutation_contribution_neg) +
                   (d1_permutation_contribution_5 +
                    ((G.inv d1_lookup_contribution_neg_6) +
                     (d1_lookup_contribution_6 +
                      (d1_lookup_contribution_7 + d1_lookup_contribution_8)))))))) + k.
              progress.
              rewrite assoc_g. congr.
              do rewrite -left_distrib_g. congr.
              rewrite -assoc_g. congr.
              rewrite -assoc_g. congr.
              do rewrite -assoc_g.
              do rewrite (H_move_left _ d1_permutation_contribution_4). congr. congr.
              do rewrite (H_move_left _ (G.inv d1_lookup_contribution_neg_6)). congr.
              do rewrite (H_move_left _ d1_lookup_contribution_7). congr.
              do rewrite (H_move_left _ d1_lookup_contribution_6). congr.
              exact g_comm.
            congr. congr. congr. congr.
            do rewrite (H_move_left _ f_v_5). congr. congr. congr. congr. congr.
            rewrite (H_move_left _ f_v_11). congr.
            exact H_move_left.
          pose e := ((quotient_poly_opening_at_z{2} (*t(z)*) + v{2} * r_at_z{2} +
             v{2} ^ 2 * a_at_z{2} + v{2} ^ 3 * b_at_z{2} + v{2} ^ 4 * c_at_z{2} +
             v{2} ^ 5 * d_at_z{2} + v{2} ^ 6 * main_gate_selector_at_z{2} +
             v{2} ^ 7 * sigma_0_at_z{2} + v{2} ^ 8 * sigma_1_at_z{2} +
             v{2} ^ 9 * sigma_2_at_z{2} + v{2} ^ 10 * t_at_z{2} +
             v{2} ^ 11 * lookup_selector_at_z{2} +
             v{2} ^ 12 * table_type_at_z{2} +
             u{2} *
             (v{2} ^ 13 * z_perm_at_z_omega{2} + v{2} ^ 14 * d_at_z_omega{2} +
              v{2} ^ 15 * s_at_z_omega{2} + v{2} ^ 16 * z_lookup_at_z_omega{2} +
              v{2} ^ 17 * t_at_z_omega{2})) *
            g_gen).

          rewrite e_bilin_add_1.
          rewrite assoc_g.
          search G.(^).
          rewrite -(G.exp1 (G.inv w_plus_u_w')).
          rewrite G.expcV -G.expN.
          have H_inv: forall (p: g), (FieldR.inF (-1)) * p = G.inv p.
            progress.
            rewrite gmulE.
            rewrite FieldR.inFK.
            rewrite -Constants.r_eq_fieldr_p -Constants.order_g.
            have H_log := G.log_spec p.
            case H_log. rewrite /log_spec. progress.
            rewrite -G.expM.
            rewrite -G.expg_modz.
            rewrite modzMmr.
            rewrite G.expg_modz.
            search G.(^) G.inv.
            rewrite -G.expN.
            rewrite mulrN1.
            reflexivity.
          have ->: (G.(^) w_plus_u_w' (-1)) = (FieldR.inF (-1)) * w_plus_u_w'.
            rewrite gmulE.
            rewrite FieldR.inFK.
            rewrite -Constants.r_eq_fieldr_p -Constants.order_g.
            have H_log := G.log_spec w_plus_u_w'.
            case H_log. rewrite /log_spec. progress.
            rewrite -H6.
            rewrite -G.expM -G.expM.
            rewrite -G.expg_modz.
            rewrite -modzMmr.
            rewrite G.expg_modz.
            reflexivity.
          rewrite e_bilin_mul_1.
          rewrite H_inv.
          have ->: forall (a b: g), (a + G.inv b = G.e) = (a = b).
            progress.
            case (a0 = b0).
              progress.
              rewrite gaddE.
              have H_log := G.log_spec b0.
              case H_log. rewrite /log_spec. progress.
              rewrite -G.expB.
              rewrite G.exp0.
              by progress.
            (* case a0 <> b0 *)
              progress.
              have H_log_a := G.log_spec a0.
              case H_log_a. rewrite /log_spec. progress.
              have H_log_b := G.log_spec b0.
              case H_log_b. rewrite /log_spec. progress.
              rewrite -G.expN.
              rewrite gaddE.
              rewrite -G.expD.
              rewrite -G.expg_modz.
              rewrite G.expg_eq0.
              rewrite Constants.order_g /Constants.R.
              progress. exact modz_ge0. exact ltz_pmod.
              smt (@G @IntDiv @Utils @Constants).
            pose lhs := z_w_plus_u_z_omega_w' + f + (G.inv e).
            rewrite e_bilin_add_2.
            rewrite e_bilin_add_2.
            have ->: forall (a b c d: g), (a + b = c + d) = (a + G.inv d = c + G.inv b).
              progress.
              rewrite gaddE.
              admit.

(* /*////////////////////////////////////////////////////////////// *)
    (*                             5. Pairing                           *)
    (* //////////////////////////////////////////////////////////////*/ *)

    (* /// @notice Checks the final pairing *)
    (* /// @dev We should check the equation: *)
    (* /// e([W] + u * [W'], [x]_2) = e(z * [W] + u * z * omega * [W'] + [F] - [E], [1]_2), *)
    (* /// where [F] and [E] were computed previously *)
    (* /// *)
    (* /// Also we need to check that e([P1], [x]_2) = e([P2], [1]_2) *)
    (* /// if we have the recursive part of the proof *)
    (* /// where [P1] and [P2] are parts of the recursive proof *)
    (* /// *)
    (* /// We can aggregate both pairings into one for gas optimization: *)
    (* /// e([W] + u * [W'] + u^2 * [P1], [x]_2) = *)
    (* /// e(z * [W] + u * z * omega * [W'] + [F] - [E] + u^2 * [P2], [1]_2) *)
    (* /// *)
    (* /// u is a valid challenge for such aggregation, *)
    (* /// because [P1] and [P2] are used in PI *)
            
qed.      
