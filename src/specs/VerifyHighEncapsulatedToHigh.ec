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


(* old proof *)
      seq 5 5: (
        (failed{1} /\ !isValid{2}) \/
        (!failed{1} /\ isValid{2} /\
        !vk_recursive_flag{1} /\
        _public_input{1} = public_input{2} /\
        _state_poly_0{1} = state_poly_0{2} /\
        _state_poly_1{1} = state_poly_1{2} /\
        _state_poly_2{1} = state_poly_2{2} /\
        _state_poly_3{1} = state_poly_3{2} /\
        _copy_permutation_grand_product{1} = copy_permutation_grand_product{2} /\
        _lookup_s_poly{1} = lookup_s_poly{2} /\
        _lookup_grand_product{1} = lookup_grand_product{2} /\
        _quotient_poly_part_0{1} = quotient_poly_part_0{2} /\
        _quotient_poly_part_1{1} = quotient_poly_part_1{2} /\
        _quotient_poly_part_2{1} = quotient_poly_part_2{2} /\
        _quotient_poly_part_3{1} = quotient_poly_part_3{2} /\
        _state_poly_0_opening_at_z{1} = state_poly_0_opening_at_z{2} /\
        _state_poly_1_opening_at_z{1} = state_poly_1_opening_at_z{2} /\
        _state_poly_2_opening_at_z{1} = state_poly_2_opening_at_z{2} /\
        _state_poly_3_opening_at_z{1} = state_poly_3_opening_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = state_poly_3_opening_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = gate_selector_0_opening_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = copy_permutation_poly_0_opening_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = copy_permutation_poly_1_opening_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = copy_permutation_poly_2_opening_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = copy_permutation_grand_product_opening_at_z_omega{2} /\
        _lookup_s_poly_opening_at_z_omega{1} = lookup_s_poly_opening_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = lookup_grand_product_opening_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = lookup_t_poly_opening_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = lookup_t_poly_opening_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_poly_opening_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = lookup_table_type_poly_opening_at_z{2} /\
        _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = linearisation_poly_opening_at_z{2} /\
        _opening_proof_at_z{1} = opening_proof_at_z{2} /\
        _opening_proof_at_z_omega{1} = opening_proof_at_z_omega{2}
      )).
      inline LoadProof.high.
      rcondf{1} 43. progress. wp. skip. by progress.
      wp. skip. by progress.

      seq 1 100: (
        (failed{1} /\ !isValid{2}) \/
        (!failed{1} /\ isValid{2} /\
        !vk_recursive_flag{1} /\
        _public_input{1} = public_input{2} /\
        _state_poly_0{1} = state_poly_0{2} /\
        _state_poly_1{1} = state_poly_1{2} /\
        _state_poly_2{1} = state_poly_2{2} /\
        _state_poly_3{1} = state_poly_3{2} /\
        _copy_permutation_grand_product{1} = copy_permutation_grand_product{2} /\
        _lookup_s_poly{1} = lookup_s_poly{2} /\
        _lookup_grand_product{1} = lookup_grand_product{2} /\
        _quotient_poly_part_0{1} = quotient_poly_part_0{2} /\
        _quotient_poly_part_1{1} = quotient_poly_part_1{2} /\
        _quotient_poly_part_2{1} = quotient_poly_part_2{2} /\
        _quotient_poly_part_3{1} = quotient_poly_part_3{2} /\
        _state_poly_0_opening_at_z{1} = state_poly_0_opening_at_z{2} /\
        _state_poly_1_opening_at_z{1} = state_poly_1_opening_at_z{2} /\
        _state_poly_2_opening_at_z{1} = state_poly_2_opening_at_z{2} /\
        _state_poly_3_opening_at_z{1} = state_poly_3_opening_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = state_poly_3_opening_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = gate_selector_0_opening_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = copy_permutation_poly_0_opening_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = copy_permutation_poly_1_opening_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = copy_permutation_poly_2_opening_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = copy_permutation_grand_product_opening_at_z_omega{2} /\
        _lookup_s_poly_opening_at_z_omega{1} = lookup_s_poly_opening_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = lookup_grand_product_opening_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = lookup_t_poly_opening_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = lookup_t_poly_opening_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_poly_opening_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = lookup_table_type_poly_opening_at_z{2} /\
        _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = linearisation_poly_opening_at_z{2} /\
        _opening_proof_at_z{1} = opening_proof_at_z{2} /\
        _opening_proof_at_z_omega{1} = opening_proof_at_z_omega{2} /\
        state_alpha{1} = state_alpha{2} /\
        state_beta{1} = state_beta{2} /\
        state_beta_lookup{1} = state_beta_lookup{2} /\
        state_gamma{1} = state_gamma{2} /\
        state_gamma_lookup{1} = state_gamma_lookup{2} /\
        state_eta{1} = state_eta{2} /\
        state_z{1} = state_z{2} /\
        state_z_in_domain{1} = state_z_in_domain{2} /\
        state_v{1} = state_v{2} /\
        state_u{1} = state_u{2}
      )).
      inline InitializeTranscript.high.
      case (failed{1}).
      conseq (_: (failed{1} /\ !isValid{2}) ==> (failed{1} /\ !isValid{2})). progress. by case H; progress.
      progress. left. by case H; progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      seq 10 10: #pre. wp. skip. by progress.
      wp. skip. by progress.

      conseq (_ : (
   !failed{1} /\
   isValid{2} /\
   !vk_recursive_flag{1} /\
   _public_input{1} = public_input{2} /\
   _state_poly_0{1} = state_poly_0{2} /\
   _state_poly_1{1} = state_poly_1{2} /\
   _state_poly_2{1} = state_poly_2{2} /\
   _state_poly_3{1} = state_poly_3{2} /\
   _copy_permutation_grand_product{1} = copy_permutation_grand_product{2} /\
   _lookup_s_poly{1} = lookup_s_poly{2} /\
   _lookup_grand_product{1} = lookup_grand_product{2} /\
   _quotient_poly_part_0{1} = quotient_poly_part_0{2} /\
   _quotient_poly_part_1{1} = quotient_poly_part_1{2} /\
   _quotient_poly_part_2{1} = quotient_poly_part_2{2} /\
   _quotient_poly_part_3{1} = quotient_poly_part_3{2} /\
   _state_poly_0_opening_at_z{1} = state_poly_0_opening_at_z{2} /\
   _state_poly_1_opening_at_z{1} = state_poly_1_opening_at_z{2} /\
   _state_poly_2_opening_at_z{1} = state_poly_2_opening_at_z{2} /\
   _state_poly_3_opening_at_z{1} = state_poly_3_opening_at_z{2} /\
   _state_poly_3_opening_at_z_omega{1} = state_poly_3_opening_at_z_omega{2} /\
   _gate_selector_0_opening_at_z{1} = gate_selector_0_opening_at_z{2} /\
   _copy_permutation_poly_0_opening_at_z{1} =
   copy_permutation_poly_0_opening_at_z{2} /\
   _copy_permutation_poly_1_opening_at_z{1} =
   copy_permutation_poly_1_opening_at_z{2} /\
   _copy_permutation_poly_2_opening_at_z{1} =
   copy_permutation_poly_2_opening_at_z{2} /\
   _copy_permutation_grand_product_opening_at_z_omega{1} =
   copy_permutation_grand_product_opening_at_z_omega{2} /\
   _lookup_s_poly_opening_at_z_omega{1} = lookup_s_poly_opening_at_z_omega{2} /\
   _lookup_grand_product_opening_at_z_omega{1} =
   lookup_grand_product_opening_at_z_omega{2} /\
   _lookup_t_poly_opening_at_z{1} = lookup_t_poly_opening_at_z{2} /\
   _lookup_t_poly_opening_at_z_omega{1} = lookup_t_poly_opening_at_z_omega{2} /\
   _lookup_selector_poly_opening_at_z{1} =
   lookup_selector_poly_opening_at_z{2} /\
   _lookup_table_type_poly_opening_at_z{1} =
   lookup_table_type_poly_opening_at_z{2} /\
   _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
   _linearisation_poly_opening_at_z{1} = linearisation_poly_opening_at_z{2} /\
   _opening_proof_at_z{1} = opening_proof_at_z{2} /\
   _opening_proof_at_z_omega{1} = opening_proof_at_z_omega{2}
      ) ==> (
!failed{1} /\
  isValid{2} /\
  !vk_recursive_flag{1} /\
  _public_input{1} = public_input{2} /\
  _state_poly_0{1} = state_poly_0{2} /\
  _state_poly_1{1} = state_poly_1{2} /\
  _state_poly_2{1} = state_poly_2{2} /\
  _state_poly_3{1} = state_poly_3{2} /\
  _copy_permutation_grand_product{1} = copy_permutation_grand_product{2} /\
  _lookup_s_poly{1} = lookup_s_poly{2} /\
  _lookup_grand_product{1} = lookup_grand_product{2} /\
  _quotient_poly_part_0{1} = quotient_poly_part_0{2} /\
  _quotient_poly_part_1{1} = quotient_poly_part_1{2} /\
  _quotient_poly_part_2{1} = quotient_poly_part_2{2} /\
  _quotient_poly_part_3{1} = quotient_poly_part_3{2} /\
  _state_poly_0_opening_at_z{1} = state_poly_0_opening_at_z{2} /\
  _state_poly_1_opening_at_z{1} = state_poly_1_opening_at_z{2} /\
  _state_poly_2_opening_at_z{1} = state_poly_2_opening_at_z{2} /\
  _state_poly_3_opening_at_z{1} = state_poly_3_opening_at_z{2} /\
  _state_poly_3_opening_at_z_omega{1} = state_poly_3_opening_at_z_omega{2} /\
  _gate_selector_0_opening_at_z{1} = gate_selector_0_opening_at_z{2} /\
  _copy_permutation_poly_0_opening_at_z{1} =
  copy_permutation_poly_0_opening_at_z{2} /\
  _copy_permutation_poly_1_opening_at_z{1} =
  copy_permutation_poly_1_opening_at_z{2} /\
  _copy_permutation_poly_2_opening_at_z{1} =
  copy_permutation_poly_2_opening_at_z{2} /\
  _copy_permutation_grand_product_opening_at_z_omega{1} =
  copy_permutation_grand_product_opening_at_z_omega{2} /\
  _lookup_s_poly_opening_at_z_omega{1} = lookup_s_poly_opening_at_z_omega{2} /\
  _lookup_grand_product_opening_at_z_omega{1} =
  lookup_grand_product_opening_at_z_omega{2} /\
  _lookup_t_poly_opening_at_z{1} = lookup_t_poly_opening_at_z{2} /\
  _lookup_t_poly_opening_at_z_omega{1} = lookup_t_poly_opening_at_z_omega{2} /\
  _lookup_selector_poly_opening_at_z{1} =
  lookup_selector_poly_opening_at_z{2} /\
  _lookup_table_type_poly_opening_at_z{1} =
  lookup_table_type_poly_opening_at_z{2} /\
  _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
  _linearisation_poly_opening_at_z{1} = linearisation_poly_opening_at_z{2} /\
  _opening_proof_at_z{1} = opening_proof_at_z{2} /\
  _opening_proof_at_z_omega{1} = opening_proof_at_z_omega{2} /\
  ={state_alpha, state_beta, state_beta_lookup, state_gamma,
      state_gamma_lookup, state_eta, state_z, state_z_in_domain, state_v,
      state_u}
      )).
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
      progress.
      sp 34 0.
      seq 4 4: (
        #pre /\
        ={state0_0, state1_0, state0_1, state1_1}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_2, state1_2, state0_3, state1_3}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_4, state1_4, state0_5, state1_5}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_6, state1_6, state0_7, state1_7}
      ). wp. skip. by progress.
      seq 3 3: (
        #pre /\
        ={state0_8, state1_8} /\
        stateEta{1} = state_eta{2}
      ). wp. skip. by progress.
      seq 3 3: (
        #pre /\
        ={state0_9, state1_9, state0_10}
      ). wp. skip. by progress.
      seq 3 3: (
        #pre /\
        ={state1_10} /\
        stateBeta{1} = state_beta{2} /\
        stateGamma{1} = state_gamma{2}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_11, state1_11, state0_12, state1_12}
      ). wp. skip. by progress.
      seq 2 2: (
        #pre /\
        stateBetaLookup{1} = state_beta_lookup{2} /\
        stateGammaLookup{1} = state_gamma_lookup{2}
      ). wp. skip. by progress.
      seq 5 5: (
        #pre /\
        ={state0_13, state1_13, state0_14, state1_14} /\
        stateAlpha{1} = state_alpha{2}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_15, state1_15, state0_16, state1_16}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_17, state1_17, state0_18, state1_18}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_19, state1_19, state0_20, state1_20}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_21, state1_21, state0_22, state1_22}
      ). wp. skip. by progress.
      seq 2 2: (
        #pre /\
        stateZ{1} = state_z{2} /\
        stateZInDomain{1} = state_z_in_domain{2}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_23, state1_23, state0_24, state1_24}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_25, state1_25, state0_26, state1_26}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_27, state1_27, state0_28, state1_28}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_29, state1_29, state0_30, state1_30}
      ). wp. skip. by progress.        
      seq 4 4: (
        #pre /\
        ={state0_31, state1_31, state0_32, state1_32}
      ). wp. skip. by progress.        
      seq 4 4: (
        #pre /\
        ={state0_33, state1_33, state0_34, state1_34}
      ). wp. skip. by progress.        
      seq 4 4: (
        #pre /\
        ={state0_35, state1_35, state0_36, state1_36}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_37, state1_37, state0_38, state1_38}
      ). wp. skip. by progress.
      seq 5 5: (
        #pre /\
        ={state0_39, state1_39, state0_40, state1_40} /\
        stateV{1} = state_v{2}
      ). wp. skip. by progress.
      seq 4 4: (
        #pre /\
        ={state0_41, state1_41, state0_42, state1_42}
      ). wp. skip. by progress.
      wp. skip. by progress.
      seq 2 7: (
        (failed{1} /\ !isValid{2}) \/
        (!failed{1} /\ isValid{2} /\
        !vk_recursive_flag{1} /\
        _public_input{1} = public_input{2} /\
        _state_poly_0{1} = state_poly_0{2} /\
        _state_poly_1{1} = state_poly_1{2} /\
        _state_poly_2{1} = state_poly_2{2} /\
        _state_poly_3{1} = state_poly_3{2} /\
        _copy_permutation_grand_product{1} = copy_permutation_grand_product{2} /\
        _lookup_s_poly{1} = lookup_s_poly{2} /\
        _lookup_grand_product{1} = lookup_grand_product{2} /\
        _quotient_poly_part_0{1} = quotient_poly_part_0{2} /\
        _quotient_poly_part_1{1} = quotient_poly_part_1{2} /\
        _quotient_poly_part_2{1} = quotient_poly_part_2{2} /\
        _quotient_poly_part_3{1} = quotient_poly_part_3{2} /\
        _state_poly_0_opening_at_z{1} = state_poly_0_opening_at_z{2} /\
        _state_poly_1_opening_at_z{1} = state_poly_1_opening_at_z{2} /\
        _state_poly_2_opening_at_z{1} = state_poly_2_opening_at_z{2} /\
        _state_poly_3_opening_at_z{1} = state_poly_3_opening_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = state_poly_3_opening_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = gate_selector_0_opening_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = copy_permutation_poly_0_opening_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = copy_permutation_poly_1_opening_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = copy_permutation_poly_2_opening_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = copy_permutation_grand_product_opening_at_z_omega{2} /\
        _lookup_s_poly_opening_at_z_omega{1} = lookup_s_poly_opening_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = lookup_grand_product_opening_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = lookup_t_poly_opening_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = lookup_t_poly_opening_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_poly_opening_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = lookup_table_type_poly_opening_at_z{2} /\
        _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = linearisation_poly_opening_at_z{2} /\
        _opening_proof_at_z{1} = opening_proof_at_z{2} /\
        _opening_proof_at_z_omega{1} = opening_proof_at_z_omega{2} /\
        state_alpha{1} = state_alpha{2} /\
        state_beta{1} = state_beta{2} /\
        state_beta_lookup{1} = state_beta_lookup{2} /\
        state_gamma{1} = state_gamma{2} /\
        state_gamma_lookup{1} = state_gamma_lookup{2} /\
        state_eta{1} = state_eta{2} /\
        state_z{1} = state_z{2} /\
        state_z_in_domain{1} = state_z_in_domain{2} /\
        state_v{1} = state_v{2} /\
        state_u{1} = state_u{2} /\
        l0_at_z{1} = l0_at_z{2} /\
        ln_minus_one_at_z{1} = ln_minus_one_at_z{2} /\
        beta_plus_one{1} = beta_plus_one{2} /\
        beta_gamma_plus_gamma{1} = beta_gamma_plus_gamma{2} /\
        z_minus_last_omega{1} = z_minus_last_omega{2} /\
        alpha2{1} = state_alpha{2}^2 /\
        alpha3{1} = state_alpha{2}^3 /\
        alpha4{1} = state_alpha{2}^4 /\
        alpha5{1} = state_alpha{2}^5 /\
        alpha6{1} = state_alpha{2}^6 /\
        alpha7{1} = state_alpha{2}^7 /\
        alpha8{1} = state_alpha{2}^8
      )).
      case (failed{1}).
      conseq (_: (failed{1} /\ !isValid{2}) ==> (failed{1} /\ !isValid{2})). progress. by case H; progress.
      progress. left. by case H; progress.
      inline VerifyQuotientEvaluation.high.
      wp. skip. progress. rewrite H0. by progress.
      left. assumption.
      rewrite H0. by progress.

      inline VerifyQuotientEvaluation.high.
      wp. skip. progress.
      case H. by progress. progress.
      rewrite H2. progress.
      rewrite H1. by progress.
      rewrite H0. progress.
      case H. by progress. progress.
      rewrite H1. progress.
      rewrite H2. progress.
      rewrite H3. progress.
      smt ().

      seq 1 6: (
        (failed{1} /\ !isValid{2}) \/
        (!failed{1} /\ isValid{2} /\
        !vk_recursive_flag{1} /\
        _public_input{1} = public_input{2} /\
        _state_poly_0{1} = state_poly_0{2} /\
        _state_poly_1{1} = state_poly_1{2} /\
        _state_poly_2{1} = state_poly_2{2} /\
        _state_poly_3{1} = state_poly_3{2} /\
        _copy_permutation_grand_product{1} = copy_permutation_grand_product{2} /\
        _lookup_s_poly{1} = lookup_s_poly{2} /\
        _lookup_grand_product{1} = lookup_grand_product{2} /\
        _quotient_poly_part_0{1} = quotient_poly_part_0{2} /\
        _quotient_poly_part_1{1} = quotient_poly_part_1{2} /\
        _quotient_poly_part_2{1} = quotient_poly_part_2{2} /\
        _quotient_poly_part_3{1} = quotient_poly_part_3{2} /\
        _state_poly_0_opening_at_z{1} = state_poly_0_opening_at_z{2} /\
        _state_poly_1_opening_at_z{1} = state_poly_1_opening_at_z{2} /\
        _state_poly_2_opening_at_z{1} = state_poly_2_opening_at_z{2} /\
        _state_poly_3_opening_at_z{1} = state_poly_3_opening_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = state_poly_3_opening_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = gate_selector_0_opening_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = copy_permutation_poly_0_opening_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = copy_permutation_poly_1_opening_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = copy_permutation_poly_2_opening_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = copy_permutation_grand_product_opening_at_z_omega{2} /\
        _lookup_s_poly_opening_at_z_omega{1} = lookup_s_poly_opening_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = lookup_grand_product_opening_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = lookup_t_poly_opening_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = lookup_t_poly_opening_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_poly_opening_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = lookup_table_type_poly_opening_at_z{2} /\
        _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = linearisation_poly_opening_at_z{2} /\
        _opening_proof_at_z{1} = opening_proof_at_z{2} /\
        _opening_proof_at_z_omega{1} = opening_proof_at_z_omega{2} /\
        state_alpha{1} = state_alpha{2} /\
        state_beta{1} = state_beta{2} /\
        state_beta_lookup{1} = state_beta_lookup{2} /\
        state_gamma{1} = state_gamma{2} /\
        state_gamma_lookup{1} = state_gamma_lookup{2} /\
        state_eta{1} = state_eta{2} /\
        state_z{1} = state_z{2} /\
        state_z_in_domain{1} = state_z_in_domain{2} /\
        state_v{1} = state_v{2} /\
        state_u{1} = state_u{2} /\
        l0_at_z{1} = l0_at_z{2} /\
        ln_minus_one_at_z{1} = ln_minus_one_at_z{2} /\
        beta_plus_one{1} = beta_plus_one{2} /\
        beta_gamma_plus_gamma{1} = beta_gamma_plus_gamma{2} /\
        z_minus_last_omega{1} = z_minus_last_omega{2} /\
        alpha2{1} = state_alpha{2}^2 /\
        alpha3{1} = state_alpha{2}^3 /\
        alpha4{1} = state_alpha{2}^4 /\
        alpha5{1} = state_alpha{2}^5 /\
        alpha6{1} = state_alpha{2}^6 /\
        alpha7{1} = state_alpha{2}^7 /\
        alpha8{1} = state_alpha{2}^8 /\
        query_at_z_0{1} = query_at_z_0{2} /\
        query_at_z_1{1} = query_at_z_1{2} /\
        copy_permutation_first_aggregated_commitment_coeff{1} = copy_permutation_first_aggregated_commitment_coeff{2} /\
        lookupSFirstAggregatedCommitment{1} = lookupSFirstAggregatedCommitment{2} /\
        lookupGrandProductFirstAggregatedCoefficient{1} = lookupGrandProductFirstAggregatedCoefficient{2} /\
        query_t_poly_aggregated{1} = query_t_poly_aggregated{2}
      )).
      case (failed{1}).
      conseq (_: (failed{1} /\ !isValid{2}) ==> (failed{1} /\ !isValid{2})).
      progress. by case H; progress.
      progress. left. rewrite H1 H2. by trivial.
      inline PrepareQueries.high.
      wp. skip. by progress.

      inline PrepareQueries.high.
      wp. skip. progress. right.
      case H. by progress. by progress.

      seq 1 58 : (
        (failed{1} /\ !isValid{2}) \/
        (!failed{1} /\ isValid{2} /\
        !vk_recursive_flag{1} /\
        _public_input{1} = public_input{2} /\
        _state_poly_0{1} = state_poly_0{2} /\
        _state_poly_1{1} = state_poly_1{2} /\
        _state_poly_2{1} = state_poly_2{2} /\
        _state_poly_3{1} = state_poly_3{2} /\
        _copy_permutation_grand_product{1} = copy_permutation_grand_product{2} /\
        _lookup_s_poly{1} = lookup_s_poly{2} /\
        _lookup_grand_product{1} = lookup_grand_product{2} /\
        _quotient_poly_part_0{1} = quotient_poly_part_0{2} /\
        _quotient_poly_part_1{1} = quotient_poly_part_1{2} /\
        _quotient_poly_part_2{1} = quotient_poly_part_2{2} /\
        _quotient_poly_part_3{1} = quotient_poly_part_3{2} /\
        _state_poly_0_opening_at_z{1} = state_poly_0_opening_at_z{2} /\
        _state_poly_1_opening_at_z{1} = state_poly_1_opening_at_z{2} /\
        _state_poly_2_opening_at_z{1} = state_poly_2_opening_at_z{2} /\
        _state_poly_3_opening_at_z{1} = state_poly_3_opening_at_z{2} /\
        _state_poly_3_opening_at_z_omega{1} = state_poly_3_opening_at_z_omega{2} /\
        _gate_selector_0_opening_at_z{1} = gate_selector_0_opening_at_z{2} /\
        _copy_permutation_poly_0_opening_at_z{1} = copy_permutation_poly_0_opening_at_z{2} /\
        _copy_permutation_poly_1_opening_at_z{1} = copy_permutation_poly_1_opening_at_z{2} /\
        _copy_permutation_poly_2_opening_at_z{1} = copy_permutation_poly_2_opening_at_z{2} /\
        _copy_permutation_grand_product_opening_at_z_omega{1} = copy_permutation_grand_product_opening_at_z_omega{2} /\
        _lookup_s_poly_opening_at_z_omega{1} = lookup_s_poly_opening_at_z_omega{2} /\
        _lookup_grand_product_opening_at_z_omega{1} = lookup_grand_product_opening_at_z_omega{2} /\
        _lookup_t_poly_opening_at_z{1} = lookup_t_poly_opening_at_z{2} /\
        _lookup_t_poly_opening_at_z_omega{1} = lookup_t_poly_opening_at_z_omega{2} /\
        _lookup_selector_poly_opening_at_z{1} = lookup_selector_poly_opening_at_z{2} /\
        _lookup_table_type_poly_opening_at_z{1} = lookup_table_type_poly_opening_at_z{2} /\
        _quotient_poly_opening_at_z{1} = quotient_poly_opening_at_z{2} /\
        _linearisation_poly_opening_at_z{1} = linearisation_poly_opening_at_z{2} /\
        _opening_proof_at_z{1} = opening_proof_at_z{2} /\
        _opening_proof_at_z_omega{1} = opening_proof_at_z_omega{2} /\
        state_alpha{1} = state_alpha{2} /\
        state_beta{1} = state_beta{2} /\
        state_beta_lookup{1} = state_beta_lookup{2} /\
        state_gamma{1} = state_gamma{2} /\
        state_gamma_lookup{1} = state_gamma_lookup{2} /\
        state_eta{1} = state_eta{2} /\
        state_z{1} = state_z{2} /\
        state_z_in_domain{1} = state_z_in_domain{2} /\
        state_v{1} = state_v{2} /\
        state_u{1} = state_u{2} /\
        l0_at_z{1} = l0_at_z{2} /\
        ln_minus_one_at_z{1} = ln_minus_one_at_z{2} /\
        beta_plus_one{1} = beta_plus_one{2} /\
        beta_gamma_plus_gamma{1} = beta_gamma_plus_gamma{2} /\
        z_minus_last_omega{1} = z_minus_last_omega{2} /\
        alpha2{1} = state_alpha{2}^2 /\
        alpha3{1} = state_alpha{2}^3 /\
        alpha4{1} = state_alpha{2}^4 /\
        alpha5{1} = state_alpha{2}^5 /\
        alpha6{1} = state_alpha{2}^6 /\
        alpha7{1} = state_alpha{2}^7 /\
        alpha8{1} = state_alpha{2}^8 /\
        query_at_z_0{1} = query_at_z_0{2} /\
        query_at_z_1{1} = query_at_z_1{2} /\
        copy_permutation_first_aggregated_commitment_coeff{1} = copy_permutation_first_aggregated_commitment_coeff{2} /\
        lookupSFirstAggregatedCommitment{1} = lookupSFirstAggregatedCommitment{2} /\
        lookupGrandProductFirstAggregatedCoefficient{1} = lookupGrandProductFirstAggregatedCoefficient{2} /\
        query_t_poly_aggregated{1} = query_t_poly_aggregated{2} /\
        aggregatedAtZSlot{1} = aggregatedAtZSlot{2} /\
        aggregatedOpeningAtZSlot{1} = aggregatedOpeningAtZSlot{2} /\
        aggregatedAtZOmegaSlot{1} = aggregatedAtZOmegaSlot{2} /\
        aggregatedOpeningAtZOmega{1} = aggregatedOpeningAtZOmega{2} /\
        pairingPairWithGeneratorSlot{1} = pairing_pair_with_generator{2} /\
        pairingBufferPointSlot{1} = pairing_buffer_point{2}
      )).
      case (failed{1}).
      conseq (_ : (failed{1} /\ !isValid{2}) ==> (failed{1} /\ !isValid{2})).
      progress. by case H; progress.
      progress. left. by case H; progress.
      inline PrepareAggregatedCommitment.high.
      wp. skip. by progress.

      inline PrepareAggregatedCommitment.high.
      sp. skip. progress.
      right.
      case H. by progress. by progress.

      case (failed{1}).
      conseq (_ : (failed{1} /\ !isValid{2}) ==> (failed{1} /\ !isValid{2})).
      progress. by case H; progress.
      progress. smt ().
      inline FinalPairing.high.
      wp. skip. progress. left. assumption.
      left. assumption.

      inline FinalPairing.high.
      wp. skip. progress.
      rewrite H0. progress. case H. by progress. by progress.
      rewrite H0. progress. case H. by progress. progress.
      rewrite H2. by progress.
qed.      
