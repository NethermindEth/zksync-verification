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

lemma verify_mid_canonicalisation:
    equiv [
      Verify.mid ~ Verify.mid:
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
    ].
    proof.
    proc.
      simplify.
      cfold {1} 1.
      cfold {2} 1.
      cfold {1} 1.
      cfold {2} 1.
      sp.
      seq 1 1: (
        ={
          load_proof_opt,
          failed,
          vk_gate_setup_0X, vk_gate_setup_0Y,
          vk_gate_setup_1X, vk_gate_setup_1Y,
          vk_gate_setup_2X, vk_gate_setup_2Y,
          vk_gate_setup_3X, vk_gate_setup_3Y,
          vk_gate_setup_4X, vk_gate_setup_4Y,
          vk_gate_setup_5X, vk_gate_setup_5Y,
          vk_gate_setup_6X, vk_gate_setup_6Y,
          vk_gate_setup_7X, vk_gate_setup_7Y,
          vk_gate_selectors_0X, vk_gate_selectors_0Y,
          vk_gate_selectors_1X, vk_gate_selectors_1Y,
          vk_permutation_0X, vk_permutation_0Y,
          vk_permutation_1X, vk_permutation_1Y,
          vk_permutation_2X, vk_permutation_2Y,
          vk_permutation_3X, vk_permutation_3Y,
          vk_lookup_table_0X, vk_lookup_table_0Y,
          vk_lookup_table_1X, vk_lookup_table_1Y,
          vk_lookup_table_2X, vk_lookup_table_2Y,
          vk_lookup_table_3X, vk_lookup_table_3Y,
          vk_lookup_selector_X, vk_lookup_selector_Y,
          vk_lookup_table_type_X, vk_lookup_table_type_Y,
          vk_recursive_flag
        }
      ).
      inline LoadProof.mid.
      seq 38 38 : (
        ={failed} /\
        ={public_input_length_in_words0} /\
        public_input0{2} = public_input0{1} %% (2^253) /\
        ={proof_length_in_words0} /\
        state_poly_00{2}.`1 = state_poly_00{1}.`1 %% FieldQ.p /\
        state_poly_00{2}.`2 = state_poly_00{1}.`2 %% FieldQ.p /\
        state_poly_10{2}.`1 = state_poly_10{1}.`1 %% FieldQ.p /\
        state_poly_10{2}.`2 = state_poly_10{1}.`2 %% FieldQ.p /\
        state_poly_20{2}.`1 = state_poly_20{1}.`1 %% FieldQ.p /\
        state_poly_20{2}.`2 = state_poly_20{1}.`2 %% FieldQ.p /\
        state_poly_30{2}.`1 = state_poly_30{1}.`1 %% FieldQ.p /\
        state_poly_30{2}.`2 = state_poly_30{1}.`2 %% FieldQ.p /\
        copy_permutation_grand_product0{2}.`1 = copy_permutation_grand_product0{1}.`1 %% FieldQ.p /\
        copy_permutation_grand_product0{2}.`2 = copy_permutation_grand_product0{1}.`2 %% FieldQ.p /\
        lookup_s_poly0{2}.`1 = lookup_s_poly0{1}.`1 %% FieldQ.p /\
        lookup_s_poly0{2}.`2 = lookup_s_poly0{1}.`2 %% FieldQ.p /\
        lookup_grand_product0{2}.`1 = lookup_grand_product0{1}.`1 %% FieldQ.p /\
        lookup_grand_product0{2}.`2 = lookup_grand_product0{1}.`2 %% FieldQ.p /\
        quotient_poly_part_00{2}.`1 = quotient_poly_part_00{1}.`1 %% FieldQ.p /\
        quotient_poly_part_00{2}.`2 = quotient_poly_part_00{1}.`2 %% FieldQ.p /\
        quotient_poly_part_10{2}.`1 = quotient_poly_part_10{1}.`1 %% FieldQ.p /\
        quotient_poly_part_10{2}.`2 = quotient_poly_part_10{1}.`2 %% FieldQ.p /\
        quotient_poly_part_20{2}.`1 = quotient_poly_part_20{1}.`1 %% FieldQ.p /\
        quotient_poly_part_20{2}.`2 = quotient_poly_part_20{1}.`2 %% FieldQ.p /\
        quotient_poly_part_30{2}.`1 = quotient_poly_part_30{1}.`1 %% FieldQ.p /\
        quotient_poly_part_30{2}.`2 = quotient_poly_part_30{1}.`2 %% FieldQ.p /\
        state_poly_0_opening_at_z0{2} = state_poly_0_opening_at_z0{1} %% FieldR.p /\
        state_poly_1_opening_at_z0{2} = state_poly_1_opening_at_z0{1} %% FieldR.p /\
        state_poly_2_opening_at_z0{2} = state_poly_2_opening_at_z0{1} %% FieldR.p /\
        state_poly_3_opening_at_z0{2} = state_poly_3_opening_at_z0{1} %% FieldR.p /\
        state_poly_3_opening_at_z_omega0{2} = state_poly_3_opening_at_z_omega0{1} %% FieldR.p /\
        gate_selector_0_opening_at_z0{2} = gate_selector_0_opening_at_z0{1} %% FieldR.p /\
        copy_permutation_poly_0_opening_at_z0{2} = copy_permutation_poly_0_opening_at_z0{1} %% FieldR.p /\
        copy_permutation_poly_1_opening_at_z0{2} = copy_permutation_poly_1_opening_at_z0{1} %% FieldR.p /\
        copy_permutation_poly_2_opening_at_z0{2} = copy_permutation_poly_2_opening_at_z0{1} %% FieldR.p /\
        copy_permutation_grand_product_opening_at_z_omega0{2} = copy_permutation_grand_product_opening_at_z_omega0{1} %% FieldR.p /\
        lookup_s_poly_opening_at_z_omega0{2} = lookup_s_poly_opening_at_z_omega0{1} %% FieldR.p /\
        lookup_grand_product_opening_at_z_omega0{2} = lookup_grand_product_opening_at_z_omega0{1} %% FieldR.p /\
        lookup_t_poly_opening_at_z0{2} = lookup_t_poly_opening_at_z0{1} %% FieldR.p /\
        lookup_t_poly_opening_at_z_omega0{2} = lookup_t_poly_opening_at_z_omega0{1} %% FieldR.p /\
        lookup_selector_poly_opening_at_z0{2} = lookup_selector_poly_opening_at_z0{1} %% FieldR.p /\
        lookup_table_type_poly_opening_at_z0{2} = lookup_table_type_poly_opening_at_z0{1} %% FieldR.p /\
        quotient_poly_opening_at_z0{2} = quotient_poly_opening_at_z0{1} %% FieldR.p /\
        linearisation_poly_opening_at_z0{2} = linearisation_poly_opening_at_z0{1} %% FieldR.p /\
        opening_proof_at_z0{2}.`1 = opening_proof_at_z0{1}.`1 %% FieldQ.p /\
        opening_proof_at_z0{2}.`2 = opening_proof_at_z0{1}.`2 %% FieldQ.p /\
        opening_proof_at_z_omega0{2}.`1 = opening_proof_at_z_omega0{1}.`1 %% FieldQ.p /\
        opening_proof_at_z_omega0{2}.`2 = opening_proof_at_z_omega0{1}.`2 %% FieldQ.p /\
        ={recursive_proof_length_in_words0} /\
        recursive_part_p10{2}.`1 = recursive_part_p10{1}.`1 %% FieldQ.p /\
        recursive_part_p10{2}.`2 = recursive_part_p10{1}.`2 %% FieldQ.p /\
        recursive_part_p20{2}.`1 = recursive_part_p20{1}.`1 %% FieldQ.p /\
        recursive_part_p20{2}.`2 = recursive_part_p20{1}.`2 %% FieldQ.p /\
        ={
          vk_gate_setup_0X, vk_gate_setup_0Y,
          vk_gate_setup_1X, vk_gate_setup_1Y,
          vk_gate_setup_2X, vk_gate_setup_2Y,
          vk_gate_setup_3X, vk_gate_setup_3Y,
          vk_gate_setup_4X, vk_gate_setup_4Y,
          vk_gate_setup_5X, vk_gate_setup_5Y,
          vk_gate_setup_6X, vk_gate_setup_6Y,
          vk_gate_setup_7X, vk_gate_setup_7Y,
          vk_gate_selectors_0X, vk_gate_selectors_0Y,
          vk_gate_selectors_1X, vk_gate_selectors_1Y,
          vk_permutation_0X, vk_permutation_0Y,
          vk_permutation_1X, vk_permutation_1Y,
          vk_permutation_2X, vk_permutation_2Y,
          vk_permutation_3X, vk_permutation_3Y,
          vk_lookup_table_0X, vk_lookup_table_0Y,
          vk_lookup_table_1X, vk_lookup_table_1Y,
          vk_lookup_table_2X, vk_lookup_table_2Y,
          vk_lookup_table_3X, vk_lookup_table_3Y,
          vk_lookup_selector_X, vk_lookup_selector_Y,
          vk_lookup_table_type_X, vk_lookup_table_type_Y,
          vk_recursive_flag,
          vk_recursive_flag0
        }
      ).
      wp. skip. by progress.
      seq 2 2: (
        #pre /\
        ={isValid}
      ).
      sp. skip. by progress.
      have H_on_curve: forall (b: bool) (p1 p2: int*int),
        p1.`1 = p2.`1 %% FieldQ.p =>
        p1.`2 = p2.`2 %% FieldQ.p =>
        (b /\ on_curve_int p2) = (b /\ on_curve_int p1).
        progress.
        case b. progress. rewrite /on_curve_int.
        rewrite H H0 Constants.q_eq_fieldq_p.
        rewrite (modzMm p2.`1 p2.`1).
        rewrite (modzMml p2.`1).
        rewrite (modzMm p2.`2 p2.`2).
        reflexivity.
        by progress.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: #pre. wp. skip. progress. exact H_on_curve.
      seq 1 1: (
        #pre /\
        ={ret_recursive_part_p1} /\
        ={ret_recursive_part_p2}
      ).
      case (vk_recursive_flag0{1}).
      rcondt{1} 1. by progress.
      rcondt{2} 1. by progress.
      wp. skip. progress.
      pose b := isValid{2} /\ recursive_proof_length_in_words0{2} = 4.
      have ->: (b /\ on_curve_int recursive_part_p10{1}) = (b /\ on_curve_int recursive_part_p10{2}).
        exact (H_on_curve b recursive_part_p10{2} recursive_part_p10{1}).
      exact H_on_curve.
      rewrite H25. rewrite Constants.q_eq_fieldq_p. rewrite modz_mod. reflexivity.
      rewrite H26. rewrite Constants.q_eq_fieldq_p. rewrite modz_mod. reflexivity.
      rewrite H27. rewrite Constants.q_eq_fieldq_p. rewrite modz_mod. reflexivity.
      rewrite H28. rewrite Constants.q_eq_fieldq_p. rewrite modz_mod. reflexivity.

      rcondf{1} 1. by progress.
      rcondf{2} 1. by progress.
      wp. skip. by progress.

      case (isValid{1}).
      rcondt{1} 1. by progress.
      rcondt{2} 1. by progress.
      wp. skip. rewrite Constants.q_eq_fieldq_p Constants.r_eq_fieldr_p.
      progress.
      rewrite modz_mod; reflexivity.
      rewrite H modz_mod; reflexivity.
      rewrite H0 modz_mod; reflexivity.
      rewrite H1 modz_mod; reflexivity.
      rewrite H2 modz_mod; reflexivity.
      rewrite H3 modz_mod; reflexivity.
      rewrite H4 modz_mod; reflexivity.
      rewrite H5 modz_mod; reflexivity.
      rewrite H6 modz_mod; reflexivity.
      rewrite H7 modz_mod; reflexivity.
      rewrite H8 modz_mod; reflexivity.
      rewrite H9 modz_mod; reflexivity.
      rewrite H10 modz_mod; reflexivity.
      rewrite H11 modz_mod; reflexivity.
      rewrite H12 modz_mod; reflexivity.
      rewrite H13 modz_mod; reflexivity.
      rewrite H14 modz_mod; reflexivity.
      rewrite H15 modz_mod; reflexivity.
      rewrite H16 modz_mod; reflexivity.
      rewrite H17 modz_mod; reflexivity.
      rewrite H18 modz_mod; reflexivity.
      rewrite H19 modz_mod; reflexivity.
      rewrite H20 modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite modz_mod; reflexivity.
      rewrite H21 modz_mod; reflexivity.
      rewrite H22 modz_mod; reflexivity.
      rewrite H23 modz_mod; reflexivity.
      rewrite H24 modz_mod; reflexivity.

      rcondf{1} 1. by progress.
      rcondf{2} 1. by progress.
      wp. skip. by progress.
      seq 1 1: #pre. wp. skip. by progress.
      seq 1 1: (
        #pre /\
        ={
          _public_input,                                      
          _state_poly_0,                                     
          _state_poly_1,                                     
          _state_poly_2,                                     
          _state_poly_3,                                     
          _copy_permutation_grand_product,                   
          _lookup_s_poly,                                    
          _lookup_grand_product,                             
          _quotient_poly_part_0,                             
          _quotient_poly_part_1,                             
          _quotient_poly_part_2,                             
          _quotient_poly_part_3,                             
          _state_poly_0_opening_at_z,                        
          _state_poly_1_opening_at_z,                        
          _state_poly_2_opening_at_z,                        
          _state_poly_3_opening_at_z,                        
          _state_poly_3_opening_at_z_omega,                  
          _gate_selector_0_opening_at_z,                     
          _copy_permutation_poly_0_opening_at_z,             
          _copy_permutation_poly_1_opening_at_z,             
          _copy_permutation_poly_2_opening_at_z,             
          _copy_permutation_grand_product_opening_at_z_omega,
          _lookup_s_poly_opening_at_z_omega,                 
          _lookup_grand_product_opening_at_z_omega,          
          _lookup_t_poly_opening_at_z,                       
          _lookup_t_poly_opening_at_z_omega,                 
          _lookup_selector_poly_opening_at_z,                
          _lookup_table_type_poly_opening_at_z,              
          _quotient_poly_opening_at_z,                       
          _linearisation_poly_opening_at_z,                  
          _opening_proof_at_z,                               
          _opening_proof_at_z_omega,                         
          _recursive_part_p1,                                
          _recursive_part_p2
        }
      ).
      by sim.
      seq 1 1: (
        #pre /\
        ={
          state_alpha,
          state_beta,
          state_beta_lookup,
          state_gamma,
          state_gamma_lookup,
          state_eta,
          state_z,
          state_z_in_domain,
          state_v,
          state_u
        }
      ).
      by sim.
      seq 1 1: (
        #pre /\
        ={
          verify_quotient_evaluation_opt,
          alpha2,
          alpha3,
          alpha4,
          alpha5,
          alpha6,
          alpha7,
          alpha8,
          l0_at_z,
          ln_minus_one_at_z,
          beta_plus_one,
          beta_gamma_plus_gamma,
          z_minus_last_omega
        }
      ).
      by sim.
      seq 1 1 : #pre. by sim.
      seq 1 1 : (
        #pre /\
        ={prepare_queries_opt}
      ). inline PrepareQueries.mid.
      seq 56 56: (
        #pre /\
        ={
          zInDomainSize,
          quotient_poly_part_00,
          quotient_poly_part_10,
          quotient_poly_part_20,
          quotient_poly_part_30,
          stateOpening0AtZ,
          stateOpening1AtZ,
          stateOpening2AtZ,
          stateOpening3AtZ,
          vk_lookup_table_0,
          vk_lookup_table_1,
          vk_lookup_table_2,
          vk_lookup_table_3,
          state_eta0,
          vk_gate_setup_0,
          vk_gate_setup_1,
          vk_gate_setup_2,
          vk_gate_setup_3,
          vk_gate_setup_4,
          vk_gate_setup_5,
          vk_gate_setup_6,
          vk_gate_setup_7,
          poly3_omega,
          v,
          z,
          gate_selector_0_opening,
          alpha,
          alpha20,          
          alpha30,
          alpha40,
          alpha50,
          alpha60,
          alpha70,
          alpha80,
          state_beta0,
          gamma,
          vk_gate_selector_1,
          vk_permutation_3,
          gp_omega,
          l0AtZ,
          poly0_opening,
          poly1_opening,
          poly2_opening,
          proofLookupGrandProductOpeningAtZOmega,
          zMinusLastOmega,
          proofLookupTPolyOpeningAtZOmega,
          betaLookup,
          proofLookupTPolyOpeningAtZ,
          betaGammaPlusGamma,
          proofLookupSelectorPolyOpeningAtZ,
          proofLookupTableTypePolyOpeningAtZ,
          gammaLookup,
          betaPlusOne,
          lNMinusOneAtZ,
          failed0,
          query_at_z_00
        }
      ). wp. skip. by progress.
      seq 3 3: (
        #pre /\
        ={query_at_z_0_opt}
      ). by sim.
      seq 4 4: (
        #pre /\
        ={currentZ}
      ). by sim.
      seq 4 4: #pre. by sim.
      seq 3 3: (
        #pre /\
        ={query_at_z_1_opt, query_at_z_10}
      ). by sim.
      seq 3 3: #pre. by sim.
      seq 3 3: (
        #pre /\
        ={result, copy_permutation_first_aggregated_commitment_coeff0}
      ). by sim.
      seq 1 1: (
        #pre /\
        ={lookupSFirstAggregatedCommitment, lookupGrandProductFirstAggregatedCoefficient}
      ). by sim.
      seq 6 6: (
        #pre /\
        ={query_t_poly_aggregated0, query_t_poly_aggregated0, currentEta}
      ). by sim.
      seq 4 4: #pre. by sim.
      seq 3 3: #pre. by sim.
      by sim.

      seq 2 2: (
        #pre /\
        ={query_at_z_0, query_at_z_1, copy_permutation_first_aggregated_commitment_coeff, lookup_s_first_aggregated_commitment, lookup_grand_product_first_aggregated_coefficient, query_t_poly_aggregated}
      ). by sim.
      by sim.
qed.
