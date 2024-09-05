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
