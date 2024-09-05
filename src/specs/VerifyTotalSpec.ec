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
require import VerifyMidCanonicalisation.
require import VerifyMidToHighEncapsulated.
require import VerifyHighEncapsulatedToHigh.

import MemoryMap PurePrimops.

pred inputs_castable_to_curve (
    state_poly_0_i: int*int,
    state_poly_1_i: int*int,
    state_poly_2_i: int*int,
    state_poly_3_i: int*int,
    copy_permutation_grand_product_i: int*int,
    lookup_s_poly_i: int*int,
    lookup_grand_product_i: int*int,
    quotient_poly_part_0_i: int*int,
    quotient_poly_part_1_i: int*int,
    quotient_poly_part_2_i: int*int,
    quotient_poly_part_3_i: int*int,
    opening_proof_at_z_i: int*int,
    opening_proof_at_z_omega_i: int*int
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

lemma verify_mid_equiv_high_or_revert (
    state_poly_0_i: int*int,
    state_poly_1_i: int*int,
    state_poly_2_i: int*int,
    state_poly_3_i: int*int,
    copy_permutation_grand_product_i: int*int,
    lookup_s_poly_i: int*int,
    lookup_grand_product_i: int*int,
    quotient_poly_part_0_i: int*int,
    quotient_poly_part_1_i: int*int,
    quotient_poly_part_2_i: int*int,
    quotient_poly_part_3_i: int*int,
    opening_proof_at_z_i: int*int,
    opening_proof_at_z_omega_i: int*int
):
    (exists (
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
      (FieldQ.inF opening_proof_at_z_omega_i.`1, FieldQ.inF opening_proof_at_z_omega_i.`2) = aspoint_G1 opening_proof_at_z_omega_g /\
      equiv [
        Verify.mid ~ Verify.high:
        ={public_input_length_in_words} /\
        (public_input{1} %% (2^253)) = FieldR.asint public_input{2} /\
        ={proof_length_in_words} /\
        state_poly_0{1} = state_poly_0_i /\ state_poly_0{2} = state_poly_0_g /\
        state_poly_1{1} = state_poly_1_i /\ state_poly_1{2} = state_poly_1_g /\
        state_poly_2{1} = state_poly_2_i /\ state_poly_2{2} = state_poly_2_g /\
        state_poly_3{1} = state_poly_3_i /\ state_poly_3{2} = state_poly_3_g /\
        copy_permutation_grand_product{1} = copy_permutation_grand_product_i /\
        copy_permutation_grand_product{2} = copy_permutation_grand_product_g /\
        lookup_s_poly{1} = lookup_s_poly_i /\
        lookup_s_poly{2} = lookup_s_poly_g /\
        lookup_grand_product{1} = lookup_grand_product_i /\
        lookup_grand_product{2} = lookup_grand_product_g /\
        quotient_poly_part_0{1} = quotient_poly_part_0_i /\
        quotient_poly_part_0{2} = quotient_poly_part_0_g /\
        quotient_poly_part_1{1} = quotient_poly_part_1_i /\
        quotient_poly_part_1{2} = quotient_poly_part_1_g /\
        quotient_poly_part_2{1} = quotient_poly_part_2_i /\
        quotient_poly_part_2{2} = quotient_poly_part_2_g /\
        quotient_poly_part_3{1} = quotient_poly_part_3_i /\
        quotient_poly_part_3{2} = quotient_poly_part_3_g /\
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
        opening_proof_at_z{1} = opening_proof_at_z_i /\
        opening_proof_at_z{2} = opening_proof_at_z_g /\
        opening_proof_at_z_omega{1} = opening_proof_at_z_omega_i /\
        opening_proof_at_z_omega{2} = opening_proof_at_z_omega_g /\
        ={recursive_proof_length_in_words} ==> 
        ={res}
      ]
    )) \/
    (hoare [
      Verify.mid:
      state_poly_0 = state_poly_0_i /\
      state_poly_1 = state_poly_1_i /\
      state_poly_2 = state_poly_2_i /\
      state_poly_3 = state_poly_3_i /\
      copy_permutation_grand_product = copy_permutation_grand_product_i /\
      lookup_s_poly = lookup_s_poly_i /\
      lookup_grand_product = lookup_grand_product_i /\
      quotient_poly_part_0 = quotient_poly_part_0_i /\
      quotient_poly_part_1 = quotient_poly_part_1_i /\
      quotient_poly_part_2 = quotient_poly_part_2_i /\
      quotient_poly_part_3 = quotient_poly_part_3_i /\
      opening_proof_at_z = opening_proof_at_z_i /\
      opening_proof_at_z_omega = opening_proof_at_z_omega_i ==>
      res = false
    ] /\ !exists (
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
    )).
    case (
      on_curve_int state_poly_0_i /\
      on_curve_int state_poly_1_i /\
      on_curve_int state_poly_2_i /\
      on_curve_int state_poly_3_i /\
      on_curve_int copy_permutation_grand_product_i /\
      on_curve_int lookup_s_poly_i /\
      on_curve_int lookup_grand_product_i /\
      on_curve_int quotient_poly_part_0_i /\
      on_curve_int quotient_poly_part_1_i /\
      on_curve_int quotient_poly_part_2_i /\
      on_curve_int quotient_poly_part_3_i /\
      on_curve_int opening_proof_at_z_i /\
      on_curve_int opening_proof_at_z_omega_i
    ).
    progress. left.
    have H_on_curve_int : forall (x y: int), on_curve_int (x,y) => exists p, (FieldQ.inF x, FieldQ.inF y) = aspoint_G1 p.
      rewrite /on_curve_int. progress.
      have H_on_curve : on_curve (FieldQ.inF x, FieldQ.inF y).
        rewrite /on_curve. simplify.
        rewrite Constants.q_eq_fieldq_p in H12.
        rewrite -FieldQ.inFM.
        rewrite FieldQ.inF_mod.
        rewrite -H12.
        rewrite -FieldQ.inFD.
        rewrite FieldQ.inFK.
        pose x_mod := x %% FieldQ.p.
        rewrite -FieldQ.inFM.
        rewrite FieldQ.inFK.
        pose x2_mod := (x*x) %% FieldQ.p.
        rewrite -modzMml.
        rewrite -/x_mod.
        rewrite modzDml.
        rewrite -FieldQ.inF_mod.
        reflexivity.
      have H_point : exists (p: g), aspoint_G1 p = (FieldQ.inF x, FieldQ.inF y).
        exact (on_curve_as_point (FieldQ.inF x) (FieldQ.inF y)).
      case H_point. progress.
      exists p. rewrite H13. reflexivity.
    have H_state_poly_0: exists state_poly_0_g, (FieldQ.inF state_poly_0_i.`1, FieldQ.inF state_poly_0_i.`2) = aspoint_G1 state_poly_0_g. exact H_on_curve_int.
    have H_state_poly_1: exists state_poly_1_g, (FieldQ.inF state_poly_1_i.`1, FieldQ.inF state_poly_1_i.`2) = aspoint_G1 state_poly_1_g. exact H_on_curve_int.
    have H_state_poly_2: exists state_poly_2_g, (FieldQ.inF state_poly_2_i.`1, FieldQ.inF state_poly_2_i.`2) = aspoint_G1 state_poly_2_g. exact H_on_curve_int.
    have H_state_poly_3: exists state_poly_3_g, (FieldQ.inF state_poly_3_i.`1, FieldQ.inF state_poly_3_i.`2) = aspoint_G1 state_poly_3_g. exact H_on_curve_int.
    have H_copy_permutation_grand_product: exists copy_permutation_grand_product_g, (FieldQ.inF copy_permutation_grand_product_i.`1, FieldQ.inF copy_permutation_grand_product_i.`2) = aspoint_G1 copy_permutation_grand_product_g. exact H_on_curve_int.
    have H_lookup_s_poly: exists lookup_s_poly_g, (FieldQ.inF lookup_s_poly_i.`1, FieldQ.inF lookup_s_poly_i.`2) = aspoint_G1 lookup_s_poly_g. exact H_on_curve_int.
    have H_lookup_grand_product: exists lookup_grand_product_g, (FieldQ.inF lookup_grand_product_i.`1, FieldQ.inF lookup_grand_product_i.`2) = aspoint_G1 lookup_grand_product_g. exact H_on_curve_int.
    have H_quotient_poly_part_0: exists quotient_poly_part_0_g, (FieldQ.inF quotient_poly_part_0_i.`1, FieldQ.inF quotient_poly_part_0_i.`2) = aspoint_G1 quotient_poly_part_0_g. exact H_on_curve_int.
    have H_quotient_poly_part_1: exists quotient_poly_part_1_g, (FieldQ.inF quotient_poly_part_1_i.`1, FieldQ.inF quotient_poly_part_1_i.`2) = aspoint_G1 quotient_poly_part_1_g. exact H_on_curve_int.
    have H_quotient_poly_part_2: exists quotient_poly_part_2_g, (FieldQ.inF quotient_poly_part_2_i.`1, FieldQ.inF quotient_poly_part_2_i.`2) = aspoint_G1 quotient_poly_part_2_g. exact H_on_curve_int.
    have H_quotient_poly_part_3: exists quotient_poly_part_3_g, (FieldQ.inF quotient_poly_part_3_i.`1, FieldQ.inF quotient_poly_part_3_i.`2) = aspoint_G1 quotient_poly_part_3_g. exact H_on_curve_int.
    have H_opening_proof_at_z: exists opening_proof_at_z_g, (FieldQ.inF opening_proof_at_z_i.`1, FieldQ.inF opening_proof_at_z_i.`2) = aspoint_G1 opening_proof_at_z_g. exact H_on_curve_int.
    have H_opening_proof_at_z_omega: exists opening_proof_at_z_omega_g, (FieldQ.inF opening_proof_at_z_omega_i.`1, FieldQ.inF opening_proof_at_z_omega_i.`2) = aspoint_G1 opening_proof_at_z_omega_g. exact H_on_curve_int.
    case H_state_poly_0.
    case H_state_poly_1.
    case H_state_poly_2.
    case H_state_poly_3.
    case H_copy_permutation_grand_product.
    case H_lookup_s_poly.
    case H_lookup_grand_product.
    case H_quotient_poly_part_0.
    case H_quotient_poly_part_1.
    case H_quotient_poly_part_2.
    case H_quotient_poly_part_3.
    case H_opening_proof_at_z.
    case H_opening_proof_at_z_omega.
    progress.
    exists state_poly_0_g state_poly_1_g state_poly_2_g state_poly_3_g copy_permutation_grand_product_g lookup_s_poly_g lookup_grand_product_g quotient_poly_part_0_g quotient_poly_part_1_g quotient_poly_part_2_g quotient_poly_part_3_g opening_proof_at_z_g opening_proof_at_z_omega_g.
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
      progress.
      rewrite H26. exact FieldR.ge0_asint. exact ltz_pmod.
      rewrite -H24 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H23 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H22 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H21 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H20 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H19 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H18 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H17 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H16 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H15 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H14 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite H28. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H29. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H30. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H31. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H32. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H33. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H34. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H35. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H36. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H37. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H38. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H39. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H40. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H41. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H42. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H43. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H44. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite H45. rewrite pmod_small. exact FieldR.rg_asint. reflexivity.
      rewrite -H13 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      rewrite -H12 /F_to_int_point. simplify. rewrite FieldQ.inFK FieldQ.inFK. reflexivity.
      progress.
      exact verify_mid_canonicalisation.
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
        ={recursive_proof_length_in_words} ==> 
        ={res}
      )
      (
        ={arg} ==> ={res}
      ).
      progress.
      exists (arg{2}). by progress.
      by progress.
      exact verify_mid_equiv_high_encapsulated.
      exact verify_high_encapsulated_equiv_high.
      progress.

      right.
      have H_de_morgan: (
        !on_curve_int state_poly_0_i \/
        !on_curve_int state_poly_1_i \/
        !on_curve_int state_poly_2_i \/
        !on_curve_int state_poly_3_i \/
        !on_curve_int copy_permutation_grand_product_i \/
        !on_curve_int lookup_s_poly_i \/
        !on_curve_int lookup_grand_product_i \/
        !on_curve_int quotient_poly_part_0_i \/
        !on_curve_int quotient_poly_part_1_i \/
        !on_curve_int quotient_poly_part_2_i \/
        !on_curve_int quotient_poly_part_3_i \/
        !on_curve_int opening_proof_at_z_i \/
        !on_curve_int opening_proof_at_z_omega_i
      ). smt ().
      case H_de_morgan.
        progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 41: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 12: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists state_poly_0_g, (FieldQ.inF state_poly_0_i.`1, FieldQ.inF state_poly_0_i.`2) = aspoint_G1 state_poly_0_g.          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF state_poly_0_i.`1, FieldQ.inF state_poly_0_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 42: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 11: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists state_poly_1_g, (FieldQ.inF state_poly_1_i.`1, FieldQ.inF state_poly_1_i.`2) = aspoint_G1 state_poly_1_g.          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF state_poly_1_i.`1, FieldQ.inF state_poly_1_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 43: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 10: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists state_poly_2_g, (FieldQ.inF state_poly_2_i.`1, FieldQ.inF state_poly_2_i.`2) = aspoint_G1 state_poly_2_g.          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF state_poly_2_i.`1, FieldQ.inF state_poly_2_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 44: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 9: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists state_poly_3_g, (FieldQ.inF state_poly_3_i.`1, FieldQ.inF state_poly_3_i.`2) = aspoint_G1 state_poly_3_g.          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF state_poly_3_i.`1, FieldQ.inF state_poly_3_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 45: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 8: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists copy_permutation_grand_product_g, (FieldQ.inF copy_permutation_grand_product_i.`1, FieldQ.inF copy_permutation_grand_product_i.`2) = aspoint_G1 copy_permutation_grand_product_g.
          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF copy_permutation_grand_product_i.`1, FieldQ.inF copy_permutation_grand_product_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 46: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 7: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists lookup_s_poly_g, (FieldQ.inF lookup_s_poly_i.`1, FieldQ.inF lookup_s_poly_i.`2) = aspoint_G1 lookup_s_poly_g.
          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF lookup_s_poly_i.`1, FieldQ.inF lookup_s_poly_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 47: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 6: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists lookup_grand_product_g, (FieldQ.inF lookup_grand_product_i.`1, FieldQ.inF lookup_grand_product_i.`2) = aspoint_G1 lookup_grand_product_g.
          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF lookup_grand_product_i.`1, FieldQ.inF lookup_grand_product_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 48: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 5: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists quotient_poly_part_0_g, (FieldQ.inF quotient_poly_part_0_i.`1, FieldQ.inF quotient_poly_part_0_i.`2) = aspoint_G1 quotient_poly_part_0_g.
          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF quotient_poly_part_0_i.`1, FieldQ.inF quotient_poly_part_0_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 49: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 4: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists quotient_poly_part_1_g, (FieldQ.inF quotient_poly_part_1_i.`1, FieldQ.inF quotient_poly_part_1_i.`2) = aspoint_G1 quotient_poly_part_1_g.
          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF quotient_poly_part_1_i.`1, FieldQ.inF quotient_poly_part_1_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 50: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 3: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists quotient_poly_part_2_g, (FieldQ.inF quotient_poly_part_2_i.`1, FieldQ.inF quotient_poly_part_2_i.`2) = aspoint_G1 quotient_poly_part_2_g.
          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF quotient_poly_part_2_i.`1, FieldQ.inF quotient_poly_part_2_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 51: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 2: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists quotient_poly_part_3_g, (FieldQ.inF quotient_poly_part_3_i.`1, FieldQ.inF quotient_poly_part_3_i.`2) = aspoint_G1 quotient_poly_part_3_g.
          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF quotient_poly_part_3_i.`1, FieldQ.inF quotient_poly_part_3_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. case H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 52: (!isValid). sp. skip. progress. rewrite H0. by progress.
        seq 1: (!isValid). sp. skip. progress. rewrite H1. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H1. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H1. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H1. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H1. by progress. rewrite H1. by progress.
          have H_neg: !exists opening_proof_at_z_g, (FieldQ.inF opening_proof_at_z_i.`1, FieldQ.inF opening_proof_at_z_i.`2) = aspoint_G1 opening_proof_at_z_g.
          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF opening_proof_at_z_i.`1, FieldQ.inF opening_proof_at_z_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H0.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
      move => H_de_morgan. progress.
        proc. simplify.
        sp. inline LoadProof.mid.
        seq 53: (!isValid). sp. skip. progress. rewrite H_de_morgan. by progress.
        seq 4: failed.
        case (vk_recursive_flag0). rcondt 1. by progress.
        seq 5: (!isValid). wp. skip. progress. rewrite H0. by progress.
        rcondf 1. by progress. wp. skip. by progress.
        rcondf 1. by progress.
        rcondf 4. wp. skip. progress. rewrite H0. by progress. wp. skip. by progress.
        seq 1: #pre. wp. skip. by progress.
        inline InitializeTranscript.mid.
        seq 47: #pre. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. by progress.
        seq 1: #pre. inline*. wp. skip. progress. rewrite H0. left. by trivial.
        seq 2: #pre. inline PrepareQueries.mid.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 10: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. sp. skip. progress. smt ().
        seq 3: #pre. inline AddAssignPermutationLinearisationContributionWithV.AddAssignPermutationLinearisationContributionWithV.mid.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          seq 10: #pre. wp. skip. by progress.
          inline*. wp. skip. by progress.

        seq 3: #pre. inline AddAssignLookupLinearisationContributionWithV.mid.
          wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 4: #pre. inline*. wp. skip. by progress.
        seq 3: #pre. inline*. wp. skip. by progress.
        wp. skip. by progress.

        seq 3: #pre. inline PrepareAggregatedCommitment.mid.
          seq 40: #pre. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          seq 5: #pre. inline*. wp. skip. by progress.
          wp. skip. by progress.
          inline*. wp. skip. progress. rewrite H0. by progress. rewrite H0. by progress.
          have H_neg: !exists opening_proof_at_z_omega_g, (FieldQ.inF opening_proof_at_z_omega_i.`1, FieldQ.inF opening_proof_at_z_omega_i.`2) = aspoint_G1 opening_proof_at_z_omega_g.
          rewrite negb_exists. progress.
            have H_curve: !on_curve (FieldQ.inF opening_proof_at_z_omega_i.`1, FieldQ.inF opening_proof_at_z_omega_i.`2).
              rewrite /on_curve.
              rewrite /on_curve_int in H_de_morgan.
              rewrite -FieldQ.inFD.
              simplify.
              rewrite -FieldQ.inFM.
              rewrite -FieldQ.inFM.
              rewrite FieldQ.inFK.
              rewrite FieldQ.inFK.
              smt (@Constants @FieldQ @IntDiv).
            smt (@EllipticCurve).
          smt ().
qed.
