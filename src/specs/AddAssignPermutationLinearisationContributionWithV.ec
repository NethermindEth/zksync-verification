pragma Goals:printall.

require import AllCore.
require        Constants.
require import PointMulIntoDest.
require import PointSubAssign.
require import PurePrimops.
require import UInt256.
require import Utils.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

module AddAssignPermutationLinearisationContributionWithV = {
  proc low(dest : uint256, stateOpening0AtZ : uint256, stateOpening1AtZ : uint256, stateOpening2AtZ : uint256, stateOpening3AtZ : uint256): unit = {
    var factor, _1, _3, gamma, _4, intermediateValue, _6, _7, _9, _10, _12, _13, l0AtZ, _16, _17, _18, _20, _21, _23, beta', gamma_1, _25, _26, _27, intermediateValue_1, _29, _30, _31, _33, _34, _35, _36;
    factor <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    _1 <@ Primops.mload(STATE_BETA_SLOT);
    _3 <@ Primops.mload(STATE_Z_SLOT);
    gamma <@ Primops.mload(STATE_GAMMA_SLOT);
    _4 <- (PurePrimops.addmod (PurePrimops.mulmod _3 _1 R_MOD) gamma R_MOD);
    intermediateValue <- (PurePrimops.addmod _4 stateOpening0AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue R_MOD);
    _6 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 R_MOD) NON_RESIDUES_0 R_MOD);
    _7 <- (PurePrimops.addmod _6 gamma R_MOD);
    intermediateValue <- (PurePrimops.addmod _7 stateOpening1AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue R_MOD);
    _9 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 R_MOD) NON_RESIDUES_1 R_MOD);
    _10 <- (PurePrimops.addmod _9 gamma R_MOD);
    intermediateValue <- (PurePrimops.addmod _10 stateOpening2AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue R_MOD);
    _12 <- (PurePrimops.mulmod (PurePrimops.mulmod _3 _1 R_MOD) NON_RESIDUES_2 R_MOD);
    _13 <- (PurePrimops.addmod _12 gamma R_MOD);
    intermediateValue <- (PurePrimops.addmod _13 stateOpening3AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue R_MOD);
    l0AtZ <@ Primops.mload(STATE_L_0_AT_Z_SLOT);
    _16 <@ Primops.mload(STATE_POWER_OF_ALPHA_5_SLOT);
    _17 <- (PurePrimops.mulmod l0AtZ _16 R_MOD);
    factor <- (PurePrimops.addmod factor _17 R_MOD);
    _18 <@ Primops.mload(STATE_V_SLOT);
    factor <- (PurePrimops.mulmod factor _18 R_MOD);
    Primops.mstore(COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF, factor);
    _20 <@ Primops.mload(STATE_BETA_SLOT);
    _21 <@ Primops.mload(STATE_POWER_OF_ALPHA_4_SLOT);
    factor <- (PurePrimops.mulmod _21 _20 R_MOD);
    _23 <@ Primops.mload(PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT);
    factor <- (PurePrimops.mulmod factor _23 R_MOD);
    beta' <@ Primops.mload(STATE_BETA_SLOT);
    gamma_1 <@ Primops.mload(STATE_GAMMA_SLOT);
    _25 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT);
    _26 <- (PurePrimops.mulmod _25 beta' R_MOD);
    _27 <- (PurePrimops.addmod _26 gamma_1 R_MOD);
    intermediateValue_1 <- (PurePrimops.addmod _27 stateOpening0AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue_1 R_MOD);
    _29 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT);
    _30 <- (PurePrimops.mulmod _29 beta' R_MOD);
    _31 <- (PurePrimops.addmod _30 gamma_1 R_MOD);
    intermediateValue_1 <- (PurePrimops.addmod _31 stateOpening1AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue_1 R_MOD);
    _33 <@ Primops.mload(PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT);
    _34 <- (PurePrimops.mulmod _33 beta' R_MOD);
    _35 <- (PurePrimops.addmod _34 gamma_1 R_MOD);
    intermediateValue_1 <- (PurePrimops.addmod _35 stateOpening2AtZ R_MOD);
    factor <- (PurePrimops.mulmod factor intermediateValue_1 R_MOD);
    _36 <@ Primops.mload(STATE_V_SLOT);
    factor <- (PurePrimops.mulmod factor _36 R_MOD);
    PointMulIntoDest.low(VK_PERMUTATION_3_X_SLOT, factor, QUERIES_BUFFER_POINT_SLOT);
    PointSubAssign.low(dest, QUERIES_BUFFER_POINT_SLOT);
  }

  proc mid(point: (int*int), vk_permutation_3: (int*int), stateOpening0AtZ: int, stateOpening1AtZ: int, stateOpening2AtZ: int, stateOpening3AtZ: int, state_beta: int, state_v: int, state_z: int, state_gamma: int, state_alpha4: int, state_alpha5: int, state_gp_omega: int, state_l0AtZ: int, poly0_opening: int, poly1_opening: int, poly2_opening: int): (int * (int*int)) option = {
      var mul_factor, buffer_point, ret_point, ret_factor,
      ret;
    mul_factor <- ((
      (state_alpha4 * state_beta * state_gp_omega) *
      ((poly0_opening * state_beta) + state_gamma + stateOpening0AtZ) *
      ((poly1_opening * state_beta) + state_gamma + stateOpening1AtZ) *
      ((poly2_opening * state_beta) + state_gamma + stateOpening2AtZ)
    ) * state_v) %% Constants.R;
    buffer_point <@ PointMulIntoDest.mid(vk_permutation_3.`1, vk_permutation_3.`2, mul_factor);
    if (is_none buffer_point) {
      ret_point <- None;
    } else {
      ret_point <@ PointSubAssign.mid(point, odflt (0,0) buffer_point);
    }

    if (is_none ret_point) {
      ret <- None;
    } else {
      ret_factor <- ((
        state_alpha4 *
        (state_z * state_beta + state_gamma + stateOpening0AtZ) *
        (state_z * state_beta * Constants.NON_RESIDUE_0 + state_gamma + stateOpening1AtZ) *
        (state_z * state_beta * Constants.NON_RESIDUE_1 + state_gamma + stateOpening2AtZ) *
        (state_z * state_beta * Constants.NON_RESIDUE_2 + state_gamma + stateOpening3AtZ) +
        state_l0AtZ * state_alpha5
      ) * state_v) %% Constants.R;
      ret <- Some (ret_factor, odflt (0, 0) ret_point);
    }

    return ret;
  }
}.

(* requries sub assign extracted fix *)
(* lemma addAssignPermutationLinearisationContributionWithV_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_addAssignPermutationLinearisationContributionWithV ~ AddAssignPermutationLinearisationContributionWithV.low :
      ={arg, glob AddAssignPermutationLinearisationContributionWithV} ==>
      ={res, glob AddAssignPermutationLinearisationContributionWithV}
    ].
proof.
  proc.
  call (pointSubAssign_extracted_equiv_low). wp.
  call (pointMulIntoDest_extracted_equiv_low).
  inline*. wp. skip. rewrite /Constants.R. by progress.
    qed. *)

op copy_permutation_first_aggregated_commitment_coeff_mid: int.

lemma addAssignPermutationLinearisationContributionWithV_low_equiv_mid (mem_0: mem) :
    equiv [
      AddAssignPermutationLinearisationContributionWithV.low ~ AddAssignPermutationLinearisationContributionWithV.mid :
      point{2}.`1 = W256.to_uint (load mem_0 dest{1}) /\
      point{2}.`2 = W256.to_uint (load mem_0 (dest{1} + W256.of_int 32)) /\
      vk_permutation_3{2}.`1 = W256.to_uint (load mem_0 VK_PERMUTATION_3_X_SLOT) /\
      vk_permutation_3{2}.`2 = W256.to_uint (load mem_0 VK_PERMUTATION_3_Y_SLOT) /\
      stateOpening0AtZ{2} = W256.to_uint stateOpening0AtZ{1} /\
      stateOpening1AtZ{2} = W256.to_uint stateOpening1AtZ{1} /\
      stateOpening2AtZ{2} = W256.to_uint stateOpening2AtZ{1} /\
      stateOpening3AtZ{2} = W256.to_uint stateOpening3AtZ{1} /\
      state_beta{2} = W256.to_uint (load mem_0 STATE_BETA_SLOT) /\
      state_v{2} = W256.to_uint (load mem_0 STATE_V_SLOT) /\
      state_z{2} = W256.to_uint (load mem_0 STATE_Z_SLOT) /\
      state_gamma{2} = W256.to_uint (load mem_0 STATE_GAMMA_SLOT) /\
      state_alpha4{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_4_SLOT) /\
      state_alpha5{2} = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_5_SLOT) /\
      state_gp_omega{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
      state_l0AtZ{2} = W256.to_uint (load mem_0 STATE_L_0_AT_Z_SLOT) /\
      poly0_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) /\
      poly1_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) /\
      poly2_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) /\
      !Primops.reverted{1} /\
      Primops.memory{1} = mem_0
      ==>
      (Primops.reverted{1} /\ res{2} = None) \/
      (!Primops.reverted{1} /\ exists (f: int) (p: (int*int)),
        res{2} = Some (f, p)
      )  
    ].
    proof.
      proc.
      exists* state_alpha4{2}, state_z{2}, state_beta{2}, state_gamma{2}, stateOpening0AtZ{2}, stateOpening1AtZ{2}, stateOpening2AtZ{2}, stateOpening3AtZ{2}, state_l0AtZ{2}, state_alpha5{2}, state_v{2}.
      elim*=> alpha4_r z_r beta_r gamma_r opening0AtZ_r opening1AtZ_r opening2AtZ_r opening3AtZ_r l0AtZ_r alpha5_r v_r.
      pose mem_1 := store mem_0 COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF (W256.of_int (
          ((
            alpha4_r *
            (z_r * beta_r + gamma_r + opening0AtZ_r) *
            (z_r * beta_r * Constants.NON_RESIDUE_0 + gamma_r + opening1AtZ_r) *
            (z_r * beta_r * Constants.NON_RESIDUE_1 + gamma_r + opening2AtZ_r) *
            (z_r * beta_r * Constants.NON_RESIDUE_2 + gamma_r + opening3AtZ_r) +
            l0AtZ_r * alpha5_r
          ) * v_r) %% Constants.R
        )).
      seq 26 0: (
        !Primops.reverted{1} /\
        Primops.memory{1} = mem_1 /\
        W256.to_uint (load mem_1 STATE_POWER_OF_ALPHA_4_SLOT) = state_alpha4{2} /\
        W256.to_uint (load mem_1 STATE_BETA_SLOT) = state_beta{2} /\
        W256.to_uint (load mem_1 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = state_gp_omega{2} /\
        W256.to_uint (load mem_1 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = poly0_opening{2} /\
        W256.to_uint (load mem_1 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = poly1_opening{2} /\
        W256.to_uint (load mem_1 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = poly2_opening{2} /\
        W256.to_uint (load mem_1 STATE_GAMMA_SLOT) = state_gamma{2} /\
        W256.to_uint (load mem_1 STATE_V_SLOT) = state_v{2} /\
        W256.to_uint stateOpening0AtZ{1} = stateOpening0AtZ{2} /\
        W256.to_uint stateOpening1AtZ{1} = stateOpening1AtZ{2} /\
        W256.to_uint stateOpening2AtZ{1} = stateOpening2AtZ{2} /\
        W256.to_uint stateOpening3AtZ{1} = stateOpening3AtZ{2}
      ).
        inline*. wp. skip. progress.
        pose z := load Primops.memory{1} STATE_Z_SLOT.
        pose b := load Primops.memory{1} STATE_BETA_SLOT.
        pose gamma := load Primops.memory{1} STATE_GAMMA_SLOT.
        pose a4 := load Primops.memory{1} STATE_POWER_OF_ALPHA_4_SLOT.
        pose l0 := load Primops.memory{1} STATE_L_0_AT_Z_SLOT.
        pose a5 := load Primops.memory{1} STATE_POWER_OF_ALPHA_5_SLOT.
        pose v := load Primops.memory{1} STATE_V_SLOT.
        have H_add: forall (a b c: int),  (a %% b + c) %% b = (a + c) %% b by smt(@IntDiv).
        have H_mul: forall(a b c: int), (a %% b * c) %% b = (a * c) %% b by smt (@IntDiv).
        have H_add': forall (a b c: int),  (a + (c %% b)) %% b = (a + c) %% b by smt(@IntDiv).
        have H_mul': forall(a b c: int), (a * (c %% b)) %% b = (a * c) %% b by smt (@IntDiv).
        rewrite /mulmod /addmod. simplify. rewrite - Constants.R_int.
        do 21! rewrite W256.of_uintK.
        rewrite (pmod_small 5 W256.modulus). by progress.
        rewrite (pmod_small 7 W256.modulus). by progress.
        rewrite (pmod_small 10 W256.modulus). by progress.
        do 18! (rewrite (pmod_small _ W256.modulus); first split; [smt (@W256 @IntDiv) | (progress; smt (@W256 @IntDiv))]).
        pose x1 := to_uint z * to_uint b. rewrite (H_add x1 _ _).
        pose x2 := x1 + to_uint gamma. rewrite (H_add x2 _ _).
        rewrite (H_mul' (to_uint a4) _ _).
        pose x3 := (W256.to_uint a4 * (x2 + W256.to_uint stateOpening0AtZ{1})).
        do have ->: forall (a: int), (x1 %% Constants.R * a %% Constants.R + W256.to_uint gamma) %% Constants.R = (x1 * a + W256.to_uint gamma) %% Constants.R by smt (@IntDiv).
        rewrite (H_add _ _ (W256.to_uint stateOpening1AtZ{1})).
        rewrite (H_add _ _ (W256.to_uint stateOpening2AtZ{1})).
        rewrite (H_add _ _ (W256.to_uint stateOpening3AtZ{1})).
        rewrite (H_mul x3 _ _). rewrite (H_mul' x3 _ _).
        rewrite /Constants.NON_RESIDUE_0 /Constants.NON_RESIDUE_1 /Constants.NON_RESIDUE_2.
        pose x4 := W256.to_uint l0 * W256.to_uint a5.
        rewrite (H_add' _ _ x4).
        pose x5 := x1 * 10 + W256.to_uint gamma + W256.to_uint stateOpening3AtZ{1}.
        pose x6 := x1 * 7 + W256.to_uint gamma + W256.to_uint stateOpening2AtZ{1}.
        pose x7 := x3 * (x1 * 5 + W256.to_uint gamma + W256.to_uint stateOpening1AtZ{1}).
        rewrite (H_mul x7 _ _). rewrite (H_mul' x7 _ _). pose x8 := x7 * x6.
        rewrite (H_mul x8 _ _). rewrite (H_mul' x8 _ _). pose x9 := x8 * x5.
        rewrite (H_add x9 _ _). pose x10 := x9 + x4.
        rewrite (H_mul x10 _ _). reflexivity.

        rewrite load_store_diff; smt (@W256 @Utils).
        rewrite load_store_diff; smt (@W256 @Utils).
        rewrite load_store_diff; smt (@W256 @Utils).
        rewrite load_store_diff; smt (@W256 @Utils).
        rewrite load_store_diff; smt (@W256 @Utils).
        rewrite load_store_diff; smt (@W256 @Utils).
        rewrite load_store_diff; smt (@W256 @Utils).
        rewrite load_store_diff; smt (@W256 @Utils).


        seq 24 1: (
          #pre /\
          W256.to_uint factor{1} = mul_factor{2}
        ).
            inline Primops.mload. wp. skip. progress.
            have H_add: forall (a b c: int),  (a %% b + c) %% b = (a + c) %% b by smt(@IntDiv).
            have H_mul: forall(a b c: int), (a %% b * c) %% b = (a * c) %% b by smt (@IntDiv).
            have H_add': forall (a b c: int),  (a + (c %% b)) %% b = (a + c) %% b by smt(@IntDiv). 
            have H_mul': forall(a b c: int), (a * (c %% b)) %% b = (a * c) %% b by smt (@IntDiv).
            pose a4 := load mem_1 STATE_POWER_OF_ALPHA_4_SLOT.
            pose b := load mem_1 STATE_BETA_SLOT.
            pose gp := load mem_1 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT.
            have ->: PurePrimops.mulmod (PurePrimops.mulmod a4 b R_MOD) gp R_MOD = W256.of_int ((W256.to_uint a4 * W256.to_uint b * W256.to_uint gp) %% Constants.R).
            rewrite /mulmod. simplify.
            rewrite W256.of_uintK. rewrite - Constants.R_int.
            rewrite (pmod_small _ W256.modulus). split. smt (@IntDiv). progress. smt (@W256 @IntDiv).
            rewrite H_mul. reflexivity.
            pose x0 := W256.to_uint a4 * W256.to_uint b * W256.to_uint gp.
            pose p0 := load mem_1 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT.
            pose g := load mem_1 STATE_GAMMA_SLOT.
            have ->: PurePrimops.addmod(PurePrimops.mulmod p0 b R_MOD) g R_MOD = W256.of_int ((W256.to_uint p0 * W256.to_uint b + W256.to_uint g) %% Constants.R).
            rewrite /addmod /mulmod. simplify.
            rewrite W256.of_uintK. rewrite - Constants.R_int.
            rewrite (pmod_small _ W256.modulus). split. smt (@IntDiv). progress. smt (@W256 @IntDiv).
            rewrite H_add. reflexivity.
            pose x1 := W256.to_uint p0 * W256.to_uint b + W256.to_uint g.
            have ->: PurePrimops.addmod (W256.of_int (x1 %% Constants.R)) stateOpening0AtZ{1} R_MOD = W256.of_int ((x1 + W256.to_uint stateOpening0AtZ{1}) %% Constants.R).
            rewrite /addmod. simplify. rewrite W256.of_uintK.
            rewrite - Constants.R_int. rewrite (pmod_small _ W256.modulus).
            split. smt (@IntDiv). progress. smt (@W256 @IntDiv).
            rewrite H_add. reflexivity.
            pose x2 := x1 + W256.to_uint stateOpening0AtZ{1}.
            have H_mulmod: forall (a b: int), PurePrimops.mulmod (W256.of_int (a %% Constants.R)) (W256.of_int (b %% Constants.R)) R_MOD = W256.of_int ((a * b) %% Constants.R).
            progress.
            rewrite /mulmod. simplify. rewrite W256.of_uintK. rewrite W256.of_uintK.
            rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv @W256).
            rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv @W256).
            rewrite - Constants.R_int. rewrite  H_mul. rewrite H_mul'. reflexivity.
            rewrite H_mulmod.
            have H_addmod: forall (a b: int), PurePrimops.addmod (W256.of_int (a %% Constants.R)) (W256.of_int (b %% Constants.R)) R_MOD = W256.of_int ((a + b) %% Constants.R).
            progress.
            rewrite /addmod. simplify. rewrite W256.of_uintK. rewrite W256.of_uintK.
            rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv @W256).
            rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv @W256).
            rewrite - Constants.R_int. rewrite  H_add. rewrite H_add'. reflexivity.
            pose p1 := load mem_1 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT.
            pose p2 := load mem_1 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT.                pose v := load mem_1 STATE_V_SLOT.
            have ->: PurePrimops.mulmod p1 b R_MOD = W256.of_int ((W256.to_uint p1) * (W256.to_uint b) %% Constants.R). smt (@PurePrimops @Constants).
            pose x3 := W256.to_uint p1 * W256.to_uint b.
            have ->: PurePrimops.addmod (W256.of_int (x3 %% Constants.R)) g R_MOD = W256.of_int ((x3 + (W256.to_uint g)) %% Constants.R).
            rewrite /addmod. simplify. rewrite W256.of_uintK.
            rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv @W256).
            rewrite - Constants.R_int. rewrite H_add. reflexivity.
            pose x4 := x3 + W256.to_uint g.
            have ->: PurePrimops.addmod (W256.of_int (x4 %% Constants.R)) stateOpening1AtZ{1} R_MOD = W256.of_int ((x4 + (W256.to_uint stateOpening1AtZ{1})) %% Constants.R).
            rewrite /addmod. simplify. rewrite W256.of_uintK.
            rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv @W256).
            rewrite - Constants.R_int. rewrite H_add. reflexivity.
            rewrite H_mulmod.
            have ->: PurePrimops.addmod(PurePrimops.addmod(PurePrimops.mulmod p2 b R_MOD) g R_MOD) stateOpening2AtZ{1} R_MOD = W256.of_int (((W256.to_uint p2) * (W256.to_uint b) + (W256.to_uint g) + (W256.to_uint stateOpening2AtZ{1})) %% Constants.R).
            rewrite /addmod /mulmod. simplify. rewrite - Constants.R_int.
            rewrite W256.of_uintK. rewrite W256.of_uintK.
            rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv @W256).
            rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv @W256).
            smt ().
            rewrite H_mulmod.
            pose x5 := ((x0 * x2 * (x4 + W256.to_uint stateOpening1AtZ{1})) * (W256.to_uint p2 * W256.to_uint b + W256.to_uint g + W256.to_uint stateOpening2AtZ{1})).
            rewrite /mulmod. simplify. rewrite - Constants.R_int.
            rewrite W256.of_uintK. rewrite W256.of_uintK.
            rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv @W256).
            rewrite (pmod_small _ W256.modulus). smt (@Constants @IntDiv @W256).
            rewrite H_mul. reflexivity.










