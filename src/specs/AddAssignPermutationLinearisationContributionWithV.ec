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
lemma addAssignPermutationLinearisationContributionWithV_extracted_equiv_low :
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
    qed.

op addAssignPermutation_memory_footprint
(mem_0: mem)
(x64 x64' x96: uint256)
(alpha4_r alpha5_r beta_r gamma_r l0AtZ_r opening0AtZ_r opening1AtZ_r opening2AtZ_r opening3AtZ_r v_r z_r: int)
(buffer_point ret_point: int*int)
(p1_addr p2_addr: uint256) =
  let mem_1 = store mem_0 COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF
               (W256.of_int
                   ((alpha4_r * (z_r * beta_r + gamma_r + opening0AtZ_r) *
                     (z_r * beta_r * Constants.NON_RESIDUE_0 + gamma_r +
                      opening1AtZ_r) *
                     (z_r * beta_r * Constants.NON_RESIDUE_1 + gamma_r +
                      opening2AtZ_r) *
                     (z_r * beta_r * Constants.NON_RESIDUE_2 + gamma_r +
                      opening3AtZ_r) +
                     l0AtZ_r * alpha5_r) *
                       v_r %% Constants.R)) in
               let mem_2 = store mem_1 W256.zero (load mem_1 VK_PERMUTATION_3_X_SLOT) in
               let mem_3 = store mem_2 (W256.of_int 32) (load mem_1 VK_PERMUTATION_3_Y_SLOT) in
               let mem_4 = store mem_3 (W256.of_int 64) x64' in
               let mem_5 = store mem_4 QUERIES_BUFFER_POINT_SLOT (W256.of_int buffer_point.`1) in
               let mem_6 = store mem_5 (QUERIES_BUFFER_POINT_SLOT + (W256.of_int 32)) (W256.of_int buffer_point.`2) in
               pointSubAssign_memory_footprint mem_6 p1_addr p2_addr x64 x96 ret_point.

(* have to pass all these variables as parameters so they can be referenced in the post *)
lemma addAssignPermutationLinearisationContributionWithV_low_equiv_mid (mem_0: mem) (dest_l: uint256) (alpha4_r alpha5_r beta_r gamma_r l0AtZ_r opening0AtZ_r opening1AtZ_r opening2AtZ_r opening3AtZ_r v_r z_r: int) :
    equiv [
    AddAssignPermutationLinearisationContributionWithV.low ~ AddAssignPermutationLinearisationContributionWithV.mid :
      dest_l = dest{1} /\
      128 <= W256.to_uint dest{1} /\
      64 <= W256.to_uint (-dest{1}) /\
      W256.of_int 32 <= dest{1} - COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /\
      W256.of_int 64 <= COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF - dest{1} /\
      W256.of_int 64 <= dest{1} - QUERIES_BUFFER_POINT_SLOT /\
      W256.of_int 64 <= QUERIES_BUFFER_POINT_SLOT - dest{1} /\
      point{2}.`1 = W256.to_uint (load mem_0 dest{1}) /\
      point{2}.`2 = W256.to_uint (load mem_0 (dest{1} + W256.of_int 32)) /\
      0 <= point{2}.`1 < Constants.Q /\
      0 <= point{2}.`2 < Constants.Q /\
      vk_permutation_3{2}.`1 = W256.to_uint (load mem_0 VK_PERMUTATION_3_X_SLOT) /\
      vk_permutation_3{2}.`1 < Constants.Q /\
      vk_permutation_3{2}.`2 = W256.to_uint (load mem_0 VK_PERMUTATION_3_Y_SLOT) /\
      vk_permutation_3{2}.`2 < Constants.Q /\      
      opening0AtZ_r = stateOpening0AtZ{2} /\ opening0AtZ_r = W256.to_uint stateOpening0AtZ{1} /\
      opening1AtZ_r = stateOpening1AtZ{2} /\ opening1AtZ_r = W256.to_uint stateOpening1AtZ{1} /\
      opening2AtZ_r = stateOpening2AtZ{2} /\ opening2AtZ_r = W256.to_uint stateOpening2AtZ{1} /\
      opening3AtZ_r = stateOpening3AtZ{2} /\ opening3AtZ_r = W256.to_uint stateOpening3AtZ{1} /\
      beta_r = state_beta{2} /\ beta_r = W256.to_uint (load mem_0 STATE_BETA_SLOT) /\
      v_r = state_v{2} /\ v_r = W256.to_uint (load mem_0 STATE_V_SLOT) /\
      z_r = state_z{2} /\ z_r = W256.to_uint (load mem_0 STATE_Z_SLOT) /\
      gamma_r = state_gamma{2} /\ gamma_r = W256.to_uint (load mem_0 STATE_GAMMA_SLOT) /\
      alpha4_r = state_alpha4{2} /\ alpha4_r = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_4_SLOT) /\
      alpha5_r = state_alpha5{2} /\ alpha5_r = W256.to_uint (load mem_0 STATE_POWER_OF_ALPHA_5_SLOT) /\
      state_gp_omega{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) /\
      l0AtZ_r = state_l0AtZ{2} /\ l0AtZ_r = W256.to_uint (load mem_0 STATE_L_0_AT_Z_SLOT) /\
      poly0_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) /\
      poly1_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) /\
      poly2_opening{2} = W256.to_uint (load mem_0 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) /\
      !Primops.reverted{1} /\
      Primops.memory{1} = mem_0
      ==>
      (Primops.reverted{1} /\ res{2} = None) \/
      (!Primops.reverted{1} /\ exists (f: int) (p: (int*int)),
        res{2} = Some (f, p) /\
        exists (x64 x64' x96: uint256) (buffer_p: int*int),
        Primops.memory{1} = addAssignPermutation_memory_footprint
          mem_0
          x64 x64' x96
          alpha4_r alpha5_r beta_r gamma_r l0AtZ_r opening0AtZ_r opening1AtZ_r opening2AtZ_r opening3AtZ_r v_r z_r
          buffer_p p
          dest_l QUERIES_BUFFER_POINT_SLOT
      )  
    ].
    proof.
      proc.
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
(* ==== low until store into COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF ===== *)
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
        W256.to_uint (load mem_1 VK_PERMUTATION_3_X_SLOT) = vk_permutation_3{2}.`1 /\
        W256.to_uint (load mem_1 VK_PERMUTATION_3_Y_SLOT) = vk_permutation_3{2}.`2 /\
        W256.to_uint stateOpening0AtZ{1} = stateOpening0AtZ{2} /\
        W256.to_uint stateOpening1AtZ{1} = stateOpening1AtZ{2} /\
        W256.to_uint stateOpening2AtZ{1} = stateOpening2AtZ{2} /\
        W256.to_uint stateOpening3AtZ{1} = stateOpening3AtZ{2} /\
        0 <= vk_permutation_3{2}.`1 < Constants.Q /\
        0 <= vk_permutation_3{2}.`2 < Constants.Q /\
        128 <= W256.to_uint dest{1} /\
        64 <= W256.to_uint (-dest{1}) /\
        0 <= point{2}.`1 < Constants.Q /\
        0 <= point{2}.`2 < Constants.Q /\
        W256.to_uint (load mem_1 dest{1}) = point{2}.`1 /\
        W256.to_uint (load mem_1 (dest{1} + W256.of_int 32)) = point{2}.`2 /\
        W256.of_int 32 <= dest{1} - COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF /\
        W256.of_int 64 <= COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF - dest{1} /\
        W256.of_int 64 <= dest{1} - QUERIES_BUFFER_POINT_SLOT /\
        W256.of_int 64 <= QUERIES_BUFFER_POINT_SLOT - dest{1} /\
        dest{1} = dest_l
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

        by (rewrite load_store_diff; [
          rewrite /STATE_POWER_OF_ALPHA_4_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          rewrite /STATE_POWER_OF_ALPHA_4_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          reflexivity
        ]).
        by (rewrite load_store_diff; [
          rewrite /STATE_BETA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          rewrite /STATE_BETA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          reflexivity
        ]).
        by (rewrite load_store_diff; [
          rewrite /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          rewrite /PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          reflexivity
        ]).
        by (rewrite load_store_diff; [
          rewrite /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          rewrite /PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          reflexivity
        ]).
        by (rewrite load_store_diff; [
          rewrite /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          rewrite /PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          reflexivity
        ]).
        by (rewrite load_store_diff; [
          rewrite /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          rewrite /PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          reflexivity
        ]).
        by (rewrite load_store_diff; [
          rewrite /STATE_GAMMA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          rewrite /STATE_GAMMA_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          reflexivity
        ]).
        by (rewrite load_store_diff; [
          rewrite /STATE_V_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          rewrite /STATE_V_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          reflexivity
        ]).
        by (rewrite load_store_diff; [
          rewrite /VK_PERMUTATION_3_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          rewrite /VK_PERMUTATION_3_X_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          smt ()
        ]).
        by (rewrite load_store_diff; [
          rewrite /VK_PERMUTATION_3_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          rewrite /VK_PERMUTATION_3_Y_SLOT /COPY_PERMUTATION_FIRST_AGGREGATED_COMMITMENT_COEFF;
            by progress |
          smt ()
        ]).
        smt (@W256).
        smt (@W256).
        rewrite load_store_diff.
          assumption. apply (uint256_le_le_trans _ (W256.of_int 64) _). by progress. assumption. rewrite H5. reflexivity.
            rewrite load_store_diff. apply uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. assumption.
            apply uint256_le_sub_add_32; assumption.
       rewrite H6. reflexivity.
(* ===== mid and low: calculate mul factor. state is unaffected ===== *)
        seq 24 1: (
          #pre /\
          W256.to_uint factor{1} = mul_factor{2}
        ).
            inline Primops.mload. wp. skip. progress.
            have H_add: forall (a b c: int),  (a %% b + c) %% b = (a + c) %% b. progress. exact modzDml.
            have H_mul: forall(a b c: int), (a %% b * c) %% b = (a * c) %% b. progress. exact modzMml.
            have H_add': forall (a b c: int),  (a + (c %% b)) %% b = (a + c) %% b. progress. exact modzDmr. 
            have H_mul': forall(a b c: int), (a * (c %% b)) %% b = (a * c) %% b. progress. exact modzMmr.
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
            pose p2 := load mem_1 PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT.
            pose v := load mem_1 STATE_V_SLOT.
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
            pose mem_2 := store mem_1 W256.zero (load mem_1 VK_PERMUTATION_3_X_SLOT).
            pose mem_3 := store mem_2 (W256.of_int 32) (load mem_1 VK_PERMUTATION_3_Y_SLOT).
            exists* factor{1}.
            elim*=> factor.
            pose mem_4 := store mem_3 (W256.of_int 64) factor.
(* ===== mid and low: point mul into dest ===== *)
          seq 1 1: (
            (Primops.reverted{1} /\ is_none buffer_point{2}) \/
            (
              !Primops.reverted{1} /\ is_some buffer_point{2} /\
              dest{1} = dest_l /\
              128 <= W256.to_uint dest{1} /\
              64 <= W256.to_uint (-dest{1}) /\
              0 <= point{2}.`1 < Constants.Q /\
              0 <= point{2}.`2 < Constants.Q /\
              0 <= (odflt (0,0) buffer_point{2}).`1 < Constants.Q /\
              0 <= (odflt (0,0) buffer_point{2}).`2 < Constants.Q /\
              Primops.memory{1} = store (
                store mem_4 QUERIES_BUFFER_POINT_SLOT (W256.of_int (odflt (0,0) buffer_point{2}).`1)
              ) (QUERIES_BUFFER_POINT_SLOT + (W256.of_int 32)) (W256.of_int (odflt (0,0) buffer_point{2}).`2) /\
              W256.to_uint (load Primops.memory{1} dest{1}) = point{2}.`1 /\
              W256.to_uint (load Primops.memory{1} (dest{1} + W256.of_int 32)) = point{2}.`2
            )
          ).
            exists* vk_permutation_3{2}.
            elim*=> vk_permutation_3.
            call (
              pointMulIntoDest_low_equiv_mid
              vk_permutation_3.`1
              vk_permutation_3.`2
              (W256.to_uint factor)
              VK_PERMUTATION_3_X_SLOT
              QUERIES_BUFFER_POINT_SLOT
              mem_1
            ).
                skip. progress.
                rewrite - Constants.q_eq_fieldq_p. assumption.
                rewrite - Constants.q_eq_fieldq_p. assumption.
                smt (@W256).
                have H_range: 0 <= to_uint factor{1} < W256.modulus by exact W256.to_uint_cmp.
                rewrite andabP in H_range. apply (weaken_and_right (0 <= to_uint factor{1}) _).
                exact H_range.
                rewrite /VK_PERMUTATION_3_X_SLOT. simplify.
                rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-1344)). by progress.
                rewrite /VK_PERMUTATION_3_X_SLOT. simplify.
                rewrite - W256.of_intN. rewrite - (W256.of_int_mod (-1376)). by progress.
                rewrite - H0. rewrite W256.to_uintK. reflexivity.
                rewrite - H1. rewrite W256.to_uintK. reflexivity.
                case H31. progress.
                smt (@EllipticCurve).
                smt (@EllipticCurve @Constants).
                smt (@EllipticCurve).
                smt (@EllipticCurve @Constants).
                rewrite /mem_4 /mem_3 /mem_2.
                rewrite H28. rewrite H29. reflexivity.
                rewrite load_store_diff. rewrite uint256_le_sub_add_32. assumption. rewrite uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. assumption.
                rewrite load_store_diff.
                  apply (uint256_le_le_trans _ (W256.of_int 64) _); [by progress | assumption].
                  apply (uint256_le_le_trans _ (W256.of_int 64) _); [by progress | assumption].
                rewrite load_store_diff.
                rewrite diff_64. rewrite - (W256.to_uintK dest{1}). rewrite ule_of_int. rewrite W256.to_uint_mod. simplify. assumption.
                rewrite diff_neg_64. rewrite - (W256.to_uintK dest{1}). rewrite ule_of_int. rewrite W256.to_uint_mod. simplify. assumption.
                smt (@W256 @Utils).
                rewrite load_store_diff.
                rewrite diff_32. rewrite - (W256.to_uintK dest{1}). rewrite ule_of_int. rewrite W256.to_uint_mod. simplify. assumption.
                rewrite diff_neg_32. rewrite - (W256.to_uintK dest{1}). rewrite ule_of_int. rewrite W256.to_uint_mod. simplify. assumption.
                smt (@W256 @Utils).
                rewrite load_store_diff.
                rewrite diff_0. rewrite - (W256.to_uintK dest{1}). rewrite ule_of_int. rewrite W256.to_uint_mod. simplify. assumption.
                rewrite diff_neg_0. rewrite - (W256.to_uintK dest{1}). rewrite ule_of_int. rewrite W256.to_uint_mod. simplify. assumption.
                smt (@W256 @Utils).
                assumption.
                rewrite load_store_diff.
                  rewrite uint256_sub_add_cancel. apply (uint256_le_le_trans _ (W256.of_int 64) _). assumption. assumption.
                  rewrite uint256_sub_add_cancel. apply (uint256_le_le_trans _ (W256.of_int 64) _). assumption. assumption.
                rewrite load_store_diff.
                  rewrite uint256_le_add_32_sub. apply (uint256_lt_le_trans _ (W256.of_int 64) _). by progress. assumption.
                  rewrite uint256_le_sub_add_32. assumption.
                rewrite load_store_diff.
                have ->: forall (a: uint256), a + W256.of_int 32 - W256.of_int 64 = a - W256.of_int 32. progress. smt (@W256 @Utils).
                rewrite diff_32. rewrite - (W256.to_uintK dest{1}). rewrite ule_of_int. rewrite W256.to_uint_mod. simplify. assumption.
                have ->: forall (a: uint256), W256.of_int 64 - (a + W256.of_int 32) = W256.of_int 32 - a. progress. simplify.
                have ->: forall (a b c: uint256), a - (b + c) = (a - c) - b. smt.
                by progress.
                smt (@W256 @Utils).
                rewrite load_store_diff. smt (@W256 @Utils). smt (@W256 @Utils).
                rewrite load_store_diff.
                  rewrite uint256_le_add_32_sub. smt (@W256 @Utils).
                  rewrite uint256_le_sub_add_32. smt (@W256 @Utils).
                  smt ().
                by progress.
              if{2}. sp. conseq (_ : Primops.reverted{1} /\ ret{2} = None ==> Primops.reverted{1} /\ ret{2} = None).
              progress. smt (). smt ().
              by progress.
              inline*. wp. skip. by progress.
              exists* buffer_point{2}. elim*=>buffer_point_2.
              pose buffer_point_dfl := odflt (0,0) buffer_point_2.
              pose mem_5 := store mem_4 QUERIES_BUFFER_POINT_SLOT (W256.of_int buffer_point_dfl.`1).
              pose mem_6 := store mem_5 (QUERIES_BUFFER_POINT_SLOT + (W256.of_int 32)) (W256.of_int buffer_point_dfl.`2).
              conseq (_ :
                !Primops.reverted{1} /\ is_some buffer_point_2 /\
                buffer_point_2 = buffer_point{2} /\
                dest_l = dest{1} /\
                128 <= W256.to_uint dest{1} /\
                64 <= W256.to_uint (-dest{1}) /\
                0 <= point{2}.`1 < Constants.Q /\
                0 <= point{2}.`2 < Constants.Q /\
                0 <= buffer_point_dfl.`1 < Constants.Q /\
                0 <= buffer_point_dfl.`2 < Constants.Q /\
                W256.to_uint (load mem_6 dest{1}) = point{2}.`1 /\
                W256.to_uint (load mem_6 (dest{1} + W256.of_int 32)) = point{2}.`2 /\
                Primops.memory{1} = mem_6
                ==>
                (Primops.reverted{1} /\ ret{2} = None) \/
                  (!Primops.reverted{1} /\ exists (f: int) (p: (int*int)),
                    ret{2} = Some (f, p) /\
                    exists (x64 x64' x96: uint256) (buffer_p: int*int),
                      Primops.memory{1} = addAssignPermutation_memory_footprint
                        mem_0
                        x64 x64' x96
                        alpha4_r alpha5_r beta_r gamma_r l0AtZ_r opening0AtZ_r opening1AtZ_r opening2AtZ_r opening3AtZ_r v_r z_r
                        buffer_p p
                        dest_l QUERIES_BUFFER_POINT_SLOT
                  )
              ). progress. smt (). smt (). smt ().
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  case H; by progress.
                  by progress.
            seq 1 1: (
              (Primops.reverted{1} /\ ret_point{2} = None) \/
                  (!Primops.reverted{1} /\ is_some ret_point{2} /\
                    exists (x64 x64' x96: uint256) (buffer_p: int*int),
                      Primops.memory{1} = addAssignPermutation_memory_footprint
                        mem_0
                        x64 x64' x96
                        alpha4_r alpha5_r beta_r gamma_r l0AtZ_r opening0AtZ_r opening1AtZ_r opening2AtZ_r opening3AtZ_r v_r z_r
                        buffer_p (odflt (0,0) ret_point{2})
                        dest_l QUERIES_BUFFER_POINT_SLOT
                  )
            ).
            exists* Primops.memory{1}. elim*=> mem_preSub. progress.
            exists* dest{1}. elim*=> dest_1. progress.
            exists* point{2}. elim*=> point_2. progress.
                call (pointSubAssign_low_equiv_mid_fixed mem_preSub dest_1 QUERIES_BUFFER_POINT_SLOT point_2 (odflt (0, 0) buffer_point_2)).
                skip.
                progress.
                rewrite W256.to_uintN. rewrite W256.of_uintK. smt (@IntDiv).
                rewrite load_store_diff. smt. smt.
                rewrite load_store_same. rewrite W256.of_uintK. smt (@W256 @Utils @IntDiv).
                rewrite load_store_same. rewrite W256.of_uintK. smt (@W256 @Utils @IntDiv).
                rewrite - Constants.q_eq_fieldq_p. assumption.
                rewrite - Constants.q_eq_fieldq_p. assumption.
                rewrite - /buffer_point_dfl. assumption.
                rewrite - Constants.q_eq_fieldq_p. assumption.
                rewrite - /buffer_point_dfl. assumption.
                rewrite - Constants.q_eq_fieldq_p. assumption.
                case H30. by progress. 
                progress. exists x64. exists factor. exists x96. exists buffer_point_dfl. rewrite /addAssignPermutation_memory_footprint. simplify. congr.
                rewrite /mem_6. congr.
                rewrite /mem_5. congr.
                rewrite /mem_4. congr.
                rewrite /mem_3. congr.
                rewrite /mem_2. congr.
                reflexivity. reflexivity. reflexivity.
                
            (*---seq done---*)
                if{2}. wp. skip. progress. case H. by progress. smt ().
                wp. skip. progress. smt ().
                smt ().
            qed. 


















              
